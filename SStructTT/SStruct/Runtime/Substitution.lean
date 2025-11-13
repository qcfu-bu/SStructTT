import SStructTT.SStruct.Runtime.Resolution

namespace SStruct.Extraction
variable {Srt : Type} [ord : SrtOrder Srt]

def IdRename (i : Var) (ξ : Var -> Var) : Prop := ∀ x, x < i -> ξ x = x

private lemma IdRename.zero : IdRename 0 (.+1) := by
  intro x lw; cases lw

private lemma IdRename.up {i ξ} :
    IdRename i ξ -> IdRename (i + 1) (upren ξ) := by
  intro idr x lt
  cases x with
  | zero => asimp
  | succ x => simp at lt; asimp; apply idr _ lt

omit ord in
private lemma closed_rename {m : Tm Srt} {i ξ} :
    Closed i m -> IdRename i ξ  -> m = m.[ren ξ] := by
  intro cl idr; induction m generalizing i ξ
  all_goals simp_all; try (solve| aesop)
  case var => asimp; simp[idr _ cl]
  case lam ih =>
    asimp; rw[Tm.up_upren]; apply ih cl
    apply idr.up
  case app =>
    have ⟨cl1, cl2⟩ := cl
    asimp; aesop
  case tup =>
    have ⟨cl1, cl2⟩ := cl
    asimp; aesop
  case prj ih =>
    have ⟨cl1, cl2⟩ := cl
    asimp; split_ands
    . aesop
    . rw[show @upn (Tm Srt) _ _ 2 (ren ξ) = ren (upren (upren ξ)) by asimp]
      apply ih cl2
      apply idr.up.up
  case ite =>
    have ⟨cl1, cl2⟩ := cl
    asimp; aesop
  case drop =>
    have ⟨cl1, cl2⟩ := cl
    asimp; aesop

namespace Runtime
open Program

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst :
  (Var -> Tm Srt) -> (Var -> Tm Srt) -> Nat -> Ctx Srt -> Heap Srt -> Prop
where
  | nil {H σ σ'} :
    Shareable H ->
    AgreeSubst σ σ' 0 [] H
  | cons {Δ H σ σ' A x r s} :
    AgreeSubst σ σ' x Δ H ->
    AgreeSubst (up σ) (up σ') (x + 1) (A :⟨r, s⟩ Δ) H
  | intro_im {Δ H σ σ' A m m' s} :
    AgreeSubst σ σ' 0 Δ H ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.im, s⟩ Δ) H
  | intro_ex {Δ H1 H2 H3 σ σ' m m' A s} :
    (s ∈ ord.contra_set -> Shareable H2) ->
    HMerge H1 H2 H3 ->
    H2 ;; m ▷ m' ->
    AgreeSubst σ σ' 0 Δ H1 ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.ex, s⟩ Δ) H3

lemma AgreeSubst.implicit_image {Δ : Ctx Srt} {H σ σ' x} :
    AgreeSubst σ σ' x Δ H -> Implicit Δ -> Shareable H := by
  intro agr im; induction agr
  case nil => assumption
  case cons ih =>
    simp at im; replace ⟨e, im⟩ := im; subst_vars
    apply ih; apply im
  case intro_im ih =>
    simp at im
    apply ih; apply im
  case intro_ex => simp at im

lemma AgreeSubst.shareable_image {Δ : Ctx Srt} {H σ σ' x s} :
    AgreeSubst σ σ' x Δ H -> Lower Δ s -> (s ∈ ord.contra_set -> Shareable H) := by
  intro agr lw; induction agr generalizing s
  case nil => intro; assumption
  case cons => cases lw <;> aesop
  case intro_im => cases lw; aesop
  case intro_ex wr hw2 mrg erm agr ih =>
    intro h
    cases lw; case ex le lw =>
    have ct1 := ih lw h
    replace ct2 := hw2 (ord.contra_set.lower le h)
    apply mrg.shareable_image ct1 ct2

lemma AgreeSubst.subst_var {Δ : Ctx Srt} {H σ σ' i x} :
    AgreeSubst σ σ' i Δ H -> x < i -> .var x = σ' x := by
  intro agr le; induction agr generalizing x
  all_goals try trivial
  case cons i _ _  agr ih =>
    cases x with
    | zero => asimp
    | succ x =>
      simp at le; asimp
      have e := ih le
      rw[<-e]; asimp

lemma AgreeSubst.closed_subst {Δ : Ctx Srt} {H σ σ' i x m} :
    AgreeSubst σ σ' i Δ H -> Closed x m -> x ≤ i -> m = m.[σ'] := by
  intro agr cl lw; induction m generalizing Δ H σ σ' i x
  all_goals simp_all
  case var =>
    asimp; apply agr.subst_var
    apply cl.trans_le lw
  case lam ih =>
    asimp; apply ih
    . apply AgreeSubst.cons agr
      constructor; apply 0; constructor; apply ord.ι
    . assumption
    . simp[lw]
  case prj ihm ihn =>
    have ⟨cl1, cl2⟩ := cl
    asimp; split_ands
    . aesop
    . apply ihn
      . apply AgreeSubst.cons
        constructor; apply 0; constructor; apply ord.ι
        apply AgreeSubst.cons
        constructor; apply 0; constructor; apply ord.ι
        apply agr
      . aesop
      . simp[lw]
  all_goals asimp; try aesop

lemma Resolve.id_rename {H : Heap Srt} {m m' i ξ} :
    H ;; m ▷ m' -> IdRename i ξ -> H ;; m.[ren ξ] ▷ m'.[ren ξ] := by
  intro rs idr; induction rs generalizing i ξ
  case var => asimp; constructor; assumption
  case lam lw _ ih =>
    asimp; apply Resolve.lam lw
    replace ih := ih idr.up
    asimp at ih; apply ih
  case app mrg rsm rsn ihm ihn =>
    replace ihm := ihm idr
    replace ihn := ihn idr
    asimp; apply Resolve.app mrg ihm ihn
  case tup mrg rsm rsn ihm ihn =>
    replace ihm := ihm idr
    replace ihn := ihn idr
    asimp; apply Resolve.tup mrg ihm ihn
  case prj mrg rsm rsn ihm ihn =>
    replace ihm := ihm idr
    replace ihn := ihn idr.up.up; asimp at ihn
    asimp; apply Resolve.prj mrg ihm ihn
  case tt => asimp; constructor; assumption
  case ff => asimp; constructor; assumption
  case ite mrg rsm rsn1 rsn2 ihm ihn1 ihn2 =>
    replace ihm := ihm idr
    replace ihn1 := ihn1 idr
    replace ihn2 := ihn2 idr
    asimp; apply Resolve.ite mrg ihm ihn1 ihn2
  case drop mrg rsm rsn ihm ihn =>
    replace ihm := ihm idr
    replace ihn := ihn idr
    asimp; apply Resolve.drop mrg ihm ihn
  case ptr l m n lk rsm ihm =>
    asimp
    have clm := lk.closed
    have clm' := (rsm.closed_image clm).weaken (zero_le i)
    rw[<-closed_rename clm' idr]
    constructor <;> assumption
  case null => asimp; constructor; assumption

lemma AgreeSubst.has {Δ : Ctx Srt} {H σ σ' x i s A} :
    AgreeSubst σ σ' i Δ H -> Has Δ x s A -> H ;; σ x ▷ σ' x := by
  intro agr hs; induction agr generalizing x s A
  case nil => cases hs
  case cons agr ih =>
    cases hs
    case nil im =>
      asimp; constructor
      apply agr.implicit_image im
    case cons =>
      asimp; apply Resolve.id_rename
      . aesop
      . apply IdRename.zero
  case intro_im =>
    cases hs; asimp; aesop
  case intro_ex wr lw mrg rsm agr ih =>
    cases hs; case nil im =>
    asimp
    have ct := agr.implicit_image im
    apply rsm.merge_shareable mrg.sym ct

lemma AgreeSubst.split {Δ1 Δ2 Δ3 : Ctx Srt} {H3 σ σ' x} :
    AgreeSubst σ σ' x Δ3 H3 -> Merge Δ1 Δ2 Δ3 ->
    ∃ H1 H2,
      HMerge H1 H2 H3 ∧
      AgreeSubst σ σ' x Δ1 H1 ∧
      AgreeSubst σ σ' x Δ2 H2 := by
  intro agr mrg; induction agr generalizing Δ1 Δ2
  case nil H _ _ ct =>
    cases mrg
    existsi H, H; and_intros
    . apply ct.merge_refl
    . constructor; assumption
    . constructor; assumption
  case cons agr ih =>
    cases mrg
    case contra mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      existsi H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
    case left mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      existsi H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
    case right mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      existsi H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
    case im mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      existsi H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
  case intro_im ih =>
    cases mrg
    case im mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      existsi H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
  case intro_ex A s wr2 ct2 mrg1 rsm agr ih =>
    cases mrg
    case contra h mrg =>
      replace ct2 := ct2 h
      have ⟨H1, H2, mrg2, agr1, agr2⟩ := ih mrg
      have mrg3 := ct2.merge_refl
      have ⟨H1', H2', mrg', mrg1', mrg2'⟩ := mrg1.distr mrg2 mrg3
      existsi H1', H2'; and_intros
      . apply mrg'
      . apply AgreeSubst.intro_ex (by aesop) mrg1' rsm agr1
      . apply AgreeSubst.intro_ex (by aesop) mrg2' rsm agr2
    case left mrg =>
      have ⟨H1, H2, mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Ha, mrg1', mrg2'⟩ := mrg1.split mrg2
      existsi Ha, H2; and_intros
      . apply mrg2'
      . apply AgreeSubst.intro_ex (by aesop) mrg1' rsm agr1
      . apply AgreeSubst.intro_im agr2
    case right  mrg =>
      have ⟨H1, H2, mrg2, agr1, agr2⟩ := ih mrg.sym
      have ⟨Ha, mrg1', mrg2'⟩ := mrg1.split mrg2
      existsi H2, Ha; and_intros
      . apply mrg2'.sym
      . apply AgreeSubst.intro_im agr2
      . apply AgreeSubst.intro_ex (by aesop) mrg1' rsm agr1

lemma Resolved.substitution {H1 H2 H3 : Heap Srt} {Δ m n n' A σ σ' x} :
    Δ ;; H1 ⊢ m ▷ n ◁ n' :: A -> HMerge H1 H2 H3 -> AgreeSubst σ σ' x Δ H2 ->
    H3 ;; n'.[σ] ▷ n.[σ'] := by
  intro ⟨er, rs⟩ mrg agr
  induction er generalizing H1 H2 H3 σ σ' n' x
  case var hs =>
    asimp; cases rs
    case var ct =>
      asimp
      apply Resolve.merge_shareable mrg.sym ct
      apply agr.has hs
    case ptr l m h rsm =>
      cases m
      all_goals simp_all[Cell.tm]; cases rsm
  case lam_im Δ A B m m' s sA iA lw tyA erm ihm =>
    have ct2 := agr.shareable_image lw
    asimp; cases rs
    case lam erm ct1 =>
      asimp
      have ct3 := mrg.split_shareable_hyp ct1 ct2
      replace ihm := ihm erm mrg agr.cons
      apply Resolve.lam ct3 ihm
    case ptr l x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
      case lam cl0 rsm ct1 =>
        asimp
        have cl1 := rsm.closed_image cl0
        have cl2 : Closed 0 (Tm.lam m' s) := by simp; assumption
        have erm := Extract.lam_im lw tyA erm
        have im := (erm.closed_stack cl2).toImplicit
        have ct := agr.implicit_image im
        have agr : AgreeSubst (up σ) (up σ') (x + 1) (A :⟨.im, sA⟩ Δ) H2 := by
          apply AgreeSubst.cons; assumption
        rw[<-agr.closed_subst cl1 (by simp)]
        apply Resolve.merge_shareable mrg ct
        apply Resolve.ptr lk
        constructor <;> assumption
  case lam_ex Δ A B m m' s sA iA lw tyA erm ihm =>
    have ct2 := agr.shareable_image lw
    asimp; cases rs
    case lam erm ct1 =>
      asimp
      have ct3 := mrg.split_shareable_hyp ct1 ct2
      replace ihm := ihm erm mrg agr.cons
      apply Resolve.lam ct3 ihm
    case ptr l x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
      case lam cl0 rsm ct1 =>
        asimp
        have cl1 := rsm.closed_image cl0
        have cl2 : Closed 0 (Tm.lam m' s) := by simp; assumption
        have erm := Extract.lam_ex lw tyA erm
        have im := (erm.closed_stack cl2).toImplicit
        have ct := agr.implicit_image im
        have agr : AgreeSubst (up σ) (up σ') (x + 1) (A :⟨.im, sA⟩ Δ) H2 := by
          apply AgreeSubst.cons; assumption
        rw[<-agr.closed_subst cl1 (by simp)]
        apply Resolve.merge_shareable mrg ct
        apply Resolve.ptr lk
        constructor <;> assumption
  case app_im A B m m' n s erm tyn ihm =>
    asimp; cases rs
    case app mrg1 rsm rsn =>
      have ⟨H2', mrg2, mrg'⟩ := mrg.split mrg1
      have ⟨ct, e⟩ := rsn.null_inv; subst e
      asimp; apply Resolve.app mrg'
      . apply ihm rsm mrg2 agr
      . assumption
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
  case app_ex mrg0 erm ern ihm ihn =>
    asimp; cases rs
    case app mrg1 rsm rsn =>
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm mrg1' agr1
      replace ihn := ihn rsn mrg2' agr2
      asimp; apply Resolve.app mrg3 ihm ihn
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
  case tup_im ty tym ern ihn =>
    asimp; cases rs
    case tup mrg1 rsm rsn =>
      have ⟨H2', mrg2, mrg'⟩ := mrg.split mrg1.sym
      have ⟨ct, e⟩ := rsm.null_inv; subst e
      asimp; apply Resolve.tup mrg'.sym
      . assumption
      . apply ihn rsn mrg2 agr
    case ptr l x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
      case box mrg0 rsm rsn =>
        have cl := rsn.ptr_closed
        have im := (ern.closed_stack cl).toImplicit
        have ct := agr.implicit_image im
        rw[<-agr.closed_subst cl (by simp)]
        apply Resolve.merge_shareable mrg ct
        apply Resolve.ptr lk; simp[Cell.tm]
        constructor <;> assumption
      case tup rs _ =>
        have ⟨_, e⟩ := rs.null_inv; cases e
  case tup_ex mrg0 ty erm ern ihm ihn =>
    asimp; cases rs
    case tup mrg1 rsm rsn =>
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm mrg1' agr1
      replace ihn := ihn rsn mrg2' agr2
      asimp; apply Resolve.tup mrg3 ihm ihn
    case ptr l x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
      case box rs _ =>
        cases rs
        exfalso; apply erm.null_preimage
      case tup mrg1 rsm rsn =>
        have cl1 := rsm.ptr_closed
        have cl2 := rsn.ptr_closed
        have im1 := (erm.closed_stack cl1).toImplicit
        have im2 := (ern.closed_stack cl2).toImplicit
        have im := mrg0.implicit_image im1 im2
        have ct := agr.implicit_image im
        rw[<-agr.closed_subst cl1 (by simp)]
        rw[<-agr.closed_subst cl2 (by simp)]
        apply Resolve.merge_shareable mrg ct
        apply Resolve.ptr lk
        constructor <;> assumption
  case prj_im mrg0 tyC erm ern ihm ihn =>
    asimp; cases rs
    case prj mrg1 rsm rsn =>
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm mrg1' agr1
      replace ihn := ihn rsn mrg2' agr2.cons.cons
      asimp; apply Resolve.prj mrg3 ihm ihn
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
  case prj_ex mrg0 tyC erm ern ihm ihn =>
    asimp; cases rs
    case prj mrg1 rsm rsn =>
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm mrg1' agr1
      replace ihn := ihn rsn mrg2' agr2.cons.cons
      asimp; apply Resolve.prj mrg3 ihm ihn
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
  case tt im =>
    have ct2 := agr.implicit_image im
    asimp; cases rs
    case tt ct1 =>
      asimp; apply Resolve.tt (mrg.shareable_image ct1 ct2)
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
      case tt =>
        asimp
        apply Resolve.merge_shareable mrg ct2
        apply Resolve.ptr lk
        constructor; assumption
  case ff im =>
    have ct2 := agr.implicit_image im
    asimp; cases rs
    case ff ct1 =>
      asimp; apply Resolve.ff (mrg.shareable_image ct1 ct2)
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
      case ff =>
        asimp
        apply Resolve.merge_shareable mrg ct2
        apply Resolve.ptr lk
        constructor; assumption
  case ite mrg0 tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    asimp; cases rs
    case ite mrg1 rsm rsn1 rsn2 =>
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm mrg1' agr1
      replace ihn1 := ihn1 rsn1 mrg2' agr2
      replace ihn2 := ihn2 rsn2 mrg2' agr2
      asimp; apply Resolve.ite mrg3 ihm ihn1 ihn2
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
  case rw ih => aesop
  case drop mrg0 lw0 h0 _ _ ihm ihn =>
    asimp; cases rs
    case drop mrg1 rsm rsn =>
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ct0 := agr1.shareable_image lw0
      replace ihm := ihm rsm mrg1' agr1
      replace ihn := ihn rsn mrg2' agr2
      asimp; apply Resolve.drop mrg3 ihm ihn
    case ptr x lk rsm =>
      cases x
      all_goals simp_all[Cell.tm]; cases rsm
  case conv => aesop

lemma Resolved.subst_im {H : Heap Srt} {m n n' v v' A B s} :
    A :⟨.im, s⟩ [] ;; H ⊢ m ▷ n ◁ n' :: B -> H ;; n'.[v'/] ▷ n.[v/] := by
  intro rsm
  have ⟨H0, mrg, sh⟩ := HMerge.exists_self_shareable H
  apply rsm.substitution mrg (x := 0)
  apply AgreeSubst.intro_im
  constructor; assumption

lemma Resolved.subst_ex {H1 H2 H3 : Heap Srt} {m n n' v v' A B s} :
    HMerge H1 H2 H3 -> (s ∈ ord.contra_set -> Shareable H2) ->
    A :⟨.ex, s⟩ [] ;; H1 ⊢ m ▷ n ◁ n' :: B ->
    H2 ;; v' ▷ v ->
    H3 ;; n'.[v'/] ▷ n.[v/] := by
  intro mrg h rsm rsv
  have ⟨H0, mrg0, sh⟩ := HMerge.exists_self_shareable H2
  apply rsm.substitution mrg (x := 0)
  apply AgreeSubst.intro_ex h mrg0.sym rsv
  constructor; assumption
