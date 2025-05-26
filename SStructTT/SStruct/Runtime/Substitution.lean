import SStructTT.SStruct.Runtime.Resolution

namespace SStruct.Erasure
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
lemma NF.id_rename {m : Tm Srt} {i ξ} :
    NF i m -> IdRename i ξ  -> m = m.[ren ξ] := by
  intro nf idr; induction m generalizing i ξ
  all_goals simp_all; try (solve| aesop)
  case var => asimp; simp[idr _ nf]
  case lam ih =>
    asimp; rw[Tm.up_upren]; apply ih nf
    apply idr.up
  case app =>
    have ⟨nf1, nf2⟩ := nf
    asimp; aesop
  case tup =>
    have ⟨nf1, nf2⟩ := nf
    asimp; aesop
  case prj ih =>
    have ⟨nf1, nf2⟩ := nf
    asimp; split_ands
    . aesop
    . rw[show @upn (Tm Srt) _ _ 2 (ren ξ) = ren (upren (upren ξ)) by asimp]
      apply ih nf2
      apply idr.up.up
  case ite =>
    have ⟨nf1, nf2⟩ := nf
    asimp; aesop
  case drop =>
    have ⟨nf1, nf2⟩ := nf
    asimp; aesop

namespace Runtime
open Dynamic

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst :
  (Var -> Tm Srt) -> (Var -> Tm Srt) -> Nat -> Ctx Srt -> Heap Srt -> Prop
where
  | nil {σ σ'} :
    AgreeSubst σ σ' 0 [] ∅
  | cons {Δ H σ σ' A x r s} :
    AgreeSubst σ σ' x Δ H ->
    AgreeSubst (up σ) (up σ') (x + 1) (A :⟨r, s⟩ Δ) H
  | intro_im {Δ H σ σ' A m m' s} :
    AgreeSubst σ σ' 0 Δ H ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.im, s⟩ Δ) H
  | intro_ex {Δ H1 H2 H3 σ σ' m m' A s} :
    WR H2 ->
    HLower H2 s ->
    HMerge H1 H2 H3 ->
    H2 ⊢ m ▷ m' ->
    AgreeSubst σ σ' 0 Δ H1 ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.ex, s⟩ Δ) H3

lemma AgreeSubst.implicit_image {Δ : Ctx Srt} {H σ σ' x} :
    AgreeSubst σ σ' x Δ H -> Implicit Δ -> H = ∅ := by
  intro agr im; induction agr
  case nil => rfl
  case cons ih =>
    simp at im; replace ⟨e, im⟩ := im; subst_vars
    apply ih; apply im
  case intro_im ih =>
    simp at im
    apply ih; apply im
  case intro_ex => simp at im

lemma AgreeSubst.lower_image {Δ : Ctx Srt} {H σ σ' x s} :
    AgreeSubst σ σ' x Δ H -> Lower Δ s -> HLower H s := by
  intro agr lw; induction agr generalizing s
  case nil => apply HLower.empty
  case cons => cases lw <;> aesop
  case intro_im => cases lw; aesop
  case intro_ex wr hw2 mrg erm agr ih =>
    cases lw; case ex le lw =>
    have hw1 := ih lw
    replace hw2 := hw2.weaken le
    apply mrg.lower_image hw1 hw2

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

lemma AgreeSubst.nf_subst {Δ : Ctx Srt} {H σ σ' i x m} :
    AgreeSubst σ σ' i Δ H -> NF x m -> x ≤ i -> m = m.[σ'] := by
  intro agr nf lw; induction m generalizing Δ H σ σ' i x
  all_goals simp_all
  case var =>
    asimp; apply agr.subst_var
    apply nf.trans_le lw
  case lam ih =>
    asimp; apply ih
    . apply AgreeSubst.cons agr
      constructor; apply 0; constructor; apply ord.e
    . assumption
    . simp[lw]
  case prj ihm ihn =>
    have ⟨nf1, nf2⟩ := nf
    asimp; split_ands
    . aesop
    . apply ihn
      . apply AgreeSubst.cons
        constructor; apply 0; constructor; apply ord.e
        apply AgreeSubst.cons
        constructor; apply 0; constructor; apply ord.e
        apply agr
      . aesop
      . simp[lw]
  all_goals asimp; try aesop

lemma AgreeSubst.wr_heap {Δ : Ctx Srt} {H σ σ' i} :
    AgreeSubst σ σ' i Δ H -> WR H := by
  intro agr; induction agr
  all_goals try aesop
  case nil => apply WR.empty
  case intro_ex wr2 _ mrg _ _ wr1 =>
    apply mrg.merge_wr wr1 wr2

lemma Resolve.id_rename {H : Heap Srt} {m m' i ξ} :
    H ⊢ m ▷ m' -> WR H -> IdRename i ξ -> H ⊢ m.[ren ξ] ▷ m'.[ren ξ] := by
  intro rs wr idr; induction rs generalizing i ξ
  case var => asimp; constructor; assumption
  case lam lw _ ih =>
    asimp; apply Resolve.lam lw
    replace ih := ih wr idr.up
    asimp at ih; apply ih
  case app mrg rsm rsn ihm ihn =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 idr
    replace ihn := ihn wr2 idr
    asimp; apply Resolve.app mrg ihm ihn
  case tup mrg rsm rsn ihm ihn =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 idr
    replace ihn := ihn wr2 idr
    asimp; apply Resolve.tup mrg ihm ihn
  case prj mrg rsm rsn ihm ihn =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 idr
    replace ihn := ihn wr2 idr.up.up; asimp at ihn
    asimp; apply Resolve.prj mrg ihm ihn
  case tt => asimp; constructor; assumption
  case ff => asimp; constructor; assumption
  case ite mrg rsm rsn1 rsn2 ihm ihn1 ihn2 =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 idr
    replace ihn1 := ihn1 wr2 idr
    replace ihn2 := ihn2 wr2 idr
    asimp; apply Resolve.ite mrg ihm ihn1 ihn2
  case drop mrg lw mem rsm rsn ihm ihn =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 idr
    replace ihn := ihn wr2 idr
    asimp; apply Resolve.drop mrg lw mem ihm ihn
  case ptr l m n s h rsm ihm =>
    asimp
    have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
    have nfm' := rsm.nf_image wr0 (wr.nf l m s (by simp))
    have nfm' := nfm'.weaken (zero_le i)
    rw[<-nfm'.id_rename idr]
    constructor <;> assumption
  case null => asimp; constructor; assumption

lemma AgreeSubst.has {Δ : Ctx Srt} {H σ σ' x i s A} :
    AgreeSubst σ σ' i Δ H -> Has Δ x s A -> H ⊢ σ x ▷ σ' x := by
  intro agr hs; induction agr generalizing x s A
  case nil => cases hs
  case cons agr ih =>
    cases hs
    case nil im =>
      rw[agr.implicit_image im]
      asimp; constructor; apply HLower.empty
    case cons =>
      asimp; apply Resolve.id_rename
      . aesop
      . apply agr.wr_heap
      . apply IdRename.zero
  case intro_im =>
    cases hs; asimp; aesop
  case intro_ex wr lw mrg rsm agr ih =>
    cases hs; case nil im =>
    asimp
    rw[agr.implicit_image im] at mrg
    have e := mrg.sym.empty_inv; subst e
    assumption

lemma AgreeSubst.split {Δ1 Δ2 Δ3 : Ctx Srt} {H3 σ σ' x} :
    AgreeSubst σ σ' x Δ3 H3 -> Merge Δ1 Δ2 Δ3 ->
    ∃ H1 H2,
      HMerge H1 H2 H3 ∧
      AgreeSubst σ σ' x Δ1 H1 ∧
      AgreeSubst σ σ' x Δ2 H2 := by
  intro agr mrg; induction agr generalizing Δ1 Δ2
  case nil =>
    cases mrg
    exists ∅, ∅; and_intros
    . apply HMerge.empty
    . constructor
    . constructor
  case cons agr ih =>
    cases mrg
    case contra mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      exists H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
    case left mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      exists H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
    case right mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      exists H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
    case im mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      exists H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
  case intro_im ih =>
    cases mrg
    case im mrg =>
      have ⟨H1, H2, mrg, agr1, agr2⟩ := ih mrg
      exists H1, H2; and_intros
      . assumption
      . constructor; assumption
      . constructor; assumption
  case intro_ex A s wr2 lw2 mrg1 rsm agr ih =>
    cases mrg
    case contra h mrg =>
      have ⟨H1, H2, mrg2, agr1, agr2⟩ := ih mrg
      have mrg3 := lw2.merge_refl h
      have ⟨H1', H2', mrg', mrg1', mrg2'⟩ := mrg1.distr mrg2 mrg3
      exists H1', H2'; and_intros
      . apply mrg'
      . apply AgreeSubst.intro_ex wr2 lw2 mrg1' rsm agr1
      . apply AgreeSubst.intro_ex wr2 lw2 mrg2' rsm agr2
    case left mrg =>
      have ⟨H1, H2, mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Ha, mrg1', mrg2'⟩ := mrg1.split mrg2
      exists Ha, H2; and_intros
      . apply mrg2'
      . apply AgreeSubst.intro_ex wr2 lw2 mrg1' rsm agr1
      . apply AgreeSubst.intro_im agr2
    case right  mrg =>
      have ⟨H1, H2, mrg2, agr1, agr2⟩ := ih mrg.sym
      have ⟨Ha, mrg1', mrg2'⟩ := mrg1.split mrg2
      exists H2, Ha; and_intros
      . apply mrg2'.sym
      . apply AgreeSubst.intro_im agr2
      . apply AgreeSubst.intro_ex wr2 lw2 mrg1' rsm agr1

lemma Resolved.substitution {H1 H2 H3 : Heap Srt} {Γ Δ m n n' A σ σ' x} :
    Γ ;; Δ ;; H1 ⊢ m ▷ n ◁ n' : A -> HMerge H1 H2 H3 -> AgreeSubst σ σ' x Δ H2 ->
    H3 ⊢ n'.[σ] ▷ n.[σ'] := by
  intro ⟨er, rs, wr⟩ mrg agr
  induction er generalizing H1 H2 H3 σ σ' n' x
  case var hs =>
    asimp; cases rs
    case var lw =>
      asimp
      apply Resolve.weaken_merge mrg.sym lw
      apply agr.has hs
    case ptr l m s h rsm =>
      cases rsm
      case var => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case lam_im Δ A B m m' s sA iA lw tyA erm ihm =>
    have lw2 := agr.lower_image lw
    asimp; cases rs
    case lam erm lw1 =>
      asimp
      have lw3 := mrg.lower_image lw1 lw2
      replace ihm := ihm erm wr mrg agr.cons
      apply Resolve.lam lw3 ihm
    case ptr l x s h rsm =>
      cases rsm
      case lam rsm _ =>
        asimp
        have nf0 := wr l; simp at nf0
        replace ⟨nf0, e⟩ := nf0; subst e
        have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
        have nf1 := rsm.nf_image wr0 nf0
        have nf2 : NF 0 (.lam m' s) := by simp; assumption
        have erm := Erased.lam_im lw tyA erm
        have im := (erm.nf_stack nf2).toImplicit
        have e := agr.implicit_image im; subst e
        have e := mrg.empty_inv; subst e
        have agr : AgreeSubst (up σ) (up σ') (x + 1) (A :⟨.im, sA⟩ Δ) ∅ := by
          apply AgreeSubst.cons; assumption
        rw[<-agr.nf_subst nf1 (by simp)]
        apply Resolve.ptr h
        constructor <;> assumption
      case ptr => have wr := wr l; simp at wr
  case lam_ex Δ A B m m' s sA iA lw tyA erm ihm =>
    have lw2 := agr.lower_image lw
    asimp; cases rs
    case lam erm lw1 =>
      asimp
      have lw3 := mrg.lower_image lw1 lw2
      replace ihm := ihm erm wr mrg agr.cons
      apply Resolve.lam lw3 ihm
    case ptr l x s h rsm =>
      cases rsm
      case lam rsm _ =>
        asimp
        have nf0 := wr l; simp at nf0
        replace ⟨nf0, e⟩ := nf0; subst e
        have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
        have nf1 := rsm.nf_image wr0 nf0
        have nf2 : NF 0 (.lam m' s) := by simp; assumption
        have erm := Erased.lam_ex lw tyA erm
        have im := (erm.nf_stack nf2).toImplicit
        have e := agr.implicit_image im; subst e
        have e := mrg.empty_inv; subst e
        have agr : AgreeSubst (up σ) (up σ') (x + 1) (A :⟨.im, sA⟩ Δ) ∅ := by
          apply AgreeSubst.cons; assumption
        rw[<-agr.nf_subst nf1 (by simp)]
        apply Resolve.ptr h
        constructor <;> assumption
      case ptr => have wr := wr l; simp at wr
  case app_im A B m m' n s erm tyn ihm =>
    asimp; cases rs
    case app mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨H2', mrg2, mrg'⟩ := mrg.split mrg1
      have ⟨lw, e⟩ := rsn.null_inv wr2; subst e
      asimp; apply Resolve.app mrg'
      . apply ihm rsm wr1 mrg2 agr
      . assumption
    case ptr l _ _ _ rsm =>
      cases rsm
      case app => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case app_ex mrg0 erm ern ihm ihn =>
    asimp; cases rs
    case app mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm wr1 mrg1' agr1
      replace ihn := ihn rsn wr2 mrg2' agr2
      asimp; apply Resolve.app mrg3 ihm ihn
    case ptr l _ _ _ rsm =>
      cases rsm
      case app => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case tup_im ty erm tyn ihm =>
    asimp; cases rs
    case tup mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨H2', mrg2, mrg'⟩ := mrg.split mrg1
      have ⟨lw, e⟩ := rsn.null_inv wr2; subst e
      asimp; apply Resolve.tup mrg'
      . apply ihm rsm wr1 mrg2 agr
      . assumption
    case ptr l _ _ h rsm =>
      asimp; cases rsm
      case tup mrg0 rsm rsn =>
        have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
        have ⟨wr1, wr2⟩ := mrg0.split_wr wr0
        have nf0 := wr.nf l; simp at nf0
        rcases nf0 with ⟨nf1, nf2⟩
        have nf1' := rsm.nf_image wr1 nf1
        have im := (erm.nf_stack nf1').toImplicit
        have e := agr.implicit_image im; subst e
        have e := mrg.empty_inv; subst e
        rw[<-agr.nf_subst nf1' (by simp)]
        apply Resolve.ptr h
        constructor <;> assumption
      case ptr => have wr := wr l; simp at wr
  case tup_ex mrg0 ty erm ern ihm ihn =>
    asimp; cases rs
    case tup mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm wr1 mrg1' agr1
      replace ihn := ihn rsn wr2 mrg2' agr2
      asimp; apply Resolve.tup mrg3 ihm ihn
    case ptr l _ _ h rsm =>
      asimp; cases rsm
      case tup mrg1 rsm rsn =>
        have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
        have ⟨wr1, wr2⟩ := mrg1.split_wr wr0
        have nf0 := wr.nf l; simp at nf0
        rcases nf0 with ⟨nf1, nf2⟩
        have nf1' := rsm.nf_image wr1 nf1
        have nf2' := rsn.nf_image wr2 nf2
        have im1 := (erm.nf_stack nf1').toImplicit
        have im2 := (ern.nf_stack nf2').toImplicit
        have im := mrg0.implicit_image im1 im2
        have e := agr.implicit_image im; subst e
        have e := mrg.empty_inv; subst e
        rw[<-agr.nf_subst nf1' (by simp)]
        rw[<-agr.nf_subst nf2' (by simp)]
        apply Resolve.ptr h
        constructor <;> assumption
      case ptr => have wr := wr l; simp at wr
  case prj_im mrg0 tyC erm ern ihm ihn =>
    asimp; cases rs
    case prj mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm wr1 mrg1' agr1
      replace ihn := ihn rsn wr2 mrg2' agr2.cons.cons
      asimp; apply Resolve.prj mrg3 ihm ihn
    case ptr l _ _ h rsm =>
      asimp; cases rsm
      case prj => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case prj_ex mrg0 tyC erm ern ihm ihn =>
    asimp; cases rs
    case prj mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm wr1 mrg1' agr1
      replace ihn := ihn rsn wr2 mrg2' agr2.cons.cons
      asimp; apply Resolve.prj mrg3 ihm ihn
    case ptr l _ _ h rsm =>
      asimp; cases rsm
      case prj => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case tt im =>
    have e := agr.implicit_image im; subst e
    have e := mrg.empty_inv; subst e
    asimp; cases rs
    case tt => asimp; apply Resolve.tt; assumption
    case ptr l _ _ h rsm =>
      cases rsm
      case tt =>
        asimp; apply Resolve.ptr h
        constructor; assumption
      case ptr => have wr := wr l; simp at wr
  case ff im =>
    have e := agr.implicit_image im; subst e
    have e := mrg.empty_inv; subst e
    asimp; cases rs
    case ff => asimp; apply Resolve.ff; assumption
    case ptr l _ _ h rsm =>
      cases rsm
      case ff =>
        asimp; apply Resolve.ptr h
        constructor; assumption
      case ptr => have wr := wr l; simp at wr
  case ite mrg0 tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    asimp; cases rs
    case ite mrg1 rsm rsn1 rsn2 =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace ihm := ihm rsm wr1 mrg1' agr1
      replace ihn1 := ihn1 rsn1 wr2 mrg2' agr2
      replace ihn2 := ihn2 rsn2 wr2 mrg2' agr2
      asimp; apply Resolve.ite mrg3 ihm ihn1 ihn2
    case ptr l _ _ h rsm =>
      cases rsm
      case ite => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case rw ih => aesop
  case drop mrg0 lw0 h0 _ _ ihm ihn =>
    asimp; cases rs
    case drop lw1 h1 mrg1 rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg1.split_wr wr
      have ⟨Ha, Hb, mrg2, agr1, agr2⟩ := agr.split mrg0
      have ⟨H1', H2', mrg3, mrg1', mrg2'⟩ := mrg.distr mrg1 mrg2
      replace lw0 := agr1.lower_image lw0
      have ⟨s, h0, h1, h2⟩ := InterSet.intersect_weaken h0 h1
      replace lw0 := lw0.cover h1
      replace lw1 := lw1.cover h2
      have lw := mrg1'.lower_image lw1 lw0
      replace ihm := ihm rsm wr1 mrg1' agr1
      replace ihn := ihn rsn wr2 mrg2' agr2
      asimp; apply Resolve.drop mrg3 lw h0 ihm ihn
    case ptr l _ _ h rsm =>
      asimp; cases rsm
      case drop => have wr := wr l; simp at wr
      case ptr => have wr := wr l; simp at wr
  case conv => aesop

lemma Resolved.subst_im {H : Heap Srt} {m n n' A B s} :
    A :: [] ;; A :⟨.im, s⟩ [] ;; H ⊢ m ▷ n ◁ n' : B ->
    H ⊢ n'.[.null/] ▷ n.[.null/] := by
  intro rsm
  apply rsm.substitution HMerge.empty
  apply AgreeSubst.intro_im
  constructor

lemma Resolved.subst_ex {H1 H2 H3 : Heap Srt} {m n n' t t' A B s} :
    WR H2 -> HLower H2 s -> HMerge H1 H2 H3 ->
    A :: [] ;; A :⟨.ex, s⟩ [] ;; H1 ⊢ m ▷ n ◁ n' : B ->
    H2 ⊢ t' ▷ t ->
    H3 ⊢ n'.[t'/] ▷ n.[t/] := by
  intro wr lw mrg rsm rst
  apply rsm.substitution mrg
  apply AgreeSubst.intro_ex wr lw HMerge.empty.sym
  . assumption
  . constructor
