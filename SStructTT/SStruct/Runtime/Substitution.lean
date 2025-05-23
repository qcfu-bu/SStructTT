import SStructTT.SStruct.Runtime.Resolution

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst :
  (Var -> Tm Srt) -> (Var -> Tm Srt) -> Nat -> Ctx Srt -> Heap Srt -> Prop
where
  | nil {H σ σ'} :
    WR H ->
    HLower H ord.e ->
    AgreeSubst σ σ' 0 [] H
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
    H2 ;; m ▷ m' ->
    AgreeSubst σ σ' 0 Δ H1 ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.ex, s⟩ Δ) H3

lemma AgreeSubst.implicit_image {Δ : Ctx Srt} {H σ σ' x} :
    AgreeSubst σ σ' x Δ H -> Implicit Δ -> HLower H ord.e := by
  intro agr im; induction agr
  case nil => assumption
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
  case nil hw =>
    apply hw.weaken (ord.e_min _)
  case cons => cases lw <;> aesop
  case intro_im => cases lw; aesop
  case intro_ex wr hw2 mrg erm agr ih =>
    cases lw; case ex le lw =>
    have hw1 := ih lw
    replace hw2 := hw2.weaken le
    apply mrg.lower_image hw1 hw2

lemma AgreeSubst.subst_var {Δ : Ctx Srt} {H σ σ' i x} :
    AgreeSubst σ σ' i Δ H -> x < i -> .var x = σ x := by
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
    AgreeSubst σ σ' i Δ H -> NF x m -> x ≤ i -> m = m.[σ] := by
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
  case intro_ex wr2 _ mrg _ _ wr1 =>
    apply mrg.merge_wr wr1 wr2

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

lemma Resolve.id_rename {H : Heap Srt} {m m' i ξ} :
    H ;; m ▷ m' -> WR H -> IdRename i ξ -> H ;; m.[ren ξ] ▷ m'.[ren ξ] := by
  intro rs wr idr; induction rs generalizing i ξ
  case var => asimp; constructor; aesop
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
  case drop mrg rsm rsn ihm ihn =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 idr
    replace ihn := ihn wr2 idr
    asimp; apply Resolve.drop mrg ihm ihn
  case ptr lk erm ihm =>
    asimp
    have nfm := lk.nf wr
    have wr' := lk.wr_image wr
    have nfm' := (erm.nf_image wr' nfm).weaken (zero_le i)
    rw[<-nfm'.id_rename idr]
    constructor <;> assumption
  case null => asimp; constructor; assumption

lemma AgreeSubst.has {Δ : Ctx Srt} {H σ σ' x i s A} :
    AgreeSubst σ σ' i Δ H -> Has Δ x s A -> H ;; σ x ▷ σ' x := by
  intro agr hs; induction agr generalizing x s A
  case nil => cases hs
  case cons agr ih =>
    cases hs
    case nil im =>
      have lw := agr.implicit_image im
      asimp; constructor; assumption
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
    have lw := agr.implicit_image im
    apply rsm.weaken_merge mrg.sym lw

lemma AgreeSubst.split {Δ1 Δ2 Δ3 : Ctx Srt} {H3 σ σ' x} :
    AgreeSubst σ σ' x Δ3 H3 -> Merge Δ1 Δ2 Δ3 ->
    ∃ H1 H2,
      HMerge H1 H2 H3 ∧
      AgreeSubst σ σ' x Δ1 H1 ∧
      AgreeSubst σ σ' x Δ2 H2 := by
  intro agr mrg; induction agr generalizing Δ1 Δ2
  case nil wr lw =>
    cases mrg
    have ⟨H1, H2, lw1, lw2, mrg⟩ := lw.split_lower ord.e_contra
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    exists H1, H2; and_intros
    . assumption
    . constructor <;> assumption
    . constructor <;> assumption
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
