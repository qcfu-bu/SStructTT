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
  | wk_im {Δ H σ σ' A m m' s} :
    AgreeSubst σ σ' 0 Δ H ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.im, s⟩ Δ) H
  | wk_ex {Δ H1 H2 H3 σ σ' m m' A s} :
    WR H2 ->
    HLower H2 s ->
    HMerge H1 H2 H3 ->
    H2 ;; m ▷ m' ->
    AgreeSubst σ σ' 0 Δ H1 ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.ex, s⟩ Δ) H3

lemma AgreeSubst.lower_image {Δ : Ctx Srt} {H σ σ' x s} :
    AgreeSubst σ σ' x Δ H -> Lower Δ s -> HLower H s := by
  intro agr lw; induction agr generalizing s
  case nil hw =>
    apply hw.trans
    apply ord.e_min
  case cons => cases lw <;> aesop
  case wk_im => cases lw; aesop
  case wk_ex wr hw2 mrg erm agr ih =>
    cases lw; case ex le lw =>
    have hw1 := ih lw
    replace hw2 := hw2.trans le
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
  case wk_ex wr2 _ mrg _ _ wr1 =>
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
  case rw => asimp; aesop

lemma Resolve.id_rename {H : Heap Srt} {m m' i ξ} :
    H ;; m ▷ m' -> WR H -> IdRename i ξ -> H ;; m.[ren ξ] ▷ m'.[ren ξ] := by
  intro rs wr idr; induction rs generalizing i ξ
  case var => sorry
  case lam => sorry
  case app => sorry
  case tup => sorry
  case prj => sorry
  case tt => sorry
  case ff => sorry
  case ite => sorry
  case rw => sorry
  case ptr => sorry
  case null => sorry
