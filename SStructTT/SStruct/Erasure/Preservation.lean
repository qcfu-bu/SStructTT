import SStructTT.SStruct.Dynamic.Preservation
import SStructTT.SStruct.Erasure.Inversion
import SStructTT.SStruct.Erasure.Step
open ARS SStruct.Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.value_image {Γ Δ} {A m1 : SStruct.Tm Srt} {m2} :
    Γ ;; Δ ⊢ m1 ▷ m2 : A -> Dynamic.Value m1 -> Value m2 := by
  intro ty; induction ty
  all_goals try (solve | intro vl; cases vl | aesop)
  case tup_im => intro vl; cases vl; constructor <;> aesop
  case tup_ex => intro vl; cases vl; constructor <;> aesop

lemma Erased.preservation {A m1 m1' : SStruct.Tm Srt} {m2} :
    [] ;; [] ⊢ m1 ▷ m2 : A -> m1 ~>> m1' ->
    ∃ m2', m2 ~>> m2' ∧ [] ;; [] ⊢ m1' ▷ m2' : A := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty st; induction ty generalizing m1'
  all_goals try trivial
  case app_im m n s erm tyn ih =>
    subst_vars; cases st
    case app_im_M st =>
      have ⟨m', st', erm'⟩ := ih rfl rfl st
      exists .app m' .none; and_intros
      . constructor; assumption
      . apply Erased.app_im erm' tyn
    case beta_im =>
      have ⟨m', e⟩ := erm.lam_im_image; subst e
      replace ⟨sA, erm⟩ := erm.lam_im_inv
      exists m'.[.none/]; and_intros
      . constructor
        constructor
        simp
      . apply erm.subst_im tyn
  case app_ex m1 m1' n1 n1' s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases st
    case app_ex_M st =>
      have ⟨m2', st', erm'⟩ := ihm rfl rfl st
      exists (.app m2' n1'); and_intros
      . apply Step.app_M; assumption
      . apply Erased.app_ex Merge.nil erm' ern
    case app_ex_N st =>
      have ⟨_, _, tyP⟩ := erm.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have rd := st.toStatic ern.toStatic
      have ⟨n2', st', ern'⟩ := ihn rfl rfl st
      exists (.app m1' n2'); and_intros
      . constructor; assumption
      . apply Erased.conv
        apply Static.Conv.subst1
        apply (Star.conv (st.toStatic ern.toStatic)).sym
        apply Erased.app_ex
        . apply Merge.nil
        . assumption
        . assumption
        . apply tyB.subst ern.toStatic
    case beta_ex vl =>
      have ⟨m', c, e⟩ := erm.lam_ex_image; subst_vars
      replace ⟨rA, sA, rs, erm⟩ := erm.lam_ex_inv
      have vl' := ern.value_image vl
      cases rs with
      | extend =>
        exists m'.[n1'/]; and_intros
        . constructor <;> aesop
        . apply erm.subst_ex (Lower.nil sA) Merge.nil ern
      | weaken =>
        exists m'.[.none/]; and_intros
        . constructor <;> aesop
        . apply erm.subst_im ern.toStatic
  all_goals sorry
