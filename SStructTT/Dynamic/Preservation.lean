import SStructTT.Dynamic.Step
import SStructTT.Dynamic.Inversion
open ARS Static

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

lemma Step.toStatic {A m n : Tm Srt} :
    [] ⊢ m : A -> m ~>> n -> m ~>* n := by
  sorry

theorem Typed.preservation {A m m' : Tm Srt} :
    [] ;; [] ⊢ m : A -> m ~>> m' -> [] ;; [] ⊢ m' : A := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty st; induction ty generalizing m'
  all_goals try trivial
  case app_im m n s tym tyn ih =>
    subst_vars; cases st
    case app_im_M st =>
      have tym' := ih rfl rfl st
      apply Typed.app_im tym' tyn
    case beta_im =>
      replace ⟨sA, tym⟩ := tym.lam_im_inv
      apply tym.subst_im tyn
  case app_ex Δ1 Δ2 Δ A B m n s mrg tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case app_ex_M st =>
      have tym' := ihm rfl rfl st
      apply Typed.app_ex Merge.nil tym' tyn
    case app_ex_N st =>
      have ⟨_, _, tyP⟩ := tym.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have rd := st.toStatic tyn.toStatic
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tyn.toStatic)).sym
      . apply Typed.app_ex
        . apply Merge.nil
        . assumption
        . apply ihn rfl rfl st
      . apply tyB.subst tyn.toStatic
    case beta_ex =>
      replace ⟨rA, sA, rs, tym⟩ := tym.lam_ex_inv
      cases rs with
      | extend => apply tym.subst_ex (Lower.nil sA) Merge.nil tyn
      | weaken => apply tym.subst_im tyn.toStatic
  all_goals sorry
