import SStructTT.SStruct.Dynamic.Preservation
import SStructTT.SStruct.Erasure.Inversion
import SStructTT.SStruct.Erasure.Step
open ARS SStruct.Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

-- lemma Erased.preservation {A m1 m1' : SStruct.Tm Srt} {m2} :
--     [] ;; [] ⊢ m1 ▷ m2 : A -> m1 ~>> m1' ->
--     ∃ m2', m2 ~>> m2' ∧ [] ;; [] ⊢ m1' ▷ m2' : A := by
--   generalize e1: [] = Γ
--   generalize e2: [] = Δ
--   intro ty st; induction ty generalizing m1'
--   all_goals try trivial
--   case app_im m n s erm tyn ih =>
--     subst_vars; cases st
--     case app_im_M st =>
--       have ⟨m', st', erm'⟩ := ih rfl rfl st
--       exists .app m' .none; and_intros
--       . constructor; assumption
--       . apply Erased.app_im erm' tyn
--     case beta_im =>
--       replace := erm.lam_im_inv
--       apply tym.subst_im tyn
