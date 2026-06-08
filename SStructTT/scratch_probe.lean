import SStructTT.SStruct.Runtime.Resolution
open Autosubst Autosubst.Notation
namespace SStruct.Extraction
variable {Srt : Type}
def IdRename (i : Var) (ξ : Var -> Var) : Prop := ∀ x, x < i -> ξ x = x
example {m : Tm Srt} {i ξ} (cl : Closed i m) (idr : IdRename i ξ) : m = m⟨ξ⟩ := by
  intro; induction m generalizing i ξ
  all_goals simp_all; try (solve| aesop)
  case lam ih => asimp; trace_state; sorry
  all_goals sorry
