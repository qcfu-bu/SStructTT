import SStructTT.SStruct.Runtime.Preservation0
import SStructTT.SStruct.Runtime.Preservation1
import SStructTT.SStruct.Runtime.Preservation2
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservation {H1 H1' : Heap Srt} {a b c c' A} :
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> (H1, c) ~>> (H1', c') ->
    ∃ a' b', [] ;; [] ;; H1' ⊢ a' ▷ b' ◁ c' : A ∧ a ~>>1 a' ∧ b ~>> b' := by
  intro rs st
  cases st
  case intro a b rd0 rd1 st =>
  rcases a with ⟨H1, a⟩
  rcases b with ⟨H2, b⟩
  have ⟨c, rs, rd⟩ := rs.preservation0' rd0
  have rs := rs.preservation1' rd1
  have ⟨a, b, rs, st1, st2⟩ := rs.preservation2 st
  existsi a, b; and_intros
  . assumption
  . assumption
  . constructor
    assumption
    assumption
