import SStructTT.SStruct.Runtime.Preservation0
import SStructTT.SStruct.Runtime.Preservation1
import SStructTT.SStruct.Runtime.Preservation2
open ARS

namespace SStruct.Extraction
namespace Runtime
open Program
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservationX {H H' : Heap Srt} {a b c c' A} :
    [] ;; H ⊢ a ▷ b ◁ c :: A -> Red01 (H, c) (H', c') ->
    ∃ b', [] ;; H' ⊢ a ▷ b' ◁ c' :: A ∧ Extraction.Red0 b b' := by
  generalize e: (H', c') = t
  intro rs rd; induction rd generalizing H' a b c' A
  case R => cases e; existsi b; aesop
  case SE x y rd st ih =>
    subst_vars
    rcases x with ⟨H2, c'⟩
    have ⟨b', rs, rd⟩ := ih rfl rs
    cases st with
    | inl st =>
      have ⟨b', rs, st⟩ := rs.preservation0 st
      existsi b'; and_intros
      . assumption
      . apply Star.SE rd st
    | inr st =>
      have rs := rs.preservation1 st
      exists b'

theorem Resolved.preservation {H H' : Heap Srt} {a b c c' A} :
    [] ;; H ⊢ a ▷ b ◁ c :: A -> (H, c) ~>> (H', c') ->
    ∃ a' b', [] ;; H' ⊢ a' ▷ b' ◁ c' :: A ∧ a ~>>1 a' ∧ b ~>> b' := by
  intro rs st
  rcases st with @⟨x, rd, ms, st⟩
  rcases x with ⟨H1, a⟩
  have ⟨c, rs, rd⟩ := rs.preservationX rd
  have ⟨a', b', rs, st, rd⟩ := rs.preservation2 st
  existsi a', b'; and_intros
  . assumption
  . assumption
  . constructor; and_intros <;> assumption
