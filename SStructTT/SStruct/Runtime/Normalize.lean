import SStructTT.SStruct.Erasure.Normalize
import SStructTT.SStruct.Runtime.Preservation
open ARS

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

theorem Resolved.normalize {H : Heap Srt} {a b c A} :
    [] ;; H ⊢ a ▷ b ◁ c :: A -> SN Step (H, c) := by
  intro rs
  have ⟨er, rs0⟩ := rs; clear rs0
  have sn := er.normalize
  induction sn generalizing H a c
  case intro m h ih =>
  constructor; intro ⟨H', c'⟩ st'
  have ⟨a', b', rs', _, st⟩ := rs.preservation st'
  apply ih <;> try assumption
  cases rs'; assumption
