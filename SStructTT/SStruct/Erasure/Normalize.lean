import SStructTT.SStruct.Dynamic.Normalize
import SStructTT.SStruct.Erasure.Preservation
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

lemma Erased.value_step {m n : Tm Srt} :
    Value m -> m ~>> n -> False := by
  intro vl st; induction vl generalizing n
  all_goals cases st <;> aesop

variable [ord : SrtOrder Srt]

theorem Erased.normalize {A m : SStruct.Tm Srt} {m'} :
    [] ;; [] ⊢ m ▷ m' : A -> SN Step m' := by
  intro er
  have sn := er.toDynamic.normalize
  induction sn generalizing m'
  case intro m h ih =>
  constructor; intro n' st'
  have ⟨n, st, ern⟩ := er.preservation st'
  apply ih <;> assumption
