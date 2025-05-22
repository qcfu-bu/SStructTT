import SStructTT.SStruct.Dynamic.Normalize
import SStructTT.SStruct.Erasure.Preservation
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

lemma Erased.value_step {m n : Tm Srt} :
    Value m -> m ~>> n -> False := by
  intro vl st; induction vl generalizing n
  case lam =>
    rcases st with ⟨rd, st⟩
    rw[Red0.lam_inv rd] at st
    cases st
  case tup ihm ihn =>
    rcases st with ⟨rd, st⟩
    have ⟨_, _, _, rd1, rd2⟩ := Red0.tup_inv rd
    subst_vars
    cases st
    case tup_M st => apply ihm (Step.intro rd1 st)
    case tup_N st => apply ihn (Step.intro rd2 st)
  case tt =>
    rcases st with ⟨rd, st⟩
    rw[Red0.tt_inv rd] at st
    cases st
  case ff =>
    rcases st with ⟨rd, st⟩
    rw[Red0.ff_inv rd] at st
    cases st
  case ptr =>
    rcases st with ⟨rd, st⟩
    rw[Red0.ptr_inv rd] at st
    cases st
  case null =>
    rcases st with ⟨rd, st⟩
    rw[Red0.null_inv rd] at st
    cases st

variable [ord : SrtOrder Srt]

theorem Erased.normalize {A m : SStruct.Tm Srt} {m'} :
    [] ;; [] ⊢ m ▷ m' : A -> SN Step m' := by
  intro er
  have sn := er.toDynamic.normalize
  induction sn generalizing m'
  case intro m h ih =>
  constructor; intro n' st'
  have ⟨n, st, ern⟩ := er.preservation1 st'
  apply ih <;> assumption
