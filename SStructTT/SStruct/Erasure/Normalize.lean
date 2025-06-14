import SStructTT.SStruct.Dynamic.Normalize
import SStructTT.SStruct.Erasure.Preservation
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

lemma Erased.value_step {m n : Tm Srt} :
    Value m -> m ~>> n -> False := by
  intro vl st; induction vl generalizing n
  case lam =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.lam_inv] at st; cases st
  case tup ihm ihn =>
    rcases st with ⟨_, rd, st⟩
    have ⟨_, _, _, rd1, rd2⟩ := rd.tup_inv
    subst_vars; cases st
    case tup_M st => apply ihm ⟨_, rd1, st⟩
    case tup_N st => apply ihn ⟨_, rd2, st⟩
  case tt =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.tt_inv] at st; cases st
  case ff =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.ff_inv] at st; cases st
  case ptr =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.ptr_inv] at st; cases st
  case null =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.null_inv] at st; cases st

variable [ord : SrtOrder Srt]

theorem Erased.normalize {A m : SStruct.Tm Srt} {m'} :
    [] ⊢ m ▷ m' :: A -> SN Step m' := by
  intro er
  have sn := er.toDynamic.normalize.star1
  induction sn generalizing m'
  case intro m h ih =>
  constructor; intro n' st'
  have ⟨n, st, ern⟩ := er.preservation st'
  apply ih <;> assumption
