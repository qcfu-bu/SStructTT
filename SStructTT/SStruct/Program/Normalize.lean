import SStructTT.SStruct.Logical.Normalize
import SStructTT.SStruct.Program.Preservation
open ARS SStruct.Logical

namespace SStruct.Program
variable {Srt : Type} [ord : SrtOrder Srt]

theorem Typed.normalize {A m : Tm Srt} :
    [] ⊢ m :: A -> SN Step m := by
  intro ty
  have sn := ty.toLogical.normalize.star1
  induction sn
  case intro m h ih =>
    constructor; intro n st
    have rd := st.toLogical1 ty.toLogical
    replace ty := ty.preservation st
    apply ih <;> assumption
