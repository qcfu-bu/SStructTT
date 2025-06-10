import SStructTT.SStruct.Static.Normalize
import SStructTT.SStruct.Dynamic.Preservation
open ARS SStruct.Static

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

theorem Typed.normalize {A m : Tm Srt} :
    [] ⊢ m :: A -> SN Step m := by
  intro ty
  have sn := ty.toStatic.normalize.star1
  induction sn
  case intro m h ih =>
    constructor; intro n st
    have rd := st.toStatic1 ty.toStatic
    replace ty := ty.preservation st
    apply ih <;> assumption
