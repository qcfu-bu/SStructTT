import SStructTT.SStruct.Static.Normalization
import SStructTT.SStruct.Dynamic.Preservation
open ARS SStruct.Static

namespace SStruct.Dynamic
variable {Srt : Type}

def Ext (x z : Tm Srt) : Prop :=
  ∃ y, Static.Step x y ∧ Star Static.Step y z

lemma static_sn_ext' {a : Tm Srt} :
    SN Static.Step a -> ∀ {b}, a ~>* b -> SN Ext b := by
  intro sn; induction sn
  case intro h ih =>
    intro a rd1
    constructor
    intro b ⟨c, st1, rd2⟩
    match Star.ES_split rd1 with
    | .inl _ => subst_vars; apply ih st1 rd2
    | .inr ⟨d, st2, rd3⟩ =>
      apply ih st2
      apply rd3.trans
      apply (Star.one st1).trans rd2

lemma static_sn_ext {a : Tm Srt} :
    SN Static.Step a -> SN Ext a := by
  intro sn; apply static_sn_ext' sn Star.R

variable [ord : SrtOrder Srt]

lemma ext_sn_dynamic' {A a : Tm Srt} :
    [] ;; [] ⊢ a : A -> SN Ext a -> ∀ {b}, a ~>>* b -> SN Step b := by
  intro ty sn; induction sn generalizing A
  case intro b h ih =>
    intro c rd1
    constructor
    intro d st1
    match Star.ES_split rd1 with
    | .inl _ =>
      subst_vars
      apply ih
      . apply st1.toStatic' ty.toStatic
      . apply ty.preservation st1
      . apply Star.R
    | .inr ⟨e, st2, rd2⟩ =>
      apply ih
      . apply st2.toStatic' ty.toStatic
      . apply ty.preservation st2
      . apply Star.SE rd2 st1

lemma ext_sn_dynamic {A a : Tm Srt} :
    [] ;; [] ⊢ a : A -> SN Ext a -> SN Step a := by
  intro sn ty; apply ext_sn_dynamic' sn ty Star.R

theorem Typed.normalization {A m : Tm Srt} :
    [] ;; [] ⊢ m : A -> SN Step m := by
  intro ty
  have sn := ty.toStatic.normalization
  have sn := static_sn_ext sn
  have sn := ext_sn_dynamic ty sn
  exact sn
