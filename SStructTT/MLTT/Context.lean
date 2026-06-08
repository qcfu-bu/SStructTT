import SStructTT.MLTT.Syntax

open Autosubst Autosubst.Notation

namespace MLTT
abbrev Ctx := List Tm

@[scoped aesop safe [constructors]]
inductive Has : Ctx -> Var -> Tm -> Prop where
  | zero Γ A :
    Has (A :: Γ) 0 A⟨↑⟩
  | succ Γ A B x :
    Has Γ x A ->
    Has (B :: Γ) (x + 1) A⟨↑⟩
