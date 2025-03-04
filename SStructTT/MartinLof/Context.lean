import SStructTT.MartinLof.Syntax

namespace MartinLof
abbrev Ctx := List Tm

@[scoped aesop safe [constructors]]
inductive Has : Ctx -> Var -> Tm -> Prop where
  | zero Γ A :
    Has (A :: Γ) 0 A.[shift 1]
  | succ Γ A B x :
    Has Γ x A ->
    Has (B :: Γ) (x + 1) A.[shift 1]
