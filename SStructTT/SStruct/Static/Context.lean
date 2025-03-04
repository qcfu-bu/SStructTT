import SStructTT.SStruct.Syntax

namespace Static
abbrev Ctx Srt := List (Tm Srt)

@[scoped aesop safe [constructors]]
inductive Has {Srt} : Ctx Srt -> Var -> Tm Srt -> Prop where
  | zero Γ A :
    Has (A :: Γ) 0 A.[shift 1]
  | succ Γ A B x :
    Has Γ x A ->
    Has (B :: Γ) (x + 1) A.[shift 1]
