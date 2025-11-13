import SStructTT.SStruct.Syntax

namespace SStruct.Logical
variable {Srt : Type}
def Ctx Srt := List (Tm Srt)

@[scoped aesop safe [constructors]]
inductive Has : Ctx Srt -> Var -> Tm Srt -> Prop where
  | zero Γ A :
    Has (A :: Γ) 0 A.[shift 1]
  | succ Γ A B x :
    Has Γ x A ->
    Has (B :: Γ) (x + 1) A.[shift 1]

lemma Has.var_lt_length {Γ : Ctx Srt} {x A} :
    Has Γ x A -> x < Γ.length := by
  intro hs; induction hs <;> aesop
