import SStructTT.Static.Typed

namespace Static
variable {Srt : Type} [SStruct Srt]

inductive AgreeRen : (Var -> Var) -> Ctx Srt -> Ctx Srt -> Prop where
  | nil {ξ} :
    AgreeRen ξ  [] []
  | cons Γ Γ' A s i ξ :
    Typed Γ A (.srt s i) ->
    AgreeRen ξ Γ Γ' ->
    AgreeRen (upren ξ) (A :: Γ) (A.[ren ξ] :: Γ')
  | wk Γ Γ' A s i ξ :
    Typed Γ' A (.srt s i) ->
    AgreeRen ξ Γ Γ' ->
    AgreeRen (ξ !>> (.+1)) Γ (A :: Γ')
