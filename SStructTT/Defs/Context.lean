import SStructTT.Defs.Syntax

variable {Srt : Type}

@[reducible]def Ctx := List (Tm Srt × Rlv × Srt)

inductive Has : @Ctx Srt -> Var -> Tm Srt -> Rlv -> Srt -> Prop where
  | zero Γ A r s :
    Has ((A, r, s) :: Γ) 0 A.[ren .succ] r s
  | succ Γ A E r s x :
    Has Γ x A r s ->
    Has (E :: Γ) x.succ A.[ren .succ] r s

notation:60 A:60 ":⟨" r:50 "," s:50 "⟩" Γ:60 => (A, r, s) :: Γ
