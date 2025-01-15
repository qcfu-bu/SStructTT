import SStructTT.Defs.SStruct
import SStructTT.Defs.Syntax

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

abbrev Ctx Srt := List (Tm Srt × Rlv × Srt)
notation m " :⟨" r "," s "⟩" Δ => (m, r, s) :: Δ

inductive Merge : Ctx Srt -> Ctx Srt -> Ctx Srt -> Prop where
  | nil : Merge [] [] []
  | contra {Δ1 Δ2 Δ} A s :
    s ∈ contra_set ->
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨.ex, s⟩ Δ1) (A :⟨.ex, s⟩ Δ2) (A :⟨.ex, s⟩ Δ)
  | left {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨.ex, s⟩ Δ1) (A :⟨.im, s⟩ Δ2) (A :⟨.ex, s⟩ Δ)
  | right {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨.im, s⟩ Δ1) (A :⟨.ex, s⟩ Δ2) (A :⟨.ex, s⟩ Δ)
  | implicit {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨.im, s⟩ Δ1) (A :⟨.im, s⟩ Δ2) (A :⟨.im, s⟩ Δ)

notation Δ1 " ∪ " Δ2 " => " Δ => Merge Δ1 Δ2 Δ
