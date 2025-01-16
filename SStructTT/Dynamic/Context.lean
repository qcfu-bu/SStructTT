import SStructTT.Defs.SStruct
import SStructTT.Defs.Syntax

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

abbrev Ctx Srt := List (Option (Tm Srt × Srt))
notation m " :⟨" s "⟩" Δ => some (m, s) :: Δ
notation "□" => none

inductive Merge : Ctx Srt -> Ctx Srt -> Ctx Srt -> Prop where
  | nil : Merge [] [] []
  | contra {Δ1 Δ2 Δ} A s :
    s ∈ contra_set ->
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨s⟩ Δ1) (A :⟨s⟩ Δ2) (A :⟨s⟩ Δ)
  | left {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨s⟩ Δ1) (□ :: Δ2)   (A :⟨s⟩ Δ)
  | right {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (□ :: Δ1) (A :⟨s⟩ Δ2) (A :⟨s⟩ Δ)
  | implicit {Δ1 Δ2 Δ} :
    Merge Δ1 Δ2 Δ ->
    Merge (□ :: Δ1) (□ :: Δ2) (□ :: Δ)

notation Δ1 " ∪ " Δ2 " => " Δ => Merge Δ1 Δ2 Δ

inductive Key : Ctx Srt -> Srt -> Prop where
  | nil s : Key [] s
  | explicit Δ A s s0 :
    s0 ≤ s ->
    Key Δ s ->
    Key (A :⟨s0⟩ Δ) s
  | implicit Δ s :
    Key Δ s ->
    Key (□ :: Δ) s

notation Δ " ▹ " s => Key Δ s

/-
Inductive dyn_has : dyn_ctx -> var -> sort -> term -> Prop :=
| dyn_has_O Δ A s :
  Δ ▷ U ->
  dyn_has (A .{s} Δ) 0 s A.[ren (+1)]
| dyn_has_S Δ A B x s :
  dyn_has Δ x s A ->
  dyn_has (B :U Δ) x.+1 s A.[ren (+1)]
| dyn_has_N Δ A x s :
  dyn_has Δ x s A ->
  dyn_has (_: Δ) x.+1 s A.[ren (+1)].
-/

-- inductive Has : Ctx Srt -> Var -> Srt -> Tm Srt -> Prop where
--   | zero Δ A s
