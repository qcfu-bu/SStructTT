import SStructTT.Defs.SStruct
import SStructTT.Defs.Syntax

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

abbrev Ctx Srt := List (Tm Srt × Rlv × Srt)
notation:max m " :⟨" r ", " s "⟩ " Δ:81 => (m, r, s) :: Δ

@[scoped aesop safe [constructors]]
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
  | im {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨.im, s⟩ Δ1) (A :⟨.im, s⟩ Δ2) (A :⟨.im, s⟩ Δ)

notation:80 Δ1:81 " ∪ " Δ2:81 " => " Δ:81 => Merge Δ1 Δ2 Δ

@[scoped aesop safe [constructors]]
inductive Lower : Ctx Srt -> Srt -> Prop where
  | nil s : Lower [] s
  | ex {Δ A s s'} :
    s' ≤ s ->
    Lower Δ s ->
    Lower (A :⟨.ex, s'⟩ Δ) s
  | im {Δ A s s'} :
    Lower Δ s ->
    Lower (A :⟨.im, s'⟩ Δ) s

notation Δ:60 " !≤ " s:60 => Lower Δ s

@[scoped aesop safe [constructors]]
inductive Has : Ctx Srt -> Var -> Srt -> Tm Srt -> Prop where
  | zero {Δ A s} :
    Weak Δ ->
    Has (A :⟨s⟩ Δ) 0 s A.[shift 1]
  | ex {Δ A B x s s'} :
    s' ∈ weaken_set ->
    Has Δ x s A ->
    Has (B :⟨s'⟩ Δ) (x + 1) s A.[shift 1]
  | im {Δ A x s} :
    Has Δ x s A ->
    Has (_: Δ) (x + 1) s A.[shift 1]

lemma Lower.split_s0 {Δ : Ctx Srt} :
    Lower Δ s0 -> ∃ Δ1 Δ2, Lower Δ1 s0 ∧ Lower Δ2 s0 ∧ Merge Δ1 Δ2 Δ := by
  generalize e: inst.s0 = s
  intro l; induction l
  case nil =>
    subst_vars
    exists [], []; aesop
  case ex A _ s' h _ ih =>
    subst_vars
    have := inst.le_antisymm _ _ h (inst.s0_min s')
    subst_vars
    have ⟨Δ1, Δ2, l1, l2, mrg⟩ := ih rfl
    exists A :⟨s0⟩ Δ1, A :⟨s0⟩ Δ2
    and_intros
    . constructor <;> assumption
    . constructor <;> assumption
    . constructor
      apply inst.s0_contra
      assumption
  case im ih =>
    subst_vars
    have ⟨Δ1, Δ2, l1, l2, mrg⟩ := ih rfl
    exists _: Δ1, _: Δ2
    and_intros
    . constructor; assumption
    . constructor; assumption
    . constructor; assumption

lemma Merge.lower {Δ1 Δ2 Δ : Ctx Srt} s :
    Merge Δ1 Δ2 Δ -> Lower Δ1 s -> Lower Δ2 s -> Lower Δ s := by
  intro mrg; induction mrg
  case nil =>
    intros; constructor
  case contra ih =>
    intro l1 l2; cases l1; cases l2
    apply Lower.ex
    . assumption
    . apply ih <;> assumption
  case left ih =>
    intro l1 l2; cases l1; cases l2
    apply Lower.ex
    . assumption
    . apply ih <;> assumption
  case right ih =>
    intro l1 l2; cases l1; cases l2
    apply Lower.ex
    . assumption
    . apply ih <;> assumption
  case im ih =>
    intro l1 l2; cases l1; cases l2
    apply Lower.im
    apply ih <;> assumption
