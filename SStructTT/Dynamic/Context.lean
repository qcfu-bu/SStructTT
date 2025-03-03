import SStructTT.Defs.SStruct
import SStructTT.Defs.Syntax

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

abbrev Ctx Srt := List (Option (Tm Srt × Srt))
notation:max m " :⟨" s "⟩ " Δ:81 => some (m, s) :: Δ
notation:max "_:" Δ:81 => none :: Δ

inductive Ext : Tm Srt -> Srt -> Ctx Srt -> Ctx Srt -> Prop where
  | ex {A s Δ} :
    Ext A s Δ (some (A, s) :: Δ)
  | wk {A s Δ} :
    s ∈ weaken_set ->
    Ext A s Δ (none :: Δ)

@[scoped aesop safe [constructors]]
inductive Merge : Ctx Srt -> Ctx Srt -> Ctx Srt -> Prop where
  | nil : Merge [] [] []
  | contra {Δ1 Δ2 Δ} A s :
    s ∈ contra_set ->
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨s⟩ Δ1) (A :⟨s⟩ Δ2) (A :⟨s⟩ Δ)
  | left {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (A :⟨s⟩ Δ1) (_: Δ2) (A :⟨s⟩ Δ)
  | right {Δ1 Δ2 Δ} A s :
    Merge Δ1 Δ2 Δ ->
    Merge (_: Δ1) (A :⟨s⟩ Δ2) (A :⟨s⟩ Δ)
  | im {Δ1 Δ2 Δ} :
    Merge Δ1 Δ2 Δ ->
    Merge (_: Δ1) (_: Δ2) (_: Δ)

@[scoped aesop safe [constructors]]
inductive Lower : Ctx Srt -> Srt -> Prop where
  | nil s : Lower [] s
  | ex {Δ A s s'} :
    s' ≤ s ->
    Lower Δ s ->
    Lower (A :⟨s'⟩ Δ) s
  | im {Δ s} :
    Lower Δ s ->
    Lower (_: Δ) s

notation Δ:60 " !≤ " s:60 => Lower Δ s

@[scoped aesop safe [constructors]]
inductive Has : Ctx Srt -> Var -> Srt -> Tm Srt -> Prop where
  | nil {Δ A s} :
    Δ.Forall (. = none) ->
    Has (A :⟨s⟩ Δ) 0 s A.[shift 1]
  | cons {Δ A x s} :
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
  case im A _ s' ih =>
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

lemma Merge.sym {Δ1 Δ2 Δ : Ctx Srt} : Merge Δ1 Δ2 Δ -> Merge Δ2 Δ1 Δ := by
  intro mrg; induction mrg
  all_goals aesop (add safe Merge)

lemma Merge.none {Δ1 Δ2 Δ : Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Δ1.Forall (. = none) -> Δ2 = Δ := by
  intro mrg h; induction mrg
  all_goals aesop

lemma Merge.compose {Δ1 Δ2 Δa Δb Δx Δy Δ : Ctx Srt} {s} :
    Δa !≤ s -> s ∈ contra_set ->
    Merge Δa Δb Δ ->
    Merge Δx Δa Δ1 ->
    Merge Δy Δa Δ2 ->
    Merge Δx Δy Δb ->
    Merge Δ1 Δ2 Δ := by
  intro lw h mrg mrg1 mrg2 mrg3
  induction mrg1 generalizing Δ2 Δb Δy Δ s
  case nil => cases mrg; cases mrg2; aesop
  case contra ih =>
    cases lw; cases mrg with
    | contra =>
      cases mrg2 with
      | contra =>
        cases mrg3; constructor
        . assumption
        . apply ih <;> assumption
      | right =>
        cases mrg3; constructor
        . assumption
        . apply ih <;> assumption
    | left =>
      cases mrg2 with
      | contra => cases mrg3
      | right => cases mrg3
  case left ih =>
    cases lw; cases mrg with
    | right =>
      cases mrg2 with
      | left =>
        cases mrg3; constructor
        . assumption
        . apply ih <;> assumption
      | im =>
        cases mrg3; constructor
        apply ih <;> assumption
    | im =>
      cases mrg2 with
      | left => cases mrg3
      | im => cases mrg3
  case right ih =>
    cases lw; cases mrg with
    | contra =>
      cases mrg2 with
      | contra =>
        cases mrg3; constructor
        . assumption
        . apply ih <;> assumption
      | right => cases mrg3
    | left =>
      cases mrg2 with
      | contra => cases mrg3
      | right =>
        cases mrg3; constructor
        . apply contra_set.lower <;> assumption
        . apply ih <;> assumption
  case im ih =>
    cases lw; cases mrg with
    | right =>
      cases mrg2 with
      | left =>
        cases mrg3; constructor
        apply ih <;> assumption
      | im => cases mrg3
    | im =>
      cases mrg2 with
      | left => cases mrg3
      | im =>
        cases mrg3; constructor
        apply ih <;> assumption

lemma Merge.split {Δ1 Δ2 Δ Δa Δb : Ctx Srt} :
    Merge Δ1 Δ2 Δ ->
    Merge Δa Δb Δ1 ->
    ∃ Δc, Merge Δa Δ2 Δc ∧ Merge Δc Δb Δ := by
  intro mrg1 mrg2; induction mrg1 generalizing Δa Δb
  case nil => cases mrg2; exists []; aesop
  case contra A s h mrg ih =>
    cases mrg2 with
    | contra _ _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨s⟩ Δc; aesop
    | left _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨s⟩ Δc; aesop
    | right _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨s⟩ Δc; aesop
  case left A s mrg ih =>
    cases mrg2 with
    | contra _ _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨s⟩ Δc; aesop
    | left _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨s⟩ Δc; aesop
    | right _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists _: Δc; aesop
  case right A s mrg ih =>
    rcases mrg2 with _ | _ | _ | _ | ⟨mrg⟩
    have ⟨Δc, mrg1, mrg2⟩ := ih mrg
    exists A :⟨s⟩ Δc; aesop
  case im mrg ih =>
    rcases mrg2 with _ | _ | _ | _ | ⟨mrg⟩
    have ⟨Δc, mrg1, mrg2⟩ := ih mrg
    exists _: Δc; aesop

lemma Merge.distr {Δ1 Δ2 Δ Δ11 Δ12 Δ21 Δ22 : Ctx Srt} :
    Merge Δ1 Δ2 Δ ->
    Merge Δ11 Δ12 Δ1 ->
    Merge Δ21 Δ22 Δ2 ->
    ∃ Δ1' Δ2',
      Merge Δ1' Δ2' Δ ∧
      Merge Δ11 Δ21 Δ1' ∧
      Merge Δ12 Δ22 Δ2' := by
  intro mrg1 mrg2 mrg3; induction mrg1 generalizing Δ11 Δ12 Δ21 Δ22
  case nil =>
    cases mrg2; cases mrg3
    exists [], []; aesop
  case contra A s h mrg ih =>
    cases mrg2 with
    | contra _ _ _ mrg2 =>
      cases mrg3 with
      | contra _ _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
      | left _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
      | right _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
    | left _ _ mrg2 =>
      cases mrg3 with
      | contra _ _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
      | left _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', _: Δ2'; aesop
      | right _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
    | right _ _ mrg2 =>
      cases mrg3 with
      | contra _ _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
      | left _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
      | right _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists _: Δ1', A :⟨s⟩ Δ2'; aesop
  case left A s mrg ih =>
    cases mrg2 with
    | contra _ _ _ mrg2 =>
      cases mrg3 with
      | im mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
    | left _ _ mrg2 =>
      cases mrg3 with
      | im mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', _: Δ2'; aesop
    | right _ _ mrg2 =>
      cases mrg3 with
      | im mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists _: Δ1', A :⟨s⟩ Δ2'; aesop
  case right A s mrg ih =>
    cases mrg2 with
    | im mrg2 =>
      cases mrg3 with
      | contra _ _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', A :⟨s⟩ Δ2'; aesop
      | left _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists A :⟨s⟩ Δ1', _: Δ2'; aesop
      | right _ _ mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists _: Δ1', A :⟨s⟩ Δ2'; aesop
  case im mrg ih =>
    cases mrg2 with
    | im mrg2 =>
      cases mrg3 with
      | im mrg3 =>
        have ⟨Δ1', Δ2', mrg1', mrg2', mrg3'⟩ := ih mrg2 mrg3
        exists _: Δ1', _: Δ2'; aesop
