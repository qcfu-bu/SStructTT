import SStructTT.SStruct.SrtOrder
import SStructTT.SStruct.Syntax

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

abbrev Ctx Srt := List (Tm Srt × Rlv × Srt)
notation:max A " :⟨" r ", " s "⟩ " Δ:81 => List.cons (A, r, s) Δ

@[scoped aesop safe [constructors]]
inductive Merge : Ctx Srt -> Ctx Srt -> Ctx Srt -> Prop where
  | nil : Merge [] [] []
  | contra {Δ1 Δ2 Δ} A s :
    s ∈ ord.contra_set ->
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

@[simp]def Implicit (Δ : Ctx Srt) : Prop :=
  Δ.Forall (fun x => x.2.1 = .im)

inductive Stack : Ctx Srt -> Nat -> Prop where
  | nil {Δ n} : Implicit Δ -> Stack Δ n
  | cons {Δ A r s x} :
    Stack Δ x ->
    Stack (A :⟨r, s⟩ Δ) (x + 1)

@[scoped aesop safe [constructors]]
inductive Has : Ctx Srt -> Var -> Srt -> Tm Srt -> Prop where
  | nil {Δ A s} :
    Implicit Δ ->
    Has (A :⟨.ex, s⟩ Δ) 0 s A.[shift 1]
  | cons {Δ A B x s s'} :
    Has Δ x s A ->
    Has (B :⟨.im, s'⟩ Δ) (x + 1) s A.[shift 1]

@[simp]def Ctx.toImplicit (Δ : Ctx Srt) : Ctx Srt :=
  Δ.map fun ⟨m, _, s⟩ => ⟨m, .im, s⟩

omit ord in
lemma Implicit.toImplicit (Δ : Ctx Srt) : Implicit Δ.toImplicit := by
  induction Δ <;> aesop

omit ord in
lemma Has.stack {Δ : Ctx Srt} {x s i A} :
    Has Δ x s A -> x < i -> Stack Δ i := by
  intro hs lt; induction hs generalizing i
  case nil =>
    cases i <;> try trivial
    apply Stack.cons
    constructor
    assumption
  case cons ih =>
    cases i <;> try trivial
    simp at lt
    apply Stack.cons (ih lt)

omit ord in
lemma Stack.toImplicit {Δ : Ctx Srt} : Stack Δ 0 -> Implicit Δ := by
  intro st; cases st; assumption

lemma Lower.split_e {Δ : Ctx Srt} :
    Lower Δ ord.e -> ∃ Δ1 Δ2, Lower Δ1 ord.e ∧ Lower Δ2 ord.e ∧ Merge Δ1 Δ2 Δ := by
  generalize e: ord.e = s
  intro l; induction l
  case nil =>
    subst_vars
    exists [], []; aesop
  case ex A _ s' h _ ih =>
    subst_vars
    have := ord.le_antisymm _ _ h (ord.e_min s')
    subst_vars
    have ⟨Δ1, Δ2, l1, l2, mrg⟩ := ih rfl
    exists A :⟨.ex, ord.e⟩ Δ1, A :⟨.ex, ord.e⟩ Δ2
    and_intros
    . constructor <;> assumption
    . constructor <;> assumption
    . constructor
      apply ord.e_contra
      assumption
  case im A s s' lw ih =>
    subst_vars
    have ⟨Δ1, Δ2, l1, l2, mrg⟩ := ih rfl
    exists A :⟨.im, s'⟩ Δ1, A :⟨.im, s'⟩ Δ2
    and_intros
    . constructor; assumption
    . constructor; assumption
    . constructor; assumption

lemma Lower.trans {Δ : Ctx Srt} {s1 s2} :
    Lower Δ s1 -> s1 ≤ s2 -> Lower Δ s2 := by
  intro lw le2; induction lw generalizing s2
  case nil => constructor
  case ex le1 _ ih =>
    constructor
    apply le1.trans le2
    apply ih le2
  case im ih =>
    constructor
    apply ih le2

lemma Lower.implicit {Δ : Ctx Srt} {s} : Implicit Δ -> Lower Δ s := by
  intro im; induction Δ
  case nil => constructor
  case cons hd tl ih =>
    have ⟨m, r, s⟩ := hd
    simp at im; have ⟨e, ih⟩ := im
    subst_vars; constructor; aesop

lemma Has.lower {Δ : Ctx Srt} {x s A} :
    Has Δ x s A -> Lower Δ s := by
  intro hs; induction hs
  case nil ih =>
    constructor; simp
    apply Lower.implicit ih
  case cons => constructor; assumption

lemma Merge.lower_image {Δ1 Δ2 Δ : Ctx Srt} {s} :
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

lemma Merge.self {Δ : Ctx Srt} : Merge Δ Δ.toImplicit Δ := by
  induction Δ
  case nil => simp; constructor
  case cons hd _ _ =>
    have ⟨m, r, s⟩ := hd
    cases r <;> aesop

lemma Merge.implicit {Δ1 Δ2 Δ3 : Ctx Srt} :
    Merge Δ1 Δ2 Δ3 -> Implicit Δ1 -> Δ3 = Δ2 := by
  intro mrg im; induction mrg
  all_goals try aesop

lemma Merge.implicit_image {Δ1 Δ2 Δ3 : Ctx Srt} :
    Merge Δ1 Δ2 Δ3 -> Implicit Δ1 -> Implicit Δ2 -> Implicit Δ3 := by
  intro mrg im1 im2; induction mrg
  all_goals try aesop

lemma Merge.stack_image {Δ1 Δ2 Δ3 : Ctx Srt} {i} :
    Merge Δ1 Δ2 Δ3 -> Stack Δ1 i -> Stack Δ2 i -> Stack Δ3 i := by
  intro mrg st1 st2; induction mrg generalizing i
  case nil => constructor; simp
  case contra ih =>
    cases st1 <;> try aesop
    cases st2 <;> try aesop
    apply Stack.cons; aesop
  case left ih =>
    cases st1 <;> try aesop
    cases st2
    case nil im =>
      simp at im
      apply Stack.cons
      apply ih
      . assumption
      . constructor
        apply im
    case cons =>
      apply Stack.cons
      apply ih <;> assumption
  case right ih =>
    cases st2 <;> try aesop
    cases st1
    case nil im =>
      simp at im
      apply Stack.cons
      apply ih
      . constructor
        apply im
      . assumption
    case cons =>
      apply Stack.cons
      apply ih <;> assumption
  case im =>
    cases st1
    case nil im1 =>
      simp at im1
      cases st2
      case nil im2 =>
        simp at im2
        constructor; simp
        apply Merge.implicit_image <;> assumption
      case cons =>
        apply Stack.cons
        apply Stack.nil at im1
        aesop
    case cons =>
      cases st2
      case nil im2 =>
        simp at im2
        apply Stack.nil at im2
        apply Stack.cons
        aesop
      case cons =>
        apply Stack.cons
        aesop

lemma Merge.sym {Δ1 Δ2 Δ : Ctx Srt} : Merge Δ1 Δ2 Δ -> Merge Δ2 Δ1 Δ := by
  intro mrg; induction mrg
  all_goals aesop (add safe Merge)

lemma Merge.compose {Δ1 Δ2 Δa Δb Δx Δy Δ : Ctx Srt} {s} :
    Lower Δa s -> s ∈ ord.contra_set ->
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
        . apply ord.contra_set.lower <;> assumption
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
      exists A :⟨.ex, s⟩ Δc; aesop
    | left _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨.ex, s⟩ Δc; aesop
    | right _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨.ex, s⟩ Δc; aesop
  case left A s mrg ih =>
    cases mrg2 with
    | contra _ _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨.ex, s⟩ Δc; aesop
    | left _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨.ex, s⟩ Δc; aesop
    | right _ _ mrg =>
      have ⟨Δc, mrg1, mrg2⟩ := ih mrg
      exists A :⟨.im, s⟩ Δc; aesop
  case right A s mrg ih =>
    rcases mrg2 with _ | _ | _ | _ | ⟨_, _, mrg⟩
    have ⟨Δc, mrg1, mrg2⟩ := ih mrg
    exists A :⟨.ex, s⟩ Δc; aesop
  case im A s mrg ih =>
    rcases mrg2 with _ | _ | _ | _ | ⟨_, _, mrg⟩
    have ⟨Δc, mrg1, mrg2⟩ := ih mrg
    exists A :⟨.im, s⟩ Δc; aesop

lemma Merge.distr {Δ1 Δ2 Δ3 Δ11 Δ12 Δ21 Δ22 : Ctx Srt} :
    Merge Δ1 Δ2 Δ3 ->
    Merge Δ11 Δ12 Δ1 ->
    Merge Δ21 Δ22 Δ2 ->
    ∃ Δ1' Δ2',
      Merge Δ1' Δ2' Δ3 ∧
      Merge Δ11 Δ21 Δ1' ∧
      Merge Δ12 Δ22 Δ2' := by
  intro mrg0 mrg1 mrg2
  have ⟨Δ4, mrg3, mrg4⟩ := mrg0.split mrg1
  have ⟨Δ5, mrg5, mrg6⟩ := mrg3.sym.split mrg2
  have ⟨Δ6, mrg7, mrg8⟩ := mrg4.split mrg6.sym
  exists Δ5, Δ6; and_intros
  . apply mrg8.sym
  . apply mrg5.sym
  . apply mrg7.sym
