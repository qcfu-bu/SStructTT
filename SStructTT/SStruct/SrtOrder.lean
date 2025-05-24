import Mathlib.Tactic
import Mathlib.Order.Defs.PartialOrder

namespace SStruct

class SrtOrder (S : Type) extends PartialOrder S where
  e : S
  weaken_set : LowerSet S
  contra_set : LowerSet S
  e_min : ∀ (x : S), e ≤ x
  e_weaken : e ∈ weaken_set
  e_contra : e ∈ contra_set
  weaken_dec : ∀ s, Decidable (s ∈ weaken_set)
  contra_dec : ∀ s, Decidable (s ∈ contra_set)

instance {S : Type} {s : S} [ord : SrtOrder S] : Decidable (s ∈ ord.weaken_set) :=
  ord.weaken_dec s

instance {S : Type} {s : S} [ord : SrtOrder S] : Decidable (s ∈ ord.contra_set) :=
  ord.contra_dec s

section InterSet
variable {Srt : Type} [ord : SrtOrder Srt]

def InterSet (s : Srt) : Set Srt :=
  fun s' =>
    (s ∈ ord.weaken_set -> s' ∈ ord.weaken_set) ∧
    (s ∈ ord.contra_set -> s' ∈ ord.contra_set)

lemma InterSet.self_mem {s : Srt} : s ∈ InterSet s := by
  constructor <;> simp

lemma InterSet.min_mem {s : Srt} : ord.e ∈ InterSet s := by
  constructor
  . intro; apply ord.e_weaken
  . intro; apply ord.e_contra

lemma InterSet.weaken {s1 s2 : Srt} :
    s1 ∈ InterSet s2 -> s2 ∈ ord.weaken_set -> s1 ∈ ord.weaken_set := by
  intro h1 h2; cases h1; aesop

lemma InterSet.contra {s1 s2 : Srt} :
    s1 ∈ InterSet s2 -> s2 ∈ ord.contra_set -> s1 ∈ ord.contra_set := by
  intro h1 h2; cases h1; aesop

lemma InterSet.lower_mem {s1 s2 : Srt} :
    s1 <= s2 -> s1 ∈ InterSet s2 := by
  intro le
  constructor
  case left  => intro h; apply ord.weaken_set.lower le h
  case right => intro h; apply ord.contra_set.lower le h

lemma InterSet.lower_subset {s1 s2 : Srt} :
    s1 <= s2 -> InterSet s1 ⊆ InterSet s2 := by
  intro le s c1
  constructor
  case left =>
    intro h; have ⟨h1, h2⟩ := c1
    have := ord.weaken_set.lower le h
    aesop
  case right =>
    intro h; have ⟨h1, h2⟩ := c1
    have := ord.contra_set.lower le h
    aesop

lemma InterSet.trans {s1 s2 s3 : Srt} :
    s2 ∈ InterSet s1 -> s3 ∈ InterSet s2 -> s3 ∈ InterSet s1 := by
  intro h1 h2
  constructor
  case left  => intro h; cases h1; cases h2; aesop
  case right => intro h; cases h1; cases h2; aesop

end InterSet

namespace SO4 -- 4 Sorted
inductive Srt where
  | U -- unbound
  | R -- relevant
  | A -- affine
  | L -- linear

inductive Srt.le : Srt -> Srt -> Prop where
  | le_refl s : le s s
  | le_trans s r t : le s r -> le r t -> le s t
  | le_UR : le U R
  | le_UA : le U A
  | le_RL : le R L
  | le_AL : le A L

lemma Srt.le_sU_false s : ¬ s = U -> ¬ le s U := by
  generalize e: U = r
  intro _ h; induction h
  all_goals try trivial
  case le_trans => aesop

lemma Srt.le_Ls_false s : ¬ s = L -> ¬ le L s := by
  generalize e: L = r
  intro _ h; induction h
  all_goals try trivial
  case le_trans => aesop

lemma Srt.le_RA_false : ¬ le R A := by
  generalize e1: R = r
  generalize e2: A = s
  intro h; induction h
  all_goals try trivial
  case le_refl =>
    subst_vars; contradiction
  case le_trans s r t h1 h2 ih1 ih2 =>
    subst_vars
    cases r with
    | U =>
      apply Srt.le_sU_false <;> try assumption
      intro; contradiction
    | A => aesop
    | R => aesop
    | L =>
      apply Srt.le_Ls_false <;> try assumption
      intro; contradiction

lemma Srt.le_AR_false : ¬ le A R := by
  generalize e1: R = r
  generalize e2: A = s
  intro h; induction h
  all_goals try trivial
  case le_refl =>
    subst_vars; contradiction
  case le_trans s r t h1 h2 ih1 ih2 =>
    subst_vars
    cases r with
    | U =>
      apply Srt.le_sU_false <;> try assumption
      intro; contradiction
    | A => aesop
    | R => aesop
    | L =>
      apply Srt.le_Ls_false <;> try assumption
      intro; contradiction

lemma Srt.le_antisymm (a b : Srt) : le a b → le b a → a = b := by
  intro h; induction h
  case le_refl => intro; rfl
  case le_trans h1 h2 ih1 ih2 =>
    intro h3
    have h4 := Srt.le.le_trans _ _ _ h2 h3
    have e := ih1 h4; subst_vars
    apply ih2; assumption
  case le_UR =>
    intro h; exfalso
    apply Srt.le_sU_false <;> try assumption
    intro; contradiction
  case le_UA =>
    intro h; exfalso
    apply Srt.le_sU_false <;> try assumption
    intro; contradiction
  case le_AL =>
    intro h; exfalso
    apply Srt.le_Ls_false <;> try assumption
    intro; contradiction
  case le_RL =>
    intro h; exfalso
    apply Srt.le_Ls_false <;> try assumption
    intro; contradiction

instance : PartialOrder Srt where
  le := Srt.le
  le_refl := Srt.le.le_refl
  le_trans := Srt.le.le_trans
  le_antisymm := Srt.le_antisymm

lemma Srt.le_U_min : ∀ (s : Srt), U ≤ s := by
  intro s; cases s
  . apply Srt.le.le_refl
  . apply Srt.le.le_UR
  . apply Srt.le.le_UA
  . apply le_trans
    apply Srt.le.le_UR
    apply Srt.le.le_RL

inductive Srt.weaken : Set Srt where
  | U : weaken U
  | A : weaken A

inductive Srt.contra : Set Srt where
  | U : contra U
  | R : contra R

lemma Srt.weaken_lower : IsLowerSet weaken := by
  intro s t h wk; cases wk
  case U =>
    cases t <;> try constructor
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
  case A =>
    cases t <;> try constructor
    . exfalso; apply Srt.le_RA_false; assumption
    . exfalso
      apply Srt.le_Ls_false <;> try assumption
      aesop

lemma Srt.contra_lower : IsLowerSet contra := by
  intro s t h wk; cases wk
  case U =>
    cases t <;> try constructor
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
  case R =>
    cases t <;> try constructor
    . exfalso; apply Srt.le_AR_false; assumption
    . exfalso
      apply Srt.le_Ls_false <;> try assumption
      aesop

def Srt.weaken_dec (s : Srt) : Decidable (s ∈ weaken) := by
  cases s with
  | U => apply isTrue .U
  | A => apply isTrue .A
  | R => apply isFalse; intro h; cases h
  | L => apply isFalse; intro h; cases h

def Srt.contra_dec (s : Srt) : Decidable (s ∈ contra) := by
  cases s with
  | U => apply isTrue .U
  | R => apply isTrue .R
  | A => apply isFalse; intro h; cases h
  | L => apply isFalse; intro h; cases h

instance : SrtOrder Srt where
  e := Srt.U
  weaken_set := ⟨_, Srt.weaken_lower⟩
  contra_set := ⟨_, Srt.contra_lower⟩
  e_min := Srt.le_U_min
  e_weaken := Srt.weaken.U
  e_contra := Srt.contra.U
  weaken_dec := Srt.weaken_dec
  contra_dec := Srt.contra_dec

end SO4
