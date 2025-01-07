import Mathlib.Tactic
import Mathlib.Order.Defs.PartialOrder

class SStruct (S : Type) extends PartialOrder S where
  s0 : S
  s0_min : ∀ (x : S), s0 ≤ x
  weaken_set : LowerSet S
  contra_set : LowerSet S
  s0_weaken : s0 ∈ weaken_set
  s0_contra : s0 ∈ contra_set

export SStruct
  (s0 s0_min weaken_set contra_set s0_weaken s0_contra)

namespace TL4 -- 4 Sorted TLL
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

lemma Srt.le_antisymm (a b : Srt) : le a b → le b a → a = b := by
  intro h
  induction h with
  | le_refl => intro; rfl
  | le_trans _ _ _ h1 h2 ih1 ih2 =>
    intro h3
    have h4 := Srt.le.le_trans _ _ _ h2 h3
    have e := ih1 h4
    subst_vars
    apply ih2
    assumption
  | le_UR =>
    intro h; exfalso
    apply Srt.le_sU_false <;> try assumption
    intro; contradiction
  | le_UA =>
    intro h; exfalso
    apply Srt.le_sU_false <;> try assumption
    intro; contradiction
  | le_AL =>
    intro h; exfalso
    apply Srt.le_Ls_false <;> try assumption
    intro; contradiction
  | le_RL =>
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

inductive Srt.contra : Srt -> Prop where
  | U : contra U
  | R : contra A

lemma Srt.weaken_lower : IsLowerSet weaken := by
  intro s t h wk
  cases wk with
  | U =>
    cases t
    all_goals try constructor
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
  | A =>
    cases t
    all_goals try constructor
    . exfalso; apply Srt.le_RA_false; assumption
    . exfalso
      apply Srt.le_Ls_false <;> try assumption
      aesop

lemma Srt.contra_lower : IsLowerSet contra := by
  intro s t h wk
  cases wk with
  | U =>
    cases t
    all_goals try constructor
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
    . exfalso
      apply Srt.le_sU_false <;> try assumption
      aesop
  | R =>
    cases t
    all_goals try constructor
    . exfalso; apply Srt.le_RA_false; assumption
    . exfalso
      apply Srt.le_Ls_false <;> try assumption
      aesop

instance : SStruct Srt where
  s0 := Srt.U
  s0_min := Srt.le_U_min
  weaken_set := ⟨_, Srt.weaken_lower⟩
  contra_set := ⟨_, Srt.contra_lower⟩
  s0_weaken := Srt.weaken.U
  s0_contra := Srt.contra.U
end TL4
