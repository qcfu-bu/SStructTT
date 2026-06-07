import SStructTT.MLTT.SN
open ARS

namespace MLTT

/-
Postulate: Extended Calculus of Constructions is strongly normalizing.

Luo, Zhaohui (ed.), Computation and Reasoning: A Type Theory for Computer Science
(Oxford, 1994; online edn, Oxford Academic, 31 Oct. 2023),
https://doi.org/10.1093/oso/9780198538356.001.0001
-/
axiom Typed.normalize {Γ m A} : Γ ⊢ m : A -> SN Step m

-- corollary of strong normalization
lemma Typed.red_value {A m : Tm} :
    [] ⊢ m : A -> ∃ n, Value n ∧ m ~>* n := by
  intro ty; have sn := ty.normalize
  induction sn generalizing A
  case intro n h ih =>
    match ty.progress with
    | .inl ⟨n, st⟩ =>
      have ⟨n', vl, rd⟩ := ih st (ty.preservation st)
      existsi n'; and_intros
      . assumption
      . apply Star.ES <;> assumption
    | .inr vl =>
      existsi n; and_intros
      . assumption
      . apply Star.R

theorem Typed.bot_not_derivable {m : Tm} : ¬ ([] ⊢ m : .bot) := by
  intro ty
  have ⟨n, vl, rd⟩ := ty.red_value
  exact (ty.preservation' rd).bot_canonical Conv.R vl
