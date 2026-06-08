import Mathlib.Tactic
import Lean.Meta.Tactic.Simp
import Aesop

-- Rule sets for Aesop solver.
declare_aesop_rule_sets [red, conv, pstep] (default := false)
declare_aesop_rule_sets [rename, subst, unique] (default := false)
