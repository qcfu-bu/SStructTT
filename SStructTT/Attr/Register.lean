import Lean.Meta.Tactic.Simp
import Aesop

-- Simplify de Bruijn index substitutions.
register_simp_attr asimp

-- Rule sets for Aesop solver.
declare_aesop_rule_sets [red, conv, pstep] (default := false)
