import SStructTT.MLTT.Typed
open ARS

namespace MLTT

/-
Postulate: Extended Calculus of Constructions is strongly normalizing.

Luo, Zhaohui (ed.), Computation and Reasoning: A Type Theory for Computer Science
(Oxford, 1994; online edn, Oxford Academic, 31 Oct. 2023),
https://doi.org/10.1093/oso/9780198538356.001.0001
-/
axiom Typed.normalize {Γ m A} : Γ ⊢ m : A -> SN Step m
