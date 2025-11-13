import SStructTT.ECC.Typed
open ARS

namespace ECC

-- Postulate: Martin-Lof Type Theory is strongly normalizing.
axiom Typed.normalize {Γ m A} : Γ ⊢ m : A -> SN Step m
