import SStructTT.Omega.Typed
open ARS

namespace Omega

-- Postulate: Martin-Lof Type Theory is strongly normalizing.
axiom Typed.normalize {Γ m A} : Γ ⊢ m : A -> SN Step m
