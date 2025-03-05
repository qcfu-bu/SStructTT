import SStructTT.MartinLof.Typed
open ARS

namespace MartinLof

-- Postulate: Martin-Lof Type Theory is strongly normalizing.
axiom Typed.normalize {Γ m A} : Γ ⊢ m : A -> SN Step m
