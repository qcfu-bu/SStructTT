import SStructTT.MartinLof.Typed
open ARS

namespace MartinLof

-- Postulate: Martin-Lof Type Theory is strongly normalizing.
axiom Typed.sn {Γ m A} : Γ ⊢ m : A -> SN Step m
