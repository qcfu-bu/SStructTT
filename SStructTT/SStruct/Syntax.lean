import SStructTT.Basics.Subst

open Autosubst Autosubst.Notation

namespace SStruct

inductive Rlv where
  | im | ex

autosubst
  Tm (Srt : Type) where
    | srt : Srt → Nat → Tm
    | pi  : Tm → (bind Tm in Tm) → Rlv → Srt → Tm
    | lam : Tm → (bind Tm in Tm) → Rlv → Srt → Tm
    | app : Tm → Tm → Tm
    | sig : Tm → (bind Tm in Tm) → Rlv → Srt → Tm
    | tup : Tm → Tm → Rlv → Srt → Tm
    | prj : (bind Tm in Tm) → Tm → (bind Tm, Tm in Tm) → Tm
    | bool : Tm
    | tt : Tm
    | ff : Tm
    | ite : (bind Tm in Tm) → Tm → Tm → Tm → Tm
    | idn : Tm → Tm → Tm → Tm
    | rfl : Tm → Tm
    | rw  : (bind Tm, Tm in Tm) → Tm → Tm → Tm
    | bot : Tm
    | exf : (bind Tm in Tm) → Tm → Tm

namespace Tm
-- `Tm.var` kept as a `match_pattern` alias for the generated `var_Tm`, so existing positional
-- uses (`.var x`, `Tm.var x`) continue to work after the autosubst migration.
@[match_pattern] abbrev var {Srt : Type} := @Tm.var_Tm Srt
end Tm

/-- Iterated lift `⇑…⇑σ` (`n` times). The library provides the single lift `⇑`/`Up.up`; this is the
`n`-fold version the SStruct development needs (`upn 0 σ = σ`, `upn (n+1) σ = ⇑(upn n σ)`); concrete
counts reduce definitionally (`upn 2 σ ≡ ⇑⇑σ`). -/
def upn {Srt : Type} : Nat → (Var → Tm Srt) → (Var → Tm Srt)
  | 0,     σ => σ
  | n + 1, σ => ⇑(upn n σ)

end SStruct
