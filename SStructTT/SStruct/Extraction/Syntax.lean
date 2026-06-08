import SStructTT.SStruct.Logical.Typed
import SStructTT.SStruct.Program.Typed

open Autosubst Autosubst.Notation

namespace SStruct.Extraction

autosubst
  Tm (Srt : Type) where
    | lam  : (bind Tm in Tm) → Srt → Tm
    | app  : Tm → Tm → Tm
    | tup  : Tm → Tm → Srt → Tm
    | prj  : Tm → (bind Tm, Tm in Tm) → Tm
    | tt : Tm
    | ff : Tm
    | ite  : Tm → Tm → Tm → Tm
    | drop : Tm → Tm → Tm
    | ptr  : Nat → Tm
    | null : Tm
    | dead : Tm

namespace Tm
-- `Tm.var` kept as a `match_pattern` alias for the generated `var_Tm`, so existing positional
-- uses (`.var x`, `Tm.var x`) continue to work after the autosubst migration.
@[match_pattern] abbrev var {Srt : Type} := @Tm.var_Tm Srt
end Tm

/-- Iterated lift `⇑…⇑σ` (`n` times). -/
def upn {Srt : Type} : Nat → (Var → Tm Srt) → (Var → Tm Srt)
  | 0,     σ => σ
  | n + 1, σ => ⇑(upn n σ)

@[simp]def Closed {Srt} (i : Nat) : Tm Srt -> Prop
  | .var x => x < i
  | .lam m _ => Closed (i + 1) m
  | .app m n => Closed i m ∧ Closed i n
  | .tup m n _ => Closed i m ∧ Closed i n
  | .prj m n => Closed i m ∧ Closed (i + 2) n
  | .tt => True
  | .ff => True
  | .ite m n1 n2 => Closed i m ∧ Closed i n1 ∧ Closed i n2
  | .drop m n => Closed i m ∧ Closed i n
  | .ptr _ => True
  | .null => True
  | .dead => True

lemma Closed.weaken {Srt : Type} {m : Tm Srt} {i j} :
    Closed i m -> i ≤ j -> Closed j m := by
  induction m generalizing i j <;> try (solve| aesop)
  case var_Tm x =>
    intros h1 h2
    apply h1.trans_le h2

end SStruct.Extraction
