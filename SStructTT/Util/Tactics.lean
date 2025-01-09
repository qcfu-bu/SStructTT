open Lean Parser Tactic

syntax "rewrite" term "to" term (location)? ":=" term : tactic
macro_rules
  | `(tactic| rewrite $m to $n $[$loc]? := $h) =>
    `(tactic| have e : $m = $n := $h; rewrite[e] $[$loc]?; clear e)
