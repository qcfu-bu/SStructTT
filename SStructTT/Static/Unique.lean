import SStructTT.Static.Inversion
open ARS

namespace Static
variable {Srt : Type}

@[aesop safe (rule_sets := [unique]) [constructors]]
inductive HeadSim : Tm Srt -> Tm Srt -> Prop where
  | var {x} : HeadSim (.var x) (.var x)
  | srt {s i1 i2} : HeadSim (.srt s i1) (.srt s i2)
  | pi {A1 A2 B1 B2} r s :
    HeadSim A1 A2 ->
    HeadSim B1 B2 ->
    HeadSim (.pi A1 B1 r s) (.pi A2 B2 r s)
  | lam {A m r s} : HeadSim (.lam A m r s) (.lam A m r s)
  | app {m n} : HeadSim (.app m n) (.app m n)
  | sig {A1 A2 B1 B2} r s :
    HeadSim A1 A2 ->
    HeadSim B1 B2 ->
    HeadSim (.sig A1 B1 r s) (.sig A2 B2 r s)
  | pair {m n r s} : HeadSim (.pair m n r s) (.pair m n r s)
  | proj {A m n} : HeadSim (.proj A m n) (.proj A m n)
  | bool : HeadSim .bool .bool
  | tt : HeadSim .tt .tt
  | ff : HeadSim .ff .ff
  | ite {A m n1 n2} : HeadSim (.ite A m n1 n2) (.ite A m n1 n2)
  | idn {A1 A2} m n :
    HeadSim A1 A2 ->
    HeadSim (.idn A1 m n) (.idn A2 m n)
  | rfl {m} : HeadSim (.rfl m) (.rfl m)
  | rw {A m n} : HeadSim (.rw A m n) (.rw A m n)

@[aesop safe (rule_sets := [unique]) [constructors]]
inductive Sim (m n : Tm Srt) : Prop where
  | intro {x y} : m === x -> HeadSim x y -> y === n -> Sim m n

lemma HeadSim.toSim {m n : Tm Srt} : HeadSim m n -> Sim m n := by
  intro; constructor <;> aesop

@[aesop safe (rule_sets := [unique])]
lemma HeadSim.refl {m : Tm Srt} : HeadSim m m := by
  induction m
  all_goals aesop (rule_sets := [unique])

lemma HeadSim.sym {m n : Tm Srt} : HeadSim m n -> HeadSim n m := by
  intro h; induction h
  all_goals aesop (rule_sets := [unique])

lemma HeadSim.subst {m n : Tm Srt} σ : HeadSim m n -> HeadSim m.[σ] n.[σ] := by
  intro h; induction h generalizing σ
  all_goals try (asimp; aesop (rule_sets := [unique]))

lemma Sim.refl {m : Tm Srt} : Sim m m := by
  aesop (rule_sets := [unique])

lemma Sim.sym {m n : Tm Srt} : Sim m n -> Sim n m := by
  intro sm; cases sm
  constructor
  . apply Conv.sym; assumption
  . apply HeadSim.sym; assumption
  . apply Conv.sym; assumption
