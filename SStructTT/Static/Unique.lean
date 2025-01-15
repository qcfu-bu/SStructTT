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

lemma Sim.trans_left {x y z : Tm Srt} : Sim x y -> y === z -> Sim x z := by
  intro sm eq; cases sm
  constructor
  . assumption
  . assumption
  . apply Conv.trans <;> assumption

lemma Sim.trans_right {x y z : Tm Srt} : Sim x y -> z === x -> Sim z y := by
  intro sm eq; cases sm
  constructor
  . apply Conv.trans <;> assumption
  . assumption
  . assumption

lemma Sim.subst {x y : Tm Srt} σ : Sim x y -> Sim x.[σ] y.[σ] := by
  intro sm; cases sm
  constructor
  . apply Conv.subst; assumption
  . apply HeadSim.subst; assumption
  . apply Conv.subst; assumption

lemma Sim.srt_inj {s1 s2 : Srt} {i1 i2} :
    Sim (.srt s1 i1) (.srt s2 i2) -> s1 = s2 := by
  generalize e1: Tm.srt s1 i1 = x
  generalize e2: Tm.srt s2 i2 = y
  intro sm; have ⟨_, h, _⟩ := sm
  induction h generalizing s1 s2 i1 i2
  all_goals subst_vars
  case var eq => false_conv eq
  case srt eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj eq1
    have ⟨_, _⟩ := Conv.srt_inj eq2
    subst_vars; rfl
  case pi eq _ _ => false_conv eq
  case lam eq => false_conv eq
  case app eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
  case sig eq _ _ => false_conv eq
  case pair eq => false_conv eq
  case proj eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
  case bool eq => false_conv eq
  case tt eq => false_conv eq
  case ff eq => false_conv eq
  case ite eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
  case idn eq _ => false_conv eq
  case rfl eq _ => false_conv eq
  case rw eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
