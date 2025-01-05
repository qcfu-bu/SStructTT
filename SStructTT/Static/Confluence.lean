import SStructTT.Static.Step

namespace Static
variable {Srt : Type}

inductive PStep : Tm Srt -> Tm Srt -> Prop where
  | var {x} :
    PStep (.var x) (.var x)
  | srt s i :
    PStep (.srt s i) (.srt s i)
  | pi {A A' B B' r s} :
    PStep A A' ->
    PStep B B' ->
    PStep (.pi A B r s) (.pi A' B' r s)
  | lam {A A' m m' r s} :
    PStep A A' ->
    PStep m m' ->
    PStep (.lam A m r s) (.lam A' m' r s)
  | app {m m' n n'} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app m n) (.app m' n')
  | beta {A m m' n n' r s} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app (.lam A m r s) n) m'.[n'/]
  | sig {A A' B B' r s} :
    PStep A A' ->
    PStep B B' ->
    PStep (.sig A B r s) (.sig A' B' r s)
  | pair {m m' n n' r s} :
    PStep m m' ->
    PStep n n' ->
    PStep (.pair m n r s) (.pair m n r s)
  | proj {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.proj A m n) (.proj A' m' n')
  | projE {A m1 m1' m2 m2' n n' r s} :
    PStep m1 m1' ->
    PStep m2 m2' ->
    PStep n n' ->
    PStep (.proj A (.pair m1 m2 r s) n) n'.[m2',m1'/]
  | bool : PStep .bool .bool
  | tt : PStep .tt .tt
  | ff : PStep .ff .ff
  | ifte {A A' m m' n1 n1' n2 n2'} :
    PStep A A' ->
    PStep m m' ->
    PStep n1 n1' ->
    PStep n2 n2' ->
    PStep (.ifte A m n1 n2) (.ifte A' m' n1' n2')
  | ifteT {A n1 n1' n2} :
    PStep n1 n1' ->
    PStep (.ifte A .tt n1 n2) n1'
  | ifteF {A n1 n2 n2'} :
    PStep n2 n2' ->
    PStep (.ifte A .ff n1 n2) n2'
  | id {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.id A m n) (.id A' m' n')
  | rfl {m m'} :
    PStep m m' ->
    PStep (.rfl m) (.rfl m')
  | rw {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.rw A m n) (.rw A' m' n')
  | rwE {A m m' n} :
    PStep m m' ->
    PStep (.rw A m (.rfl n)) m'

infix:50 " ≈> " => PStep

def SRed (σ τ : Nat -> Tm Srt) := ∀ x, (σ x) ~>* (τ x)

lemma Step.subst (m n : Tm Srt) σ : m ~> n -> m.[σ] ~> n.[σ] := by
  intro st
  induction st generalizing σ with
  | piA st ih => asimp; constructor; apply ih
  | piB st ih => asimp; constructor; apply ih
  | lamA st ih => asimp; constructor; apply ih
  | lamM st ih => asimp; constructor; apply ih
  | appM st ih => asimp; constructor; apply ih
  | appN st ih => asimp; constructor; apply ih
  | @beta A m n r s  =>
    asimp
    have h := @Step.beta _ A.[σ] m.[up σ] n.[σ] r s
    asimp at h
    assumption
  | sigA st ih => asimp; constructor; apply ih
  | sigB st ih => asimp; constructor; apply ih
  | pairM st ih => asimp; constructor; apply ih
  | pairN st ih => asimp; constructor; apply ih
  | projA st ih => asimp; constructor; apply ih
  | projM st ih => asimp; constructor; apply ih
  | projN st ih => asimp; constructor; apply ih
  | @projE A m1 m2 n r s =>
    asimp
    have h := @Step.projE _ A.[up σ] m1.[σ] m2.[σ] n.[up $ up σ] r s
    asimp at h
    assumption
