import SStructTT.Basics.ARS
import SStructTT.SStruct.Erasure.Syntax
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

@[scoped aesop safe [constructors]]
inductive Value : Tm Srt -> Prop where
  | lam {m s} :
    Value (.lam m s)
  | tup {m n s} :
    Value m ->
    Value n ->
    Value (.tup m n s)
  | tt : Value .tt
  | ff : Value .ff
  | ptr {l} : Value (.ptr l)
  | null : Value .null

@[scoped aesop safe [constructors]]
inductive Step0 : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    Step0 m m' ->
    Step0 (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step0 n n' ->
    Step0 (.app m n) (.app m n')
  | tup_M {m m'} n s :
    Step0 m m' ->
    Step0 (.tup m n s) (.tup m' n s)
  | tup_N m {n n'} s :
    Step0 n n' ->
    Step0 (.tup m n s) (.tup m n' s)
  | prj_M {m m'} n :
    Step0 m m' ->
    Step0 (.prj m n) (.prj m' n)
  | ite_M {m m'} n1 n2 :
    Step0 m m' ->
    Step0 (.ite m n1 n2) (.ite m' n1 n2)
  | drop_elim m n :
    Step0 (.drop m n) n

@[scoped aesop safe [constructors]]
inductive Step1 : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    Step1 m m' ->
    Step1 (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step1 n n' ->
    Step1 (.app m n) (.app m n')
  | beta m n s :
    Value n ->
    Step1 (.app (.lam m s) n) m.[n/]
  | tup_M {m m'} n s :
    Step1 m m' ->
    Step1 (.tup m n s) (.tup m' n s)
  | tup_N m {n n'} s :
    Step1 n n' ->
    Step1 (.tup m n s) (.tup m n' s)
  | prj_M {m m'} n :
    Step1 m m' ->
    Step1 (.prj m n) (.prj m' n)
  | prj_elim {m1 m2} n {s} :
    Value (.tup m1 m2 s) ->
    Step1 (.prj (.tup m1 m2 s) n) n.[m2,m1/]
  | ite_M {m m'} n1 n2 :
    Step1 m m' ->
    Step1 (.ite m n1 n2) (.ite m' n1 n2)
  | ite_tt n1 n2 :
    Step1 (.ite .tt n1 n2) n1
  | ite_ff n1 n2 :
    Step1 (.ite .ff n1 n2) n2
  | rw_elim m :
    Step1 (.rw m) m

def Step (m : Tm Srt) (n : Tm Srt) : Prop :=
  Step0 m n ∨ Step1 m n

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n

lemma Step.app_M {m m' n : Tm Srt} :
    m ~>> m' -> .app m n ~>> .app m' n := by
  intro st
  cases st with
  | inl st => left; constructor; assumption
  | inr st => right; constructor; assumption

lemma Step.app_N {m n n' : Tm Srt} :
    n ~>> n' -> .app m n ~>> .app m n' := by
  intro st
  cases st with
  | inl st => left; constructor; assumption
  | inr st => right; constructor; assumption

lemma Step.tup_M {m m' n : Tm Srt} {s} :
    m ~>> m' -> .tup m n s ~>> .tup m' n s := by
  intro st
  cases st with
  | inl st => left; constructor; assumption
  | inr st => right; constructor; assumption

lemma Step.tup_N {m n n' : Tm Srt} {s} :
    n ~>> n' -> .tup m n s ~>> .tup m n' s := by
  intro st
  cases st with
  | inl st => left; constructor; assumption
  | inr st => right; constructor; assumption

lemma Step.prj_M {m m' n : Tm Srt} :
    m ~>> m' -> .prj m n ~>> .prj m' n := by
  intro st
  cases st with
  | inl st => left; constructor; assumption
  | inr st => right; constructor; assumption

lemma Step.ite_M {m m' n1 n2 : Tm Srt} :
    m ~>> m' -> .ite m n1 n2 ~>> .ite m' n1 n2 := by
  intro st
  cases st with
  | inl st => left; constructor; assumption
  | inr st => right; constructor; assumption
