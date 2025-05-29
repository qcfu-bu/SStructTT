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

/- Drop-reductions. -/
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

/- Core-reductions. -/
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

abbrev Red0 (m m' : Tm Srt) : Prop := Star Step0 m m'

def Step : Rel (Tm Srt) := Relation.Comp Red0 Step1

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n

lemma Red0.var_inv {x} {t : Tm Srt} :
    Red0 (.var x) t -> t = .var x := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Red0.lam_inv {m t : Tm Srt} {s} :
    Red0 (.lam m s) t -> t = .lam m s := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.app_inv {m n t : Tm Srt} :
    Red0 (.app m n) t ->
    ∃ m' n', t = .app m' n' ∧ Red0 m m' ∧ Red0 n n' := by
  intro rd; induction rd
  case R =>
    existsi m, n; aesop
  case SE st ih =>
    have ⟨m', n', e, rd1, rd2⟩  := ih
    subst_vars
    cases st
    case app_M mx st =>
      existsi mx, n'; simp; and_intros
      . apply Star.SE rd1 st
      . assumption
    case app_N nx st =>
      existsi m', nx; simp; and_intros
      . assumption
      . apply Star.SE rd2 st

lemma Red0.tup_inv {m n t : Tm Srt} {s} :
    Red0 (.tup m n s) t ->
    ∃ m' n', t = .tup m' n' s ∧ Red0 m m' ∧ Red0 n n' := by
  intro rd; induction rd
  case R => existsi m, n; aesop
  case SE st ih =>
    have ⟨m', n', e, rd1, rd2⟩  := ih
    subst_vars
    cases st
    case tup_M mx st =>
      existsi mx, n'; simp; and_intros
      . apply Star.SE rd1 st
      . assumption
    case tup_N nx st =>
      existsi m', nx; simp; and_intros
      . assumption
      . apply Star.SE rd2 st

lemma Red0.prj_inv {m n t : Tm Srt} :
    Red0 (.prj m n) t ->
    ∃ m', t = .prj m' n ∧ Red0 m m' := by
  intro rd; induction rd
  case R => existsi m; aesop
  case SE st ih =>
    have ⟨m', e, rd⟩  := ih
    subst_vars
    cases st
    case prj_M mx st =>
      existsi mx; simp
      apply Star.SE rd st

lemma Red0.tt_inv {t : Tm Srt} : Red0 .tt t -> t = .tt := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Red0.ff_inv {t : Tm Srt} : Red0 .ff t -> t = .ff := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Red0.ite_inv {m n1 n2 t : Tm Srt} :
    Red0 (.ite m n1 n2) t ->
    ∃ m', t = .ite m' n1 n2 ∧ Red0 m m' := by
  intro rd; induction rd
  case R => existsi m; aesop
  case SE st ih =>
    have ⟨m', e, rd⟩  := ih
    subst_vars
    cases st
    case ite_M mx st =>
      existsi mx; simp
      apply Star.SE rd st

lemma Red0.drop_inv {m n a b : Tm Srt} :
    Red0 (.drop m n) a -> Step0 a b -> Red0 n b := by
  intro rd st; induction rd generalizing b
  case R =>
    cases st
    constructor
  case SE st ih =>
    apply Star.SE
    . apply ih
      assumption
    . assumption

lemma Red0.ptr_inv {l} {t : Tm Srt} :
    Red0 (.ptr l) t -> t = .ptr l := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Red0.null_inv {t : Tm Srt} :
    Red0 .null t -> t = .null := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Red0.app {m m' n n' : Tm Srt} :
    Red0 m m' -> Red0 n n' -> Red0 (.app m n) (.app m' n') := by
  intro rm rn
  apply (@Star.trans _ _ (.app m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red0.tup {m m' n n' : Tm Srt} {s} :
    Red0 m m' -> Red0 n n' -> Red0 (.tup m n s) (.tup m' n' s) := by
  intro rm rn
  apply (@Star.trans _ _ (.tup m' n s))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red0.prj {m m' n : Tm Srt} :
    Red0 m m' -> Red0 (.prj m n) (.prj m' n) := by
  intro rm; apply Star.hom _ _ rm; aesop

lemma Red0.ite {m m' n1 n2 : Tm Srt} :
    Red0 m m' -> Red0 (.ite m n1 n2) (.ite m' n1 n2) := by
  intro rm; apply Star.hom _ _ rm; aesop

lemma Step.app_M {m m' n : Tm Srt} :
    m ~>> m' -> .app m n ~>> .app m' n := by
  intro st
  rcases st with ⟨_, rd, st⟩
  constructor; and_intros
  . apply Red0.app rd Star.R
  . constructor; assumption

lemma Step.app_N {m n n' : Tm Srt} :
    n ~>> n' -> .app m n ~>> .app m n' := by
  intro st
  rcases st with ⟨_, rd, st⟩
  constructor; and_intros
  . apply Red0.app Star.R rd
  . constructor; assumption

lemma Step.tup_M {m m' n : Tm Srt} {s} :
    m ~>> m' -> .tup m n s ~>> .tup m' n s := by
  intro st
  rcases st with ⟨_, rd, st⟩
  constructor; and_intros
  . apply Red0.tup rd Star.R
  . constructor; assumption

lemma Step.tup_N {m n n' : Tm Srt} {s} :
    n ~>> n' -> .tup m n s ~>> .tup m n' s := by
  intro st
  rcases st with ⟨_, rd, st⟩
  constructor; and_intros
  . apply Red0.tup Star.R rd
  . constructor; assumption

lemma Step.prj_M {m m' n : Tm Srt} :
    m ~>> m' -> .prj m n ~>> .prj m' n := by
  intro st
  rcases st with ⟨_, rd, st⟩
  constructor; and_intros
  . apply Red0.prj rd
  . constructor; assumption

lemma Step.ite_M {m m' n1 n2 : Tm Srt} :
    m ~>> m' -> .ite m n1 n2 ~>> .ite m' n1 n2 := by
  intro st
  rcases st with ⟨_, rd, st⟩
  constructor; and_intros
  . apply Red0.ite rd
  . constructor; assumption

lemma Step.drop {m n n' : Tm Srt} :
    n ~>> n' -> .drop m n ~>> n' := by
  intro st
  rcases st with ⟨_, rd, st⟩
  cases rd
  case R =>
    constructor; and_intros
    . apply Star.one
      constructor
    . assumption
  case SE rd st0 =>
    have rd := Star.SE rd st0
    constructor; and_intros
    . apply Star.trans _ rd
      apply Star.one
      constructor
    . assumption
