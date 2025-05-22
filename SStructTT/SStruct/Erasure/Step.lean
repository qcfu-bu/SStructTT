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

inductive Step (m : Tm Srt) : Tm Srt -> Prop where
  | intro {m' n} : Star Step0 m m' -> Step1 m' n -> Step m n

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n

lemma Red0.var_inv {x} {t : Tm Srt} :
    Star Step0 (.var x) t -> t = .var x := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Red0.lam_inv {m t : Tm Srt} {s} :
    Star Step0 (.lam m s) t -> t = .lam m s := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.app_inv {m n t : Tm Srt} :
    Star Step0 (.app m n) t ->
    ∃ m' n', t = .app m' n' ∧ Star Step0 m m' ∧ Star Step0 n n' := by
  intro rd; induction rd
  case R => exists m, n; aesop
  case SE st ih =>
    have ⟨m', n', e, rd1, rd2⟩  := ih
    subst_vars
    cases st
    case app_M mx st =>
      exists mx, n'; simp; and_intros
      . apply Star.SE rd1 st
      . assumption
    case app_N nx st =>
      exists m', nx; simp; and_intros
      . assumption
      . apply Star.SE rd2 st

lemma Red0.tup_inv {m n t : Tm Srt} {s} :
    Star Step0 (.tup m n s) t ->
    ∃ m' n', t = .tup m' n' s ∧ Star Step0 m m' ∧ Star Step0 n n' := by
  intro rd; induction rd
  case R => exists m, n; aesop
  case SE st ih =>
    have ⟨m', n', e, rd1, rd2⟩  := ih
    subst_vars
    cases st
    case tup_M mx st =>
      exists mx, n'; simp; and_intros
      . apply Star.SE rd1 st
      . assumption
    case tup_N nx st =>
      exists m', nx; simp; and_intros
      . assumption
      . apply Star.SE rd2 st

lemma Red0.prj_inv {m n t : Tm Srt} :
    Star Step0 (.prj m n) t ->
    ∃ m', t = .prj m' n ∧ Star Step0 m m' := by
  intro rd; induction rd
  case R => exists m; aesop
  case SE st ih =>
    have ⟨m', e, rd⟩  := ih
    subst_vars
    cases st
    case prj_M mx st =>
      exists mx; simp
      apply Star.SE rd st

lemma Red0.tt_inv {t : Tm Srt} : Star Step0 .tt t -> t = .tt := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Red0.ff_inv {t : Tm Srt} : Star Step0 .ff t -> t = .ff := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Red0.ite_inv {m n1 n2 t : Tm Srt} :
    Star Step0 (.ite m n1 n2) t ->
    ∃ m', t = .ite m' n1 n2 ∧ Star Step0 m m' := by
  intro rd; induction rd
  case R => exists m; aesop
  case SE st ih =>
    have ⟨m', e, rd⟩  := ih
    subst_vars
    cases st
    case ite_M mx st =>
      exists mx; simp
      apply Star.SE rd st

lemma Red0.rw_inv {m t : Tm Srt} : Star Step0 (.rw m) t -> t = .rw m := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Red0.drop_inv {m n a b : Tm Srt} :
    Star Step0 (.drop m n) a -> Step0 a b -> Star Step0 n b := by
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
    Star Step0 (.ptr l) t -> t = .ptr l := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Red0.null_inv {t : Tm Srt} :
    Star Step0 .null t -> t = .null := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st
