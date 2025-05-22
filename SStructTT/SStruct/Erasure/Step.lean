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
inductive Drop : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    Drop m m' ->
    Drop (.app m n) (.app m' n)
  | app_N m {n n'} :
    Drop n n' ->
    Drop (.app m n) (.app m n')
  | tup_M {m m'} n s :
    Drop m m' ->
    Drop (.tup m n s) (.tup m' n s)
  | tup_N m {n n'} s :
    Drop n n' ->
    Drop (.tup m n s) (.tup m n' s)
  | prj_M {m m'} n :
    Drop m m' ->
    Drop (.prj m n) (.prj m' n)
  | ite_M {m m'} n1 n2 :
    Drop m m' ->
    Drop (.ite m n1 n2) (.ite m' n1 n2)
  | drop_elim m n :
    Drop (.drop m n) n

@[scoped aesop safe [constructors]]
inductive CoreStep : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    CoreStep m m' ->
    CoreStep (.app m n) (.app m' n)
  | app_N m {n n'} :
    CoreStep n n' ->
    CoreStep (.app m n) (.app m n')
  | beta m n s :
    Value n ->
    CoreStep (.app (.lam m s) n) m.[n/]
  | tup_M {m m'} n s :
    CoreStep m m' ->
    CoreStep (.tup m n s) (.tup m' n s)
  | tup_N m {n n'} s :
    CoreStep n n' ->
    CoreStep (.tup m n s) (.tup m n' s)
  | prj_M {m m'} n :
    CoreStep m m' ->
    CoreStep (.prj m n) (.prj m' n)
  | prj_elim {m1 m2} n {s} :
    Value (.tup m1 m2 s) ->
    CoreStep (.prj (.tup m1 m2 s) n) n.[m2,m1/]
  | ite_M {m m'} n1 n2 :
    CoreStep m m' ->
    CoreStep (.ite m n1 n2) (.ite m' n1 n2)
  | ite_tt n1 n2 :
    CoreStep (.ite .tt n1 n2) n1
  | ite_ff n1 n2 :
    CoreStep (.ite .ff n1 n2) n2
  | rw_elim m :
    CoreStep (.rw m) m

abbrev Drops (m m' : Tm Srt) : Prop := Star Drop m m'

inductive Step (m : Tm Srt) : Tm Srt -> Prop where
  | intro {m' n} : Drops m m' -> CoreStep m' n -> Step m n

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n

lemma Drops.var_inv {x} {t : Tm Srt} :
    Drops (.var x) t -> t = .var x := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Drops.lam_inv {m t : Tm Srt} {s} :
    Drops (.lam m s) t -> t = .lam m s := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Drops.app_inv {m n t : Tm Srt} :
    Drops (.app m n) t ->
    ∃ m' n', t = .app m' n' ∧ Drops m m' ∧ Drops n n' := by
  intro rd; induction rd
  case R =>
    exists m, n; aesop
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

lemma Drops.tup_inv {m n t : Tm Srt} {s} :
    Drops (.tup m n s) t ->
    ∃ m' n', t = .tup m' n' s ∧ Drops m m' ∧ Drops n n' := by
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

lemma Drops.prj_inv {m n t : Tm Srt} :
    Drops (.prj m n) t ->
    ∃ m', t = .prj m' n ∧ Drops m m' := by
  intro rd; induction rd
  case R => exists m; aesop
  case SE st ih =>
    have ⟨m', e, rd⟩  := ih
    subst_vars
    cases st
    case prj_M mx st =>
      exists mx; simp
      apply Star.SE rd st

lemma Drops.tt_inv {t : Tm Srt} : Drops .tt t -> t = .tt := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Drops.ff_inv {t : Tm Srt} : Drops .ff t -> t = .ff := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Drops.ite_inv {m n1 n2 t : Tm Srt} :
    Drops (.ite m n1 n2) t ->
    ∃ m', t = .ite m' n1 n2 ∧ Drops m m' := by
  intro rd; induction rd
  case R => exists m; aesop
  case SE st ih =>
    have ⟨m', e, rd⟩  := ih
    subst_vars
    cases st
    case ite_M mx st =>
      exists mx; simp
      apply Star.SE rd st

lemma Drops.rw_inv {m t : Tm Srt} : Drops (.rw m) t -> t = .rw m := by
  intro rd; induction rd
  case R => simp
  case SE st ih => subst_vars; cases st

lemma Drops.drop_inv {m n a b : Tm Srt} :
    Drops (.drop m n) a -> Drop a b -> Drops n b := by
  intro rd st; induction rd generalizing b
  case R =>
    cases st
    constructor
  case SE st ih =>
    apply Star.SE
    . apply ih
      assumption
    . assumption

lemma Drops.ptr_inv {l} {t : Tm Srt} :
    Drops (.ptr l) t -> t = .ptr l := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Drops.null_inv {t : Tm Srt} :
    Drops .null t -> t = .null := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st
