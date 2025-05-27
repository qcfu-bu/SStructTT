import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime

variable {Srt : Type} [ord : SrtOrder Srt]

/- Deallocate dropped terms. -/
inductive Drop : Heap Srt -> Tm Srt -> Heap Srt -> Prop where
  | var {H x} : Drop H (.var x) H
  | lam {H1 H2 m s} :
    Drop H1 m H2 ->
    Drop H1 (.lam m s) H2
  | app {H1 H2 H3 m n} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.app m n) H3
  | tup {H1 H2 H3 m n s} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.tup m n s) H3
  | prj {H1 H2 H3 m n} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.prj m n) H3
  | tt {H} : Drop H .tt H
  | ff {H} : Drop H .ff H
  | ite {H1 H2 H3 m n1 n2} :
    Drop H1 m H2 ->
    Drop H2 n1 H3 ->
    Drop H2 n2 H3 ->
    Drop H1 (.ite m n1 n2) H3
  | drop {H1 H2 H3 m n} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.drop m n) H3
  | ptr {H1 H2 H3 m l} :
    HLookup H1 l m H2 ->
    Drop H2 m H3 ->
    Drop H1 (.ptr l) H3
  | null {H} : Drop H .null H -- free(NULL) in C does nothing

/- Force drop-reductions to have deterministic eval order.  -/
@[simp]def DropFree : Tm Srt -> Prop
  | .var _ => True
  | .lam _ _ => True
  | .app m n => DropFree m ∧ DropFree n
  | .tup m n _ => DropFree m ∧ DropFree n
  | .prj m _ => DropFree m
  | .tt => True
  | .ff => True
  | .ite m _ _ => DropFree m
  | .drop _ _ => False
  | .ptr _ => True
  | .null => True

/- Heap allocated values. -/
@[scoped aesop safe [constructors]]
inductive HValue : Tm Srt -> Srt -> Prop where
  | lam {m s}   : HValue (.lam m s) s
  | tup {l p s} : Nullptr p -> HValue (.tup (.ptr l) p s) s
  | tt : HValue .tt ord.e
  | ff : HValue .ff ord.e

/- State (Heap + Term) of the evaluator. -/
abbrev State Srt := Heap Srt × Tm Srt

/- Drop-reductions. -/
@[scoped aesop safe [constructors]]
inductive Step0 : State Srt -> State Srt -> Prop where
  | app_M {H1 H2 m m'} n :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .app m n) (H2, .app m' n)
  | app_N {H1 H2} m {n n'} :
    DropFree m ->
    Step0 (H1, n) (H2, n') ->
    Step0 (H1, .app m n) (H2, .app m n')
  | tup_M {H1 H2 m m'} n s :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .tup m n s) (H2, .tup m' n s)
  | tup_N {H1 H2} m {n n'} s :
    DropFree m ->
    Step0 (H1, n) (H2, n') ->
    Step0 (H1, .tup m n s) (H2, .tup m n' s)
  | prj_M {H1 H2 m m'} n :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .prj m n) (H2, .prj m' n)
  | ite_M {H1 H2 m m'} n1 n2 :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .ite m n1 n2) (H2, .ite m' n1 n2)
  | drop_elim {H1 H2 m n} :
    Drop H1 m H2 ->
    Step0 (H1, .drop m n) (H2, n)

/- Alloc-reductions. -/
@[scoped aesop safe [constructors]]
inductive Step1 : State Srt -> State Srt -> Prop where
  | app_M {H1 H2 m m'} n :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .app m n) (H2, .app m' n)
  | app_N {H1 H2} l {n n'} :
    Step1 (H1, n) (H2, n') ->
    Step1 (H1, .app (.ptr l) n) (H2, .app (.ptr l) n')
  | tup_M {H1 H2 m m'} n s :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .tup m n s) (H2, .tup m' n s)
  | tup_N {H1 H2} l {n n'} s :
    Step1 (H1, n) (H2, n') ->
    Step1 (H1, .tup (.ptr l) n s) (H2, .tup (.ptr l) n' s)
  | prj_M {H1 H2 m m'} n :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .prj m n) (H2, .prj m' n)
  | ite_M {H1 H2 m m'} n1 n2 :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .ite m n1 n2) (H2, .ite m' n1 n2)
  | alloc {H v s l} :
    l ∉ H.keys ->
    HValue v s ->
    Step1 (H, v) (H.insert l ⟨v, s⟩, .ptr l)

/- Core-reductions. -/
@[scoped aesop safe [constructors]]
inductive Step2 : State Srt -> State Srt -> Prop where
  | app_M {H H' m m' n} :
    Step2 (H, m) (H', m') ->
    Step2 (H, .app m n) (H', .app m' n)
  | app_N {H H' m n n'} :
    Step2 (H, n) (H', n') ->
    Step2 (H, .app m n) (H', .app m n')
  | beta {H1 H2 m s lf p} :
    Nullptr p ->
    HLookup H1 lf (.lam m s) H2 ->
    Step2 (H1, .app (.ptr lf) p) (H2, m.[p/])
  | tup_M {H H' m m' n s} :
    Step2 (H, m) (H', m') ->
    Step2 (H, .tup m n s) (H', .tup m' n s)
  | tup_N {H H' m n n' s} :
    Step2 (H, n) (H', n') ->
    Step2 (H, .tup m n s) (H', .tup m n' s)
  | prj_M {H H' m m' n} :
    Step2 (H, m) (H', m') ->
    Step2 (H, .prj m n) (H', .prj m' n)
  | prj_elim {H1 H2 H3 n s l l1 p} :
    Nullptr p ->
    HLookup H1 l (.tup (.ptr l1) p s) H2 ->
    Step2 (H1, .prj (.ptr l) n) (H3, n.[p,.ptr l1/])
  | ite_M {H H' m m' n1 n2} :
    Step2 (H, m) (H', m') ->
    Step2 (H, .ite m n1 n2) (H', .ite m' n1 n2)
  | ite_tt {H H' n1 n2 l} :
    HLookup H l .tt H' ->
    Step2 (H, .ite (.ptr l) n1 n2) (H', n1)
  | ite_ff {H H' n1 n2 l} :
    HLookup H l .ff H' ->
    Step2 (H, .ite (.ptr l) n1 n2) (H', n2)

abbrev Red0 (t1 t2 : @State Srt) : Prop := Star Step0 t1 t2
abbrev Red1 (t1 t2 : @State Srt) : Prop := Star Step1 t1 t2

inductive Step (m : State Srt) : State Srt -> Prop where
  | intro {x y n} : Red0 m x -> Red1 x y -> Step2 y n -> Step m n

notation:50 t:50 " ~>> " t':51 => Step t t'
notation:50 t:50 " ~>>* " t':51 => Star Step t t'

lemma Step0.not_dropfree {H m} {t : State Srt} :
    Step0 (H, m) t -> ¬ DropFree m := by
  generalize e: (H, m) = t0
  intro st; induction st generalizing H m
  all_goals cases e; aesop

lemma Red0.var_inv {H x} {t : State Srt} :
    Red0 (H, .var x) t -> t = (H, .var x) := by
  intro rd; induction rd
  case R => simp
  case SE st ih =>
    subst_vars; cases st

lemma Red0.lam_inv {H m s} {t : State Srt}  :
    Red0 (H, .lam m s) t -> t = (H, .lam m s) := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.app_inv' {H1 m n} {t : State Srt} :
    Red0 (H1, .app m n) t ->
    ∃ H2 H3 m' n',
      t = (H3, .app m' n') ∧
      Red0 (H1, m) (H2, m') ∧
      Red0 (H2, n) (H3, n') ∧
      (¬DropFree m' -> H2 = H3 ∧ n = n') := by
  intro rd; induction rd
  case R =>
    exists H1, H1, m, n; aesop
  case SE st ih =>
    rcases ih with ⟨H2, H3, m', n', e, rd1, rd2, h⟩
    subst_vars
    cases st
    case app_M Hx mx st =>
      have ⟨e1, e2⟩ := h st.not_dropfree; subst_vars
      exists Hx, Hx, mx, n'; simp; and_intros
      apply Star.SE rd1 st
      apply Star.R
    case app_N Hx nx h st =>
      exists H2, Hx, m', nx; simp; and_intros
      . assumption
      . apply Star.SE rd2 st
      . intro; contradiction

lemma Red0.app_inv {H1 m n} {t : State Srt} :
    Red0 (H1, .app m n) t ->
    ∃ H2 H3 m' n',
      t = (H3, .app m' n') ∧
      Red0 (H1, m) (H2, m') ∧
      Red0 (H2, n) (H3, n') := by
  intro rd; have := rd.app_inv'; aesop

lemma Red0.tup_inv' {H1 m n s} {t : State Srt} :
    Red0 (H1, .tup m n s) t ->
    ∃ H2 H3 m' n',
      t = (H3, .tup m' n' s) ∧
      Red0 (H1, m) (H2, m') ∧
      Red0 (H2, n) (H3, n') ∧
      (¬DropFree m' -> H2 = H3 ∧ n = n') := by
  intro rd; induction rd
  case R =>
    exists H1, H1, m, n; aesop
  case SE st ih =>
    rcases ih with ⟨H2, H3, m', n', e, rd1, rd2, h⟩
    subst_vars
    cases st
    case tup_M Hx mx st =>
      have ⟨e1, e2⟩ := h st.not_dropfree; subst_vars
      exists Hx, Hx, mx, n'; simp; and_intros
      apply Star.SE rd1 st
      apply Star.R
    case tup_N Hx nx h st =>
      exists H2, Hx, m', nx; simp; and_intros
      . assumption
      . apply Star.SE rd2 st
      . intro; contradiction

lemma Red0.tup_inv {H1 m n s} {t : State Srt} :
    Red0 (H1, .tup m n s) t ->
    ∃ H2 H3 m' n',
      t = (H3, .tup m' n' s) ∧
      Red0 (H1, m) (H2, m') ∧
      Red0 (H2, n) (H3, n') := by
  intro rd; have := rd.tup_inv'; aesop

lemma Red0.prj_inv {H1 m n} {t : State Srt} :
    Red0 (H1, .prj m n) t ->
    ∃ H2 m', t = (H2, .prj m' n) ∧ Red0 (H1, m) (H2, m') := by
  intro rd; induction rd
  case R => exists H1, m; aesop
  case SE st ih =>
    rcases ih with ⟨H2, m', e, rd⟩
    subst_vars; cases st
    case prj_M Hx mx st =>
      exists Hx, mx; simp
      apply Star.SE rd st

lemma Red0.tt_inv {H1} (t : State Srt) :
    Red0 (H1, .tt) t -> t = (H1, .tt) := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.ff_inv {H1} (t : State Srt) :
    Red0 (H1, .ff) t -> t = (H1, .ff) := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.ite_inv {H1 m n1 n2} {t : State Srt} :
    Red0 (H1, .ite m n1 n2) t ->
    ∃ H2 m', t = (H2, .ite m' n1 n2) ∧ Red0 (H1, m) (H2, m') := by
  intro rd; induction rd
  case R => simp; aesop
  case SE rd st ih =>
    rcases ih with ⟨H2, m', e, rd0⟩
    subst_vars; cases st
    case ite_M Hx mx st =>
      exists Hx, mx; simp
      apply Star.SE rd0 st

lemma Red0.ptr_inv {H1 l} {t : State Srt} :
    Red0 (H1, .ptr l) t -> t = (H1, .ptr l) := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.null_inv {H1} {t : State Srt} :
    Red0 (H1, .null) t -> t = (H1, .null) := by
  intro rd; induction rd
  case R => simp
  case SE st e => subst_vars; cases st

lemma Red0.app_M {H1 H2} {m m' n : Tm Srt} :
    Red0 (H1, m) (H2, m') ->
    Red0 (H1, .app m n) (H2, .app m' n) := by
  intro rm
  apply Star.hom (fun (H, x) => (H, Tm.app x n)) _ rm (e2 := Step0)
  simp; aesop

lemma Drop.wr_image {H1 H2 : Heap Srt} {m} :
    Drop H1 m H2 -> WR H1 -> WR H2 := by
  intro dp wr; induction dp
  all_goals try (solve|aesop)
  case ptr lk dp ih => have := lk.wr_image wr; aesop

lemma Drop.resolve {H1 H2 H3 H4 : Heap Srt} {m m'} :
    Drop H3 m H4 -> H1 ⊢ m ▷ m' ->
    HMerge H1 H2 H3 -> Weaken H1 ->
    ∃ H0, HMerge H0 H2 H4 ∧ Weaken H0 ∧ Contra H0 := by
  intro dp rs mrg wk; induction rs generalizing H2 H3 H4
  case var => cases dp; aesop
  case lam => cases dp; aesop
  case app mrg0 rsm rsn ihm ihn =>
    cases dp; case app dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨wk1, wk2⟩ := mrg0.split_weaken wk
    have ⟨H2x, mrg3, wk3, ct3⟩ := ihm dp1 mrg2.sym wk1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, wk4, ct4⟩ := ihn dp2 mrg5.sym wk2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.weaken_image wk3 wk4
    . apply mrg7.contra_image ct3 ct4
  case tup mrg0 rsm rsn ihm ihn =>
    cases dp; case tup dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨wk1, wk2⟩ := mrg0.split_weaken wk
    have ⟨H2x, mrg3, wk3, ct3⟩ := ihm dp1 mrg2.sym wk1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, wk4, ct4⟩ := ihn dp2 mrg5.sym wk2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.weaken_image wk3 wk4
    . apply mrg7.contra_image ct3 ct4
  case prj mrg0 rsm rsn ihm ihn =>
    cases dp; case prj dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨wk1, wk2⟩ := mrg0.split_weaken wk
    have ⟨H2x, mrg3, wk3, ct3⟩ := ihm dp1 mrg2.sym wk1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, wk4, ct4⟩ := ihn dp2 mrg5.sym wk2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.weaken_image wk3 wk4
    . apply mrg7.contra_image ct3 ct4
  case tt => cases dp; aesop
  case ff => cases dp; aesop
  case ite mrg0 rsm1 rsn1 rsn2 ihm ihn1 ihn2 =>
    cases dp; case ite dp1 dp2 dp3 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨wk1, wk2⟩ := mrg0.split_weaken wk
    have ⟨H2x, mrg3, wk3, ct3⟩ := ihm dp1 mrg2.sym wk1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, wk4, ct4⟩ := ihn1 dp2 mrg5.sym wk2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.weaken_image wk3 wk4
    . apply mrg7.contra_image ct3 ct4
  case drop mrg0 _ rsm rsn ihm ihn =>
    cases dp; case drop dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨wk1, wk2⟩ := mrg0.split_weaken wk
    have ⟨H2x, mrg3, wk3, ct3⟩ := ihm dp1 mrg2.sym wk1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, wk4, ct4⟩ := ihn dp2 mrg5.sym wk2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.weaken_image wk3 wk4
    . apply mrg7.contra_image ct3 ct4
  case null H1 _ => cases dp; aesop
  case ptr lk1 rs ih =>
    cases dp; case ptr lk2 dp =>
    have ⟨e, mrg1⟩ := HLookup.collision mrg lk2 lk1; subst e
    have lw1 := lk1.weaken_image wk; aesop
