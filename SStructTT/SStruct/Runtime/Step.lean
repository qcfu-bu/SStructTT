import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime

variable {Srt : Type} [ord : SrtOrder Srt]

def HLookup (H1 : Heap Srt) (l : Nat) (m : Tm Srt) (H2 : Heap Srt) : Prop :=
  match H1.lookup l with
  | some (m', s) =>
    m = m' ∧ if s ∈ ord.contra_set then H1 = H2 else H2 = H1.erase l
  | none => False

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

/- Possibly NULL pointers. -/
@[scoped aesop safe [constructors]]
inductive Nullptr : Tm Srt -> Prop where
  | ptr {l} : Nullptr (.ptr l)
  | null    : Nullptr .null

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
    Step1 (H2, .tup m n s) (H2, .tup m' n s)
  | tup_N {H1 H2} l {n n'} s :
    Step1 (H1, n) (H2, n') ->
    Step1 (H2, .tup (.ptr l) n s) (H2, .tup (.ptr l) n' s)
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

lemma HLookup.not_mem {H1 H2 : Heap Srt} {l1 l2 m} :
    HLookup H1 l1 m H2 -> l2 ∉ H1.keys -> l2 ∉ H2.keys := by
  intro lk h
  rw[HLookup] at lk
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none]
  split at lk <;> try trivial
  case h_1 opt m' s e =>
    have ⟨_, h⟩ := lk; split_ifs at h
    case pos => subst_vars; assumption
    case neg =>
      subst_vars
      cases l2.decEq l1 with
      | isTrue => subst_vars; apply Finmap.lookup_erase
      | isFalse ne => rw[Finmap.lookup_erase_ne ne]; assumption

lemma HLookup.insert {H1 H2 : Heap Srt} {l1 l2 m n s} :
    HLookup H1 l1 m H2 -> l2 ∉ H1.keys ->
    HLookup (H1.insert l2 ⟨n, s⟩) l1 m (H2.insert l2 ⟨n, s⟩) := by
  intro lk h
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
  rw[HLookup]
  cases l1.decEq l2 with
  | isTrue =>
    subst_vars
    rw[HLookup] at lk
    rw[h] at lk; simp at lk
  | isFalse ne =>
    rw[H1.lookup_insert_of_ne ne]
    rw[HLookup] at lk
    split at lk <;> try trivial
    replace ⟨_, lk⟩ := lk; subst_vars; simp
    split_ifs at lk <;> try simp_all
    apply Finmap.ext_lookup
    intro x
    cases x.decEq l2 with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]
      rw[Finmap.lookup_erase_ne (by aesop)]
      rw[Finmap.lookup_insert]
    | isFalse ne2 =>
      rw[Finmap.lookup_insert_of_ne _ ne2]
      cases x.decEq l1 with
      | isTrue =>
        subst_vars
        rw[Finmap.lookup_erase]
        rw[Finmap.lookup_erase]
      | isFalse ne1 =>
        repeat rw[Finmap.lookup_erase_ne ne1]
        rw[Finmap.lookup_insert_of_ne _ ne2]

lemma HLookup.insert_lookup {H H' : Heap Srt} {m n l s} :
    HLookup (H.insert l (m, s)) l n H' ->
    m = n ∧
      if s ∈ ord.contra_set
      then H' = H.insert l (m, s)
      else H' = H.erase l := by
  intro lk
  simp_rw[HLookup,Finmap.lookup_insert] at lk
  replace ⟨_, lk⟩ := lk; subst_vars; simp
  split_ifs at lk
  case pos h => simp[h]; aesop
  case neg h =>
    simp[h,lk]
    apply Finmap.ext_lookup
    intro x
    cases x.decEq l with
    | isTrue => subst_vars; repeat rw[Finmap.lookup_erase]
    | isFalse ne =>
      repeat rw[Finmap.lookup_erase_ne ne]
      rw[Finmap.lookup_insert_of_ne _ ne]

lemma HLookup.merge {H1 H1' H2 H3 : Heap Srt} {l m} :
    HLookup H1 l m H1' -> HMerge H1 H2 H3 ->
    ∃ H3', HLookup H3 l m H3' ∧ HMerge H1' H2 H3' := by
  intro lk mrg
  rw[HLookup] at lk; split at lk <;> try trivial
  case h_1 opt n s e =>
    replace ⟨_, lk⟩ := lk; subst_vars
    split_ifs at lk
    case pos h =>
      subst_vars
      exists H3; and_intros
      . replace mrg := mrg l
        rw[e] at mrg; split at mrg <;> try trivial
        case h_1 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
        case h_2 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
      . assumption
    case neg h =>
      subst_vars
      exists H3.erase l; and_intros
      . replace mrg := mrg l
        rw[e] at mrg; split at mrg <;> try trivial
        case h_1 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
        case h_2 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
      . intro x
        replace mrg := mrg x
        cases x.decEq l with
        | isTrue =>
          subst_vars
          rw[e] at mrg; split at mrg <;> try trivial
          case h_1 e _ _ =>
            rcases mrg with ⟨_, _, _, _, _⟩
            cases e; subst_vars
            contradiction
          case h_2 e h1 h2 =>
            rcases mrg with ⟨_, _⟩
            cases e; subst_vars
            simp[h1,h2,e]
        | isFalse ne =>
          simp[Finmap.lookup_erase_ne ne]
          assumption

lemma HLookup.lower {H H' : Heap Srt} {l m s} :
    HLookup H l m H' -> HLower H s -> HLower H' s := by
  intro lk
  unfold HLookup at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk; subst_vars
  split_ifs at lk <;> subst_vars
  . simp
  . apply HLower.erase_lower

lemma HLookup.collision {H1 H1' H2 H3 H3' : Heap Srt} {l m n} :
    HMerge H1 H2 H3 ->
    HLookup H3 l m H3' ->
    HLookup H1 l n H1' ->
    m = n ∧ HMerge H1' H2 H3' := by
  intro mrg lk1 lk2
  unfold HLookup at lk1 lk2
  split at lk1 <;> try trivial
  split at lk2 <;> try trivial
  replace ⟨_, lk1⟩ := lk1; subst_vars
  replace ⟨_, lk2⟩ := lk2; subst_vars
  case h_1 h1 _ _ _ h2 =>
    have h := Finmap.mem_of_lookup_eq_some h2
    have e := mrg.lookup_collision h
    rw[h1,h2] at e; cases e; simp
    split_ifs at lk1 <;> simp_all
    intro x; replace mrg := mrg x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      simp[Finmap.lookup_erase]
      simp[h1,h2] at mrg
      split at mrg <;> simp_all
      aesop
    | isFalse ne =>
      simp[Finmap.lookup_erase_ne ne]
      assumption

lemma HLookup.nf {H H' : Heap Srt} {l m} :
    HLookup H l m H' -> WR H -> NF 0 m := by
  intro lk wr
  unfold HLookup at lk; split at lk <;> try trivial
  case h_1 m' s h =>
    replace ⟨_, lk⟩ := lk; subst_vars
    split_ifs at lk
    case pos =>
      subst_vars
      replace wr := wr l
      simp[h] at wr; split at wr
      all_goals simp_all
    case neg =>
      subst_vars
      replace wr := wr l
      simp[h] at wr; split at wr
      all_goals simp_all

lemma HLookup.wr_image {H H' : Heap Srt} {l m} :
    HLookup H l m H' -> WR H -> WR H' := by
  intro lk wr x
  replace wr := wr x
  unfold HLookup at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk
  split_ifs at lk <;> simp_all
  subst_vars
  cases x.decEq l with
  | isTrue => subst_vars; simp[Finmap.lookup_erase]
  | isFalse ne =>
    simp[Finmap.lookup_erase_ne ne]
    assumption

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

-- n' : Tm Srt
-- s' : Srt
-- h1✝ : l ∉ Finmap.keys H1
-- H2 : Heap Srt
-- s : Srt
-- h0 : s ∈ SrtOrder.weaken_set
-- mx : Tm Srt
-- rsm : H1 ⊢ mx ▷ n'
-- ihm : ∀ {H2 H3 H3' : Heap Srt} {s : Srt},
--   HMerge H1 H2 H3 →
--     HLower H1 s → s ∈ SrtOrder.weaken_set → Drop H3 mx H3' → ∃ H1', HMerge H1' H2 H3' ∧ HLower H1' SrtOrder.e
-- lw0✝ : HLower (Finmap.insert l (mx, s') H1) s
-- lw0 : HLower H1 s
-- h : s' ∈ SrtOrder.contra_set
-- b : Bool
-- dec : l ∉ H2
-- H3x : Heap Srt
-- mrgx : HMerge H1 H2 H3x
-- h1 : l ∉ H3x
-- mrg0 : HMerge (Finmap.insert l (mx, s') H1) H2 (Finmap.insert l (mx, s') H3x)
-- H3y : Heap Srt
-- dp' : Drop H3x mx H3y
-- h2 : l ∉ H3y
-- dp : Drop (Finmap.insert l (mx, s') H3x) mx (Finmap.insert l (mx, s') H3y)
-- ⊢ ∃ H1', HMerge H1' H2 (Finmap.insert l (mx, s') H3y) ∧ HLower H1' SrtOrder.e

def SubHeap (H1 H2 : Heap Srt) : Prop :=
  ∀ l, l ∈ H1 -> H1.lookup l = H2.lookup l

omit ord in
lemma Heap.erase_insert_comm {H : Heap Srt} {l1 l2 x} :
    l1 ≠ l2 -> (H.insert l1 x).erase l2 = (H.erase l2).insert l1 x := by
  intro ne
  apply Finmap.ext_lookup; intro x
  if dec1: x = l1 then
    subst_vars; simp
    if dec2: x = l2
    then subst_vars; contradiction
    else rw[Finmap.lookup_erase_ne ne]; simp
  else
    if dec2: x = l2
    then
      subst_vars; simp
      rw[Finmap.lookup_insert_of_ne _ dec1]
      rw[Finmap.lookup_erase]
    else
      rw[Finmap.lookup_insert_of_ne _ dec1]
      rw[Finmap.lookup_erase_ne dec2]
      rw[Finmap.lookup_erase_ne dec2]
      rw[Finmap.lookup_insert_of_ne _ dec1]

lemma Drop.insert_inv {H0 H1 H2 : Heap Srt} {m m' x s l} :
    H0 ⊢ m ▷ m' ->
    Drop (H1.insert l (x, s)) m H2 ->
    SubHeap H0 H1 ->  l ∉ H0 -> l ∉ H1 ->
    ∃ H2', Drop H1 m H2' ∧ H2 = H2'.insert l (x, s) ∧ l ∉ H2' := by
  intro rsm dp sb h0 h1; induction rsm generalizing H1 H2 x s l
  case var =>
    cases dp
    exists H1; and_intros
    . constructor
    . rfl
    . assumption
  case lam ih =>
    cases dp; case lam dp =>
    have ⟨H2', dp, e, h2⟩ := ih dp sb h0 h1; subst e
    exists H2'; and_intros
    . constructor; assumption
    . rfl
    . assumption
  case app =>
    sorry
  case ptr l0 m m' s h2 rsm ih =>
    cases dp; case ptr H3 n lk dp =>
    have sb0 := sb l0; simp at sb0
    rw[Finmap.mem_insert] at h0; simp at h0
    rcases h0 with ⟨h3, h4⟩
    unfold HLookup at lk
    rw[Finmap.lookup_insert_of_ne _ (by aesop)] at lk
    rw[<-sb0] at lk; simp at lk
    rcases lk with ⟨e, lk⟩; subst e
    split_ifs at lk
    case pos =>
      subst_vars
      have ⟨H2', dp, e, h⟩ := ih dp sorry h4 h1
      exists H2'; and_intros
      . constructor
        pick_goal 2
        apply dp
        unfold HLookup
        rw[<-sb0]; simp
        intro
        contradiction
      . assumption
      . assumption
    case neg =>
      subst_vars
      rw[Heap.erase_insert_comm] at dp
      have ⟨H2', dp, e, h⟩ := ih dp sorry h4 sorry
      exists H2'; and_intros
      . constructor
        pick_goal 2
        apply dp
        unfold HLookup
        rw[<-sb0]; simp
        intro; contradiction
      . assumption
      . assumption
      . assumption
  all_goals sorry

/-

lemma Drop.resolve {H1 H2 H3 H3' : Heap Srt} {m m' s} :
    HMerge H1 H2 H3 -> HLower H1 s -> s ∈ ord.weaken_set ->
    H1 ⊢ m ▷ m' -> Drop H3 m H3' ->
    ∃ H1', HMerge H1' H2 H3' ∧ HLower H1' ord.e := by
  intro mrg0 lw0 h0 rs0 dp0; induction rs0 generalizing H2 H3 H3' s
  case var => cases dp0; exists ∅
  case lam => cases dp0; aesop
  case app mrg rsm rsn ihm ihn =>
    cases dp0; case app dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg0.split mrg.sym
    have ⟨lw1, lw2⟩ := mrg.split_lower lw0
    have ⟨H2x, mrg3, lw3⟩ := ihm mrg2.sym lw1 h0 dp1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, lw4⟩ := ihn mrg5.sym lw2 h0 dp2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.lower_image lw3 lw4
  case tup mrg rsm rsn ihm ihn =>
    cases dp0; case tup dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg0.split mrg.sym
    have ⟨lw1, lw2⟩ := mrg.split_lower lw0
    have ⟨H2x, mrg3, lw3⟩ := ihm mrg2.sym lw1 h0 dp1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, lw4⟩ := ihn mrg5.sym lw2 h0 dp2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.lower_image lw3 lw4
  case prj mrg rsm rsn ihm ihn =>
    cases dp0; case prj dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg0.split mrg.sym
    have ⟨lw1, lw2⟩ := mrg.split_lower lw0
    have ⟨H2x, mrg3, lw3⟩ := ihm mrg2.sym lw1 h0 dp1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, lw4⟩ := ihn mrg5.sym lw2 h0 dp2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.lower_image lw3 lw4
  case tt => cases dp0; exists ∅
  case ff => cases dp0; exists ∅
  case ite mrg rsm1 rsn1 rsn2 ihm ihn1 ihn2 =>
    cases dp0; case ite dp1 dp2 dp3 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg0.split mrg.sym
    have ⟨lw1, lw2⟩ := mrg.split_lower lw0
    have ⟨H2x, mrg3, lw3⟩ := ihm mrg2.sym lw1 h0 dp1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, lw4⟩ := ihn1 mrg5.sym lw2 h0 dp2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    have ⟨H4x, mrg6, lw4⟩ := ihn2 mrg5.sym lw2 h0 dp3
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.lower_image lw3 lw4
  case drop mrg _ _ rsm rsn ihm ihn =>
    cases dp0; case drop dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg0.split mrg.sym
    have ⟨lw1, lw2⟩ := mrg.split_lower lw0
    have ⟨H2x, mrg3, lw3⟩ := ihm mrg2.sym lw1 h0 dp1
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, lw4⟩ := ihn mrg5.sym lw2 h0 dp2
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    exists H5x; and_intros
    . assumption
    . apply mrg7.lower_image lw3 lw4
  case null H1 _ => cases dp0; exists H1
  case ptr H1 l n n' s' h1 rsm ihm =>
    cases dp0; case ptr mx lk2 dp =>
    unfold HLookup at lk2
    rw[mrg0.insert_lookup] at lk2; simp at lk2
    rcases lk2 with ⟨e, lk2⟩; subst e
    have lw0 := lw0.erase_lower l; simp[Heap.erase_insert,h1] at lw0
    cases ord.contra_dec s' with
    | isTrue h =>
      simp[h] at lk2; subst lk2
      have b : Bool := true
      if dec: l ∈ H2 then
        have mrg1 : HMerge H1 H2 H3 := by sorry
        have := ihm mrg1 lw0 h0 dp
        assumption
      else
        have ⟨H3x, mrgx, e, h2⟩ := HMerge.insert_inv mrg0 h1 dec; subst e
        have ⟨H3y, dp', e, h3⟩ := Drop.insert_inv rsm h1 h2 dp; subst e
        have ⟨H1', mrg', lw'⟩ := ihm mrgx lw0 h0 dp'
        have mrgx := mrg'.insert_left l mx s' h3
        exists (Finmap.insert l (mx, s') H1'); and_intros
        . assumption
        . intro x
          if e: x = l then
            subst_vars; simp
            have lw1 := lw0 x; simp at lw1
            have h3 := InterSet.weaken lw1 h0
            constructor <;> aesop
          else simp[e]; apply lw'
    | isFalse => sorry

-/
