import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime

variable {Srt : Type} [ord : SrtOrder Srt]

/- Deallocate dropped terms. -/
@[scoped aesop safe [constructors]]
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
    Drop H1 (.ite m n1 n2) H3
  | drop {H1 H2 H3 m n} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.drop m n) H3
  | ptr {H1 H2 H3 m l} :
    HLookup H1 l m H2 ->
    Drop H2 m.tm H3 ->
    Drop H1 (.ptr l) H3
  | null {H} : Drop H .null H -- free(NULL) in C does nothing

/- Force drop-reductions to have deterministic eval order.  -/
@[simp]def drop_count : Tm Srt -> Nat
  | .var _ => 0
  | .lam _ _ => 0
  | .app m n => drop_count m + drop_count n
  | .tup m n _ => drop_count m + drop_count n
  | .prj m _ => drop_count m
  | .tt => 0
  | .ff => 0
  | .ite m _ _ => drop_count m
  | .drop _ _ => 1
  | .ptr _ => 0
  | .null => 0

/- State (Heap + Term) of the evaluator. -/
abbrev State Srt := Heap Srt × Tm Srt

/- Drop-reductions. -/
@[scoped aesop safe [constructors]]
inductive Step0 : State Srt -> State Srt -> Prop where
  | app_M {H1 H2 m m'} n :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .app m n) (H2, .app m' n)
  | app_N {H1 H2} m {n n'} :
    Step0 (H1, n) (H2, n') ->
    Step0 (H1, .app m n) (H2, .app m n')
  | tup_M {H1 H2 m m'} n s :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .tup m n s) (H2, .tup m' n s)
  | tup_N {H1 H2} m {n n'} s :
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
  | app_N {H1 H2} m {n n'} :
    Step1 (H1, n) (H2, n') ->
    Step1 (H1, .app m n) (H2, .app m n')
  | tup_M {H1 H2 m m'} n s :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .tup m n s) (H2, .tup m' n s)
  | tup_N {H1 H2} m {n n'} s :
    Step1 (H1, n) (H2, n') ->
    Step1 (H1, .tup m n s) (H2, .tup m n' s)
  | prj_M {H1 H2 m m'} n :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .prj m n) (H2, .prj m' n)
  | ite_M {H1 H2 m m'} n1 n2 :
    Step1 (H1, m) (H2, m') ->
    Step1 (H1, .ite m n1 n2) (H2, .ite m' n1 n2)
  | alloc_clo {H m s l} :
    l ∉ H ->
    (cl : Closed 1 m) ->
    Step1 (H, .lam m s) (H.insert l (.clo m s cl), .ptr l)
  | alloc_box {H s l l1} :
    l ∉ H.keys ->
    Step1 (H, .tup .null (.ptr l1) s) (H.insert l (.box l1 s), .ptr l)
  | alloc_tup {H s l l1 l2} :
    l ∉ H.keys ->
    Step1 (H, .tup (.ptr l1) (.ptr l2) s) (H.insert l (.tup l1 l2 s), .ptr l)
  | alloc_tt {H l} :
    l ∉ H.keys ->
    Step1 (H, .tt) (H.insert l .tt, .ptr l)
  | alloc_ff {H l} :
    l ∉ H ->
    Step1 (H, .ff) (H.insert l .ff, .ptr l)

/- Possibly NULL pointers. -/
@[scoped aesop safe [constructors]]
inductive Nullptr : Tm Srt -> Prop where
  | ptr {l} : Nullptr (.ptr l)
  | null    : Nullptr .null

/- Core-reductions. -/
@[scoped aesop safe [constructors]]
inductive Step2 : State Srt -> State Srt -> Prop where
  | app_M {H H' m m' n} :
    Step2 (H, m) (H', m') ->
    Step2 (H, .app m n) (H', .app m' n)
  | app_N {H H' m n n'} :
    Step2 (H, n) (H', n') ->
    Step2 (H, .app m n) (H', .app m n')
  | beta {H1 H2 m s lf p cl} :
    Nullptr p ->
    HLookup H1 lf (.clo m s cl) H2 ->
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
  | prj_box {H1 H2 n s l l1} :
    HLookup H1 l (.box l1 s) H2 ->
    Step2 (H1, .prj (.ptr l) n) (H2, n.[.ptr l1,.null/])
  | prj_tup {H1 H2 n s l l1 l2} :
    HLookup H1 l (.tup l1 l2 s) H2 ->
    Step2 (H1, .prj (.ptr l) n) (H2, n.[.ptr l2,.ptr l1/])
  | ite_M {H H' m m' n1 n2} :
    Step2 (H, m) (H', m') ->
    Step2 (H, .ite m n1 n2) (H', .ite m' n1 n2)
  | ite_tt {H H' n1 n2 l} :
    HLookup H l .tt H' ->
    Step2 (H, .ite (.ptr l) n1 n2) (H', n1)
  | ite_ff {H H' n1 n2 l} :
    HLookup H l .ff H' ->
    Step2 (H, .ite (.ptr l) n1 n2) (H', n2)

def Step01 (t1 t2 : State Srt) : Prop := (Union Step0 Step1) t1 t2

def Red0 (t1 t2 : State Srt) : Prop := Star Step0 t1 t2
def Red1 (t1 t2 : State Srt) : Prop := Star Step1 t1 t2
def Red01 (t1 t2 : State Srt) : Prop := Star Step01 t1 t2

inductive Step (x z : State Srt) : Prop where
  | intro {y : State Srt} :
    Red01 x y -> Normal Step01 y -> Step2 y z -> Step x z

notation:50 t:50 " ~>> " t':51 => Step t t'
notation:50 t:50 " ~>>* " t':51 => Star Step t t'
