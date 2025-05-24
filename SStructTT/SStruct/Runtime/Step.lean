import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime

variable {Srt : Type} [ord : SrtOrder Srt]

inductive Drop : Heap Srt -> Tm Srt -> Heap Srt -> Prop where
  | var {H x} : Drop H x H
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

@[scoped aesop safe [constructors]]
inductive Nullptr : Tm Srt -> Prop where
  | ptr {l} : Nullptr (.ptr l)
  | null    : Nullptr .null

@[scoped aesop safe [constructors]]
inductive HValue : Tm Srt -> Srt -> Prop where
  | lam {m s}   : HValue (.lam m s) s
  | tup {l p s} : Nullptr p -> HValue (.tup (.ptr l) p s) s
  | tt : HValue .tt ord.e
  | ff : HValue .ff ord.e

abbrev State Srt := Heap Srt × Tm Srt

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
    Step0 (H2, .tup m n s) (H2, .tup m' n s)
  | tup_N {H1 H2} m {n n'} s :
    Step0 (H1, n) (H2, n') ->
    Step0 (H2, .tup m n s) (H2, .tup m n' s)
  | prj_M {H1 H2 m m'} n :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .prj m n) (H2, .prj m' n)
  | ite_M {H1 H2 m m'} n1 n2 :
    Step0 (H1, m) (H2, m') ->
    Step0 (H1, .ite m n1 n2) (H2, .ite m' n1 n2)
  | alloc {H v s l} :
    l ∉ H.keys ->
    HValue v s ->
    Step0 (H, v) (H.insert l ⟨v, s⟩, .ptr l)
  | drop_elim {H1 H2 m n} :
    Drop H1 m H2 ->
    Step0 (H1, .drop m n) (H2, n)

@[scoped aesop safe [constructors]]
inductive Step1 : State Srt -> State Srt -> Prop where
  | app_M {H H' m m' n} :
    Step1 (H, m) (H', m') ->
    Step1 (H, .app m n) (H', .app m' n)
  | app_N {H H' m n n'} :
    Step1 (H, n) (H', n') ->
    Step1 (H, .app m n) (H', .app m n')
  | beta {H1 H2 m s lf p} :
    Nullptr p ->
    HLookup H1 lf (.lam m s) H2 ->
    Step1 (H1, .app (.ptr lf) p) (H2, m.[p/])
  | tup_M {H H' m m' n s} :
    Step1 (H, m) (H', m') ->
    Step1 (H, .tup m n s) (H', .tup m' n s)
  | tup_N {H H' m n n' s} :
    Step1 (H, n) (H', n') ->
    Step1 (H, .tup m n s) (H', .tup m n' s)
  | prj_M {H H' m m' n} :
    Step1 (H, m) (H', m') ->
    Step1 (H, .prj m n) (H', .prj m' n)
  | prj_elim {H1 H2 H3 n s l l1 p} :
    Nullptr p ->
    HLookup H1 l (.tup (.ptr l1) p s) H2 ->
    Step1 (H1, .prj (.ptr l) n) (H3, n.[p,.ptr l1/])
  | ite_M {H H' m m' n1 n2} :
    Step1 (H, m) (H', m') ->
    Step1 (H, .ite m n1 n2) (H', .ite m' n1 n2)
  | ite_tt {H H' n1 n2 l} :
    HLookup H l .tt H' ->
    Step1 (H, .ite (.ptr l) n1 n2) (H', n1)
  | ite_ff {H H' n1 n2 l} :
    HLookup H l .ff H' ->
    Step1 (H, .ite (.ptr l) n1 n2) (H', n2)

abbrev Red0 (t1 t2 : @State Srt) : Prop := Star Step0 t1 t2

inductive Step (m : State Srt) : State Srt -> Prop where
  | intro {m' n} : Red0 m m' -> Step1 m' n -> Step m n

notation:50 H:50 " ;; " m:51 " ~>> " H':51 " ;; " m':51 =>
  Step (H, m) (H', m')
