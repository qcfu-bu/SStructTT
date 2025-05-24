import SStructTT.SStruct.Runtime.Resolution

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

inductive Step : Heap Srt -> Tm Srt -> Heap Srt -> Tm Srt -> Prop where
  | alloc {H v s l} :
    l ∉ H.keys ->
    HValue v s ->
    Step H v (H.insert l ⟨v, s⟩) (.ptr l)
  | app_M {H H' m m' n} :
    Step H m H' m' ->
    Step H (.app m n) H' (.app m' n)
  | app_N {H H' m n n'} :
    Step H n H' n' ->
    Step H (.app m n) H' (.app m n')
  | beta {H1 H2 m s lf p} :
    Nullptr p ->
    HLookup H1 lf (.lam m s) H2 ->
    Step H1 (.app (.ptr lf) p) H2 m.[p/]
  | tup_M {H H' m m' n s} :
    Step H m H' m' ->
    Step H (.tup m n s) H' (.tup m' n s)
  | tup_N {H H' m n n' s} :
    Step H n H' n' ->
    Step H (.tup m n s) H' (.tup m n' s)
  | prj_M {H H' m m' n} :
    Step H m H' m' ->
    Step H (.prj m n) H' (.prj m' n)
  | prj_elim {H1 H2 H3 n s l l1 p} :
    Nullptr p ->
    HLookup H1 l (.tup (.ptr l1) p s) H2 ->
    Step H1 (.prj (.ptr l) n) H3 n.[p,.ptr l1/]
  | ite_M {H H' m m' n1 n2} :
    Step H m H' m' ->
    Step H (.ite m n1 n2) H' (.ite m' n1 n2)
  | ite_tt {H H' n1 n2 l} :
    HLookup H l .tt H' ->
    Step H (.ite (.ptr l) n1 n2) H' n1
  | ite_ff {H H' n1 n2 l} :
    HLookup H l .ff H' ->
    Step H (.ite (.ptr l) n1 n2) H' n2
  | drop {H1 H2 m n} :
    Drop H1 m H2 ->
    Step H1 (.drop m n) H2 n

notation:50 H:50 " ;; " m:51 " ~>> " H':51 " ;; " m':51 =>
  Step H m H' m'
