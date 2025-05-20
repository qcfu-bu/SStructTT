import SStructTT.SStruct.Runtime.Resolution

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

open Runtime in
inductive Drop : Heap Srt -> Tm Srt -> Heap Srt -> Prop where
  | var {H x} : Drop H x H
  | lam {H1 H2 m c s} :
    Drop H1 m H2 ->
    Drop H1 (.lam m c s) H2
  | app {H1 H2 H3 m n} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.app m n) H3
  | tup {H1 H2 H3 m n s} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.tup m n s) H3
  | prj {H1 H2 H3 m n c1 c2} :
    Drop H1 m H2 ->
    Drop H2 n H3 ->
    Drop H1 (.prj m n c1 c2) H3
  | tt {H} : Drop H .tt H
  | ff {H} : Drop H .ff H
  | ite {H1 H2 H3 m n1 n2} :
    Drop H1 m H2 ->
    Drop H2 n1 H3 ->
    Drop H2 n2 H3 ->
    Drop H1 (.ite m n1 n2) H3
  | ptr {H1 H2 H3 m l} :
    HLookup H1 l m H2 ->
    Drop H2 m H3 ->
    Drop H1 (.ptr l) H3
  | null {H} : Drop H .null H

open Runtime in
@[simp]def Ctrl.do_drop
    (c : Ctrl)
    (H1 : Heap Srt) (m : Tm Srt)
    (H2 : Heap Srt) (n : Tm Srt) : Prop :=
  match c with
  | .keep => H1 = H2 ∧ n = m
  | .drop => Drop H1 m H2 ∧ n = .null

namespace Runtime

inductive Step : Heap Srt -> Tm Srt -> Heap Srt -> Tm Srt -> Prop where
  | lam H m c s l :
    l ∉ H.keys ->
    Step H (.lam m c s) (H.insert l ⟨.lam m c s, s⟩) (.ptr l)
  | app_M H H' m m' n :
    Step H m H' m' ->
    Step H (.app m n) H' (.app m' n)
  | app_N H H' m n n' :
    Step H n H' n' ->
    Step H (.app m n) H' (.app m n')
  | beta_null H1 H2 m c s l :
    HLookup H1 l (.lam m c s) H2 ->
    Step H1 (.app (.ptr l) .null) H2 m.[.null/]
  | beta_ptr H1 H2 H3 m v c s lf lv :
    HLookup H1 lf (.lam m c s) H2 ->
    c.do_drop H2 (.ptr lv) H3 v ->
    Step H1 (.app (.ptr lf) (.ptr lv)) H2 m.[v/]
