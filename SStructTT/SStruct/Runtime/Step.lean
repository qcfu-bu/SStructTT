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
@[simp]def Ctrl.try_drop
    (c : Ctrl)
    (H1 : Heap Srt) (m : Tm Srt)
    (H2 : Heap Srt) (n : Tm Srt) : Prop :=
  match c with
  | .keep => H1 = H2 ∧ n = m
  | .drop => Drop H1 m H2 ∧ n = .null

namespace Runtime

@[simp]def HValue (m : Tm Srt) (s : Srt) :=
  match m with
  | .lam _ _ s0 => s = s0
  | .tup (.ptr _) (.ptr _) s0 => s = s0
  | .tup (.ptr _) .null s0 => s = s0
  | .tt => s = ord.e
  | .ff => s = ord.e
  | _ => False

inductive Step : Heap Srt -> Tm Srt -> Heap Srt -> Tm Srt -> Prop where
  | alloc H v s l :
    l ∉ H.keys ->
    HValue v s ->
    Step H v (H.insert l ⟨v, s⟩) (.ptr l)
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
    c.try_drop H2 (.ptr lv) H3 v ->
    Step H1 (.app (.ptr lf) (.ptr lv)) H2 m.[v/]
  | tup_M H H' m m' n s :
    Step H m H' m' ->
    Step H (.tup m n s) H' (.tup m' n s)
  | tup_N H H' m n n' s :
    Step H n H' n' ->
    Step H (.tup m n s) H' (.tup m n' s)
  | prj_M H H' m m' n c1 c2 :
    Step H m H' m' ->
    Step H (.prj m n c1 c2) H' (.prj m' n c1 c2)
  | prj_elim H1 H2 H3 H4 m1 m2 v1 v2 n c1 c2 s l :
    HLookup H1 l (.tup m1 m2 s) H2 ->
    c1.try_drop H2 m1 H3 v1 ->
    c2.try_drop H3 m2 H4 v2 ->
    Step H1 (.prj (.ptr l) n c1 c2) H4 n.[v2,v1/]
  | ite_M H H' m m' n1 n2 :
    Step H m H' m' ->
    Step H (.ite m n1 n2) H' (.ite m' n1 n2)
  | ite_tt H H' n1 n2 l :
    HLookup H l .tt H' ->
    Step H (.ite (.ptr l) n1 n2) H' n1
  | ite_ff H H' n1 n2 l :
    HLookup H l .ff H' ->
    Step H (.ite (.ptr l) n1 n2) H' n2
  | rw_elim H m :
    Step H (.rw m) H m

notation:50 H:50 " ;; " m:51 " ~>> " H':51 " ;; " m':51 =>
  Step H m H' m'
