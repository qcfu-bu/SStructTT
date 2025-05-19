import SStructTT.SStruct.Runtime.Heap
import SStructTT.SStruct.Erasure.Erased

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

def HLookup (H1 : Heap Srt) (l : Nat) (m : Tm Srt) (H2 : Heap Srt) : Prop :=
  match H1.lookup l with
  | some ⟨n, s⟩ =>
    m = n ∧ (
      (s ∉ ord.contra_set -> H2 = H1.erase l) ∨
      (s ∈ ord.contra_set -> H1 = H2))
  | none => False

inductive Resolve : Heap Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {H x} :
    HLower H ord.e ->
    Resolve H (.var x) (.var x)

  | lam {H m m' c s} :
    HLower H s ->
    Resolve H m m' ->
    Resolve H (.lam m c s) (.lam m' c s)

  | app {H1 H2 H3 m m' n n'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.app m n) (.app m' n')

  | tup {H1 H2 H3 m m' n n' s} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.tup m n s) (.tup m' n' s)

  | proj {H1 H2 H3 m m' n n' c1 c2} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.proj m n c1 c2) (.proj m' n' c1 c2)

  | tt {H} :
    HLower H ord.e ->
    Resolve H .tt .tt

  | ff {H} :
    HLower H ord.e ->
    Resolve H .ff .ff

  | ite H1 H2 H3 m m' n1 n1' n2 n2' :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n1 n1' ->
    Resolve H2 n2 n2' ->
    Resolve H3 (.ite m n1 n2) (.ite m' n1' n2')

  | rw H m m' :
    Resolve H m m' ->
    Resolve H (.rw m) (.rw m')

  | ptr H H' l m m' :
    HLookup H l m H' ->
    Resolve H' m m' ->
    Resolve H (.ptr l) m'

  | none H :
    HLower H ord.e ->
    Resolve H .none .none

notation:50 H:50 " ;; " m:51 " ▷ " m':51 => Resolve H m m'

@[simp]def Resolved : Tm Srt -> Prop
  | .var _ => True
  | .lam m _ _ => Resolved m
  | .app m n => Resolved m ∧ Resolved n
  | .tup m n _ => Resolved m ∧ Resolved n
  | .proj m n _ _ => Resolved m ∧ Resolved n
  | .tt => True
  | .ff => True
  | .ite m n1 n2 => Resolved m ∧ Resolved n1 ∧ Resolved n2
  | .rw m => Resolved m
  | .ptr _ => False
  | .none => True

lemma Resolve.is_resolved {H : Heap Srt} {m m'} : H ;; m ▷ m' -> Resolved m' := by
  intro rs; induction rs
  all_goals aesop

inductive WellResolved :
  Heap Srt -> SStruct.Tm Srt -> Tm Srt -> Tm Srt -> SStruct.Tm Srt -> Prop
where
  | intro {H x y z A} :
    [] ;; [] ⊢ x ▷ y : A ->
    H ;; z ▷ y ->
    WellResolved H x y z A

notation:50 H:50 " ;; " x:51 " ▷ " y:51 " ◁ " z:51 " : " A:51 =>
  WellResolved H x y z A
