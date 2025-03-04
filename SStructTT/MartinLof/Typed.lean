import SStructTT.MartinLof.Syntax
import SStructTT.MartinLof.Context
import SStructTT.MartinLof.Confluence

namespace MartinLof

mutual
inductive Typed : Ctx -> Tm -> Tm -> Prop where
  | srt {Γ} i :
    Wf Γ ->
    Typed Γ (.ty i) (.ty (i + 1))

  | var {Γ x A} :
    Wf Γ ->
    Has Γ x A ->
    Typed Γ (.var x) A

  | pi {Γ A B iA iB} :
    Typed Γ A (.ty iA) ->
    Typed (A :: Γ) B (.ty iB) ->
    Typed Γ (.pi A B) (.ty (max iA iB))

  | lam {Γ A B m iA} :
    Typed Γ A (.ty iA) ->
    Typed (A :: Γ) m B ->
    Typed Γ (.lam A m) (.pi A B)

  | app {Γ A B m n} :
    Typed Γ m (.pi A B) ->
    Typed Γ n A ->
    Typed Γ (.app m n) B.[n/]

  | sig {Γ A B iA iB} :
    Typed Γ A (.ty iA) ->
    Typed (A :: Γ) B (.ty iB) ->
    Typed Γ (.sig A B) (.ty (max iA iB))

  | tup {Γ A B m n i} :
    Typed Γ (.sig A B) (.ty i) ->
    Typed Γ m A ->
    Typed Γ n B.[m/] ->
    Typed Γ (.tup m n) (.sig A B)

  | proj {Γ A B C m n iC} :
    Typed (.sig A B :: Γ) C (.ty iC) ->
    Typed Γ m (.sig A B) ->
    Typed (B :: A :: Γ) n C.[.tup (.var 1) (.var 0) .: shift 2] ->
    Typed Γ (.proj C m n) C.[m/]

  | bool {Γ} :
    Wf Γ ->
    Typed Γ .bool (.ty 0)

  | tt {Γ} :
    Wf Γ ->
    Typed Γ .tt .bool

  | ff {Γ} :
    Wf Γ ->
    Typed Γ .ff .bool

  | ite {Γ A m n1 n2 i} :
    Typed (.bool :: Γ) A (.ty i) ->
    Typed Γ m .bool ->
    Typed Γ n1 A.[.tt/] ->
    Typed Γ n2 A.[.ff/] ->
    Typed Γ (.ite A m n1 n2) A.[m/]

  | idn {Γ A m n i} :
    Typed Γ A (.ty i) ->
    Typed Γ m A ->
    Typed Γ n A ->
    Typed Γ (.idn A m n) (.ty i)

  | rfl {Γ A m} :
    Typed Γ m A ->
    Typed Γ (.rfl m) (.idn A m m)

  | rw {Γ A B m n a b i} :
    Typed (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A (.ty i) ->
    Typed Γ m A.[.rfl a,a/] ->
    Typed Γ n (.idn B a b) ->
    Typed Γ (.rw A m n) A.[n,b/]

  | conv {Γ A B m i} :
    A === B ->
    Typed Γ m A ->
    Typed Γ B (.ty i) ->
    Typed Γ m B

inductive Wf : Ctx -> Prop where
  | nil : Wf []
  | cons {Γ A i} :
    Typed Γ A (.ty i) ->
    Wf Γ ->
    Wf (A :: Γ)
end

notation:50 Γ:50 " ⊢ " m:51 " : " A:51 => Typed Γ m A
notation:50 Γ:50 " ⊢ " => Wf Γ

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Typed.rec_non_mutual {motive : ∀ Γ m A, Typed Γ m A -> Prop} :=
  Typed.rec (motive_1 := motive) (motive_2 := fun _ _ => True)

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Wf.rec_non_mutual {motive : ∀ Γ, Wf Γ -> Prop} :=
  Wf.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := motive)

lemma Typed.toWf {Γ A m} : Γ ⊢ m : A -> Γ ⊢ := by
  intro h; induction h
  all_goals trivial

lemma Typed.ctx_inv {Γ A B m} :
    A :: Γ ⊢ m : B -> ∃ i, Γ ⊢ ∧ Γ ⊢ A : .ty i := by
  intro ty; cases ty.toWf
  case cons i wf tyA => exists i
