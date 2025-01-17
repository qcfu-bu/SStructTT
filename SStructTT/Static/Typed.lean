import SStructTT.Defs.SStruct
import SStructTT.Defs.Syntax
import SStructTT.Static.Confluence
import SStructTT.Static.Context

namespace Static
variable {Srt : Type} [SStruct Srt]

mutual
inductive Typed : Ctx Srt -> Tm Srt -> Tm Srt -> Prop where
  | srt {Γ} s i :
    Wf Γ ->
    Typed Γ (.srt s i) (.srt s0 (i + 1))
  | var {Γ x A} :
    Wf Γ ->
    Has Γ x A ->
    Typed Γ (.var x) A
  | pi0 {Γ A B} s {sA sB iA iB} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) B (.srt sB iB) ->
    Typed Γ (.pi0 A B s) (.srt s (max iA iB))
  | pi1 {Γ A B} s {sA sB iA iB} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) B (.srt sB iB) ->
    Typed Γ (.pi1 A B s) (.srt s (max iA iB))
  | lam0 {Γ A B m} s {sA iA} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) m B ->
    Typed Γ (.lam0 A m s) (.pi0 A B s)
  | lam1 {Γ A B m} s {sA iA} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) m B ->
    Typed Γ (.lam1 A m s) (.pi1 A B s)
  | app0 {Γ A B m n s} :
    Typed Γ m (.pi0 A B s) ->
    Typed Γ n A ->
    Typed Γ (.app m n) B.[n/]
  | app1 {Γ A B m n s} :
    Typed Γ m (.pi1 A B s) ->
    Typed Γ n A ->
    Typed Γ (.app m n) B.[n/]
  | sig0 {Γ A B} s {sA sB iA iB} :
    sA ≤ s ->
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) B (.srt sB iB) ->
    Typed Γ (.sig0 A B s) (.srt s (max iA iB))
  | sig1 {Γ A B} s {sA sB iA iB} :
    sA ≤ s ->
    sB ≤ s ->
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) B (.srt sB iB) ->
    Typed Γ (.sig1 A B s) (.srt s (max iA iB))
  | tup0 {Γ A B m n s i} :
    Typed Γ (.sig0 A B s) (.srt s i) ->
    Typed Γ m A ->
    Typed Γ n B.[m/] ->
    Typed Γ (.tup0 m n s) (.sig0 A B s)
  | tup1 {Γ A B m n s i} :
    Typed Γ (.sig1 A B s) (.srt s i) ->
    Typed Γ m A ->
    Typed Γ n B.[m/] ->
    Typed Γ (.tup1 m n s) (.sig1 A B s)
  | proj0 {Γ A B C m n s sC iC} :
    Typed (.sig0 A B s :: Γ) C (.srt sC iC) ->
    Typed Γ m (.sig0 A B s) ->
    Typed (B :: A :: Γ) n C.[.tup0 (.var 1) (.var 0) s .: shift 2] ->
    Typed Γ (.proj C m n) C.[m/]
  | proj1 {Γ A B C m n s sC iC} :
    Typed (.sig1 A B s :: Γ) C (.srt sC iC) ->
    Typed Γ m (.sig1 A B s) ->
    Typed (B :: A :: Γ) n C.[.tup1 (.var 1) (.var 0) s .: shift 2] ->
    Typed Γ (.proj C m n) C.[m/]
  | bool {Γ} :
    Wf Γ ->
    Typed Γ .bool (.srt s0 0)
  | tt {Γ} :
    Wf Γ ->
    Typed Γ .tt .bool
  | ff {Γ} :
    Wf Γ ->
    Typed Γ .ff .bool
  | ite {Γ A m n1 n2 s i} :
    Typed (.bool :: Γ) A (.srt s i) ->
    Typed Γ m .bool ->
    Typed Γ n1 A.[.tt/] ->
    Typed Γ n2 A.[.ff/] ->
    Typed Γ (.ite A m n1 n2) A.[m/]
  | idn {Γ A m n s i} :
    Typed Γ A (.srt s i) ->
    Typed Γ m A ->
    Typed Γ n A ->
    Typed Γ (.idn A m n) (.srt s0 i)
  | rfl {Γ A m} :
    Typed Γ m A ->
    Typed Γ (.rfl m) (.idn A m m)
  | rw {Γ A B m n a b s i} :
    Typed (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A (.srt s i) ->
    Typed Γ m A.[.rfl a,a/] ->
    Typed Γ n (.idn B a b) ->
    Typed Γ (.rw A m n) A.[n,b/]
  | conv {Γ A B m s i} :
    A === B ->
    Typed Γ m A ->
    Typed Γ B (.srt s i) ->
    Typed Γ m B

inductive Wf : Ctx Srt -> Prop where
  | nil : Wf []
  | cons {Γ A s i} :
    Typed Γ A (.srt s i) ->
    Wf Γ ->
    Wf (A :: Γ)
end

notation:50 Γ:50 " ⊢ " m:51 " : " A:51 => Typed Γ m A
notation:50 Γ:50 " ⊢ " => Wf Γ

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Typed.rec_non_mutual {motive : ∀ Γ m a, @Typed Srt _ Γ m a -> Prop} :=
  Typed.rec (motive_1 := motive) (motive_2 := fun _ _ => True)

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Wf.rec_non_mutual {motive : ∀ Γ, @Wf Srt _ Γ -> Prop} :=
  Wf.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := motive)

lemma Typed.toWf {Γ : Ctx Srt} {A m} : Γ ⊢ m : A -> Γ ⊢ := by
  intro h
  induction h
  all_goals trivial

lemma Typed.ctx_inv {Γ : Ctx Srt} {A B m} :
    A :: Γ ⊢ m : B -> ∃ s i, Γ ⊢ ∧ Γ ⊢ A : .srt s i := by
  intro ty
  cases ty.toWf
  case cons s i wf tyA =>
    exists s, i
