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
  | pi {Γ A B} r s {sA sB iA iB} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) B (.srt sB iB) ->
    Typed Γ (.pi A B r s) (.srt s (max iA iB))
  | lam {Γ A B m} r s {sA iA} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) m B ->
    Typed Γ (.lam A m r s) (.pi A B r s)
  | app {Γ A B m n r s} :
    Typed Γ m (.pi A B r s) ->
    Typed Γ n A ->
    Typed Γ (.app m n) B.[n/]
  | sig {Γ A B} r s {sA sB iA iB} :
    Typed Γ A (.srt sA iA) ->
    Typed (A :: Γ) B (.srt sB iB) ->
    Typed Γ (.sig A B r s) (.srt s (max iA iB))
  | pair {Γ A B m n r s i} :
    Typed Γ (.sig A B r s) (.srt s i) ->
    Typed Γ m A ->
    Typed Γ n B.[m/] ->
    Typed Γ (.pair m n r s) (.sig A B r s)
  | proj {Γ A B C m n r s sC iC} :
    Typed (.sig A B r s :: Γ) C (.srt sC iC) ->
    Typed Γ m (.sig A B r s) ->
    Typed (B :: A :: Γ) n C.[.pair (.var 1) (.var 0) r s .: shift 2] ->
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
  | id {Γ A m n s i} :
    Typed Γ A (.srt s i) ->
    Typed Γ m A ->
    Typed Γ n A ->
    Typed Γ  (.id A m n) (.srt s0 i)
  | rfl {Γ A m} :
    Typed Γ m A ->
    Typed Γ (.rfl m) (.id A m m)
  | rw {Γ A B m n a b s i} :
    Typed (.id A.[shift 1] a.[shift 1] (.var 0) :: A :: Γ) B (.srt s i) ->
    Typed Γ m B.[.rfl a,a/] ->
    Typed Γ n (.id A a b) ->
    Typed Γ (.rw B m n) B.[n,b/]
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
