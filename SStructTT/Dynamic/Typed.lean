import SStructTT.Static.Typed
import SStructTT.Dynamic.Context

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

mutual
inductive Typed : Static.Ctx Srt -> Dynamic.Ctx Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {Γ Δ x s A} :
    Wf Γ Δ ->
    Has Δ x s A ->
    Typed Γ Δ (.var x) A
  | lam0 {Γ Δ A B m} s :
    Δ !≤ s ->
    Typed (A :: Γ) (_: Δ) m B ->
    Typed Γ Δ (.lam0 A m s) (.pi0 A B s)
  | lam1 {Γ Δ A B m} s :
    Δ !≤ s ->
    Typed (A :: Γ) (A :⟨s⟩ Δ) m B ->
    Typed Γ Δ (.lam1 A m s) (.pi1 A B s)
  | app0 Γ Δ A B m n s :
    Typed Γ Δ m (.pi0 A B s) ->
    Γ ⊢ n : A ->
    Typed Γ Δ (.app m n) B.[n/]
  | app1 Γ Δ1 Δ2 Δ A B m n s :
    Δ1 ∪ Δ2 => Δ ->
    Typed Γ Δ1 m (.pi1 A B s) ->
    Typed Γ Δ2 n A ->
    Typed Γ Δ (.app m n) B.[n/]
  | tup0 Γ Δ A B m n s i :
    Γ ⊢ .sig0 A B s : .srt s i ->
    Typed Γ Δ m A ->
    Γ ⊢ n : B.[m/] ->
    Typed Γ Δ (.tup0 m n s) (.sig0 A B s)
  | tup1 Γ Δ1 Δ2 Δ A B m n s i :
    Δ1 ∪ Δ2 => Δ ->
    Γ ⊢ .sig1 A B s : .srt s i ->
    Typed Γ Δ1 m A ->
    Typed Γ Δ2 n B.[m/] ->
    Typed Γ Δ (.tup1 m n s) (.sig1 A B s)
  | proj0 Γ Δ1 Δ2 Δ A B C m n s sA sC iC :
    Δ1 ∪ Δ2 => Δ ->
    .sig0 A B s :: Γ ⊢ C : .srt sC iC ->
    Typed Γ Δ1 m (.sig0 A B s) ->
    Typed (B :: A :: Γ) (_: A :⟨sA⟩ Δ2) n C.[.tup0 (.var 1) (.var 0) s .: shift 2] ->
    Typed Γ Δ (.proj C m n) C.[m/]
  | proj1 Γ Δ1 Δ2 Δ A B C m n s sA sB sC iC :
    Δ1 ∪ Δ2 => Δ ->
    .sig1 A B s :: Γ ⊢ C : .srt sC iC ->
    Typed Γ Δ1 m (.sig1 A B s) ->
    Typed (B :: A :: Γ) (B :⟨sB⟩ A :⟨sA⟩ Δ2) n C.[.tup1 (.var 1) (.var 0) s .: shift 2] ->
    Typed Γ Δ (.proj C m n) C.[m/]

inductive Wf : Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop where
  | nil : Wf [] []
  | ex Γ Δ A s i :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (A :⟨s⟩ Δ)
  | im Γ Δ A s i :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (_: Δ)
end

notation:50 Γ:50 "; " Δ:51 " ⊢ " m:51 " : " A:51 => Typed Γ Δ m A
notation:50 Γ:50 "; " Δ:51 " ⊢ " => Wf Γ Δ
