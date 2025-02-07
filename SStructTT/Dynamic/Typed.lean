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
  | lam_ex {Γ Δ A B m} s {rA sA iA} :
    Δ !≤ s ->
    (¬sA ∈ weaken_set -> rA = .ex) ->
    Γ ⊢ A : .srt sA iA ->
    Typed (A :: Γ) (A :⟨rA, sA⟩ Δ) m B ->
    Typed Γ Δ (.lam A m .ex s) (.pi A B .ex s)
  | lam_im {Γ Δ A B m} s {sA iA} :
    Δ !≤ s ->
    Γ ⊢ A : .srt sA iA ->
    Typed (A :: Γ) (A :⟨.im, s⟩ Δ) m B ->
    Typed Γ Δ (.lam A m .im s) (.pi A B .im s)
  | app_im Γ Δ A B m n s :
    Typed Γ Δ m (.pi A B .im s) ->
    Γ ⊢ n : A ->
    Typed Γ Δ (.app m n .im) B.[n/]
  | app_ex Γ Δ1 Δ2 Δ A B m n s :
    Δ1 ∪ Δ2 => Δ ->
    Typed Γ Δ1 m (.pi A B .ex s) ->
    Typed Γ Δ2 n A ->
    Typed Γ Δ (.app m n .ex) B.[n/]
  -- | tup1 Γ Δ1 Δ2 Δ A B m n s i :
  --   Δ1 ∪ Δ2 => Δ ->
  --   Γ ⊢ .sig1 A B s : .srt s i ->
  --   Typed Γ Δ1 m A ->
  --   Typed Γ Δ2 n B.[m/] ->
  --   Typed Γ Δ (.tup1 m n s) (.sig1 A B s)
  -- | proj0 Γ Δ1 Δ2 Δ A B C m n s sA sC iC :
  --   Δ1 ∪ Δ2 => Δ ->
  --   .sig0 A B s :: Γ ⊢ C : .srt sC iC ->
  --   Typed Γ Δ1 m (.sig0 A B s) ->
  --   Typed (B :: A :: Γ) (_: A :⟨sA⟩ Δ2) n C.[.tup0 (.var 1) (.var 0) s .: shift 2] ->
  --   Typed Γ Δ (.proj C m n) C.[m/]
  -- | proj1 Γ Δ1 Δ2 Δ A B C m n s sA sB sC iC :
  --   Δ1 ∪ Δ2 => Δ ->
  --   .sig1 A B s :: Γ ⊢ C : .srt sC iC ->
  --   Typed Γ Δ1 m (.sig1 A B s) ->
  --   Typed (B :: A :: Γ) (B :⟨sB⟩ A :⟨sA⟩ Δ2) n C.[.tup1 (.var 1) (.var 0) s .: shift 2] ->
  --   Typed Γ Δ (.proj C m n) C.[m/]
  -- | tt Γ Δ :
  --   Wf Γ Δ ->
  --   Weak Δ ->
  --   Typed Γ Δ .tt .bool
  -- | ff Γ Δ :
  --   Wf Γ Δ ->
  --   Weak Δ ->
  --   Typed Γ Δ .ff .bool

inductive Wf : Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop where
  | nil : Wf [] []
  | ex Γ Δ A s i :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (A :⟨.ex, s⟩ Δ)
  | im Γ Δ A s i :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (A :⟨.im, s⟩ Δ)
end

notation:50 Γ:50 "; " Δ:51 " ⊢ " m:51 " : " A:51 => Typed Γ Δ m A
notation:50 Γ:50 "; " Δ:51 " ⊢ " => Wf Γ Δ
