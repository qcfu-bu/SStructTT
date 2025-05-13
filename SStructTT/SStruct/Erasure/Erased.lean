import SStructTT.SStruct.Dynamic.Typed
import SStructTT.SStruct.Erasure.Syntax

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

@[scoped aesop safe [constructors]]
inductive RSrt : Rlv -> Srt -> Ctrl -> Prop where
  | extend {s} : RSrt .ex s .keep
  | weaken {s} :
    s ∈ ord.weaken_set ->
    RSrt .im s .drop

open Dynamic in
inductive Erased :
  Static.Ctx Srt -> Dynamic.Ctx Srt ->
  SStruct.Tm Srt -> Erasure.Tm Srt ->
  SStruct.Tm Srt ->
  Prop
where
  | var {Γ Δ x s A} :
    Wf Γ Δ ->
    Has Δ x s A ->
    Erased Γ Δ (.var x) (.var x) A

  | lam_im {Γ Δ A B m m' s sA iA} :
    Δ ≤* s ->
    Γ ⊢ A : .srt sA iA ->
    Erased (A :: Γ) (A :⟨.im, sA⟩ Δ) m m' B ->
    Erased Γ Δ (.lam A m .im s) (.lam m' .keep s) (.pi A B .im s)

  | lam_ex {Γ Δ A B m em0 em1 rA s sA iA} :
    RSrt rA sA em0 em1 ->
    Δ ≤* s ->
    Γ ⊢ A : .srt sA iA ->
    Erased (A :: Γ) (A :⟨rA, sA⟩ Δ) m em0 B ->
    Erased Γ Δ (.lam A m .ex s) (.lam em1 s) (.pi A B .ex s)

  | app_im {Γ Δ A B m m' n s} :
    Erased Γ Δ m m' (.pi A B .im s) ->
    Γ ⊢ n : A ->
    Erased Γ Δ (.app m n .im) (.app m' .none) B.[n/]

  | app_ex {Γ Δ1 Δ2 Δ A B m m' n n' s} :
    Merge Δ1 Δ2 Δ ->
    Erased Γ Δ1 m m' (.pi A B .ex s) ->
    Erased Γ Δ2 n n' A ->
    Erased Γ Δ (.app m n .ex) (.app m' n') B.[n/]

  | tup_im {Γ Δ A B m m' n s i} :
    Γ ⊢ .sig A B .im s : .srt s i ->
    Erased Γ Δ m m' A ->
    Γ ⊢ n : B.[m/] ->
    Erased Γ Δ (.tup m n .im s) (.tup m' .none s) (.sig A B .im s)

  | tup_ex {Γ Δ1 Δ2 Δ A B m m' n n' s i} :
    Merge Δ1 Δ2 Δ ->
    Γ ⊢ .sig A B .ex s : .srt s i ->
    Erased Γ Δ1 m m' A ->
    Erased Γ Δ2 n n' B.[m/] ->
    Erased Γ Δ (.tup m n .ex s) (.tup m' n' s) (.sig A B .ex s)

  | proj_im {Γ Δ1 Δ2 Δ A B C m m' n n' n'' rA s sA sB sC iC} :
    RSrt rA sA n' n'' ->
    Merge Δ1 Δ2 Δ ->
    .sig A B .im s :: Γ ⊢ C : .srt sC iC ->
    Erased Γ Δ1 m m' (.sig A B .im s) ->
    Erased (B :: A :: Γ) (B :⟨.im, sB⟩ A :⟨rA, sA⟩ Δ2) n n' C.[.tup (.var 1) (.var 0) .im s .: shift 2] ->
    Erased Γ Δ (.proj C m n .im) (.proj m' n'') C.[m/]

  | proj_ex {Γ Δ1 Δ2 Δ A B C m m' n n' n'' n''' rA rB s sA sB sC iC} :
    RSrt rA sA n' n'' ->
    RSrt rB sB n'' n''' ->
    Merge Δ1 Δ2 Δ ->
    .sig A B .ex s :: Γ ⊢ C : .srt sC iC ->
    Erased Γ Δ1 m m' (.sig A B .ex s) ->
    Erased (B :: A :: Γ) (B :⟨rB, sB⟩ A :⟨rA, sA⟩ Δ2) n n' C.[.tup (.var 1) (.var 0) .ex s .: shift 2] ->
    Erased Γ Δ (.proj C m n .ex) (.proj m' n''') C.[m/]

/-
  | tt {Γ Δ} :
    Wf Γ Δ ->
    Δ.Forall (∃ A s, . = (A, .im, s)) ->
    Typed Γ Δ .tt .bool

  | ff {Γ Δ} :
    Wf Γ Δ ->
    Δ.Forall (∃ A s, . = (A, .im, s)) ->
    Typed Γ Δ .ff .bool

  | ite {Γ Δ1 Δ2 Δ A m n1 n2 s i} :
    Merge Δ1 Δ2 Δ ->
    .bool :: Γ ⊢ A : .srt s i ->
    Typed Γ Δ1 m .bool ->
    Typed Γ Δ2 n1 A.[.tt/] ->
    Typed Γ Δ2 n2 A.[.ff/] ->
    Typed Γ Δ (.ite A m n1 n2) A.[m/]

  | rw {Γ Δ A B m n a b s i} :
    .idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ ⊢ A : .srt s i ->
    Typed Γ Δ m A.[.rfl a,a/] ->
    Γ ⊢ n : .idn B a b ->
    Typed Γ Δ (.rw A m n) A.[n,b/]

  | conv {Γ Δ A B m s i} :
    A === B ->
    Typed Γ Δ m A ->
    Γ ⊢ B : .srt s i ->
    Typed Γ Δ m B
-/
