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
    Lower Δ s ->
    Typed (A :: Γ) (_: Δ) m B ->
    Typed Γ Δ (.lam0 A m s) (.pi0 A B s)
  | lam1 {Γ Δ A B m} s :
    Lower Δ s ->
    Typed (A :: Γ) (A :⟨s⟩ Δ) m B ->
    Typed Γ Δ (.lam1 A m s) (.pi1 A B s)
  | app0 Γ Δ A B m n s :
    Typed Γ Δ m (.pi0 A B s) ->
    Γ ⊢ n : A ->
    Typed Γ Δ (.app m n) B.[n/]
  | app1 Γ Δ1 Δ2 Δ A B m n s :
    Merge Δ1 Δ2 Δ ->
    Typed Γ Δ1 m (.pi1 A B s) ->
    Typed Γ Δ2 n A ->
    Typed Γ Δ (.app m n) B.[n/]
  | tup0 Γ Δ A B m n s i :
    Γ ⊢ .sig0 A B s : .srt s i ->
    Typed Γ Δ m A ->
    Γ ⊢ n : B.[m/] ->
    Typed Γ Δ (.tup0 m n s) (.sig0 A B s)
  | tup1 Γ Δ1 Δ2 Δ A B m n s i :
    Merge Δ1 Δ2 Δ ->
    Γ ⊢ .sig1 A B s : .srt s i ->
    Typed Γ Δ1 m A ->
    Typed Γ Δ2 n B.[m/] ->
    Typed Γ Δ (.tup1 m n s) (.sig1 A B s)
  | proj0 Γ Δ1 Δ2 Δ A B C m n s1 s2 s3 i :
    Merge Δ1 Δ2 Δ ->
    (.sig A B t :: Γ) ⊢ C : Sort s l ->
    Typed Γ Δ1 m (.sig A B .im t) ->
    Typed (B :: A :: Γ) (_: A :⟨r⟩ Δ2) n C.[Pair0 (Var 1) (Var 0) t .: shift 2] ->
    Typed Γ Δ (.proj C m n) C.[m/]
  | dyn_letin1 Γ Δ1 Δ2 Δ A B C m n s r1 r2 t l :
    Δ1 ∘ Δ2 => Δ ->
    (Sig1 A B t :: Γ) ⊢ C : Sort s l ->
    Γ ; Δ1 ⊢ m : Sig1 A B t ->
    (B :: A :: Γ) ; B .{r2} A .{r1} Δ2 ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
    Γ ; Δ ⊢ LetIn C m n : C.[m/]

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
