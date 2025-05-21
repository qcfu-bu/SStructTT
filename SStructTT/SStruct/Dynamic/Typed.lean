import SStructTT.SStruct.Static.Typed
import SStructTT.SStruct.Dynamic.Context

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

mutual
inductive Typed : Static.Ctx Srt -> Dynamic.Ctx Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {Γ Δ x s A} :
    Wf Γ Δ ->
    Has Δ x s A ->
    Typed Γ Δ (.var x) A

  | lam_im {Γ Δ A B m s sA iA} :
    Lower Δ s ->
    Γ ⊢ A : .srt sA iA ->
    Typed (A :: Γ) (A :⟨.im, sA⟩ Δ) m B ->
    Typed Γ Δ (.lam A m .im s) (.pi A B .im s)

  | lam_ex {Γ Δ A B m s sA iA} :
    Lower Δ s ->
    Γ ⊢ A : .srt sA iA ->
    Typed (A :: Γ) (A :⟨.ex, sA⟩ Δ) m B ->
    Typed Γ Δ (.lam A m .ex s) (.pi A B .ex s)

  | app_im {Γ Δ A B m n s} :
    Typed Γ Δ m (.pi A B .im s) ->
    Γ ⊢ n : A ->
    Typed Γ Δ (.app m n .im) B.[n/]

  | app_ex {Γ Δ1 Δ2 Δ A B m n s} :
    Merge Δ1 Δ2 Δ ->
    Typed Γ Δ1 m (.pi A B .ex s) ->
    Typed Γ Δ2 n A ->
    Typed Γ Δ (.app m n .ex) B.[n/]

  | tup_im {Γ Δ A B m n s i} :
    Γ ⊢ .sig A B .im s : .srt s i ->
    Typed Γ Δ m A ->
    Γ ⊢ n : B.[m/] ->
    Typed Γ Δ (.tup m n .im s) (.sig A B .im s)

  | tup_ex {Γ Δ1 Δ2 Δ A B m n s i} :
    Merge Δ1 Δ2 Δ ->
    Γ ⊢ .sig A B .ex s : .srt s i ->
    Typed Γ Δ1 m A ->
    Typed Γ Δ2 n B.[m/] ->
    Typed Γ Δ (.tup m n .ex s) (.sig A B .ex s)

  | prj_im {Γ Δ1 Δ2 Δ A B C m n s sA sB sC iC} :
    Merge Δ1 Δ2 Δ ->
    .sig A B .im s :: Γ ⊢ C : .srt sC iC ->
    Typed Γ Δ1 m (.sig A B .im s) ->
    Typed (B :: A :: Γ) (B :⟨.im, sB⟩ A :⟨.ex, sA⟩ Δ2) n C.[.tup (.var 1) (.var 0) .im s .: shift 2] ->
    Typed Γ Δ (.prj C m n .im) C.[m/]

  | prj_ex {Γ Δ1 Δ2 Δ A B C m n s sA sB sC iC} :
    Merge Δ1 Δ2 Δ ->
    .sig A B .ex s :: Γ ⊢ C : .srt sC iC ->
    Typed Γ Δ1 m (.sig A B .ex s) ->
    Typed (B :: A :: Γ) (B :⟨.ex, sB⟩ A :⟨.ex, sA⟩ Δ2) n C.[.tup (.var 1) (.var 0) .ex s .: shift 2] ->
    Typed Γ Δ (.prj C m n .ex) C.[m/]

  | tt {Γ Δ} :
    Wf Γ Δ ->
    Lower Δ ord.e ->
    Typed Γ Δ .tt .bool

  | ff {Γ Δ} :
    Wf Γ Δ ->
    Lower Δ ord.e ->
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

  | weak {Γ Δ1 Δ2 m A} :
    Weaken Δ1 Δ2 ->
    Typed Γ Δ1 m A ->
    Typed Γ Δ2 m A

  | conv {Γ Δ A B m s i} :
    A === B ->
    Typed Γ Δ m A ->
    Γ ⊢ B : .srt s i ->
    Typed Γ Δ m B

inductive Wf : Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop where
  | nil : Wf [] []
  | cons {Γ Δ A r s i} :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (A :⟨r, s⟩ Δ)
end

notation:50 Γ:50 " ;; " Δ:51 " ⊢ " m:51 " : " A:51 => Typed Γ Δ m A
notation:50 Γ:50 " ;; " Δ:51 " ⊢ " => Wf Γ Δ

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Typed.rec_non_mutual {motive : ∀ Γ Δ m A, @Typed Srt _ Γ Δ m A -> Prop} :=
  Typed.rec (motive_1 := motive) (motive_2 := fun _ _ _ => True)

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Wf.rec_non_mutual {motive : ∀ Γ Δ, @Wf Srt _ Γ Δ -> Prop} :=
  Wf.rec (motive_1 := fun _ _ _ _ _ => True) (motive_2 := motive)

lemma Wf.size {Γ} {Δ : Ctx Srt} :
    Wf Γ Δ -> Γ.length = Δ.length := by
  intro wf
  induction wf
  all_goals aesop

lemma Wf.merge {Γ} {Δ Δ1 Δ2 : Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Γ ;; Δ1 ⊢ -> Γ ;; Δ2 ⊢ -> Γ ;; Δ ⊢ := by
  intro mrg wf1 wf2
  induction mrg generalizing Γ
  case nil       => cases wf1; aesop
  case contra ih => cases wf1; cases wf2; aesop (add safe Wf)
  case left ih   => cases wf1; cases wf2; aesop (add safe Wf)
  case right ih  => cases wf1; cases wf2; aesop (add safe Wf)
  case im ih     => cases wf1; cases wf2; aesop (add safe Wf)

lemma Wf.weaken {Γ} {Δ1 Δ2 : Ctx Srt} :
    Weaken Δ1 Δ2 -> Γ ;; Δ1 ⊢ -> Γ ;; Δ2 ⊢ := by
  intro wk agr; induction wk generalizing Γ
  case nil => assumption
  case cons =>
    cases agr
    constructor
    assumption
    aesop
  case weak =>
    cases agr
    constructor
    assumption
    aesop

lemma Wf.split {Γ} {Δ Δ1 Δ2 : Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Γ ;; Δ ⊢ -> Γ ;; Δ1 ⊢ ∧ Γ ;; Δ2 ⊢ := by
  intro mrg wf
  induction mrg generalizing Γ
  case nil       => cases wf; aesop (add safe Wf)
  case contra ih => cases wf; aesop (add safe Wf)
  case left ih   => cases wf; aesop (add safe Wf)
  case right ih  => cases wf; aesop (add safe Wf)
  case im ih     => cases wf; aesop (add safe Wf)

lemma Typed.toWf {Γ} {Δ : Ctx Srt} {A m} :
    Γ ;; Δ ⊢ m : A -> Γ ;; Δ ⊢ := by
  intro ty
  induction ty <;> try (solve | aesop)
  case lam_im ih =>
    cases ih
    aesop
  case lam_ex ih =>
    cases ih; assumption
  case app_ex mrg _ _ ih1 ih2 =>
    apply Wf.merge mrg ih1 ih2
  case tup_ex mrg _ _ _ ih1 ih2 =>
    apply Wf.merge mrg ih1 ih2
  case prj_im rs mrg _ _ _ ih1 ih2 =>
    rcases ih2 with _ | ⟨_, ih2⟩
    rcases ih2 with _ | ⟨_, ih2⟩
    apply Wf.merge mrg ih1 ih2
  case prj_ex rs1 rs2 mrg _ _ _ ih1 ih2 =>
    rcases ih2 with _ | ⟨_, ih2⟩
    rcases ih2 with _ | ⟨_, ih2⟩
    apply Wf.merge mrg ih1 ih2
  case ite mrg _ _ _ _ ih1 ih2 _ =>
    apply Wf.merge mrg ih1 ih2
  case weak wk _ wf =>
    apply Wf.weaken wk wf

lemma Wf.toStatic {Γ} {Δ : Ctx Srt} : Γ ;; Δ ⊢ -> Γ ⊢ := by
  intro wf; induction wf
  all_goals aesop (add safe Static.Wf)

lemma Wf.hasStatic {Γ} {Δ : Ctx Srt} {A x s} :
    Γ ;; Δ ⊢ -> Dynamic.Has Δ x s A -> Static.Has Γ x A := by
  intro wf hs; induction wf generalizing x s A <;> try trivial
  cases hs <;> aesop (add safe Static.Has)

lemma Typed.toStatic {Γ} {Δ : Ctx Srt} {m A} :
    Γ ;; Δ ⊢ m : A -> Γ ⊢ m : A := by
  intro ty; induction ty
  case var wf hs _ =>
    constructor
    . apply wf.toStatic
    . apply wf.hasStatic hs
  case lam_im => constructor <;> aesop
  case lam_ex => constructor <;> aesop
  case app_im => constructor <;> aesop
  case app_ex => constructor <;> aesop
  case tup_im => constructor <;> aesop
  case tup_ex => constructor <;> aesop
  case prj_im => constructor <;> aesop
  case prj_ex => constructor <;> aesop
  case tt wf _ _ => constructor; apply wf.toStatic
  case ff wf _ _ => constructor; apply wf.toStatic
  case ite => constructor <;> aesop
  case rw => constructor <;> aesop
  case conv => constructor <;> assumption
  all_goals trivial

lemma Typed.ctx_inv {Γ} {Δ : Ctx Srt} {A B m r s} :
    A :: Γ ;; A :⟨r, s⟩ Δ ⊢ m : B -> ∃ i, Γ ;; Δ ⊢ ∧ Γ ⊢ A : .srt s i := by
  intro ty
  have wf := ty.toWf
  rcases wf with _ | ⟨ty, wf⟩
  constructor <;> aesop
