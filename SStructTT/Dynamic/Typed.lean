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

  | lam_im {Γ Δ A B m s sA iA} :
    Δ !≤ s ->
    Γ ⊢ A : .srt sA iA ->
    Typed (A :: Γ) (_: Δ) m B ->
    Typed Γ Δ (.lam A m .im s) (.pi A B .im s)

  | lam_ex {Γ Δ Δ1 A B m s sA iA} :
    Δ !≤ s ->
    Γ ⊢ A : .srt sA iA ->
    Ext A sA Δ Δ1 ->
    Typed (A :: Γ) Δ1 m B ->
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

  | proj_im {Γ Δ1 Δ2 Δ3 Δ A B C m n s sA sC iC} :
    Merge Δ1 Δ2 Δ ->
    .sig A B .im s :: Γ ⊢ C : .srt sC iC ->
    Typed Γ Δ1 m (.sig A B .im s) ->
    Ext A sA Δ2 Δ3 ->
    Typed (B :: A :: Γ) (_: Δ3) n C.[.tup (.var 1) (.var 0) .im s .: shift 2] ->
    Typed Γ Δ (.proj C m n .im) C.[m/]

  | proj_ex {Γ Δ1 Δ2 Δ3 Δ4 Δ A B C m n s sA sB sC iC} :
    Merge Δ1 Δ2 Δ ->
    .sig A B .ex s :: Γ ⊢ C : .srt sC iC ->
    Typed Γ Δ1 m (.sig A B .ex s) ->
    Ext A sA Δ2 Δ3 ->
    Ext B sB Δ3 Δ4 ->
    Typed (B :: A :: Γ) Δ4 n C.[.tup (.var 1) (.var 0) .ex s .: shift 2] ->
    Typed Γ Δ (.proj C m n .ex) C.[m/]

  | tt {Γ Δ} :
    Wf Γ Δ ->
    Δ.Forall (fun e => e = none) ->
    Typed Γ Δ .tt .bool

  | ff {Γ Δ} :
    Wf Γ Δ ->
    Δ.Forall (fun e => e = none) ->
    Typed Γ Δ .ff .bool

  | ite {Γ Δ1 Δ2 Δ A m n1 n2 s i} :
    Merge Δ1 Δ2 Δ ->
    (.bool :: Γ) ⊢ A : .srt s i ->
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

inductive Wf : Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop where
  | nil : Wf [] []
  | ex {Γ Δ A s i} :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (A :⟨s⟩ Δ)
  | im {Γ Δ A s i} :
    Γ ⊢ A : .srt s i ->
    Wf Γ Δ ->
    Wf (A :: Γ) (_: Δ)
end

notation:50 Γ:50 "; " Δ:51 " ⊢ " m:51 " : " A:51 => Typed Γ Δ m A
notation:50 Γ:50 "; " Δ:51 " ⊢ " => Wf Γ Δ

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Typed.rec_non_mutual {motive : ∀ Γ Δ m a, @Typed Srt _ Γ Δ m a -> Prop} :=
  Typed.rec (motive_1 := motive) (motive_2 := fun _ _ _ => True)

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Wf.rec_non_mutual {motive : ∀ Γ Δ, @Wf Srt _ Γ Δ -> Prop} :=
  Wf.rec (motive_1 := fun _ _ _ _ _ => True) (motive_2 := motive)

lemma Wf.size {Γ : Static.Ctx Srt} {Δ : Dynamic.Ctx Srt} :
    Γ ; Δ ⊢ -> Γ.length = Δ.length := by
  intro wf
  induction wf
  all_goals aesop

lemma Wf.merge {Γ : Static.Ctx Srt} {Δ Δ1 Δ2 : Dynamic.Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Γ ; Δ1 ⊢ -> Γ ; Δ2 ⊢ -> Γ ; Δ ⊢ := by
  intro mrg wf1
  induction mrg generalizing Γ
  case nil =>
    cases wf1
    aesop
  case contra ih =>
    intro wf2
    cases wf1
    cases wf2
    aesop (add safe Wf)
  case left ih =>
    intro wf2
    cases wf1
    cases wf2
    aesop (add safe Wf)
  case right ih =>
    intro wf2
    cases wf1
    cases wf2
    aesop (add safe Wf)
  case im ih =>
    intro wf2
    cases wf1
    cases wf2
    aesop (add safe Wf)

lemma Wf.split {Γ : Static.Ctx Srt} {Δ Δ1 Δ2 : Dynamic.Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Γ ; Δ ⊢ -> Γ ; Δ1 ⊢ ∧ Γ ; Δ2 ⊢ := by
  intro mrg wf
  induction mrg generalizing Γ
  case nil =>
    cases wf
    aesop (add safe Wf)
  case contra ih =>
    cases wf
    aesop (add safe Wf)
  case left ih =>
    cases wf
    aesop (add safe Wf)
  case right ih =>
    cases wf
    aesop (add safe Wf)
  case im ih =>
    cases wf
    aesop (add safe Wf)

lemma Typed.toWf {Γ : Static.Ctx Srt} {Δ : Dynamic.Ctx Srt} {A m} :
    Γ ; Δ ⊢ m : A -> Γ ; Δ ⊢ := by
  intro ty
  induction ty <;> try (solve | aesop)
  case lam_im ih =>
    cases ih
    aesop
  case lam_ex ih =>
    cases ih
    case ex ext _ =>
      cases ext
      assumption
    case im ext _ =>
      cases ext
      assumption
  case app_ex mrg _ _ ih1 ih2 =>
    apply Wf.merge mrg ih1 ih2
  case tup_ex mrg _ _ _ ih1 ih2 =>
    apply Wf.merge mrg ih1 ih2
  case proj_im mrg _ _ ext _ ih1 ih2 =>
    cases ext with
    | ex =>
      rcases ih2 with _ | _ | ⟨_, ih2⟩
      rcases ih2 with _ | ⟨_, ih2⟩
      apply Wf.merge mrg ih1 ih2
    | wk =>
      rcases ih2 with _ | _ | ⟨_, ih2⟩
      rcases ih2 with _ | _ | ⟨_, ih2⟩
      apply Wf.merge mrg ih1 ih2
  case proj_ex mrg _ _ ext1 ext2 _ ih1 ih2 =>
    cases ext1 with
    | ex =>
      cases ext2 with
      | ex =>
        rcases ih2 with _ | ⟨_, ih2⟩
        rcases ih2 with _ | ⟨_, ih2⟩
        apply Wf.merge mrg ih1 ih2
      | wk =>
        rcases ih2 with _ | _ | ⟨_, ih2⟩
        rcases ih2 with _ | ⟨_, ih2⟩
        apply Wf.merge mrg ih1 ih2
    | wk =>
      cases ext2 with
      | ex =>
        rcases ih2 with _ | ⟨_, ih2⟩
        rcases ih2 with _ | _ | ⟨_, ih2⟩
        apply Wf.merge mrg ih1 ih2
      | wk =>
        rcases ih2 with _ | _ | ⟨_, ih2⟩
        rcases ih2 with _ | _ | ⟨_, ih2⟩
        apply Wf.merge mrg ih1 ih2
  case ite mrg _ _ _ _ ih1 ih2 _ =>
    apply Wf.merge mrg ih1 ih2
