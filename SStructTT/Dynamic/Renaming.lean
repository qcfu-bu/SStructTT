import SStructTT.Static.Renaming
import SStructTT.Dynamic.Typed

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

@[aesop safe (rule_sets := [rename]) [constructors]]
inductive AgreeRen : (Var -> Var) ->
  Static.Ctx Srt -> Dynamic.Ctx Srt ->
  Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop
where
  | nil {ξ} :
    AgreeRen ξ [] [] [] []
  | ex {Γ Γ' Δ Δ' A s i ξ} :
    Γ ⊢ A : .srt s i ->
    AgreeRen ξ Γ Δ Γ' Δ' ->
    AgreeRen (upren ξ)
      (A :: Γ) (A :⟨s⟩ Δ) (A.[ren ξ] :: Γ') (A.[ren ξ] :⟨s⟩ Δ')
  | im {Γ Γ' Δ Δ' A s i ξ} :
    Γ ⊢ A : .srt s i ->
    AgreeRen ξ Γ Δ Γ' Δ' ->
    AgreeRen (upren ξ)
      (A :: Γ) (_: Δ) (A.[ren ξ] :: Γ') (_: Δ')
  | wk {Γ Γ' Δ Δ' A s i ξ} :
    Γ' ⊢ A : .srt s i ->
    AgreeRen ξ Γ Δ Γ' Δ' ->
    AgreeRen (ξ !>> (.+1)) Γ Δ (A :: Γ') (_: Δ')

lemma AgreeRen.toStatic {Γ Γ' : Static.Ctx Srt} {Δ Δ' : Dynamic.Ctx Srt} {ξ} :
    Dynamic.AgreeRen ξ Γ Δ Γ' Δ' -> Static.AgreeRen ξ Γ Γ' := by
  intro agr
  induction agr <;> aesop (rule_sets := [rename])

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.refl {Γ : Static.Ctx Srt} {Δ : Dynamic.Ctx Srt} :
    Γ ; Δ ⊢ -> AgreeRen id Γ Δ Γ Δ := by
  intro wf; induction wf <;> try aesop (rule_sets := [rename])
  case ex ty _ agr =>
    have agr := agr.ex ty
    asimp at agr
    assumption
  case im ty _ agr =>
    have agr := agr.im ty
    asimp at agr
    assumption

lemma AgreeRen.none {Γ Γ' : Static.Ctx Srt} {Δ Δ' : Dynamic.Ctx Srt} {ξ} :
    AgreeRen ξ Γ Δ Γ' Δ' -> Δ.Forall (. = none) -> Δ'.Forall (. = none) := by
  intro agr; induction agr <;> aesop

lemma AgreeRen.lower {Γ Γ' : Static.Ctx Srt} {Δ Δ' : Dynamic.Ctx Srt} {ξ s} :
    AgreeRen ξ Γ Δ Γ' Δ' -> Δ !≤ s -> Δ' !≤ s := by
  intro agr lw; induction agr <;> try (solve| aesop)
  case ex =>
    cases lw
    constructor <;> aesop
  case im =>
    cases lw
    constructor; aesop

lemma AgreeRen.has {Γ Γ' : Static.Ctx Srt} {Δ Δ' : Dynamic.Ctx Srt} {ξ x s A} :
    AgreeRen ξ Γ Δ Γ' Δ' ->
    Has Δ x s A ->
    Has Δ' (ξ x) s A.[ren ξ] := by
  intro agr
  induction agr generalizing x s A
  case nil =>
    intro h; cases h
  case ex A _ _ ξ _ agr ih =>
    intro h;
    rcases h with ⟨h⟩
    have h := agr.none h
    asimp
    rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
    constructor; assumption
  case im B _ _ ξ _ agr ih =>
    intro h;
    cases h with | @cons _ A x _ h =>
    specialize ih h
    asimp
    rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
    constructor; assumption
  case wk ξ _ _ ih =>
    intro h
    specialize ih h
    asimp
    rw[show A.[ren (ξ !>> (.+1))] = A.[ren ξ].[shift 1] by asimp; rfl]
    constructor; assumption

lemma AgreeRen.split {Γ Γ'} {Δ Δ' Δ1 Δ2 : Ctx Srt} ξ :
    AgreeRen ξ Γ Δ Γ' Δ' -> Merge Δ1 Δ2 Δ ->
    ∃ Δ1' Δ2',
      Merge Δ1' Δ2' Δ' ∧
      AgreeRen ξ Γ Δ1 Γ' Δ1' ∧
      AgreeRen ξ Γ Δ2 Γ' Δ2' := by
  intro agr; induction agr generalizing Δ1 Δ2
  case nil =>
    intro mrg; cases mrg
    exists [], []
    aesop (rule_sets := [rename])
  case ex Γ Γ' Δ Δ' A s i ξ ty agr ih =>
    intro mrg; cases mrg with
    | contra Δ1 Δ2 h mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists A.[ren ξ] :⟨s⟩ Δ1', A.[ren ξ] :⟨s⟩ Δ2'
      and_intros
      . constructor <;> assumption
      . constructor <;> assumption
      . constructor <;> assumption
    | @left Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists A.[ren ξ] :⟨s⟩ Δ1', _: Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> assumption
      . constructor <;> assumption
    | @right Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists _: Δ1', A.[ren ξ] :⟨s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> assumption
      . constructor <;> assumption
  case im Γ Γ' Δ Δ' A s i ξ ty agr ih =>
    intro mrg; cases mrg with
    | @im Δ1 Δ2 _ mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists _: Δ1', _: Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> assumption
      . constructor <;> assumption
  case wk Γ Γ' Δ Δ' A s i ξ ty agr ih =>
    intro mrg
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
    exists _: Δ1', _: Δ2'
    and_intros
    . constructor; assumption
    . constructor <;> assumption
    . constructor <;> assumption

lemma Typed.renaming {Γ Γ' : Static.Ctx Srt} {Δ Δ' : Dynamic.Ctx Srt} {A m ξ} :
    Γ ; Δ ⊢ m : A -> AgreeRen ξ Γ Δ Γ' Δ' -> Γ' ; Δ' ⊢ m.[ren ξ] : A.[ren ξ] := by
  intro ty agr; induction ty
  using
    @Typed.rec _ inst
      (motive_2 := fun Γ Δ _ => ∀ Γ' Δ' ξ, AgreeRen ξ Γ Δ Γ' Δ' -> Γ' ; Δ' ⊢)
  generalizing Γ' Δ' ξ
  case var h _ =>
    asimp; constructor <;> try aesop
    apply agr.has h
  case lam_im Γ Δ A B m s sA i lw tyA tym ih =>
    asimp; constructor
    . apply agr.lower lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.im tyA)
      asimp at ih; assumption
  case lam_ex Γ Δ Δ1 A B m s sA i lw tyA ext tym ih =>
    asimp; cases ext with
    | ex =>
      constructor
      . apply agr.lower lw
      . apply tyA.renaming agr.toStatic
      . apply Ext.ex
      . specialize ih (agr.ex tyA)
        asimp at ih; assumption
    | wk h =>
      constructor
      . apply agr.lower lw
      . apply tyA.renaming agr.toStatic
      . apply Ext.wk h
      . specialize ih (agr.im tyA)
        asimp at ih; assumption
  case app_im Γ Δ A B m n s tym tyn ih =>
