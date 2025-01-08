import SStructTT.Static.Renaming

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst : (Var -> Tm Srt) -> Ctx Srt -> Ctx Srt -> Prop where
  | nil {σ} :
    AgreeSubst σ [] []
  | cons {Γ Γ' A s i σ} :
    Typed Γ A (.srt s i) ->
    AgreeSubst σ Γ Γ' ->
    AgreeSubst (up σ) (A :: Γ) (A.[σ] :: Γ')
  | wk {Γ Γ' A m σ} :
    Typed Γ' m  A.[σ] ->
    AgreeSubst σ Γ Γ' ->
    AgreeSubst (m .: σ) (A :: Γ) Γ'
  | conv {Γ Γ' A B s i σ} :
    A === B ->
    Typed Γ B (.srt s i) ->
    Typed Γ' B.[ren .succ].[σ] (.srt s i) ->
    AgreeSubst σ (A :: Γ) Γ' ->
    AgreeSubst σ (B :: Γ) Γ'

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Γ : Ctx Srt} : Wf Γ -> AgreeSubst ids Γ Γ := by
  intro wf
  induction wf
  all_goals try trivial
  case nil =>
    constructor
  case cons ty _ _ agr =>
    replace agr := AgreeSubst.cons ty agr
    asimp at agr
    assumption

lemma AgreeSubst.has {Γ Γ' : Ctx Srt} {A x σ} :
    AgreeSubst σ Γ Γ' -> Wf Γ' -> Has Γ x A -> Typed Γ' (σ x) A.[σ]  := by
  intro agr
  induction agr generalizing x A with
  | nil => intro _ hs; cases hs
  | @cons _ _ A _ _ σ _ _ ih =>
    intro wf hs
    cases wf; case cons wf ty =>
    cases hs with
    | zero =>
      asimp
      constructor
      . constructor <;> assumption
      . have : A.[σ >> shift 1] = A.[σ].[shift 1] := by asimp
        rw[this]; constructor
    | @succ _ A _ _ hs =>
      asimp
      have : A.[σ >> shift 1] = A.[σ].[shift 1] := by asimp
      rw[this]; clear this
      apply Typed.eweaken <;> try first | rfl | assumption
      apply ih <;> assumption
  | wk _ _ ih  =>
    intro wf hs
    cases hs with
    | zero => asimp; assumption
    | succ => asimp; apply ih <;> assumption
  | @conv _ _ A B _ _ σ eq ty ty' agr ih =>
    intro wf hs
    cases hs with
    | zero =>
      apply Typed.conv
      . apply Conv.subst _ (Conv.subst _ eq)
      . apply ih; assumption; constructor
      . assumption
    | succ =>
      apply ih
      . assumption
      . constructor; assumption

lemma AgreeSubst.wf_nil {Γ : Ctx Srt} {σ} : AgreeSubst σ [] Γ -> Wf Γ := by
  intro agr
  cases agr with
  | nil => constructor

lemma AgreeSubst.wf_cons {Γ Γ' : Ctx Srt} {A σ} :
    AgreeSubst σ (A :: Γ) Γ' -> Wf Γ ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> Wf Γ') ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> ∃ s i, Typed Γ' A.[σ] (.srt s i)) ->
    Wf Γ' := by
  intro agr
  cases agr with
  | cons _ agr =>
    intro _ h1 h2
    have wf := h1 _ _ agr
    have ⟨_, _, ty⟩ := h2 _ _ agr
    constructor
    . exact ty
    . apply h1; assumption
  | wk =>
    intro _ h1 h2
    apply h1; assumption
  | conv _ _ ty' =>
    intro wf h1 h2
    apply ty'.toWf
