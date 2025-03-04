import SStructTT.SStruct.Static.Renaming

namespace Static
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst : (Var -> Tm Srt) -> Ctx Srt -> Ctx Srt -> Prop where
  | nil {σ} :
    AgreeSubst σ [] []
  | cons {Γ Γ' A s i σ} :
    Γ ⊢ A : .srt s i ->
    AgreeSubst σ Γ Γ' ->
    AgreeSubst (up σ) (A :: Γ) (A.[σ] :: Γ')
  | wk {Γ Γ' A m σ} :
    Γ' ⊢ m : A.[σ] ->
    AgreeSubst σ Γ Γ' ->
    AgreeSubst (m .: σ) (A :: Γ) Γ'
  | conv {Γ Γ' A B s i σ} :
    A === B ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ (A :: Γ) Γ' ->
    AgreeSubst σ (B :: Γ) Γ'

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Γ : Ctx Srt} : Γ ⊢ -> AgreeSubst ids Γ Γ := by
  intro wf; induction wf <;> try trivial
  case nil => constructor
  case cons ty _ _ agr =>
    replace agr := AgreeSubst.cons ty agr
    asimp at agr; assumption

lemma AgreeSubst.has {Γ Γ' : Ctx Srt} {A x σ} :
    AgreeSubst σ Γ Γ' -> Γ' ⊢ -> Has Γ x A -> Γ' ⊢ σ x : A.[σ]  := by
  intro agr wf hs; induction agr generalizing x A
  case nil => cases hs
  case cons A _ _ σ _ _ ih =>
    rcases wf with _ | ⟨wf, ty⟩
    cases hs with
    | zero =>
      asimp
      constructor
      . constructor <;> assumption
      . rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
        constructor
    | @succ _ A _ _ hs =>
      asimp
      rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
      apply Typed.eweaken <;> try first | rfl | assumption
      apply ih <;> assumption
  case wk _ _ ih  =>
    cases hs with
    | zero => asimp; assumption
    | succ => asimp; apply ih <;> assumption
  case conv A B _ _ σ eq ty ty' agr ih =>
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

lemma AgreeSubst.wf_nil {Γ : Ctx Srt} {σ} : AgreeSubst σ [] Γ -> Γ ⊢ := by
  intro agr
  cases agr with
  | nil => constructor

lemma AgreeSubst.wf_cons {Γ Γ' : Ctx Srt} {A σ} :
    AgreeSubst σ (A :: Γ) Γ' -> Γ ⊢ ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> Γ' ⊢) ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> ∃ s i, Γ' ⊢ A.[σ] : .srt s i) ->
    Γ' ⊢ := by
  intro agr; cases agr
  case cons agr _ =>
    intro _ h1 h2
    have wf := h1 _ _ agr
    have ⟨_, _, ty⟩ := h2 _ _ agr
    constructor
    . exact ty
    . apply h1; assumption
  case wk =>
    intro _ h1 h2
    apply h1; assumption
  case conv ty' _ =>
    intro wf h1 h2
    apply ty'.toWf

lemma Typed.substitution {Γ Γ' : Ctx Srt} {A m σ} :
    Γ ⊢ m : A -> AgreeSubst σ Γ Γ' -> Γ' ⊢ m.[σ] : A.[σ] := by
  intro ty agr; induction ty using
    @Typed.rec _ ord
      (motive_2 := fun Γ _ => ∀ Γ' σ, AgreeSubst σ Γ Γ' -> Γ' ⊢)
  generalizing Γ' σ <;> asimp
  case srt ih =>
    constructor; apply ih; assumption
  case var ih =>
    apply AgreeSubst.has
    . assumption
    . apply ih; assumption
    . assumption
  case pi ihA ihB =>
    constructor
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  case lam ihA ihm =>
    constructor
    . apply ihA; assumption
    . apply ihm; constructor <;> assumption
  case app ihm ihn =>
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr
    have ty := Typed.app ihm ihn
    asimp at ty
    assumption
  case sig ihA ihB =>
    constructor
    . assumption
    . assumption
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  case tup ihS ihm ihn =>
    constructor
    . replace ihS := ihS agr; asimp at ihS
      assumption
    . apply ihm; assumption
    . replace ihn := ihn agr; asimp at ihn
      asimp; assumption
  case proj C m _ _ _ _ _ tyC _ tyn ihC ihm ihn =>
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyn.ctx_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    replace ihC := ihC (agr.cons tyS); asimp at ihC
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn ((agr.cons tyA).cons tyB); asimp at ihn
    apply Typed.proj
    . assumption
    . assumption
    . asimp; assumption
  case bool ih => constructor; apply ih; assumption
  case tt ih => constructor; apply ih; assumption
  case ff ih => constructor; apply ih; assumption
  case ite A m _ _ _ _ tyA _ _ _ ihA ihm ihn1 ihn2 =>
    rw[show A.[m.[σ] .: σ] = A.[up σ].[m.[σ]/] by asimp]
    have ⟨_, _, _, tyb⟩ := tyA.ctx_inv
    replace ihn1 := ihn1 agr; asimp at ihn1
    replace ihn2 := ihn2 agr; asimp at ihn2
    constructor
    . apply ihA; constructor <;> assumption
    . apply ihm; assumption
    . asimp; assumption
    . asimp; assumption
  case idn ihA ihm ihn =>
    constructor
    . apply ihA; assumption
    . apply ihm; assumption
    . apply ihn; assumption
  case rfl ih => constructor; apply ih; assumption
  case rw A _ _ n _ b _ _ tyA _ _ ihA ihm ihn =>
    rw[show A.[n.[σ] .: b.[σ] .: σ] = A.[upn 2 σ].[n.[σ],b.[σ]/] by asimp]
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyA⟩ := tyI.ctx_inv
    replace ihA := ihA ((agr.cons tyA).cons tyI); asimp at ihA
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr; asimp at ihn
    simp[<-SubstLemmas.subst_comp] at ihA
    constructor
    . asimp; assumption
    . asimp; assumption
    . assumption
  case conv eq _ _ ihm ihB =>
    apply Typed.conv
    . apply Conv.subst _ eq
    . apply ihm; assumption
    . apply ihB; assumption
  case nil =>
    apply AgreeSubst.wf_nil
    assumption
  case cons s i tyA wf ih1 ih2 _ _ agr =>
    apply AgreeSubst.wf_cons
    . apply agr
    . apply tyA.toWf
    . assumption
    . intros; exists s, i
      apply ih1; assumption

lemma Typed.subst {Γ : Ctx Srt} {A B m n} :
    A :: Γ ⊢ m : B ->
    Γ ⊢ n : A ->
    Γ ⊢ m.[n/] : B.[n/] := by
  intro tym tyn
  apply Typed.substitution
  . assumption
  . apply AgreeSubst.wk
    asimp; assumption
    exact AgreeSubst.refl tyn.toWf

lemma Typed.esubst {Γ : Ctx Srt} {A B B' m m' n} :
    m' = m.[n/] ->
    B' = B.[n/] ->
    A :: Γ ⊢ m : B ->
    Γ ⊢ n : A ->
    Γ ⊢ m' : B' := by
  intros; subst_vars; apply Typed.subst <;> assumption

lemma Typed.conv_ctx {Γ : Ctx Srt} {A B C m s i} :
    B === A ->
    Γ ⊢ B : .srt s i ->
    A :: Γ ⊢ m : C ->
    B :: Γ ⊢ m : C := by
  intro eq tyB tym
  replace tym : B :: Γ ⊢ m.[ids] : C.[ids] := by
    have ⟨_, _, _, tyA⟩ := tym.ctx_inv
    apply Typed.substitution
    . assumption
    . apply AgreeSubst.conv <;> try assumption
      . asimp; apply tyA.weaken tyB
      . apply AgreeSubst.refl; constructor <;> assumption
  asimp at tym; assumption
