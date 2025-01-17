import SStructTT.Static.Renaming

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

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
    Γ' ⊢ B.[ren .succ].[σ] : .srt s i ->
    AgreeSubst σ (A :: Γ) Γ' ->
    AgreeSubst σ (B :: Γ) Γ'

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Γ : Ctx Srt} : Γ ⊢ -> AgreeSubst ids Γ Γ := by
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
    AgreeSubst σ Γ Γ' -> Γ' ⊢ -> Has Γ x A -> Γ' ⊢ σ x : A.[σ]  := by
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
      . rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
        constructor
    | @succ _ A _ _ hs =>
      asimp
      rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
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

lemma AgreeSubst.wf_nil {Γ : Ctx Srt} {σ} : AgreeSubst σ [] Γ -> Γ ⊢ := by
  intro agr
  cases agr with
  | nil => constructor

lemma AgreeSubst.wf_cons {Γ Γ' : Ctx Srt} {A σ} :
    AgreeSubst σ (A :: Γ) Γ' -> Γ ⊢ ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> Γ' ⊢) ->
    (∀ Γ' σ, AgreeSubst σ Γ Γ' -> ∃ s i, Γ' ⊢ A.[σ] : .srt s i) ->
    Γ' ⊢ := by
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

lemma Typed.substitution {Γ Γ' : Ctx Srt} {A m σ} :
    Γ ⊢ m : A -> AgreeSubst σ Γ Γ' -> Γ' ⊢ m.[σ] : A.[σ] := by
  intro ty
  induction ty
  using @Typed.rec _ inst (motive_2 := fun Γ _ => ∀ Γ' σ, AgreeSubst σ Γ Γ' -> Γ' ⊢)
  generalizing Γ' σ with
  | srt _ _ _ ih =>
    intro agr; asimp
    constructor
    apply ih; assumption
  | var _ _ ih =>
    intro agr; asimp
    apply AgreeSubst.has
    . assumption
    . apply ih; assumption
    . assumption
  | pi0 _ _ _ ihA ihB =>
    intro agr; asimp
    asimp
    constructor
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  | pi1 _ _ _ ihA ihB =>
    intro agr; asimp
    asimp
    constructor
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  | lam0 _ _ _ ihA ihm =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihm; constructor <;> assumption
  | lam1 _ _ _ ihA ihm =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihm; constructor <;> assumption
  | app0 _ _ ihm ihn =>
    intro agr; asimp
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr
    have ty := Typed.app0 ihm ihn
    asimp at ty
    assumption
  | app1 _ _ ihm ihn =>
    intro agr; asimp
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr
    have ty := Typed.app1 ihm ihn
    asimp at ty
    assumption
  | sig0 _ _ _ _ ihA ihB =>
    intro agr; asimp
    constructor
    . assumption
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  | sig1 _ leA leB _ _ ihA ihB =>
    intro agr; asimp
    constructor
    . apply leA
    . apply leB
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  | tup0 _ _ _ ihS ihm ihn =>
    intro agr; asimp
    constructor
    . replace ihS := ihS agr; asimp at ihS
      assumption
    . apply ihm; assumption
    . replace ihn := ihn agr; asimp at ihn
      asimp; assumption
  | tup1 _ _ _ ihS ihm ihn =>
    intro agr; asimp
    constructor
    . replace ihS := ihS agr; asimp at ihS
      assumption
    . apply ihm; assumption
    . replace ihn := ihn agr; asimp at ihn
      asimp; assumption
  | @proj0 _ _ _ C m _ _ _ _ tyC _ tyn ihC ihm ihn =>
    intro agr; asimp
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyn.ctx_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    replace ihC := ihC (agr.cons tyS); asimp at ihC
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn ((agr.cons tyA).cons tyB); asimp at ihn
    apply Typed.proj0
    . assumption
    . assumption
    . asimp; assumption
  | @proj1 _ _ _ C m _ _ _ _ tyC _ tyn ihC ihm ihn =>
    intro agr; asimp
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyn.ctx_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    replace ihC := ihC (agr.cons tyS); asimp at ihC
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn ((agr.cons tyA).cons tyB); asimp at ihn
    apply Typed.proj1
    . assumption
    . assumption
    . asimp; assumption
  | bool _ ih =>
    intro agr; asimp
    constructor
    apply ih; assumption
  | tt _ ih =>
    intro agr; asimp
    constructor
    apply ih; assumption
  | ff _ ih =>
    intro agr; asimp
    constructor
    apply ih; assumption
  | @ite _ A m _ _ _ _ tyA _ _ _ ihA ihm ihn1 ihn2 =>
    intro agr; asimp
    rw[show A.[m.[σ] .: σ] = A.[up σ].[m.[σ]/] by asimp]
    have ⟨_, _, _, tyb⟩ := tyA.ctx_inv
    replace ihn1 := ihn1 agr; asimp at ihn1
    replace ihn2 := ihn2 agr; asimp at ihn2
    constructor
    . apply ihA; constructor <;> assumption
    . apply ihm; assumption
    . asimp; assumption
    . asimp; assumption
  | idn _ _ _ ihA ihm ihn =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihm; assumption
    . apply ihn; assumption
  | rfl _ ih =>
    intro; asimp
    constructor
    apply ih; assumption
  | @rw _ A _ _ n _ b _ _ tyA _ _ ihA ihm ihn =>
    intro agr; asimp
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
  | conv eq _ _ ihm ihB =>
    intro agr;
    apply Typed.conv
    . apply Conv.subst _ eq
    . apply ihm; assumption
    . apply ihB; assumption
  | nil =>
    apply AgreeSubst.wf_nil
    assumption
  | @cons _ _ s i tyA wf ih1 ih2 _ _ agr =>
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
  intros
  subst_vars
  apply Typed.subst <;> assumption

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
  asimp at tym
  exact tym
