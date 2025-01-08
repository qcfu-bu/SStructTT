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
      . have : A.[σ !> shift 1] = A.[σ].[shift 1] := by asimp
        rw[this]; constructor
    | @succ _ A _ _ hs =>
      asimp
      have : A.[σ !> shift 1] = A.[σ].[shift 1] := by asimp
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

lemma Typed.substitution {Γ Γ' : Ctx Srt} {A m σ} :
    Typed Γ m A -> AgreeSubst σ Γ Γ' -> Typed Γ' m.[σ] A.[σ] := by
  intro ty
  induction ty
  using @Typed.rec _ inst (motive_2 := fun Γ _ => ∀ Γ' σ, AgreeSubst σ Γ Γ' -> Wf Γ')
  generalizing Γ' σ with
  | srt i wf ih =>
    intro agr; asimp
    constructor
    apply ih; assumption
  | var _ _ ih =>
    intro agr; asimp
    apply AgreeSubst.has
    . assumption
    . apply ih; assumption
    . assumption
  | pi _ _ _ _ ihA ihB =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  | lam _ _ _ _ ihA ihm =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihm; constructor <;> assumption
  | app _ _ ihm ihn =>
    intro agr; asimp
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr
    have ty := Typed.app ihm ihn
    asimp at ty
    assumption
  | sig _ _ _ _ ihA ihB =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihB; constructor <;> assumption
  | pair _ _ _ ihS ihm ihn =>
    intro agr; asimp
    constructor
    . replace ihS := ihS agr; asimp at ihS
      assumption
    . apply ihm; assumption
    . replace ihn := ihn agr; asimp at ihn
      asimp; assumption
  | @proj _ _ _ C m _ _ _ _ _ tyC _ tyn ihC ihm ihn =>
    intro agr; asimp
    have : C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] := by asimp
    rw[this]
    cases tyC.toWf; case cons _ tyS =>
    cases tyn.toWf; case cons wf tyB =>
    cases wf; case cons _ tyA =>
    replace ihC := ihC (agr.cons tyS); asimp at ihC
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn ((agr.cons tyA).cons tyB); asimp at ihn
    constructor
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
    have : A.[m.[σ] .: σ] = A.[up σ].[m.[σ]/] := by asimp
    rw[this]
    cases tyA.toWf; case cons _ tyb =>
    replace ihn1 := ihn1 agr; asimp at ihn1
    replace ihn2 := ihn2 agr; asimp at ihn2
    constructor
    . apply ihA; constructor <;> assumption
    . apply ihm; assumption
    . asimp; assumption
    . asimp; assumption
  | id _ _ _ ihA ihm ihn =>
    intro agr; asimp
    constructor
    . apply ihA; assumption
    . apply ihm; assumption
    . apply ihn; assumption
  | rfl _ ih =>
    intro; asimp
    constructor
    apply ih; assumption
  | @rw _ _ B _ n _ b _ _ tyB _ _ ihB ihm ihn =>
    intro agr; asimp
    have : B.[n.[σ] .: b.[σ] .: σ] = B.[upn 2 σ].[n.[σ],b.[σ]/] := by asimp
    rw[this]
    cases tyB.toWf; case cons _ tyI =>
    cases tyI.toWf; case cons _ tyA =>
    replace ihB := ihB ((agr.cons tyA).cons tyI); asimp at ihB
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr; asimp at ihn
    simp[<-SubstLemmas.subst_comp] at ihB
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
    Typed (A :: Γ) m B ->
    Typed Γ n A ->
    Typed Γ m.[n/] B.[n/] := by
  intro tym tyn
  apply Typed.substitution
  . assumption
  . apply AgreeSubst.wk
    asimp; assumption
    exact AgreeSubst.refl tyn.toWf

lemma Typed.esubst {Γ : Ctx Srt} {A B B' m m' n} :
    m' = m.[n/] ->
    B' = B.[n/] ->
    Typed (A :: Γ) m B ->
    Typed Γ n A ->
    Typed Γ m' B' := by
  intros
  subst_vars
  apply Typed.subst <;> assumption

lemma Typed.conv_ctx {Γ : Ctx Srt} {A B C m s i} :
    B === A ->
    Typed Γ B (.srt s i) ->
    Typed (A :: Γ) m C ->
    Typed (B :: Γ) m C := by
  intro eq tyb tym
  replace tym : Typed (B :: Γ) m.[ids] C.[ids] := by
    have wf := tym.toWf
    cases wf; case cons wf tya =>
    apply Typed.substitution
    . assumption
    . apply AgreeSubst.conv <;> try assumption
      . asimp
        apply Typed.eweaken <;> try first | rfl | assumption
        asimp
      . apply AgreeSubst.refl; constructor <;>
        assumption
  asimp at tym
  exact tym
