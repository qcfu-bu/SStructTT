import SStructTT.Static.Typed

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

@[aesop safe (rule_sets := [rename]) [constructors]]
inductive AgreeRen : (Var -> Var) -> Ctx Srt -> Ctx Srt -> Prop where
  | nil {ξ} :
    AgreeRen ξ  [] []
  | cons {Γ Γ' A s i ξ} :
    Γ ⊢ A : .srt s i ->
    AgreeRen ξ Γ Γ' ->
    AgreeRen (upren ξ) (A :: Γ) (A.[ren ξ] :: Γ')
  | wk {Γ Γ' A s i ξ} :
    Γ' ⊢ A : .srt s i ->
    AgreeRen ξ Γ Γ' ->
    AgreeRen (ξ !>> (.+1)) Γ (A :: Γ')

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.refl {Γ : Ctx Srt} : Γ ⊢ -> AgreeRen id Γ Γ := by
  intro wf
  induction wf
  all_goals try trivial
  case nil => constructor
  case cons Γ A s i ty wf _ ih =>
    have h := AgreeRen.cons ty ih
    asimp at h
    assumption

lemma AgreeRen.has {Γ Γ' : Ctx Srt} {A x ξ} :
    AgreeRen ξ Γ Γ' -> Has Γ x A -> Has Γ' (ξ x) A.[ren ξ] := by
  intro agr
  induction agr generalizing x A with
  | nil => intro h; cases h
  | @cons _ _ A _ _ ξ _ _ ih =>
    intro h; cases h <;> asimp
    case zero =>
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor
    case succ A x hs =>
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor; apply ih; assumption
  | @wk _ _ A _ _ ξ _ _ ih =>
    intro h; asimp
    rw[show A.[ren (ξ !>> (.+1))] = A.[ren ξ].[shift 1] by asimp; rfl]
    constructor; apply ih; assumption

lemma AgreeRen.wf_nil {Γ' : Ctx Srt} {ξ} : AgreeRen ξ [] Γ' -> Γ' ⊢ := by
  intro agr
  cases agr with
  | nil => constructor
  | wk ty agr =>
    constructor
    . assumption
    . apply ty.toWf

lemma AgreeRen.wf_cons {Γ Γ' : Ctx Srt} {A ξ} :
    AgreeRen ξ (A :: Γ) Γ' -> Γ ⊢ ->
    (∀ Γ' ξ, AgreeRen ξ Γ Γ' → Γ' ⊢) ->
    (∀ Γ' ξ, AgreeRen ξ Γ Γ' → ∃ s i, Γ' ⊢ A.[ren ξ] : .srt s i) ->
    Γ' ⊢ := by
  intro agr
  cases agr with
  | cons ty agr =>
    intro wf h1 h2
    have ⟨s, i, ty⟩ := h2 _ _ agr
    constructor
    . assumption
    . apply h1; assumption
  | wk ty agr =>
    intros
    constructor
    . assumption
    . exact ty.toWf

lemma Typed.renaming {Γ Γ' : Ctx Srt} {A m ξ} :
    Γ ⊢ m : A -> AgreeRen ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ] := by
  intro ty
  induction ty
  using @Typed.rec _ inst (motive_2 := fun Γ _ => ∀ Γ' ξ, AgreeRen ξ Γ Γ' -> Γ' ⊢)
  generalizing Γ' ξ with
  | srt _ _ _ ih =>
    intro; asimp; constructor
    apply ih; assumption
  | var _ _ ih =>
    intro; asimp; constructor
    . apply ih; assumption
    . apply AgreeRen.has <;> assumption
  | pi tyA _ ihA ihB =>
    intro agr; asimp; constructor
    . apply ihA; assumption
    . have := ihB (agr.cons tyA)
      asimp at this; assumption
  | lam tyA _ ihA ihm =>
    intro agr; asimp; constructor
    . apply ihA; assumption
    . have := ihm (agr.cons tyA)
      asimp at this; assumption
  | app tym tyn ihm ihn =>
    intro agr; asimp
    replace tym := ihm agr; asimp at tym
    replace tyn := ihn agr; asimp at tyn
    have ty := Typed.app tym tyn; asimp at ty
    assumption
  | sig _ _ tyA tyB ihA ihB =>
    intro agr; asimp; constructor
    . assumption
    . assumption
    . apply ihA; assumption
    . have := ihB (agr.cons tyA)
      asimp at this; assumption
  | tup _ _ _ ihT ihm ihn =>
    intro agr; asimp; constructor
    . apply ihT; assumption
    . apply ihm; assumption
    . have := ihn agr
      asimp at this; asimp; assumption
  | @proj Γ A B C m n r s sC iC tyC tym tyn ihC ihm ihn =>
    intro agr; asimp
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyn.ctx_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    replace ihC := ihC (agr.cons tyS)
    replace ihm := ihm agr
    have agr' : AgreeRen (upren (upren ξ)) (B :: A :: Γ)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') := by
      aesop (rule_sets := [rename])
    replace ihn := ihn agr'
    asimp at ihC
    asimp at ihm
    rw [show C.[.tup (.var 1) (.var 0) r s .: shift 2].[ren (upren $ upren ξ)]
           = C.[up (ren ξ)].[.tup (.var 1) (.var 0) r s .: shift 2]
          by asimp] at ihn
    rw[SubstLemmas.upren_up] at ihn
    replace := Typed.proj ihC ihm ihn
    asimp at this
    assumption
  | bool _ ih =>
    intro; asimp; constructor;
    apply ih; assumption
  | tt _ ih =>
    intro; asimp; constructor;
    apply ih; assumption
  | ff _ ih =>
    intro; asimp; constructor;
    apply ih; assumption
  | @ite _ A _ _ _ _ _ tyA _ _ _ ihA ihm ihn1 ihn2 =>
    intro agr; asimp
    have ⟨_, _, _, tyb⟩ := tyA.ctx_inv
    replace ihA := ihA (agr.cons tyb); asimp at ihA
    replace ihm := ihm agr; asimp at ihm
    replace ihn1 := ihn1 agr; asimp at ihn1
    replace ihn2 := ihn2 agr; asimp at ihn2
    rw[show A.[.tt .: ren ξ] = A.[up (ren ξ)].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: ren ξ] = A.[up (ren ξ)].[.ff/] by asimp] at ihn2
    have := Typed.ite ihA ihm ihn1 ihn2
    asimp at this; assumption
  | idn tyA tym tyn ihA ihm ihn =>
    intro; asimp; constructor
    . apply ihA; assumption
    . apply ihm; assumption
    . apply ihn; assumption
  | rfl _ ih =>
    intro; asimp; constructor
    apply ih; assumption
  | @rw _ A B _ _ a b _ _ tyA tym tyn ihA ihm ihn =>
    intro agr; asimp
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace ihA := ihA ((agr.cons tyB).cons tyI); asimp at ihA
    replace ihm := ihm agr; asimp at ihm
    replace ihn := ihn agr; asimp at ihn
    simp[<-SubstLemmas.subst_comp] at ihA
    rw[show A.[a.[ren ξ].rfl .: a.[ren ξ] .: ren ξ]
          = A.[upn 2 (ren ξ)].[.rfl a.[ren ξ],a.[ren ξ]/]
         by asimp] at ihm
    have := Typed.rw ihA ihm ihn
    asimp at this; assumption
  | conv eq tym tyB ihm ihB =>
    intro agr
    replace ihB := ihB agr; asimp at ihB
    replace ihm := ihm agr
    apply Typed.conv
    . apply Conv.subst _ eq
    . assumption
    . assumption
  | nil Γ' ξ agr => exact agr.wf_nil
  | @cons _ _ s i _ _ ih _ _ _ agr =>
    apply agr.wf_cons
    . assumption
    . assumption
    . intros
      exists s, i
      apply ih; assumption

lemma Wf.has_typed {Γ : Ctx Srt} {A x} :
    Γ ⊢ -> Has Γ x A -> ∃ s i, Γ ⊢ A : .srt s i := by
  intro wf
  induction wf
  generalizing x A
  all_goals try trivial
  case nil => intro h; cases h
  case cons s i ty wf _ ih =>
    intro h
    cases h with
    | zero =>
      exists s, i
      apply ty.renaming
      constructor
      . assumption
      . exact AgreeRen.refl wf
    | succ _ _ _ _ hs =>
      have ⟨s, i, ty⟩ := ih hs
      exists s, i
      apply ty.renaming
      constructor
      . assumption
      . exact AgreeRen.refl wf

lemma Typed.weaken {Γ : Ctx Srt} {A B m s i} :
    Γ ⊢ m : A ->
    Γ ⊢ B : .srt s i ->
    B :: Γ ⊢ m.[shift 1] : A.[shift 1] := by
  intro tym tyb
  apply tym.renaming
  constructor
  . assumption
  . exact AgreeRen.refl tym.toWf

lemma Typed.eweaken {Γ Γ' : Ctx Srt} {A A' B m m' s i} :
    Γ' = (B :: Γ) ->
    m' = m.[ren .succ] ->
    A' = A.[ren .succ] ->
    Γ ⊢ m : A ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ m' : A' := by
  intros
  subst_vars
  apply Typed.weaken <;> assumption
