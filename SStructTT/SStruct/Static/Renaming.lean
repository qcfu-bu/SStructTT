import SStructTT.SStruct.Static.Typed

namespace Static
variable {Srt : Type} [ord : SrtOrder Srt]

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
  intro wf; induction wf <;> try trivial
  case nil => constructor
  case cons Γ A s i ty wf _ ih =>
    have h := AgreeRen.cons ty ih
    asimp at h
    assumption

lemma AgreeRen.has {Γ Γ' : Ctx Srt} {A x ξ} :
    AgreeRen ξ Γ Γ' -> Has Γ x A -> Has Γ' (ξ x) A.[ren ξ] := by
  intro agr hs; induction agr generalizing x A
  case nil => cases hs
  case cons A _ _ ξ _ _ ih =>
    cases hs <;> asimp
    case zero =>
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor
    case succ A x hs =>
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor; apply ih; assumption
  case wk A _ _ ξ _ _ ih =>
    asimp; rw[show A.[ren (ξ !>> (.+1))] = A.[ren ξ].[shift 1] by asimp; rfl]
    constructor; apply ih; assumption

lemma AgreeRen.wf_nil {Γ' : Ctx Srt} {ξ} : AgreeRen ξ [] Γ' -> Γ' ⊢ := by
  intro
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
  intro
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
  intro ty agr; induction ty using
    @Typed.rec _ ord
      (motive_2 := fun Γ _ => ∀ Γ' ξ, AgreeRen ξ Γ Γ' -> Γ' ⊢)
  generalizing Γ' ξ <;> asimp
  case srt ih =>
    constructor
    apply ih; assumption
  case var ih =>
    constructor
    . apply ih; assumption
    . apply AgreeRen.has <;> assumption
  case pi tyA _ ihA ihB =>
    constructor
    . apply ihA; assumption
    . have := ihB (agr.cons tyA)
      asimp at this; assumption
  case lam tyA _ ihA ihm =>
    constructor
    . apply ihA; assumption
    . have := ihm (agr.cons tyA)
      asimp at this; assumption
  case app tym tyn ihm ihn =>
    replace tym := ihm agr; asimp at tym
    replace tyn := ihn agr; asimp at tyn
    have ty := Typed.app tym tyn; asimp at ty
    assumption
  case sig tyA tyB ihA ihB =>
    constructor
    . assumption
    . assumption
    . apply ihA; assumption
    . have := ihB (agr.cons tyA)
      asimp at this; assumption
  case tup ihT ihm ihn =>
    constructor
    . apply ihT; assumption
    . apply ihm; assumption
    . have := ihn agr
      asimp at this; asimp; assumption
  case proj Γ A B C m n r s sC iC tyC tym tyn ihC ihm ihn =>
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
  case bool ih =>
    constructor;
    apply ih; assumption
  case tt ih =>
    constructor;
    apply ih; assumption
  case ff ih =>
    constructor;
    apply ih; assumption
  case ite A _ _ _ _ _ tyA _ _ _ ihA ihm ihn1 ihn2 =>
    have ⟨_, _, _, tyb⟩ := tyA.ctx_inv
    replace ihA := ihA (agr.cons tyb); asimp at ihA
    replace ihm := ihm agr; asimp at ihm
    replace ihn1 := ihn1 agr; asimp at ihn1
    replace ihn2 := ihn2 agr; asimp at ihn2
    rw[show A.[.tt .: ren ξ] = A.[up (ren ξ)].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: ren ξ] = A.[up (ren ξ)].[.ff/] by asimp] at ihn2
    have := Typed.ite ihA ihm ihn1 ihn2
    asimp at this; assumption
  case idn tyA tym tyn ihA ihm ihn =>
    constructor
    . apply ihA; assumption
    . apply ihm; assumption
    . apply ihn; assumption
  case rfl ih =>
    constructor
    apply ih; assumption
  case rw A B _ _ a b _ _ tyA tym tyn ihA ihm ihn =>
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
  case conv eq tym tyB ihm ihB =>
    replace ihB := ihB agr
    replace ihm := ihm agr
    apply Typed.conv
    . apply Conv.subst _ eq
    . assumption
    . assumption
  case nil Γ' ξ agr => exact agr.wf_nil
  case cons s i _ _ ih _ _ _ agr =>
    apply agr.wf_cons
    . assumption
    . assumption
    . intros
      exists s, i
      apply ih; assumption

lemma Wf.has_typed {Γ : Ctx Srt} {A x} :
    Γ ⊢ -> Has Γ x A -> ∃ s i, Γ ⊢ A : .srt s i := by
  intro wf; induction wf generalizing x A <;> try trivial
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
  intro tym tyB
  apply tym.renaming
  constructor
  . assumption
  . exact AgreeRen.refl tym.toWf

lemma Typed.eweaken {Γ Γ' : Ctx Srt} {A A' B m m' s i} :
    Γ' = B :: Γ ->
    m' = m.[shift 1] ->
    A' = A.[shift 1] ->
    Γ ⊢ m : A ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ m' : A' := by
  intros; subst_vars
  apply Typed.weaken <;> assumption
