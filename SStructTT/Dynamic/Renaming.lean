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
  | cons {Γ Γ' Δ Δ' A} r {s i ξ} :
    Γ ⊢ A : .srt s i ->
    AgreeRen ξ Γ Δ Γ' Δ' ->
    AgreeRen (upren ξ)
      (A :: Γ) (A :⟨r, s⟩ Δ) (A.[ren ξ] :: Γ') (A.[ren ξ] :⟨r, s⟩ Δ')
  | wk {Γ Γ' Δ Δ' A s i ξ} :
    Γ' ⊢ A : .srt s i ->
    AgreeRen ξ Γ Δ Γ' Δ' ->
    AgreeRen (ξ !>> (.+1)) Γ Δ (A :: Γ') (A :⟨.im, s⟩ Δ')

lemma AgreeRen.toStatic {Γ Γ'} {Δ Δ' : Ctx Srt} {ξ} :
    Dynamic.AgreeRen ξ Γ Δ Γ' Δ' -> Static.AgreeRen ξ Γ Γ' := by
  intro agr
  induction agr <;> aesop (rule_sets := [rename])

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.refl {Γ} {Δ : Ctx Srt} :
    Γ ;; Δ ⊢ -> AgreeRen id Γ Δ Γ Δ := by
  intro wf; induction wf <;> try aesop (rule_sets := [rename])
  case cons r _ _ ty _ agr =>
    replace agr := agr.cons r ty
    asimp at agr; assumption

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.implicit {Γ Γ'} {Δ Δ' : Ctx Srt} {ξ} :
    AgreeRen ξ Γ Δ Γ' Δ' ->
    Δ.Forall (∃ A s, . = (A, .im, s)) ->
    Δ'.Forall (∃ A s, . = (A, .im, s)) := by
  intro agr; induction agr <;> aesop

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.lower {Γ Γ'} {Δ Δ' : Ctx Srt} {ξ s} :
    AgreeRen ξ Γ Δ Γ' Δ' -> Δ !≤ s -> Δ' !≤ s := by
  intro agr lw; induction agr <;> try (solve| aesop)
  cases lw <;> constructor <;> aesop

lemma AgreeRen.has {Γ Γ'} {Δ Δ' : Ctx Srt} {ξ x s A} :
    AgreeRen ξ Γ Δ Γ' Δ' ->
    Has Δ x s A ->
    Has Δ' (ξ x) s A.[ren ξ] := by
  intro agr hs
  induction agr generalizing x s A
  case nil => cases hs
  case cons A r _ _ ξ _ agr ih =>
    cases r with
    | ex =>
      rcases hs with ⟨h⟩
      have h := agr.implicit h; asimp
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor; assumption
    | im =>
      rcases hs with _ | @⟨_, A, B, _, _, _, hs⟩
      specialize ih hs; asimp
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor; assumption
  case wk ξ _ _ ih =>
    specialize ih hs; asimp
    rw[show A.[ren (ξ !>> (.+1))] = A.[ren ξ].[shift 1] by asimp; rfl]
    constructor; assumption

lemma AgreeRen.wf_nil {Γ'} {Δ' : Ctx Srt} {ξ} :
    AgreeRen ξ [] [] Γ' Δ' -> Γ' ;; Δ' ⊢ := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro agr; induction agr <;> try trivial
  case nil => constructor
  case wk => subst_vars; aesop (add safe Wf)

lemma AgreeRen.wf_cons {Γ Γ'} {Δ Δ' : Ctx Srt} {A r s ξ} :
    AgreeRen ξ (A :: Γ) (A :⟨r, s⟩ Δ) Γ' Δ' -> Γ ;; Δ ⊢ ->
    (∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' → Γ' ;; Δ' ⊢) ->
    Γ' ;; Δ' ⊢ := by
  generalize e1: A :: Γ = Γ0
  generalize e2: A :⟨r, s⟩ Δ = Δ0
  intro agr wf h; induction agr generalizing Γ Δ A r s <;> try trivial
  case cons ξ tyA agr ih =>
    cases e1; cases e2
    constructor
    . apply tyA.renaming agr.toStatic
    . apply h agr
  case wk _ ih =>
    cases e1; cases e2
    specialize ih rfl rfl wf h
    constructor <;> aesop

lemma AgreeRen.split {Γ Γ'} {Δ Δ' Δ1 Δ2 : Ctx Srt} {ξ} :
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
  case cons Γ Γ' Δ Δ' A r s i ξ ty agr ih =>
    intro mrg; cases mrg with
    | contra Δ1 Δ2 h mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists A.[ren ξ] :⟨.ex, s⟩ Δ1', A.[ren ξ] :⟨.ex, s⟩ Δ2'
      and_intros
      . constructor <;> assumption
      . constructor <;> assumption
      . constructor <;> assumption
    | @left Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists A.[ren ξ] :⟨.ex, s⟩ Δ1', A.[ren ξ] :⟨.im, s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> assumption
      . constructor <;> assumption
    | @right Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists A.[ren ξ] :⟨.im, s⟩ Δ1', A.[ren ξ] :⟨.ex, s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> assumption
      . constructor <;> assumption
    | @im Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
      exists A.[ren ξ] :⟨.im, s⟩ Δ1', A.[ren ξ] :⟨.im, s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> assumption
      . constructor <;> assumption
  case wk Γ Γ' Δ Δ' A s i ξ ty agr ih =>
    intro mrg
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
    exists A :⟨.im, s⟩ Δ1', A :⟨.im, s⟩ Δ2'
    and_intros
    . constructor; assumption
    . constructor <;> assumption
    . constructor <;> assumption

lemma Typed.renaming {Γ Γ'} {Δ Δ' : Ctx Srt} {A m ξ} :
    Γ ;; Δ ⊢ m : A -> AgreeRen ξ Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢ m.[ren ξ] : A.[ren ξ] := by
  intro ty agr; induction ty using
    @Typed.rec _ inst
      (motive_2 := fun Γ Δ _ => ∀ {Γ' Δ' ξ}, AgreeRen ξ Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢)
  generalizing Γ' Δ' ξ <;> asimp
  case var h _ =>
    constructor <;> try aesop
    apply agr.has h
  case lam_im Γ Δ A B m s sA i lw tyA tym ih =>
    constructor
    . apply agr.lower lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.cons .im tyA)
      asimp at ih; assumption
  case lam_ex Γ Δ A B m rA s sA i rs lw tyA tym ih =>
    constructor
    . apply rs
    . apply agr.lower lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.cons rA tyA)
      asimp at ih; assumption
  case app_im Γ Δ A B m n s tym tyn ih =>
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    have ty := Typed.app_im tym tyn
    asimp at ty; assumption
  case app_ex Γ Δ1 Δ2 Δ A B m n s mrg tym tyn ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn agr2; asimp at tyn
    have ty := Typed.app_ex mrg tym tyn
    asimp at ty; assumption
  case tup_im tyS tym tyn ih =>
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    replace tyS := tyS.renaming agr.toStatic; asimp at tyS
    constructor <;> (asimp; assumption)
  case tup_ex mrg tyS tym tyn ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn agr2; asimp at tyn
    replace tyS := tyS.renaming agr.toStatic; asimp at tyS
    constructor <;> (asimp; assumption)
  case proj_im A B C m n rA s sA sB sC iC rs mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have wf := tyn.toWf
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    rcases wf with _ | ⟨tyB, wf⟩
    rcases wf with _ | ⟨tyA, _⟩
    replace tyC := tyC.renaming (agr.toStatic.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons rA tyA).cons .im tyB)
    rw[show C.[.tup (.var 1) (.var 0) .im s .: shift 2].[ren (upren (upren ξ))]
          = C.[up (ren ξ)].[.tup (.var 1) (.var 0) .im s .: shift 2]
        by asimp] at tyn
    rw[SubstLemmas.upren_up] at tyn
    have ty := Typed.proj_im rs mrg tyC tym tyn
    asimp at ty; assumption
  case proj_ex A B C m n rA rB s sA sB sC iC rs1 rs2 mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have wf := tyn.toWf
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    rcases wf with _ | ⟨tyB, wf⟩
    rcases wf with _ | ⟨tyA, _⟩
    replace tyC := tyC.renaming (agr.toStatic.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons rA tyA).cons rB tyB)
    rw[show C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[ren (upren (upren ξ))]
          = C.[up (ren ξ)].[.tup (.var 1) (.var 0) .ex s .: shift 2]
        by asimp] at tyn
    rw[SubstLemmas.upren_up] at tyn
    have ty := Typed.proj_ex rs1 rs2 mrg tyC tym tyn
    asimp at ty; assumption
  case tt h ih => constructor <;> aesop (rule_sets := [rename])
  case ff h ih => constructor <;> aesop (rule_sets := [rename])
  case ite A _ _ _ _ _  mrg tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    have ⟨s, i, _, tyb⟩ := tyA.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn1 agr2; asimp at ihn1
    specialize ihn2 agr2; asimp at ihn2
    replace tyA := tyA.renaming (agr.toStatic.cons tyb); asimp at tyA
    rw[show A.[.tt .: ren ξ] = A.[up (ren ξ)].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: ren ξ] = A.[up (ren ξ)].[.ff/] by asimp] at ihn2
    have ty := Typed.ite mrg tyA ihm ihn1 ihn2; asimp at ty
    assumption
  case rw A B m n a b s i tyA tym tyn ih =>
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace tyA := tyA.renaming ((agr.toStatic.cons tyB).cons tyI); asimp at tyA
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    simp[<-SubstLemmas.subst_comp] at tyA
    rw[show A.[a.[ren ξ].rfl .: a.[ren ξ] .: ren ξ]
          = A.[upn 2 (ren ξ)].[.rfl a.[ren ξ],a.[ren ξ]/]
         by asimp] at tym
    have := Typed.rw tyA tym tyn
    asimp at this; assumption
  case conv eq tym tyB ih =>
    replace tyB := tyB.renaming agr.toStatic
    replace tym := ih agr
    apply Typed.conv
    . apply Static.Conv.subst _ eq
    . assumption
    . assumption
  case nil agr => apply agr.wf_nil
  case cons agr => apply agr.wf_cons <;> aesop

lemma Typed.weaken {Γ} {Δ : Ctx Srt} {A B m s i} :
    Γ ;; Δ ⊢ m : A ->
    Γ ⊢ B : .srt s i ->
    B :: Γ ;; B :⟨.im, s⟩ Δ ⊢ m.[shift 1] : A.[shift 1] := by
  intro tym tyB
  apply tym.renaming
  constructor
  . assumption
  . exact AgreeRen.refl tym.toWf

lemma Typed.eweaken {Γ Γ'} {Δ Δ' : Ctx Srt} {A A' B m m' s i} :
    Γ' = B :: Γ ->
    Δ' = B :⟨.im, s⟩ Δ ->
    m' = m.[shift 1] ->
    A' = A.[shift 1] ->
    Γ ;; Δ ⊢ m : A ->
    Γ ⊢ B : .srt s i ->
    Γ' ;; Δ' ⊢ m' : A' := by
  intros; subst_vars
  apply Typed.weaken <;> assumption
