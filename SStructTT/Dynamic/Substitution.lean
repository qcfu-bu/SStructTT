import SStructTT.Static.Substitution
import SStructTT.Dynamic.Renaming

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst : (Var -> Tm Srt) ->
  Static.Ctx Srt -> Dynamic.Ctx Srt ->
  Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop
where
  | nil {σ} :
    AgreeSubst σ [] [] [] []
  | ex {Γ Γ' Δ Δ' A s i σ} :
    Γ ⊢ A : .srt s i ->
    AgreeSubst σ Γ Δ Γ' Δ' ->
    AgreeSubst (up σ) (A :: Γ) (A :⟨s⟩ Δ) (A.[σ] :: Γ') (A.[σ] :⟨s⟩ Δ')
  | im {Γ Γ' Δ Δ' A s i σ} :
    Γ ⊢ A : .srt s i ->
    AgreeSubst σ Γ Δ Γ' Δ' ->
    AgreeSubst (up σ) (A :: Γ) (_: Δ) (A.[σ] :: Γ') (_: Δ')
  | wk_im {Γ Γ' Δ Δ' A m σ} :
    Γ' ⊢ m : A.[σ] ->
    AgreeSubst σ Γ Δ Γ' Δ' ->
    AgreeSubst (m .: σ) (A :: Γ) (_: Δ) Γ' Δ'
  | wk_ex {Γ Γ' Δ Δ' Δa Δb A m s σ} :
    Merge Δa Δb Δ' ->
    Δa !≤ s ->
    Γ' ;; Δa ⊢ m : A.[σ] ->
    AgreeSubst σ Γ Δ Γ' Δb ->
    AgreeSubst (m .: σ) (A :: Γ) (A :⟨s⟩ Δ) Γ' Δ'
  | conv_im {Γ Γ' Δ Δ' A B s i σ} :
    A === B ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ (A :: Γ) (_: Δ) Γ' Δ' ->
    AgreeSubst σ (B :: Γ) (_: Δ) Γ' Δ'
  | conv_ex {Γ Γ' Δ Δ' A B s i σ} :
    A === B ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ (A :: Γ) (A :⟨s⟩ Δ) Γ' Δ' ->
    AgreeSubst σ (B :: Γ) (B :⟨s⟩ Δ) Γ' Δ'

lemma AgreeSubst.toStatic {Γ Γ'} {Δ Δ' : Ctx Srt} {σ} :
    Dynamic.AgreeSubst σ Γ Δ Γ' Δ' -> Static.AgreeSubst σ Γ Γ' := by
  intro agr
  induction agr <;> try aesop (rule_sets := [subst])
  case ex => constructor <;> assumption
  case im => constructor <;> assumption
  case wk_im => constructor <;> assumption
  case wk_ex tym agr ih =>
    constructor
    . apply tym.toStatic
    . assumption

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Γ} {Δ : Ctx Srt} : Γ ;; Δ ⊢ -> AgreeSubst ids Γ Δ Γ Δ := by
  intro wf; induction wf
  all_goals try trivial
  case nil => constructor
  case ex ty wf agr =>
    replace agr := AgreeSubst.ex ty agr
    asimp at agr; assumption
  case im ty wf agr =>
    replace agr := AgreeSubst.im ty agr
    asimp at agr; assumption

lemma AgreeSubst.none {Γ Γ'} {Δ Δ' : Ctx Srt} {σ} :
    AgreeSubst σ Γ Δ Γ' Δ' -> Δ.Forall (. = none) -> Δ'.Forall (. = none) := by
  intro agr h; induction agr
  case nil => simp
  case ex => simp at h
  case im ih => simp at h; aesop
  case wk_im ih => simp at h; aesop
  case wk_ex => simp at h
  case conv_im => simp at h; aesop
  case conv_ex => simp at h

lemma AgreeSubst.lower {Γ Γ'} {Δ Δ' : Ctx Srt} {s σ} :
    AgreeSubst σ Γ Δ Γ' Δ' -> Δ !≤ s -> Δ' !≤ s := by
  sorry

lemma AgreeSubst.has {Γ Γ'} {Δ Δ' : Ctx Srt} {A x s σ} :
    AgreeSubst σ Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢ -> Has Δ x s A -> Γ' ;; Δ' ⊢ (σ x) : A.[σ] := by
  intro agr wf hs; induction agr generalizing x A
  case nil => cases hs
  case ex A s i σ tyA agr ih =>
    rcases hs with ⟨h⟩
    asimp
    constructor
    . assumption
    . rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
      constructor
      apply agr.none h
  case im A s i σ tyA agr ih =>
    rcases wf with _ | _ | ⟨_, wf⟩
    rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
    rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
    apply Typed.eweaken <;> try first | rfl | assumption
    apply ih <;> assumption
  case wk_im ih =>
    rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
    apply ih <;> assumption
  case wk_ex mrg _ _ agr ih =>
    rcases hs with ⟨h⟩; asimp
    rw[<-mrg.sym.none (agr.none h)]
    assumption
  case conv_im σ eq tyB tyB' agr ih =>
    rcases hs with _ | @⟨_, A, x, s, hs⟩
    apply ih
    . assumption
    . constructor; assumption
  case conv_ex σ eq tyB tyB' agr ih =>
    rcases hs with ⟨h⟩
    apply Typed.conv
    . open Static in
      apply Conv.subst _ (Conv.subst _ eq)
    . apply ih wf; constructor; assumption
    . assumption

lemma AgreeSubst.split {Γ Γ'} {Δ Δ' Δa Δb : Ctx Srt} {σ} :
    AgreeSubst σ Γ Δ Γ' Δ' -> Merge Δa Δb Δ ->
    ∃ Δa' Δb',
      Merge Δa' Δb' Δ' ∧
      AgreeSubst σ Γ Δa Γ' Δa' ∧
      AgreeSubst σ Γ Δb Γ' Δb' := by
  intro agr mrg; induction agr generalizing Δa Δb
  case nil =>
    cases mrg; exists [], []
    aesop (rule_sets := [subst])
  case ex A s i σ tyA agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists A.[σ] :⟨s⟩ Δa', A.[σ] :⟨s⟩ Δb'; and_intros
      all_goals constructor <;> assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists A.[σ] :⟨s⟩ Δa', _: Δb'; and_intros
      all_goals constructor <;> assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists _: Δa', A.[σ] :⟨s⟩ Δb'; and_intros
      all_goals constructor <;> assumption
  case im A s i σ tyA agr ih =>
    cases mrg with
    | im mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists _: Δa', _: Δb'; and_intros
      all_goals constructor <;> assumption
  case wk_im agr ih =>
    cases mrg with
    | im mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists Δa', Δb'; and_intros
      . assumption
      . constructor <;> assumption
      . constructor <;> assumption
  case wk_ex mrg1 lw tym agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2
      have ⟨Δc2, mrg5, mrg6⟩ := mrg1.sym.split mrg2.sym
      exists Δc1, Δc2; and_intros
      . apply Merge.compose <;> assumption
      . apply AgreeSubst.wk_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr1
      . apply AgreeSubst.wk_ex
        . exact mrg5.sym
        . exact lw
        . exact tym
        . exact agr2
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2
      exists Δc1, Δb'; and_intros
      . exact mrg4
      . apply AgreeSubst.wk_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr1
      . apply AgreeSubst.wk_im
        . exact tym.toStatic
        . exact agr2
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2.sym
      exists Δa', Δc1; and_intros
      . exact mrg4.sym
      . apply AgreeSubst.wk_im
        . exact tym.toStatic
        . exact agr1
      . apply AgreeSubst.wk_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr2
  case conv_im eq tyB tyB' agr ih =>
    cases mrg with
    | im mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.im mrg)
      exists Δa', Δb'; and_intros
      . assumption
      . apply AgreeSubst.conv_im <;> assumption
      . apply AgreeSubst.conv_im <;> assumption
  case conv_ex A B s i σ eq tyB tyB' agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.contra A s h mrg)
      exists Δa', Δb'; and_intros
      . assumption
      . apply AgreeSubst.conv_ex <;> assumption
      . apply AgreeSubst.conv_ex <;> assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.left A s mrg)
      exists Δa', Δb'
      and_intros
      . assumption
      . apply AgreeSubst.conv_ex <;> assumption
      . apply AgreeSubst.conv_im <;> assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.right A s mrg)
      exists Δa', Δb'
      and_intros
      . assumption
      . apply AgreeSubst.conv_im <;> assumption
      . apply AgreeSubst.conv_ex <;> assumption
