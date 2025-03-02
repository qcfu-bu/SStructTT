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
