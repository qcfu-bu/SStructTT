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
    cases hs
    asimp
    constructor
    . assumption
    . rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
      constructor
      sorry
  case im A s i σ tyA agr ih =>
    rcases wf with _ | _ | ⟨_, wf⟩
    rcases hs with _ | @⟨_, A, s, x, hs⟩; asimp
    rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
    apply Typed.eweaken <;> try first | rfl | assumption
    apply ih <;> assumption
