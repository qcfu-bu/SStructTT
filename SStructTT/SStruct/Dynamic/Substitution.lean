import SStructTT.SStruct.Static.Substitution
import SStructTT.SStruct.Dynamic.Renaming
open SStruct.Static

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst : (Var -> Tm Srt) ->
  Static.Ctx Srt -> Dynamic.Ctx Srt ->
  Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop
where
  | nil {σ} :
    AgreeSubst σ [] [] [] []
  | cons {Γ Γ' Δ Δ' A} r {s i σ} :
    Γ ⊢ A : .srt s i ->
    AgreeSubst σ Γ Δ Γ' Δ' ->
    AgreeSubst (up σ) (A :: Γ) (A :⟨r, s⟩ Δ) (A.[σ] :: Γ') (A.[σ] :⟨r, s⟩ Δ')
  | wk_im {Γ Γ' Δ Δ' A m s σ} :
    Γ' ⊢ m : A.[σ] ->
    AgreeSubst σ Γ Δ Γ' Δ' ->
    AgreeSubst (m .: σ) (A :: Γ) (A :⟨.im, s⟩ Δ) Γ' Δ'
  | wk_ex {Γ Γ' Δ Δ' Δa Δb A m s σ} :
    Merge Δa Δb Δ' ->
    Lower Δa s ->
    Γ' ;; Δa ⊢ m : A.[σ] ->
    AgreeSubst σ Γ Δ Γ' Δb ->
    AgreeSubst (m .: σ) (A :: Γ) (A :⟨.ex, s⟩ Δ) Γ' Δ'
  | conv {Γ Γ' Δ Δ' A B r s i σ} :
    A === B ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ (A :: Γ) (A :⟨r, s⟩ Δ) Γ' Δ' ->
    AgreeSubst σ (B :: Γ) (B :⟨r, s⟩ Δ) Γ' Δ'

lemma AgreeSubst.toStatic {Γ Γ'} {Δ Δ' : Ctx Srt} {σ} :
    Dynamic.AgreeSubst σ Γ Δ Γ' Δ' -> Static.AgreeSubst σ Γ Γ' := by
  intro agr
  induction agr <;> try aesop (rule_sets := [subst])
  case cons => constructor <;> assumption
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
  case cons r _ _ ty wf agr =>
    replace agr := agr.cons r ty
    asimp at agr; assumption

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.implicit {Γ Γ'} {Δ Δ' : Ctx Srt} {σ} :
    AgreeSubst σ Γ Δ Γ' Δ' ->
    Δ.Forall (∃ A s, . = (A, .im, s)) ->
    Δ'.Forall (∃ A s, . = (A, .im, s)) := by
  intro agr h; induction agr
  case nil => simp
  case cons ih => simp at h; aesop
  case wk_im ih => simp at h; aesop
  case wk_ex => simp at h
  case conv => simp at h; aesop

lemma AgreeSubst.lower {Γ Γ'} {Δ Δ' : Ctx Srt} {s σ} :
    AgreeSubst σ Γ Δ Γ' Δ' -> Lower Δ s -> Lower Δ' s := by
  intro agr lw; induction agr generalizing s
  case nil => assumption
  case cons =>
    cases lw <;> constructor <;> aesop
  case wk_im => cases lw; aesop
  case wk_ex mrg _ _ _ _ =>
    cases lw
    apply mrg.lower
    . apply Lower.trans <;> assumption
    . aesop
  case conv ih => cases lw <;> aesop

lemma AgreeSubst.has {Γ Γ'} {Δ Δ' : Ctx Srt} {A x s σ} :
    AgreeSubst σ Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢ -> Has Δ x s A -> Γ' ;; Δ' ⊢ (σ x) : A.[σ] := by
  intro agr wf hs; induction agr generalizing x A
  case nil => cases hs
  case cons A r s i σ tyA agr ih =>
    cases r with
    | ex =>
      rcases hs with ⟨h⟩; asimp
      constructor
      . assumption
      . rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
        constructor; apply agr.implicit h
    | im =>
      rcases wf with _ | ⟨_, wf⟩
      rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
      rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
      apply Typed.eweaken <;> try first | rfl | assumption
      apply ih <;> assumption
  case wk_im ih =>
    rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
    apply ih <;> assumption
  case wk_ex mrg _ _ agr ih =>
    rcases hs with ⟨h⟩; asimp
    rw[<-mrg.sym.implicit (agr.implicit h)]
    assumption
  case conv r _ _  σ eq tyB tyB' agr ih =>
    cases r with
    | im =>
      rcases hs with _ | @⟨_, A, x, s, hs⟩
      apply ih
      . assumption
      . constructor; assumption
    | ex =>
      rcases hs with ⟨h⟩
      apply Typed.conv
      . apply Conv.subst _ (Conv.subst _ eq)
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
  case cons A r s i σ tyA agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists A.[σ] :⟨.ex, s⟩ Δa', A.[σ] :⟨.ex, s⟩ Δb'; and_intros
      all_goals constructor <;> assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists A.[σ] :⟨.ex, s⟩ Δa', A.[σ] :⟨.im, s⟩ Δb'; and_intros
      all_goals constructor <;> assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists A.[σ] :⟨.im, s⟩ Δa', A.[σ] :⟨.ex, s⟩ Δb'; and_intros
      all_goals constructor <;> assumption
    | im _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      exists A.[σ] :⟨.im, s⟩ Δa', A.[σ] :⟨.im, s⟩ Δb'; and_intros
      all_goals constructor <;> assumption
  case wk_im agr ih =>
    cases mrg with
    | im _ _ mrg =>
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
  case conv A B r s i σ eq tyB tyB' agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.contra A s h mrg)
      exists Δa', Δb'; aesop (rule_sets := [subst])
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.left A s mrg)
      exists Δa', Δb'; aesop (rule_sets := [subst])
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.right A s mrg)
      exists Δa', Δb'; aesop (rule_sets := [subst])
    | im _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.im _ _ mrg)
      exists Δa', Δb'; aesop (rule_sets := [subst])

lemma AgreeSubst.wf_nil {Γ'} {Δ' : Ctx Srt} {σ} :
    AgreeSubst σ [] [] Γ' Δ' -> Γ' ;; Δ' ⊢ := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro agr; induction agr <;> try trivial
  constructor

lemma AgreeSubst.wf_cons {Γ Γ'} {Δ Δ' : Ctx Srt} {A r s σ} :
    AgreeSubst σ (A :: Γ) (A :⟨r, s⟩ Δ) Γ' Δ' -> Γ ;; Δ ⊢ ->
    (∀ {Γ' Δ' σ}, AgreeSubst σ Γ Δ Γ' Δ' → Γ' ;; Δ' ⊢) ->
    Γ' ;; Δ' ⊢ := by
  generalize e1: A :: Γ = Γ0
  generalize e2: A :⟨r, s⟩ Δ = Δ0
  intro agr wf h; induction agr generalizing Γ Δ A r s <;> try trivial
  case cons tyA agr ih =>
    cases e1; cases e2
    constructor
    . apply tyA.substitution agr.toStatic
    . apply h agr
  case wk_im agr _ =>
    cases e1; cases e2
    apply h agr
  case wk_ex mrg lw tym agr ih =>
    cases e1; cases e2
    apply Wf.merge mrg tym.toWf (h agr)
  case conv ih =>
    cases e1; cases e2
    apply ih rfl rfl wf h

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.wf {Γ Γ'} {Δ Δ' : Ctx Srt} {σ} :
    AgreeSubst σ Γ Δ Γ' Δ' ->
    Γ ;; Δ ⊢ -> Γ' ;; Δ' ⊢ := by
  intro agr wf; induction wf generalizing Γ' Δ' σ
  all_goals try aesop
  case nil => apply agr.wf_nil
  case cons => apply agr.wf_cons <;> aesop

lemma Typed.substitution {Γ Γ'} {Δ Δ' : Ctx Srt} {A m σ} :
    Γ ;; Δ ⊢ m : A -> AgreeSubst σ Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢ m.[σ] : A.[σ] := by
  intro ty agr; induction ty using
    @Typed.rec _ ord
      (motive_2 := fun Γ Δ _ => ∀ {Γ' Δ' σ}, AgreeSubst σ Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢)
  generalizing Γ' Δ' σ <;> asimp
  case var wf hs ih => apply agr.has (ih agr) hs
  case lam_im lw tyA tym ih =>
    apply Typed.lam_im
    . apply agr.lower lw
    . apply tyA.substitution agr.toStatic
    . apply ih; constructor <;> assumption
  case lam_ex A B m rA s sA i rs lw tyA tym ih =>
    apply Typed.lam_ex
    . assumption
    . apply agr.lower lw
    . apply tyA.substitution agr.toStatic
    . apply ih; constructor <;> assumption
  case app_im tym tyn ih =>
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.substitution agr.toStatic
    have ty := Typed.app_im tym tyn
    asimp at ty; assumption
  case app_ex mrg tym tyn ihm ihn =>
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn agr2
    have ty := Typed.app_ex mrg ihm ihn
    asimp at ty; assumption
  case tup_im B m n s i tyS tym tyn ihm =>
    replace tyS := tyS.substitution agr.toStatic; asimp at tyS
    replace tym := ihm agr; asimp at tym
    replace tyn := tyn.substitution agr.toStatic; asimp at tyn
    rw[show B.[m.[σ] .: σ] = B.[up σ].[m.[σ]/] by asimp] at tyn
    have ty := Typed.tup_im tyS tym tyn; assumption
  case tup_ex B m n s i mrg tyS tym tyn ihm ihn =>
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyS := tyS.substitution agr.toStatic; asimp at tyS
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn agr2; asimp at tyn
    rw[show B.[m.[σ] .: σ] = B.[up σ].[m.[σ]/] by asimp] at tyn
    have ty := Typed.tup_ex mrg tyS tym tyn; assumption
  case proj_im A B C m n rA s sA sB sC iC rs mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := tyn.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toStatic.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons rA tyA).cons .im tyB); asimp at tyn
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Typed.proj_im <;> (asimp; assumption)
  case proj_ex C m n rA rB s sA sB sC i rs1 rs2 mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := tyn.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toStatic.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons rA tyA).cons rB tyB); asimp at tyn
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Typed.proj_ex
    . apply rs1
    . apply rs2
    . assumption
    . assumption
    . assumption
    . asimp; assumption
  case tt h ih => constructor <;> aesop (rule_sets := [subst])
  case ff h ih => constructor <;> aesop (rule_sets := [subst])
  case ite A m n1 n2 s i mrg tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    have ⟨s, i, _, tyb⟩ := tyA.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn1 agr2; asimp at ihn1
    specialize ihn2 agr2; asimp at ihn2
    replace tyA := tyA.substitution (agr.toStatic.cons tyb); asimp at tyA
    rw[show A.[.tt .: σ] = A.[up σ].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: σ] = A.[up σ].[.ff/] by asimp] at ihn2
    have ty := Typed.ite mrg tyA ihm ihn1 ihn2; asimp at ty
    assumption
  case rw A B m n a b s i tyA tym tyn ih =>
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace tyA := tyA.substitution ((agr.toStatic.cons tyB).cons tyI); asimp at tyA
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.substitution agr.toStatic; asimp at tyn
    simp[<-SubstLemmas.subst_comp] at tyA
    rw[show A.[a.[σ].rfl .: a.[σ] .: σ]
          = A.[upn 2 σ].[.rfl a.[σ],a.[σ]/]
         by asimp] at tym
    have := Typed.rw tyA tym tyn
    asimp at this; assumption
  case conv eq tym tyB ih =>
    replace tyB := tyB.substitution agr.toStatic
    replace tym := ih agr
    apply Typed.conv
    . apply Conv.subst _ eq
    . assumption
    . assumption
  case nil agr => apply agr.wf_nil
  case cons agr => apply agr.wf_cons <;> aesop

lemma Typed.subst_im {Γ} {Δ : Ctx Srt} {A B m n s} :
    A :: Γ ;; A :⟨.im, s⟩ Δ ⊢ m : B ->
    Γ ⊢ n : A ->
    Γ ;; Δ ⊢ m.[n/] : B.[n/] := by
  intro tym tyn
  obtain ⟨_, _, _⟩ := tym.ctx_inv
  apply tym.substitution
  apply AgreeSubst.wk_im
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Typed.subst_ex {Γ} {Δ1 Δ2 Δ : Ctx Srt} {A B m n s} :
    Lower Δ2 s -> Merge Δ1 Δ2 Δ ->
    A :: Γ ;; A :⟨.ex, s⟩ Δ1 ⊢ m : B ->
    Γ ;; Δ2 ⊢ n : A ->
    Γ ;; Δ ⊢ m.[n/] : B.[n/] := by
  intro lw mrg tym tyn
  obtain ⟨_, _, _⟩ := tym.ctx_inv
  apply tym.substitution
  apply AgreeSubst.wk_ex
  . apply mrg.sym
  . assumption
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Typed.esubst_im {Γ} {Δ : Ctx Srt} {A B B' m m' n s} :
    m' = m.[n/] ->
    B' = B.[n/] ->
    A :: Γ ;; A :⟨.im, s⟩ Δ ⊢ m : B ->
    Γ ⊢ n : A ->
    Γ ;; Δ ⊢ m' : B' := by
  intros; subst_vars; apply Typed.subst_im <;> assumption

lemma Typed.esubst_ex {Γ} {Δ1 Δ2 Δ : Ctx Srt} {A B B' m m' n s} :
    m' = m.[n/] ->
    B' = B.[n/] ->
    Lower Δ2 s -> Merge Δ1 Δ2 Δ ->
    A :: Γ ;; A :⟨.ex, s⟩ Δ1 ⊢ m : B ->
    Γ ;; Δ2 ⊢ n : A ->
    Γ ;; Δ ⊢ m' : B' := by
  intros; subst_vars; apply Typed.subst_ex <;> assumption

lemma Typed.conv_ctx {Γ} {Δ : Ctx Srt} {A B C m r s i} :
    B === A ->
    Γ ⊢ B : .srt s i ->
    A :: Γ ;; A :⟨r, s⟩ Δ ⊢ m : C ->
    B :: Γ ;; B :⟨r, s⟩ Δ ⊢ m : C := by
  intro eq tyB tym
  obtain ⟨_, wf, tyA⟩ := tym.ctx_inv
  replace tym : B :: Γ ;; B :⟨r, s⟩ Δ ⊢ m.[ids] : C.[ids] := by
    apply tym.substitution
    apply AgreeSubst.conv <;> try assumption
    . asimp; apply tyA.weaken tyB
    . apply AgreeSubst.refl; constructor <;> assumption
  asimp at tym; assumption
