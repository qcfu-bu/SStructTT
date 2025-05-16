import SStructTT.SStruct.Dynamic.Substitution
import SStructTT.SStruct.Erasure.Renaming
open SStruct.Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst :
  (Var -> SStruct.Tm Srt) ->
  (Var -> Erasure.Tm Srt) ->
  Static.Ctx Srt -> Dynamic.Ctx Srt ->
  Static.Ctx Srt -> Dynamic.Ctx Srt -> Prop
where
  | nil {σ σ'} :
    AgreeSubst σ σ' [] [] [] []
  | cons {Γ Γ' Δ Δ' A} r {s i σ σ'} :
    Γ ⊢ A : .srt s i ->
    AgreeSubst σ σ' Γ Δ Γ' Δ' ->
    AgreeSubst (up σ) (up σ') (A :: Γ) (A :⟨r, s⟩ Δ) (A.[σ] :: Γ') (A.[σ] :⟨r, s⟩ Δ')
  | wk_im {Γ Γ' Δ Δ' A m m' s σ σ'} :
    Γ' ⊢ m : A.[σ] ->
    AgreeSubst σ σ' Γ Δ Γ' Δ' ->
    AgreeSubst (m .: σ) (m' .: σ') (A :: Γ) (A :⟨.im, s⟩ Δ) Γ' Δ'
  | wk_ex {Γ Γ' Δ Δ' Δa Δb A m m' s σ σ'} :
    Merge Δa Δb Δ' ->
    Δa ≤* s ->
    Γ' ;; Δa ⊢ m ▷ m' : A.[σ] ->
    AgreeSubst σ σ' Γ Δ Γ' Δb ->
    AgreeSubst (m .: σ) (m' .: σ') (A :: Γ) (A :⟨.ex, s⟩ Δ) Γ' Δ'
  | conv {Γ Γ' Δ Δ' A B r s i σ σ'} :
    A === B ->
    Γ ⊢ B : .srt s i ->
    Γ' ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ σ' (A :: Γ) (A :⟨r, s⟩ Δ) Γ' Δ' ->
    AgreeSubst σ σ' (B :: Γ) (B :⟨r, s⟩ Δ) Γ' Δ'

lemma AgreeSubst.toDynamic {Γ Γ'} {Δ Δ' : Ctx Srt} {σ σ'} :
    Erasure.AgreeSubst σ σ' Γ Δ Γ' Δ' -> Dynamic.AgreeSubst σ Γ Δ Γ' Δ' := by
  intro agr
  induction agr <;> try aesop (rule_sets := [subst])
  case cons => constructor <;> assumption
  case wk_im => constructor <;> assumption
  case wk_ex tym agr ih =>
    constructor <;> try assumption
    apply tym.toDynamic

lemma AgreeSubst.toStatic {Γ Γ'} {Δ Δ' : Ctx Srt} {σ σ'} :
    Erasure.AgreeSubst σ σ' Γ Δ Γ' Δ' -> Static.AgreeSubst σ Γ Γ' := by
  intro agr; apply agr.toDynamic.toStatic

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Γ} {Δ : Ctx Srt} : Γ ;; Δ ⊢ -> AgreeSubst ids ids Γ Δ Γ Δ := by
  intro wf; induction wf
  all_goals try trivial
  case nil => constructor
  case cons r _ _ ty wf agr =>
    replace agr := agr.cons r ty
    asimp at agr; assumption

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.implicit {Γ Γ'} {Δ Δ' : Ctx Srt} {σ σ'} :
    AgreeSubst σ σ' Γ Δ Γ' Δ' ->
    Δ.Forall (∃ A s, . = (A, .im, s)) ->
    Δ'.Forall (∃ A s, . = (A, .im, s)) := by
  intro agr; apply agr.toDynamic.implicit

lemma AgreeSubst.lower {Γ Γ'} {Δ Δ' : Ctx Srt} {s σ σ'} :
    AgreeSubst σ σ' Γ Δ Γ' Δ' -> Δ ≤* s -> Δ' ≤* s := by
  intro agr; apply agr.toDynamic.lower

lemma AgreeSubst.has {Γ Γ'} {Δ Δ' : Ctx Srt} {A x s σ σ'} :
    AgreeSubst σ σ' Γ Δ Γ' Δ' -> Γ' ;; Δ' ⊢ ->
    Has Δ x s A -> Γ' ;; Δ' ⊢ (σ x) ▷ (σ' x) : A.[σ] := by
  intro agr wf hs; induction agr generalizing x A
  case nil => cases hs
  case cons A r s i σ σ' tyA agr ih =>
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
      apply Erased.eweaken <;> try first | rfl | assumption
      apply ih <;> assumption
  case wk_im ih =>
    rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
    apply ih <;> assumption
  case wk_ex mrg _ _ agr ih =>
    rcases hs with ⟨h⟩; asimp
    rw[<-mrg.sym.implicit (agr.implicit h)]
    assumption
  case conv r _ _  σ σ' eq tyB tyB' agr ih =>
    cases r with
    | im =>
      rcases hs with _ | @⟨_, A, x, s, hs⟩
      apply ih
      . assumption
      . constructor; assumption
    | ex =>
      rcases hs with ⟨h⟩
      apply Erased.conv
      . apply Static.Conv.subst _ (Static.Conv.subst _ eq)
      . apply ih wf; constructor; assumption
      . assumption

lemma AgreeSubst.split {Γ Γ'} {Δ Δ' Δa Δb : Ctx Srt} {σ σ'} :
    AgreeSubst σ σ' Γ Δ Γ' Δ' -> Merge Δa Δb Δ ->
    ∃ Δa' Δb',
      Merge Δa' Δb' Δ' ∧
      AgreeSubst σ σ' Γ Δa Γ' Δa' ∧
      AgreeSubst σ σ' Γ Δb Γ' Δb' := by
  intro agr mrg; induction agr generalizing Δa Δb
  case nil =>
    cases mrg; exists [], []
    aesop (rule_sets := [subst])
  case cons A r s i σ σ' tyA agr ih =>
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
  case conv A B r s i σ σ' eq tyB tyB' agr ih =>
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

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.wf {Γ Γ'} {Δ Δ' : Ctx Srt} {σ σ'} :
    AgreeSubst σ σ' Γ Δ Γ' Δ' ->
    Γ ;; Δ ⊢ -> Γ' ;; Δ' ⊢ := by
  intro agr; apply agr.toDynamic.wf

lemma Erased.substitution {Γ Γ'} {Δ Δ' : Ctx Srt} {A m m' σ σ'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> AgreeSubst σ σ' Γ Δ Γ' Δ' ->
    Γ' ;; Δ' ⊢ m.[σ] ▷ m'.[σ'] : A.[σ] := by
  intro ty agr; induction ty generalizing Γ' Δ' σ σ' <;> asimp
  case var wf hs =>
    apply agr.has (agr.wf wf) hs
  case lam_im lw tyA erm ihm =>
    apply Erased.lam_im
    . apply agr.lower lw
    . apply tyA.substitution agr.toStatic
    . apply ihm; constructor <;> assumption
  case lam_ex A B m rA s sA i rs lw tyA erm ih =>
    apply Erased.lam_ex
    . assumption
    . apply agr.lower lw
    . apply tyA.substitution agr.toStatic
    . apply ih; constructor <;> assumption
  case app_im erm tyn ih =>
    replace erm := ih agr; asimp at erm
    replace tyn := tyn.substitution agr.toStatic
    have er := Erased.app_im erm tyn
    asimp at er; assumption
  case app_ex mrg erm ern ihm ihn =>
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn agr2
    have er := Erased.app_ex mrg ihm ihn
    asimp at er; assumption
  case tup_im B m m' n s i tyS erm tyn ihm =>
    replace tyS := tyS.substitution agr.toStatic; asimp at tyS
    replace erm := ihm agr; asimp at erm
    replace tyn := tyn.substitution agr.toStatic; asimp at tyn
    rw[show B.[m.[σ] .: σ] = B.[up σ].[m.[σ]/] by asimp] at tyn
    have er := Erased.tup_im tyS erm tyn; assumption
  case tup_ex B m m' n n' s i mrg tyS erm ern ihm ihn =>
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyS := tyS.substitution agr.toStatic; asimp at tyS
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn agr2; asimp at ern
    rw[show B.[m.[σ] .: σ] = B.[up σ].[m.[σ]/] by asimp] at ern
    have er := Erased.tup_ex mrg tyS erm ern; assumption
  case proj_im A B C m m' n n' rA s sA sB sC iC c rs mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toStatic.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons rA tyA).cons .im tyB); asimp at ern
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Erased.proj_im <;> (asimp; assumption)
  case proj_ex C m m' n n' rA rB s sA sB sC i c1 c2 rs1 rs2 mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toStatic.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons rA tyA).cons rB tyB); asimp at ern
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Erased.proj_ex
    . apply rs1
    . apply rs2
    . assumption
    . assumption
    . assumption
    . asimp; assumption
  case tt h ih => constructor; apply agr.wf h; apply agr.implicit ih
  case ff h ih => constructor; apply agr.wf h; apply agr.implicit ih
  case ite A m m' n1 n1' n2 n2' s i mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    have ⟨s, i, _, tyb⟩ := tyA.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn1 agr2; asimp at ihn1
    specialize ihn2 agr2; asimp at ihn2
    replace tyA := tyA.substitution (agr.toStatic.cons tyb); asimp at tyA
    rw[show A.[.tt .: σ] = A.[up σ].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: σ] = A.[up σ].[.ff/] by asimp] at ihn2
    have er := Erased.ite mrg tyA ihm ihn1 ihn2; asimp at er
    assumption
  case rw A B m m' n a b s i tyA erm tyn ih =>
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace tyA := tyA.substitution ((agr.toStatic.cons tyB).cons tyI); asimp at tyA
    replace erm := ih agr; asimp at erm
    replace tyn := tyn.substitution agr.toStatic; asimp at tyn
    simp[<-SubstLemmas.subst_comp] at tyA
    rw[show A.[a.[σ].rfl .: a.[σ] .: σ]
          = A.[upn 2 σ].[.rfl a.[σ],a.[σ]/]
         by asimp] at erm
    have := Erased.rw tyA erm tyn
    asimp at this; assumption
  case conv eq erm tyB ih =>
    replace tyB := tyB.substitution agr.toStatic
    replace erm := ih agr
    apply Erased.conv
    . apply Static.Conv.subst _ eq
    . assumption
    . assumption

lemma Erased.subst_im {Γ} {Δ : Ctx Srt} {A B m m' n s} :
    A :: Γ ;; A :⟨.im, s⟩ Δ ⊢ m ▷ m' : B ->
    Γ ⊢ n : A ->
    Γ ;; Δ ⊢ m.[n/] ▷ m'.[.none/] : B.[n/] := by
  intro erm tyn
  obtain ⟨_, _, _⟩ := erm.ctx_inv
  apply erm.substitution
  apply AgreeSubst.wk_im
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Erased.subst_ex {Γ} {Δ1 Δ2 Δ : Ctx Srt} {A B m m' n n' s} :
    Δ2 ≤* s -> Merge Δ1 Δ2 Δ ->
    A :: Γ ;; A :⟨.ex, s⟩ Δ1 ⊢ m ▷ m' : B ->
    Γ ;; Δ2 ⊢ n ▷ n' : A ->
    Γ ;; Δ ⊢ m.[n/] ▷ m'.[n'/] : B.[n/] := by
  intro lw mrg tym tyn
  obtain ⟨_, _, _⟩ := tym.ctx_inv
  apply tym.substitution
  apply AgreeSubst.wk_ex
  . apply mrg.sym
  . assumption
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Erased.esubst_im {Γ} {Δ : Ctx Srt} {A B1 B2 m1 m2 e1 e2 n s} :
    m2 = m1.[n/] ->
    e2 = e1.[.none/] ->
    B2 = B1.[n/] ->
    A :: Γ ;; A :⟨.im, s⟩ Δ ⊢ m1 ▷ e1 : B1 ->
    Γ ⊢ n : A ->
    Γ ;; Δ ⊢ m2 ▷ e2 : B2 := by
  intros; subst_vars; apply Erased.subst_im <;> assumption

lemma Erased.esubst_ex {Γ} {Δ1 Δ2 Δ : Ctx Srt} {A B1 B2 m1 e1 m2 e2 n1 n2 s} :
    m2 = m1.[n1/] ->
    e2 = e1.[n2/] ->
    B2 = B1.[n1/] ->
    Δ2 ≤* s -> Merge Δ1 Δ2 Δ ->
    A :: Γ ;; A :⟨.ex, s⟩ Δ1 ⊢ m1 ▷ e1 : B1 ->
    Γ ;; Δ2 ⊢ n1 ▷ n2 : A ->
    Γ ;; Δ ⊢ m2 ▷ e2 : B2 := by
  intros; subst_vars; apply Erased.subst_ex <;> assumption

lemma Erased.conv_ctx {Γ} {Δ : Ctx Srt} {A B C m m' r s i} :
    B === A ->
    Γ ⊢ B : .srt s i ->
    A :: Γ ;; A :⟨r, s⟩ Δ ⊢ m ▷ m' : C ->
    B :: Γ ;; B :⟨r, s⟩ Δ ⊢ m ▷ m' : C := by
  intro eq tyB erm
  obtain ⟨_, wf, tyA⟩ := erm.ctx_inv
  replace erm : B :: Γ ;; B :⟨r, s⟩ Δ ⊢ m.[ids] ▷ m'.[ids] : C.[ids] := by
    apply erm.substitution
    apply AgreeSubst.conv <;> try assumption
    . asimp; apply tyA.weaken tyB
    . apply AgreeSubst.refl; constructor <;> assumption
  asimp at erm; assumption
