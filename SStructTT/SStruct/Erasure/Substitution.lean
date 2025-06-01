import SStructTT.SStruct.Dynamic.Substitution
import SStructTT.SStruct.Erasure.Renaming
open SStruct.Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst :
  (Var -> SStruct.Tm Srt) ->
  (Var -> Erasure.Tm Srt) ->
  Dynamic.Ctx Srt ->
  Dynamic.Ctx Srt -> Prop
where
  | nil {σ σ'} :
    AgreeSubst σ σ' [] []
  | cons {Δ Δ' : Ctx Srt} {A s i σ σ'} r :
    Δ.static ⊢ A : .srt s i ->
    AgreeSubst σ σ' Δ Δ' ->
    AgreeSubst (up σ) (up σ') (A :⟨r, s⟩ Δ) (A.[σ] :⟨r, s⟩ Δ')
  | intro_im {Δ Δ' : Ctx Srt} {A m m' s σ σ'} :
    Δ'.static ⊢ m : A.[σ] ->
    AgreeSubst σ σ' Δ Δ' ->
    AgreeSubst (m .: σ) (m' .: σ') (A :⟨.im, s⟩ Δ) Δ'
  | intro_ex {Δ Δ' Δa Δb : Ctx Srt} {A m m' s σ σ'} :
    Merge Δa Δb Δ' ->
    Lower Δa s ->
    Δa ⊢ m ▷ m' :: A.[σ] ->
    AgreeSubst σ σ' Δ Δb ->
    AgreeSubst (m .: σ) (m' .: σ') (A :⟨.ex, s⟩ Δ) Δ'
  | conv {Δ Δ' : Ctx Srt} {A B r s i σ σ'} :
    A === B ->
    Δ.static ⊢ B : .srt s i ->
    Δ'.static ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ σ' (A :⟨r, s⟩ Δ) Δ' ->
    AgreeSubst σ σ' (B :⟨r, s⟩ Δ) Δ'

lemma AgreeSubst.toDynamic {Δ Δ' : Ctx Srt} {σ σ'} :
    Erasure.AgreeSubst σ σ' Δ Δ' -> Dynamic.AgreeSubst σ Δ Δ' := by
  intro agr
  induction agr <;> try aesop (rule_sets := [subst])
  case cons => constructor <;> assumption
  case intro_im => constructor <;> assumption
  case intro_ex tym agr ih =>
    constructor <;> try assumption
    apply tym.toDynamic

lemma AgreeSubst.toStatic {Δ Δ' : Ctx Srt} {σ σ'} :
    Erasure.AgreeSubst σ σ' Δ Δ' -> Static.AgreeSubst σ Δ.static Δ'.static := by
  intro agr; apply agr.toDynamic.toStatic

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Δ : Ctx Srt} : Δ ⊢ -> AgreeSubst ids ids Δ Δ := by
  intro wf; induction wf
  all_goals try trivial
  case nil => constructor
  case cons r _ _ ty wf agr =>
    replace agr := agr.cons r ty
    asimp at agr; assumption

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.implicit_image {Δ Δ' : Ctx Srt} {σ σ'} :
    AgreeSubst σ σ' Δ Δ' -> Implicit Δ -> Implicit Δ' := by
  intro agr; apply agr.toDynamic.implicit_image

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.lower_image {Δ Δ' : Ctx Srt} {s σ σ'} :
    AgreeSubst σ σ' Δ Δ' -> Lower Δ s -> Lower Δ' s := by
  intro agr; apply agr.toDynamic.lower_image

lemma AgreeSubst.has {Δ Δ' : Ctx Srt} {A x s σ σ'} :
    AgreeSubst σ σ' Δ Δ' -> Δ' ⊢ ->
    Has Δ x s A -> Δ' ⊢ (σ x) ▷ (σ' x) :: A.[σ] := by
  intro agr wf hs; induction agr generalizing x A
  case nil => cases hs
  case cons A s i σ σ' r tyA agr ih =>
    cases r with
    | ex =>
      rcases hs with ⟨im⟩; asimp
      constructor
      . assumption
      . rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
        constructor; apply agr.implicit_image im
    | im =>
      rcases wf with _ | ⟨_, wf⟩
      rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
      rw[show A.[σ !> shift 1] = A.[σ].[shift 1] by asimp]
      apply Erased.eweaken <;> try first | rfl | assumption
      apply ih <;> assumption
  case intro_im ih =>
    rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
    apply ih <;> assumption
  case intro_ex mrg _ _ agr ih =>
    rcases hs with ⟨im⟩; asimp
    replace im := agr.implicit_image im
    rw[mrg.sym.implicit im]; assumption
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

lemma AgreeSubst.split {Δ Δ' Δa Δb : Ctx Srt} {σ σ'} :
    AgreeSubst σ σ' Δ Δ' -> Merge Δa Δb Δ ->
    ∃ Δa' Δb',
      Merge Δa' Δb' Δ' ∧
      AgreeSubst σ σ' Δa Δa' ∧
      AgreeSubst σ σ' Δb Δb' := by
  intro agr mrg; induction agr generalizing Δa Δb
  case nil =>
    cases mrg; existsi [], []
    aesop (rule_sets := [subst])
  case cons A s i σ σ' r tyA agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.ex, s⟩ Δa', A.[σ] :⟨.ex, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.static]; assumption
      rw[<-mrg.sym.static]; assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.ex, s⟩ Δa', A.[σ] :⟨.im, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.static]; assumption
      rw[<-mrg.sym.static]; assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.im, s⟩ Δa', A.[σ] :⟨.ex, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.static]; assumption
      rw[<-mrg.sym.static]; assumption
    | im _ _ mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.im, s⟩ Δa', A.[σ] :⟨.im, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.static]; assumption
      rw[<-mrg.sym.static]; assumption
  case intro_im agr ih =>
    cases mrg with
    | im _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor <;> try assumption
        rw[<-mrg.static]; assumption
      . constructor <;> try assumption
        rw[<-mrg.sym.static]; assumption
  case intro_ex mrg1 lw tym agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2
      have ⟨Δc2, mrg5, mrg6⟩ := mrg1.sym.split mrg2.sym
      existsi Δc1, Δc2; and_intros
      . apply Merge.compose <;> assumption
      . apply AgreeSubst.intro_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr1
      . apply AgreeSubst.intro_ex
        . exact mrg5.sym
        . exact lw
        . exact tym
        . exact agr2
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2
      existsi Δc1, Δb'; and_intros
      . exact mrg4
      . apply AgreeSubst.intro_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr1
      . apply AgreeSubst.intro_im
        . rw[<-mrg2.sym.static]
          rw[<-mrg1.sym.static]
          rw[mrg1.static]
          exact tym.toStatic
        . exact agr2
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2.sym
      existsi Δa', Δc1; and_intros
      . exact mrg4.sym
      . apply AgreeSubst.intro_im
        . rw[<-mrg2.static]
          rw[<-mrg1.sym.static]
          rw[mrg1.static]
          exact tym.toStatic
        . exact agr1
      . apply AgreeSubst.intro_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr2
  case conv A B r s i σ σ' eq tyB tyB' agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.contra A s h mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.static]; assumption
        rw[<-mrg'.static]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.static]; assumption
        rw[<-mrg'.sym.static]; assumption
        assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.left A s mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.static]; assumption
        rw[<-mrg'.static]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.static]; assumption
        rw[<-mrg'.sym.static]; assumption
        assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.right A s mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.static]; assumption
        rw[<-mrg'.static]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.static]; assumption
        rw[<-mrg'.sym.static]; assumption
        assumption
    | im _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.im _ _ mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.static]; assumption
        rw[<-mrg'.static]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.static]; assumption
        rw[<-mrg'.sym.static]; assumption
        assumption

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.wf {Δ Δ' : Ctx Srt} {σ σ'} :
    AgreeSubst σ σ' Δ Δ' -> Δ ⊢ -> Δ' ⊢ := by
  intro agr; apply agr.toDynamic.wf

lemma Erased.substitution {Δ Δ' : Ctx Srt} {A m m' σ σ'} :
    Δ ⊢ m ▷ m' :: A -> AgreeSubst σ σ' Δ Δ' -> Δ' ⊢ m.[σ] ▷ m'.[σ'] :: A.[σ] := by
  intro ty agr; induction ty generalizing Δ' σ σ' <;> asimp
  case var wf hs =>
    apply agr.has (agr.wf wf) hs
  case lam_im lw tyA erm ihm =>
    apply Erased.lam_im
    . apply agr.lower_image lw
    . apply tyA.substitution agr.toStatic
    . apply ihm; constructor <;> assumption
  case lam_ex A B m s sA i lw tyA erm ih =>
    apply Erased.lam_ex
    . apply agr.lower_image lw
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
  case prj_im A B C m m' n n' s sA sB sC iC mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toStatic.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons .ex tyA).cons .im tyB); asimp at ern
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Erased.prj_im <;> (asimp; assumption)
  case prj_ex C m m' n n' s sA sB sC i mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toStatic.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons .ex tyA).cons .ex tyB); asimp at ern
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Erased.prj_ex
    . assumption
    . assumption
    . assumption
    . asimp; assumption
  case tt wf im => constructor; apply agr.wf wf; apply agr.implicit_image im
  case ff wf im => constructor; apply agr.wf wf; apply agr.implicit_image im
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
  case drop mrg lw h erm ern ihm ihn =>
    have ⟨Δa', Δb', mrg', agr1, agr2⟩ := agr.split mrg
    replace ihm := ihm agr1
    replace ihn := ihn agr2
    have lw' := agr1.lower_image lw
    apply Erased.drop mrg' lw' h ihm ihn
  case conv eq erm tyB ih =>
    replace tyB := tyB.substitution agr.toStatic
    replace erm := ih agr
    apply Erased.conv
    . apply Static.Conv.subst _ eq
    . assumption
    . assumption

lemma Erased.subst_im {Δ : Ctx Srt} {A B m m' n s} :
    A :⟨.im, s⟩ Δ ⊢ m ▷ m' :: B ->
    Δ.static ⊢ n : A ->
    Δ ⊢ m.[n/] ▷ m'.[.null/] :: B.[n/] := by
  intro erm tyn
  obtain ⟨_, _, _⟩ := erm.ctx_inv
  apply erm.substitution
  apply AgreeSubst.intro_im
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Erased.subst_ex {Δ1 Δ2 Δ : Ctx Srt} {A B m m' n n' s} :
    Lower Δ2 s -> Merge Δ1 Δ2 Δ ->
    A :⟨.ex, s⟩ Δ1 ⊢ m ▷ m' :: B ->
    Δ2 ⊢ n ▷ n' :: A ->
    Δ ⊢ m.[n/] ▷ m'.[n'/] :: B.[n/] := by
  intro lw mrg tym tyn
  obtain ⟨_, _, _⟩ := tym.ctx_inv
  apply tym.substitution
  apply AgreeSubst.intro_ex
  . apply mrg.sym
  . assumption
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Erased.esubst_im {Δ : Ctx Srt} {A B1 B2 m1 m2 e1 e2 n s} :
    m2 = m1.[n/] ->
    e2 = e1.[.null/] ->
    B2 = B1.[n/] ->
    A :⟨.im, s⟩ Δ ⊢ m1 ▷ e1 :: B1 ->
    Δ.static ⊢ n : A ->
    Δ ⊢ m2 ▷ e2 :: B2 := by
  intros; subst_vars; apply Erased.subst_im <;> assumption

lemma Erased.esubst_ex {Δ1 Δ2 Δ : Ctx Srt} {A B1 B2 m1 e1 m2 e2 n1 n2 s} :
    m2 = m1.[n1/] ->
    e2 = e1.[n2/] ->
    B2 = B1.[n1/] ->
    Lower Δ2 s -> Merge Δ1 Δ2 Δ ->
    A :⟨.ex, s⟩ Δ1 ⊢ m1 ▷ e1 :: B1 ->
    Δ2 ⊢ n1 ▷ n2 :: A ->
    Δ ⊢ m2 ▷ e2 :: B2 := by
  intros; subst_vars; apply Erased.subst_ex <;> assumption

lemma Erased.conv_ctx {Δ : Ctx Srt} {A B C m m' r s i} :
    B === A ->
    Δ.static ⊢ B : .srt s i ->
    A :⟨r, s⟩ Δ ⊢ m ▷ m' :: C ->
    B :⟨r, s⟩ Δ ⊢ m ▷ m' :: C := by
  intro eq tyB erm
  obtain ⟨_, wf, tyA⟩ := erm.ctx_inv
  replace erm : B :⟨r, s⟩ Δ ⊢ m.[ids] ▷ m'.[ids] :: C.[ids] := by
    apply erm.substitution
    apply AgreeSubst.conv <;> try assumption
    . asimp; apply tyA.weaken tyB
    . apply AgreeSubst.refl; constructor <;> assumption
  asimp at erm; assumption
