import SStructTT.SStruct.Logical.Substitution
import SStructTT.SStruct.Program.Renaming
open SStruct.Logical

namespace SStruct.Program
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst : (Var -> Tm Srt) -> Ctx Srt -> Ctx Srt -> Prop where
  | nil {σ} :
    AgreeSubst σ [] []
  | cons {Δ Δ' : Ctx Srt} {A s i σ} r :
    Δ.logical ⊢ A : .srt s i ->
    AgreeSubst σ Δ Δ' ->
    AgreeSubst (up σ) (A :⟨r, s⟩ Δ) (A.[σ] :⟨r, s⟩ Δ')
  | intro_im {Δ Δ' : Ctx Srt} {A m s σ} :
    Δ'.logical ⊢ m : A.[σ] ->
    AgreeSubst σ Δ Δ' ->
    AgreeSubst (m .: σ) (A :⟨.im, s⟩ Δ) Δ'
  | intro_ex {Δ Δ' : Ctx Srt} {Δa Δb A m s σ} :
    Merge Δa Δb Δ' ->
    Lower Δa s ->
    Δa ⊢ m :: A.[σ] ->
    AgreeSubst σ Δ Δb ->
    AgreeSubst (m .: σ) (A :⟨.ex, s⟩ Δ) Δ'
  | conv {Δ Δ' : Ctx Srt} {A B r s i σ} :
    A === B ->
    Δ.logical ⊢ B : .srt s i ->
    Δ'.logical ⊢ B.[shift 1].[σ] : .srt s i ->
    AgreeSubst σ (A :⟨r, s⟩ Δ) Δ' ->
    AgreeSubst σ (B :⟨r, s⟩ Δ) Δ'

lemma AgreeSubst.toLogical {Δ Δ' : Ctx Srt} {σ} :
    Program.AgreeSubst σ Δ Δ' -> Logical.AgreeSubst σ Δ.logical Δ'.logical := by
  intro agr
  induction agr
  case nil => simp; constructor
  case cons => constructor <;> assumption
  case intro_im => constructor <;> assumption
  case intro_ex mrg _ tym agr ih =>
    constructor
    . rw[mrg.logical]; apply tym.toLogical
    . rw[mrg.sym.logical]; assumption
  case conv => aesop (rule_sets := [subst])

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.refl {Δ : Ctx Srt} : Δ ⊢ -> AgreeSubst ids Δ Δ := by
  intro wf; induction wf
  all_goals try trivial
  case nil => constructor
  case cons r _ _ ty wf agr =>
    replace agr := agr.cons r ty
    asimp at agr; assumption

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.implicit_image {Δ Δ' : Ctx Srt} {σ} :
    AgreeSubst σ Δ Δ' -> Implicit Δ -> Implicit Δ' := by
  intro agr im; induction agr
  all_goals try aesop

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.lower_image {Δ Δ' : Ctx Srt} {s σ} :
    AgreeSubst σ Δ Δ' -> Lower Δ s -> Lower Δ' s := by
  intro agr lw; induction agr generalizing s
  case nil => assumption
  case cons =>
    cases lw <;> constructor <;> aesop
  case intro_im => cases lw; aesop
  case intro_ex mrg _ _ _ _ =>
    cases lw
    apply mrg.lower_image
    . apply Lower.trans <;> assumption
    . aesop
  case conv ih => cases lw <;> aesop

lemma AgreeSubst.has {Δ Δ' : Ctx Srt} {A x s σ} :
    AgreeSubst σ Δ Δ' -> Δ' ⊢ -> Has Δ x s A -> Δ' ⊢ (σ x) :: A.[σ] := by
  intro agr wf hs; induction agr generalizing x A
  case nil => cases hs
  case cons A s i σ r tyA agr ih =>
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
      apply Typed.eweaken_im <;> try first | rfl | assumption
      apply ih <;> assumption
  case intro_im ih =>
    rcases hs with _ | @⟨_, A, x, s, hs⟩; asimp
    apply ih <;> assumption
  case intro_ex mrg lw tym agr ih =>
    rcases hs with ⟨im⟩; asimp
    replace im := agr.implicit_image im
    rw[mrg.sym.implicit im]; assumption
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

lemma AgreeSubst.split {Δ Δ' Δa Δb : Ctx Srt} {σ} :
    AgreeSubst σ Δ Δ' -> Merge Δa Δb Δ ->
    ∃ Δa' Δb',
      Merge Δa' Δb' Δ' ∧
      AgreeSubst σ Δa Δa' ∧
      AgreeSubst σ Δb Δb' := by
  intro agr mrg; induction agr generalizing Δa Δb
  case nil =>
    cases mrg; existsi [], []
    aesop (rule_sets := [subst])
  case cons A s i σ r tyA agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.ex, s⟩ Δa', A.[σ] :⟨.ex, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.logical]; assumption
      rw[<-mrg.sym.logical]; assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.ex, s⟩ Δa', A.[σ] :⟨.im, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.logical]; assumption
      rw[<-mrg.sym.logical]; assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.im, s⟩ Δa', A.[σ] :⟨.ex, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.logical]; assumption
      rw[<-mrg.sym.logical]; assumption
    | im _ _ mrg =>
      have ⟨Δa', Δb', _, agr1, agr2⟩ := ih mrg
      existsi A.[σ] :⟨.im, s⟩ Δa', A.[σ] :⟨.im, s⟩ Δb'; and_intros
      all_goals constructor <;> try assumption
      rw[<-mrg.logical]; assumption
      rw[<-mrg.sym.logical]; assumption
  case intro_im agr ih =>
    cases mrg with
    | im _ _ mrg =>
      have ⟨Δa', Δb', mrg, agr1, agr2⟩ := ih mrg
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor <;> try assumption
        rw[<-mrg.logical]; assumption
      . constructor <;> try assumption
        rw[<-mrg.sym.logical]; assumption
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
        . rw[<-mrg2.sym.logical]
          rw[<-mrg1.sym.logical]
          rw[mrg1.logical]
          exact tym.toLogical
        . exact agr2
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg2, agr1, agr2⟩ := ih mrg
      have ⟨Δc1, mrg3, mrg4⟩ := mrg1.sym.split mrg2.sym
      existsi Δa', Δc1; and_intros
      . exact mrg4.sym
      . apply AgreeSubst.intro_im
        . rw[<-mrg2.logical]
          rw[<-mrg1.sym.logical]
          rw[mrg1.logical]
          exact tym.toLogical
        . exact agr1
      . apply AgreeSubst.intro_ex
        . exact mrg3.sym
        . exact lw
        . exact tym
        . exact agr2
  case conv A B r s i σ eq tyB tyB' agr ih =>
    cases mrg with
    | contra _ _ h mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.contra A s h mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.logical]; assumption
        rw[<-mrg'.logical]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.logical]; assumption
        rw[<-mrg'.sym.logical]; assumption
        assumption
    | left _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.left A s mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.logical]; assumption
        rw[<-mrg'.logical]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.logical]; assumption
        rw[<-mrg'.sym.logical]; assumption
        assumption
    | right _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.right A s mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.logical]; assumption
        rw[<-mrg'.logical]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.logical]; assumption
        rw[<-mrg'.sym.logical]; assumption
        assumption
    | im _ _ mrg =>
      have ⟨Δa', Δb', mrg', agr1, agr2⟩ := ih (Merge.im _ _ mrg)
      existsi Δa', Δb'; and_intros
      . assumption
      . constructor
        assumption
        rw[<-mrg.logical]; assumption
        rw[<-mrg'.logical]; assumption
        assumption
      . constructor
        assumption
        rw[<-mrg.sym.logical]; assumption
        rw[<-mrg'.sym.logical]; assumption
        assumption

lemma AgreeSubst.wf_nil {Δ' : Ctx Srt} {σ} :
    AgreeSubst σ [] Δ' -> Δ' ⊢ := by
  generalize e: [] = Δ
  intro agr; induction agr <;> try trivial
  constructor

lemma AgreeSubst.wf_cons {Δ Δ' : Ctx Srt} {A r s σ} :
    AgreeSubst σ (A :⟨r, s⟩ Δ) Δ' -> Δ ⊢ ->
    (∀ {Δ' σ}, AgreeSubst σ Δ Δ' → Δ' ⊢) -> Δ' ⊢ := by
  generalize e: A :⟨r, s⟩ Δ = Δ0
  intro agr wf h; induction agr generalizing Δ A r s <;> try trivial
  case cons tyA agr ih =>
    cases e
    constructor
    . apply tyA.substitution agr.toLogical
    . apply h agr
  case intro_im agr _ =>
    cases e; apply h agr
  case intro_ex mrg lw tym agr ih =>
    cases e; apply (Wf.merge mrg tym.toWf).right
  case conv ih =>
    cases e; apply ih rfl wf h

@[aesop safe (rule_sets := [subst])]
lemma AgreeSubst.wf {Δ Δ' : Ctx Srt} {σ} :
    AgreeSubst σ Δ Δ' -> Δ ⊢ -> Δ' ⊢ := by
  intro agr wf; induction wf generalizing Δ' σ
  all_goals try aesop
  case nil => apply agr.wf_nil
  case cons => apply agr.wf_cons <;> aesop

lemma Typed.substitution {Δ Δ' : Ctx Srt} {A m σ} :
    Δ ⊢ m :: A -> AgreeSubst σ Δ Δ' -> Δ' ⊢ m.[σ] :: A.[σ] := by
  intro ty agr; induction ty using
    @Typed.rec _ ord
      (motive_2 := fun Δ _ => ∀ {Δ' σ}, AgreeSubst σ Δ Δ' -> Δ' ⊢)
  generalizing Δ' σ <;> asimp
  case var wf hs ih => apply agr.has (ih agr) hs
  case lam_im lw tyA tym ih =>
    apply Typed.lam_im
    . apply agr.lower_image lw
    . apply tyA.substitution agr.toLogical
    . apply ih; constructor <;> assumption
  case lam_ex A B m s sA i lw tyA tym ih =>
    apply Typed.lam_ex
    . apply agr.lower_image lw
    . apply tyA.substitution agr.toLogical
    . apply ih; constructor <;> assumption
  case app_im tym tyn ih =>
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.substitution agr.toLogical
    have ty := Typed.app_im tym tyn
    asimp at ty; assumption
  case app_ex mrg tym tyn ihm ihn =>
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn agr2
    have ty := Typed.app_ex mrg ihm ihn
    asimp at ty; assumption
  case tup_im B m n s i tyS tym tyn ihm =>
    replace tyS := tyS.substitution agr.toLogical; asimp at tyS
    replace tym := tym.substitution agr.toLogical; asimp at tym
    replace tyn := ihm agr; asimp at tyn
    rw[show B.[m.[σ] .: σ] = B.[up σ].[m.[σ]/] by asimp] at tyn
    have ty := Typed.tup_im tyS tym tyn; assumption
  case tup_ex B m n s i mrg tyS tym tyn ihm ihn =>
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyS := tyS.substitution agr.toLogical; asimp at tyS
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn agr2; asimp at tyn
    rw[show B.[m.[σ] .: σ] = B.[up σ].[m.[σ]/] by asimp] at tyn
    have ty := Typed.tup_ex mrg tyS tym tyn; assumption
  case prj_im A B C m n s sA sB sC iC mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := tyn.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toLogical.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons .im tyA).cons .ex tyB); asimp at tyn
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Typed.prj_im <;> (asimp; assumption)
  case prj_ex C m n s sA sB sC i mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := tyn.ctx_inv
    have ⟨Δa, Δb, mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.substitution (agr.toLogical.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons .ex tyA).cons .ex tyB); asimp at tyn
    rw[show C.[m.[σ] .: σ] = C.[up σ].[m.[σ]/] by asimp]
    apply Typed.prj_ex <;> (asimp; assumption)
  case tt im ih =>
    constructor
    apply ih <;> try assumption
    apply agr.implicit_image im
  case ff im ih =>
    constructor
    apply ih <;> try assumption
    apply agr.implicit_image im
  case ite A m n1 n2 s i mrg tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    have ⟨s, i, _, tyb⟩ := tyA.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn1 agr2; asimp at ihn1
    specialize ihn2 agr2; asimp at ihn2
    replace tyA := tyA.substitution (agr.toLogical.cons tyb); asimp at tyA
    rw[show A.[.tt .: σ] = A.[up σ].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: σ] = A.[up σ].[.ff/] by asimp] at ihn2
    have ty := Typed.ite mrg tyA ihm ihn1 ihn2; asimp at ty
    assumption
  case rw A B m n a b s i tyA tym tyn ih =>
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace tyA := tyA.substitution ((agr.toLogical.cons tyB).cons tyI); asimp at tyA
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.substitution agr.toLogical; asimp at tyn
    simp[<-SubstLemmas.subst_comp] at tyA
    rw[show A.[a.[σ].rfl .: a.[σ] .: σ]
          = A.[upn 2 σ].[.rfl a.[σ],a.[σ]/]
         by asimp] at tym
    have := Typed.rw tyA tym tyn
    asimp at this; assumption
  case drop Δ1 Δ2 Δ3 n s i mrg lw h tyn ihn =>
    have ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := agr.split mrg
    replace lw := agr1.lower_image lw
    specialize ihn agr2
    apply Typed.drop mrg' lw h ihn
  case conv eq tym tyB ih =>
    replace tyB := tyB.substitution agr.toLogical
    replace tym := ih agr
    apply Typed.conv
    . apply Conv.subst _ eq
    . assumption
    . assumption
  case nil agr => apply agr.wf_nil
  case cons agr => apply agr.wf_cons <;> aesop

lemma Typed.subst_im {Δ : Ctx Srt} {A B m n s} :
    A :⟨.im, s⟩ Δ ⊢ m :: B -> Δ.logical ⊢ n : A -> Δ ⊢ m.[n/] :: B.[n/] := by
  intro tym tyn
  obtain ⟨_, _, _⟩ := tym.ctx_inv
  apply tym.substitution
  apply AgreeSubst.intro_im
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Typed.subst_ex {Δ1 Δ2 Δ : Ctx Srt} {A B m n s} :
    Lower Δ2 s -> Merge Δ1 Δ2 Δ ->
    A :⟨.ex, s⟩ Δ1 ⊢ m :: B -> Δ2 ⊢ n :: A -> Δ ⊢ m.[n/] :: B.[n/] := by
  intro lw mrg tym tyn
  obtain ⟨_, _, _⟩ := tym.ctx_inv
  apply tym.substitution
  apply AgreeSubst.intro_ex
  . apply mrg.sym
  . assumption
  . asimp; assumption
  . apply AgreeSubst.refl; assumption

lemma Typed.esubst_im {Δ : Ctx Srt} {A B B' m m' n s} :
    m' = m.[n/] ->
    B' = B.[n/] ->
    A :⟨.im, s⟩ Δ ⊢ m :: B ->
    Δ.logical ⊢ n : A ->
    Δ ⊢ m' :: B' := by
  intros; subst_vars; apply Typed.subst_im <;> assumption

lemma Typed.esubst_ex {Δ1 Δ2 Δ : Ctx Srt} {A B B' m m' n s} :
    m' = m.[n/] ->
    B' = B.[n/] ->
    Lower Δ2 s -> Merge Δ1 Δ2 Δ ->
    A :⟨.ex, s⟩ Δ1 ⊢ m :: B -> Δ2 ⊢ n :: A -> Δ ⊢ m' :: B' := by
  intros; subst_vars; apply Typed.subst_ex <;> assumption

lemma Typed.conv_ctx {Δ : Ctx Srt} {A B C m r s i} :
    B === A ->
    Δ.logical ⊢ B : .srt s i ->
    A :⟨r, s⟩ Δ ⊢ m :: C ->
    B :⟨r, s⟩ Δ ⊢ m :: C := by
  intro eq tyB tym
  obtain ⟨_, wf, tyA⟩ := tym.ctx_inv
  replace tym : B :⟨r, s⟩ Δ ⊢ m.[ids] :: C.[ids] := by
    apply tym.substitution
    apply AgreeSubst.conv <;> try assumption
    . asimp; apply tyA.weaken tyB
    . apply AgreeSubst.refl; constructor <;> assumption
  asimp at tym; assumption
