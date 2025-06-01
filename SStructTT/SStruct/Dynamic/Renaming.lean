import SStructTT.SStruct.Static.Renaming
import SStructTT.SStruct.Dynamic.Typed

namespace SStruct.Dynamic
open Static
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [rename]) [constructors]]
inductive AgreeRen : (Var -> Var) -> Ctx Srt -> Ctx Srt -> Prop where
  | nil {ξ} :
    AgreeRen ξ [] []
  | cons {Δ Δ' : Ctx Srt} {A s i ξ} r :
    Δ.static ⊢ A : (.srt s i) ->
    AgreeRen ξ Δ Δ' ->
    AgreeRen (upren ξ) (A :⟨r, s⟩ Δ) (A.[ren ξ] :⟨r, s⟩ Δ')
  | intro {Δ Δ' : Ctx Srt} {A s i ξ} :
    Δ'.static ⊢ A : .srt s i ->
    AgreeRen ξ Δ Δ' ->
    AgreeRen (ξ !>> (.+1)) Δ (A :⟨.im, s⟩ Δ')

lemma AgreeRen.toStatic {Δ Δ' : Ctx Srt} {ξ} :
    Dynamic.AgreeRen ξ Δ Δ' -> Static.AgreeRen ξ Δ.static Δ'.static := by
  intro agr; induction agr <;> aesop (rule_sets := [rename])

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.refl {Δ : Ctx Srt} :
    Δ ⊢ -> AgreeRen id Δ Δ := by
  intro wf; induction wf <;> try aesop (rule_sets := [rename])
  case cons r _ _ ty _ agr =>
    replace agr := agr.cons r ty
    asimp at agr; assumption

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.implicit_image {Δ Δ' : Ctx Srt} {ξ} :
    AgreeRen ξ Δ Δ' -> Implicit Δ -> Implicit Δ' := by
  intro agr im; induction agr <;> try (solve| aesop)

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.lower_image {Δ Δ' : Ctx Srt} {ξ s} :
    AgreeRen ξ Δ Δ' -> Lower Δ s -> Lower Δ' s := by
  intro agr lw; induction agr <;> try (solve| aesop)
  cases lw <;> constructor <;> aesop

lemma AgreeRen.has {Δ Δ' : Ctx Srt} {ξ x s A} :
    AgreeRen ξ Δ Δ' -> Has Δ x s A -> Has Δ' (ξ x) s A.[ren ξ] := by
  intro agr hs
  induction agr generalizing x s A
  case nil => cases hs
  case cons A _ _ ξ r _ agr ih =>
    cases r with
    | ex =>
      rcases hs with ⟨im⟩
      have lw := agr.implicit_image im; asimp
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor; assumption
    | im =>
      rcases hs with _ | @⟨_, A, B, _, _, _, hs⟩
      specialize ih hs; asimp
      rw[show A.[ren ξ !> shift 1] = A.[ren ξ].[shift 1] by asimp]
      constructor; assumption
  case intro ξ _ _ ih =>
    specialize ih hs; asimp
    rw[show A.[ren (ξ !>> (.+1))] = A.[ren ξ].[shift 1] by asimp; rfl]
    constructor; assumption

lemma AgreeRen.wf_nil {Δ' : Ctx Srt} {ξ} : AgreeRen ξ [] Δ' -> Δ' ⊢ := by
  generalize e: [] = Δ
  intro agr; induction agr <;> try trivial
  case nil => constructor
  case intro => subst_vars; aesop (add safe Wf)

lemma AgreeRen.wf_cons {Δ Δ' : Ctx Srt} {A r s ξ} :
    AgreeRen ξ (A :⟨r, s⟩ Δ) Δ' -> Δ ⊢ ->
    (∀ {Δ' ξ}, AgreeRen ξ Δ Δ' → Δ' ⊢) -> Δ' ⊢ := by
  generalize e: A :⟨r, s⟩ Δ = Δ0
  intro agr wf h; induction agr generalizing Δ A r s <;> try trivial
  case cons ξ tyA agr ih =>
    cases e
    constructor
    . apply tyA.renaming agr.toStatic
    . apply h agr
  case intro _ ih =>
    cases e
    specialize ih rfl wf h
    constructor <;> aesop

@[aesop safe (rule_sets := [rename])]
lemma AgreeRen.wf {Δ Δ' : Ctx Srt} {ξ} :
    AgreeRen ξ Δ Δ' -> Δ ⊢ -> Δ' ⊢ := by
  intro agr wf; induction wf generalizing Δ' ξ <;> try aesop
  case nil => apply agr.wf_nil
  case cons ih => apply agr.wf_cons <;> aesop

lemma AgreeRen.split {Δ Δ' Δ1 Δ2 : Ctx Srt} {ξ} :
    AgreeRen ξ Δ Δ' -> Merge Δ1 Δ2 Δ ->
    ∃ Δ1' Δ2',
      Merge Δ1' Δ2' Δ' ∧
      AgreeRen ξ Δ1 Δ1' ∧
      AgreeRen ξ Δ2 Δ2' := by
  intro agr mrg; induction agr generalizing Δ1 Δ2
  case nil =>
    cases mrg
    existsi [], []
    aesop (rule_sets := [rename])
  case cons Δ Δ' A s i ξ r ty agr ih =>
    cases mrg with
    | contra Δ1 Δ2 h mrg =>
      have ⟨Δ1', Δ2', _, agr1, agr2⟩ := ih mrg
      existsi A.[ren ξ] :⟨.ex, s⟩ Δ1', A.[ren ξ] :⟨.ex, s⟩ Δ2'
      and_intros
      . constructor <;> assumption
      . constructor <;> try assumption
        rw[<-mrg.static]; assumption
      . constructor <;> try assumption
        rw[<-mrg.sym.static]; assumption
    | @left Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', _, agr1, agr2⟩ := ih mrg
      existsi A.[ren ξ] :⟨.ex, s⟩ Δ1', A.[ren ξ] :⟨.im, s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> try assumption
        rw[<-mrg.static]; assumption
      . constructor <;> try assumption
        rw[<-mrg.sym.static]; assumption
    | @right Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', _, agr1, agr2⟩ := ih mrg
      existsi A.[ren ξ] :⟨.im, s⟩ Δ1', A.[ren ξ] :⟨.ex, s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> try assumption
        rw[<-mrg.static]; assumption
      . constructor <;> try assumption
        rw[<-mrg.sym.static]; assumption
    | @im Δ1 Δ2 _ _ _ mrg =>
      have ⟨Δ1', Δ2', _, agr1, agr2⟩ := ih mrg
      existsi A.[ren ξ] :⟨.im, s⟩ Δ1', A.[ren ξ] :⟨.im, s⟩ Δ2'
      and_intros
      . constructor; assumption
      . constructor <;> try assumption
        rw[<-mrg.static]; assumption
      . constructor <;> try assumption
        rw[<-mrg.sym.static]; assumption
  case intro Δ Δ' A s i ξ ty agr ih =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := ih mrg
    existsi A :⟨.im, s⟩ Δ1', A :⟨.im, s⟩ Δ2'
    and_intros
    . constructor; assumption
    . constructor <;> try assumption
      rw[<-mrg.static]; assumption
    . constructor <;> try assumption
      rw[<-mrg.sym.static]; assumption

lemma Typed.renaming {Δ Δ' : Ctx Srt} {A m ξ} :
    Δ ⊢ m :: A -> AgreeRen ξ Δ Δ' -> Δ' ⊢ m.[ren ξ] :: A.[ren ξ] := by
  intro ty agr; induction ty using
    @Typed.rec _ ord
      (motive_2 := fun Δ _ => ∀ {Δ' ξ}, AgreeRen ξ Δ Δ' -> Δ' ⊢)
  generalizing Δ' ξ <;> asimp
  case var h _ =>
    constructor <;> try aesop
    apply agr.has h
  case lam_im Δ A B m s sA i lw tyA tym ih =>
    constructor
    . apply agr.lower_image lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.cons .im tyA)
      asimp at ih; assumption
  case lam_ex Δ A B m s sA i lw tyA tym ih =>
    constructor
    . apply agr.lower_image lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.cons .ex tyA)
      asimp at ih; assumption
  case app_im Δ A B m n s tym tyn ih =>
    replace tym := ih agr; asimp at tym
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    have ty := Typed.app_im tym tyn
    asimp at ty; assumption
  case app_ex Δ1 Δ2 Δ A B m n s mrg tym tyn ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn agr2; asimp at tyn
    have ty := Typed.app_ex mrg tym tyn
    asimp at ty; assumption
  case tup_im tyS tym tyn ih =>
    replace tym := tym.renaming agr.toStatic; asimp at tym
    replace tyn := ih agr; asimp at tyn
    replace tyS := tyS.renaming agr.toStatic; asimp at tyS
    constructor <;> (asimp; assumption)
  case tup_ex mrg tyS tym tyn ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn agr2; asimp at tyn
    replace tyS := tyS.renaming agr.toStatic; asimp at tyS
    constructor <;> (asimp; assumption)
  case prj_im A B C m n s sA sB sC iC mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := tyn.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.renaming (agr.toStatic.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons .im tyA).cons .ex tyB)
    rw[show C.[.tup (.var 1) (.var 0) .im s .: shift 2].[ren (upren (upren ξ))]
          = C.[up (ren ξ)].[.tup (.var 1) (.var 0) .im s .: shift 2]
        by asimp] at tyn
    rw[SubstLemmas.upren_up] at tyn
    have ty := Typed.prj_im mrg tyC tym tyn
    asimp at ty; assumption
  case prj_ex A B C m n s sA sB sC iC mrg tyC tym tyn ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := tyn.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.renaming (agr.toStatic.cons tyS); asimp at tyC
    replace tym := ihm agr1; asimp at tym
    replace tyn := ihn ((agr2.cons .ex tyA).cons .ex tyB)
    rw[show C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[ren (upren (upren ξ))]
          = C.[up (ren ξ)].[.tup (.var 1) (.var 0) .ex s .: shift 2]
        by asimp] at tyn
    rw[SubstLemmas.upren_up] at tyn
    have ty := Typed.prj_ex mrg tyC tym tyn
    asimp at ty; assumption
  case tt im ih =>
    constructor
    aesop (rule_sets := [rename])
    apply agr.implicit_image im
  case ff im ih =>
    constructor
    aesop (rule_sets := [rename])
    apply agr.implicit_image im
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
  case drop mrg lw h _ ihn =>
    have ⟨Δ1', Δ2', mrg', agr1, agr2⟩ := agr.split mrg
    replace ihn := ihn agr2
    replace lw :=  agr1.lower_image lw
    apply Typed.drop mrg' lw h ihn
  case conv eq tym tyB ih =>
    replace tyB := tyB.renaming agr.toStatic
    replace tym := ih agr
    apply Typed.conv
    . apply Conv.subst _ eq
    . assumption
    . assumption
  case nil agr => apply agr.wf_nil
  case cons agr => apply agr.wf_cons <;> aesop

lemma Typed.weaken_im {Δ : Ctx Srt} {A B m s i} :
    Δ ⊢ m :: A ->
    Δ.static ⊢ B : .srt s i ->
    B :⟨.im, s⟩ Δ ⊢ m.[shift 1] :: A.[shift 1] := by
  intro tym tyB
  apply tym.renaming
  constructor
  . assumption
  . exact AgreeRen.refl tym.toWf

lemma Typed.weaken_ex {Δ : Ctx Srt} {A B m s i} :
    Δ ⊢ m :: A ->
    Δ.static ⊢ B : .srt s i ->
    s ∈ ord.weaken_set ->
    B :⟨.ex, s⟩ Δ ⊢ m.[shift 1] :: A.[shift 1] := by
  intro tym tyB h
  have mrg : Merge (B :⟨.im, s⟩ Δ) (B :⟨.ex, s⟩ Δ.toImplicit) (B :⟨.ex, s⟩ Δ) := by
    constructor; apply Merge.self
  replace tym := tym.weaken_im tyB
  have ⟨i, wf, tyB⟩ := tym.ctx_inv
  apply Typed.drop mrg.sym _ h
  . assumption
  . constructor; simp; apply Lower.implicit (Implicit.toImplicit _)

lemma Typed.eweaken_im {Δ Δ' : Ctx Srt} {A A' B m m' s i} :
    Δ' = B :⟨.im, s⟩ Δ ->
    m' = m.[shift 1] ->
    A' = A.[shift 1] ->
    Δ ⊢ m :: A ->
    Δ.static ⊢ B : .srt s i ->
    Δ' ⊢ m' :: A' := by
  intros; subst_vars
  apply Typed.weaken_im <;> assumption

lemma Typed.eweaken_ex {Δ Δ' : Ctx Srt} {A A' B m m' s i} :
    Δ' = B :⟨.ex, s⟩ Δ ->
    m' = m.[shift 1] ->
    A' = A.[shift 1] ->
    Δ ⊢ m :: A ->
    Δ.static ⊢ B : .srt s i ->
    s ∈ ord.weaken_set ->
    Δ' ⊢ m' :: A' := by
  intros; subst_vars
  apply Typed.weaken_ex <;> assumption

inductive Spine (Δ0 : Ctx Srt) : Ctx Srt -> Prop where
  | refl : Spine Δ0 Δ0
  | cons {Δ1 Δ2 Δ3 x s A} :
    Merge Δ1 Δ2 Δ3 ->
    s ∈ ord.weaken_set ->
    Has Δ2 x s A ->
    Spine Δ0 Δ1 ->
    Spine Δ0 Δ3

lemma Spine.extend {Δ1 Δ2 : Ctx Srt} {A r s} :
    Spine Δ1 Δ2 -> Spine (A :⟨r, s⟩ Δ1) (A :⟨r, s⟩ Δ2) := by
  intro sp; induction sp
  case refl => constructor
  case cons Δ1 Δ2 Δ3 x _ _ mrg h hs sp ih =>
    replace mrg : Merge (A :⟨r, s⟩ Δ1) (A :⟨.im, s⟩ Δ2) (A :⟨r, s⟩ Δ3) := by
      cases r
      . constructor; assumption
      . constructor; assumption
    constructor
    . apply mrg
    . assumption
    . constructor
      assumption
    . assumption

lemma Merge.toSpine {Δ1 Δ2 Δ3 : Ctx Srt} {s} :
    Merge Δ1 Δ2 Δ3 -> Lower Δ2 s -> s ∈ ord.weaken_set -> Spine Δ1 Δ3 := by
  intro mrg lw h; induction mrg
  case nil => constructor
  case contra ih =>
    cases lw; case ex lw =>
    apply (ih lw).extend
  case left ih =>
    cases lw; case im lw =>
    apply (ih lw).extend
  case right Δ1 Δ2 Δ3 A s mrg ih =>
    cases lw; case ex le lw =>
    have sp := @Spine.extend _ _ _ _ A .im s (ih lw)
    replace mrg : Merge (A :⟨.im, s⟩ Δ3) (A :⟨.ex, s⟩ Δ3.toImplicit) (A :⟨.ex, s⟩ Δ3) := by
      constructor
      apply Merge.self
    have hs : Has (A :⟨.ex, s⟩ Δ3.toImplicit) 0 s A.[shift 1] := by
      constructor; apply Implicit.toImplicit
    constructor
    . apply mrg
    . apply ord.weaken_set.lower le
      assumption
    . apply hs
    . apply (ih lw).extend
  case im ih =>
    cases lw; case im lw =>
    apply (ih lw).extend

lemma Typed.drop_spine {Δ1 Δ3 : Ctx Srt} {A m} :
    Spine Δ1 Δ3 ->
    Δ1 ⊢ m :: A ->
    Δ3 ⊢ m :: A := by
  intro sp tym; induction sp
  case refl => assumption
  case cons Δ1 Δ2 Δ3 x s A mrg h hs sp ih =>
    have ⟨wf1, wf2⟩ := ih.toWf.merge mrg
    have ⟨i, tyA⟩ := wf1.has_typed hs
    have tyn : Δ2 ⊢ .var x :: A := by
      constructor <;> assumption
    apply Typed.drop mrg.sym
    . apply hs.lower
    . apply h
    . assumption
