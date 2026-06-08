import SStructTT.SStruct.Program.Renaming
import SStructTT.SStruct.Extraction.Extract
open SStruct.Program
open Autosubst Autosubst.Notation

namespace SStruct.Extraction
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Extract.renaming {Δ Δ' : Ctx Srt} {A m m' ξ} :
    Δ ⊢ m ▷ m' :: A -> AgreeRen ξ Δ Δ' ->
    Δ' ⊢ m⟨ξ⟩ ▷ m'⟨ξ⟩ :: A⟨ξ⟩ := by
  intro er agr; induction er generalizing Δ' ξ <;> (try asimp)
  case var wf h =>
    constructor <;> try aesop
    . apply agr.wf wf
    . apply agr.has h
  case lam_im Δ A B m m' s sA i lw tyA erm ih =>
    constructor
    . apply agr.lower_image lw
    . apply tyA.renaming agr.toLogical
    . specialize ih (agr.cons .im tyA)
      asimp at ih; assumption
  case lam_ex Δ A B m m' s sA i lw tyA erm ih =>
    constructor
    . apply agr.lower_image lw
    . apply tyA.renaming agr.toLogical
    . specialize ih (agr.cons .ex tyA)
      asimp at ih; assumption
  case app_im Δ A B m m' n s erm tyn ihm =>
    replace erm := ihm agr; asimp at erm
    replace tyn := tyn.renaming agr.toLogical; asimp at tyn
    have er := Extract.app_im erm tyn
    asimp at er; assumption
  case app_ex Δ1 Δ2 Δ A B m m' n n' s mrg erm ern ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn agr2; asimp at ern
    have er := Extract.app_ex mrg erm ern
    asimp at er; assumption
  case tup_im tyS tym ern ih =>
    replace tym := tym.renaming agr.toLogical; asimp at tym
    replace ern := ih agr; asimp at ern
    replace tyS := tyS.renaming agr.toLogical; asimp at tyS
    constructor <;> (first | assumption | (asimp; assumption))
  case tup_ex mrg tyS erm ern ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn agr2; asimp at ern
    replace tyS := tyS.renaming agr.toLogical; asimp at tyS
    constructor <;> (first | assumption | (asimp; assumption))
  case prj_im A B C m m' n n' s sA sB sC iC mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.renaming (agr.toLogical.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons .im tyA).cons .ex tyB)
    rw[show C[.tup (.var 1) (.var 0) .im s .: shift >> shift >> SStruct.Tm.var_Tm]⟨up_ren (up_ren ξ)⟩
          = (C⟨up_ren ξ⟩)[.tup (.var 1) (.var 0) .im s .: shift >> shift >> SStruct.Tm.var_Tm] by asimp] at ern
    have er := Extract.prj_im mrg tyC erm ern
    asimp at er; assumption
  case prj_ex A B C m m' n n' s sA sB sC iC mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.renaming (agr.toLogical.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons .ex tyA).cons .ex tyB)
    rw[show C[.tup (.var 1) (.var 0) .ex s .: shift >> shift >> SStruct.Tm.var_Tm]⟨up_ren (up_ren ξ)⟩
          = (C⟨up_ren ξ⟩)[.tup (.var 1) (.var 0) .ex s .: shift >> shift >> SStruct.Tm.var_Tm] by asimp] at ern
    have er := Extract.prj_ex mrg tyC erm ern
    asimp at er; assumption
  case tt im =>
    constructor
    aesop (rule_sets := [rename])
    apply agr.implicit_image im
  case ff im =>
    constructor
    aesop (rule_sets := [rename])
    apply agr.implicit_image im
  case ite A _ _ _ _ _ _ _ _  mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    have ⟨s, i, _, tyb⟩ := tyA.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn1 agr2; asimp at ihn1
    specialize ihn2 agr2; asimp at ihn2
    replace tyA := tyA.renaming (agr.toLogical.cons tyb); asimp at tyA
    rw[show A[(SStruct.Tm.tt : SStruct.Tm Srt) .: ξ >> SStruct.Tm.var_Tm] = (A⟨up_ren ξ⟩)[(SStruct.Tm.tt : SStruct.Tm Srt)/] by asimp] at ihn1
    rw[show A[(SStruct.Tm.ff : SStruct.Tm Srt) .: ξ >> SStruct.Tm.var_Tm] = (A⟨up_ren ξ⟩)[(SStruct.Tm.ff : SStruct.Tm Srt)/] by asimp] at ihn2
    have ty := Extract.ite mrg tyA ihm ihn1 ihn2; asimp at ty
    assumption
  case rw A B m m' n a b s i tyA erm tyn ih =>
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace tyA := tyA.renaming ((agr.toLogical.cons tyB).cons tyI)
    rw[show (SStruct.Tm.idn B⟨↑⟩ a⟨↑⟩ (SStruct.Tm.var_Tm 0))⟨up_ren ξ⟩
          = SStruct.Tm.idn ((B⟨ξ⟩)⟨↑⟩) ((a⟨ξ⟩)⟨↑⟩) (SStruct.Tm.var_Tm 0) by asimp] at tyA
    replace erm := ih agr; asimp at erm
    replace tyn := tyn.renaming agr.toLogical; asimp at tyn
    rw[show A[a⟨ξ⟩.rfl .: a⟨ξ⟩ .: ξ >> SStruct.Tm.var_Tm]
          = (A⟨up_ren (up_ren ξ)⟩)[a⟨ξ⟩.rfl, a⟨ξ⟩/] by asimp] at erm
    have := Extract.rw tyA erm tyn
    asimp at this; assumption
  case exf Δ A m s i wf im tyA tym =>
    have tyBot := Logical.Typed.bot wf.toLogical
    replace tyA := tyA.renaming (agr.toLogical.cons tyBot); asimp at tyA
    replace tym := tym.renaming agr.toLogical; asimp at tym
    have wf' := agr.wf wf
    have im' := agr.implicit_image im
    have er := Extract.exf wf' im' tyA tym
    asimp at er; assumption
  case exf_drop Δ1 Δ2 Δ3 A0 m0 n0 B0 s0 i0 n0' b0' mrg tyA tym ern erb ihn ihb =>
    have wf3 := (Wf.merge mrg ern.toWf).right
    have tyBot := Logical.Typed.bot wf3.toLogical
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyA := tyA.renaming (agr.toLogical.cons tyBot); asimp at tyA
    replace tym := tym.renaming agr.toLogical; asimp at tym
    replace ern := ihn agr1; asimp at ern
    replace erb := ihb agr2; asimp at erb
    rw[show A0[m0⟨ξ⟩ .: ξ >> SStruct.Tm.var_Tm] = (A0⟨up_ren ξ⟩)[m0⟨ξ⟩/] by asimp] at erb
    have er := Extract.exf_drop mrg tyA tym ern erb
    asimp at er; assumption
  case drop mrg lw h erm ern ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn agr2; asimp at ern
    have lw' := agr1.lower_image lw
    apply Extract.drop mrg lw' h erm ern
  case conv eq erm tyB ih =>
    replace tyB := tyB.renaming agr.toLogical
    replace erm := ih agr
    apply Extract.conv
    . apply Logical.Conv.ren _ eq
    . assumption
    . assumption

lemma Extract.weaken_im {Δ : Program.Ctx Srt} {A B m m' s i} :
    Δ ⊢ m ▷ m' :: A ->
    Δ.logical ⊢ B : .srt s i ->
    B :⟨.im, s⟩ Δ ⊢ m⟨↑⟩ ▷ m'⟨↑⟩ :: A⟨↑⟩ := by
  intro erm tyB
  apply erm.renaming
  constructor
  . assumption
  . exact AgreeRen.refl erm.toWf

lemma Extract.weaken_ex {Δ : Program.Ctx Srt} {A B m m' s i} :
    Δ ⊢ m ▷ m' :: A ->
    Δ.logical ⊢ B : .srt s i ->
    s ∈ ord.weaken_set ->
    B :⟨.ex, s⟩ Δ ⊢ m⟨↑⟩ ▷ .drop (.var 0) m'⟨↑⟩ :: A⟨↑⟩ := by
  intro erm tyB h
  have mrg : Merge (B :⟨.im, s⟩ Δ) (B :⟨.ex, s⟩ Δ.toImplicit) (B :⟨.ex, s⟩ Δ) := by
    constructor; apply Merge.self
  replace erm := erm.weaken_im tyB
  have ⟨i, wf, tyB⟩ := erm.ctx_inv
  apply Extract.drop
  . apply mrg.sym
  . constructor
    apply ord.le_refl
    apply Lower.implicit
    apply Implicit.toImplicit
  . apply h
  . apply Extract.var
    constructor
    . rw[Implicit.logical]; assumption
    . apply wf.implicit
    . constructor
      apply Implicit.toImplicit
  . apply erm

lemma Extract.eweaken_im {Δ1 Δ2 : Program.Ctx Srt} {A1 A2 B m1 m2 n1 n2 s i} :
    Δ2 = B :⟨.im, s⟩ Δ1 ->
    m2 = m1⟨↑⟩ ->
    n2 = n1⟨↑⟩ ->
    A2 = A1⟨↑⟩ ->
    Δ1 ⊢ m1 ▷ n1 :: A1 ->
    Δ1.logical ⊢ B : .srt s i ->
    Δ2 ⊢ m2 ▷ n2 :: A2 := by
  intros; subst_vars
  apply Extract.weaken_im <;> assumption
