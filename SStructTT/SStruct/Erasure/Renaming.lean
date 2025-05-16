import SStructTT.SStruct.Dynamic.Renaming
import SStructTT.SStruct.Erasure.Erased
open SStruct.Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.renaming {Γ Γ'} {Δ Δ' : Ctx Srt} {A m m' ξ} :
    Γ ;; Δ ⊢ m ▷ m' : A ->
    AgreeRen ξ Γ Δ Γ' Δ' ->
    Γ' ;; Δ' ⊢ m.[ren ξ] ▷ m'.[ren ξ] : A.[ren ξ] := by
  intro er agr; induction er generalizing Γ' Δ' ξ <;> asimp
  case var wf h =>
    constructor <;> try aesop
    . apply agr.wf wf
    . apply agr.has h
  case lam_im Γ Δ A B m m' s sA i lw tyA erm ih =>
    constructor
    . apply agr.lower lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.cons .im tyA)
      asimp at ih; assumption
  case lam_ex Γ Δ A B m m' rA s sA i c rs lw tyA erm ih =>
    constructor
    . apply rs
    . apply agr.lower lw
    . apply tyA.renaming agr.toStatic
    . specialize ih (agr.cons rA tyA)
      asimp at ih; assumption
  case app_im Γ Δ A B m m' n s erm tyn ihm =>
    replace erm := ihm agr; asimp at erm
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    have er := Erased.app_im erm tyn
    asimp at er; assumption
  case app_ex Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ern ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn agr2; asimp at ern
    have er := Erased.app_ex mrg erm ern
    asimp at er; assumption
  case tup_im tyS erm tyn ih =>
    replace erm := ih agr; asimp at erm
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    replace tyS := tyS.renaming agr.toStatic; asimp at tyS
    constructor <;> (asimp; assumption)
  case tup_ex mrg tyS erm ern ihm ihn =>
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn agr2; asimp at ern
    replace tyS := tyS.renaming agr.toStatic; asimp at tyS
    constructor <;> (asimp; assumption)
  case proj_im A B C m m' n n' rA s sA sB sC iC c rs mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.renaming (agr.toStatic.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons rA tyA).cons .im tyB)
    rw[show C.[.tup (.var 1) (.var 0) .im s .: shift 2].[ren (upren (upren ξ))]
          = C.[up (ren ξ)].[.tup (.var 1) (.var 0) .im s .: shift 2]
        by asimp] at ern
    rw[SubstLemmas.upren_up] at ern
    have er := Erased.proj_im rs mrg tyC erm ern
    asimp at er; assumption
  case proj_ex A B C m m' n n' rA rB s sA sB sC iC c1 c2 rs1 rs2 mrg tyC erm ern ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    obtain ⟨_, _ | ⟨tyA, _⟩, tyB⟩ := ern.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    replace tyC := tyC.renaming (agr.toStatic.cons tyS); asimp at tyC
    replace erm := ihm agr1; asimp at erm
    replace ern := ihn ((agr2.cons rA tyA).cons rB tyB)
    rw[show C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[ren (upren (upren ξ))]
          = C.[up (ren ξ)].[.tup (.var 1) (.var 0) .ex s .: shift 2]
        by asimp] at ern
    rw[SubstLemmas.upren_up] at ern
    have er := Erased.proj_ex rs1 rs2 mrg tyC erm ern
    asimp at er; assumption
  case tt h ih => constructor <;> aesop (rule_sets := [rename])
  case ff h ih => constructor <;> aesop (rule_sets := [rename])
  case ite A _ _ _ _ _ _ _ _  mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    have ⟨s, i, _, tyb⟩ := tyA.ctx_inv
    have ⟨Δ1', Δ2', mrg, agr1, agr2⟩ := agr.split mrg
    specialize ihm agr1; asimp at ihm
    specialize ihn1 agr2; asimp at ihn1
    specialize ihn2 agr2; asimp at ihn2
    replace tyA := tyA.renaming (agr.toStatic.cons tyb); asimp at tyA
    rw[show A.[.tt .: ren ξ] = A.[up (ren ξ)].[.tt/] by asimp] at ihn1
    rw[show A.[.ff .: ren ξ] = A.[up (ren ξ)].[.ff/] by asimp] at ihn2
    have ty := Erased.ite mrg tyA ihm ihn1 ihn2; asimp at ty
    assumption
  case rw A B m m' n a b s i tyA erm tyn ih =>
    have ⟨_, _, _, tyI⟩ := tyA.ctx_inv
    have ⟨_, _, _, tyB⟩ := tyI.ctx_inv
    replace tyA := tyA.renaming ((agr.toStatic.cons tyB).cons tyI); asimp at tyA
    replace erm := ih agr; asimp at erm
    replace tyn := tyn.renaming agr.toStatic; asimp at tyn
    simp[<-SubstLemmas.subst_comp] at tyA
    rw[show A.[a.[ren ξ].rfl .: a.[ren ξ] .: ren ξ]
          = A.[upn 2 (ren ξ)].[.rfl a.[ren ξ],a.[ren ξ]/]
         by asimp] at erm
    have := Erased.rw tyA erm tyn
    asimp at this; assumption
  case conv eq erm tyB ih =>
    replace tyB := tyB.renaming agr.toStatic
    replace erm := ih agr
    apply Erased.conv
    . apply Static.Conv.subst _ eq
    . assumption
    . assumption

lemma Erased.weaken {Γ} {Δ : Dynamic.Ctx Srt} {A B m m' s i} :
    Γ ;; Δ ⊢ m ▷ m' : A ->
    Γ ⊢ B : .srt s i ->
    B :: Γ ;; B :⟨.im, s⟩ Δ ⊢ m.[shift 1] ▷ m'.[shift 1] : A.[shift 1] := by
  intro erm tyB
  apply erm.renaming
  constructor
  . assumption
  . exact AgreeRen.refl erm.toWf

lemma Erased.eweaken {Γ1 Γ2} {Δ1 Δ2 : Dynamic.Ctx Srt} {A1 A2 B m1 m2 n1 n2 s i} :
    Γ2 = B :: Γ1 ->
    Δ2 = B :⟨.im, s⟩ Δ1 ->
    m2 = m1.[shift 1] ->
    n2 = n1.[shift 1] ->
    A2 = A1.[shift 1] ->
    Γ1 ;; Δ1 ⊢ m1 ▷ n1 : A1 ->
    Γ1 ⊢ B : .srt s i ->
    Γ2 ;; Δ2 ⊢ m2 ▷ n2 : A2 := by
  intros; subst_vars
  apply Erased.weaken <;> assumption
