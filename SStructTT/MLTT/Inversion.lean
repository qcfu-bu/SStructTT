import SStructTT.MLTT.Substitution
open ARS

namespace MLTT

lemma Typed.pi_inv {Γ : Ctx} {A B T} :
    Γ ⊢ .pi A B : T ->
    ∃ iB i, A :: Γ ⊢ B : .ty iB ∧ T === .ty i := by
  generalize e: Tm.pi A B = x
  intro ty; induction ty generalizing A B
  all_goals try trivial
  case pi iA iB _ _ _ _ =>
    cases e; existsi iB, (max iA iB); aesop
  case conv eq1 _ _ ih _ =>
    have ⟨iB, i, _, eq2⟩ := ih e
    existsi iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.sig_inv {Γ : Ctx} {A B T} :
    Γ ⊢ .sig A B : T ->
    ∃ iB i, A :: Γ ⊢ B : .ty iB ∧ T === .ty i := by
  generalize e: Tm.sig A B = x
  intro ty; induction ty generalizing A B
  all_goals try trivial
  case sig iA iB _ _ _ _ =>
    cases e; existsi iB, (max iA iB); aesop
  case conv eq1 _ _ ih _ =>
    have ⟨iB, i, _, eq2⟩ := ih e
    existsi iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.idn_inv {Γ : Ctx} {A T m n} :
    Γ ⊢ .idn A m n : T ->
    ∃ i, Γ ⊢ m : A ∧ Γ ⊢ n : A ∧ T === .ty i := by
  generalize e: Tm.idn A m n = x
  intro ty; induction ty generalizing A m n
  all_goals try trivial
  case idn i _ _ _ _ _ _ =>
    cases e
    existsi i
    aesop
  case conv eq1 _ _ ih _ =>
    have ⟨i, _, _, eq2⟩ := ih e
    existsi i
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam_inv' {Γ : Ctx} {A T m} :
    Γ ⊢ .lam A m : T ->
    ∃ B, A :: Γ ⊢ m : B ∧ T === .pi A B := by
  generalize e: Tm.lam A m = x
  intro ty; induction ty generalizing A m
  all_goals try trivial
  case lam A B m iA tyA tym ihA ihm =>
    cases e
    exact ⟨B, tym, Conv.R⟩
  case conv eq1 _ _ ih _ =>
    have ⟨B, _, eq2⟩ := ih e
    existsi B
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup_inv' {Γ : Ctx} {T m n} :
    Γ ⊢ .tup m n : T ->
    ∃ A B, Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ T === .sig A B := by
  generalize e: Tm.tup m n = x
  intro ty; induction ty generalizing m n
  all_goals try trivial
  case tup A B m n i tyS tym tyn ihS ihm ihn =>
    cases e
    exact ⟨A, B, tym, tyn, Conv.R⟩
  case conv eq1 _ _ ih _ =>
    have ⟨A, B, _, _, eq2⟩ := ih e
    existsi A, B
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.rfl_inv' {Γ : Ctx} {T m} :
    Γ ⊢ .rfl m : T ->
    ∃ A, Γ ⊢ m : A ∧ T === .idn A m m := by
  generalize e: Tm.rfl m = x
  intro ty; induction ty generalizing m
  all_goals try trivial
  case rfl A m tym ihm =>
    cases e
    exact ⟨A, tym, Conv.R⟩
  case conv eq1 _ _ ih _ =>
    have ⟨A, _, eq2⟩ := ih e
    existsi A
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

theorem Typed.validity {Γ : Ctx} {A m} :
    Γ ⊢ m : A -> ∃ i, Γ ⊢ A : .ty i := by
  intro ty; induction ty
  case srt i _ _ =>
    existsi i + 2
    constructor
    assumption
  case var wf hs _ =>
    have ⟨i, tyA⟩ := wf.has_typed hs
    exact ⟨i, tyA⟩
  case pi iA iB tyA _ _ _ =>
    existsi max iA iB + 1
    constructor
    apply tyA.toWf
  case lam _ _ _ tym _ ihm =>
    have wf := tym.toWf
    cases wf; case cons iA _ _ =>
    have ⟨iB, _⟩ := ihm
    existsi max iA iB
    constructor <;> assumption
  case app A B m n tym tyn ihm ihn =>
    replace ⟨_, tym⟩ := ihm
    have ⟨i, _, tyB, _⟩ := tym.pi_inv
    have tyB' := tyB.subst tyn
    asimp at tyB'
    exact ⟨i, tyB'⟩
  case sig iA iB tyA _ _ _ =>
    existsi max iA iB + 1
    constructor
    apply tyA.toWf
  case tup A B m n i tyS tym tyn ihS ihm ihn =>
    exact ⟨_, tyS⟩
  case prj A B C m n iC tyC tym tyn ihC ihm ihn =>
    have tyC' := tyC.subst tym
    asimp at tyC'
    exact ⟨_, tyC'⟩
  case bool => existsi 1; constructor; assumption
  case tt => existsi 0; constructor; assumption
  case ff => existsi 0; constructor; assumption
  case bot => existsi 1; constructor; assumption
  case exf A m i tyA tym ihA ihm =>
    existsi i
    have := tyA.subst tym; asimp at this; assumption
  case ite A m n1 n2 i tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    have tyA' := tyA.subst tym
    asimp at tyA'
    exact ⟨i, tyA'⟩
  case idn A m n i tyA tym tyn ihA ihm ihn =>
    existsi i + 1; constructor; apply tyA.toWf
  case rfl ih =>
    have ⟨i, ty⟩ := ih
    existsi i
    constructor <;> assumption
  case rw A B m n a b i tyA tym tyn ihA ihm ihn =>
    have ⟨_, tyI⟩ := ihn
    have ⟨_, tya, tyb, _⟩ := tyI.idn_inv
    existsi i
    rw[show Tm.ty i = (Tm.ty i).[n,b/] by asimp]
    apply Typed.substitution
    . assumption
    . constructor
      asimp; assumption
      constructor
      asimp; assumption
      apply AgreeSubst.refl
      apply tya.toWf
  case conv => aesop
  case nil => trivial
  case cons => trivial

lemma Typed.lam_inv {Γ : Ctx} {A A' B m} :
    Γ ⊢ .lam A m : .pi A' B ->
    A' :: Γ ⊢ m : B := by
  intro ty
  have ⟨B', tym, eq⟩ := ty.lam_inv'
  have ⟨eqA, eqB⟩ := Conv.pi_inj eq
  have ⟨_, tyP⟩ := ty.validity
  have ⟨_, _, tyB, _⟩ := tyP.pi_inv
  have ⟨_, _, tyA'⟩ := tyB.ctx_inv
  have ⟨_, _, tyA⟩ := tym.ctx_inv
  replace tyB := Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.tup_inv {Γ : Ctx} {A B m n} :
    Γ ⊢ .tup m n : .sig A B ->
    Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] := by
  intro ty
  have ⟨A', B', tym, tyn, eq⟩ := ty.tup_inv'
  have ⟨eqA, eqB⟩ := Conv.sig_inj eq
  have ⟨_, tyS⟩ := ty.validity
  have ⟨_, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, tyA⟩ := tyB.ctx_inv
  replace tym := Typed.conv eqA.sym tym tyA
  replace tyB := tyB.subst tym; asimp at tyB
  constructor
  . assumption
  . apply Typed.conv
    apply Conv.subst _ eqB.sym
    assumption
    assumption

lemma Typed.rfl_inv {Γ : Ctx} {A m a b} :
    Γ ⊢ .rfl m : .idn A a b -> Γ ⊢ m : A ∧ m === a ∧ m === b := by
  intro ty
  have ⟨A', tym, eq⟩ := ty.rfl_inv'
  have ⟨eqA, eqa, eqb⟩ := Conv.idn_inj eq
  have ⟨_, tyI⟩ := ty.validity
  have ⟨_, tya, _, _⟩ := tyI.idn_inv
  have ⟨_, tyA⟩ := tya.validity
  and_intros
  . apply Typed.conv eqA.sym tym tyA
  . apply eqa.sym
  . apply eqb.sym
