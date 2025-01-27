import SStructTT.Static.Substitution
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

lemma Typed.pi0_inv {Γ : Ctx Srt} {A B T r s} :
    Γ ⊢ .pi A B r s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.pi A B r s = x
  intro ty; induction ty generalizing A B r s
  all_goals try trivial
  case pi sB iA iB _ _ _ _ =>
    cases e; exists sB, iB, (max iA iB); aesop
  case conv eq1 _ _ ih _ =>
    have ⟨sB, iB, i, _, eq2⟩ := ih e
    exists sB, iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.sig_inv {Γ : Ctx Srt} {A B T r s} :
    Γ ⊢ .sig A B r s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.sig A B r s = x
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case sig sB iA iB _ _ _ _ _ _ =>
    cases e; exists sB, iB, (max iA iB); aesop
  case conv eq1 _ _ ih _ =>
    have ⟨sB, iB, i, _, eq2⟩ := ih e
    exists sB, iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.idn_inv {Γ : Ctx Srt} {A T m n} :
    Γ ⊢ .idn A m n : T ->
    ∃ i, Γ ⊢ m : A ∧ Γ ⊢ n : A ∧ T === .srt s0 i := by
  generalize e: Tm.idn A m n = x
  intro ty; induction ty generalizing A m n
  all_goals try trivial
  case idn _ iA _ _ _ _ _ _ =>
    cases e
    exists iA
    aesop
  case conv eq1 _ _ ih _ =>
    have ⟨i, _, _, eq2⟩ := ih e
    exists i
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam_inv' {Γ : Ctx Srt} {A T m r s} :
    Γ ⊢ .lam A m r s : T ->
    ∃ B, A :: Γ ⊢ m : B ∧ T === .pi A B r s := by
  generalize e: Tm.lam A m r s = x
  intro ty; induction ty generalizing A m r s
  all_goals try trivial
  case lam B _ _ _ _ _ _ _ _ _ =>
    cases e; exists B; aesop
  case conv eq1 _ _ ih _ =>
    have ⟨B, _, eq2⟩ := ih e
    exists B
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup_inv' {Γ : Ctx Srt} {T m n r s} :
    Γ ⊢ .tup m n r s : T ->
    ∃ A B, Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ T === .sig A B r s := by
  generalize e: Tm.tup m n r s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup A B _ _ _ _ _ _ _ _ _ _ _ =>
    cases e; exists A, B; aesop
  case conv eq1 _ _ ih _ =>
    have ⟨A, B, _, _, eq2⟩ := ih e
    exists A, B
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.rfl_inv' {Γ : Ctx Srt} {T m} :
    Γ ⊢ .rfl m : T ->
    ∃ A, Γ ⊢ m : A ∧ T === .idn A m m := by
  generalize e: Tm.rfl m = x
  intro ty; induction ty generalizing m
  all_goals try trivial
  case rfl A _ _ _ =>
    exists A; cases e; aesop
  case conv eq1 _ _ ih _ =>
    have ⟨A, _, eq2⟩ := ih e
    exists A
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

theorem Typed.validity {Γ : Ctx Srt} {A m} :
    Γ ⊢ m : A -> ∃ s i, Γ ⊢ A : .srt s i := by
  intro ty; induction ty
  all_goals try trivial
  case srt i _ _ =>
    exists s0, i+2
    constructor
    assumption
  case var wf hs _ =>
    have ⟨s, i, _⟩ := wf.has_typed hs
    exists s, i
  case pi s _ _ iA iB tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case lam s _ _ _ tym _ ihm =>
    have wf := tym.toWf
    cases wf; case cons iA _ _ =>
    have ⟨_, iB, _⟩ := ihm
    exists s, (max iA iB)
    constructor <;> assumption
  case app ihm _ =>
    replace ⟨s, i, ihm⟩ := ihm
    have ⟨s, i, j, tyB, eq⟩ := ihm.pi0_inv
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case sig iA iB _ _ tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case tup s i _ _ _ _ _ _ =>
    exists s, i
  case proj s i _ _ _ _ _ _ =>
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case bool => exists s0, 1; constructor; assumption
  case tt => exists s0, 0; constructor; assumption
  case ff => exists s0, 0; constructor; assumption
  case ite s i _ _ _ _ _ _ _ _ =>
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case idn i tyA _ _ _ _ _ =>
    exists s0, i+1; constructor; apply tyA.toWf
  case rfl ih =>
    have ⟨s, i, ty⟩ := ih
    exists s0, i
    constructor <;> assumption
  case rw m n a b s i _ _ _ _ _ ihI =>
    have ⟨sI, iI, tyI⟩ := ihI
    have ⟨_, tya, tyb, _⟩ := tyI.idn_inv
    exists s, i
    rw[show Tm.srt s i = (Tm.srt s i).[n,b/] by asimp]
    apply Typed.substitution
    . assumption
    . constructor
      asimp; assumption
      constructor
      asimp; assumption
      apply AgreeSubst.refl
      apply tya.toWf
  case conv => aesop

lemma Typed.lam_inv {Γ : Ctx Srt} {A A' B m r r' s s'} :
    Γ ⊢ .lam A m r s : .pi A' B r' s' ->
    A' :: Γ ⊢ m : B ∧ r = r' ∧ s = s' := by
  intro ty
  have ⟨B', tym, eq⟩ := ty.lam_inv'
  have ⟨_, _, eqA, eqB⟩ := Conv.pi_inj eq
  subst_vars; simp
  have ⟨s, i, tyP⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi0_inv
  have ⟨_, _, _, tyA'⟩ := tyB.ctx_inv
  have ⟨_, _, _, tyA⟩ := tym.ctx_inv
  replace tyB := Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.tup_inv {Γ : Ctx Srt} {A B m n r r' s s'} :
    Γ ⊢ .tup m n r s : .sig A B r' s' ->
    Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ r = r' ∧ s = s' := by
  intro ty
  have ⟨A', B', tym, tyn, eq⟩ := ty.tup_inv'
  have ⟨_, _, eqA, eqB⟩ := Conv.sig_inj eq
  subst_vars; simp
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace tym := Typed.conv eqA.sym tym tyA
  replace tyB := tyB.subst tym; asimp at tyB
  constructor
  . assumption
  . apply Typed.conv
    apply Conv.subst _ eqB.sym
    assumption
    assumption

lemma Typed.rfl_inv {Γ : Ctx Srt} {A m a b} :
    Γ ⊢ .rfl m : .idn A a b -> Γ ⊢ m : A ∧ m === a ∧ m === b := by
  intro ty
  have ⟨A', tym, eq⟩ := ty.rfl_inv'
  have ⟨eqA, eqa, eqb⟩ := Conv.idn_inj eq
  have ⟨s, i, tyI⟩ := ty.validity
  have ⟨_, tya, _, _⟩ := tyI.idn_inv
  have ⟨_, _, tyA⟩ := tya.validity
  and_intros
  . apply Typed.conv eqA.sym tym tyA
  . apply eqa.sym
  . apply eqb.sym
