import SStructTT.Static.Substitution
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

lemma Typed.pi0_inv {Γ : Ctx Srt} {A B T s} :
    Γ ⊢ .pi0 A B s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.pi0 A B s = x
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case pi0 sB iA iB _ _ _ _ =>
    cases e
    exists sB, iB, (max iA iB)
    aesop
  case conv eq1 _ _ ih _ =>
    have ⟨sB, iB, i, _, eq2⟩ := ih e
    exists sB, iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.pi1_inv {Γ : Ctx Srt} {A B T s} :
    Γ ⊢ .pi1 A B s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.pi1 A B s = x
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case pi1 sB iA iB _ _ _ _ =>
    cases e
    exists sB, iB, (max iA iB)
    aesop
  case conv eq1 _ _ ih _ =>
    have ⟨sB, iB, i, _, eq2⟩ := ih e
    exists sB, iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.sig0_inv {Γ : Ctx Srt} {A B T s} :
    Γ ⊢ .sig0 A B s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.sig0 A B s = x
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case sig0 sB iA iB _ _ _ _ =>
    cases e
    exists sB, iB, (max iA iB)
    aesop
  case conv eq1 _ _ ih _ =>
    have ⟨sB, iB, i, _, eq2⟩ := ih e
    exists sB, iB, i
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.sig1_inv {Γ : Ctx Srt} {A B T s} :
    Γ ⊢ .sig1 A B s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.sig1 A B s = x
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case sig1 sB iA iB _ _ _ _ =>
    cases e
    exists sB, iB, (max iA iB)
    aesop
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

lemma Typed.lam0_inv' {Γ : Ctx Srt} {A T m s} :
    Γ ⊢ .lam0 A m s : T ->
    ∃ B, A :: Γ ⊢ m : B ∧ T === .pi0 A B s := by
  generalize e: Tm.lam0 A m s = x
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam0 B _ _ _ _ _ _ _ _ =>
    cases e; exists B; aesop
  case conv eq1 _ _ ih _ =>
    have ⟨B, _, eq2⟩ := ih e
    exists B
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam1_inv' {Γ : Ctx Srt} {A T m s} :
    Γ ⊢ .lam1 A m s : T ->
    ∃ B, A :: Γ ⊢ m : B ∧ T === .pi1 A B s := by
  generalize e: Tm.lam1 A m s = x
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam1 B _ _ _ _ _ _ _ _ =>
    cases e; exists B; aesop
  case conv eq1 _ _ ih _ =>
    have ⟨B, _, eq2⟩ := ih e
    exists B
    constructor
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup0_inv' {Γ : Ctx Srt} {T m n s} :
    Γ ⊢ .tup0 m n s : T ->
    ∃ A B, Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ T === .sig0 A B s := by
  generalize e: Tm.tup0 m n s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup0 A B _ _ _ _ _ _ _ _ _ _ =>
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

lemma Typed.tup1_inv' {Γ : Ctx Srt} {T m n s} :
    Γ ⊢ .tup1 m n s : T ->
    ∃ A B, Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ T === .sig1 A B s := by
  generalize e: Tm.tup1 m n s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup1 A B _ _ _ _ _ _ _ _ _ _ =>
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
  case pi0 s _ _ iA iB tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case pi1 s _ _ iA iB tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case lam0 s _ _ _ tym _ ihm =>
    have wf := tym.toWf
    cases wf; case cons iA _ _ =>
    have ⟨_, iB, _⟩ := ihm
    exists s, (max iA iB)
    constructor <;> assumption
  case lam1 s _ _ _ tym _ ihm =>
    have wf := tym.toWf
    cases wf; case cons iA _ _ =>
    have ⟨_, iB, _⟩ := ihm
    exists s, (max iA iB)
    constructor <;> assumption
  case app0 ihm _ =>
    replace ⟨s, i, ihm⟩ := ihm
    have ⟨s, i, j, tyB, eq⟩ := ihm.pi0_inv
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case app1 ihm _ =>
    replace ⟨s, i, ihm⟩ := ihm
    have ⟨s, i, j, tyB, eq⟩ := ihm.pi1_inv
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case sig0 s _ _ iA iB tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case sig1 s _ _ iA iB tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case tup0 s i _ _ _ _ _ _ =>
    exists s, i
  case tup1 s i _ _ _ _ _ _ =>
    exists s, i
  case proj0 s i _ _ _ _ _ _ =>
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case proj1 s i _ _ _ _ _ _ =>
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

lemma Typed.lam0_inv {Γ : Ctx Srt} {A A' B m s s'} :
    Γ ⊢ .lam0 A m s : .pi0 A' B s' ->
    A' :: Γ ⊢ m : B ∧ s = s' := by
  intro ty
  have ⟨B', tym, eq⟩ := ty.lam0_inv'
  have ⟨_, eqA, eqB⟩ := Conv.pi0_inj eq
  subst_vars; simp
  have ⟨s, i, tyP⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi0_inv
  have ⟨_, _, _, tyA'⟩ := tyB.ctx_inv
  have ⟨_, _, _, tyA⟩ := tym.ctx_inv
  replace tyB := Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.lam1_inv {Γ : Ctx Srt} {A A' B m s s'} :
    Γ ⊢ .lam1 A m s : .pi1 A' B s' ->
    A' :: Γ ⊢ m : B ∧ s = s' := by
  intro ty
  have ⟨B', tym, eq⟩ := ty.lam1_inv'
  have ⟨_, eqA, eqB⟩ := Conv.pi1_inj eq
  subst_vars; simp
  have ⟨s, i, tyP⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi1_inv
  have ⟨_, _, _, tyA'⟩ := tyB.ctx_inv
  have ⟨_, _, _, tyA⟩ := tym.ctx_inv
  replace tyB := Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.tup0_inv {Γ : Ctx Srt} {A B m n s s'} :
    Γ ⊢ .tup0 m n s : .sig0 A B s' ->
    Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ s = s' := by
  intro ty
  have ⟨A', B', tym, tyn, eq⟩ := ty.tup0_inv'
  have ⟨_, eqA, eqB⟩ := Conv.sig0_inj eq
  subst_vars; simp
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig0_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace tym := Typed.conv eqA.sym tym tyA
  replace tyB := tyB.subst tym; asimp at tyB
  constructor
  . assumption
  . apply Typed.conv
    apply Conv.subst _ eqB.sym
    assumption
    assumption

lemma Typed.tup1_inv {Γ : Ctx Srt} {A B m n s s'} :
    Γ ⊢ .tup1 m n s : .sig1 A B s' ->
    Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ s = s' := by
  intro ty
  have ⟨A', B', tym, tyn, eq⟩ := ty.tup1_inv'
  have ⟨_, eqA, eqB⟩ := Conv.sig1_inj eq
  subst_vars; simp
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig1_inv
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

lemma Typed.lam0_pi1_false {Γ : Ctx Srt} {A1 A2 B C m s1 s2} :
    Γ ⊢ .lam0 A1 m s1 : C -> C === .pi1 A2 B s2 -> False := by
  generalize e: Tm.lam0 A1 m s1 = n
  intro ty; induction ty generalizing A1 m s1
  all_goals try trivial
  case lam0 => intro eq; false_conv eq
  case conv ihm _ =>
    intro eq; subst_vars
    apply ihm; rfl
    apply Conv.trans <;> assumption

lemma Typed.lam1_pi0_false {Γ : Ctx Srt} {A1 A2 B C m s1 s2} :
    Γ ⊢ .lam1 A1 m s1 : C -> C === .pi0 A2 B s2 -> False := by
  generalize e: Tm.lam1 A1 m s1 = n
  intro ty; induction ty generalizing A1 m s1
  all_goals try trivial
  case lam1 => intro eq; false_conv eq
  case conv ihm _ =>
    intro eq; subst_vars
    apply ihm; rfl
    apply Conv.trans <;> assumption

lemma Typed.tup0_sig1_false {Γ : Ctx Srt} {A B C m1 m2 s1 s2} :
    Γ ⊢ .tup0 m1 m2 s1 : C -> C === .sig1 A B s2 -> False := by
  generalize e: Tm.tup0 m1 m2 s1 = n
  intro ty; induction ty generalizing m1 m2 s1
  all_goals try trivial
  case tup0 => intro eq; false_conv eq
  case conv ihm _ =>
    intro eq; subst_vars
    apply ihm; rfl
    apply Conv.trans <;> assumption

lemma Typed.tup1_sig0_false {Γ : Ctx Srt} {A B C m1 m2 s1 s2} :
    Γ ⊢ .tup1 m1 m2 s1 : C -> C === .sig0 A B s2 -> False := by
  generalize e: Tm.tup1 m1 m2 s1 = n
  intro ty; induction ty generalizing m1 m2 s1
  all_goals try trivial
  case tup1 => intro eq; false_conv eq
  case conv ihm _ =>
    intro eq; subst_vars
    apply ihm; rfl
    apply Conv.trans <;> assumption
