import SStructTT.Static.Substitution
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

lemma Typed.pi_inv {Γ : Ctx Srt} {A B T r s} :
    Γ ⊢ .pi A B r s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.pi A B r s = x
  intro ty; induction ty generalizing A B r s
  all_goals try trivial
  case pi sB iA iB _ _ _ _ =>
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

lemma Typed.sig_inv {Γ : Ctx Srt} {A B T r s} :
    Γ ⊢ .sig A B r s : T ->
    ∃ sB iB i, A :: Γ ⊢ B : .srt sB iB ∧ T === .srt s i := by
  generalize e: Tm.sig A B r s = x
  intro ty; induction ty generalizing A B r s
  all_goals try trivial
  case sig sB iA iB _ _ _ _ =>
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

lemma Typed.id_inv {Γ : Ctx Srt} {A T m n} :
    Γ ⊢ .id A m n : T ->
    ∃ i, Γ ⊢ m : A ∧ Γ ⊢ n : A ∧ T === .srt s0 i := by
  generalize e: Tm.id A m n = x
  intro ty; induction ty generalizing A m n
  all_goals try trivial
  case id _ iA _ _ _ _ _ _ =>
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

lemma Typed.lam_inv {Γ : Ctx Srt} {A T m r s} :
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

lemma Typed.pair_inv {Γ : Ctx Srt} {T m n r s} :
    Γ ⊢ .pair m n r s : T ->
    ∃ A B, Γ ⊢ m : A ∧ Γ ⊢ n : B.[m/] ∧ T === .sig A B r s := by
  generalize e: Tm.pair m n r s = x
  intro ty; induction ty generalizing m n r s
  all_goals try trivial
  case pair A B _ _ _ _ _ _ _ _ _ _ _ =>
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

lemma Typed.rfl_inv {Γ : Ctx Srt} {T m} :
    Γ ⊢ .rfl m : T ->
    ∃ A, Γ ⊢ m : A ∧ T === .id A m m := by
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

theorem Typed.valid {Γ : Ctx Srt} {A m} :
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
    have ⟨s, i, j, tyB, eq⟩ := ihm.pi_inv
    exists s, i
    apply Typed.esubst <;> try first | rfl | assumption
    asimp
  case sig s _ _ iA iB tyA _ _ _ =>
    exists s0, (max iA iB + 1)
    constructor
    apply tyA.toWf
  case pair s i _ _ _ _ _ _ =>
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
  case id i tyA _ _ _ _ _ =>
    exists s0, i+1; constructor; apply tyA.toWf
  case rfl ih =>
    have ⟨s, i, ty⟩ := ih
    exists s0, i
    constructor <;> assumption
  case rw m n a b s i _ _ _ _ _ ihI =>
    have ⟨sI, iI, tyI⟩ := ihI
    have ⟨_, tya, tyb, _⟩ := tyI.id_inv
    exists s, i
    have : Tm.srt s i = (Tm.srt s i).[n,b/] := by asimp
    rw[this]
    apply Typed.substitution
    . assumption
    . constructor
      asimp; assumption
      constructor
      asimp; assumption
      apply AgreeSubst.refl
      apply tya.toWf
  case conv => aesop
