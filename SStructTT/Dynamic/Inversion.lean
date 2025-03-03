import SStructTT.Static.Inversion
import SStructTT.Static.Preservation
import SStructTT.Static.Unique
import SStructTT.Dynamic.Substitution
open ARS

namespace Dynamic
variable {Srt : Type} [inst : SStruct Srt]

theorem Typed.validity {Γ} {Δ : Ctx Srt} {A m} :
    Γ ;; Δ ⊢ m : A -> ∃ s i, Γ ⊢ A : .srt s i := by
  intro ty; apply ty.toStatic.validity

lemma Typed.lam_im_inv' {Γ} {Δ : Ctx Srt} {A T m s} :
    Γ ;; Δ ⊢ .lam A m .im s : T ->
    ∃ B sA,
      A :: Γ ;; A :⟨.im, sA⟩ Δ ⊢ m : B ∧
      T === .pi A B .im s := by
  generalize e: Tm.lam A m .im s = x
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam_im B _ _ sA _ _ _ _ _ =>
    cases e; exists B, sA; aesop
  case lam_ex => cases e
  case conv eq1 _ _ ih =>
    have ⟨B, sA, tym, eq2⟩ := ih e
    exists B, sA
    and_intros
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam_ex_inv' {Γ} {Δ : Ctx Srt} {A T m s} :
    Γ ;; Δ ⊢ .lam A m .ex s : T ->
    ∃ B rA sA,
      RSrt rA sA ∧
      A :: Γ ;; A :⟨rA, sA⟩ Δ ⊢ m : B ∧
      T === .pi A B .ex s := by
  generalize e: Tm.lam A m .ex s = x
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam_im => cases e
  case lam_ex B _ rA _ sA _ rs _ _ _ _ =>
    cases e; exists B, rA, sA; aesop
  case conv eq1 _ _ ih =>
    have ⟨B, sA, rA, rs, tym, eq2⟩ := ih e
    exists B, sA, rA
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup_im_inv' {Γ} {Δ : Ctx Srt} {T m n s} :
    Γ ;; Δ ⊢ .tup m n .im s : T ->
    ∃ A B,
      Γ ;; Δ ⊢ m : A ∧
      Γ ⊢ n : B.[m/] ∧
      T === .sig A B .im s := by
  generalize e: Tm.tup m n .im s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup_im A B _ _ _ _ _ _ _ _ =>
    cases e; exists A, B; aesop
  case tup_ex => cases e
  case conv eq1 _ _ ih =>
    have ⟨A, B, _, _, eq2⟩ := ih e
    exists A, B
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup_ex_inv' {Γ} {Δ : Ctx Srt} {T m n s} :
    Γ ;; Δ ⊢ .tup m n .ex s : T ->
    ∃ Δ1 Δ2 A B,
      Merge Δ1 Δ2 Δ ∧
      Γ ;; Δ1 ⊢ m : A ∧
      Γ ;; Δ2 ⊢ n : B.[m/] ∧
      T === .sig A B .ex s := by
  generalize e: Tm.tup m n .ex s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup_im => cases e
  case tup_ex Δ1 Δ2 Δ A B _ _ _ _ _ _ _ _ _ _ =>
    cases e; exists Δ1, Δ2, A, B; aesop
  case conv eq1 _ _ ih =>
    have ⟨Δ1, Δ2, A, B, mrg, _, _, eq2⟩ := ih e
    exists Δ1, Δ2, A, B
    and_intros
    . assumption
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam_im_inv {Γ} {Δ : Ctx Srt} {A A' B m s s'} :
    Γ ;; Δ ⊢ .lam A m .im s : .pi A' B .im s' ->
    ∃ sA, A' :: Γ ;; A' :⟨.im, sA⟩ Δ ⊢ m : B := by
  intro ty
  have ⟨B, sA, tym, eq⟩ := ty.lam_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := ty.toStatic.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := tym.ctx_inv
  have ⟨x, rd', rd⟩ := Static.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Static.Typed.unique ty1 ty2
  subst_vars; exists sA'
  replace tyB := Static.Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.lam_ex_inv {Γ} {Δ : Ctx Srt} {A A' B m s s'} :
    Γ ;; Δ ⊢ .lam A m .ex s : .pi A' B .ex s' ->
    ∃ rA sA, RSrt rA sA ∧ A' :: Γ ;; A' :⟨rA, sA⟩ Δ ⊢ m : B := by
  intro ty
  have ⟨B, rA, sA, rs, tym, eq⟩ := ty.lam_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := ty.toStatic.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := tym.ctx_inv
  have ⟨x, rd', rd⟩ := Static.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Static.Typed.unique ty1 ty2
  subst_vars; exists rA, sA'
  replace tyB := Static.Typed.conv_ctx eqA.sym tyA tyB
  and_intros
  . assumption
  . apply Typed.conv_ctx eqA tyA'
    apply Typed.conv eqB.sym tym tyB

lemma Typed.tup_im_inv {Γ} {Δ : Ctx Srt} {A B m n s s'} :
    Γ ;; Δ ⊢ .tup m n .im s : .sig A B .im s' ->
    Γ ;; Δ ⊢ m : A ∧ Γ ⊢ n : B.[m/] := by
  intro ty
  have ⟨A', B', tym, tyn, eq⟩ := ty.tup_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace tym := Typed.conv eqA.sym tym tyA
  replace tyB := tyB.subst tym.toStatic; asimp at tyB
  constructor
  . assumption
  . apply Static.Typed.conv
    apply Static.Conv.subst _ eqB.sym
    assumption
    assumption

lemma Typed.tup_ex_inv {Γ} {Δ : Ctx Srt} {A B m n s s'} :
    Γ ;; Δ ⊢ .tup m n .ex s : .sig A B .ex s' ->
    ∃ Δ1 Δ2,
      Merge Δ1 Δ2 Δ ∧
      Γ ;; Δ1 ⊢ m : A ∧
      Γ ;; Δ2 ⊢ n : B.[m/] := by
  intro ty
  have ⟨Δ1, Δ2, A', B', mrg, tym, tyn, eq⟩ := ty.tup_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace tym := Typed.conv eqA.sym tym tyA
  replace tyB := tyB.subst tym.toStatic; asimp at tyB
  exists Δ1, Δ2; and_intros
  . assumption
  . assumption
  . apply Typed.conv
    apply Static.Conv.subst _ eqB.sym
    assumption
    assumption
