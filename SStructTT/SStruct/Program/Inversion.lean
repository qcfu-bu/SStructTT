import SStructTT.SStruct.Logical.Inversion
import SStructTT.SStruct.Logical.Preservation
import SStructTT.SStruct.Logical.Unique
import SStructTT.SStruct.Program.Substitution
open ARS

namespace SStruct.Program
variable {Srt : Type} [ord : SrtOrder Srt]

theorem Typed.validity {Δ : Ctx Srt} {A m} :
    Δ ⊢ m :: A -> ∃ s i, Δ.logical ⊢ A : .srt s i := by
  intro ty; apply ty.toLogical.validity

lemma Typed.lam_im_inv' {Δ : Ctx Srt} {A T m s} :
    Δ ⊢ .lam A m .im s :: T ->
    ∃ B sA,
      A :⟨.im, sA⟩ Δ ⊢ m :: B ∧
      T === .pi A B .im s := by
  generalize e: Tm.lam A m .im s = x
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam_im B _ _ sA _ _ _ _ _ =>
    cases e; existsi B, sA; aesop
  case lam_ex => cases e
  case drop mrg lw h tyn ihn =>
    have ⟨B, sA, tym, eq2⟩ := ihn e
    existsi B, sA; and_intros
    . apply Typed.drop (mrg.im _ _) _ h tym
      constructor; assumption
    . assumption
  case conv eq1 _ _ ih =>
    have ⟨B, sA, tym, eq2⟩ := ih e
    existsi B, sA; and_intros
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam_ex_inv' {Δ : Ctx Srt} {A T m s} :
    Δ ⊢ .lam A m .ex s :: T ->
    ∃ B sA,
      A :⟨.ex, sA⟩ Δ ⊢ m :: B ∧
      T === .pi A B .ex s := by
  generalize e: Tm.lam A m .ex s = x
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam_im => cases e
  case lam_ex B _ _ sA _ _ _ _ _ =>
    cases e; existsi B, sA; aesop
  case drop mrg lw h tyn ihn =>
    have ⟨B, sA, tym, eq2⟩ := ihn e
    existsi B, sA; and_intros
    . apply Typed.drop (mrg.right _ _) _ h tym
      constructor; assumption
    . assumption
  case conv eq1 _ _ ih =>
    have ⟨B, sA, tym, eq2⟩ := ih e
    existsi B, sA; and_intros
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup_im_inv' {Δ : Ctx Srt} {T m n s} :
    Δ ⊢ .tup m n .im s :: T ->
    ∃ A B,
      Δ.logical ⊢ m : A ∧
      Δ ⊢ n :: B.[m/] ∧
      T === .sig A B .im s := by
  generalize e: Tm.tup m n .im s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup_im A B _ _ _ _ _ _ _ _ =>
    cases e; existsi A, B; aesop
  case tup_ex => cases e
  case drop mrg lw h tyn ihn =>
    have ⟨A, B, tym, tyn, eq2⟩ := ihn e
    existsi A, B; and_intros
    . rw[mrg.sym.logical]; assumption
    . apply Typed.drop mrg _ h tyn
      assumption
    . assumption
  case conv eq1 _ _ ih =>
    have ⟨A, B, _, _, eq2⟩ := ih e
    existsi A, B; and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.tup_ex_inv' {Δ : Ctx Srt} {T m n s} :
    Δ ⊢ .tup m n .ex s :: T ->
    ∃ Δ1 Δ2 A B,
      Merge Δ1 Δ2 Δ ∧
      Δ1 ⊢ m :: A ∧
      Δ2 ⊢ n :: B.[m/] ∧
      T === .sig A B .ex s := by
  generalize e: Tm.tup m n .ex s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup_im => cases e
  case tup_ex Δ1 Δ2 Δ A B _ _ _ _ _ _ _ _ _ _ =>
    cases e; existsi Δ1, Δ2, A, B; aesop
  case drop mrg lw h tyn ihn =>
    have ⟨Δ1, Δ2, A, B, mrg', tym, tyn, eq2⟩ := ihn e
    have ⟨Δ3, mrg1, mrg2⟩ := mrg.sym.split mrg'.sym
    existsi Δ1, Δ3, A, B; and_intros
    . apply mrg2.sym
    . assumption
    . apply Typed.drop mrg1.sym lw h tyn
    . assumption
  case conv eq1 _ _ ih =>
    have ⟨Δ1, Δ2, A, B, mrg, _, _, eq2⟩ := ih e
    existsi Δ1, Δ2, A, B; and_intros
    . assumption
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Typed.lam_im_inv {Δ : Ctx Srt} {A A' B m s s'} :
    Δ ⊢ .lam A m .im s :: .pi A' B .im s' ->
    ∃ sA, A' :⟨.im, sA⟩ Δ ⊢ m :: B := by
  intro ty
  have ⟨B, sA, tym, eq⟩ := ty.lam_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Logical.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := ty.toLogical.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := tym.ctx_inv
  have ⟨x, rd', rd⟩ := Logical.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Logical.Typed.unique ty1 ty2
  subst_vars; existsi sA'
  replace tyB := Logical.Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.lam_ex_inv {Δ : Ctx Srt} {A A' B m s s'} :
    Δ ⊢ .lam A m .ex s :: .pi A' B .ex s' ->
    ∃ sA, A' :⟨.ex, sA⟩ Δ ⊢ m :: B := by
  intro ty
  have ⟨B, sA, tym, eq⟩ := ty.lam_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Logical.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := ty.toLogical.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := tym.ctx_inv
  have ⟨x, rd', rd⟩ := Logical.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Logical.Typed.unique ty1 ty2
  subst_vars; existsi sA'
  replace tyB := Logical.Typed.conv_ctx eqA.sym tyA tyB
  apply Typed.conv_ctx eqA tyA'
  apply Typed.conv eqB.sym tym tyB

lemma Typed.tup_im_inv {Δ : Ctx Srt} {A B m n s s'} :
    Δ ⊢ .tup m n .im s :: .sig A B .im s' ->
    Δ.logical ⊢ m : A ∧ Δ ⊢ n :: B.[m/] ∧ s = s' := by
  intro ty
  have ⟨A', B', tym, tyn, eq⟩ := ty.tup_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Logical.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace tym := Logical.Typed.conv eqA.sym tym tyA
  replace tyB := tyB.subst tym; asimp at tyB
  simp; and_intros
  . assumption
  . apply Typed.conv
    apply Logical.Conv.subst _ eqB.sym
    assumption
    assumption

lemma Typed.tup_ex_inv {Δ : Ctx Srt} {A B m n s s'} :
    Δ ⊢ .tup m n .ex s :: .sig A B .ex s' ->
    ∃ Δ1 Δ2,
      Merge Δ1 Δ2 Δ ∧
      Δ1 ⊢ m :: A ∧
      Δ2 ⊢ n :: B.[m/] ∧ s = s' := by
  intro ty
  have ⟨Δ1, Δ2, A', B', mrg, tym, tyn, eq⟩ := ty.tup_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Logical.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := ty.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  rw[mrg.logical] at tyA
  replace tym := Typed.conv eqA.sym tym tyA
  rw[mrg.logical] at tyB
  replace tyB := tyB.subst tym.toLogical; asimp at tyB
  existsi Δ1, Δ2; simp; and_intros
  . assumption
  . assumption
  . apply Typed.conv
    apply Logical.Conv.subst _ eqB.sym
    assumption
    rw[<-mrg.sym.logical]
    rw[<-mrg.logical] at tyB
    assumption
