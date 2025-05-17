import SStructTT.SStruct.Dynamic.Inversion
import SStructTT.SStruct.Erasure.Substitution
open ARS

namespace SStruct.Erasure
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.none_preimage {Γ} {Δ : Ctx Srt} {t B} :
    Γ ;; Δ ⊢ t ▷ .none : B -> False := by
  generalize e: Tm.none = k
  intro er; induction er <;> trivial

lemma Erased.var_preimage {Γ} {Δ : Ctx Srt} {B t x} :
    Γ ;; Δ ⊢ t ▷ .var x : B -> ∃ x, t = .var x := by
  generalize e: Tm.var x = k
  intro er; induction er <;> try trivial
  case var => cases e; exists x
  case conv ih => subst_vars; simp[ih]

lemma Erased.lam_preimage {Γ} {Δ : Ctx Srt} {B t m' c s} :
    Γ ;; Δ ⊢ t ▷ .lam m' c s : B ->
    ∃ A m r, t = .lam A m r s := by
  generalize e: Tm.lam m' c s = k
  intro er; induction er <;> try trivial
  case lam_im => cases e; aesop
  case lam_ex => cases e; aesop
  case conv ih => subst_vars; simp[ih]

lemma Erased.tup_preimage {Γ} {Δ : Ctx Srt} {B m' n' t s} :
    Γ ;; Δ ⊢ t ▷ .tup m' n' s : B ->
    ∃ m n r, t = .tup m n r s := by
  generalize e: Tm.tup m' n' s = k
  intro er; induction er <;> try trivial
  case tup_im => cases e; aesop
  case tup_ex => cases e; aesop
  case conv ih => subst_vars; simp[ih]

lemma Erased.tt_preimage {Γ} {Δ : Ctx Srt} {B t} :
    Γ ;; Δ ⊢ t ▷ .tt : B -> t = .tt := by
  generalize e: Tm.tt = k
  intro er; induction er <;> try trivial
  case conv ih => subst_vars; simp[ih]

lemma Erased.ff_preimage {Γ} {Δ : Ctx Srt} {B t} :
    Γ ;; Δ ⊢ t ▷ .ff : B -> t = .ff := by
  generalize e: Tm.ff = k
  intro er; induction er <;> try trivial
  case conv ih => subst_vars; simp[ih]

theorem Erased.validity {Γ} {Δ : Ctx Srt} {A m m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> ∃ s i, Γ ⊢ A : .srt s i := by
  intro erm; apply erm.toDynamic.validity

lemma Erased.lam_im_inv' {Γ} {Δ : Ctx Srt} {A T m m' c s} :
    Γ ;; Δ ⊢ .lam A m .im s ▷ .lam m' c s : T ->
    ∃ B sA,
      A :: Γ ;; A :⟨.im, sA⟩ Δ ⊢ m ▷ m' : B ∧
      T === .pi A B .im s ∧ c = .keep := by
  generalize e1: SStruct.Tm.lam A m .im s = x
  generalize e2: Tm.lam m' c s = y
  intro er; induction er generalizing A m m' c s
  all_goals try trivial
  case lam_im B _ _ _ sA _ _ _ _ _ =>
    cases e1; cases e2; exists B, sA; aesop
  case lam_ex => cases e1
  case conv eq1 _ _ ih =>
    have ⟨B, sA, erm, eq2, e⟩ := ih e1 e2
    exists B, sA
    and_intros
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2
    . assumption

lemma Erased.lam_ex_inv' {Γ} {Δ : Ctx Srt} {A T m m' c s} :
    Γ ;; Δ ⊢ .lam A m .ex s ▷ .lam m' c s : T ->
    ∃ B rA sA,
      RSrt rA sA c ∧
      A :: Γ ;; A :⟨rA, sA⟩ Δ ⊢ m ▷ m' : B ∧
      T === .pi A B .ex s := by
  generalize e1: SStruct.Tm.lam A m .ex s = x
  generalize e2: Tm.lam m' c s = x
  intro er; induction er generalizing A m s
  all_goals try trivial
  case lam_im => cases e1
  case lam_ex B _ _ rA _ sA _ _ rs _ _ _ _ =>
    cases e1; cases e2; exists B, rA, sA; aesop
  case conv eq1 _ _ ih =>
    have ⟨B, sA, rA, rs, erm, eq2⟩ := ih e1 e2
    exists B, sA, rA
    and_intros
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.tup_im_inv' {Γ} {Δ : Ctx Srt} {T m m' n n' s} :
    Γ ;; Δ ⊢ .tup m n .im s ▷ .tup m' n' s : T ->
    ∃ A B,
      Γ ;; Δ ⊢ m ▷ m' : A ∧
      Γ ⊢ n : B.[m/] ∧ n' = .none ∧
      T === .sig A B .im s := by
  generalize e1: SStruct.Tm.tup m n .im s = x
  generalize e2: Tm.tup m' n' s = y
  intro er; induction er generalizing m n s
  all_goals try trivial
  case tup_im A B _ _ _ _ _ _ _ _ _ =>
    cases e1; cases e2; exists A, B; aesop
  case tup_ex => cases e1
  case conv eq1 _ _ ih =>
    have ⟨A, B, _, _, _, eq2⟩ := ih e1 e2
    exists A, B
    and_intros
    . assumption
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.tup_ex_inv' {Γ} {Δ : Ctx Srt} {T m m' n n' s} :
    Γ ;; Δ ⊢ .tup m n .ex s ▷ .tup m' n' s : T ->
    ∃ Δ1 Δ2 A B,
      Merge Δ1 Δ2 Δ ∧
      Γ ;; Δ1 ⊢ m ▷ m' : A ∧
      Γ ;; Δ2 ⊢ n ▷ n' : B.[m/] ∧
      T === .sig A B .ex s := by
  generalize e1: SStruct.Tm.tup m n .ex s = x
  generalize e2: Tm.tup m' n' s = y
  intro er; induction er generalizing m n s
  all_goals try trivial
  case tup_im => cases e1
  case tup_ex Δ1 Δ2 Δ A B _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases e1; cases e2; exists Δ1, Δ2, A, B; aesop
  case conv eq1 _ _ ih =>
    have ⟨Δ1, Δ2, A, B, mrg, _, _, eq2⟩ := ih e1 e2
    exists Δ1, Δ2, A, B
    and_intros
    . assumption
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.lam_im_inv {Γ} {Δ : Ctx Srt} {A A' B m m' c s s'} :
    Γ ;; Δ ⊢ .lam A m .im s ▷ .lam m' c s : .pi A' B .im s' ->
    ∃ sA, A' :: Γ ;; A' :⟨.im, sA⟩ Δ ⊢ m ▷ m' : B ∧ c = .keep := by
  intro er
  have ⟨B, sA, erm, eq, _⟩ := er.lam_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := er.toStatic.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := erm.ctx_inv
  have ⟨x, rd', rd⟩ := Static.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Static.Typed.unique ty1 ty2
  subst_vars; exists sA'; simp
  replace tyB := Static.Typed.conv_ctx eqA.sym tyA tyB
  apply Erased.conv_ctx eqA tyA'
  apply Erased.conv eqB.sym erm tyB

lemma Erased.lam_ex_inv {Γ} {Δ : Ctx Srt} {A A' B m m' c s s'} :
    Γ ;; Δ ⊢ .lam A m .ex s ▷ .lam m' c s : .pi A' B .ex s' ->
    ∃ rA sA, RSrt rA sA c ∧ A' :: Γ ;; A' :⟨rA, sA⟩ Δ ⊢ m ▷ m' : B := by
  intro er
  have ⟨B, rA, sA, rs, erm, eq⟩ := er.lam_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := er.toStatic.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := erm.ctx_inv
  have ⟨x, rd', rd⟩ := Static.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Static.Typed.unique ty1 ty2
  subst_vars; exists rA, sA'
  replace tyB := Static.Typed.conv_ctx eqA.sym tyA tyB
  and_intros
  . assumption
  . apply Erased.conv_ctx eqA tyA'
    apply Erased.conv eqB.sym erm tyB

lemma Erased.tup_im_inv {Γ} {Δ : Ctx Srt} {A B m m' n n' s s'} :
    Γ ;; Δ ⊢ .tup m n .im s ▷ .tup m' n' s : .sig A B .im s' ->
    Γ ;; Δ ⊢ m ▷ m' : A ∧ Γ ⊢ n : B.[m/] ∧ n' = .none ∧ s = s' := by
  intro er
  have ⟨A', B', erm, tyn, e, eq⟩ := er.tup_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := er.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace erm := Erased.conv eqA.sym erm tyA
  replace tyB := tyB.subst erm.toStatic; asimp at tyB
  simp; and_intros
  . assumption
  . apply Static.Typed.conv
    apply Static.Conv.subst _ eqB.sym
    assumption
    assumption

lemma Erased.tup_ex_inv {Γ} {Δ : Ctx Srt} {A B m m' n n' s s'} :
    Γ ;; Δ ⊢ .tup m n .ex s ▷ .tup m' n' s : .sig A B .ex s' ->
    ∃ Δ1 Δ2,
      Merge Δ1 Δ2 Δ ∧
      Γ ;; Δ1 ⊢ m ▷ m' : A ∧
      Γ ;; Δ2 ⊢ n ▷ n' : B.[m/] ∧ s = s' := by
  intro er
  have ⟨Δ1, Δ2, A', B', mrg, erm, ern, eq⟩ := er.tup_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := er.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  replace erm := Erased.conv eqA.sym erm tyA
  replace tyB := tyB.subst erm.toStatic; asimp at tyB
  exists Δ1, Δ2; simp; and_intros
  . assumption
  . assumption
  . apply Erased.conv
    apply Static.Conv.subst _ eqB.sym
    assumption
    assumption
