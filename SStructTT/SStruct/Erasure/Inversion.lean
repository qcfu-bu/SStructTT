import SStructTT.SStruct.Static.Normalize
import SStructTT.SStruct.Dynamic.Inversion
import SStructTT.SStruct.Erasure.Substitution
import SStructTT.SStruct.Dynamic.Step
open ARS

namespace SStruct.Erasure
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

inductive Rw

theorem Erased.validity {Δ : Ctx Srt} {A m m'} :
    Δ ⊢ m ▷ m' :: A -> ∃ s i, Δ.static ⊢ A : .srt s i := by
  intro erm; apply erm.toDynamic.validity

lemma Erased.lam_im_inv' {Δ : Ctx Srt} {A T m m' s} :
    Δ ⊢ .lam A m .im s ▷ .lam m' s :: T ->
    ∃ B sA,
      A :⟨.im, sA⟩ Δ ⊢ m ▷ m' :: B ∧
      T === .pi A B .im s := by
  generalize e1: SStruct.Tm.lam A m .im s = x
  generalize e2: Tm.lam m' s = y
  intro er; induction er generalizing A m m' s
  all_goals try trivial
  case lam_im B _ _ _ sA _ _ _ _ _ =>
    cases e1; cases e2; existsi B, sA; aesop
  case lam_ex => cases e1
  case conv eq1 _ _ ih =>
    have ⟨B, sA, erm, eq2⟩ := ih e1 e2
    existsi B, sA
    and_intros
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.lam_ex_inv' {Δ : Ctx Srt} {A T m m' s} :
    Δ ⊢ .lam A m .ex s ▷ .lam m' s :: T ->
    ∃ B sA,
      A :⟨.ex, sA⟩ Δ ⊢ m ▷ m' :: B ∧
      T === .pi A B .ex s := by
  generalize e1: SStruct.Tm.lam A m .ex s = x
  generalize e2: Tm.lam m' s = x
  intro er; induction er generalizing A m s
  all_goals try trivial
  case lam_im => cases e1
  case lam_ex B _ _ _ sA _ _ _ _ _ =>
    cases e1; cases e2; existsi B, sA; aesop
  case conv eq1 _ _ ih =>
    have ⟨B, sA, erm, eq2⟩ := ih e1 e2
    existsi B, sA
    and_intros
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.tup_im_inv' {Δ : Ctx Srt} {T m m' n n' s} :
    Δ ⊢ .tup m n .im s ▷ .tup m' n' s :: T ->
    ∃ A B,
      Δ ⊢ m ▷ m' :: A ∧
      Δ.static ⊢ n : B.[m/] ∧ n' = .null ∧
      T === .sig A B .im s := by
  generalize e1: SStruct.Tm.tup m n .im s = x
  generalize e2: Tm.tup m' n' s = y
  intro er; induction er generalizing m n s
  all_goals try trivial
  case tup_im A B _ _ _ _ _ _ _ _ _ =>
    cases e1; cases e2; existsi A, B; aesop
  case tup_ex => cases e1
  case conv eq1 _ _ ih =>
    have ⟨A, B, _, _, _, eq2⟩ := ih e1 e2
    existsi A, B
    and_intros
    . assumption
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.tup_ex_inv' {Δ : Ctx Srt} {T m m' n n' s} :
    Δ ⊢ .tup m n .ex s ▷ .tup m' n' s :: T ->
    ∃ Δ1 Δ2 A B,
      Merge Δ1 Δ2 Δ ∧
      Δ1 ⊢ m ▷ m' :: A ∧
      Δ2 ⊢ n ▷ n' :: B.[m/] ∧
      T === .sig A B .ex s := by
  generalize e1: SStruct.Tm.tup m n .ex s = x
  generalize e2: Tm.tup m' n' s = y
  intro er; induction er generalizing m n s
  all_goals try trivial
  case tup_im => cases e1
  case tup_ex Δ1 Δ2 Δ A B _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases e1; cases e2; existsi Δ1, Δ2, A, B; aesop
  case conv eq1 _ _ ih =>
    have ⟨Δ1, Δ2, A, B, mrg, _, _, eq2⟩ := ih e1 e2
    existsi Δ1, Δ2, A, B
    and_intros
    . assumption
    . assumption
    . assumption
    . apply Conv.trans
      apply Conv.sym eq1
      apply eq2

lemma Erased.lam_im_inv {Δ : Ctx Srt} {A A' B m m' s s'} :
    Δ ⊢ .lam A m .im s ▷ .lam m' s :: .pi A' B .im s' ->
    ∃ sA, A' :⟨.im, sA⟩ Δ ⊢ m ▷ m' :: B := by
  intro er
  have ⟨B, sA, erm, eq⟩ := er.lam_im_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := er.toStatic.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := erm.ctx_inv
  have ⟨x, rd', rd⟩ := Static.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Static.Typed.unique ty1 ty2
  subst_vars; existsi sA'
  replace tyB := Static.Typed.conv_ctx eqA.sym tyA tyB
  apply Erased.conv_ctx eqA tyA'
  apply Erased.conv eqB.sym erm tyB

lemma Erased.lam_ex_inv {Δ : Ctx Srt} {A A' B m m' s s'} :
    Δ ⊢ .lam A m .ex s ▷ .lam m' s :: .pi A' B .ex s' ->
    ∃ sA, A' :⟨.ex, sA⟩ Δ ⊢ m ▷ m' :: B := by
  intro er
  have ⟨B, sA, erm, eq⟩ := er.lam_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
  have ⟨s, i, tyP⟩ := er.toStatic.validity
  have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
  have ⟨sA', _, _, tyA'⟩ := tyB.ctx_inv
  obtain ⟨_, _, tyA⟩ := erm.ctx_inv
  have ⟨x, rd', rd⟩ := Static.Step.cr eqA
  have ty1 := tyA'.preservation' rd'
  have ty2 := tyA.preservation' rd
  have e := Static.Typed.unique ty1 ty2
  subst_vars; existsi sA'
  replace tyB := Static.Typed.conv_ctx eqA.sym tyA tyB
  apply Erased.conv_ctx eqA tyA'
  apply Erased.conv eqB.sym erm tyB

lemma Erased.tup_im_inv {Δ : Ctx Srt} {A B m m' n n' s s'} :
    Δ ⊢ .tup m n .im s ▷ .tup m' n' s :: .sig A B .im s' ->
    Δ ⊢ m ▷ m' :: A ∧ Δ.static ⊢ n : B.[m/] ∧ n' = .null ∧ s = s' := by
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

lemma Erased.tup_ex_inv {Δ : Ctx Srt} {A B m m' n n' s s'} :
    Δ ⊢ .tup m n .ex s ▷ .tup m' n' s :: .sig A B .ex s' ->
    ∃ Δ1 Δ2,
      Merge Δ1 Δ2 Δ ∧
      Δ1 ⊢ m ▷ m' :: A ∧
      Δ2 ⊢ n ▷ n' :: B.[m/] ∧ s = s' := by
  intro er
  have ⟨Δ1, Δ2, A', B', mrg, erm, ern, eq⟩ := er.tup_ex_inv'
  have ⟨_, _, eqA, eqB⟩ := Static.Conv.sig_inj eq
  subst_vars
  have ⟨s, i, tyS⟩ := er.validity
  have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
  have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
  rw[mrg.static] at tyA
  replace erm := Erased.conv eqA.sym erm tyA
  rw[mrg.static] at tyB
  replace tyB := tyB.subst erm.toStatic; asimp at tyB
  existsi Δ1, Δ2; simp; and_intros
  . assumption
  . assumption
  . apply Erased.conv
    apply Static.Conv.subst _ eqB.sym
    assumption
    rw[<-mrg.sym.static]
    rw[<-mrg.static] at tyB
    assumption

lemma Erased.null_preimage {Δ : Ctx Srt} {t B} :
    Δ ⊢ t ▷ .null :: B -> False := by
  generalize e: Tm.null = k
  intro er; induction er <;> trivial

lemma Erased.lam_preimage {B t : SStruct.Tm Srt} {m' s} :
    [] ⊢ t ▷ .lam m' s :: B ->
    ∃ A m r, t ~>>* .lam A m r s ∧ [] ⊢ .lam A m r s ▷ .lam m' s :: B := by
  generalize e1: [] = Δ
  generalize e2: Tm.lam m' s = Δ
  intro er; induction er <;> try trivial
  case lam_im A _ m _ _ _ _ _ _ _ _ =>
    subst_vars; cases e2
    existsi A, m, .im; and_intros
    . apply Star.R
    . constructor <;> assumption
  case lam_ex A B m s _ _ _ _ _ _ _ =>
    subst_vars; cases e2
    existsi A, m, .ex; and_intros
    . apply Star.R
    . constructor <;> assumption
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, tyA⟩ := tyn.closed_idn tyA
    have ⟨A, m, r, rd, er⟩ := ih
    existsi A, m, r; and_intros
    . apply Star.ES
      constructor
      assumption
    . apply Erased.conv <;> assumption
  case conv ih =>
    subst_vars; simp_all
    have ⟨A, m, r, td, er⟩ := ih
    existsi A, m, r; and_intros
    . assumption
    . apply Erased.conv <;> assumption

lemma Erased.tup_preimage {B t : SStruct.Tm Srt} {m' n' s} :
    [] ⊢ t ▷ .tup m' n' s :: B ->
    ∃ m n r, t ~>>* .tup m n r s ∧ [] ⊢ .tup m n r s ▷ .tup m' n' s :: B := by
  generalize e1: [] = Δ
  generalize e2: Tm.tup m' n' s = k
  intro er; induction er <;> try trivial
  case tup_im A _ m _ n _ _ _ _ _ _ =>
    subst_vars; cases e2
    existsi m, n, .im; and_intros
    . apply Star.R
    . constructor <;> assumption
  case tup_ex A _ m _ n _ _ _ _ _ _ _ _ _ =>
    subst_vars; cases e2
    existsi m, n, .ex; and_intros
    . apply Star.R
    . constructor <;> assumption
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, tyA⟩ := tyn.closed_idn tyA
    have ⟨A, m, r, rd, er⟩ := ih
    existsi A, m, r; and_intros
    . apply Star.ES
      constructor
      assumption
    . apply Erased.conv <;> assumption
  case conv ih =>
    subst_vars; simp_all
    have ⟨A, m, r, td, er⟩ := ih
    existsi A, m, r; and_intros
    . assumption
    . apply Erased.conv <;> assumption

lemma Erased.tt_preimage {B t : SStruct.Tm Srt} :
    [] ⊢ t ▷ .tt :: B -> t ~>>* .tt := by
  generalize e1: [] = Δ
  generalize e2: Tm.tt = k
  intro er; induction er <;> try trivial
  case tt => subst_vars; apply Star.R
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars; simp_all
    apply Star.ES
    constructor
    assumption
  case conv ih => subst_vars; simp[ih]

lemma Erased.ff_preimage {B t : SStruct.Tm Srt} :
    [] ⊢ t ▷ .ff :: B -> t ~>>* .ff := by
  generalize e1: [] = Δ
  generalize e2: Tm.ff = k
  intro er; induction er <;> try trivial
  case ff => subst_vars; apply Star.R
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars; simp_all
    apply Star.ES
    constructor
    assumption
  case conv ih => subst_vars; simp[ih]
