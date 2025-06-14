import SStructTT.SStruct.Dynamic.Progress
import SStructTT.SStruct.Erasure.Preservation
open ARS Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.pi_canonical {A B C m : SStruct.Tm Srt} {m' r s} :
    [] ⊢ m ▷ m' :: C -> C === .pi A B r s -> Value m' ->
    ∃ n', m' = .lam n' s := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case lam_im A B m m' _ _ _ _ _ _ _  =>
    have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
    subst_vars; exists m'
  case lam_ex A B m m' _ _ _ _ _ _ _ =>
    have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
    subst_vars; exists m'
  case rw tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, ty⟩ := tyn.closed_idn tyA
    apply ih; apply Conv.trans eq; assumption
  case conv ih =>
    apply ih <;> try assumption
    apply Conv.trans <;> assumption

lemma Erased.sig_canonical {A B C m : SStruct.Tm Srt} {m' r s} :
    [] ⊢ m ▷ m' :: C -> C === .sig A B r s -> Value m' ->
    ∃ m1' m2', m' = .tup m1' m2' s  := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tup_im A0 B0 m n n' _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Static.Conv.sig_inj eq
    subst_vars; exists .null, n'
  case tup_ex A0 B0 m m' n n' _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Static.Conv.sig_inj eq
    subst_vars; exists m', n'
  case rw tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, ty⟩ := tyn.closed_idn tyA
    apply ih; apply Conv.trans eq; assumption
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Erased.bool_canonical {C m : SStruct.Tm Srt} {m'} :
    [] ⊢ m ▷ m' :: C -> C === .bool -> Value m' -> m' = .tt ∨ m' = .ff := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tt => simp
  case ff => simp
  case rw tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, ty⟩ := tyn.closed_idn tyA
    apply ih; apply Conv.trans eq; assumption
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

theorem Erased.progress {A m} {m' : Tm Srt} :
    [] ⊢ m ▷ m' :: A ->
    (∃ n', m' ~>> n') ∨ (∃ v, Red0 m' v ∧ Value v) := by
  generalize e: [] = Δ
  intro er; induction er <;> (subst_vars; try trivial)
  case lam_im m' s _ _ _ _ _ _ =>
    right; existsi .lam m' s; and_intros
    . constructor
    . constructor
  case lam_ex m' s _ _ _ _ _ _ =>
    right; existsi .lam m' s; and_intros
    . constructor
    . constructor
  case app_im n _ _ erm _ ih =>
    simp_all
    match ih with
    | .inl ⟨m', _⟩ =>
      left; existsi Tm.app m' .null
      apply Step.app_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preservation0' rd
      have ⟨m', e⟩ := erm.pi_canonical Conv.R vl
      subst_vars; left; existsi m'.[.null/]
      constructor; and_intros
      . apply Red0.app rd Star.R
      . aesop
  case app_ex m m' n n' _ erm ern ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m', _⟩ =>
      left; existsi Tm.app m' n'
      apply Step.app_M; assumption
    | .inr ⟨v1, rd1, vl1⟩ =>
      replace erm := erm.preservation0' rd1
      match ihn with
      | .inl ⟨n', _⟩ =>
        left; existsi Tm.app m' n'
        apply Step.app_N; assumption
      | .inr ⟨v2, rd2, vl2⟩ =>
        replace ern := ern.preservation0' rd2
        have ⟨m', e⟩ := erm.pi_canonical Conv.R vl1
        subst_vars; left; existsi m'.[v2/]
        constructor; and_intros
        . apply Red0.app rd1 rd2
        . aesop
  case tup_im m n n' s _ _ _ _ ih =>
    simp_all
    match ih with
    | .inl ⟨n, _⟩ =>
      left; existsi Tm.tup .null n s
      apply Step.tup_N; assumption
    | .inr ⟨v, rd, vl⟩ =>
      right; existsi .tup .null v s; and_intros
      . apply Red0.tup Star.R rd
      . aesop
  case tup_ex m m' n n' s _ _ _ ihm ihn mrg _ =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.tup m n' s
      apply Step.tup_M; assumption
    | .inr ⟨v1, rd1, vl1⟩ =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; existsi Tm.tup m' n s
        apply Step.tup_N; assumption
      | .inr ⟨v2, rd2, vl2⟩ =>
        right; existsi .tup v1 v2 s; and_intros
        . apply Red0.tup rd1 rd2
        . aesop
  case prj_im C m m' n n' _ _ _ _ _ erm _ ihm ihn mrg _ =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.prj m n'
      apply Step.prj_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preservation0' rd
      have ⟨m1', m2', _⟩ := erm.sig_canonical Conv.R vl
      subst_vars; left; existsi n'.[m2',m1'/]
      constructor; and_intros
      . apply Red0.prj rd
      . aesop
  case prj_ex C m m' n n' _ _ _ _ _ erm _ ihm _ mrg _ =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.prj m n'
      apply Step.prj_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preservation0' rd
      have ⟨m1', m2', _⟩ := erm.sig_canonical Conv.R vl
      subst_vars; left; existsi n'.[m2',m1'/]
      constructor; and_intros
      . apply Red0.prj rd
      . aesop
  case tt => right; existsi .tt; aesop
  case ff => right; existsi .ff; aesop
  case ite A m m' n1 n1' n2 n2' _ _  erm _ _ ihm _ _ mrg _ =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m', _⟩ =>
      left; existsi Tm.ite m' n1' n2'
      apply Step.ite_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preservation0' rd
      cases erm.bool_canonical Conv.R vl with
      | inl =>
        subst_vars; left; existsi n1'
        constructor; and_intros
        . apply Red0.ite rd
        . constructor
      | inr =>
        subst_vars; left; existsi n2'
        constructor; and_intros
        . apply Red0.ite rd
        . constructor
  case drop s lw h erm ern ihm ihn mrg =>
    cases mrg; simp_all
    match ihn with
    | .inl ⟨n', st⟩ =>
      left; existsi n'; apply Step.drop st
    | .inr ⟨v, rd, vl⟩ =>
      right; existsi v;
      constructor
      . apply Star.ES
        constructor
        assumption
      . assumption
  case rw => aesop
  case conv => aesop
