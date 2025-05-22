import SStructTT.SStruct.Dynamic.Progress
import SStructTT.SStruct.Erasure.Preservation
open ARS Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.pi_canonical {A B C m : SStruct.Tm Srt} {m' r s} :
    [] ;; [] ⊢ m ▷ m' : C -> C === .pi A B r s -> Value m' ->
    ∃ A n n', m = .lam A n r s ∧ m' = .lam n' s := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case lam_im A B m m' _ _ _ _ _ _ _  =>
    have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
    subst_vars; exists A, m, m'
  case lam_ex A B m m' _ _ _ _ _ _ _ =>
    have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
    subst_vars; exists A, m, m'
  case conv ih =>
    apply ih <;> try assumption
    apply Conv.trans <;> assumption

lemma Erased.sig_canonical {A B C m : SStruct.Tm Srt} {m' r s} :
    [] ;; [] ⊢ m ▷ m' : C -> C === .sig A B r s -> Value m' ->
    ∃ m1 m1' m2 m2', m = .tup m1 m2 r s ∧ m' = .tup m1' m2' s  := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tup_im A0 B0 m m' n _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Static.Conv.sig_inj eq
    subst_vars; exists m, m', n, .null
  case tup_ex A0 B0 m m' n n' _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Static.Conv.sig_inj eq
    subst_vars; exists m, m', n, n'
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Erased.bool_canonical {C m : SStruct.Tm Srt} {m'} :
    [] ;; [] ⊢ m ▷ m' : C -> C === .bool -> Value m' ->
      (m = .tt ∧ m' = .tt) ∨ (m = .ff ∧ m' = .ff) := by
  generalize e1: [] = Γ
  generalize e2: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tt => simp
  case ff => simp
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

theorem Erased.progress {A m} {m' : Tm Srt} :
    [] ;; [] ⊢ m ▷ m' : A ->
      (∃ n', m' ~>> n') ∨ (∃ v, Drops m' v ∧ Value v) := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro er; induction er <;> (subst_vars; try trivial)
  case lam_im m' s _ _ _ _ _ _ =>
    right; exists .lam m' s; and_intros
    . constructor
    . constructor
  case lam_ex m' s _ _ _ _ _ _ =>
    right; exists .lam m' s; and_intros
    . constructor
    . constructor
  case app_im n _ _ erm ih =>
    simp_all
    match ih with
    | .inl ⟨m', _⟩ =>
      left; exists Tm.app m' .null
      apply Step.app_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preserve_drops rd
      have ⟨_, m, m', e1, e2⟩ := erm.pi_canonical Conv.R vl
      subst_vars; left; exists m'.[.null/]
      constructor
      . apply Drops.app rd Star.R
      . aesop
  case app_ex m m' n n' _ erm ern ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m', _⟩ =>
      left; exists Tm.app m' n'
      apply Step.app_M; assumption
    | .inr ⟨v1, rd1, vl1⟩ =>
      replace erm := erm.preserve_drops rd1
      match ihn with
      | .inl ⟨n', _⟩ =>
        left; exists Tm.app m' n'
        apply Step.app_N; assumption
      | .inr ⟨v2, rd2, vl2⟩ =>
        replace ern := ern.preserve_drops rd2
        have ⟨_, m, m', e1, e2⟩ := erm.pi_canonical Conv.R vl1
        subst_vars; left; exists m'.[v2/]
        constructor
        . apply Drops.app rd1 rd2
        . aesop
  case tup_im m m' n s _ _ _ _ ih =>
    simp_all
    match ih with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m .null s
      apply Step.tup_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      right; exists .tup v .null s; and_intros
      . apply Drops.tup rd Star.R
      . aesop
  case tup_ex m m' n n' s _ _ _ _ ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m n' s
      apply Step.tup_M; assumption
    | .inr ⟨v1, rd1, vl1⟩ =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.tup m' n s
        apply Step.tup_N; assumption
      | .inr ⟨v2, rd2, vl2⟩ =>
        right; exists .tup v1 v2 s; and_intros
        . apply Drops.tup rd1 rd2
        . aesop
  case prj_im C m m' n n' _ _ _ _ _ _ erm _ ihm _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.prj m n'
      apply Step.prj_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preserve_drops rd
      have ⟨m1, m1', m2, m2', _, _⟩ := erm.sig_canonical Conv.R vl
      subst_vars; left; exists n'.[m2',m1'/]
      constructor
      . apply Drops.prj rd
      . aesop
  case prj_ex C m m' n n' _ _ _ _ _ _ erm _ ihm _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.prj m n'
      apply Step.prj_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preserve_drops rd
      have ⟨m1, m1', m2, m2', _, _⟩ := erm.sig_canonical Conv.R vl
      subst_vars; left; exists n'.[m2',m1'/]
      constructor
      . apply Drops.prj rd
      . aesop
  case tt => right; exists .tt; aesop
  case ff => right; exists .ff; aesop
  case ite A m m' n1 n1' n2 n2' _ _ _ erm _ _ ihm _ _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m', _⟩ =>
      left; exists Tm.ite m' n1' n2'
      apply Step.ite_M; assumption
    | .inr ⟨v, rd, vl⟩ =>
      replace erm := erm.preserve_drops rd
      match erm.bool_canonical Conv.R vl with
      | .inl ⟨e1, e2⟩ =>
        subst_vars; left; exists n1'; constructor
        . apply Drops.ite rd
        . constructor
      | .inr ⟨e1, e2⟩ =>
        subst_vars; left; exists n2'; constructor
        . apply Drops.ite rd
        . constructor
  case drop s lw h erm ern ihm ihn mrg =>
    cases mrg; simp_all
    match ihn with
    | .inl ⟨n', st⟩ =>
      left; exists n'; apply Step.drop st
    | .inr ⟨v, rd, vl⟩ =>
      right; exists v;
      constructor
      . apply Star.ES
        constructor
        assumption
      . assumption
  case rw m n _ _ _ _ _ _ _ _ =>
    left; exists m; constructor
    . apply Star.R
    . constructor
  case conv ih => aesop
