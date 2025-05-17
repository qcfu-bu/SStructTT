import SStructTT.SStruct.Dynamic.Progress
import SStructTT.SStruct.Erasure.Preservation
open ARS Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.pi_canonical {A B C m : SStruct.Tm Srt} {m' r s} :
    [] ;; [] ⊢ m ▷ m' : C -> C === .pi A B r s -> Value m' ->
    ∃ A n n' c, m = .lam A n r s ∧ m' = .lam n' c s := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case lam_im A B m m' _ _ _ _ _ _ _  =>
    have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
    subst_vars; exists A, m, m', .keep
  case lam_ex A B m m' _ _ _ _ c rs _ _ _ _ =>
    have ⟨_, _, eqA, eqB⟩ := Static.Conv.pi_inj eq
    subst_vars; exists A, m, m', c
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
    subst_vars; exists m, m', n, .none
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
    [] ;; [] ⊢ m ▷ m' : A -> (∃ n', m' ~>> n') ∨ Value m' := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro er; induction er <;> (subst_vars; try trivial)
  case lam_im => right; constructor
  case lam_ex => right; constructor
  case app_im n _ _ erm ih =>
    simp_all
    match ih with
    | .inl ⟨m', _⟩ =>
      left; exists Tm.app m' .none
      constructor; assumption
    | .inr vl =>
      have ⟨_, m, m', c, e1, e2⟩ := erm.pi_canonical Conv.R vl
      subst_vars; left; exists m'.[.none/]
      constructor
      constructor
      cases c <;> simp
  case app_ex m m' n n' _ erm ern ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m', _⟩ =>
      left; exists Tm.app m' n'
      constructor; assumption
    | .inr vl =>
      match ihn with
      | .inl ⟨n', _⟩ =>
        left; exists Tm.app m' n'
        constructor; assumption
      | .inr _ =>
        have ⟨_, m, m', c, e1, e2⟩ := erm.pi_canonical Conv.R vl
        cases c with
        | keep =>
          subst_vars; left; exists m'.[n'/]
          constructor; assumption; simp
        | drop =>
          subst_vars; left; exists m'.[.none/]
          constructor; assumption; simp
  case tup_im m m' n s _ _ _ _ ih =>
    simp_all
    match ih with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m .none s
      constructor; assumption
    | .inr _ => right; aesop
  case tup_ex m m' n n' s _ _ _ _ ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m n' s
      constructor; assumption
    | .inr _ =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.tup m' n s
        constructor; assumption
      | .inr _ => right; constructor <;> assumption
  case proj_im C n n' _ _ _ _ _ _ c _ _ erm _ ihm _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj m n' c .keep
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m1', m2, m2', _, _⟩ := erm.sig_canonical Conv.R vl
      subst_vars; left; exists n'.[m2',c.ctrl m1'/]; aesop
  case proj_ex C _ _ n n' _ _ _ _ _ _ _ c1 c2 _ _ _ erm _ ihm _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj m n' c1 c2
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m1', m2, m2', _, _⟩ := erm.sig_canonical Conv.R vl
      subst_vars; left; exists n'.[c2.ctrl m2',c1.ctrl m1'/]; aesop
  case tt => right; constructor
  case ff => right; constructor
  case ite A m m' n1 n1' n2 n2' _ _ _ erm _ _ ihm _ _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m', _⟩ =>
      left; exists Tm.ite m' n1' n2'
      constructor; assumption
    | .inr vl =>
      match erm.bool_canonical Conv.R vl with
      | .inl ⟨e1, e2⟩ => subst_vars; left; exists n1'; constructor
      | .inr ⟨e1, e2⟩ => subst_vars; left; exists n2'; constructor
  case rw m n _ _ _ _ _ _ _ _ =>
    left; exists m; apply Step.rw_elim
  case conv ih => aesop
