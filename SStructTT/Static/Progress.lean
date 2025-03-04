import SStructTT.Static.Preservation
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

lemma Typed.pi_canonical {A B C m : Tm Srt} {r s} :
    [] ⊢ m : C -> C === .pi A B r s -> Value m ->
    ∃ A n, m = .lam A n r s := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case lam A0 B0 m _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.pi_inj eq
    subst_vars; exists A0, m
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.sig_canonical {A B C m : Tm Srt} {r s} :
    [] ⊢ m : C -> C === .sig A B r s -> Value m ->
    ∃ m1 m2, m = .tup m1 m2 r s := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tup A0 B0 m n _ _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.sig_inj eq
    subst_vars; exists m, n
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.bool_canonical {C m : Tm Srt} :
    [] ⊢ m : C -> C === .bool -> Value m -> m = .tt ∨ m = .ff := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tt => simp
  case ff => simp
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.idn_canonical {A C m a b : Tm Srt} :
    [] ⊢ m : C -> C === .idn A a b -> Value m -> ∃ n, m = .rfl n := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case rfl m _ _ => exists m
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

theorem Typed.progress {m A : Tm Srt} :
    [] ⊢ m : A -> (∃ n, m ~> n) ∨ Value m := by
  generalize e: [] = Γ
  intro ty; induction ty <;> (subst_vars; simp_all; try trivial)
  case srt => right; constructor
  case pi => right; constructor
  case lam => right; constructor
  case app n r _ tym tyn ihm ihn =>
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.app m n r
      constructor; assumption
    | .inr vl =>
      have ⟨A, m, _⟩ := tym.pi_canonical Conv.R vl
      subst_vars; left; exists m.[n/]; constructor
  case sig => right; constructor
  case tup m n r s _ _ _ _ _ ihm ihn =>
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m n r s
      constructor; assumption
    | .inr vl =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.tup m n r s
        constructor; assumption
      | .inr vl =>
        right; constructor
        . assumption
        . intro; assumption
  case proj C m n r _ _ _ _ tym _ ihm =>
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj C m n r
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars; left; exists n.[m2,m1/]; constructor
  case bool => right; constructor
  case tt => right; constructor
  case ff => right; constructor
  case ite A m n1 n2 _ _ _ tym _ _ ihm _ _ =>
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.ite A m n1 n2
      constructor; assumption
    | .inr vl =>
      cases Typed.bool_canonical tym Conv.R vl with
      | inl => subst_vars; left; exists n1; constructor
      | inr => subst_vars; left; exists n2; constructor
  case idn => right; constructor
  case rfl => right; constructor
  case rw A B m n _ _ _ _ _ _ tyn _ ihn =>
    match ihn with
    | .inl ⟨n, _⟩ =>
      left; exists Tm.rw A m n
      constructor; assumption
    | .inr vl =>
      have ⟨_, _⟩ := Typed.idn_canonical tyn Conv.R vl
      subst_vars; left; exists m; constructor
