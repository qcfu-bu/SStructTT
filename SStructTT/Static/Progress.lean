import SStructTT.Static.Preservation
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

inductive Value : Tm Srt -> Prop where
  | srt s i : Value (.srt s i)
  | pi A B r s : Value (.pi A B r s)
  | lam A m r s : Value (.lam A m r s)
  | sig A B r s : Value (.sig A B r s)
  | tup m n r s :
    Value m ->
    (r = .ex -> Value n) ->
    Value (.tup m n r s)
  | bool : Value .bool
  | tt : Value .tt
  | ff : Value .ff
  | idn A m n : Value (.idn A m n)
  | rfl m : Value (.rfl m)

lemma Typed.pi_canonical {A B C m : Tm Srt} {r s} :
    [] ⊢ m : C -> C === .pi A B r s -> Value m ->
    ∃ A n, m = .lam A n r s := by
  generalize e: [] = Γ
  intro ty; induction ty generalizing A B s
  all_goals try (intro eq vl; false_conv)
  case var hs _ => subst_vars; cases hs
  case lam A0 B0 m _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.pi_inj eq
    subst_vars; exists A0, m
  case app => cases vl
  case proj => cases vl
  case ite => cases vl
  case rw => cases vl
  case conv ihm _ =>
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption
  all_goals trivial

lemma Typed.sig_canonical {A B C m : Tm Srt} {r s} :
    [] ⊢ m : C -> C === .sig A B r s -> Value m ->
    ∃ m1 m2, m = .tup m1 m2 r s := by
  generalize e: [] = Γ
  intro ty; induction ty generalizing A B s
  all_goals try (intro eq vl; false_conv)
  case var hs _ => subst_vars; cases hs
  case app => cases vl
  case tup A0 B0 m n _ _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.sig_inj eq
    subst_vars; exists m, n
  case proj => cases vl
  case ite => cases vl
  case rw => cases vl
  case conv ihm _ =>
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption
  all_goals trivial

lemma Typed.bool_canonical {C m : Tm Srt} :
    [] ⊢ m : C -> C === .bool -> Value m -> m = .tt ∨ m = .ff := by
  generalize e: [] = Γ
  intro ty; induction ty
  all_goals try (intro eq vl; false_conv)
  case var hs _ => subst_vars; cases hs
  case app => cases vl
  case proj => cases vl
  case tt => left; rfl
  case ff => right; rfl
  case ite => cases vl
  case rw => cases vl
  case conv ihm _ =>
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption
  all_goals trivial

lemma Typed.idn_canonical {A C m a b : Tm Srt} :
    [] ⊢ m : C -> C === .idn A a b -> Value m -> ∃ n, m = .rfl n := by
  generalize e: [] = Γ
  intro ty; induction ty
  all_goals try (intro eq vl; false_conv)
  case var hs _ => subst_vars; cases hs
  case app => cases vl
  case proj => cases vl
  case ite => cases vl
  case rfl m _ _ => exists m
  case rw => cases vl
  case conv ihm _ =>
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption
  all_goals trivial

theorem Typed.progress {m A : Tm Srt} :
    [] ⊢ m : A -> (∃ n, m ~> n) ∨ Value m := by
  generalize e: [] = Γ
  intro ty; induction ty
  all_goals try trivial
  case srt => right; constructor
  case var hs _ => subst_vars; cases hs
  case pi => right; constructor
  case lam => right; constructor
  case app _ n r _ tym tyn ihm ihn =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.app m n r
      constructor; assumption
    | .inr vl =>
      have ⟨A, m, _⟩ := tym.pi_canonical Conv.R vl
      subst_vars
      left; exists m.[n/]
      constructor
  case sig => right; constructor
  case tup m n r s _ _ _ _ _ ihm ihn =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m n r s
      constructor; assumption
    | .inr vl =>
      match ihn (Eq.refl _) with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.tup m n r s
        constructor; assumption
      | .inr vl =>
        right; constructor
        . assumption
        . intro; assumption
  case proj C m n r _ _ _ _ tym _ _ ihm _ =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj C m n r
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars
      left; exists n.[m2,m1/]
      constructor
  case bool => right; constructor
  case tt => right; constructor
  case ff => right; constructor
  case ite A m n1 n2 _ _ _ tym _ _ _ ihm _ _ =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.ite A m n1 n2
      constructor; assumption
    | .inr vl =>
      cases Typed.bool_canonical tym Conv.R vl with
      | inl => subst_vars; left; exists n1; constructor
      | inr => subst_vars; left; exists n2; constructor
  case idn => right; constructor
  case rfl => right; constructor
  case rw A _ m n _ _ _ _ _ _ tyn _ _ ihn =>
    subst_vars
    match ihn (Eq.refl _) with
    | .inl ⟨n, _⟩ =>
      left; exists Tm.rw A m n
      constructor; assumption
    | .inr vl =>
      have ⟨_, _⟩ := Typed.idn_canonical tyn Conv.R vl
      subst_vars
      left; exists m
      constructor
  case conv => subst_vars; aesop
