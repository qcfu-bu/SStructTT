import SStructTT.Static.Preservation
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

inductive Value : Tm Srt -> Prop where
  | var x : Value (.var x)
  | srt s i : Value (.srt s i)
  | pi0 A B s : Value (.pi0 A B s)
  | pi1 A B s : Value (.pi1 A B s)
  | lam0 A m s : Value (.lam0 A m s)
  | lam1 A m s : Value (.lam1 A m s)
  | sig0 A B s : Value (.sig0 A B s)
  | sig1 A B s : Value (.sig1 A B s)
  | tup0 m n s :
    Value m ->
    Value (.tup0 m n s)
  | tup1 m n s :
    Value m ->
    Value n ->
    Value (.tup1 m n s)
  | bool : Value .bool
  | tt : Value .tt
  | ff : Value .ff
  | idn A m n : Value (.idn A m n)
  | rfl m : Value (.rfl m)

lemma Typed.pi0_canonical {A B C m : Tm Srt} {s} :
    [] ⊢ m : C -> C === .pi0 A B s -> Value m ->
    ∃ A n, m = .lam0 A n s := by
  generalize e: [] = Γ
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case srt => intro eq; false_conv eq
  case var hs _ => subst_vars; cases hs
  case pi0 => intro eq; false_conv eq
  case pi1 => intro eq; false_conv eq
  case lam0 _ A0 B0 m _ _ _ _ _ _ _ =>
    intro eq _
    have ⟨_, _, _⟩ := Conv.pi0_inj eq
    subst_vars; exists A0, m
  case lam1 => intro eq; false_conv eq
  case app0 => intro _ vl; cases vl
  case app1 => intro _ vl; cases vl
  case sig0 => intro eq; false_conv eq
  case sig1 => intro eq; false_conv eq
  case tup0 => intro eq; false_conv eq
  case tup1 => intro eq; false_conv eq
  case proj0 => intro _ vl; cases vl
  case proj1 => intro _ vl; cases vl
  case bool => intro eq; false_conv eq
  case tt => intro eq; false_conv eq
  case ff => intro eq; false_conv eq
  case ite => intro _ vl; cases vl
  case idn => intro eq; false_conv eq
  case rfl => intro eq; false_conv eq
  case rw => intro _ vl; cases vl
  case conv ihm _ =>
    intro eq vl
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption

lemma Typed.pi1_canonical {A B C m : Tm Srt} {s} :
    [] ⊢ m : C -> C === .pi1 A B s -> Value m ->
    ∃ A n, m = .lam1 A n s := by
  generalize e: [] = Γ
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case srt => intro eq; false_conv eq
  case var hs _ => subst_vars; cases hs
  case pi0 => intro eq; false_conv eq
  case pi1 => intro eq; false_conv eq
  case lam0 => intro eq; false_conv eq
  case lam1 _ A0 B0 m _ _ _ _ _ _ _ =>
    intro eq _
    have ⟨_, _, _⟩ := Conv.pi1_inj eq
    subst_vars; exists A0, m
  case app0 => intro _ vl; cases vl
  case app1 => intro _ vl; cases vl
  case sig0 => intro eq; false_conv eq
  case sig1 => intro eq; false_conv eq
  case tup0 => intro eq; false_conv eq
  case tup1 => intro eq; false_conv eq
  case proj0 => intro _ vl; cases vl
  case proj1 => intro _ vl; cases vl
  case bool => intro eq; false_conv eq
  case tt => intro eq; false_conv eq
  case ff => intro eq; false_conv eq
  case ite => intro _ vl; cases vl
  case idn => intro eq; false_conv eq
  case rfl => intro eq; false_conv eq
  case rw => intro _ vl; cases vl
  case conv ihm _ =>
    intro eq vl
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption

lemma Typed.sig0_canonical {A B C m : Tm Srt} {s} :
    [] ⊢ m : C -> C === .sig0 A B s -> Value m ->
    ∃ m1 m2, m = .tup0 m1 m2 s := by
  generalize e: [] = Γ
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case srt => intro eq; false_conv eq
  case var hs _ => subst_vars; cases hs
  case pi0 => intro eq; false_conv eq
  case pi1 => intro eq; false_conv eq
  case lam0 => intro eq; false_conv eq
  case lam1 => intro eq; false_conv eq
  case app0 => intro _ vl; cases vl
  case app1 => intro _ vl; cases vl
  case sig0 => intro eq; false_conv eq
  case sig1 => intro eq; false_conv eq
  case tup0 _ A0 B0 m n _ _ _ _ _ _ _ _ =>
    intro eq _
    have ⟨_, _, _⟩ := Conv.sig0_inj eq
    subst_vars; exists m, n
  case tup1 => intro eq; false_conv eq
  case proj0 => intro _ vl; cases vl
  case proj1 => intro _ vl; cases vl
  case bool => intro eq; false_conv eq
  case tt => intro eq; false_conv eq
  case ff => intro eq; false_conv eq
  case ite => intro _ vl; cases vl
  case idn => intro eq; false_conv eq
  case rfl => intro eq; false_conv eq
  case rw => intro _ vl; cases vl
  case conv ihm _ =>
    intro eq vl
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption

lemma Typed.sig1_canonical {A B C m : Tm Srt} {s} :
    [] ⊢ m : C -> C === .sig1 A B s -> Value m ->
    ∃ m1 m2, m = .tup1 m1 m2 s := by
  generalize e: [] = Γ
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case srt => intro eq; false_conv eq
  case var hs _ => subst_vars; cases hs
  case pi0 => intro eq; false_conv eq
  case pi1 => intro eq; false_conv eq
  case lam0 => intro eq; false_conv eq
  case lam1 => intro eq; false_conv eq
  case app0 => intro _ vl; cases vl
  case app1 => intro _ vl; cases vl
  case sig0 => intro eq; false_conv eq
  case sig1 => intro eq; false_conv eq
  case tup0 => intro eq; false_conv eq
  case tup1 _ A0 B0 m n _ _ _ _ _ _ _ _ =>
    intro eq _
    have ⟨_, _, _⟩ := Conv.sig1_inj eq
    subst_vars; exists m, n
  case proj0 => intro _ vl; cases vl
  case proj1 => intro _ vl; cases vl
  case bool => intro eq; false_conv eq
  case tt => intro eq; false_conv eq
  case ff => intro eq; false_conv eq
  case ite => intro _ vl; cases vl
  case idn => intro eq; false_conv eq
  case rfl => intro eq; false_conv eq
  case rw => intro _ vl; cases vl
  case conv ihm _ =>
    intro eq vl
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption

lemma Typed.bool_canonical {C m : Tm Srt} :
    [] ⊢ m : C -> C === .bool -> Value m -> m = .tt ∨ m = .ff := by
  generalize e: [] = Γ
  intro ty; induction ty
  all_goals try trivial
  case srt => intro eq; false_conv eq
  case var hs _ => subst_vars; cases hs
  case pi0 => intro eq; false_conv eq
  case pi1 => intro eq; false_conv eq
  case lam0 => intro eq; false_conv eq
  case lam1 => intro eq; false_conv eq
  case app0 => intro _ vl; cases vl
  case app1 => intro _ vl; cases vl
  case sig0 => intro eq; false_conv eq
  case sig1 => intro eq; false_conv eq
  case tup0 => intro eq; false_conv eq
  case tup1 => intro eq; false_conv eq
  case proj0 => intro _ vl; cases vl
  case proj1 => intro _ vl; cases vl
  case bool => intro eq; false_conv eq
  case tt => intros; left; rfl
  case ff => intros; right; rfl
  case ite => intro _ vl; cases vl
  case idn => intro eq; false_conv eq
  case rfl => intro eq; false_conv eq
  case rw => intro _ vl; cases vl
  case conv ihm _ =>
    intro eq vl
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption

lemma Typed.idn_canonical {A C m a b : Tm Srt} :
    [] ⊢ m : C -> C === .idn A a b -> Value m -> ∃ n, m = .rfl n := by
  generalize e: [] = Γ
  intro ty; induction ty
  all_goals try trivial
  case srt => intro eq; false_conv eq
  case var hs _ => subst_vars; cases hs
  case pi0 => intro eq; false_conv eq
  case pi1 => intro eq; false_conv eq
  case lam0 => intro eq; false_conv eq
  case lam1 => intro eq; false_conv eq
  case app0 => intro _ vl; cases vl
  case app1 => intro _ vl; cases vl
  case sig0 => intro eq; false_conv eq
  case sig1 => intro eq; false_conv eq
  case tup0 => intro eq; false_conv eq
  case tup1 => intro eq; false_conv eq
  case proj0 => intro _ vl; cases vl
  case proj1 => intro _ vl; cases vl
  case bool => intro eq; false_conv eq
  case tt => intro eq; false_conv eq
  case ff => intro eq; false_conv eq
  case ite => intro _ vl; cases vl
  case idn => intro eq; false_conv eq
  case rfl m _ _ => intros; exists m
  case rw => intro _ vl; cases vl
  case conv ihm _ =>
    intro eq vl
    apply ihm
    . assumption
    . apply Conv.trans <;> assumption
    . assumption

theorem Typed.progress {m A : Tm Srt} :
    [] ⊢ m : A -> (∃ n, m ~> n) ∨ Value m := by
  generalize e: [] = Γ
  intro ty; induction ty
  all_goals try trivial
  case srt => right; constructor
  case var => right; constructor
  case pi0 => right; constructor
  case pi1 => right; constructor
  case lam0 => right; constructor
  case lam1 => right; constructor
  case app0 _ n _ tym tyn ihm ihn =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.app m n
      constructor; assumption
    | .inr vl =>
      have ⟨A, m, _⟩ := tym.pi0_canonical Conv.R vl
      subst_vars
      left; exists m.[n/]
      constructor
  case app1 _ n _ tym tyn ihm ihn =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.app m n
      constructor; assumption
    | .inr vl =>
      have ⟨A, m, _⟩ := tym.pi1_canonical Conv.R vl
      subst_vars
      left; exists m.[n/]
      constructor
  case sig0 => right; constructor
  case sig1 => right; constructor
  case tup0 m n s _ _ _ _ _ ihm ihn =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup0 m n s
      constructor; assumption
    | .inr vl =>
      right; constructor; assumption
  case tup1 m n s _ _ _ _ _ ihm ihn =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup1 m n s
      constructor; assumption
    | .inr vl =>
      match ihn (Eq.refl _) with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.tup1 m n s
        constructor; assumption
      | .inr vl =>
        right; constructor <;> assumption
  case proj0 C m n _ _ _ _ tym _ _ ihm _ =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj C m n
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig0_canonical Conv.R vl
      subst_vars
      left; exists n.[m2,m1/]
      constructor
  case proj1 C m n _ _ _ _ tym _ _ ihm _ =>
    subst_vars
    match ihm (Eq.refl _) with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj C m n
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig1_canonical Conv.R vl
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
