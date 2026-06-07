import SStructTT.MLTT.Preservation
open ARS

namespace MLTT

@[scoped aesop safe [constructors]]
inductive Value : Tm -> Prop where
  | ty i : Value (.ty i)
  | pi A B : Value (.pi A B)
  | lam A m : Value (.lam A m)
  | sig A B : Value (.sig A B)
  | tup m n :
    Value m ->
    Value n ->
    Value (.tup m n)
  | bool : Value .bool
  | tt : Value .tt
  | ff : Value .ff
  | idn A m n : Value (.idn A m n)
  | rfl m : Value (.rfl m)
  | bot : Value .bot

lemma Typed.pi_canonical {A B C m : Tm} :
    [] ⊢ m : C -> C === .pi A B -> Value m ->
    ∃ A n, m = .lam A n := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try mltt_false_conv
  case lam Γ0 A0 B0 m0 iA tyA tym ihA ihm =>
    exact ⟨A0, m0, Eq.refl _⟩
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.sig_canonical {A B C m : Tm} :
    [] ⊢ m : C -> C === .sig A B -> Value m ->
    ∃ m1 m2, m = .tup m1 m2 := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try mltt_false_conv
  case tup Γ0 A0 B0 m0 n0 i tyS tym tyn ihS ihm ihn =>
    exact ⟨m0, n0, Eq.refl _⟩
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.bool_canonical {C m : Tm} :
    [] ⊢ m : C -> C === .bool -> Value m -> m = .tt ∨ m = .ff := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try mltt_false_conv
  case tt => simp
  case ff => simp
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.idn_canonical {A C m a b : Tm} :
    [] ⊢ m : C -> C === .idn A a b -> Value m -> ∃ n, m = .rfl n := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try mltt_false_conv
  case rfl m _ _ => exists m
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.bot_canonical {C m : Tm} :
    [] ⊢ m : C -> C === .bot -> Value m -> False := by
  generalize e: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try mltt_false_conv
  case conv ihm _ =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

theorem Typed.progress {m A : Tm} :
    [] ⊢ m : A -> (∃ n, m ~> n) ∨ Value m := by
  generalize e: [] = Γ
  intro ty; induction ty <;> (subst_vars; simp_all; try trivial)
  case srt => right; constructor
  case pi => right; constructor
  case lam => right; constructor
  case app A B m n tym tyn ihm ihn =>
    match ihm with
    | .inl ⟨m', st⟩ =>
      exact .inl ⟨Tm.app m' n, Step.app_M n st⟩
    | .inr vl =>
      have ⟨A', m', e⟩ := tym.pi_canonical Conv.R vl
      subst_vars
      exact .inl ⟨m'.[n/], Step.beta A' m' n⟩
  case sig => right; constructor
  case tup A B m n i tyS tym tyn ihS ihm ihn =>
    match ihm with
    | .inl ⟨m', st⟩ =>
      exact .inl ⟨Tm.tup m' n, Step.tup_M n st⟩
    | .inr vl =>
      match ihn with
      | .inl ⟨n', st⟩ =>
        exact .inl ⟨Tm.tup m n', Step.tup_N m st⟩
      | .inr vl =>
        right; constructor
        . assumption
        . assumption
  case prj A B C m n iC tyC tym tyn ihm =>
    match ihm with
    | .inl ⟨m', st⟩ =>
      exact .inl ⟨Tm.prj C m' n, Step.prj_M C n st⟩
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars
      exact .inl ⟨n.[m2,m1/], Step.prj_elim C m1 m2 n⟩
  case bool => right; constructor
  case tt => right; constructor
  case ff => right; constructor
  case ite A m n1 n2 i tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    match ihm with
    | .inl ⟨m', st⟩ =>
      exact .inl ⟨Tm.ite A m' n1 n2, Step.ite_M A n1 n2 st⟩
    | .inr vl =>
      cases Typed.bool_canonical tym Conv.R vl with
      | inl =>
        subst_vars
        exact .inl ⟨n1, Step.ite_tt A n1 n2⟩
      | inr =>
        subst_vars
        exact .inl ⟨n2, Step.ite_ff A n1 n2⟩
  case idn => right; constructor
  case rfl => right; constructor
  case rw A B m n a b i tyA tym tyn ihm ihn =>
    match ihn with
    | .inl ⟨n', st⟩ =>
      exact .inl ⟨Tm.rw A m n', Step.rw_N A m st⟩
    | .inr vl =>
      have ⟨_, _⟩ := Typed.idn_canonical tyn Conv.R vl
      subst_vars
      exact .inl ⟨m, Step.rw_elim A m _⟩
  case bot => right; constructor
  case exf A m i tyA tym ihm =>
    match ihm with
    | .inl ⟨m', st⟩ =>
      exact .inl ⟨Tm.exf A m', Step.exf_M A st⟩
    | .inr vl =>
      exact (Typed.bot_canonical tym Conv.R vl).elim
