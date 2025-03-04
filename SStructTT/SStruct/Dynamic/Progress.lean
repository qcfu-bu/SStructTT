import SStructTT.SStruct.Static.Progress
import SStructTT.SStruct.Dynamic.Step
import SStructTT.SStruct.Dynamic.Inversion
open ARS SStruct.Static

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Typed.pi_canonical {A B C m : Tm Srt} {r s} :
    [] ;; [] ⊢ m : C -> C === .pi A B r s -> Value m ->
    ∃ A n, m = .lam A n r s := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case lam_im A B m _ _ _ _ _ _ _  =>
    have ⟨_, _, eqA, eqB⟩ := Conv.pi_inj eq
    subst_vars; exists A, m
  case lam_ex A B m _ _ _ _ _ _ _ _ _ =>
    have ⟨_, _, eqA, eqB⟩ := Conv.pi_inj eq
    subst_vars; exists A, m
  case conv ih =>
    apply ih <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.sig_canonical {A B C m : Tm Srt} {r s} :
    [] ;; [] ⊢ m : C -> C === .sig A B r s -> Value m ->
    ∃ m1 m2, m = .tup m1 m2 r s := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tup_im A0 B0 m n _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.sig_inj eq
    subst_vars; exists m, n
  case tup_ex A0 B0 m n _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.sig_inj eq
    subst_vars; exists m, n
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.bool_canonical {C m : Tm Srt} :
    [] ;; [] ⊢ m : C -> C === .bool -> Value m -> m = .tt ∨ m = .ff := by
  generalize e1: [] = Γ
  generalize e2: [] = Γ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tt => simp
  case ff => simp
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.idn_canonical {A C m a b : Tm Srt} :
    [] ;; [] ⊢ m : C -> C === .idn A a b -> Value m -> ∃ n, m = .rfl n := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

theorem Typed.progress {m A : Tm Srt} :
    [] ;; [] ⊢ m : A -> (∃ n, m ~>> n) ∨ Value m := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty; induction ty <;> (subst_vars; simp_all; try trivial)
  case lam_im => right; constructor
  case lam_ex => right; constructor
  case app_im n _ _ tym ih =>
    match ih with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.app m n .im
      constructor; assumption
    | .inr vl =>
      have ⟨_, m, _⟩ := tym.pi_canonical Conv.R vl
      subst_vars; left; exists m.[n/]; constructor
  case app_ex m n _ tym tyn ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.app m n .ex
      constructor; assumption
    | .inr vl =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.app m n .ex
        constructor; assumption
      | .inr _ =>
        have ⟨_, m, _⟩ := tym.pi_canonical Conv.R vl
        subst_vars; left; exists m.[n/]
        constructor; assumption
  case tup_im m n s _ _ _ _ ih =>
    match ih with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m n .im s
      constructor; assumption
    | .inr _ => right; constructor; assumption
  case tup_ex m n s _ _ _ _ ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.tup m n .ex s
      constructor; assumption
    | .inr _ =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; exists Tm.tup m n .ex s
        constructor; assumption
      | .inr _ => right; constructor <;> assumption
  case proj_im C _ n _ _ _ _ _ _ _ _ tym _ ihm mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj C m n .im
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars; left; exists n.[m2,m1/]
      constructor; assumption
  case proj_ex C _ n _ _ _ _ _ _ _ _ _ _ tym _ ihm mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.proj C m n .ex
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars; left; exists n.[m2,m1/]
      constructor; assumption
  case tt => right; constructor
  case ff => right; constructor
  case ite A _ n1 n2 _ _ _ tym _ _ ihm _ _ mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; exists Tm.ite A m n1 n2
      constructor; assumption
    | .inr vl =>
      cases tym.bool_canonical Conv.R vl with
      | inl => subst_vars; left; exists n1; constructor
      | inr => subst_vars; left; exists n2; constructor
  case rw m n _ _ _ _ _ _ _ _ =>
    left; exists m; constructor
