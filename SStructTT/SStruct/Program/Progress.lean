import SStructTT.SStruct.Logical.Progress
import SStructTT.SStruct.Program.Step
import SStructTT.SStruct.Program.Inversion
open ARS SStruct.Logical

namespace SStruct.Program
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Typed.pi_canonical {A B C m : Tm Srt} {r s} :
    [] ⊢ m :: C -> C === .pi A B r s -> Value m ->
    ∃ A n, m = .lam A n r s := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case lam_im A B m _ _ _ _ _ _ _  =>
    have ⟨_, _, eqA, eqB⟩ := Conv.pi_inj eq
    subst_vars; exists A, m
  case lam_ex A B m _ _ _ _ _ _ _ =>
    have ⟨_, _, eqA, eqB⟩ := Conv.pi_inj eq
    subst_vars; exists A, m
  case drop mrg _ _ _ _ =>
    subst_vars; cases mrg; aesop
  case conv ih =>
    apply ih <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.sig_canonical {A B C m : Tm Srt} {r s} :
    [] ⊢ m :: C -> C === .sig A B r s -> Value m ->
    ∃ m1 m2, m = .tup m1 m2 r s := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tup_im A0 B0 m n _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.sig_inj eq
    subst_vars; exists m, n
  case tup_ex A0 B0 m n _ _ _ _ _ _ _ _ =>
    have ⟨_, _, _, _⟩ := Conv.sig_inj eq
    subst_vars; exists m, n
  case drop mrg _ _ _ _ =>
    subst_vars; cases mrg; aesop
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.bool_canonical {C m : Tm Srt} :
    [] ⊢ m :: C -> C === .bool -> Value m -> m = .tt ∨ m = .ff := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case tt => simp
  case ff => simp
  case drop mrg _ _ _ _ =>
    subst_vars; cases mrg; aesop
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

lemma Typed.idn_canonical {A C m a b : Tm Srt} :
    [] ⊢ m :: C -> C === .idn A a b -> Value m -> ∃ n, m = .rfl n := by
  generalize e: [] = Δ
  intro ty eq vl; induction ty <;> try trivial
  all_goals try false_conv
  case drop mrg _ _ _ _ =>
    subst_vars; cases mrg; aesop
  case conv ihm =>
    apply ihm <;> try assumption
    apply Conv.trans <;> assumption

theorem Typed.progress {m A : Tm Srt} :
    [] ⊢ m :: A -> (∃ n, m ~>> n) ∨ Value m := by
  generalize e: [] = Δ
  intro ty; induction ty <;> (subst_vars; simp_all; try trivial)
  case lam_im => right; constructor
  case lam_ex => right; constructor
  case app_im n _ tym tyn ih =>
    match ih with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.app m n
      constructor; assumption
    | .inr vl =>
      have ⟨_, m, _⟩ := tym.pi_canonical Conv.R vl
      subst_vars; left; existsi m.[n/]; constructor
  case app_ex m n _ tym tyn ihm ihn mrg =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.app m n
      constructor; assumption
    | .inr vl =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; existsi Tm.app m n
        constructor; assumption
      | .inr _ =>
        have ⟨_, m, _⟩ := tym.pi_canonical Conv.R vl
        subst_vars; left; existsi m.[n/]
        constructor; assumption
  case tup_im m n s _ _ _ _ ih =>
    match ih with
    | .inl ⟨n, _⟩ =>
      left; existsi Tm.tup m n .im s
      constructor; assumption
    | .inr _ => right; constructor; assumption
  case tup_ex m n s _ _ _ ihm ihn mrg ty =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.tup m n .ex s
      constructor; assumption
    | .inr _ =>
      match ihn with
      | .inl ⟨n, _⟩ =>
        left; existsi Tm.tup m n .ex s
        constructor; assumption
      | .inr _ => right; constructor <;> assumption
  case prj_im C _ n _ _ _ _ _ tym ihn ihm mrg tyC =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.prj C m n
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars; left; existsi n.[m2,m1/]
      constructor; assumption
  case prj_ex C _ n _ _ _ _ _ tym ihn ihm mrg tyC =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.prj C m n
      constructor; assumption
    | .inr vl =>
      have ⟨m1, m2, _⟩ := tym.sig_canonical Conv.R vl
      subst_vars; left; existsi n.[m2,m1/]
      constructor; assumption
  case tt => right; constructor
  case ff => right; constructor
  case ite A m n1 n2 _ _ tym _ _ ihm _ _ mrg _ =>
    cases mrg; simp_all
    match ihm with
    | .inl ⟨m, _⟩ =>
      left; existsi Tm.ite A m n1 n2
      constructor; assumption
    | .inr vl =>
      cases tym.bool_canonical Conv.R vl with
      | inl => subst_vars; left; existsi n1; constructor
      | inr => subst_vars; left; existsi n2; constructor
  case drop mrg => cases mrg; aesop
  case rw m _ _ _ _ _ _ _ _ _ =>
    left; existsi m; apply Step.rw_elim
