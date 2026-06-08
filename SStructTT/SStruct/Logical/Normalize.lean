import SStructTT.MLTT.Normalize
import SStructTT.MLTT.Substitution
import SStructTT.SStruct.Logical.Progress
open ARS
open Autosubst Autosubst.Notation

namespace SStruct.Logical
variable {Srt : Type}

@[simp]def interp : Tm Srt -> MLTT.Tm
  | .var x => .var_Tm x
  | .srt _ i => .ty i
  | .pi A B _ _ => .pi (interp A) (interp B)
  | .lam A m _ _ => .lam (interp A) (interp m)
  | .app m n => .app (interp m) (interp n)
  | .sig A B _ _ => .sig (interp A) (interp B)
  | .tup m n _ _ => .tup (interp m) (interp n)
  | .prj A m n => .prj (interp A) (interp m) (interp n)
  | .bool => .bool
  | .tt => .tt
  | .ff => .ff
  | .ite A m n1 n2 => .ite (interp A) (interp m) (interp n1) (interp n2)
  | .idn A m n => .idn (interp A) (interp m) (interp n)
  | .rfl m => .rfl (interp m)
  | .rw A m n => .rw (interp A) (interp m) (interp n)
  | .bot => .bot
  | .exf A m => .exf (interp A) (interp m)

@[simp]def interp_ctx : Ctx Srt -> MLTT.Ctx
  | [] => []
  | A :: Γ => interp A :: interp_ctx Γ

notation "[| " m " |]" => interp m
notation "[| " Γ " |]*" => interp_ctx Γ

lemma interp_ren_com {m : Tm Srt} {ξ : Var -> Var} :
    [| m |]⟨ξ⟩ = [| m⟨ξ⟩ |] := by
  induction m generalizing ξ <;>
    (simp only [interp]; asimp; simp only [interp]) <;>
    simp_all

def InterpSubst
  (σ : Var -> Tm Srt)
  (τ : Var -> MLTT.Tm) : Prop := ∀ x, [| σ x |] = τ x

lemma interp_subst_up {σ : Var -> Tm Srt} {τ} :
    InterpSubst σ τ -> InterpSubst (⇑σ) (⇑τ) := by
  intro h x; induction x generalizing σ τ
  case zero => asimp; simp
  case succ n _ =>
    asimp
    show [| (σ n)⟨↑⟩ |] = (τ n)⟨↑⟩
    rw[<-interp_ren_com, h]

lemma interp_subst_com {m : Tm Srt} {σ : Var -> Tm Srt} {τ} :
    InterpSubst σ τ -> [| m[σ] |] = [| m |][τ] := by
  intro h; induction m generalizing σ τ <;>
    (simp only [interp]; asimp; try simp only [interp])
  case var_Tm => exact h _
  case pi ihA ihB => congr 1; exacts [ihA h, ihB (interp_subst_up h)]
  case lam ihA ihm => congr 1; exacts [ihA h, ihm (interp_subst_up h)]
  case app ihm ihn => congr 1; exacts [ihm h, ihn h]
  case sig ihA ihB => congr 1; exacts [ihA h, ihB (interp_subst_up h)]
  case tup ihm ihn => congr 1; exacts [ihm h, ihn h]
  case prj ihA ihm ihn =>
    congr 1
    · exact ihA (interp_subst_up h)
    · exact ihm h
    · apply ihn; intro x
      match x with
      | 0 => simp
      | 1 => asimp; simp
      | n+2 => asimp; rw[<-interp_ren_com, h]
  case ite ihA ihm ihn1 ihn2 =>
    congr 1; exacts [ihA (interp_subst_up h), ihm h, ihn1 h, ihn2 h]
  case idn ihA ihm ihn => congr 1; exacts [ihA h, ihm h, ihn h]
  case rfl ihm => congr 1; exact ihm h
  case rw ihA ihm ihn =>
    congr 1
    · apply ihA; intro x
      match x with
      | 0 => simp
      | 1 => asimp; simp
      | n+2 => asimp; rw[<-interp_ren_com, h]
    · exact ihm h
    · exact ihn h
  case exf ihA ihm => congr 1; exacts [ihA (interp_subst_up h), ihm h]

lemma interp_step {m n : Tm Srt} :
    Step m n -> MLTT.Step [| m |] [| n |] := by
  intro st; induction st <;> simp
  all_goals try (constructor; try assumption)
  case beta =>
    rw[interp_subst_com]
    . constructor
    . intro x; cases x <;> asimp; simp
  case prj_elim =>
    rw[interp_subst_com]
    . constructor
    . intro x; rcases x with _ | ⟨_ | _⟩ <;> asimp; simp

lemma interp_red {m n : Tm Srt} :
    Star Step m n -> Star MLTT.Step [| m |] [| n |] := by
  intro rd; induction rd
  case R => constructor
  case SE =>
    apply Star.SE
    . assumption
    . apply interp_step; assumption

lemma interp_conv {m n : Tm Srt} :
    Conv Step m n -> Conv MLTT.Step [| m |] [| n |] := by
  intro eq; induction eq
  case R => constructor
  case SE =>
    apply Conv.SE
    . assumption
    . apply interp_step; assumption
  case SEi =>
    apply Conv.SEi
    . assumption
    . apply interp_step; assumption

lemma interp_has {Γ : Ctx Srt} {A x} :
    Has Γ x A -> MLTT.Has [| Γ |]* x [| A |] := by
  intro hs; induction hs
  case zero =>
    simp; rw[<-interp_ren_com]; constructor
  case succ hs ih =>
    simp; rw[<-interp_ren_com]; constructor; assumption

lemma interp_sn' {m : MLTT.Tm} :
    SN MLTT.Step m ->
    ∀ {n : Tm Srt}, [| n |] = m -> SN Step n := by
  intro sn; induction sn
  case intro ih =>
    by_contra h; simp at h
    have ⟨x, _, nn⟩ := h; subst_vars
    have ⟨y, st, nn⟩ := SN.negate nn
    have sn := ih (interp_step st) rfl
    contradiction

lemma interp_sn {m : Tm Srt} :
    SN MLTT.Step [| m |] -> SN Step m := by
  intro sn; apply interp_sn' <;> aesop

variable [ord : SrtOrder Srt]

theorem Typed.toMLTT {Γ : Ctx Srt} {A m} :
    Typed Γ m A -> MLTT.Typed [| Γ |]* [| m |] [| A |] := by
  intro ty; induction ty using
    @Typed.rec _ ord (motive_2 := fun Γ _ => MLTT.Wf [| Γ |]*)
  all_goals try (simp_all; try constructor <;> assumption)
  case var =>
    constructor
    . assumption
    . apply interp_has; assumption
  case app =>
    rw[interp_subst_com]
    . constructor <;> assumption
    . intro x; cases x <;> asimp; simp
  case tup =>
    constructor <;> try assumption
    rwa[<-interp_subst_com]
    intro x; cases x <;> asimp; simp
  case prj =>
    rw[interp_subst_com]
    . constructor <;> try assumption
      rw[<-interp_subst_com]
      . assumption
      . intro x; cases x <;> asimp <;> simp
    . intro x; cases x <;> asimp; simp
  case ite =>
    rw[interp_subst_com]
    . constructor <;> try assumption
      . rwa[<-interp_subst_com]
        intro x; cases x <;> asimp <;> simp
      . rwa[<-interp_subst_com]
        intro x; cases x <;> asimp <;> simp
    . intro x; cases x <;> asimp; simp
  case exf =>
    rw[interp_subst_com]
    . constructor <;> assumption
    . intro x; cases x <;> asimp; simp
  case rw =>
    rw[interp_subst_com]
    . constructor <;> try assumption
      . simp only [interp_ren_com]; assumption
      . rw[<-interp_subst_com]
        . assumption
        . intro x; rcases x with _ | ⟨_ | _⟩ <;> asimp <;> simp
    . intro x; rcases x with _ | ⟨_ | _⟩ <;> asimp; simp
  case conv =>
    apply MLTT.Typed.conv
    . apply interp_conv; assumption
    . assumption
    . assumption

theorem Typed.normalize {Γ : Ctx Srt} {A m} :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  replace ty := ty.toMLTT
  have sn := ty.normalize
  apply interp_sn sn

-- corollary of strong normalization
lemma Typed.red_value {A m : Tm Srt} :
    [] ⊢ m : A -> ∃ n, Logical.Value n ∧ m ~>* n := by
  intro ty; have sn := ty.normalize
  induction sn generalizing A
  case intro n h ih =>
    match ty.progress with
    | .inl ⟨n, st⟩ =>
      have ⟨n', vl, rd⟩ := ih st (ty.preservation st)
      existsi n'; and_intros
      . assumption
      . apply Star.ES <;> assumption
    | .inr vl =>
      existsi n; and_intros
      . assumption
      . apply Star.R

/--
The empty type `bot` is not derivable: there is no closed term of type `bot`.

Proof via strong normalization. By `red_value` (a corollary of `Typed.normalize`),
any closed well-typed term reduces to a `Value`; subject reduction (`preservation'`)
keeps it at type `bot`; but `bot_canonical` shows no `Value` inhabits `bot`.
-/
theorem Typed.bot_not_derivable {m : Tm Srt} : ¬ ([] ⊢ m : .bot) := by
  intro ty
  have ⟨n, vl, rd⟩ := ty.red_value
  exact (ty.preservation' rd).bot_canonical Conv.R vl

lemma Typed.closed_idn {A B m a b : Tm Srt} {s i} :
    [] ⊢ m : B.idn a b ->
    [.idn B⟨↑⟩ a⟨↑⟩ (.var 0), B] ⊢ A : Tm.srt s i ->
    A[.rfl a,a/] === A[m,b/] ∧ [] ⊢ A[m, b/] : .srt s i := by
  intro tym tyA
  have ⟨m', vl, rd⟩ := Typed.red_value tym
  have tym' := tym.preservation' rd
  have ⟨a', _⟩ := tym'.idn_canonical Conv.R vl; subst_vars
  have ⟨_, _, tyI⟩ := tym.validity
  have ⟨_, tya, tyb, eq⟩ := tyI.idn_inv
  have ⟨_, _⟩ := Conv.srt_inj eq; subst_vars
  have ⟨tya', eq1, eq2⟩ := tym'.rfl_inv
  have sc : SConv (.rfl a .: a .: Tm.var_Tm) (m .: b .: Tm.var_Tm) := by
    intro x; match x with
    | .zero =>
      asimp; apply Conv.trans;
      apply (Conv.rfl eq1).sym
      apply (Star.conv rd).sym
    | .succ .zero => asimp; apply Conv.trans eq1.sym eq2
    | .succ (.succ _) => asimp; constructor
  have tyA : [] ⊢ A[m, b/] : .srt s i := by
    rw[show Tm.srt s i = (Tm.srt s i)[m,b/] by asimp]
    apply Typed.substitution
    . assumption
    . apply AgreeSubst.intro; asimp; assumption
      apply AgreeSubst.intro; asimp; assumption
      apply AgreeSubst.refl
      apply tym.toWf
  and_intros
  . apply Conv.compat _ sc
  . assumption
