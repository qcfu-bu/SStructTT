import SStructTT.MartinLof.Normalization
import SStructTT.MartinLof.Substitution
import SStructTT.SStruct.Static.Substitution
open ARS

namespace SStruct.Static
variable {Srt : Type}

@[simp]def interp : Tm Srt -> MartinLof.Tm
  | .var x => .var x
  | .srt _ i => .ty i
  | .pi A B _ _ => .pi (interp A) (interp B)
  | .lam A m _ _ => .lam (interp A) (interp m)
  | .app m n _ => .app (interp m) (interp n)
  | .sig A B _ _ => .sig (interp A) (interp B)
  | .tup m n _ _ => .tup (interp m) (interp n)
  | .proj A m n _ => .proj (interp A) (interp m) (interp n)
  | .bool => .bool
  | .tt => .tt
  | .ff => .ff
  | .ite A m n1 n2 => .ite (interp A) (interp m) (interp n1) (interp n2)
  | .idn A m n => .idn (interp A) (interp m) (interp n)
  | .rfl m => .rfl (interp m)
  | .rw A m n => .rw (interp A) (interp m) (interp n)

@[simp]def interp_ctx : Ctx Srt -> MartinLof.Ctx
  | [] => []
  | A :: Γ => interp A :: interp_ctx Γ

notation "[| " m " |]" => interp m
notation "[| " Γ " |]*" => interp_ctx Γ

lemma interp_ren_com {m : Tm Srt} {ξ} :
    [| m |].[ren ξ] = [| m.[ren ξ] |] := by
  induction m generalizing ξ <;> asimp
  case pi ihA ihB => rw[<-SubstLemmas.upren_up,ihA,ihB]; asimp
  case lam ihA ihm => rw[<-SubstLemmas.upren_up,ihA,ihm]; asimp
  case app ihm ihn => rw[ihm,ihn]; asimp
  case sig ihA ihB => rw[<-SubstLemmas.upren_up,ihA,ihB]; asimp
  case tup ihm ihn => rw[ihm,ihn]; asimp
  case proj ihA ihm ihn =>
    rw[show 2 = (1 + 1) by simp]
    rw[<-SubstLemmas.upn_comp]
    repeat rw[SubstLemmas.upn1_up]
    repeat rw[<-SubstLemmas.upren_up]
    rw[ihA,ihm,ihn]; asimp
  case ite ihA ihm ihn1 ihn2 =>
    rw[<-SubstLemmas.upren_up,ihA,ihm,ihn1,ihn2]; asimp
  case idn ihA ihm ihn => rw[ihA,ihm,ihn]; asimp
  case rfl ihm => rw[ihm]
  case rw ihA ihm ihn =>
    rw[show 2 = (1 + 1) by simp]
    rw[<-SubstLemmas.upn_comp]
    repeat rw[SubstLemmas.upn1_up]
    repeat rw[<-SubstLemmas.upren_up]
    rw[ihA,ihm,ihn]; asimp

def InterpSubst
  (σ : Var -> Tm Srt)
  (τ : Var -> MartinLof.Tm) : Prop := ∀ x, [| σ x |] = τ x

lemma interp_subst_up {σ : Var -> Tm Srt} {τ} :
    InterpSubst σ τ -> InterpSubst (up σ) (up τ) := by
  intro h x; induction x generalizing σ τ <;> asimp
  rw[<-h,interp_ren_com]

lemma interp_subst_com {m : Tm Srt} {σ τ} :
    InterpSubst σ τ -> [| m.[σ] |] = [| m |].[τ] := by
  intro h; induction m generalizing σ τ <;> asimp
  case var => aesop
  case pi ihA ihB => rw[ihA h,ihB (interp_subst_up h)]; asimp
  case lam ihA ihm => rw[ihA h,ihm (interp_subst_up h)]; asimp
  case app ihm ihn => rw[ihm h,ihn h]; asimp
  case sig ihA ihB => rw[ihA h,ihB (interp_subst_up h)]; asimp
  case tup ihm ihn => rw[ihm h,ihn h]; asimp
  case proj ihA ihm ihn =>
    rw[show 2 = (1 + 1) by simp]
    rw[<-SubstLemmas.upn_comp]
    repeat rw[SubstLemmas.upn1_up]
    rw[ihm h,
       ihA (interp_subst_up h),
       ihn (interp_subst_up (interp_subst_up h))]
    asimp
  case ite ihA ihm ihn1 ihn2 =>
    rw[ihA (interp_subst_up h),ihm h,ihn1 h,ihn2 h]; asimp
  case idn ihA ihm ihn => rw[ihA h,ihm h,ihn h]; asimp
  case rfl ihm => rw[ihm h]
  case rw ihA ihm ihn =>
    rw[show 2 = (1 + 1) by simp]
    rw[<-SubstLemmas.upn_comp]
    repeat rw[SubstLemmas.upn1_up]
    rw[ihm h, ihn h,
       ihA (interp_subst_up (interp_subst_up h))]
    asimp

lemma interp_step {m n : Tm Srt} :
    Step m n -> MartinLof.Step [| m |] [| n |] := by
  intro st; induction st <;> simp
  all_goals try (constructor; try assumption)
  case beta =>
    rw[interp_subst_com]
    . constructor
    . intro x; cases x <;> asimp
  case proj_elim =>
    rw[interp_subst_com]
    . constructor
    . intro x; rcases x with _ | ⟨_ | _⟩ <;> asimp

lemma interp_red {m n : Tm Srt} :
    Star Step m n -> Star MartinLof.Step [| m |] [| n |] := by
  intro rd; induction rd
  case R => constructor
  case SE =>
    apply Star.SE
    . assumption
    . apply interp_step; assumption

lemma interp_conv {m n : Tm Srt} :
    Conv Step m n -> Conv MartinLof.Step [| m |] [| n |] := by
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

lemma interp_has {Γ : Ctx Srt} {x A} :
    Has Γ x A -> MartinLof.Has [| Γ |]* x [| A |] := by
  intro hs; induction hs
  case zero =>
    simp; rw[interp_subst_com]
    . constructor
    . intro x; cases x <;> asimp
  case succ hs ih =>
    simp; rw[interp_subst_com]
    . constructor; assumption
    . intro x; cases x <;> asimp

variable [ord : SrtOrder Srt]

theorem Typed.toMartinLof {Γ : Ctx Srt} {m A} :
    Typed Γ m A -> MartinLof.Typed [| Γ |]* [| m |] [| A |] := by
  intro ty; induction ty using
    @Typed.rec _ ord (motive_2 := fun Γ _ => MartinLof.Wf [| Γ |]*)
  all_goals try (simp_all; try constructor <;> assumption)
  case var =>
    constructor
    . assumption
    . apply interp_has; assumption
  case app =>
    rw[interp_subst_com]
    . constructor <;> assumption
    . intro x; cases x <;> asimp
  case tup =>
    constructor <;> try assumption
    rwa[<-interp_subst_com]
    intro x; cases x <;> asimp
  case proj =>
    rw[interp_subst_com]
    . constructor <;> try assumption
      rw[<-interp_subst_com]
      . assumption
      . intro x; cases x <;> asimp
    . intro x; cases x <;> asimp
  case ite =>
    rw[interp_subst_com]
    . constructor <;> try assumption
      . rwa[<-interp_subst_com]
        intro x; cases x <;> asimp
      . rwa[<-interp_subst_com]
        intro x; cases x <;> asimp
    . intro x; cases x <;> asimp
  case rw =>
    rw[interp_subst_com]
    . constructor <;> try assumption
      repeat rw[<-interp_subst_com]
      . assumption
      . intro x; cases x <;> asimp
      . intro x; cases x <;> asimp
      . rwa[<-interp_subst_com]
        intro x; rcases x with _ | ⟨_ | _⟩ <;> asimp
    . intro x; rcases x with _ | ⟨_ | _⟩ <;> asimp
  case conv =>
    apply MartinLof.Typed.conv
    . apply interp_conv; assumption
    . assumption
    . assumption
