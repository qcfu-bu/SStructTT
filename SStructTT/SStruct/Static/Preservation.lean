import SStructTT.SStruct.Static.Inversion
open ARS

namespace SStruct.Static
variable {Srt : Type} [ord : SrtOrder Srt]

theorem Typed.preservation {Γ : Ctx Srt} {A m m'} :
    Γ ⊢ m : A -> m ~> m' -> Γ ⊢ m' : A := by
  intro ty st; induction ty generalizing m'
  all_goals try trivial
  case pi ihA ihB =>
    cases st
    case pi_A st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case pi_B st =>
      constructor
      . assumption
      . apply ihB st
  case lam tym ihA ihm =>
    have ⟨_, _, _⟩ := tym.validity
    cases st
    case lam_A st =>
      apply Typed.conv
      . apply Conv.pi
        apply Conv.onei st
        constructor
      . constructor
        apply ihA st
        apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
      . constructor <;> assumption
    case lam_M st =>
      constructor
      . assumption
      . apply ihm st
  case app tym tyn ihm ihn =>
    cases st
    case app_M st =>
      apply Typed.app
      . apply ihm st
      . assumption
    case app_N st =>
      have ⟨_, _, tyP⟩ := tym.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.app
        assumption
        apply ihn st
      . apply tyB.subst tyn
    case beta =>
      replace ⟨tym, _⟩ := tym.lam_inv
      apply tym.subst tyn
  case sig ihA ihB =>
    cases st
    case sig_A st =>
      constructor
      . assumption
      . assumption
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case sig_B st =>
      constructor
      . assumption
      . assumption
      . assumption
      . apply ihB st
  case tup tyS _ _ _ ihm ihn =>
    cases st
    case tup_M st =>
      replace ihm := ihm st
      have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
      constructor
      . assumption
      . assumption
      . apply Typed.conv
        apply Conv.subst1
        apply Conv.one st
        assumption
        apply tyB.subst ihm
    case tup_N st =>
      constructor
      . assumption
      . assumption
      . apply ihn st
  case prj Γ A B C _ _ r s sC iC tyC tym tyn ihC ihm ihn =>
    have ⟨s, _, wf, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB, eq⟩ := tyS.sig_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    have ⟨_, _⟩ := Conv.srt_inj eq
    subst_vars; clear eq
    cases st
    case prj_A C' st =>
      replace ihC := ihC st
      have wf := tyn.toWf
      have tyC' : (.sig A B r s).[shift 2] :: B :: A :: Γ ⊢ C'.[ren (upren (.+2))] :
                  (.srt sC iC).[ren (upren (.+2))] := by
        apply Typed.renaming
        . assumption
        . apply AgreeRen.cons
          assumption
          rw[show (.+2) = (id !>> (.+1)) !>> (.+1) by funext; rfl]
          aesop (rule_sets := [rename])
      have typ : B :: A :: Γ ⊢ .tup (.var 1) (.var 0) r s : (.sig A B r s).[shift 2] := by
        asimp; apply Typed.tup
        . have ty := (tyS.weaken tyA).weaken tyB
          asimp at ty; assumption
        . rw[show A.[shift 2] = A.[shift 1].[shift 1] by asimp]
          constructor <;> aesop
        . asimp; constructor <;> aesop
      replace tyC' := tyC'.subst typ; asimp at tyC'; clear typ
      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . apply Typed.prj ihC tym
        apply Typed.conv
        apply Conv.subst
        apply Conv.one st
        assumption
        assumption
      . apply tyC.subst tym
    case prj_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.prj tyC (ihm st) tyn
      . apply tyC.subst tym
    case prj_N => apply Typed.prj <;> aesop
    case prj_elim m1 m2 r s =>
      have ⟨tym1, tym2, _, _⟩ := tym.tup_inv; subst_vars
      rw[show C.[.tup m1 m2 r s/]
            = C.[.tup (.var 1) (.var 0) r s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.intro tym2
      constructor; asimp; assumption
      apply AgreeSubst.refl wf
  case ite tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    cases st
    case ite_A st =>
      have wf := tym.toWf
      replace ihA := ihA st
      have tyAm := ihA.subst tym; asimp at tyAm
      have tyA1 := ihA.subst (Typed.tt wf); asimp at tyA1
      have tyA2 := ihA.subst (Typed.ff wf); asimp at tyA2
      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . constructor <;> try assumption
        . apply Typed.conv <;> try assumption
          apply Conv.subst
          apply Conv.one st
        . apply Typed.conv <;> try assumption
          apply Conv.subst
          apply Conv.one st
      . apply tyA.subst tym
    case ite_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . constructor <;> try assumption
        apply ihm st
      . apply tyA.subst tym
    case ite_N1 st =>
      constructor <;> try assumption
      apply ihn1 st
    case ite_N2 st =>
      constructor <;> try assumption
      apply ihn2 st
    case ite_tt => assumption
    case ite_ff => assumption
  case idn ihA ihm ihn =>
    cases st
    case idn_A st =>
      replace ihA := ihA st
      constructor
      . assumption
      . apply Typed.conv <;> try assumption
        apply Conv.one st
      . apply Typed.conv <;> try assumption
        apply Conv.one st
    case idn_M => constructor <;> aesop
    case idn_N => constructor <;> aesop
  case rfl tym ihm =>
    have ⟨_, _, _⟩ := tym.validity
    cases st
    case rfl_M st =>
      apply Typed.conv
      . apply Conv.idn
        constructor
        apply Conv.onei st
        apply Conv.onei st
      . constructor
        apply ihm st
      . constructor <;> assumption
  case rw Γ A B m n a b s i tyA tym tyn ihA ihm ihn =>
    have wf := tym.toWf
    have ⟨_, _, tyI⟩ := tyn.validity
    have ⟨_, tya, _, _⟩ := tyI.idn_inv
    have ⟨_, _, _⟩ := tya.validity
    cases st
    case rw_A A' st =>
      have : Γ ⊢ A'.[.rfl a, a/] : .srt s i := by
        rw[show .srt s i = (.srt s i).[.rfl a,a/] by asimp]
        apply Typed.substitution
        . apply ihA st
        . apply AgreeSubst.intro
          asimp; constructor; assumption
          apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.refl; assumption
      have : Γ ⊢ A.[n,b/] : .srt s i := by
        rw[show .srt s i = (.srt s i).[n,b/] by asimp]
        apply Typed.substitution
        . assumption
        . apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.refl; assumption
      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . constructor
        apply ihA st
        apply tym.conv
        apply Conv.subst
        apply Conv.one st
        assumption
        assumption
      . assumption
    case rw_M st => constructor <;> aesop
    case rw_N n' st =>
      have : SConv (n' .: b .: ids) (n .: b .: ids) := by
        intro x; cases x with
        | zero => asimp; apply Conv.onei st
        | succ => asimp; constructor
      have : Γ ⊢ A.[n,b/] : .srt s i := by
        rw[show .srt s i = (.srt s i).[n,b/] by asimp]
        apply Typed.substitution
        . assumption
        . apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.refl; assumption
      apply Typed.conv
      . apply Conv.compat
        assumption
      . constructor <;> try assumption
        apply ihn st
      . assumption
    case rw_elim c =>
      have ⟨_, eq1, eq2⟩ := tyn.rfl_inv
      have : SConv (.rfl a .: a .: ids) (.rfl c .: b .: ids) := by
        intro x; match x with
        | .zero => asimp; apply Conv.rfl (eq1.sym)
        | .succ .zero => asimp; apply Conv.trans (eq1.sym) eq2
        | .succ (.succ _) => asimp; constructor
      have : Γ ⊢ A.[.rfl c,b/] : .srt s i := by
        rw[show .srt s i = (.srt s i).[.rfl c,b/] by asimp]
        apply Typed.substitution
        . assumption
        . apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.intro
          asimp; assumption
          apply AgreeSubst.refl
          apply tyn.toWf
      apply Typed.conv
      . apply Conv.compat; assumption
      . assumption
      . assumption
  case conv eq _ tyB ihm _ =>
    have tym := ihm st
    apply Typed.conv eq tym tyB

theorem Typed.preservation' {Γ : Ctx Srt} {A m n} :
    Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A := by
  intro ty rd
  induction rd generalizing Γ A
  case R => assumption
  case SE rd st ih =>
    apply (ih ty).preservation st
