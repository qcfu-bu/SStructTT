import SStructTT.Static.Inversion
import Init.Prelude
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

theorem Typed.preservation {Γ : Ctx Srt} {A m n} :
    Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A := by
  intro ty
  induction ty generalizing n
  all_goals try trivial
  case srt => intro st; cases st
  case var => intro st; cases st
  case pi0 ihA ihB =>
    intro st; cases st
    case pi0_A st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case pi0_B st =>
      constructor
      . assumption
      . apply ihB st
  case pi1 ihA ihB =>
    intro st; cases st
    case pi1_A st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case pi1_B st =>
      constructor
      . assumption
      . apply ihB st
  case lam0 tym ihA ihm =>
    have ⟨_, _, _⟩ := tym.validity
    intro st; cases st
    case lam0_A st =>
      apply Typed.conv
      . apply Conv.pi0
        apply Conv.onei st
        constructor
      . constructor
        apply ihA st
        apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
      . constructor <;> assumption
    case lam0_M st =>
      constructor
      . assumption
      . apply ihm st
  case lam1 tym ihA ihm =>
    have ⟨_, _, _⟩ := tym.validity
    intro st; cases st
    case lam1_A st =>
      apply Typed.conv
      . apply Conv.pi1
        apply Conv.onei st
        constructor
      . constructor
        apply ihA st
        apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
      . constructor <;> assumption
    case lam1_M st =>
      constructor
      . assumption
      . apply ihm st
  case app0 tym tyn ihm ihn =>
    have ⟨_, _, tyP⟩ := tym.validity
    have ⟨_, _, _, tyB, _⟩ := tyP.pi0_inv
    intro st; cases st
    case app_M st =>
      apply Typed.app0
      . apply ihm st
      . assumption
    case app_N st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.app0
        assumption
        apply ihn st
      . apply tyB.subst tyn
    case beta0 =>
      replace ⟨tym, _⟩ := tym.lam0_inv; subst_vars
      have ⟨_, _, _, tyA⟩ := tym.ctx_inv
      replace tyB := tyB.subst tyn; asimp at tyB
      apply tym.subst tyn
    case beta1 =>
      exfalso; apply tym.lam1_pi0_false; constructor
  case app1 tym tyn ihm ihn =>
    have ⟨_, _, tyP⟩ := tym.validity
    have ⟨_, _, _, tyB, _⟩ := tyP.pi1_inv
    intro st; cases st
    case app_M st =>
      apply Typed.app1
      . apply ihm st
      . assumption
    case app_N st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.app1
        assumption
        apply ihn st
      . apply tyB.subst tyn
    case beta0 =>
      exfalso; apply tym.lam0_pi1_false; constructor
    case beta1 =>
      replace ⟨tym, _⟩ := tym.lam1_inv; subst_vars
      have ⟨_, _, _, tyA⟩ := tym.ctx_inv
      replace tyB := tyB.subst tyn; asimp at tyB
      apply tym.subst tyn
  case sig0 ihA ihB =>
    intro st; cases st
    case sig0_A st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case sig0_B st =>
      constructor
      . assumption
      . apply ihB st
  case sig1 ihA ihB =>
    intro st; cases st
    case sig1_A st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case sig1_B st =>
      constructor
      . assumption
      . apply ihB st
  case tup0 tyS _ _ _ ihm ihn =>
    intro st; cases st
    case tup0_M st =>
      replace ihm := ihm st
      have ⟨_, _, _, tyB, _⟩ := tyS.sig0_inv
      constructor
      . assumption
      . assumption
      . apply Typed.conv
        apply Conv.subst1
        apply Conv.one st
        assumption
        apply tyB.subst ihm
    case tup0_N st =>
      constructor
      . assumption
      . assumption
      . apply ihn st
  case tup1 tyS _ _ _ ihm ihn =>
    intro st; cases st
    case tup1_M st =>
      replace ihm := ihm st
      have ⟨_, _, _, tyB, _⟩ := tyS.sig1_inv
      constructor
      . assumption
      . assumption
      . apply Typed.conv
        apply Conv.subst1
        apply Conv.one st
        assumption
        apply tyB.subst ihm
    case tup1_N st =>
      constructor
      . assumption
      . assumption
      . apply ihn st
  case proj0 Γ A B C _ _ s sC iC tyC tym tyn ihC ihm ihn =>
    have ⟨s, _, wf, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB, eq⟩ := tyS.sig0_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    have ⟨_, _⟩ := Conv.srt_inj eq
    subst_vars; clear eq
    intro st; cases st
    case proj_A C' st =>
      replace ihC := ihC st
      have wf := tyn.toWf
      have tyC' : (.sig0 A B s).[shift 2] :: B :: A :: Γ ⊢ C'.[ren (upren (.+2))] :
                  (.srt sC iC).[ren (upren (.+2))] := by
        apply Typed.renaming
        . assumption
        . apply AgreeRen.cons
          assumption
          rw[show (.+2) = (id !>> (.+1)) !>> (.+1) by funext; rfl]
          aesop (rule_sets := [rename])
      have typ : B :: A :: Γ ⊢ .tup0 (.var 1) (.var 0) s : (.sig0 A B s).[shift 2] := by
        asimp; apply Typed.tup0
        . rw[show Tm.sig0 A.[shift 2] B.[up (shift 2)] s
                = (Tm.sig0 A B s).[shift 1].[shift 1] by asimp]
          have := (tyS.weaken tyA).weaken tyB
          assumption
        . rw[show A.[shift 2] = A.[shift 1].[shift 1] by asimp]
          constructor <;> aesop
        . asimp; constructor <;> aesop
      replace tyC' := tyC'.subst typ; asimp at tyC'; clear typ
      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . apply Typed.proj0 ihC tym
        apply Typed.conv
        apply Conv.subst
        apply Conv.one st
        assumption
        assumption
      . apply tyC.subst tym
    case proj_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.proj0 tyC (ihm st) tyn
      . apply tyC.subst tym
    case proj_N => apply Typed.proj0 <;> aesop
    case proj0 m1 m2 s =>
      have ⟨tym1, tym2, _⟩ := tym.tup0_inv; subst_vars
      rw[show C.[.tup0 m1 m2 s/]
            = C.[.tup0 (.var 1) (.var 0) s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.wk tym2
      constructor; asimp; assumption
      apply AgreeSubst.refl wf
    case proj1 =>
      exfalso; apply tym.tup1_sig0_false; constructor
  case proj1 Γ A B C _ _ s sC iC tyC tym tyn ihC ihm ihn =>
    have ⟨s, _, wf, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB, eq⟩ := tyS.sig1_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    have ⟨_, _⟩ := Conv.srt_inj eq
    subst_vars; clear eq
    intro st; cases st
    case proj_A C' st =>
      replace ihC := ihC st
      have wf := tyn.toWf
      have tyC' : (.sig1 A B s).[shift 2] :: B :: A :: Γ ⊢ C'.[ren (upren (.+2))] :
                  (.srt sC iC).[ren (upren (.+2))] := by
        apply Typed.renaming
        . assumption
        . apply AgreeRen.cons
          assumption
          rw[show (.+2) = (id !>> (.+1)) !>> (.+1) by funext; rfl]
          aesop (rule_sets := [rename])
      have typ : B :: A :: Γ ⊢ .tup1 (.var 1) (.var 0) s : (.sig1 A B s).[shift 2] := by
        asimp; apply Typed.tup1
        . rw[show Tm.sig1 A.[shift 2] B.[up (shift 2)] s
                = (Tm.sig1 A B s).[shift 1].[shift 1] by asimp]
          have := (tyS.weaken tyA).weaken tyB
          assumption
        . rw[show A.[shift 2] = A.[shift 1].[shift 1] by asimp]
          constructor <;> aesop
        . asimp; constructor <;> aesop
      replace tyC' := tyC'.subst typ; asimp at tyC'; clear typ
      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . apply Typed.proj1 ihC tym
        apply Typed.conv
        apply Conv.subst
        apply Conv.one st
        assumption
        assumption
      . apply tyC.subst tym
    case proj_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.proj1 tyC (ihm st) tyn
      . apply tyC.subst tym
    case proj_N => apply Typed.proj1 <;> aesop
    case proj0 =>
      exfalso; apply tym.tup0_sig1_false; constructor
    case proj1 m1 m2 s =>
      have ⟨tym1, tym2, _⟩ := tym.tup1_inv; subst_vars
      rw[show C.[.tup1 m1 m2 s/]
            = C.[.tup1 (.var 1) (.var 0) s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.wk tym2
      constructor; asimp; assumption
      apply AgreeSubst.refl wf
  case bool => intro st; cases st
  case tt => intro st; cases st
  case ff => intro st; cases st
  case ite tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    intro st; cases st
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
    case ite_true => assumption
    case ite_false => assumption
  case idn ihA ihm ihn =>
    intro st; cases st
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
    intro st; cases st
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
    intro st; cases st
    case rw_A A' st =>
      have : Γ ⊢ A'.[.rfl a, a/] : .srt s i := by
        rw[show .srt s i = (.srt s i).[.rfl a,a/] by asimp]
        apply Typed.substitution
        . apply ihA st
        . apply AgreeSubst.wk
          asimp; constructor; assumption
          apply AgreeSubst.wk
          asimp; assumption
          apply AgreeSubst.refl; assumption
      have : Γ ⊢ A.[n,b/] : .srt s i := by
        rw[show .srt s i = (.srt s i).[n,b/] by asimp]
        apply Typed.substitution
        . assumption
        . apply AgreeSubst.wk
          asimp; assumption
          apply AgreeSubst.wk
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
        . apply AgreeSubst.wk
          asimp; assumption
          apply AgreeSubst.wk
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
        . apply AgreeSubst.wk
          asimp; assumption
          apply AgreeSubst.wk
          asimp; assumption
          apply AgreeSubst.refl
          apply tyn.toWf
      apply Typed.conv
      . apply Conv.compat; assumption
      . assumption
      . assumption
  case conv eq _ tyB ihm _ =>
    intro st
    have tym := ihm st
    apply Typed.conv eq tym tyB
