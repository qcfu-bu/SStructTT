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
  case pi ihA ihB =>
    intro st; cases st
    case piA st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case piB st =>
      constructor
      . assumption
      . apply ihB st
  case lam tym ihA ihm =>
    have ⟨_, _, _⟩ := tym.validity
    intro st; cases st
    case lamA st =>
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
    case lamM st =>
      constructor
      . assumption
      . apply ihm st
  case app tym tyn ihm ihn =>
    have ⟨_, _, tyP⟩ := tym.validity
    have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
    intro st; cases st
    case appM st =>
      constructor
      . apply ihm st
      . assumption
    case appN st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . constructor
        assumption
        apply ihn st
      . apply tyB.subst tyn
    case beta =>
      replace ⟨tym, _, _⟩ := tym.lam_inv; subst_vars
      have ⟨_, _, _, tyA⟩ := tym.ctx_inv
      replace tyB := tyB.subst tyn; asimp at tyB
      apply tym.subst tyn
  case sig ihA ihB =>
    intro st; cases st
    case sigA st =>
      constructor
      . apply ihA st
      . apply Typed.conv_ctx
        apply Conv.onei st
        apply ihA st
        assumption
    case sigB st =>
      constructor
      . assumption
      . apply ihB st
  case pair tyS _ _ _ ihm ihn =>
    intro st; cases st
    case pairM st =>
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
    case pairN st =>
      constructor
      . assumption
      . assumption
      . apply ihn st
  case proj Γ A B C _ _ r s sC iC tyC tym tyn ihC ihm ihn =>
    have ⟨s, _, wf, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB, eq⟩ := tyS.sig_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    have ⟨_, _⟩ := Conv.srt_inj eq
    subst_vars; clear eq
    intro st; cases st
    case projA C' st =>
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
      have typ : B :: A :: Γ ⊢ .pair (.var 1) (.var 0) r s : (.sig A B r s).[shift 2] := by
        asimp; apply Typed.pair
        . rw[show Tm.sig A.[shift 2] B.[up (shift 2)] r s
                = (Tm.sig A B r s).[shift 1].[shift 1] by asimp]
          have := (tyS.weaken tyA).weaken tyB
          assumption
        . rw[show A.[shift 2] = A.[shift 1].[shift 1] by asimp]
          constructor <;> aesop
        . asimp; constructor <;> aesop
      replace tyC' := tyC'.subst typ; asimp at tyC'; clear typ
      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . apply Typed.proj ihC tym
        apply Typed.conv
        apply Conv.subst
        apply Conv.one st
        assumption
        assumption
      . apply tyC.subst tym
    case projM st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . apply Typed.proj tyC (ihm st) tyn
      . apply tyC.subst tym
    case projN => constructor <;> aesop
    case projE m1 m2 r s =>
      have ⟨tym1, tym2, _, _⟩ := tym.pair_inv; subst_vars
      rw[show C.[.pair m1 m2 r s/]
            = C.[.pair (.var 1) (.var 0) r s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.wk tym2
      constructor; asimp; assumption
      apply AgreeSubst.refl wf
  case bool => intro st; cases st
  case tt => intro st; cases st
  case ff => intro st; cases st
  case ite tyA tym tyn1 tyn2 ihA ihm ihn1 ihn2 =>
    intro st; cases st
    case iteA st =>
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
    case iteM st =>
      apply Typed.conv
      . apply Conv.subst1
        apply Conv.onei st
      . constructor <;> try assumption
        apply ihm st
      . apply tyA.subst tym
    case iteN1 st =>
      constructor <;> try assumption
      apply ihn1 st
    case iteN2 st =>
      constructor <;> try assumption
      apply ihn2 st
    case iteT => assumption
    case iteF => assumption
  case idn ihA ihm ihn =>
    intro st; cases st
    case idnA st =>
      replace ihA := ihA st
      constructor
      . assumption
      . apply Typed.conv <;> try assumption
        apply Conv.one st
      . apply Typed.conv <;> try assumption
        apply Conv.one st
    case idnM => constructor <;> aesop
    case idnN => constructor <;> aesop
  case rfl tym ihm =>
    have ⟨_, _, _⟩ := tym.validity
    intro st; cases st
    case rflM st =>
      apply Typed.conv
      . apply Conv.idn
        constructor
        apply Conv.onei st
        apply Conv.onei st
      . constructor
        apply ihm st
      . constructor <;> assumption
  case rw Γ A B m n a b s i tyA tym tyn ihA ihm ihn =>
    intro st; cases st
    case rwA A' st =>
      have wf := tym.toWf
      have ⟨_, _, tyI⟩ := tyn.validity
      have ⟨_, tya, _, _⟩ := tyI.idn_inv
      have ⟨_, _, _⟩ := tya.validity
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
    case rwM =>
      sorry
    case rwN => sorry
    case rwE => sorry
  case conv eq _ tyB ihm _ =>
    intro st
    have tym := ihm st
    apply Typed.conv eq tym tyB
