import SStructTT.Static.Inversion
open ARS

namespace Static
variable {Srt : Type} [inst : SStruct Srt]

theorem preservation {Γ : Ctx Srt} {A m n} :
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
      replace ⟨B, tym, eq⟩ := tym.lam_inv
      have ⟨_, _, eqA, eqB⟩ := Conv.pi_inj eq
      subst_vars
      have ⟨_, _, _, tyA⟩ := tym.ctx_inv
      replace tyB := tyB.subst tyn; asimp at tyB
      replace tyn := Typed.conv eqA tyn tyA
      replace tym := tym.subst tyn
      apply Typed.conv
      . apply Conv.subst _ eqB.sym
      . assumption
      . assumption
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
  case proj Γ A B _ _ _ r s sC iC  tyC tym tyn ihC ihm ihn =>
    have ⟨_, _, _, tyS⟩ := tyC.ctx_inv
    have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
    have ⟨_, _, _, tyA⟩ := tyB.ctx_inv
    intro st; cases st
    case projA C' st =>
      replace ihC := ihC st
      have tyC' : (.sig A B r s).[shift 2] :: B :: A :: Γ ⊢ C'.[ren (upren (.+2))] :
                  (.srt sC iC).[ren (upren (.+2))] := by
        apply Typed.renaming
        . assumption
        . apply AgreeRen.cons
          assumption
          replace (.+2) with ((id !>> (.+1)) !>> (.+1)) := by funext x; rfl
          aesop (rule_sets := [rename])
      have typ : B :: A :: Γ ⊢ .pair (.var 1) (.var 0) r s : (.sig A B r s).[shift 2] := by
        asimp; apply Typed.pair
        sorry
















      apply Typed.conv
      . apply Conv.subst
        apply Conv.onei st
      . constructor
        apply ihC st
        assumption

        apply Typed.conv
        apply Conv.subst
        apply Conv.one st
        assumption







      sorry
    case projM => sorry
    case projN => sorry
    case projE => sorry
