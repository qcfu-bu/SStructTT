import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservation2 {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 -> WR H2 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step2 (H3, c) (H3', c') ->
    ∃ H1' a' b',
      HMerge H1' H2 H3' ∧
      [] ;; [] ;; H1' ⊢ a' ▷ b' ◁ c' : A ∧ a ~>>1 a' ∧ Erasure.Step1 b b' := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro mrg0 wr2 ⟨er, rs, wr1⟩ st; induction er generalizing H1 H2 H3 H3' c c'
  case var hs =>
    subst_vars; cases hs
  case lam_im =>
    subst_vars; cases rs
    case lam => cases st
    case ptr => cases st
  case lam_ex =>
    subst_vars; cases rs
    case lam => cases st
    case ptr => cases st
  case app_im m m' n n' erm tyn ihm =>
    subst_vars; cases rs
    case app H1' H2' m' n' mrg1 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg1.split_wr wr1
      have ⟨lw2', e⟩ := rsn.null_inv wr2'; subst e
      cases st
      case app_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', a', b', mrgx, ⟨er', rs', wr'⟩, st1, st2⟩ :=
          ihm rfl rfl mrg3.sym wrx rsm wr1' st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        exists Hx, .app a' n .im, .app b' .null; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . constructor
            apply mrg1.sym
            assumption
            assumption
          . apply mrg1.merge_wr wr2' wr'
        . apply Red1.app_im st1
        . constructor; assumption
      case app_N st => cases st
      case beta => sorry
    case ptr => cases st
  all_goals sorry
