import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservation0 {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 -> WR H2 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step0 (H3, c) (H3', c') ->
    ∃ H1' b',
      HMerge H1' H2 H3' ∧
      [] ;; [] ;; H1' ⊢ a ▷ b' ◁ c' : A ∧ Erasure.Step0 b b' := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro mrg0 wr2 ⟨er, rs, wr1⟩ st; induction er generalizing H1 H2 H3 H3' c c'
  case var wf hs =>
    subst_vars; cases hs
  case lam_im =>
    subst_vars; cases rs
    case lam => cases st
    case ptr => cases st
  case lam_ex =>
    subst_vars; cases rs
    case lam => cases st
    case ptr => cases st
  case app_im m m' n s erm tyn ih =>
    subst_vars; cases rs
    case app =>
      cases st
      case app_M mrg rsm rsn mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ih rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .app mx' .null; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . constructor
            apply mrg1.sym
            assumption
            assumption
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
      case app_N mrg rsm rsn n0 dpf st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨lw, e⟩ := rsn.null_inv wr2'; subst e
        cases st
    case ptr => cases st
  case app_ex m m' n n' s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case app =>
      cases st
      case app_M mrg rsm rsn mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihm rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .app mx' n'; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil erx ern
          . apply Resolve.app mrg1.sym rsx rsn
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
      case app_N mrg rsm rsn nx dpf st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg
        have wrx := mrg1.merge_wr wr1' wr2
        have ⟨H1', nx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihn rfl rfl mrg2.sym wrx rsn wr2' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .app m' nx'; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil erm erx
          . apply Resolve.app mrg1 rsm rsx
          . apply mrg1.merge_wr wr1' wrx
        . constructor; assumption
    case ptr => cases st
  case tup_im m m' n s i ty erm tyn ih =>
    subst_vars; cases rs
    case tup =>
      cases st
      case tup_M mrg rsm rsn mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ih rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .tup mx' .null s; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . constructor
            apply mrg1.sym
            assumption
            assumption
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
      case tup_N mrg rsm rsn n0 dpf st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨lw, e⟩ := rsn.null_inv wr2'; subst e
        cases st
    case ptr => cases st
  case tup_ex m m' n n' s i mrg ty erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case tup =>
      cases st
      case tup_M mrg rsm rsn mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihm rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .tup mx' n' s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil ty erx ern
          . apply Resolve.tup mrg1.sym rsx rsn
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
      case tup_N mrg rsm rsn nx dpf st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg
        have wrx := mrg1.merge_wr wr1' wr2
        have ⟨H1', nx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihn rfl rfl mrg2.sym wrx rsn wr2' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .tup m' nx' s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil ty erm erx
          . apply Resolve.tup mrg1 rsm rsx
          . apply mrg1.merge_wr wr1' wrx
        . constructor; assumption
    case ptr => cases st
  case prj_im m m' n n' s sA sB sC i mrg tyC erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case prj =>
      cases st
      case prj_M mrg rsm rsn mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihm rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .prj mx' n'; and_intros
        . assumption
        . constructor
          . apply Erased.prj_im Merge.nil tyC erx ern
          . apply Resolve.prj mrg1.sym rsx rsn
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
    case ptr => cases st
  case prj_ex m m' n n' s sA sB sC i mrg tyC erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case prj =>
      cases st
      case prj_M mrg rsm rsn mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihm rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .prj mx' n'; and_intros
        . assumption
        . constructor
          . apply Erased.prj_ex Merge.nil tyC erx ern
          . apply Resolve.prj mrg1.sym rsx rsn
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
    case ptr => cases st
  case tt => subst_vars; cases rs; cases st; cases st
  case ff => subst_vars; cases rs; cases st; cases st
  case ite m m' n1 n1' n2 n2' s i mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg; cases rs
    case ite =>
      cases st
      case ite_M mrg rsm rsn1 rsn2 mx st =>
        have ⟨wr1', wr2'⟩ := mrg.split_wr wr1
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have wrx := mrg1.merge_wr wr2' wr2
        have ⟨H1', mx', mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ihm rfl rfl mrg2.sym wrx rsm wr1' st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        exists Hx, .ite mx' n1' n2'; and_intros
        . assumption
        . constructor
          . apply Erased.ite Merge.nil tyA erx ern1 ern2
          . apply Resolve.ite mrg1.sym rsx rsn1 rsn2
          . apply mrg1.merge_wr wr2' wrx
        . constructor; assumption
    case ptr => cases st
  case rw ih =>
    subst_vars
    replace ih := ih rfl rfl mrg0 wr2 rs wr1 st
    rcases ih with ⟨H1', b', mrg', ⟨er', rs', wr'⟩, st⟩
    exists H1', b'; and_intros
    . assumption
    . constructor
      . constructor <;> assumption
      . assumption
      . assumption
    . assumption
  case drop m m' n n' A B s mrg lw h erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case drop H1' H2' m m' lw1 h1 mrg1 rsm rsn =>
      cases st; case drop_elim dp =>
      have wr3 := mrg0.merge_wr wr1 wr2
      have wr3' := dp.wr_image wr3
      have ⟨H0, mrg1, mrg2⟩ := mrg0.split mrg1.sym
      have ⟨Hx, mrgx, lwx⟩ := dp.resolve rsm mrg2.sym lw1 h1
      have ⟨Hy, mrg1', mrg2'⟩ := mrgx.sym.split mrg1
      have rsn := rsn.weaken_merge mrg1' lwx
      have ⟨wry, _⟩ := mrg2'.split_wr wr3'
      exists Hy, n'; and_intros
      . assumption
      . constructor <;> assumption
      . constructor
    case ptr => cases st
  case conv eq erm tyB ih =>
    subst_vars
    have ⟨Hx, x, mrgx, ⟨erx, rsx, wrx⟩, stx⟩ := ih rfl rfl mrg0 wr2 rs wr1 st
    exists Hx, x; and_intros
    . assumption
    . constructor
      apply Erased.conv eq erx tyB
      assumption
      assumption
    . assumption

lemma Resolved.preservation0' {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 -> WR H2 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Red0 (H3, c) (H3', c') ->
    ∃ H1' b',
      HMerge H1' H2 H3' ∧
      [] ;; [] ;; H1' ⊢ a ▷ b' ◁ c' : A ∧ Erasure.Red0 b b' := by
  generalize e: (H3', c') = t
  intro mrg wr rs rd; induction rd generalizing H1 H2 H3' a b c' A
  case R => cases e; exists H1, b; aesop
  case SE x y rd st ih =>
    subst_vars
    rcases x with ⟨H2, c'⟩
    replace ⟨H1, v1, mrg1, rs1, rd1⟩ := ih rfl mrg wr rs
    have ⟨H2, v2, mrg2, rs2, st2⟩ := rs1.preservation0 mrg1 wr st
    exists H2, v2; and_intros
    . assumption
    . assumption
    . apply Star.SE rd1 st2
