import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Runtime.Drop
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservation0X {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 ->
    [] ;; H1 ⊢ a ▷ b ◁ c :: A -> Step0 (H3, c) (H3', c') ->
    ∃ H1' b',
      HMerge H1' H2 H3' ∧
      [] ;; H1' ⊢ a ▷ b' ◁ c' :: A ∧ Erasure.Step0 b b' := by
  generalize e: [] = Δ
  intro mrg0 ⟨er, rs⟩ st; induction er generalizing H1 H2 H3 H3' c c'
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
  case app_im m m' n s erm tyn ih =>
    subst_vars; cases rs
    case app =>
      cases st
      case app_M mrg rsm rsn mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have ⟨H1', mx', mrgx, ⟨erx, rsx⟩, stx⟩ := ih rfl mrg2.sym rsm st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .app mx' .null; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . constructor
            apply mrg1.sym
            assumption
            assumption
        . constructor; assumption
      case app_N mrg rsm rsn n0 st =>
        have ⟨_, e⟩ := rsn.null_inv; subst e
        cases st
    case ptr => cases st
  case app_ex m m' n n' s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case app =>
      cases st
      case app_M mrg rsm rsn mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have ⟨H1', mx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihm rfl mrg2.sym rsm st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .app mx' n'; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil erx ern
          . apply Resolve.app mrg1.sym rsx rsn
        . constructor; assumption
      case app_N mrg rsm rsn nx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg
        have ⟨H1', nx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihn rfl mrg2.sym rsn st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .app m' nx'; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil erm erx
          . apply Resolve.app mrg1 rsm rsx
        . constructor; assumption
    case ptr => cases st
  case tup_im m m' n s i ty tym ern ih =>
    subst_vars; cases rs
    case tup =>
      cases st
      case tup_M mrg rsm rsn n0 st =>
        have ⟨_, e⟩ := rsm.null_inv; subst e
        cases st
      case tup_N mrg rsm rsn mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg
        have ⟨H1', nx', mrgx, ⟨erx, rsx⟩, stx⟩ := ih rfl mrg2.sym rsn st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .tup .null nx' s; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . constructor
            apply mrg1
            assumption
            assumption
        . constructor; assumption
    case ptr => cases st
  case tup_ex m m' n n' s i mrg ty erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case tup =>
      cases st
      case tup_M mrg rsm rsn mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have ⟨H1', mx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihm rfl mrg2.sym rsm st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .tup mx' n' s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil ty erx ern
          . apply Resolve.tup mrg1.sym rsx rsn
        . constructor; assumption
      case tup_N mrg rsm rsn nx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg
        have ⟨H1', nx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihn rfl mrg2.sym rsn st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .tup m' nx' s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil ty erm erx
          . apply Resolve.tup mrg1 rsm rsx
        . constructor; assumption
    case ptr => cases st
  case prj_im m m' n n' s sA sB sC i mrg tyC erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case prj =>
      cases st
      case prj_M mrg rsm rsn mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have ⟨H1', mx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihm rfl mrg2.sym rsm st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .prj mx' n'; and_intros
        . assumption
        . constructor
          . apply Erased.prj_im Merge.nil tyC erx ern
          . apply Resolve.prj mrg1.sym rsx rsn
        . constructor; assumption
    case ptr => cases st
  case prj_ex m m' n n' s sA sB sC i mrg tyC erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case prj =>
      cases st
      case prj_M mrg rsm rsn mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have ⟨H1', mx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihm rfl mrg2.sym rsm st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .prj mx' n'; and_intros
        . assumption
        . constructor
          . apply Erased.prj_ex Merge.nil tyC erx ern
          . apply Resolve.prj mrg1.sym rsx rsn
        . constructor; assumption
    case ptr => cases st
  case tt => subst_vars; cases rs; cases st; cases st
  case ff => subst_vars; cases rs; cases st; cases st
  case ite m m' n1 n1' n2 n2' s i mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg; cases rs
    case ite =>
      cases st
      case ite_M mrg rsm rsn1 rsn2 mx st =>
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg.sym
        have ⟨H1', mx', mrgx, ⟨erx, rsx⟩, stx⟩ := ihm rfl mrg2.sym rsm st
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg1
        existsi Hx, .ite mx' n1' n2'; and_intros
        . assumption
        . constructor
          . apply Erased.ite Merge.nil tyA erx ern1 ern2
          . apply Resolve.ite mrg1.sym rsx rsn1 rsn2
        . constructor; assumption
    case ptr => cases st
  case rw ih =>
    subst_vars
    replace ih := ih rfl mrg0 rs st
    rcases ih with ⟨H1', b', mrg', ⟨er', rs'⟩, st⟩
    existsi H1', b'; and_intros
    . assumption
    . constructor
      . constructor <;> assumption
      . assumption
    . assumption
  case drop m m' n n' A B s mrg lw h erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case drop H1' H2' m m' h1 mrg1 rsm rsn =>
      cases st; case drop_elim dp =>
      have ⟨H0, mrg1, mrg2⟩ := mrg0.split mrg1.sym
      have ⟨Hx, mrgx, ct⟩ := dp.resolve rsm mrg2.sym
      have ⟨Hy, mrg1', mrg2'⟩ := mrgx.sym.split mrg1
      have rsn := rsn.merge_shareable mrg1' ct
      existsi Hy, n'; and_intros
      . assumption
      . constructor <;> assumption
      . constructor
    case ptr => cases st
  case conv eq erm tyB ih =>
    subst_vars
    have ⟨Hx, x, mrgx, ⟨erx, rsx⟩, stx⟩ := ih rfl mrg0 rs st
    existsi Hx, x; and_intros
    . assumption
    . constructor
      apply Erased.conv eq erx tyB
      assumption
    . assumption

lemma Resolved.preservation0 {H H' : Heap Srt} {a b c c' A} :
    [] ;; H ⊢ a ▷ b ◁ c :: A -> Step0 (H, c) (H', c') ->
    ∃ b', [] ;; H' ⊢ a ▷ b' ◁ c' :: A ∧ Erasure.Step0 b b' := by
  intro rs st
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_shareable H
  have ⟨H0', b', mrg', rs'⟩ := rs.preservation0X mrg st
  have e := mrg'.self_shareable ct; subst e
  existsi b'; simp_all

lemma Resolved.preservation0' {H H' : Heap Srt} {a b c c' A} :
    [] ;; H ⊢ a ▷ b ◁ c :: A -> Red0 (H, c) (H', c') ->
    ∃ b', [] ;; H' ⊢ a ▷ b' ◁ c' :: A ∧ Erasure.Red0 b b' := by
  generalize e: (H', c') = t
  intro rs rd; induction rd generalizing H' a b c' A
  case R => cases e; existsi b; aesop
  case SE x y rd st ih =>
    subst_vars
    rcases x with ⟨H2, c'⟩
    replace ⟨b', rs, rd⟩ := ih rfl rs
    have ⟨b', rs, st⟩ := rs.preservation0 st
    existsi b'; and_intros
    . assumption
    . apply Star.SE rd st
