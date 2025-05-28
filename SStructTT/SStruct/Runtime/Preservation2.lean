import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
import SStructTT.SStruct.Runtime.Substitution
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolve.lookup {H1 H2 H3 H3' : Heap Srt} {l m m'} :
    H1 ⊢ .ptr l ▷ m' -> HMerge H1 H2 H3 ->
    HLookup H3 l m H3' -> ∃ H1', H1' ⊢ m ▷ m' ∧ HMerge H1' H2 H3' := by
  generalize e: Tm.ptr l = t
  intro ty mrg lk; induction ty generalizing H2 H3 H3' l m <;> try trivial
  case ptr Ha Hb l n n' lk0 rsm ihm =>
    cases e; clear ihm
    have ⟨e, mrg0⟩ := lk.collision mrg lk0; subst e
    existsi Hb; simp_all

lemma Resolved.preservation2X {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
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
  case app_im m m' n s erm tyn ihm =>
    subst_vars; cases rs
    case app H1' H2' m' n' mrg1 rsm rsn =>
      have wr3 := mrg0.merge_wr wr1 wr2
      have ⟨wr1', wr2'⟩ := mrg1.split_wr wr1
      have ⟨ct, e⟩ := rsn.null_inv wr2'; subst e
      cases st
      case app_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', a', b', mrgx, ⟨er', rs', wr'⟩, st1, st2⟩ :=
          ihm rfl rfl mrg3.sym wrx rsm wr1' st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .app a' n .im, .app b' .null; and_intros
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
      case beta mx s lf np lk =>
        clear ihm
        have wr3' := lk.wr_image wr3
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg1.sym
        have ⟨Hy, rs0, mrg3⟩ := rsm.lookup mrg2.sym lk
        have ⟨wry, wrx⟩ := mrg3.split_wr wr3'
        have ⟨Hz, mrg4, mrg5⟩ := mrg3.sym.split mrg1
        cases rs0; case lam m0 rs0 hyp =>
        have ⟨A, m1, r, rd, rs1⟩ := erm.lam_preimage
        have ⟨_, _, eq⟩ := rs1.toStatic.lam_inv'
        have ⟨e, _⟩ := Static.Conv.pi_inj eq; subst e
        have ⟨sA, erm⟩ := rs1.lam_im_inv
        have ⟨H0, mrg0, ct0⟩ := HMerge.exists_self_contra Hy
        have rsm := Resolved.intro erm rs0 wry
        have rsm : Hy ⊢ mx.[.null/] ▷ m0.[.null/] := by
          apply rsm.substitution
          . apply mrg0
          . constructor
            constructor
            apply (mrg0.split_wr wry).right
            assumption
        existsi Hz, m1.[n/], m0.[.null/]; and_intros
        . assumption
        . constructor
          . apply erm.subst_im tyn
          . apply rsm.merge_contra mrg4.sym ct
          . apply mrg4.merge_wr wr2' wry
        . apply Star1.SE_join
          . apply Dynamic.Red.app_im rd
          . constructor
        . constructor
          constructor
    case ptr => cases st
  case app_ex m0 m1 n0 n1 s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case app H1' H2' m' n' mrg1 rsm rsn =>
      have wr3 := mrg0.merge_wr wr1 wr2
      have ⟨wr1', wr2'⟩ := mrg1.split_wr wr1
      have ⟨_, _, ty⟩ := erm.validity
      have ⟨_, _, _, tyB, _⟩ := ty.pi_inv
      have tyn0 := ern.toStatic
      cases st
      case app_M st =>
        clear ihn
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', a', b', mrgx, ⟨er', rs', wr'⟩, st1, st2⟩ :=
          ihm rfl rfl mrg3.sym wrx rsm wr1' st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .app a' n0 .ex, .app b' n1; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil <;> assumption
          . constructor
            apply mrg1.sym
            assumption
            assumption
          . apply mrg1.merge_wr wr2' wr'
        . apply Red1.app_ex_M st1
        . constructor; assumption
      case app_N st =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1
        have wrx := mrg2.merge_wr wr1' wr2
        have ⟨H1', a', b', mrgx, ⟨er', rs', wr'⟩, st1, st2⟩ :=
          ihn rfl rfl mrg3.sym wrx rsn wr2' st
        clear ihn
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        have tyn1 := tyn0.preservation' (Red.toStatic tyn0 st1.toStar)
        existsi Hx, .app m0 a' .ex, .app m1 b'; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1
            apply (Star.conv (Red.toStatic tyn0 st1.toStar)).sym
            apply Erased.app_ex Merge.nil erm er'
            apply tyB.subst tyn0
          . apply Resolve.app mrg1 <;> assumption
          . apply mrg1.merge_wr wr1' wr'
        . apply Red1.app_ex_N st1
        . constructor; assumption
      case beta mx s lf np lk =>
        clear ihm ihn; cases np
        case ptr lp =>
          have wr3' := lk.wr_image wr3
          have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg1.sym
          have ⟨Hy, rs0, mrg3⟩ := rsm.lookup mrg2.sym lk
          have ⟨wry, wrx⟩ := mrg3.split_wr wr3'
          have ⟨wr1', wr2'⟩ := mrg1.split_wr wrx
          have ⟨Hz, mrg4, mrg5⟩ := mrg3.sym.split mrg1
          cases rs0; case lam m0 rs0 hyp =>
          have ⟨A, m1, r, rd, rs1⟩ := erm.lam_preimage
          have ⟨_, _, eq⟩ := rs1.toStatic.lam_inv'
          have ⟨e, _⟩ := Static.Conv.pi_inj eq; subst e
          have ⟨sA, erm⟩ := rs1.lam_ex_inv
          have ⟨_, _, tyA⟩ := erm.ctx_inv
          have rsm := Resolved.intro erm rs0 wry
          have vl1 := rsn.ptr_value wr1'
          have ⟨n2, rd2, vl2, ern1⟩ := ern.value_preimage vl1
          have hyp := (Resolved.intro ern rsn wr1').resolution tyA vl1
          have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H2'
          have rsm : Hz ⊢ mx.[.ptr lp/] ▷ m0.[n1/] := by
            apply rsm.substitution
            . apply mrg4.sym
            . constructor
              pick_goal 4
              assumption
              assumption
              assumption
              apply mrg.sym
              constructor
              apply mrg.sym.split_wr' wr1'
              assumption
          existsi Hz, m1.[n2/], m0.[n1/]; and_intros
          . assumption
          . constructor
            . apply Erased.conv
              apply Static.Conv.subst1
              apply (Star.conv (Red.toStatic ern.toStatic rd2)).sym
              apply erm.subst_ex (Lower.nil _) Merge.nil ern1
              apply tyB.subst tyn0
            . assumption
            . apply mrg4.merge_wr wr1' wry
          . apply Star1.SE_join
            apply Dynamic.Red.app_ex rd rd2
            constructor; assumption
          . constructor; assumption
        case null =>
          cases rsn; exfalso; apply ern.null_preimage
    case ptr => cases st
  case tup_im m' n s i ty erm tyn ihm =>
    subst_vars; cases rs
    case tup H1' H2' m' n' mrg1 rsm rsn =>
      have ⟨_, _, _, tyB, _⟩ := ty.sig_inv
      have wr3 := mrg0.merge_wr wr1 wr2
      have ⟨wr1', wr2'⟩ := mrg1.split_wr wr1
      have ⟨ct, e⟩ := rsn.null_inv wr2'; subst e
      cases st
      case tup_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', a', b', mrgx, ⟨er', rs', wr'⟩, st1, st2⟩ :=
          ihm rfl rfl mrg3.sym wrx rsm wr1' st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .tup a' n .im s, .tup b' .null s; and_intros
        . assumption
        . constructor
          . constructor
            assumption
            assumption
            apply Static.Typed.conv
            apply Static.Conv.subst1
            apply Star.conv (Red.toStatic erm.toStatic st1.toStar)
            assumption
            apply tyB.subst er'.toStatic
          . constructor
            apply mrg1.sym
            assumption
            assumption
          . apply mrg1.merge_wr wr2' wr'
        . apply Red1.tup_im st1
        . constructor; assumption
      case tup_N st => cases st
    case ptr => cases st
  all_goals sorry

lemma Resolved.preservation2 {H1 H2 : Heap Srt} {a b c c' A} :
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step2 (H1, c) (H2, c') ->
    ∃ a' b', [] ;; [] ;; H2 ⊢ a' ▷ b' ◁ c' : A ∧ a ~>>1 a' ∧ Erasure.Step1 b b' := by
  intro rsm st
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H1
  have ⟨_, _, wr⟩ := rsm
  have wr0 := mrg.sym.split_wr' wr
  have ⟨H1', a', b', mrg', rsm', rd, st⟩ := rsm.preservation2X mrg wr0 st
  have e := mrg'.self_contra ct; subst e
  existsi a', b'; simp_all
