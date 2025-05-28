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
    exists Hb

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
  case app_im B m m' n s erm tyn ihm =>
    subst_vars; cases rs
    case app H1' H2' m' n' mrg1 rsm rsn =>
      have wr3 := mrg0.merge_wr wr1 wr2
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
      case beta mx s lf np lk =>
        have wr3' := lk.wr_image wr3
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg1.sym
        have ⟨Hy, rs0, mrg3⟩ := rsm.lookup mrg2.sym lk
        have ⟨wry, wrx⟩ := mrg3.split_wr wr3'
        have ⟨Hz, mrg4, mrg5⟩ := mrg3.sym.split mrg1
        cases rs0; case lam m0 rs0 lw =>
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
        exists Hz, m1.[n/], m0.[.null/]; and_intros
        . assumption
        . constructor
          . apply erm.subst_im tyn
          . apply rsm.merge_contra mrg4.sym lw2'
          . apply mrg4.merge_wr wr2' wry
        . apply Star1.SE_join
          . apply Dynamic.Red.app_im rd
          . constructor
        . constructor
          constructor
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
  exists a', b'
