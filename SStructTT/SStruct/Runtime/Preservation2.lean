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
    H1 ;; .ptr l ▷ m' -> HMerge H1 H2 H3 ->
    HLookup H3 l m H3' -> ∃ H1', H1' ;; m.tm ▷ m' ∧ HMerge H1' H2 H3' := by
  generalize e: Tm.ptr l = t
  intro ty mrg lk; induction ty generalizing H2 H3 H3' l m <;> try trivial
  case ptr Ha Hb l n n' lk0 rsm ihm =>
    cases e; clear ihm
    have ⟨e, mrg0⟩ := lk.collision mrg lk0; subst e
    existsi Hb; simp_all

lemma Resolved.preservation2X {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 ->
    [] ;; H1 ⊢ a ▷ b ◁ c :: A -> Step2 (H3, c) (H3', c') ->
    ∃ H1' a' b',
      HMerge H1' H2 H3' ∧
      [] ;; H1' ⊢ a' ▷ b' ◁ c' :: A ∧ a ~>>1 a' ∧ Erasure.Step1 b b' := by
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
  case app_im m m' n s erm tyn ihm =>
    subst_vars; cases rs
    case app H1' H2' m' n' mrg1 rsm rsn =>
      have ⟨ct, e⟩ := rsn.null_inv; subst e
      cases st
      case app_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg3.sym rsm st
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
        . apply Red1.app_im st1
        . constructor; assumption
      case app_N st => cases st
      case beta mx s lf cl np lk =>
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg1.sym
        have ⟨Hy, rs0, mrg3⟩ := rsm.lookup mrg2.sym lk
        have ⟨Hz, mrg4, mrg5⟩ := mrg3.sym.split mrg1
        cases rs0; case lam m0 rs0 hyp =>
        have ⟨A, m1, r, rd, rs1⟩ := erm.lam_preimage
        have ⟨_, _, eq⟩ := rs1.toStatic.lam_inv'
        have ⟨e, _⟩ := Static.Conv.pi_inj eq; subst e
        have ⟨sA, erm⟩ := rs1.lam_im_inv
        have ⟨H0, mrg0, ct0⟩ := HMerge.exists_self_contra Hy
        have rsm := Resolved.intro erm rs0
        have rsm : Hy ;; mx.[.null/] ▷ m0.[.null/] := by
          apply rsm.substitution
          . apply mrg0
          . constructor
            constructor
            assumption
        existsi Hz, m1.[n/], m0.[.null/]; and_intros
        . assumption
        . constructor
          . apply erm.subst_im tyn
          . apply rsm.mergι_contra mrg4.sym ct
        . apply Star1.SE_join
          . apply Dynamic.Red.app_im rd
          . constructor
        . constructor
          constructor
    case ptr => cases st
  case app_ex m0 m1 n0 n1 s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case app H1' H2' m' n' mrg1 rsm rsn =>
      have ⟨_, _, ty⟩ := erm.validity
      have ⟨_, _, _, tyB, _⟩ := ty.pi_inv
      have tyn0 := ern.toStatic
      cases st
      case app_M st =>
        clear ihn
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg3.sym rsm st
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
        . apply Red1.app_ex_M st1
        . constructor; assumption
      case app_N st =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihn rfl mrg3.sym rsn st
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
        . apply Red1.app_ex_N st1
        . constructor; assumption
      case beta mx s lf cl np lk =>
        clear ihm ihn; cases np
        case ptr lp =>
          have ⟨Hx, mrg1, mrg2⟩ := mrg0.split mrg1.sym
          have ⟨Hy, rs0, mrg3⟩ := rsm.lookup mrg2.sym lk
          have ⟨Hz, mrg4, mrg5⟩ := mrg3.sym.split mrg1
          cases rs0; case lam m0 rs0 hyp =>
          have ⟨A, m1, r, rd, rs1⟩ := erm.lam_preimage
          have ⟨_, _, eq⟩ := rs1.toStatic.lam_inv'
          have ⟨e, _⟩ := Static.Conv.pi_inj eq; subst e
          have ⟨sA, erm⟩ := rs1.lam_ex_inv
          have ⟨_, _, tyA⟩ := erm.ctx_inv
          have rsm := Resolved.intro erm rs0
          have vl1 := rsn.ptr_value
          have ⟨n2, rd2, vl2, ern1⟩ := ern.value_preimage vl1
          have hyp := (Resolved.intro ern rsn).resolution tyA vl1
          have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H2'
          have rsm : Hz ;; mx.[.ptr lp/] ▷ m0.[n1/] := by
            apply rsm.substitution
            . apply mrg4.sym
            . constructor
              pick_goal 3
              assumption
              assumption
              apply mrg.sym
              constructor
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
          . apply Star1.SE_join
            apply Dynamic.Red.app_ex rd rd2
            constructor; assumption
          . constructor; assumption
        case null =>
          cases rsn; exfalso; apply ern.null_preimage
    case ptr => cases st
  case tup_im m n n' s i ty tym ern ihn =>
    subst_vars; cases rs
    case tup H1' H2' m' n' mrg1 rsm rsn =>
      have ⟨_, _, _, tyB, _⟩ := ty.sig_inv
      have ⟨ct, e⟩ := rsm.null_inv; subst e
      cases st
      case tup_M st => cases st
      case tup_N st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihn rfl mrg3.sym rsn st
        clear ihn
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .tup m a' .im s, .tup .null b' s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_im <;> assumption
          . constructor
            apply mrg1
            assumption
            assumption
        . apply Red1.tup_im st1
        . constructor; assumption
    case ptr => cases st
  case tup_ex m0 m1 n0 n1 s i mrg ty erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case tup H1' H2' m' n' mrg1 rsm rsn =>
      have ⟨_, _, _, tyB, _⟩ := ty.sig_inv
      cases st
      case tup_M st =>
        clear ihn
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg3.sym rsm st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .tup a' n0 .ex s, .tup b' n1 s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil
            assumption
            assumption
            apply Erased.conv
            apply Static.Conv.subst1
            apply Star.conv (Red.toStatic erm.toStatic st1.toStar)
            assumption
            apply tyB.subst er'.toStatic
          . constructor
            apply mrg1.sym
            assumption
            assumption
        . apply Red1.tup_ex_M st1
        . constructor; assumption
      case tup_N st =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihn rfl mrg3.sym rsn st
        clear ihn
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .tup m0 a' .ex s, .tup m1 b' s; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil <;> assumption
          . constructor <;> assumption
        . apply Red1.tup_ex_N st1
        . constructor; assumption
    case ptr => cases st
  case prj_im B C m0 m1 n0 n1 _ _ _ _ i mrg tyC erm ern ihm ihn =>
    clear ihn; subst_vars; cases mrg; cases rs
    case prj H1' H2' m' n' mrg1 rsm rsn =>
      have tym0 := erm.toStatic
      have wf := ern.toWf
      cases wf; case cons wf tyB =>
      cases wf; case cons tyA =>
      cases st
      case prj_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg3.sym rsm st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .prj C a' n0 .im, .prj b' n1; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1
            apply (Star.conv (Red.toStatic tym0 st1.toStar)).sym
            apply Erased.prj_im Merge.nil tyC
            assumption
            assumption
            apply tyC.subst tym0
          . apply Resolve.prj mrg1.sym <;> assumption
        . apply Red1.prj st1
        . constructor; assumption
      case prj_box H1' s l l1 lk =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H4, rsm', mrg'⟩ := rsm.lookup mrg3.sym lk
        have ⟨Hx, mrg4, mrg5⟩ := mrg'.sym.split mrg2
        cases rsm'; case tup mx0 nx0 mrg rs1 rs2 =>
        have vl := rsm.ptr_value
        cases vl; case tup vl1 vl2 =>
        cases rs1
        have ⟨mx1, nx1, r, rd1, erx⟩ := erm.tup_preimage
        have ⟨_, _, _, _⟩ := erx.toStatic.tup_inv; subst_vars
        have ⟨tymx, ernx, _, _⟩ := erx.tup_im_inv
        have ⟨v0, rd2, vl0, erv0⟩ := ernx.value_preimage vl2
        have rsn := Resolved.intro ern rsn
        have hyp := (Resolved.intro erv0 rs2).resolution (tyB.subst tymx) vl2
        have rdv0 := Red.toStatic ernx.toStatic rd2
        have eq : m0 === (.tup mx1 v0 .im s) := by
          apply Star.conv
          apply Star.trans (Red.toStatic erm.toStatic rd1)
          apply Static.Red.tup _ _ Star.R rdv0
        existsi Hx, n0.[v0,mx1/], n1.[nx0,.null/]; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1 _ eq.sym
            rw[show C.[.tup mx1 v0 .im s/]
                  = C.[.tup (.var 1) (.var 0) .im s .: shift 2].[v0,mx1/] by asimp]
            apply ern.substitution
            apply Erasure.AgreeSubst.intro_ex Merge.nil (Lower.nil _) erv0
            apply Erasure.AgreeSubst.intro_im; asimp; assumption
            apply Erasure.AgreeSubst.refl Wf.nil
            apply tyC.subst erm.toStatic
          . apply rsn.substitution mrg4
            constructor
            . assumption
            . assumption
            . assumption
            . constructor
              constructor; assumption
        . apply Star1.SE_join
          apply Star.trans
          apply Red.prj rd1
          apply Red.prj (Red.tup_im rd2)
          aesop
        . aesop
      case prj_tup lk =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨_, rsm0, _⟩ := rsm.lookup mrg3.sym lk
        simp[Cell.tm] at rsm0
        cases rsm0
        case tup rs _ =>
          replace ⟨_, _, _, _, erm⟩ := erm.tup_preimage
          have ⟨_, _, _, _⟩ := erm.toStatic.tup_inv; subst_vars
          have ⟨_, _, _, _⟩ := erm.tup_im_inv; subst_vars
          have ⟨_, e⟩ := rs.null_inv; cases e
    case ptr => cases st
  case prj_ex B C m0 m1 n0 n1 _ _ _ _ i mrg tyC erm ern ihm ihn =>
    clear ihn; subst_vars; cases mrg; cases rs
    case prj H1' H2' m' n' mrg1 rsm rsn =>
      have tym0 := erm.toStatic
      have wf := ern.toWf
      cases wf; case cons wf tyB =>
      cases wf; case cons tyA =>
      cases st
      case prj_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg3.sym rsm st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .prj C a' n0 .ex, .prj b' n1; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1
            apply (Star.conv (Red.toStatic tym0 st1.toStar)).sym
            apply Erased.prj_ex Merge.nil tyC
            assumption
            assumption
            apply tyC.subst tym0
          . apply Resolve.prj mrg1.sym <;> assumption
        . apply Red1.prj st1
        . constructor; assumption
      case prj_box lk =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨_, rsm0, _⟩ := rsm.lookup mrg3.sym lk
        simp[Cell.tm] at rsm0
        cases rsm0
        case tup rs _ =>
          cases rs
          replace ⟨_, _, _, _, erm⟩ := erm.tup_preimage
          have ⟨_, _, _, _⟩ := erm.toStatic.tup_inv; subst_vars
          have ⟨_, _, _, er, _, _⟩ := erm.tup_ex_inv
          exfalso; apply er.null_preimage
      case prj_tup H1' s l l1 l2 lk =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H4, rsm', mrg'⟩ := rsm.lookup mrg3.sym lk
        have ⟨Hx, mrg4, mrg5⟩ := mrg'.sym.split mrg2
        cases rsm'; case tup Hm Hn mx0 nx0 mrg rs1 rs2 =>
        have vl := rsm.ptr_value
        cases vl; case tup vlm vln =>
        have ⟨mx1, nx1, r, rd1, erx⟩ := erm.tup_preimage
        have ⟨_, _, _, _⟩ := erx.toStatic.tup_inv; subst_vars
        have ⟨_, _, mrg, ermx, ernx, _⟩ := erx.tup_ex_inv; cases mrg
        have ⟨v1, rdv1, vl1, erv1⟩ := ermx.value_preimage vlm
        have ⟨v2, rdv2, vl2, erv2⟩ := ernx.value_preimage vln
        have tymx := ermx.toStatic
        have rsn := Resolved.intro ern rsn
        have hyp1 := (Resolved.intro erv1 rs1).resolution tyA vlm
        have hyp2 := (Resolved.intro erv2 rs2).resolution (tyB.subst tymx) vln
        have rdv1' := Red.toStatic tymx rdv1
        have rdv2' := Red.toStatic ernx.toStatic rdv2
        have ⟨Hm', mrg, ct⟩ := HMerge.exists_self_contra Hm
        have eq : m0 === (.tup v1 v2 .ex s) := by
          apply Star.conv
          apply Star.trans (Red.toStatic erm.toStatic rd1)
          apply Static.Red.tup _ _ rdv1' rdv2'
        have erv2 : [] ⊢ v2 ▷ nx0 :: B.[v1/] := by
          apply Erased.conv
          apply Static.Conv.subst1
          apply Star.conv rdv1'
          apply erv2
          apply tyB.subst erv1.toStatic
        existsi Hx, n0.[v2,v1/], n1.[nx0,mx0/]; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1 _ eq.sym
            rw[show C.[.tup v1 v2 .ex s/]
                  = C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[v2,v1/] by asimp]
            apply ern.substitution
            apply Erasure.AgreeSubst.intro_ex Merge.nil (Lower.nil _) erv2
            apply Erasure.AgreeSubst.intro_ex Merge.nil (Lower.nil _)
            asimp; assumption
            apply Erasure.AgreeSubst.refl Wf.nil
            apply tyC.subst erm.toStatic
          . apply rsn.substitution mrg4
            constructor
            . assumption
            . assumption
            . assumption
            . constructor
              . assumption
              . apply mrg.sym
              . assumption
              . constructor
                assumption
        . apply Star1.SE_join
          apply Star.trans
          apply Red.prj rd1
          apply Red.prj (Red.tup_ex rdv1 rdv2)
          aesop
        . aesop
    case ptr => cases st
  case tt =>
    subst_vars; cases rs
    case tt => cases st
    case ptr => cases st
  case ff =>
    subst_vars; cases rs
    case ff => cases st
    case ptr => cases st
  case ite A m m' n1 n1' n2 n2' s i mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    clear ihn1 ihn2
    subst_vars; cases mrg; cases rs
    case ite mrg1 rsm rsn1 rsn2 =>
      have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
      cases st
      case ite_M mx st =>
        have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg3.sym rsm st
        clear ihm
        have ⟨Hx, mrg1, mrg2⟩ := mrgx.sym.split mrg2
        existsi Hx, .ite A a' n1 n2, .ite b' n1' n2'; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1
            apply (Star.conv (Red.toStatic erm.toStatic st1.toStar)).sym
            apply Erased.ite Merge.nil <;> assumption
            apply tyA.subst erm.toStatic
          . apply Resolve.ite mrg1.sym <;> assumption
        . apply Red1.ite st1
        . constructor; assumption
      case ite_tt l lk =>
        clear ihm
        have e := lk.contra_tt; subst e
        have ⟨Hx, rsx, mrgx⟩ := rsm.lookup mrg3.sym lk
        cases rsx
        have ct := rsm.tt_inv
        have rd := erm.tt_preimage
        existsi H1, n1, n1'; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1
            apply (Star.conv (Red.toStatic erm.toStatic rd)).sym
            assumption
            apply tyA.subst erm.toStatic
          . apply rsn1.mergι_contra mrg1.sym ct
        . apply Star1.SE_join
          apply Red.ite rd
          constructor
        . constructor
      case ite_ff l lk =>
        clear ihm
        have e := lk.contra_ff; subst e
        have ⟨Hx, rsx, mrgx⟩ := rsm.lookup mrg3.sym lk
        cases rsx
        have ct := rsm.ff_inv
        have rd := erm.ff_preimage
        existsi H1, n2, n2'; and_intros
        . assumption
        . constructor
          . apply Erased.conv
            apply Static.Conv.subst1
            apply (Star.conv (Red.toStatic erm.toStatic rd)).sym
            assumption
            apply tyA.subst erm.toStatic
          . apply rsn2.mergι_contra mrg1.sym ct
        . apply Star1.SE_join
          apply Red.ite rd
          constructor
        . constructor
    case ptr => cases st
  case rw tyA erm tyn ihm =>
    subst_vars
    have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg0 rs st
    clear ihm
    have ⟨eq, tyA⟩ := tyn.closed_idn tyA
    existsi H1', a', b'; and_intros
    . assumption
    . constructor
      . apply Erased.conv eq
        assumption
        assumption
      . assumption
    . apply Star1.ES
      constructor
      assumption
    . assumption
  case drop => cases rs; cases st; cases st
  case conv eq erm tyB ihm =>
    subst_vars
    have ⟨H1', a', b', mrgx, ⟨er', rs'⟩, st1, st2⟩ := ihm rfl mrg0 rs st
    clear ihm
    existsi H1', a', b'; and_intros
    . assumption
    . constructor
      . apply Erased.conv eq
        assumption
        assumption
      . assumption
    . assumption
    . assumption

lemma Resolved.preservation2 {H1 H2 : Heap Srt} {a b c c' A} :
    [] ;; H1 ⊢ a ▷ b ◁ c :: A -> Step2 (H1, c) (H2, c') ->
    ∃ a' b', [] ;; H2 ⊢ a' ▷ b' ◁ c' :: A ∧ a ~>>1 a' ∧ Erasure.Step1 b b' := by
  intro rsm st
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H1
  have ⟨H1', a', b', mrg', rsm', rd, st⟩ := rsm.preservation2X mrg st
  have e := mrg'.self_contra ct; subst e
  existsi a', b'; simp_all
