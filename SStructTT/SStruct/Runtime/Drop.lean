import SStructTT.SStruct.Runtime.Step
open ARS

namespace SStruct.Erasure
namespace Runtime

variable {Srt : Type} [ord : SrtOrder Srt]

lemma Drop.resolve {H1 H2 H3 H4 : Heap Srt} {m m'} :
    Drop H3 m H4 -> H1 ;; m ▷ m' -> HMerge H1 H2 H3 ->
    ∃ H0, HMerge H0 H2 H4 ∧ Sharable H0 := by
  intro dp rs mrg; induction rs generalizing H2 H3 H4
  case var => cases dp; aesop
  case lam => cases dp; aesop
  case app mrg0 rsm rsn ihm ihn =>
    cases dp; case app dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H2x, mrg3, ct3⟩ := ihm dp1 mrg2.sym
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, ct4⟩ := ihn dp2 mrg5.sym
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    existsi H5x; and_intros
    . assumption
    . apply mrg7.contra_image ct3 ct4
  case tup mrg0 rsm rsn ihm ihn =>
    cases dp; case tup dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H2x, mrg3, ct3⟩ := ihm dp1 mrg2.sym
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, ct4⟩ := ihn dp2 mrg5.sym
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    existsi H5x; and_intros
    . assumption
    . apply mrg7.contra_image ct3 ct4
  case prj mrg0 rsm rsn ihm ihn =>
    cases dp; case prj dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H2x, mrg3, ct3⟩ := ihm dp1 mrg2.sym
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, ct4⟩ := ihn dp2 mrg5.sym
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    existsi H5x; and_intros
    . assumption
    . apply mrg7.contra_image ct3 ct4
  case tt => cases dp; aesop
  case ff => cases dp; aesop
  case ite mrg0 rsm1 rsn1 rsn2 ihm ihn1 ihn2 =>
    cases dp; case ite dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H2x, mrg3, ct3⟩ := ihm dp1 mrg2.sym
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, ct4⟩ := ihn1 dp2 mrg5.sym
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    existsi H5x; and_intros
    . assumption
    . apply mrg7.contra_image ct3 ct4
  case drop mrg0 rsm rsn ihm ihn =>
    cases dp; case drop dp1 dp2 =>
    have ⟨H1x, mrg1, mrg2⟩ := mrg.split mrg0.sym
    have ⟨H2x, mrg3, ct3⟩ := ihm dp1 mrg2.sym
    have ⟨H3x, mrg4, mrg5⟩ := mrg3.sym.split mrg1.sym
    have ⟨H4x, mrg6, ct4⟩ := ihn dp2 mrg5.sym
    have ⟨H5x, mrg7, mrg8⟩ := mrg6.sym.split mrg4.sym
    existsi H5x; and_intros
    . assumption
    . apply mrg7.contra_image ct3 ct4
  case null H1 _ => cases dp; aesop
  case ptr lk1 rs ih =>
    cases dp; case ptr lk2 dp =>
    have ⟨e, mrg1⟩ := HLookup.collision mrg lk2 lk1
    subst e; aesop

lemma Resolve.drop_safeX {H1 H2 H3 : Heap Srt} {m m'} :
    H1 ;; m ▷ m' -> HMerge H1 H2 H3 ->
    ∃ H1' H3', Drop H3 m H3' ∧ HMerge H1' H2 H3' := by
  intro rsm mrg; induction rsm generalizing H2 H3
  case var H1 x ct =>
    existsi H1, H3; and_intros
    . constructor
    . assumption
  case lam ih =>
    have ⟨Hx, Hy, dp, mrg⟩ := ih mrg
    existsi Hx, Hy; and_intros
    . constructor; assumption
    . assumption
  case app mrg1 rsm rsn ih1 ih2 =>
    have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
    have ⟨Hy, H0, dp1, mrg4⟩ := ih1 mrg3.sym
    have ⟨Hz, mrg5, mrg6⟩ := mrg4.sym.split mrg2.sym
    have ⟨Ha, Hb, dp2, mrg7⟩ := ih2 mrg6.sym
    have ⟨Hc, mrg8, mrg9⟩ := mrg7.sym.split mrg5.sym
    existsi Hc, Hb; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case tup mrg1 rsm rsn ih1 ih2 =>
    have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
    have ⟨Hy, H0, dp1, mrg4⟩ := ih1 mrg3.sym
    have ⟨Hz, mrg5, mrg6⟩ := mrg4.sym.split mrg2.sym
    have ⟨Ha, Hb, dp2, mrg7⟩ := ih2 mrg6.sym
    have ⟨Hc, mrg8, mrg9⟩ := mrg7.sym.split mrg5.sym
    existsi Hc, Hb; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case prj mrg1 rsm rsn ih1 ih2 =>
    have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
    have ⟨Hy, H0, dp1, mrg4⟩ := ih1 mrg3.sym
    have ⟨Hz, mrg5, mrg6⟩ := mrg4.sym.split mrg2.sym
    have ⟨Ha, Hb, dp2, mrg7⟩ := ih2 mrg6.sym
    have ⟨Hc, mrg8, mrg9⟩ := mrg7.sym.split mrg5.sym
    existsi Hc, Hb; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case tt H1 _ =>
    exists H1, H3; and_intros
    . constructor
    . assumption
  case ff H1 _ =>
    exists H1, H3; and_intros
    . constructor
    . assumption
  case ite mrg1 rsm rsn1 rsn2 ih1 ih2 ih3 =>
    have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
    have ⟨Hy, H0, dp1, mrg4⟩ := ih1 mrg3.sym
    have ⟨Hz, mrg5, mrg6⟩ := mrg4.sym.split mrg2.sym
    have ⟨Ha, Hb, dp2, mrg7⟩ := ih2 mrg6.sym
    have ⟨Hc, mrg8, mrg9⟩ := mrg7.sym.split mrg5.sym
    existsi Hc, Hb; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case drop mrg1 rsm rsn ih1 ih2 =>
    have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
    have ⟨Hy, H0, dp1, mrg4⟩ := ih1 mrg3.sym
    have ⟨Hz, mrg5, mrg6⟩ := mrg4.sym.split mrg2.sym
    have ⟨Ha, Hb, dp2, mrg7⟩ := ih2 mrg6.sym
    have ⟨Hc, mrg8, mrg9⟩ := mrg7.sym.split mrg5.sym
    existsi Hc, Hb; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case ptr lk rs ih =>
    have ⟨Hx, lk, mrg⟩ := lk.merge mrg
    have ⟨Hy, Hz, dp, mrg⟩ := ih mrg
    existsi Hy, Hz; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case null H1 _ =>
    exists H1, H3; and_intros
    . constructor
    . assumption

lemma Resolve.drop_safe {H1 : Heap Srt} {m m'} :
    H1 ;; m ▷ m' -> ∃ H1', Drop H1 m H1' := by
  intro rs
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H1
  have ⟨H1', H3', dp, mrg⟩ := rs.drop_safeX mrg
  have e := mrg.self_contra ct; subst e
  existsi H1'; assumption
