import SStructTT.SStruct.Program.Preservation
import SStructTT.SStruct.Extraction.Inversion
import SStructTT.SStruct.Extraction.Step
open ARS SStruct.Program

namespace SStruct.Extraction
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Extract.value_preimage {A m1 : SStruct.Tm Srt} {m2} :
    [] ⊢ m1 ▷ m2 :: A -> Value m2 ->
    ∃ v, m1 ~>>* v ∧ Program.Value v ∧ [] ⊢ v ▷ m2 :: A := by
  generalize e: [] = Δ
  intro erm vl; induction erm
  all_goals try trivial
  case lam_im A B m m' s sA i lw tyA erm ihm =>
    subst_vars; simp_all
    existsi .lam A m .im s; and_intros
    . apply Star.R
    . constructor
    . constructor <;> assumption
  case lam_ex A B m m' s sA i lw tyA erm ihm =>
    subst_vars; simp_all
    existsi .lam A m .ex s; and_intros
    . apply Star.R
    . constructor
    . constructor <;> assumption
  case tup_im A B m n n' s i tyA tym ern ihn =>
    subst_vars; simp_all
    cases vl; case tup vl1 vl2 =>
    have ⟨v, rd, vl, erv⟩ := ihn vl2
    have ⟨_, _, _, tyB, _⟩ := tyA.sig_inv
    have rd0 := Red.toLogical ern.toLogical rd
    existsi .tup m v .im s; and_intros
    . apply Red.tup_im rd
    . constructor; assumption
    . rw[<-Ctx.logical.eq_1] at tyA
      apply Extract.tup_im tyA tym
      assumption
  case tup_ex A B m m' n n' s i mrg tyA erm ern ihm ihn =>
    subst_vars; cases mrg; simp_all
    cases vl; case tup vl1 vl2 =>
    have ⟨v1, rd1, vl1, erv1⟩ := ihm vl1
    have ⟨v2, rd2, vl2, erv2⟩ := ihn vl2
    have ⟨_, _, _, tyB, _⟩ := tyA.sig_inv
    have rd0 := Red.toLogical erm.toLogical rd1
    existsi .tup v1 v2 .ex s; and_intros
    . apply Red.tup_ex rd1 rd2
    . constructor <;> assumption
    . apply Extract.tup_ex Merge.nil tyA erv1
      apply Extract.conv
      apply Logical.Conv.subst1
      apply Star.conv rd0
      assumption
      apply tyB.subst erv1.toLogical
  case tt =>
    subst_vars; simp_all
    existsi .tt; and_intros
    . apply Star.R
    . constructor
    . constructor <;> aesop
  case ff =>
    subst_vars; simp_all
    existsi .ff; and_intros
    . apply Star.R
    . constructor
    . constructor <;> aesop
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, tyA⟩ := tyn.closed_idn tyA
    have ⟨v, rd, vl, erv⟩ := ih
    existsi v; and_intros
    . apply Star.ES
      constructor
      assumption
    . assumption
    . apply Extract.conv <;> assumption
  case conv ih =>
    subst_vars; simp_all
    have ⟨v, rd, vl, erv⟩ := ih
    existsi v; and_intros
    . assumption
    . assumption
    . apply Extract.conv <;> assumption

lemma Extract.preservation0 {A m1 : SStruct.Tm Srt} {m2 m2'} :
    [] ⊢ m1 ▷ m2 :: A -> Step0 m2 m2' ->
    [] ⊢ m1 ▷ m2' :: A := by
  generalize e: [] = Δ
  intro erm st; induction erm generalizing m2'
  all_goals try trivial
  case app_im st tyn erm ihm =>
    subst_vars; simp_all; cases st
    case app_M => constructor <;> aesop
    case app_N st => cases st
  case app_ex mrg erm ern ihm ihn =>
    subst_vars; simp_all; cases mrg; cases st
    case app_M => constructor <;> aesop
    case app_N => constructor <;> aesop
  case tup_im erm tyn ihm =>
    subst_vars; simp_all; cases st
    case tup_M st => cases st
    case tup_N st => constructor <;> aesop
  case tup_ex mrg tyS erm ern ihm ihn =>
    subst_vars; simp_all; cases mrg; cases st
    case tup_M => constructor <;> aesop
    case tup_N => constructor <;> aesop
  case prj_im mrg tyC erm ern ihm ihn =>
    subst_vars; simp_all; cases mrg; cases st
    apply Extract.prj_im <;> aesop
  case prj_ex mrg tyC erm ern ihm ihn =>
    subst_vars; simp_all; cases mrg; cases st
    apply Extract.prj_ex <;> aesop
  case ite mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; simp_all; cases mrg; cases st
    constructor <;> aesop
  case drop mrg lw h erm ern ihm ihn =>
    subst_vars; cases mrg; cases st
    assumption
  case rw tyA erm tyn ihm =>
    subst_vars
    have ⟨eq, tyA⟩ := tyn.closed_idn tyA
    have erm := ihm rfl st
    have erm := Extract.conv eq erm tyA
    constructor <;> assumption
  case conv eq _ tyB ihm =>
    subst_vars
    have erm := ihm rfl st
    apply erm.conv eq tyB

lemma Extract.preservation0' {A m1 : SStruct.Tm Srt} {m2 m2'} :
    [] ⊢ m1 ▷ m2 :: A -> Red0 m2 m2' -> [] ⊢ m1 ▷ m2' :: A := by
  intro erm rd; induction rd
  case R => assumption
  case SE st ih => apply ih.preservation0 st

theorem Extract.preservation {A m1 : SStruct.Tm Srt} {m2 m2'} :
    [] ⊢ m1 ▷ m2 :: A -> m2 ~>> m2' ->
    ∃ m1', m1 ~>>1 m1' ∧ [] ⊢ m1' ▷ m2' :: A := by
  generalize e: [] = Δ
  intro ty st; induction ty generalizing m2'
  case var =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.var_inv] at st; cases st
  case lam_im =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.lam_inv] at st; cases st
  case lam_ex =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.lam_inv] at st; cases st
  case app_im m' n s erm tyn ih =>
    subst_vars; simp_all
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, nx, e, rd1, rd2⟩ := rd.app_inv
    replace erm := erm.preservation0' rd1
    have e := rd2.null_inv
    subst_vars; cases st
    case app_M st =>
      have ⟨m, st, erm⟩ := ih ⟨_, rd1, st⟩
      existsi .app m n; and_intros
      . apply Red1.app_M st
      . apply Extract.app_im erm tyn
    case app_N st => cases st
    case beta vl e0 =>
      have ⟨A, m, r, rd, erm⟩ := erm.lam_preimage
      cases r with
      | im =>
        replace ⟨sA, erm⟩ := erm.lam_im_inv
        existsi m.[n/]; and_intros
        . apply Star1.SE_join
          apply Red.app rd Star.R
          constructor
        . apply erm.subst_im tyn
      | ex =>
        have ⟨_, _, _, eq⟩ := erm.toProgram.lam_ex_inv'
        have ⟨e, _⟩ := Logical.Conv.pi_inj eq
        contradiction
  case app_ex m1 m1' n1 n1' s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; simp_all;
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, nx, e, rd1, rd2⟩ := rd.app_inv
    replace erm := erm.preservation0' rd1
    replace ern := ern.preservation0' rd2
    subst_vars; cases st
    case app_M st' =>
      have ⟨m2, st, erm⟩ := ihm ⟨_, rd1, st'⟩
      existsi (.app m2 n1); and_intros
      . apply Red1.app_M st
      . apply Extract.app_ex Merge.nil erm ern
    case app_N st' =>
      have ⟨_, _, tyP⟩ := erm.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have ⟨n2, st, ern2⟩ := ihn ⟨_, rd2, st'⟩
      have rd := Red.toLogical ern.toLogical st.toStar
      existsi (.app m1 n2); and_intros
      . apply Red1.app_N st
      . apply Extract.conv
        apply Logical.Conv.subst1
        apply (Star.conv (Red.toLogical ern.toLogical st.toStar)).sym
        apply Extract.app_ex
        . apply Merge.nil
        . assumption
        . assumption
        . apply tyB.subst ern.toLogical
    case beta vl' =>
      have ⟨A, m, r, rd, erm⟩ := erm.lam_preimage
      cases r with
      | im =>
        have ⟨_, _, _, eq⟩ := erm.toProgram.lam_im_inv'
        have ⟨e, _⟩ := Logical.Conv.pi_inj eq
        contradiction
      | ex =>
        have ⟨v, st, vl, tyv⟩ := ern.value_preimage vl'
        have st0 := Red.toLogical ern.toLogical st
        replace ⟨sA, erm⟩ := erm.lam_ex_inv
        have ⟨s, i, tyB⟩ := erm.validity
        existsi m.[v/]; and_intros
        . apply Star1.SE_join
          apply Red.app rd st
          constructor; aesop
        . have ty := erm.subst_ex (Lower.nil sA) Merge.nil tyv
          apply Extract.conv
          apply Logical.Conv.subst1
          apply (Star.conv st0).sym
          assumption
          apply tyB.subst ern.toLogical
  case tup_im m m' n s _ tyS tym ern ih =>
    subst_vars; simp_all
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, nx, e, rd1, rd2⟩ := rd.tup_inv
    have e := rd1.null_inv
    replace ern := ern.preservation0' rd2
    subst_vars; cases st
    case tup_M st' => cases st'
    case tup_N st' =>
      have ⟨n1, st, ern1⟩ := ih ⟨_, rd2, st'⟩
      have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
      existsi .tup m n1 .im s; and_intros
      . apply Red1.tup_im st
      . constructor <;> assumption
  case tup_ex m m' n n' s _ mrg tyS erm ern ihm ihn =>
    have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
    subst_vars; cases mrg; simp_all
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, nx, e, rd1, rd2⟩ := rd.tup_inv
    replace erm := erm.preservation0' rd1
    replace ern := ern.preservation0' rd2
    subst_vars; cases st
    case tup_M st =>
      have ⟨m1, st, erm1⟩ := ihm ⟨_, rd1, st⟩
      existsi .tup m1 n .ex s; and_intros
      . apply Red1.tup_ex_M st
      . constructor
        . constructor
        . assumption
        . assumption
        . apply Extract.conv
          apply Logical.Conv.subst1
          apply Star.conv (Red.toLogical erm.toLogical st.toStar)
          assumption
          apply tyB.subst erm1.toLogical
    case tup_N st =>
      have ⟨n1, st, ern1⟩ := ihn ⟨_, rd2, st⟩
      existsi .tup m n1 .ex s; and_intros
      . apply Red1.tup_ex_N st
      . constructor <;> aesop
  case prj_im B C m m' n n' s sA sB sC iC mrg tyC erm ern ihm _ =>
    subst_vars; cases mrg; simp_all
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, e, rd1⟩ := rd.prj_inv
    replace erm := erm.preservation0' rd1
    subst_vars; cases st
    case prj_M st' =>
      have ⟨m1, st, erm1⟩ := ihm ⟨_, rd1, st'⟩
      existsi .prj C m1 n; and_intros
      . apply Red1.prj st
      . apply Extract.conv
        . apply Logical.Conv.subst1
          apply (Star.conv (Red.toLogical erm.toLogical st.toStar)).sym
        . apply Extract.prj_im Merge.nil tyC erm1 ern
        . apply tyC.subst erm.toLogical
    case prj_elim m1 m2 s vl' =>
      have ⟨_, _, ty⟩ := erm.toLogical.validity
      have ⟨_, _, _, tyB, _⟩ := ty.sig_inv
      have ⟨m1, m2, r, rdm, er⟩ := erm.tup_preimage
      cases r with
      | im =>
        have ⟨erm1, erm2, _, _⟩ := er.tup_im_inv; subst_vars
        cases vl'; case tup _ vl' =>
        have ⟨v, rdv, vl, erv⟩ := erm2.value_preimage vl'
        have rdv0 := Red.toLogical erm2.toLogical rdv
        have eq : m === (.tup m1 v .im s) := by
          apply Star.conv
          apply Star.trans (Red.toLogical erm.toLogical rdm)
          apply Logical.Red.tup _ _ Star.R rdv0
        existsi n.[v,m1/]; and_intros
        . apply Star1.SE_join
          apply Star.trans (Red.prj rdm)
          apply Red.prj (Red.tup_im rdv)
          constructor; aesop
        . apply Extract.conv
          apply Logical.Conv.subst1 _ eq.sym
          rw[show C.[.tup m1 v .im s/]
                = C.[.tup (.var 1) (.var 0) .im s .: shift 2].[v,m1/] by asimp]
          apply ern.substitution
          -- rw[<-Ctx.logical.eq_1] at erm2
          apply AgreeSubst.intro_ex Merge.nil; constructor; assumption
          apply AgreeSubst.intro_im; asimp; assumption
          apply AgreeSubst.refl Wf.nil
          apply tyC.subst erm.toLogical
      | ex =>
        have ⟨_, _, _, _, _, _, _, eq⟩ := er.toProgram.tup_ex_inv'
        have ⟨e, _⟩ := Logical.Conv.sig_inj eq
        contradiction
  case prj_ex B C m m' n n' s sA sB sC iC mrg tyC erm ern ihm ihn =>
    subst_vars; cases mrg; simp_all
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, e, rd1⟩ := rd.prj_inv
    replace erm := erm.preservation0' rd1
    subst_vars; cases st
    case prj_M st' =>
      have ⟨m1, st, erm1⟩ := ihm ⟨_, rd1, st'⟩
      existsi .prj C m1 n; and_intros
      . apply Red1.prj st
      . apply Extract.conv
        . apply Logical.Conv.subst1
          apply (Star.conv (Red.toLogical erm.toLogical st.toStar)).sym
        . apply Extract.prj_ex Merge.nil tyC erm1 ern
        . apply tyC.subst erm.toLogical
    case prj_elim m1 m2 s vl' =>
      have ⟨n1, n2, r, rdm, er⟩ := erm.tup_preimage
      cases r with
      | im =>
        have ⟨_, _, _, _, eq⟩ := er.toProgram.tup_im_inv'
        have ⟨e, _⟩ := Logical.Conv.sig_inj eq
        contradiction
      | ex =>
        have ⟨_, _, ty⟩ := erm.toLogical.validity
        have ⟨_, _, _, tyB, _⟩ := ty.sig_inv
        have ⟨Δ1, Δ2, mrg, erm1, erm2, _⟩ := er.tup_ex_inv
        cases mrg; subst_vars
        cases vl'; case tup vl1' vl2' =>
        have ⟨v1, rdv1, vl1, erv1⟩ := erm1.value_preimage vl1'
        have ⟨v2, rdv2, vl2, erv2⟩ := erm2.value_preimage vl2'
        have rdv1' := Red.toLogical erm1.toLogical rdv1
        have rdv2' := Red.toLogical erm2.toLogical rdv2
        have eq : m === (.tup v1 v2 .ex s) := by
          apply Star.conv
          apply Star.trans (Red.toLogical erm.toLogical rdm)
          apply Logical.Red.tup _ _ rdv1' rdv2'
        have erm2 : [] ⊢ v2 ▷ m2 :: B.[v1/] := by
          apply Extract.conv
          apply Logical.Conv.subst1
          apply Star.conv rdv1'
          apply erv2
          apply tyB.subst erv1.toLogical
        existsi n.[v2,v1/]; and_intros
        . apply Star1.SE_join
          apply Star.trans (Red.prj rdm)
          apply Red.prj (Red.tup_ex rdv1 rdv2)
          constructor; aesop
        . apply Extract.conv
          apply Logical.Conv.subst1 _ eq.sym
          rw[show C.[.tup v1 v2 .ex s/]
                = C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[v2,v1/] by asimp]
          apply ern.substitution
          apply AgreeSubst.intro_ex Merge.nil (Lower.nil _) erm2
          apply AgreeSubst.intro_ex Merge.nil; constructor; asimp; assumption
          apply AgreeSubst.refl Wf.nil
          apply tyC.subst erm.toLogical
  case tt =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.tt_inv] at st; cases st
  case ff =>
    rcases st with ⟨_, rd, st⟩
    rw[rd.ff_inv] at st; cases st
  case ite A m m' n1 n1' n2 n2' _ _ mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg; simp_all
    rcases st with ⟨_, rd, st⟩
    have ⟨mx, e, rd1⟩ := rd.ite_inv
    replace erm := erm.preservation0' rd1
    subst_vars; cases st
    case ite_M st =>
      have ⟨m1, st, erm1⟩ := ihm ⟨_, rd1, st⟩
      existsi .ite A m1 n1 n2; and_intros
      . apply Red1.ite st
      . apply Extract.conv
        . apply Logical.Conv.subst1
          apply (Star.conv (Red.toLogical erm.toLogical st.toStar)).sym
        . apply Extract.ite Merge.nil tyA erm1 ern1 ern2
        . apply tyA.subst erm.toLogical
    case ite_tt =>
      have rd := erm.tt_preimage
      existsi n1; and_intros
      . apply Star1.SE_join
        apply Red.ite rd
        constructor
      . apply Extract.conv
        apply Logical.Conv.subst1
        apply (Star.conv (Red.toLogical erm.toLogical rd)).sym
        assumption
        apply tyA.subst erm.toLogical
    case ite_ff =>
      have rd := erm.ff_preimage
      existsi n2; and_intros
      . apply Star1.SE_join
        apply Red.ite rd
        constructor
      . apply Extract.conv
        apply Logical.Conv.subst1
        apply (Star.conv (Red.toLogical erm.toLogical rd)).sym
        assumption
        apply tyA.subst erm.toLogical
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars; simp_all
    have ⟨eq, tyA⟩ := tyn.closed_idn tyA
    have ⟨m, rd, erm⟩ := ih st
    existsi m; and_intros
    . apply Star1.ES
      constructor
      assumption
    . apply Extract.conv <;> assumption
  case drop mrg lw h erm ern ihm ihn =>
    subst_vars; cases mrg; simp_all
    rcases st with ⟨_, rd, st⟩
    cases rd
    case R => cases st
    case SE rd st0 =>
      replace rd := Red0.drop_inv rd st0
      apply ihn; constructor
      and_intros <;> assumption
  case conv eq _ tyB ihm =>
    subst_vars
    have ⟨m', st', erm'⟩ := ihm rfl st
    existsi m'; and_intros
    . assumption
    . apply erm'.conv eq tyB
