import SStructTT.SStruct.Dynamic.Preservation
import SStructTT.SStruct.Erasure.Inversion
import SStructTT.SStruct.Erasure.Step
open ARS SStruct.Dynamic

namespace SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Erased.value_preimage {Γ Δ} {A m1 : SStruct.Tm Srt} {m2} :
    Γ ;; Δ ⊢ m1 ▷ m2 : A -> Value m2 -> Dynamic.Value m1 := by
  intro ty; induction ty
  all_goals try (solve | intro vl; cases vl | aesop)
  case tup_im => intro vl; cases vl; constructor; aesop
  case tup_ex => intro vl; cases vl; constructor <;> aesop

theorem Erased.preservation {A m1 : SStruct.Tm Srt} {m2 m2'} :
    [] ;; [] ⊢ m1 ▷ m2 : A -> m2 ~>> m2' ->
    ∃ m1', m1 ~>> m1' ∧ [] ;; [] ⊢ m1' ▷ m2' : A := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty st; induction ty generalizing m2'
  all_goals try trivial
  case app_im m' n s erm tyn ih =>
    subst_vars; cases st
    case app_M st =>
      have ⟨m, st, erm⟩ := ih rfl rfl st
      exists .app m n .im; and_intros
      . constructor; assumption
      . apply Erased.app_im erm tyn
    case app_N st => cases st
    case beta vl e0 =>
      have ⟨A, m, r, e⟩ := erm.lam_preimage; subst e
      cases r with
      | im =>
        replace ⟨sA, erm, e⟩ := erm.lam_im_inv; subst e
        exists m.[n/]; and_intros
        . aesop
        . simp at e0; subst e0
          apply erm.subst_im tyn
      | ex =>
        have ⟨_, _, _, _, _, eq⟩ := erm.toDynamic.lam_ex_inv'
        have ⟨e, _⟩ := Static.Conv.pi_inj eq
        contradiction
  case app_ex m1 m1' n1 n1' s mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases st
    case app_M st' =>
      have ⟨m2, st, erm⟩ := ihm rfl rfl st'
      exists (.app m2 n1 .ex); and_intros
      . apply Step.app_ex_M; assumption
      . apply Erased.app_ex Merge.nil erm ern
    case app_N st' =>
      have ⟨_, _, tyP⟩ := erm.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have ⟨n2, st, ern2⟩ := ihn rfl rfl st'
      have rd := st.toStatic ern.toStatic
      exists (.app m1 n2 .ex); and_intros
      . constructor; assumption
      . apply Erased.conv
        apply Static.Conv.subst1
        apply (Star.conv (st.toStatic ern.toStatic)).sym
        apply Erased.app_ex
        . apply Merge.nil
        . assumption
        . assumption
        . apply tyB.subst ern.toStatic
    case beta vl' e0 =>
      have ⟨A, m, r, e⟩ := erm.lam_preimage; subst e
      cases r with
      | im =>
        have ⟨_, _, _, eq⟩ := erm.toDynamic.lam_im_inv'
        have ⟨e, _⟩ := Static.Conv.pi_inj eq
        contradiction
      | ex =>
        replace ⟨rA, sA, rs, erm⟩ := erm.lam_ex_inv
        have vl := ern.value_preimage vl'
        cases rs with
        | extend =>
          exists m.[n1/]; and_intros
          . constructor; aesop
          . simp at e0; subst e0
            apply erm.subst_ex (Lower.nil sA) Merge.nil ern
        | weaken =>
          exists m.[n1/]; and_intros
          . constructor; aesop
          . simp at e0; subst e0
            apply erm.subst_im ern.toStatic
  case tup_im m m' n s _ tyS erm tyn ih =>
    subst_vars; cases st
    case tup_M st' =>
      have ⟨m1, st, erm1⟩ := ih rfl rfl st'
      have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
      exists .tup m1 n .im s; and_intros
      . constructor; assumption
      . constructor
        . assumption
        . assumption
        . apply Static.Typed.conv
          apply Static.Conv.subst1
          apply Star.conv (st.toStatic erm.toStatic)
          assumption
          apply tyB.subst erm1.toStatic
    case tup_N st' => cases st'
  case tup_ex m m' n n' s _ mrg tyS erm ern ihm ihn =>
    have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
    subst_vars; cases mrg; cases st
    case tup_M st =>
      have ⟨m1, st, erm1⟩ := ihm rfl rfl st
      exists .tup m1 n .ex s; and_intros
      . constructor; assumption
      . constructor
        . constructor
        . assumption
        . assumption
        . apply Erased.conv
          apply Static.Conv.subst1
          apply Star.conv (st.toStatic erm.toStatic)
          assumption
          apply tyB.subst erm1.toStatic
    case tup_N st =>
      have ⟨n1, st, ern1⟩ := ihn rfl rfl st
      exists .tup m n1 .ex s; and_intros
      constructor
      . assumption
      . constructor <;> aesop
  case prj_im C m m' n n' rA s sA sB sC iC c rs mrg tyC erm ern ihm _ =>
    subst_vars; cases mrg; cases st
    case prj_M st' =>
      have ⟨m1, st, erm1⟩ := ihm rfl rfl st'
      exists .prj C m1 n .im; and_intros
      . constructor; assumption
      . apply Erased.conv
        . apply Static.Conv.subst1
          apply (Star.conv (st.toStatic erm.toStatic)).sym
        . apply Erased.prj_im rs Merge.nil tyC erm1 ern
        . apply tyC.subst erm.toStatic
    case prj_elim m1 m2 m1' m2' s vl' e1 e2 =>
      have ⟨m1, m2, r, e⟩ := erm.tup_preimage; subst_vars
      cases r with
      | im =>
        have ⟨erm1, erm2, _, _⟩ := erm.tup_im_inv; subst_vars
        cases vl'; case tup vl' _ =>
        have vl := erm1.value_preimage vl'
        rw[show C.[.tup m1 m2 .im s/]
              = C.[.tup (.var 1) (.var 0) .im s .: shift 2].[m2,m1/] by asimp]
        exists n.[m2,m1/]; and_intros
        . aesop
        . apply ern.substitution
          apply AgreeSubst.wk_im erm2
          cases rs with
          | extend =>
            apply AgreeSubst.wk_ex Merge.nil; constructor; asimp; assumption
            apply AgreeSubst.refl Wf.nil
          | weaken =>
            apply AgreeSubst.wk_im; asimp; apply erm1.toStatic
            apply AgreeSubst.refl Wf.nil
      | ex =>
        have ⟨_, _, _, _, _, _, _, eq⟩ := erm.toDynamic.tup_ex_inv'
        have ⟨e, _⟩ := Static.Conv.sig_inj eq
        contradiction
  case prj_ex C m m' n n' rA rB s sA sB sC iC c1 c2 rs1 rs2 mrg tyC erm ern ihm ihn =>
    subst_vars; cases mrg; cases st
    case prj_M st' =>
      have ⟨m1, st, erm1⟩ := ihm rfl rfl st'
      exists .prj C m1 n .ex; and_intros
      . constructor; assumption
      . apply Erased.conv
        . apply Static.Conv.subst1
          apply (Star.conv (st.toStatic erm.toStatic)).sym
        . apply Erased.prj_ex rs1 rs2 Merge.nil tyC erm1 ern
        . apply tyC.subst erm.toStatic
    case prj_elim m1' m2' s vl' e1 e2 =>
      have ⟨m1, m2, r, e⟩ := erm.tup_preimage; subst_vars
      cases r with
      | im =>
        have ⟨_, _, _, _, eq⟩ := erm.toDynamic.tup_im_inv'
        have ⟨e, _⟩ := Static.Conv.sig_inj eq
        contradiction
      | ex =>
        have ⟨Δ1, Δ2, mrg, erm1, erm2, _⟩ := erm.tup_ex_inv; subst_vars
        cases vl'; case tup vl1' vl2' =>
        have vl1 := erm1.value_preimage vl1'
        have vl2 := erm2.value_preimage vl2'
        cases mrg
        rw[show C.[.tup m1 m2 .ex s/]
              = C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[m2,m1/] by asimp]
        exists n.[m2,m1/]; and_intros
        . aesop
        . apply ern.substitution
          cases rs1 with
          | extend =>
            cases rs2 with
            | extend =>
              apply AgreeSubst.wk_ex Merge.nil; constructor; assumption
              apply AgreeSubst.wk_ex Merge.nil; constructor; asimp; assumption
              apply AgreeSubst.refl Wf.nil
            | weaken =>
              apply AgreeSubst.wk_im; apply erm2.toStatic
              apply AgreeSubst.wk_ex Merge.nil; constructor; asimp; assumption
              apply AgreeSubst.refl Wf.nil
          | weaken =>
            cases rs2 with
            | extend =>
              apply AgreeSubst.wk_ex Merge.nil; constructor; assumption
              apply AgreeSubst.wk_im; asimp; apply erm1.toStatic
              apply AgreeSubst.refl Wf.nil
            | weaken =>
              apply AgreeSubst.wk_im; apply erm2.toStatic
              apply AgreeSubst.wk_im; asimp; apply erm1.toStatic
              apply AgreeSubst.refl Wf.nil
  case ite A m m' n1 n1' n2 n2' _ _ mrg tyA erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg; cases st
    case ite_M st =>
      have ⟨m1, st, erm1⟩ := ihm rfl rfl st
      exists .ite A m1 n1 n2; and_intros
      . aesop
      . apply Erased.conv
        . apply Static.Conv.subst1
          apply (Star.conv (st.toStatic erm.toStatic)).sym
        . constructor
          . apply Merge.nil
          . assumption
          . assumption
          . assumption
          . assumption
        . apply tyA.subst erm.toStatic
    case ite_tt => have e := erm.tt_preimage; subst e; aesop
    case ite_ff => have e := erm.ff_preimage; subst e; aesop
  case rw A B m m' n a b s i tyA erm tyn ih =>
    subst_vars
    have ⟨n', vl, rd⟩ := Static.Typed.red_value tyn
    have tyn' := tyn.preservation' rd
    have ⟨a', _⟩ := tyn'.idn_canonical Conv.R vl; subst_vars
    have ⟨_, _, tyI⟩ := tyn.validity
    have ⟨_, tya, tyb, eq⟩ := tyI.idn_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj eq; subst_vars
    have ⟨tya', eq1, eq2⟩ := tyn'.rfl_inv
    have sc : Static.SConv (.rfl a .: a .: ids) (n .: b .: ids) := by
      intro x; match x with
      | .zero =>
        asimp; apply Conv.trans;
        apply (Static.Conv.rfl eq1).sym
        apply (Star.conv rd).sym
      | .succ .zero => asimp; apply Conv.trans eq1.sym eq2
      | .succ (.succ _) => asimp; constructor
    have : [] ⊢ A.[n,b/] : .srt s i := by
      rw[show .srt s i = (.srt s i).[n,b/] by asimp]
      apply Static.Typed.substitution
      . assumption
      . apply Static.AgreeSubst.wk; asimp; assumption
        apply Static.AgreeSubst.wk; asimp; assumption
        apply Static.AgreeSubst.refl
        apply tyn.toWf
    cases st
    exists m; and_intros
    . constructor
    . apply Erased.conv
      . apply Static.Conv.compat; assumption
      . assumption
      . assumption
  case conv eq _ tyB ihm =>
    subst_vars
    have ⟨m', st', erm'⟩ := ihm rfl rfl st
    exists m'; and_intros
    . assumption
    . apply erm'.conv eq tyB

theorem Erased.preservation' {A m1 : SStruct.Tm Srt} {m2 m2'} :
    [] ;; [] ⊢ m1 ▷ m2 : A -> m2 ~>>* m2' ->
    ∃ m1', m1 ~>>* m1' ∧ [] ;; [] ⊢ m1' ▷ m2' : A := by
  intro er rd
  induction rd generalizing A m1
  case R => exists m1; and_intros <;> aesop
  case SE rd st ih =>
    have ⟨m2', rd', er'⟩ := ih er
    have ⟨m3', st', erm'⟩ := er'.preservation st
    exists m3'; and_intros
    . apply Star.SE <;> assumption
    . assumption
