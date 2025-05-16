import SStructTT.SStruct.Static.Normalize
import SStructTT.SStruct.Dynamic.Step
import SStructTT.SStruct.Dynamic.Inversion
open ARS SStruct.Static

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Step.toStatic' {A m n : Tm Srt} :
    [] ⊢ m : A -> m ~>> n -> ∃ x, m ~> x ∧ x ~>* n := by
  generalize e: [] = Γ; intro ty st;
  induction ty generalizing n <;> try trivial
  case app m n _ _ _ _ ihm ihn =>
    subst_vars; cases st
    case app_im_M st _ =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.app m' n .im; and_intros
      . constructor; assumption
      . apply Red.app <;> aesop
    case app_ex_M st _ =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.app m' n .ex; and_intros
      . constructor; assumption
      . apply Red.app <;> aesop
    case app_ex_N st _ =>
      have ⟨n', st, rd⟩ := ihn rfl st
      exists Tm.app m n' .ex; and_intros
      . constructor; assumption
      . apply Red.app <;> aesop
    case beta_im m _ _ =>
      exists m.[n/]; and_intros <;> constructor
    case beta_ex m _ _ _ =>
      exists m.[n/]; and_intros <;> constructor
  case tup m n _ s _ _ _ _ _ ihm ihn =>
    subst_vars; cases st
    case tup_im_M st _ _ =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.tup m' n .im s; and_intros
      . constructor; assumption
      . apply Red.tup <;> aesop
    case tup_ex_M st _ _ =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.tup m' n .ex s; and_intros
      . constructor; assumption
      . apply Red.tup <;> aesop
    case tup_ex_N st _ _ =>
      have ⟨n', st, rd⟩ := ihn rfl st
      exists Tm.tup m n' .ex s; and_intros
      . constructor; assumption
      . apply Red.tup <;> aesop
  case proj C m n _ _ _ _ _ _ _ _ ihm ihn =>
    subst_vars; cases st
    case proj_im_M st _ _ _ _ =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.proj C m' n .im; and_intros
      . constructor; assumption
      . apply Red.proj <;> aesop
    case proj_ex_M st _ _ _ _ =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.proj C m' n .ex; and_intros
      . constructor; assumption
      . apply Red.proj <;> aesop
    case proj_im_elim m1 m2 _ _ _ _ _ _ =>
      exists n.[m2,m1/]; and_intros <;> constructor
    case proj_ex_elim m1 m2 _ _ _ _ _ _ =>
      exists n.[m2,m1/]; and_intros <;> constructor
  case ite A m n1 n2 _ _ _ _ _ _ _ ihm ihn1 ihn2 =>
    subst_vars; cases st
    case ite_M st =>
      have ⟨m', st, rd⟩ := ihm rfl st
      exists Tm.ite A m' n1 n2; and_intros
      . constructor; assumption
      . apply Red.ite <;> aesop
    case ite_tt => exists n1; and_intros <;> constructor
    case ite_ff => exists n2; and_intros <;> constructor
  case rw A B m n _ _ _ _ _ _ tyn _ ihm ihn =>
    subst_vars
    have ⟨n', vl, rd⟩ := Static.Typed.red_value tyn
    have tyn' := tyn.preservation' rd
    have ⟨a', _⟩ := tyn'.idn_canonical Conv.R vl; subst_vars
    cases st
    match Star.ES_split rd with
    | .inl _ => subst_vars; exists m; and_intros <;> constructor
    | .inr ⟨n', st, rd⟩ =>
      exists Tm.rw A m n'; and_intros
      . constructor; assumption
      . apply Star.trans
        apply Red.rw Star.R Star.R rd
        apply Star.one; constructor
  case conv => aesop

lemma Step.toStatic {A m n : Tm Srt} :
    [] ⊢ m : A -> m ~>> n -> m ~>* n := by
  intro ty st
  have ⟨x, st, rd⟩ := st.toStatic' ty
  apply Star.ES <;> assumption

theorem Typed.preservation {A m m' : Tm Srt} :
    [] ;; [] ⊢ m : A -> m ~>> m' -> [] ;; [] ⊢ m' : A := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ty st; induction ty generalizing m'
  all_goals try trivial
  case app_im m n s tym tyn ih =>
    subst_vars; cases st
    case app_im_M st =>
      have tym' := ih rfl rfl st
      apply Typed.app_im tym' tyn
    case beta_im =>
      replace ⟨sA, tym⟩ := tym.lam_im_inv
      apply tym.subst_im tyn
  case app_ex mrg tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case app_ex_M st =>
      have tym' := ihm rfl rfl st
      apply Typed.app_ex Merge.nil tym' tyn
    case app_ex_N st =>
      have ⟨_, _, tyP⟩ := tym.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have rd := st.toStatic tyn.toStatic
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tyn.toStatic)).sym
      . apply Typed.app_ex
        . apply Merge.nil
        . assumption
        . apply ihn rfl rfl st
      . apply tyB.subst tyn.toStatic
    case beta_ex =>
      replace ⟨rA, sA, rs, tym⟩ := tym.lam_ex_inv
      cases rs with
      | extend => apply tym.subst_ex (Lower.nil sA) Merge.nil tyn
      | weaken => apply tym.subst_im tyn.toStatic
  case tup_im tyS tym tyn ih =>
    subst_vars; cases st
    case tup_im_M st =>
      have tym' := ih rfl rfl st
      have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
      constructor
      . assumption
      . assumption
      . apply Static.Typed.conv
        apply Conv.subst1
        apply Star.conv (st.toStatic tym.toStatic)
        assumption
        apply tyB.subst tym'.toStatic
  case tup_ex mrg tyS tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case tup_ex_M st =>
      have tym' := ihm rfl rfl st
      have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
      constructor
      . constructor
      . assumption
      . assumption
      . apply Typed.conv
        apply Conv.subst1
        apply Star.conv (st.toStatic tym.toStatic)
        assumption
        apply tyB.subst tym'.toStatic
    case tup_ex_N st =>
      constructor
      . constructor
      . assumption
      . assumption
      . apply ihn rfl rfl st
  case proj_im C m n rA s sA sB sC iC rs mrg tyC tym tyn ihm _ =>
    subst_vars; cases mrg; cases st
    case proj_im_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tym.toStatic)).sym
      . apply Typed.proj_im rs Merge.nil tyC (ihm rfl rfl st) tyn
      . apply tyC.subst tym.toStatic
    case proj_im_elim m1 m2 s vl =>
      have ⟨tym1, tym2, _⟩ := tym.tup_im_inv; subst_vars
      rw[show C.[.tup m1 m2 .im s/]
            = C.[.tup (.var 1) (.var 0) .im s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.wk_im tym2
      cases rs with
      | extend =>
        apply AgreeSubst.wk_ex Merge.nil; constructor; asimp; assumption
        apply AgreeSubst.refl Wf.nil
      | weaken =>
        apply AgreeSubst.wk_im; asimp; apply tym1.toStatic
        apply AgreeSubst.refl Wf.nil
  case proj_ex C m n rA rB s sA sB sC iC rs1 rs2 mrg tyC tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case proj_ex_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tym.toStatic)).sym
      . apply Typed.proj_ex rs1 rs2 Merge.nil tyC (ihm rfl rfl st) tyn
      . apply tyC.subst tym.toStatic
    case proj_ex_elim m1 m2 s vl =>
      have ⟨Δ1, Δ2, mrg, tym1, tym2, _⟩ := tym.tup_ex_inv; subst_vars
      cases mrg
      rw[show C.[.tup m1 m2 .ex s/]
            = C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      cases rs1 with
      | extend =>
        cases rs2 with
        | extend =>
          apply AgreeSubst.wk_ex Merge.nil; constructor; assumption
          apply AgreeSubst.wk_ex Merge.nil; constructor; asimp; assumption
          apply AgreeSubst.refl Wf.nil
        | weaken =>
          apply AgreeSubst.wk_im; apply tym2.toStatic
          apply AgreeSubst.wk_ex Merge.nil; constructor; asimp; assumption
          apply AgreeSubst.refl Wf.nil
      | weaken =>
        cases rs2 with
        | extend =>
          apply AgreeSubst.wk_ex Merge.nil; constructor; assumption
          apply AgreeSubst.wk_im; asimp; apply tym1.toStatic
          apply AgreeSubst.refl Wf.nil
        | weaken =>
          apply AgreeSubst.wk_im; apply tym2.toStatic
          apply AgreeSubst.wk_im; asimp; apply tym1.toStatic
          apply AgreeSubst.refl Wf.nil
  case ite mrg tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg; cases st
    case ite_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tym.toStatic)).sym
      . constructor
        . apply Merge.nil
        . assumption
        . apply ihm rfl rfl st
        . assumption
        . assumption
      . apply tyA.subst tym.toStatic
    case ite_tt => assumption
    case ite_ff => assumption
  case rw A B m n a b s i tyA tym tyn ih =>
    subst_vars
    have ⟨n', vl, rd⟩ := Static.Typed.red_value tyn
    have tyn' := tyn.preservation' rd
    have ⟨a', _⟩ := tyn'.idn_canonical Conv.R vl; subst_vars
    have ⟨_, _, tyI⟩ := tyn.validity
    have ⟨_, tya, tyb, eq⟩ := tyI.idn_inv
    have ⟨_, _⟩ := Conv.srt_inj eq; subst_vars
    have ⟨tya', eq1, eq2⟩ := tyn'.rfl_inv
    have sc : SConv (.rfl a .: a .: ids) (n .: b .: ids) := by
      intro x; match x with
      | .zero =>
        asimp; apply Conv.trans;
        apply (Conv.rfl eq1).sym
        apply (Star.conv rd).sym
      | .succ .zero => asimp; apply Conv.trans eq1.sym eq2
      | .succ (.succ _) => asimp; constructor
    have : [] ⊢ A.[n,b/] : .srt s i := by
      rw[show .srt s i = (.srt s i).[n,b/] by asimp]
      apply Static.Typed.substitution
      . assumption
      . apply AgreeSubst.wk; asimp; assumption
        apply AgreeSubst.wk; asimp; assumption
        apply Static.AgreeSubst.refl
        apply tyn.toWf
    cases st
    apply Typed.conv
    . apply Conv.compat; assumption
    . assumption
    . assumption
  case conv eq _ tyB ihm =>
    subst_vars; have tym := ihm rfl rfl st
    apply tym.conv eq tyB

theorem Typed.preservation' {A m m' : Tm Srt} :
    [] ;; [] ⊢ m : A -> m ~>>* m' -> [] ;; [] ⊢ m' : A := by
  intro ty rd
  induction rd generalizing A
  case R => assumption
  case SE rd st ih =>
    apply (ih ty).preservation st
