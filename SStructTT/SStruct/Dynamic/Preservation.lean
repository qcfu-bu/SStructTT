import SStructTT.SStruct.Static.Normalize
import SStructTT.SStruct.Dynamic.Step
import SStructTT.SStruct.Dynamic.Inversion
open ARS SStruct.Static

namespace SStruct.Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Step.toStatic1 {A m n : Tm Srt} :
    [] ⊢ m : A -> m ~>> n -> m ~>1 n := by
  generalize e: [] = Γ; intro ty st;
  induction ty generalizing n <;> try trivial
  case app m n _ _ _ _ ihm ihn =>
    subst_vars; cases st
    case app_M st =>
      have ⟨m', st, rd⟩ := (ihm rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.app_M; assumption
      . apply Static.Red.app <;> aesop
    case app_N st =>
      have ⟨n', st, rd⟩ := (ihn rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.app_N; assumption
      . apply Static.Red.app <;> aesop
    case beta_im m _ _ =>
      apply Star1.E; constructor
    case beta_ex m _ _ _ =>
      apply Star1.E; constructor
  case tup m n _ s _ _ _ _ _ ihm ihn =>
    subst_vars; cases st
    case tup_im_N st _ _ =>
      have ⟨n', st, rd⟩ := (ihn rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.tup_N; assumption
      . apply Static.Red.tup <;> aesop
    case tup_ex_M st _ _ =>
      have ⟨m', st, rd⟩ := (ihm rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.tup_M; assumption
      . apply Static.Red.tup <;> aesop
    case tup_ex_N st _ _ =>
      have ⟨n', st, rd⟩ := (ihn rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.tup_N; assumption
      . apply Static.Red.tup <;> aesop
  case prj C m n _ _ _ _ _ _ _ _ ihm ihn =>
    subst_vars; cases st
    case prj_M st =>
      have ⟨m', st, rd⟩ := (ihm rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.prj_M; assumption
      . apply Static.Red.prj <;> aesop
    case prj_im_elim m1 m2 _ _ _ =>
      apply Star1.E; constructor
    case prj_ex_elim m1 m2 _ _ _ =>
      apply Star1.E; constructor
  case ite A m n1 n2 _ _ _ _ _ _ _ ihm ihn1 ihn2 =>
    subst_vars; cases st
    case ite_M st =>
      have ⟨m', st, rd⟩ := (ihm rfl st).ES_split
      apply Star1.ES_join
      . apply Static.Step.ite_M; assumption
      . apply Static.Red.ite <;> aesop
    case ite_tt => apply Star1.E; constructor
    case ite_ff => apply Star1.E; constructor
  case rw A B m n _ _ _ _ _ _ tyn _ ihm ihn =>
    subst_vars
    have ⟨n', vl, rd⟩ := Static.Typed.red_value tyn
    have tyn' := tyn.preservation' rd
    have ⟨a', _⟩ := tyn'.idn_canonical Conv.R vl; subst_vars
    cases st
    match Star.ES_split rd with
    | .inl _ => subst_vars; apply Star1.E; constructor
    | .inr ⟨n', st, rd⟩ =>
      apply Star1.ES_join
      . apply Static.Step.rw_N; assumption
      . apply Star.trans
        apply Red.rw Star.R Star.R rd
        apply Star.one; constructor
  case conv => aesop

lemma Step.toStatic {A m n : Tm Srt} :
    ([] : Static.Ctx Srt) ⊢ m : A -> m ~>> n -> m ~>* n := by
  intro ty st
  apply (st.toStatic1 ty).toStar

lemma Red.toStatic {A m n : Tm Srt} :
    ([] : Static.Ctx Srt) ⊢ m : A -> m ~>>* n -> m ~>* n := by
  intro tym rd
  induction rd
  case R => constructor
  case SE st ih =>
  have ty := tym.preservation' ih
  have rd := Step.toStatic ty st
  apply Star.trans ih rd

theorem Typed.preservation {A m m' : Tm Srt} :
    [] ⊢ m :: A -> m ~>> m' -> [] ⊢ m' :: A := by
  generalize e: [] = Δ
  intro ty st; induction ty generalizing m'
  all_goals try trivial
  case app_im m n s tym tyn ih =>
    subst_vars; cases st
    case app_M st =>
      have tym' := ih rfl st
      apply Typed.app_im tym' tyn
    case app_N st =>
      have ⟨_, _, tyP⟩ := tym.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have rd := st.toStatic tyn
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tyn)).sym
      . apply Typed.app_im
        . assumption
        . apply tyn.preservation' rd
      . apply tyB.subst tyn
    case beta_im =>
      replace ⟨sA, tym⟩ := tym.lam_im_inv
      apply tym.subst_im tyn
    case beta_ex =>
      have ⟨_, _, _, eq⟩ := tym.lam_ex_inv'
      have ⟨e, _⟩ := Static.Conv.pi_inj eq; cases e
  case app_ex mrg tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case app_M st =>
      have tym' := ihm rfl st
      apply Typed.app_ex Merge.nil tym' tyn
    case app_N st =>
      have ⟨_, _, tyP⟩ := tym.validity
      have ⟨_, _, _, tyB, _⟩ := tyP.pi_inv
      have rd := st.toStatic tyn.toStatic
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tyn.toStatic)).sym
      . apply Typed.app_ex
        . apply Merge.nil
        . assumption
        . apply ihn rfl st
      . apply tyB.subst tyn.toStatic
    case beta_im =>
      have ⟨_, _, _, eq⟩ := tym.lam_im_inv'
      have ⟨e, _⟩ := Static.Conv.pi_inj eq; cases e
    case beta_ex =>
      replace ⟨sA, tym⟩ := tym.lam_ex_inv
      apply tym.subst_ex (Lower.nil sA) Merge.nil tyn
  case tup_im tyS tym tyn ih =>
    subst_vars; cases st
    case tup_im_N st =>
      have tym' := ih rfl st
      have ⟨_, _, _, tyB, _⟩ := tyS.sig_inv
      constructor
      . assumption
      . assumption
      . assumption
  case tup_ex mrg tyS tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case tup_ex_M st =>
      have tym' := ihm rfl st
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
      . apply ihn rfl st
  case prj_im C m n s sA sB sC iC mrg tyC tym tyn ihm _ =>
    subst_vars; cases mrg; cases st
    case prj_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tym.toStatic)).sym
      . apply Typed.prj_im Merge.nil tyC (ihm rfl st) tyn
      . apply tyC.subst tym.toStatic
    case prj_im_elim m1 m2 s vl =>
      have ⟨tym1, tym2, _⟩ := tym.tup_im_inv; subst_vars
      rw[show C.[.tup m1 m2 .im s/]
            = C.[.tup (.var 1) (.var 0) .im s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.intro_ex Merge.nil; constructor; assumption
      apply AgreeSubst.intro_im; asimp; assumption
      apply AgreeSubst.refl Wf.nil
    case prj_ex_elim =>
      have ⟨_, _, _, _, _, _, _, eq⟩ := tym.tup_ex_inv'
      have ⟨e, _⟩ := Static.Conv.sig_inj eq; cases e
  case prj_ex C m n s sA sB sC iC mrg tyC tym tyn ihm ihn =>
    subst_vars; cases mrg; cases st
    case prj_M st =>
      apply Typed.conv
      . apply Conv.subst1
        apply (Star.conv (st.toStatic tym.toStatic)).sym
      . apply Typed.prj_ex Merge.nil tyC (ihm rfl st) tyn
      . apply tyC.subst tym.toStatic
    case prj_im_elim =>
      have ⟨_, _, _, _, eq⟩ := tym.tup_im_inv'
      have ⟨e, _⟩ := Static.Conv.sig_inj eq; cases e
    case prj_ex_elim m1 m2 s vl =>
      have ⟨Δ1, Δ2, mrg, tym1, tym2, _⟩ := tym.tup_ex_inv; subst_vars
      cases mrg
      rw[show C.[.tup m1 m2 .ex s/]
            = C.[.tup (.var 1) (.var 0) .ex s .: shift 2].[m2,m1/] by asimp]
      apply tyn.substitution
      apply AgreeSubst.intro_ex Merge.nil; constructor; assumption
      apply AgreeSubst.intro_ex Merge.nil; constructor; asimp; assumption
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
        . apply ihm rfl st
        . assumption
        . assumption
      . apply tyA.subst tym.toStatic
    case ite_tt => assumption
    case ite_ff => assumption
  case rw A B m n a b s i tyA tym tyn ih =>
    subst_vars
    have ⟨eq, ty⟩ := tyn.closed_idn tyA
    cases st
    apply Typed.conv <;> assumption
  case drop mrg lw h tyn ihn =>
    subst_vars; cases mrg; aesop
  case conv eq _ tyB ihm =>
    subst_vars; have tym := ihm rfl st
    apply tym.conv eq tyB

theorem Typed.preservation' {A m m' : Tm Srt} :
    [] ⊢ m :: A -> m ~>>* m' -> [] ⊢ m' :: A := by
  intro ty rd
  induction rd generalizing A
  case R => assumption
  case SE rd st ih =>
    apply (ih ty).preservation st
