import SStructTT.MLTT.Progress
open ARS

namespace MLTT

@[scoped aesop safe [constructors]]
inductive Neutral : Tm -> Prop where
  | var x : Neutral (.var x)
  | app m n :
    Neutral m ->
    Neutral (.app m n)
  | prj A m n :
    Neutral m ->
    Neutral (.prj A m n)
  | ite A m n1 n2 :
    Neutral m ->
    Neutral (.ite A m n1 n2)
  | rw A m n :
    Neutral n ->
    Neutral (.rw A m n)
  | exf A m :
    Neutral m ->
    Neutral (.exf A m)

lemma Neutral.not_lam {A m : Tm} : ¬ Neutral (.lam A m) := by
  intro h; cases h

lemma Neutral.not_tup {m n : Tm} : ¬ Neutral (.tup m n) := by
  intro h; cases h

lemma Neutral.not_tt : ¬ Neutral .tt := by
  intro h; cases h

lemma Neutral.not_ff : ¬ Neutral .ff := by
  intro h; cases h

lemma Neutral.not_rfl {m : Tm} : ¬ Neutral (.rfl m) := by
  intro h; cases h

lemma Neutral.step {m n : Tm} :
    Neutral m -> m ~> n -> Neutral n := by
  intro neu st
  induction neu generalizing n
  case var => cases st
  case app m a neu ih =>
    cases st with
    | app_M a stM =>
      exact Neutral.app _ _ (ih stM)
    | app_N m stN =>
      exact Neutral.app _ _ neu
    | beta A body a =>
      exact (Neutral.not_lam neu).elim
  case prj A m branch neu ih =>
    cases st with
    | prj_A m branch stA =>
      exact Neutral.prj _ _ _ neu
    | prj_M A branch stM =>
      exact Neutral.prj _ _ _ (ih stM)
    | prj_N A m stN =>
      exact Neutral.prj _ _ _ neu
    | prj_elim A m1 m2 branch =>
      exact (Neutral.not_tup neu).elim
  case ite A m n1 n2 neu ih =>
    cases st with
    | ite_A m n1 n2 stA =>
      exact Neutral.ite _ _ _ _ neu
    | ite_M A n1 n2 stM =>
      exact Neutral.ite _ _ _ _ (ih stM)
    | ite_N1 A m n2 st1 =>
      exact Neutral.ite _ _ _ _ neu
    | ite_N2 A m n1 st2 =>
      exact Neutral.ite _ _ _ _ neu
    | ite_tt A n1 n2 =>
      exact Neutral.not_tt neu |>.elim
    | ite_ff A n1 n2 =>
      exact Neutral.not_ff neu |>.elim
  case rw A m p neu ih =>
    cases st with
    | rw_A m p stA =>
      exact Neutral.rw _ _ _ neu
    | rw_M A p stM =>
      exact Neutral.rw _ _ _ neu
    | rw_N A m stN =>
      exact Neutral.rw _ _ _ (ih stN)
    | rw_elim A m p =>
      exact (Neutral.not_rfl neu).elim
  case exf A m neu ih =>
    cases st with
    | exf_A m stA =>
      exact Neutral.exf _ _ neu
    | exf_M A stM =>
      exact Neutral.exf _ _ (ih stM)

lemma Neutral.red {m n : Tm} :
    Neutral m -> m ~>* n -> Neutral n := by
  intro neu rd
  induction rd
  case R => assumption
  case SE rd st ih =>
    exact ih.step st

lemma Neutral.not_red_lam {m A body : Tm} :
    Neutral m -> ¬ m ~>* .lam A body := by
  intro neu rd
  exact Neutral.not_lam (neu.red rd)

lemma Neutral.not_red_tup {m m1 m2 : Tm} :
    Neutral m -> ¬ m ~>* .tup m1 m2 := by
  intro neu rd
  exact Neutral.not_tup (neu.red rd)

lemma Neutral.not_red_tt {m : Tm} :
    Neutral m -> ¬ m ~>* .tt := by
  intro neu rd
  exact Neutral.not_tt (neu.red rd)

lemma Neutral.not_red_ff {m : Tm} :
    Neutral m -> ¬ m ~>* .ff := by
  intro neu rd
  exact Neutral.not_ff (neu.red rd)

lemma Neutral.not_red_rfl {m n : Tm} :
    Neutral m -> ¬ m ~>* .rfl n := by
  intro neu rd
  exact Neutral.not_rfl (neu.red rd)

lemma Conv.not_tt_ff : ¬ (.tt === .ff) := by
  intro eq
  have ⟨z, rtt, rff⟩ := Step.cr eq
  have e1 := Red.tt_inv rtt
  have e2 := Red.ff_inv rff
  rw [e1] at e2
  cases e2

lemma Conv.not_ff_tt : ¬ (.ff === .tt) := by
  intro eq
  exact Conv.not_tt_ff eq.sym

lemma sn_step {m n : Tm} : SN Step m -> m ~> n -> SN Step n := by
  intro sn st
  cases sn with
  | intro h => exact h st

lemma sn_red {m n : Tm} : SN Step m -> m ~>* n -> SN Step n := by
  intro sn rd
  induction rd
  case R => assumption
  case SE rd st ih => exact sn_step ih st

def down1 : Var -> Tm
  | 0 => .var 0
  | x + 1 => .var x

lemma shift_down1 : (shift 1 : Var -> Tm) !> down1 = ids := by
  funext x
  asimp [down1]

lemma subst_shift1_down1 (m : Tm) : m.[shift 1].[down1] = m := by
  rw [Tm.subst_comp, shift_down1, Tm.subst_id]

lemma subst_shift_shift (m : Tm) (i j : Nat) :
    m.[shift i].[shift j] = m.[shift (i + j)] := by
  rw [Tm.subst_comp, SubstLemmas.shift_comp]

def shiftSubst (σ : Var -> Tm) (i : Nat) : Var -> Tm :=
  fun x => (σ x).[shift i]

lemma shiftSubst_zero (σ : Var -> Tm) :
    shiftSubst σ 0 = σ := by
  funext x
  asimp [shiftSubst]

lemma shiftSubst_add (σ : Var -> Tm) (i j : Nat) :
    shiftSubst (shiftSubst σ i) j = shiftSubst σ (i + j) := by
  funext x
  simp [shiftSubst, subst_shift_shift]

lemma SRed.scons_same {σ τ : Var -> Tm} {m : Tm} :
    SRed σ τ -> SRed (m .: σ) (m .: τ) := by
  intro h x
  cases x with
  | zero =>
    asimp
    exact Star.R
  | succ x =>
    asimp
    exact h x

lemma SConv.scons_same {σ τ : Var -> Tm} {m : Tm} :
    SConv σ τ -> SConv (m .: σ) (m .: τ) := by
  intro h x
  cases x with
  | zero =>
    asimp
    exact Conv.R
  | succ x =>
    asimp
    exact h x

lemma sn_shift {m : Tm} : SN Step m -> SN Step m.[shift 1] := by
  intro hsn
  have hmap : ∀ x y, Step x y -> Step x.[down1] y.[down1] := by
    intro x y st
    exact Step.subst down1 st
  have htarget : SN Step ((m.[shift 1]).[down1]) := by
    simpa [subst_shift1_down1] using hsn
  exact SN.preimage (e := Step) (x := m.[shift 1]) (f := fun t => t.[down1]) hmap htarget

lemma sn_shiftn {m : Tm} (i : Nat) : SN Step m -> SN Step m.[shift i] := by
  intro hsn
  induction i with
  | zero =>
    simpa [SubstLemmas.shift0, Tm.subst_id] using hsn
  | succ i ih =>
    have h := sn_shift ih
    simpa [subst_shift_shift] using h

lemma sn_var {x : Var} : SN Step (.var x) := by
  constructor
  intro y st
  cases st

lemma sn_ty {i : Nat} : SN Step (.ty i) := by
  constructor
  intro y st
  cases st

lemma sn_bool : SN Step .bool := by
  constructor
  intro y st
  cases st

lemma sn_tt : SN Step .tt := by
  constructor
  intro y st
  cases st

lemma sn_ff : SN Step .ff := by
  constructor
  intro y st
  cases st

lemma sn_bot : SN Step .bot := by
  constructor
  intro y st
  cases st

lemma sn_pi {A B : Tm} :
    SN Step A -> SN Step B -> SN Step (.pi A B) := by
  intro snA
  induction snA generalizing B
  case intro A ihA ihA' =>
    intro snB
    induction snB
    case intro B ihB ihB' =>
      constructor
      intro y st
      cases st with
      | pi_A B stA =>
        exact ihA' stA (SN.intro ihB)
      | pi_B A stB =>
        exact ihB' stB

lemma sn_lam {A m : Tm} :
    SN Step A -> SN Step m -> SN Step (.lam A m) := by
  intro snA
  induction snA generalizing m
  case intro A ihA ihA' =>
    intro snm
    induction snm
    case intro m ihm ihm' =>
      constructor
      intro y st
      cases st with
      | lam_A m stA =>
        exact ihA' stA (SN.intro ihm)
      | lam_M A stM =>
        exact ihm' stM

lemma sn_sig {A B : Tm} :
    SN Step A -> SN Step B -> SN Step (.sig A B) := by
  intro snA
  induction snA generalizing B
  case intro A ihA ihA' =>
    intro snB
    induction snB
    case intro B ihB ihB' =>
      constructor
      intro y st
      cases st with
      | sig_A B stA =>
        exact ihA' stA (SN.intro ihB)
      | sig_B A stB =>
        exact ihB' stB

lemma sn_tup {m n : Tm} :
    SN Step m -> SN Step n -> SN Step (.tup m n) := by
  intro snm
  induction snm generalizing n
  case intro m ihm ihm' =>
    intro snn
    induction snn
    case intro n ihn ihn' =>
      constructor
      intro y st
      cases st with
      | tup_M n stM =>
        exact ihm' stM (SN.intro ihn)
      | tup_N m stN =>
        exact ihn' stN

lemma sn_idn {A m n : Tm} :
    SN Step A -> SN Step m -> SN Step n -> SN Step (.idn A m n) := by
  intro snA
  induction snA generalizing m n
  case intro A ihA ihA' =>
    intro snm
    induction snm generalizing n
    case intro m ihm ihm' =>
      intro snn
      induction snn
      case intro n ihn ihn' =>
        constructor
        intro y st
        cases st with
        | idn_A m n stA =>
          exact ihA' stA (SN.intro ihm) (SN.intro ihn)
        | idn_M A n stM =>
          exact ihm' stM (SN.intro ihn)
        | idn_N A m stN =>
          exact ihn' stN

lemma sn_rfl {m : Tm} :
    SN Step m -> SN Step (.rfl m) := by
  intro snm
  induction snm
  case intro m ihm ihm' =>
    constructor
    intro y st
    cases st with
    | rfl_M stM =>
      exact ihm' stM

lemma sn_exf {A m : Tm} :
    SN Step A -> SN Step m -> SN Step (.exf A m) := by
  intro snA
  induction snA generalizing m
  case intro A ihA ihA' =>
    intro snm
    induction snm
    case intro m ihm ihm' =>
      constructor
      intro y st
      cases st with
      | exf_A m stA =>
        exact ihA' stA (SN.intro ihm)
      | exf_M A stM =>
        exact ihm' stM

lemma sn_app {m n : Tm} :
    SN Step m ->
    SN Step n ->
    (∀ A body n', n ~>* n' -> m ~>* .lam A body -> SN Step body.[n'/]) ->
    SN Step (.app m n) := by
  intro snm
  induction snm generalizing n
  case intro m ihm ihm' =>
    intro snn hβ
    induction snn
    case intro n ihn ihn' =>
      constructor
      intro y st
      cases st with
      | app_M n stM =>
        apply ihm' stM (SN.intro ihn)
        intro A body n' rdN rdM
        apply hβ A body n'
        . assumption
        . apply Star.ES stM rdM
      | app_N m stN =>
        apply ihn' stN
        intro A body n'' rdN rdM
        apply hβ A body n''
        . apply Star.ES stN rdN
        . assumption
      | beta A body n =>
        apply hβ A body n
        . apply Star.R
        . apply Star.R

lemma sn_app_neutral {m n : Tm} :
    Neutral m -> SN Step m -> SN Step n -> SN Step (.app m n) := by
  intro neu snm snn
  apply sn_app snm snn
  intro A body n' rdN rdM
  exact (neu.not_red_lam rdM).elim

lemma sn_prj {A m n : Tm} :
    SN Step A ->
    SN Step m ->
    SN Step n ->
    (∀ m1 m2 n', m ~>* .tup m1 m2 -> n ~>* n' -> SN Step n'.[m2,m1/]) ->
    SN Step (.prj A m n) := by
  intro snA
  induction snA generalizing m n
  case intro A ihA ihA' =>
    intro snm
    induction snm generalizing n
    case intro m ihm ihm' =>
      intro snn hβ
      induction snn
      case intro n ihn ihn' =>
        constructor
        intro y st
        cases st with
        | prj_A m n stA =>
          apply ihA' stA (SN.intro ihm) (SN.intro ihn)
          intro m1 m2 n' rdM rdN
          exact hβ m1 m2 n' rdM rdN
        | prj_M A n stM =>
          apply ihm' stM (SN.intro ihn)
          intro m1 m2 n' rdM rdN
          apply hβ m1 m2 n'
          . apply Star.ES stM rdM
          . assumption
        | prj_N A m stN =>
          apply ihn' stN
          intro m1 m2 n'' rdM rdN
          apply hβ m1 m2 n''
          . assumption
          . apply Star.ES stN rdN
        | prj_elim A m1 m2 n =>
          apply hβ m1 m2 n
          . apply Star.R
          . apply Star.R

lemma sn_prj_neutral {A m n : Tm} :
    Neutral m -> SN Step A -> SN Step m -> SN Step n -> SN Step (.prj A m n) := by
  intro neu snA snm snn
  apply sn_prj snA snm snn
  intro m1 m2 n' rdM rdN
  exact (neu.not_red_tup rdM).elim

lemma sn_ite {A m n1 n2 : Tm} :
    SN Step A ->
    SN Step m ->
    SN Step n1 ->
    SN Step n2 ->
    SN Step (.ite A m n1 n2) := by
  intro snA
  induction snA generalizing m n1 n2
  case intro A ihA ihA' =>
    intro snm
    induction snm generalizing n1 n2
    case intro m ihm ihm' =>
      intro sn1
      induction sn1 generalizing n2
      case intro n1 ih1 ih1' =>
        intro sn2
        induction sn2
        case intro n2 ih2 ih2' =>
          constructor
          intro y st
          cases st with
          | ite_A m n1 n2 stA =>
            exact ihA' stA (SN.intro ihm) (SN.intro ih1) (SN.intro ih2)
          | ite_M A n1 n2 stM =>
            exact ihm' stM (SN.intro ih1) (SN.intro ih2)
          | ite_N1 A m n2 st1 =>
            exact ih1' st1 (SN.intro ih2)
          | ite_N2 A m n1 st2 =>
            exact ih2' st2
          | ite_tt A n1 n2 =>
            exact SN.intro ih1
          | ite_ff A n1 n2 =>
            exact SN.intro ih2

lemma sn_rw {A m n : Tm} :
    SN Step A ->
    SN Step m ->
    SN Step n ->
    SN Step (.rw A m n) := by
  intro snA
  induction snA generalizing m n
  case intro A ihA ihA' =>
    intro snm
    induction snm generalizing n
    case intro m ihm ihm' =>
      intro snn
      induction snn
      case intro n ihn ihn' =>
        constructor
        intro y st
        cases st with
        | rw_A m n stA =>
          exact ihA' stA (SN.intro ihm) (SN.intro ihn)
        | rw_M A n stM =>
          exact ihm' stM (SN.intro ihn)
        | rw_N A m stN =>
          exact ihn' stN
        | rw_elim A m n =>
          exact SN.intro ihm

structure Candidate where
  mem : Tm -> Prop
  sn : ∀ {m}, mem m -> SN Step m
  closed_step : ∀ {m n}, mem m -> m ~> n -> mem n
  neutral : ∀ {m}, Neutral m -> SN Step m -> (∀ {n}, m ~> n -> mem n) -> mem m

namespace Candidate

def Expansive (C : Candidate) : Prop :=
  ∀ {m}, SN Step m -> (∀ {n}, m ~> n -> C.mem n) -> C.mem m

def Weakens (C : Candidate) : Prop :=
  ∀ {m}, C.mem m -> C.mem m.[shift 1]

lemma closed_red (C : Candidate) {m n : Tm} :
    C.mem m -> m ~>* n -> C.mem n := by
  intro hm rd
  induction rd
  case R => assumption
  case SE rd st ih => exact C.closed_step ih st

def snCandidate : Candidate where
  mem m := SN Step m
  sn hm := hm
  closed_step hm st := sn_step hm st
  neutral _ hsn _ := hsn

lemma snCandidate_expansive : Expansive Candidate.snCandidate := by
  intro m hsn _
  exact hsn

lemma snCandidate_weakens : Weakens Candidate.snCandidate := by
  intro m hm
  exact sn_shift hm

lemma weakens_iter {C : Candidate} (hC : C.Weakens) {m : Tm} :
    C.mem m -> ∀ i, C.mem m.[shift i] := by
  intro hm i
  induction i with
  | zero =>
    simpa [SubstLemmas.shift0, Tm.subst_id] using hm
  | succ i ih =>
    have h := hC ih
    simpa [subst_shift_shift] using h

lemma expansive_of_steps {C : Candidate} (hC : Expansive C) {m : Tm} :
    (∀ {n}, m ~> n -> C.mem n) -> C.mem m := by
  intro hred
  apply hC
  . constructor
    intro n st
    exact C.sn (hred st)
  . intro n st
    exact hred st

lemma expansive_red_backward {C : Candidate} (hC : Expansive C) {m n : Tm} :
    SN Step m -> m ~>* n -> C.mem n -> C.mem m := by
  intro hsn rd hn
  induction hsn generalizing n with
  | intro hstep ih =>
    apply hC (SN.intro hstep)
    intro y st
    have ⟨z, ryz, rnz⟩ := Step.confluent (Star.one st) rd
    have hz : C.mem z := C.closed_red hn rnz
    exact ih st ryz hz

lemma conv_of_expansive {C : Candidate} (hC : Expansive C) {m n : Tm} :
    SN Step m -> m === n -> C.mem n -> C.mem m := by
  intro hsn eq hn
  have ⟨z, rmz, rnz⟩ := Step.cr eq
  exact expansive_red_backward hC hsn rmz (C.closed_red hn rnz)

lemma var (C : Candidate) x : C.mem (.var x) := by
  apply C.neutral
  . exact Neutral.var x
  . exact sn_var
  . intro n st
    cases st

lemma neutral_app (C : Candidate) {m n : Tm} :
    Neutral m ->
    SN Step m ->
    SN Step n ->
    (∀ {x}, .app m n ~> x -> C.mem x) ->
    C.mem (.app m n) := by
  intro neu snm snn h
  apply C.neutral
  . exact Neutral.app m n neu
  . exact sn_app_neutral neu snm snn
  . intro x st
    exact h st

lemma neutral_prj (C : Candidate) {A m n : Tm} :
    Neutral m ->
    SN Step A ->
    SN Step m ->
    SN Step n ->
    (∀ {x}, .prj A m n ~> x -> C.mem x) ->
    C.mem (.prj A m n) := by
  intro neu snA snm snn h
  apply C.neutral
  . exact Neutral.prj A m n neu
  . exact sn_prj_neutral neu snA snm snn
  . intro x st
    exact h st

lemma neutral_ite (C : Candidate) {A m n1 n2 : Tm} :
    Neutral m ->
    SN Step A ->
    SN Step m ->
    SN Step n1 ->
    SN Step n2 ->
    (∀ {x}, .ite A m n1 n2 ~> x -> C.mem x) ->
    C.mem (.ite A m n1 n2) := by
  intro neu snA snm sn1 sn2 h
  apply C.neutral
  . exact Neutral.ite A m n1 n2 neu
  . exact sn_ite snA snm sn1 sn2
  . intro x st
    exact h st

lemma neutral_rw (C : Candidate) {A m n : Tm} :
    Neutral n ->
    SN Step A ->
    SN Step m ->
    SN Step n ->
    (∀ {x}, .rw A m n ~> x -> C.mem x) ->
    C.mem (.rw A m n) := by
  intro neu snA snm snn h
  apply C.neutral
  . exact Neutral.rw A m n neu
  . exact sn_rw snA snm snn
  . intro x st
    exact h st

lemma neutral_exf (C : Candidate) {A m : Tm} :
    Neutral m ->
    SN Step A ->
    SN Step m ->
    (∀ {x}, .exf A m ~> x -> C.mem x) ->
    C.mem (.exf A m) := by
  intro neu snA snm h
  apply C.neutral
  . exact Neutral.exf A m neu
  . exact sn_exf snA snm
  . intro x st
    exact h st

end Candidate

def Candidate.arrow (A B : Candidate) : Candidate where
  mem m := SN Step m ∧ ∀ n, A.mem n -> B.mem (.app m n)
  sn hm := hm.1
  closed_step hm st := by
    constructor
    . exact sn_step hm.1 st
    . intro n hn
      exact B.closed_step (hm.2 n hn) (Step.app_M n st)
  neutral neu hsn hred := by
    constructor
    . exact hsn
    . intro n hn
      have snn := A.sn hn
      revert hn
      induction snn
      case intro n ihN ihN' =>
        intro hn
        apply B.neutral
        . exact Neutral.app _ _ neu
        . exact sn_app_neutral neu hsn (SN.intro ihN)
        . intro x st
          cases st with
          | app_M n stM =>
            exact (hred stM).2 n hn
          | app_N m stN =>
            exact ihN' stN (A.closed_step hn stN)
          | beta A body n =>
            exact (Neutral.not_lam neu).elim

lemma Candidate.arrow_intro {A B : Candidate} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    (∀ n, A.mem n -> B.mem (.app (.lam T m) n)) ->
    (Candidate.arrow A B).mem (.lam T m) := by
  intro snT snm happ
  constructor
  . exact sn_lam snT snm
  . exact happ

lemma Candidate.arrow_lam {A B : Candidate} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    Candidate.Expansive B ->
    (∀ n, A.mem n -> ∀ {x}, .app (.lam T m) n ~> x -> B.mem x) ->
    (Candidate.arrow A B).mem (.lam T m) := by
  intro snT snm hB hstep
  apply Candidate.arrow_intro snT snm
  intro n hn
  exact Candidate.expansive_of_steps hB (hstep n hn)

lemma Candidate.arrow_lam_step {A B : Candidate} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    Candidate.Expansive B ->
    (∀ T', T ~> T' -> (Candidate.arrow A B).mem (.lam T' m)) ->
    (∀ m', m ~> m' -> (Candidate.arrow A B).mem (.lam T m')) ->
    (∀ n, A.mem n -> B.mem m.[n/]) ->
    (Candidate.arrow A B).mem (.lam T m) := by
  intro snT snm hB hT hm hβ
  apply Candidate.arrow_intro snT snm
  intro n hn
  have snn := A.sn hn
  revert hn
  induction snn
  case intro n ihN ihN' =>
    intro hn
    apply Candidate.expansive_of_steps hB
    intro x st
    cases st with
    | app_M n stM =>
      cases stM with
      | lam_A m stT =>
        exact (hT _ stT).2 n hn
      | lam_M T stM =>
        exact (hm _ stM).2 n hn
    | app_N m stN =>
      exact ihN' stN (A.closed_step hn stN)
    | beta T m n =>
      exact hβ n hn

lemma Candidate.arrow_lam_body {A B : Candidate} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    Candidate.Expansive B ->
    (∀ n, A.mem n -> B.mem m.[n/]) ->
    (Candidate.arrow A B).mem (.lam T m) := by
  intro snT
  induction snT generalizing m
  case intro T ihT ihT' =>
    intro snm
    induction snm
    case intro m ihM ihM' =>
      intro hB hβ
      apply Candidate.arrow_lam_step (SN.intro ihT) (SN.intro ihM) hB
      . intro T' stT
        exact ihT' stT (SN.intro ihM) hB hβ
      . intro m' stM
        apply ihM' stM hB
        intro n hn
        exact B.closed_step (hβ n hn) (Step.subst (n .: ids) stM)
      . exact hβ

lemma Candidate.arrow_app {A B : Candidate} {m n : Tm} :
    (Candidate.arrow A B).mem m ->
    A.mem n ->
    B.mem (.app m n) := by
  intro hm hn
  exact hm.2 n hn

lemma Candidate.arrow_app_sn {A B : Candidate} {m n : Tm} :
    (Candidate.arrow A B).mem m ->
    A.mem n ->
    SN Step (.app m n) := by
  intro hm hn
  exact B.sn (Candidate.arrow_app hm hn)

structure CandidateFamily (A : Candidate) where
  fiber : Tm -> Candidate
  stable_step :
    ∀ {a a' m}, A.mem a -> a ~> a' -> (fiber a').mem m -> (fiber a).mem m
  stable_step_fwd :
    ∀ {a a' m}, A.mem a -> a ~> a' -> (fiber a).mem m -> (fiber a').mem m

namespace CandidateFamily

def Expansive {A : Candidate} (B : CandidateFamily A) : Prop :=
  ∀ {a}, A.mem a -> Candidate.Expansive (B.fiber a)

lemma stable_red {A : Candidate} (B : CandidateFamily A) {a a' m : Tm} :
    A.mem a -> a ~>* a' -> (B.fiber a').mem m -> (B.fiber a).mem m := by
  intro ha rd hm
  induction rd
  case R => assumption
  case SE rd st ih =>
    apply ih
    exact B.stable_step (A.closed_red ha rd) st hm

lemma stable_red_fwd {A : Candidate} (B : CandidateFamily A) {a a' m : Tm} :
    A.mem a -> a ~>* a' -> (B.fiber a).mem m -> (B.fiber a').mem m := by
  intro ha rd hm
  induction rd
  case R => assumption
  case SE rd st ih =>
    exact B.stable_step_fwd (A.closed_red ha rd) st ih

lemma stable_conv {A : Candidate} (B : CandidateFamily A) {a a' m : Tm} :
    A.mem a -> A.mem a' -> a === a' ->
    (B.fiber a).mem m -> (B.fiber a').mem m := by
  intro ha ha' eq hm
  have ⟨z, raz, ra'z⟩ := Step.cr eq
  have hz : (B.fiber z).mem m := B.stable_red_fwd ha raz hm
  exact B.stable_red ha' ra'z hz

lemma stable_conv_sym {A : Candidate} (B : CandidateFamily A) {a a' m : Tm} :
    A.mem a -> A.mem a' -> a === a' ->
    (B.fiber a').mem m -> (B.fiber a).mem m := by
  intro ha ha' eq hm
  exact B.stable_conv ha' ha eq.sym hm

def const (A B : Candidate) : CandidateFamily A where
  fiber _ := B
  stable_step _ _ hm := hm
  stable_step_fwd _ _ hm := hm

lemma const_expansive {A B : Candidate} :
    Candidate.Expansive B -> (CandidateFamily.const A B).Expansive := by
  intro hB _a _ha
  exact hB

end CandidateFamily

def Candidate.pi (A : Candidate) (B : CandidateFamily A) : Candidate where
  mem m := SN Step m ∧ ∀ n, A.mem n -> (B.fiber n).mem (.app m n)
  sn hm := hm.1
  closed_step hm st := by
    constructor
    . exact sn_step hm.1 st
    . intro n hn
      exact (B.fiber n).closed_step (hm.2 n hn) (Step.app_M n st)
  neutral neu hsn hred := by
    constructor
    . exact hsn
    . intro n hn
      have snn := A.sn hn
      revert hn
      induction snn
      case intro n ihN ihN' =>
        intro hn
        apply (B.fiber n).neutral
        . exact Neutral.app _ _ neu
        . exact sn_app_neutral neu hsn (SN.intro ihN)
        . intro x st
          cases st with
          | app_M n stM =>
            exact (hred stM).2 n hn
          | app_N m stN =>
            exact B.stable_step hn stN (ihN' stN (A.closed_step hn stN))
          | beta A body n =>
            exact (Neutral.not_lam neu).elim

lemma Candidate.pi_intro {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    (∀ n, A.mem n -> (B.fiber n).mem (.app (.lam T m) n)) ->
    (Candidate.pi A B).mem (.lam T m) := by
  intro snT snm happ
  constructor
  . exact sn_lam snT snm
  . exact happ

lemma Candidate.pi_lam {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    B.Expansive ->
    (∀ n, (hn : A.mem n) -> ∀ {x}, .app (.lam T m) n ~> x -> (B.fiber n).mem x) ->
    (Candidate.pi A B).mem (.lam T m) := by
  intro snT snm hB hstep
  apply Candidate.pi_intro snT snm
  intro n hn
  exact Candidate.expansive_of_steps (hB hn) (hstep n hn)

lemma Candidate.pi_lam_step {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    B.Expansive ->
    (∀ T', T ~> T' -> (Candidate.pi A B).mem (.lam T' m)) ->
    (∀ m', m ~> m' -> (Candidate.pi A B).mem (.lam T m')) ->
    (∀ n, (hn : A.mem n) -> (B.fiber n).mem m.[n/]) ->
    (Candidate.pi A B).mem (.lam T m) := by
  intro snT snm hB hT hm hβ
  apply Candidate.pi_intro snT snm
  intro n hn
  have snn := A.sn hn
  revert hn
  induction snn
  case intro n ihN ihN' =>
    intro hn
    apply Candidate.expansive_of_steps (hB hn)
    intro x st
    cases st with
    | app_M n stM =>
      cases stM with
      | lam_A m stT =>
        exact (hT _ stT).2 n hn
      | lam_M T stM =>
        exact (hm _ stM).2 n hn
    | app_N m stN =>
      exact B.stable_step hn stN (ihN' stN (A.closed_step hn stN))
    | beta T m n =>
      exact hβ n hn

lemma Candidate.pi_lam_body {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    SN Step T ->
    SN Step m ->
    B.Expansive ->
    (∀ n, (hn : A.mem n) -> (B.fiber n).mem m.[n/]) ->
    (Candidate.pi A B).mem (.lam T m) := by
  intro snT
  induction snT generalizing m
  case intro T ihT ihT' =>
    intro snm
    induction snm
    case intro m ihM ihM' =>
      intro hB hβ
      apply Candidate.pi_lam_step (SN.intro ihT) (SN.intro ihM) hB
      . intro T' stT
        exact ihT' stT (SN.intro ihM) hB hβ
      . intro m' stM
        apply ihM' stM hB
        intro n hn
        exact (B.fiber n).closed_step (hβ n hn) (Step.subst (n .: ids) stM)
      . exact hβ

lemma Candidate.pi_app {A : Candidate} {B : CandidateFamily A} {m n : Tm} :
    (Candidate.pi A B).mem m ->
    A.mem n ->
    (B.fiber n).mem (.app m n) := by
  intro hm hn
  exact hm.2 n hn

lemma Candidate.pi_app_sn {A : Candidate} {B : CandidateFamily A} {m n : Tm} :
    (Candidate.pi A B).mem m ->
    A.mem n ->
    SN Step (.app m n) := by
  intro hm hn
  exact (B.fiber n).sn (Candidate.pi_app hm hn)

lemma Candidate.arrow_beta_sn {A B : Candidate} {m n n' T body : Tm} :
    (Candidate.arrow A B).mem m ->
    A.mem n ->
    n ~>* n' ->
    m ~>* .lam T body ->
    SN Step body.[n'/] := by
  intro hm hn rdN rdM
  have hApp := hm.2 n hn
  have rdApp : .app m n ~>* body.[n'/] := by
    apply Star.SE
    . apply Red.app <;> assumption
    . apply Step.beta
  exact B.sn (B.closed_red hApp rdApp)

lemma Candidate.pi_beta_sn {A : Candidate} {B : CandidateFamily A} {m n n' T body : Tm} :
    (Candidate.pi A B).mem m ->
    A.mem n ->
    n ~>* n' ->
    m ~>* .lam T body ->
    SN Step body.[n'/] := by
  intro hm hn rdN rdM
  have hApp := hm.2 n hn
  have rdApp : .app m n ~>* body.[n'/] := by
    apply Star.SE
    . apply Red.app <;> assumption
    . apply Step.beta
  exact (B.fiber n).sn ((B.fiber n).closed_red hApp rdApp)

def Candidate.sigma (A : Candidate) (B : CandidateFamily A) : Candidate where
  mem p := SN Step p ∧ ∀ a b, p ~>* .tup a b -> A.mem a ∧ (B.fiber a).mem b
  sn hp := hp.1
  closed_step hp st := by
    constructor
    . exact sn_step hp.1 st
    . intro a b rd
      exact hp.2 a b (Star.ES st rd)
  neutral neu hsn hred := by
    constructor
    . exact hsn
    . intro a b rd
      cases rd.ES_split with
      | inl e =>
        subst_vars
        exact (Neutral.not_tup neu).elim
      | inr h =>
        rcases h with ⟨p', st, rd'⟩
        exact (hred st).2 a b rd'

lemma Candidate.sigma_pair {A : Candidate} {B : CandidateFamily A} {a b : Tm} :
    A.mem a -> (B.fiber a).mem b -> (Candidate.sigma A B).mem (.tup a b) := by
  intro ha hb
  constructor
  . exact sn_tup (A.sn ha) ((B.fiber a).sn hb)
  . intro a' b' rd
    have ⟨a0, b0, rdA, rdB, e⟩ := Red.tup_inv rd
    cases e
    have ha' := A.closed_red ha rdA
    have hb' := (B.fiber a).closed_red hb rdB
    exact ⟨ha', B.stable_red_fwd ha rdA hb'⟩

lemma Candidate.sigma_components {A : Candidate} {B : CandidateFamily A} {p a b : Tm} :
    (Candidate.sigma A B).mem p ->
    p ~>* .tup a b ->
    A.mem a ∧ (B.fiber a).mem b := by
  intro hp rd
  exact hp.2 a b rd

lemma Candidate.sigma_prj_sn {A : Candidate} {B : CandidateFamily A}
    {C p n : Tm} :
    SN Step C ->
    (Candidate.sigma A B).mem p ->
    SN Step n ->
    (∀ a b n',
      A.mem a ->
      (B.fiber a).mem b ->
      p ~>* .tup a b ->
      n ~>* n' ->
      SN Step n'.[b,a/]) ->
    SN Step (.prj C p n) := by
  intro snC hp snn hβ
  apply sn_prj snC ((Candidate.sigma A B).sn hp) snn
  intro a b n' rdP rdN
  have ⟨ha, hb⟩ := Candidate.sigma_components hp rdP
  exact hβ a b n' ha hb rdP rdN

lemma Candidate.sigma_prj {A : Candidate} {B : CandidateFamily A}
    {D : Candidate} {C p n : Tm} :
    Candidate.Expansive D ->
    (Candidate.sigma A B).mem p ->
    (∀ C', C ~> C' -> D.mem (.prj C' p n)) ->
    (∀ p', p ~> p' -> D.mem (.prj C p' n)) ->
    (∀ n', n ~> n' -> D.mem (.prj C p n')) ->
    (∀ a b, A.mem a -> (B.fiber a).mem b -> D.mem n.[b,a/]) ->
    D.mem (.prj C p n) := by
  intro hD hp hC hpStep hn hβ
  apply Candidate.expansive_of_steps hD
  intro x st
  cases st with
  | prj_A p n stC =>
    exact hC _ stC
  | prj_M C n stP =>
    exact hpStep _ stP
  | prj_N C p stN =>
    exact hn _ stN
  | prj_elim C a b n =>
    have ⟨ha, hb⟩ := Candidate.sigma_components hp Star.R
    exact hβ a b ha hb

lemma Candidate.sigma_prj_dep {A : Candidate} {B : CandidateFamily A}
    {D : CandidateFamily (Candidate.sigma A B)} {C p n : Tm} :
    D.Expansive ->
    (hp : (Candidate.sigma A B).mem p) ->
    (∀ C', C ~> C' -> (D.fiber p).mem (.prj C' p n)) ->
    (∀ p', p ~> p' -> (D.fiber p').mem (.prj C p' n)) ->
    (∀ n', n ~> n' -> (D.fiber p).mem (.prj C p n')) ->
    (∀ a b, A.mem a -> (B.fiber a).mem b -> (D.fiber (.tup a b)).mem n.[b,a/]) ->
    (D.fiber p).mem (.prj C p n) := by
  intro hD hp hC hpStep hn hβ
  apply Candidate.expansive_of_steps (hD hp)
  intro x st
  cases st with
  | prj_A p n stC =>
    exact hC _ stC
  | prj_M C n stP =>
    exact D.stable_step hp stP (hpStep _ stP)
  | prj_N C p stN =>
    exact hn _ stN
  | prj_elim C a b n =>
    have ⟨ha, hb⟩ := Candidate.sigma_components hp Star.R
    exact hβ a b ha hb

def Candidate.bool : Candidate := Candidate.snCandidate

def Candidate.bot : Candidate := Candidate.snCandidate

def Candidate.idn (_ : Candidate) (_ _ : Tm) : Candidate := Candidate.snCandidate

structure TypeCodeInterp (i : Nat) (A : Tm) where
  cand : Candidate
  type_sn : SN Step A

namespace TypeCodeInterp

def ofSN (i : Nat) (A : Tm) (hsn : SN Step A) : TypeCodeInterp i A where
  cand := Candidate.snCandidate
  type_sn := hsn

def weaken {i : Nat} {A : Tm} (I : TypeCodeInterp i A) :
    TypeCodeInterp i A.[shift 1] where
  cand := I.cand
  type_sn := sn_shift I.type_sn

def weakenN {i : Nat} {A : Tm} (I : TypeCodeInterp i A) (k : Nat) :
    TypeCodeInterp i A.[shift k] where
  cand := I.cand
  type_sn := sn_shiftn k I.type_sn

end TypeCodeInterp

def Candidate.univ (i : Nat) : Candidate where
  mem A := ∃ I : TypeCodeInterp i A, True
  sn h := by
    rcases h with ⟨I, _⟩
    exact I.type_sn
  closed_step h st := by
    rcases h with ⟨I, _⟩
    exact ⟨{ cand := I.cand
             type_sn := sn_step I.type_sn st }, trivial⟩
  neutral _ hsn _ := by
    exact ⟨TypeCodeInterp.ofSN i _ hsn, trivial⟩

lemma Candidate.bool_expansive : Candidate.Expansive Candidate.bool :=
  Candidate.snCandidate_expansive

lemma Candidate.bot_expansive : Candidate.Expansive Candidate.bot :=
  Candidate.snCandidate_expansive

lemma Candidate.idn_expansive {A : Candidate} {a b : Tm} :
    Candidate.Expansive (Candidate.idn A a b) :=
  Candidate.snCandidate_expansive

lemma Candidate.bool_weakens : Candidate.Weakens Candidate.bool :=
  Candidate.snCandidate_weakens

lemma Candidate.bot_weakens : Candidate.Weakens Candidate.bot :=
  Candidate.snCandidate_weakens

lemma Candidate.idn_weakens {A : Candidate} {a b : Tm} :
    Candidate.Weakens (Candidate.idn A a b) :=
  Candidate.snCandidate_weakens

lemma Candidate.univ_expansive {i : Nat} :
    Candidate.Expansive (Candidate.univ i) := by
  intro m hsn _
  exact ⟨TypeCodeInterp.ofSN i m hsn, trivial⟩

lemma Candidate.univ_weakens {i : Nat} :
    Candidate.Weakens (Candidate.univ i) := by
  intro A hA
  rcases hA with ⟨I, _⟩
  exact ⟨I.weaken, trivial⟩

noncomputable def Candidate.univ_witness {i : Nat} {A : Tm} :
    (Candidate.univ i).mem A -> TypeCodeInterp i A := by
  intro h
  exact h.choose

namespace TypeCodeInterp

def ty (i j : Nat) : TypeCodeInterp j (.ty i) where
  cand := Candidate.univ i
  type_sn := sn_ty

def bool (i : Nat) : TypeCodeInterp i .bool where
  cand := Candidate.bool
  type_sn := sn_bool

def bot (i : Nat) : TypeCodeInterp i .bot where
  cand := Candidate.bot
  type_sn := sn_bot

def piSN (i : Nat) (A B : Tm) :
    SN Step A -> SN Step B -> TypeCodeInterp i (.pi A B) := by
  intro snA snB
  exact TypeCodeInterp.ofSN i (.pi A B) (sn_pi snA snB)

def sigSN (i : Nat) (A B : Tm) :
    SN Step A -> SN Step B -> TypeCodeInterp i (.sig A B) := by
  intro snA snB
  exact TypeCodeInterp.ofSN i (.sig A B) (sn_sig snA snB)

def pi (i : Nat) (A B : Tm) (C : Candidate) (D : CandidateFamily C) :
    SN Step A -> SN Step B -> TypeCodeInterp i (.pi A B) := by
  intro snA snB
  exact
    { cand := Candidate.pi C D
      type_sn := sn_pi snA snB }

def sig (i : Nat) (A B : Tm) (C : Candidate) (D : CandidateFamily C) :
    SN Step A -> SN Step B -> TypeCodeInterp i (.sig A B) := by
  intro snA snB
  exact
    { cand := Candidate.sigma C D
      type_sn := sn_sig snA snB }

def idn (i : Nat) (C : Candidate) (A a b : Tm) :
    SN Step A -> SN Step a -> SN Step b -> TypeCodeInterp i (.idn A a b) := by
  intro snA sna snb
  exact
    { cand := Candidate.idn C a b
      type_sn := sn_idn snA sna snb }

lemma mem_univ {i : Nat} {A : Tm} (I : TypeCodeInterp i A) :
    (Candidate.univ i).mem A := by
  exact ⟨I, trivial⟩

end TypeCodeInterp

lemma Candidate.univ_type_sn {i : Nat} {A : Tm} :
    (Candidate.univ i).mem A -> SN Step A := by
  intro h
  exact (Candidate.univ_witness h).type_sn

namespace CandidateFamily

def boolCases (T F : Candidate) : CandidateFamily Candidate.bool where
  fiber b :=
    { mem m := SN Step m ∧ (b === .tt -> T.mem m) ∧ (b === .ff -> F.mem m)
      sn hm := hm.1
      closed_step hm st := by
        constructor
        . exact sn_step hm.1 st
        . constructor
          . intro eq
            exact T.closed_step (hm.2.1 eq) st
          . intro eq
            exact F.closed_step (hm.2.2 eq) st
      neutral neu hsn hred := by
        constructor
        . exact hsn
        . constructor
          . intro eq
            apply T.neutral neu hsn
            intro n st
            exact (hred st).2.1 eq
          . intro eq
            apply F.neutral neu hsn
            intro n st
            exact (hred st).2.2 eq }
  stable_step _ st hm := by
    constructor
    . exact hm.1
    . constructor
      . intro eq
        exact hm.2.1 (Conv.ESi st eq)
      . intro eq
        exact hm.2.2 (Conv.ESi st eq)
  stable_step_fwd _ st hm := by
    constructor
    . exact hm.1
    . constructor
      . intro eq
        exact hm.2.1 (Conv.ES st eq)
      . intro eq
        exact hm.2.2 (Conv.ES st eq)

lemma boolCases_expansive {T F : Candidate} :
    Candidate.Expansive T ->
    Candidate.Expansive F ->
    (CandidateFamily.boolCases T F).Expansive := by
  intro hT hF b hb m hsn hred
  constructor
  . exact hsn
  . constructor
    . intro eq
      apply Candidate.expansive_of_steps hT
      intro n st
      exact (hred st).2.1 eq
    . intro eq
      apply Candidate.expansive_of_steps hF
      intro n st
      exact (hred st).2.2 eq

end CandidateFamily

lemma CandidateFamily.boolCases_tt {T F : Candidate} {m : Tm} :
    T.mem m -> ((CandidateFamily.boolCases T F).fiber .tt).mem m := by
  intro hm
  constructor
  . exact T.sn hm
  . constructor
    . intro _eq
      exact hm
    . intro eq
      exact (Conv.not_tt_ff eq).elim

lemma CandidateFamily.boolCases_ff {T F : Candidate} {m : Tm} :
    F.mem m -> ((CandidateFamily.boolCases T F).fiber .ff).mem m := by
  intro hm
  constructor
  . exact F.sn hm
  . constructor
    . intro eq
      exact (Conv.not_ff_tt eq).elim
    . intro _eq
      exact hm

lemma CandidateFamily.boolCases_tt_inv {T F : Candidate} {m : Tm} :
    ((CandidateFamily.boolCases T F).fiber .tt).mem m -> T.mem m := by
  intro hm
  exact hm.2.1 Conv.R

lemma CandidateFamily.boolCases_ff_inv {T F : Candidate} {m : Tm} :
    ((CandidateFamily.boolCases T F).fiber .ff).mem m -> F.mem m := by
  intro hm
  exact hm.2.2 Conv.R

lemma CandidateFamily.boolCases_conv {T F : Candidate} {b b' m : Tm} :
    b === b' ->
    ((CandidateFamily.boolCases T F).fiber b).mem m ->
    ((CandidateFamily.boolCases T F).fiber b').mem m := by
  intro eq hm
  constructor
  . exact hm.1
  . constructor
    . intro eq'
      exact hm.2.1 (Conv.trans eq eq')
    . intro eq'
      exact hm.2.2 (Conv.trans eq eq')

lemma CandidateFamily.boolCases_conv_sym {T F : Candidate} {b b' m : Tm} :
    b === b' ->
    ((CandidateFamily.boolCases T F).fiber b').mem m ->
    ((CandidateFamily.boolCases T F).fiber b).mem m := by
  intro eq hm
  exact CandidateFamily.boolCases_conv eq.sym hm

def CandidateFamily.idCases
    (I : Candidate) (a b : Tm) (R : Tm -> Candidate) :
    CandidateFamily (Candidate.idn I a b) where
  fiber p :=
    { mem m := SN Step m ∧ ∀ c, p === .rfl c -> (R c).mem m
      sn hm := hm.1
      closed_step hm st := by
        constructor
        . exact sn_step hm.1 st
        . intro c eq
          exact (R c).closed_step (hm.2 c eq) st
      neutral neu hsn hred := by
        constructor
        . exact hsn
        . intro c eq
          apply (R c).neutral neu hsn
          intro n st
          exact (hred st).2 c eq }
  stable_step _ st hm := by
    constructor
    . exact hm.1
    . intro c eq
      exact hm.2 c (Conv.ESi st eq)
  stable_step_fwd _ st hm := by
    constructor
    . exact hm.1
    . intro c eq
      exact hm.2 c (Conv.ES st eq)

lemma CandidateFamily.idCases_expansive {I : Candidate} {a b : Tm} {R : Tm -> Candidate} :
    (∀ c, Candidate.Expansive (R c)) ->
    (CandidateFamily.idCases I a b R).Expansive := by
  intro hR p hp m hsn hred
  constructor
  . exact hsn
  . intro c eq
    apply Candidate.expansive_of_steps (hR c)
    intro n st
    exact (hred st).2 c eq

lemma CandidateFamily.idCases_conv {I : Candidate} {a b p p' m : Tm} {R : Tm -> Candidate} :
    p === p' ->
    ((CandidateFamily.idCases I a b R).fiber p).mem m ->
    ((CandidateFamily.idCases I a b R).fiber p').mem m := by
  intro eq hm
  constructor
  . exact hm.1
  . intro c eq'
    exact hm.2 c (Conv.trans eq eq')

lemma CandidateFamily.idCases_conv_sym {I : Candidate} {a b p p' m : Tm} {R : Tm -> Candidate} :
    p === p' ->
    ((CandidateFamily.idCases I a b R).fiber p').mem m ->
    ((CandidateFamily.idCases I a b R).fiber p).mem m := by
  intro eq hm
  exact CandidateFamily.idCases_conv eq.sym hm

lemma CandidateFamily.idCases_rfl_all {I : Candidate} {a b c m : Tm}
    {R : Tm -> Candidate} :
    (∀ d, (R d).mem m) ->
    ((CandidateFamily.idCases I a b R).fiber (.rfl c)).mem m := by
  intro h
  constructor
  . exact (R c).sn (h c)
  . intro d _eq
    exact h d

lemma CandidateFamily.idCases_rfl_inv {I : Candidate} {a b c m : Tm}
    {R : Tm -> Candidate} :
    ((CandidateFamily.idCases I a b R).fiber (.rfl c)).mem m ->
    (R c).mem m := by
  intro hm
  exact hm.2 c Conv.R

lemma Candidate.univ_intro {i : Nat} {m : Tm} :
    SN Step m -> (Candidate.univ i).mem m := by
  intro snm
  exact ⟨TypeCodeInterp.ofSN i m snm, trivial⟩

lemma Candidate.ty {i j : Nat} :
    (Candidate.univ j).mem (.ty i) := by
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.ty i j)

lemma Candidate.pi_type {i : Nat} {A B : Tm} :
    SN Step A ->
    SN Step B ->
    (Candidate.univ i).mem (.pi A B) := by
  intro snA snB
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.piSN i A B snA snB)

lemma Candidate.pi_type_code {i : Nat} {A B : Tm} {C : Candidate}
    {D : CandidateFamily C} :
    SN Step A ->
    SN Step B ->
    (Candidate.univ i).mem (.pi A B) := by
  intro snA snB
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.pi i A B C D snA snB)

lemma Candidate.sig_type {i : Nat} {A B : Tm} :
    SN Step A ->
    SN Step B ->
    (Candidate.univ i).mem (.sig A B) := by
  intro snA snB
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.sigSN i A B snA snB)

lemma Candidate.sig_type_code {i : Nat} {A B : Tm} {C : Candidate}
    {D : CandidateFamily C} :
    SN Step A ->
    SN Step B ->
    (Candidate.univ i).mem (.sig A B) := by
  intro snA snB
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.sig i A B C D snA snB)

lemma Candidate.bool_type {i : Nat} :
    (Candidate.univ i).mem .bool := by
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.bool i)

lemma Candidate.bot_type {i : Nat} :
    (Candidate.univ i).mem .bot := by
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.bot i)

lemma Candidate.idn_type {i : Nat} {A m n : Tm} :
    SN Step A ->
    SN Step m ->
    SN Step n ->
    (Candidate.univ i).mem (.idn A m n) := by
  intro snA snm snn
  exact TypeCodeInterp.mem_univ (TypeCodeInterp.idn i Candidate.snCandidate A m n snA snm snn)

lemma Candidate.tt : Candidate.bool.mem .tt := sn_tt

lemma Candidate.ff : Candidate.bool.mem .ff := sn_ff

lemma Candidate.bool_intro {m : Tm} :
    SN Step m -> Candidate.bool.mem m := by
  intro snm
  exact snm

lemma Candidate.bot_intro {m : Tm} :
    SN Step m -> Candidate.bot.mem m := by
  intro snm
  exact snm

lemma Candidate.rfl {A : Candidate} {a : Tm} :
    SN Step a -> (Candidate.idn A a a).mem (.rfl a) := by
  intro sna
  exact sn_rfl sna

lemma Candidate.idn_intro {A : Candidate} {a b m : Tm} :
    SN Step m -> (Candidate.idn A a b).mem m := by
  intro snm
  exact snm

lemma Candidate.ite {D : Candidate} {A m n1 n2 : Tm} :
    Candidate.Expansive D ->
    (∀ A', A ~> A' -> D.mem (.ite A' m n1 n2)) ->
    (∀ m', m ~> m' -> D.mem (.ite A m' n1 n2)) ->
    (∀ n1', n1 ~> n1' -> D.mem (.ite A m n1' n2)) ->
    (∀ n2', n2 ~> n2' -> D.mem (.ite A m n1 n2')) ->
    D.mem n1 ->
    D.mem n2 ->
    D.mem (.ite A m n1 n2) := by
  intro hD hA hm hn1 hn2 htt hff
  apply Candidate.expansive_of_steps hD
  intro x st
  cases st with
  | ite_A m n1 n2 stA =>
    exact hA _ stA
  | ite_M A n1 n2 stM =>
    exact hm _ stM
  | ite_N1 A m n2 stN1 =>
    exact hn1 _ stN1
  | ite_N2 A m n1 stN2 =>
    exact hn2 _ stN2
  | ite_tt A n1 n2 =>
    exact htt
  | ite_ff A n1 n2 =>
    exact hff

lemma Candidate.bool_ite {B : CandidateFamily Candidate.bool} {A m n1 n2 : Tm} :
    B.Expansive ->
    SN Step A ->
    (hm : Candidate.bool.mem m) ->
    (B.fiber .tt).mem n1 ->
    (B.fiber .ff).mem n2 ->
    (B.fiber m).mem (.ite A m n1 n2) := by
  intro hB snA
  induction snA generalizing m n1 n2
  case intro A ihA ihA' =>
    intro hm
    have snm := Candidate.bool.sn hm
    induction snm generalizing n1 n2
    case intro m ihM ihM' =>
      intro hn1 hn2
      have sn1 := (B.fiber .tt).sn hn1
      induction sn1 generalizing n2
      case intro n1 ih1 ih1' =>
        have sn2 := (B.fiber .ff).sn hn2
        induction sn2
        case intro n2 ih2 ih2' =>
          apply Candidate.expansive_of_steps (hB hm)
          intro x st
          cases st with
          | ite_A m n1 n2 stA =>
            exact ihA' stA hm hn1 hn2
          | ite_M A n1 n2 stM =>
            have hm' := Candidate.bool.closed_step hm stM
            exact B.stable_step hm stM (ihM' stM hm' hn1 hn2)
          | ite_N1 A m n2 stN1 =>
            exact ih1' stN1 ((B.fiber .tt).closed_step hn1 stN1) hn2
          | ite_N2 A m n1 stN2 =>
            exact ih2' stN2 ((B.fiber .ff).closed_step hn2 stN2)
          | ite_tt A n1 n2 =>
            exact hn1
          | ite_ff A n1 n2 =>
            exact hn2

lemma Candidate.bool_ite_cases {T F : Candidate} {A m n1 n2 : Tm} :
    Candidate.Expansive T ->
    Candidate.Expansive F ->
    SN Step A ->
    (hm : Candidate.bool.mem m) ->
    T.mem n1 ->
    F.mem n2 ->
    ((CandidateFamily.boolCases T F).fiber m).mem (.ite A m n1 n2) := by
  intro hT hF snA hm hn1 hn2
  apply Candidate.bool_ite
  . exact CandidateFamily.boolCases_expansive hT hF
  . exact snA
  . exact hm
  . exact CandidateFamily.boolCases_tt hn1
  . exact CandidateFamily.boolCases_ff hn2

lemma Candidate.rw {D : Candidate} {A m n : Tm} :
    Candidate.Expansive D ->
    (∀ A', A ~> A' -> D.mem (.rw A' m n)) ->
    (∀ m', m ~> m' -> D.mem (.rw A m' n)) ->
    (∀ n', n ~> n' -> D.mem (.rw A m n')) ->
    D.mem m ->
    D.mem (.rw A m n) := by
  intro hD hA hm hn hrfl
  apply Candidate.expansive_of_steps hD
  intro x st
  cases st with
  | rw_A m n stA =>
    exact hA _ stA
  | rw_M A n stM =>
    exact hm _ stM
  | rw_N A m stN =>
    exact hn _ stN
  | rw_elim A m n =>
    exact hrfl

lemma Candidate.rw_dep {I : Candidate} {a b : Tm}
    {D : CandidateFamily (Candidate.idn I a b)} {A m n : Tm} :
    D.Expansive ->
    (hn : (Candidate.idn I a b).mem n) ->
    (∀ A', A ~> A' -> (D.fiber n).mem (.rw A' m n)) ->
    (∀ m', m ~> m' -> (D.fiber n).mem (.rw A m' n)) ->
    (∀ n', n ~> n' -> (D.fiber n').mem (.rw A m n')) ->
    (∀ c, (D.fiber (.rfl c)).mem m) ->
    (D.fiber n).mem (.rw A m n) := by
  intro hD hn hA hm hnStep hrfl
  apply Candidate.expansive_of_steps (hD hn)
  intro x st
  cases st with
  | rw_A m n stA =>
    exact hA _ stA
  | rw_M A n stM =>
    exact hm _ stM
  | rw_N A m stN =>
    exact D.stable_step hn stN (hnStep _ stN)
  | rw_elim A m c =>
    exact hrfl c

lemma Candidate.exf {D : Candidate} {A m : Tm} :
    Candidate.Expansive D ->
    (∀ A', A ~> A' -> D.mem (.exf A' m)) ->
    (∀ m', m ~> m' -> D.mem (.exf A m')) ->
    D.mem (.exf A m) := by
  intro hD hA hm
  apply Candidate.expansive_of_steps hD
  intro x st
  cases st with
  | exf_A m stA =>
    exact hA _ stA
  | exf_M A stM =>
    exact hm _ stM

lemma Candidate.exf_dep {B : CandidateFamily Candidate.bot} {A m : Tm} :
    B.Expansive ->
    (hm : Candidate.bot.mem m) ->
    (∀ A', A ~> A' -> (B.fiber m).mem (.exf A' m)) ->
    (∀ m', m ~> m' -> (B.fiber m').mem (.exf A m')) ->
    (B.fiber m).mem (.exf A m) := by
  intro hB hm hA hmStep
  apply Candidate.expansive_of_steps (hB hm)
  intro x st
  cases st with
  | exf_A m stA =>
    exact hA _ stA
  | exf_M A stM =>
    exact B.stable_step hm stM (hmStep _ stM)

lemma Candidate.ite_sn {A m n1 n2 : Tm} :
    SN Step A ->
    Candidate.bool.mem m ->
    SN Step n1 ->
    SN Step n2 ->
    SN Step (.ite A m n1 n2) := by
  intro snA hm sn1 sn2
  exact sn_ite snA hm sn1 sn2

lemma Candidate.rw_sn {A m n : Tm} {C : Candidate} {a b : Tm} :
    SN Step A ->
    SN Step m ->
    (Candidate.idn C a b).mem n ->
    SN Step (.rw A m n) := by
  intro snA snm hn
  exact sn_rw snA snm hn

lemma Candidate.exf_sn {A m : Tm} :
    SN Step A ->
    Candidate.bot.mem m ->
    SN Step (.exf A m) := by
  intro snA hm
  exact sn_exf snA hm

abbrev CandCtx := List Candidate

namespace CandCtx

def sn (Γ : Ctx) : CandCtx :=
  Γ.map fun _ => Candidate.snCandidate

@[simp] lemma sn_nil : sn [] = [] := by
  rfl

@[simp] lemma sn_cons (Γ : Ctx) (A : Tm) :
    sn (A :: Γ) = Candidate.snCandidate :: sn Γ := by
  rfl

end CandCtx

@[scoped aesop safe [constructors]]
inductive HasCand : CandCtx -> Var -> Candidate -> Prop where
  | zero Δ C :
    HasCand (C :: Δ) 0 C
  | succ Δ C D x :
    HasCand Δ x C ->
    HasCand (D :: Δ) (x + 1) C

def CandSubst (Δ : CandCtx) (σ : Var -> Tm) : Prop :=
  ∀ {x C}, HasCand Δ x C -> C.mem (σ x)

namespace CandCtx

def Weakens (Δ : CandCtx) : Prop :=
  ∀ {x C}, HasCand Δ x C -> Candidate.Weakens C

lemma sn_weakens (Γ : Ctx) : (CandCtx.sn Γ).Weakens := by
  intro x C hs
  induction Γ generalizing x C with
  | nil =>
    cases hs
  | cons A Γ ih =>
    cases hs with
    | zero =>
      exact Candidate.snCandidate_weakens
    | succ Δ C D x hs =>
      exact ih hs

end CandCtx

namespace HasCand

lemma mem {Δ : CandCtx} {σ : Var -> Tm} {x C} :
    HasCand Δ x C -> CandSubst Δ σ -> C.mem (σ x) := by
  intro hs hσ
  exact hσ hs

lemma of_has_sn {Γ : Ctx} {x : Var} {A : Tm} :
    Has Γ x A -> HasCand (CandCtx.sn Γ) x Candidate.snCandidate := by
  intro hs
  induction hs with
  | zero Γ A =>
    exact HasCand.zero (CandCtx.sn Γ) Candidate.snCandidate
  | succ Γ A B x hs ih =>
    exact HasCand.succ (CandCtx.sn Γ) Candidate.snCandidate Candidate.snCandidate x ih

end HasCand

namespace CandSubst

lemma nil {σ : Var -> Tm} : CandSubst [] σ := by
  intro x C hs
  cases hs

lemma cons {Δ : CandCtx} {σ : Var -> Tm} {C : Candidate} {m : Tm} :
    C.mem m ->
    CandSubst Δ σ ->
    CandSubst (C :: Δ) (m .: σ) := by
  intro hm hσ x D hs
  cases hs with
  | zero =>
    asimp
    exact hm
  | succ Δ D C x hs =>
    asimp
    exact hσ hs

lemma head {Δ : CandCtx} {σ : Var -> Tm} {C : Candidate} :
    CandSubst (C :: Δ) σ -> C.mem (σ 0) := by
  intro hσ
  exact hσ (HasCand.zero Δ C)

lemma tail {Δ : CandCtx} {σ : Var -> Tm} {C : Candidate} :
    CandSubst (C :: Δ) σ -> CandSubst Δ (fun x => σ (x + 1)) := by
  intro hσ x D hs
  exact hσ (HasCand.succ Δ D C x hs)

lemma ids (Δ : CandCtx) : CandSubst Δ ids := by
  intro x C hs
  induction hs with
  | zero Δ C =>
    exact Candidate.var C 0
  | succ Δ C D x hs ih =>
    exact Candidate.var C (x + 1)

lemma closed_red {Δ : CandCtx} {σ τ : Var -> Tm} :
    CandSubst Δ σ ->
    SRed σ τ ->
    CandSubst Δ τ := by
  intro hσ hred x C hs
  exact C.closed_red (hσ hs) (hred x)

lemma cons_closed_red {Δ : CandCtx} {σ τ : Var -> Tm} {C : Candidate} {m n : Tm} :
    C.mem m ->
    m ~>* n ->
    CandSubst Δ σ ->
    SRed σ τ ->
    CandSubst (C :: Δ) (n .: τ) := by
  intro hm rd hσ hred
  apply CandSubst.cons
  . exact C.closed_red hm rd
  . exact CandSubst.closed_red hσ hred

lemma sn_of_has {Γ : Ctx} {σ : Var -> Tm} {x : Var} {A : Tm} :
    CandSubst (CandCtx.sn Γ) σ ->
    Has Γ x A ->
    SN Step (σ x) := by
  intro hσ hs
  exact hσ (HasCand.of_has_sn hs)

end CandSubst

structure DCandCtx where
  valid : (Var -> Tm) -> Prop
  closed_red : ∀ {σ τ}, valid σ -> SRed σ τ -> valid τ

namespace DCandCtx

def empty : DCandCtx where
  valid _ := True
  closed_red _ _ := trivial

def Weakens (Δ : DCandCtx) : Prop :=
  ∀ {σ}, Δ.valid σ -> Δ.valid (fun x => (σ x).[shift 1])

lemma empty_weakens : DCandCtx.empty.Weakens := by
  intro σ hσ
  trivial

lemma weakens_iter {Δ : DCandCtx} (hΔ : Δ.Weakens) {σ : Var -> Tm} :
    Δ.valid σ -> ∀ i, Δ.valid (shiftSubst σ i) := by
  intro hσ i
  induction i with
  | zero =>
    simpa [shiftSubst_zero] using hσ
  | succ i ih =>
    have h := hΔ ih
    have hsubst :
        (fun x => (shiftSubst σ i x).[shift 1]) = shiftSubst σ (i + 1) := by
      funext x
      simp [shiftSubst, subst_shift_shift]
    simpa [hsubst] using h

def ofCandCtx (Δ : CandCtx) : DCandCtx where
  valid σ := CandSubst Δ σ
  closed_red hσ hred := CandSubst.closed_red hσ hred

lemma ofCandCtx_weakens {Δ : CandCtx} :
    Δ.Weakens -> (DCandCtx.ofCandCtx Δ).Weakens := by
  intro hΔ σ hσ x C hs
  exact hΔ hs (hσ hs)

lemma of_sn_weakens (Γ : Ctx) :
    (DCandCtx.ofCandCtx (CandCtx.sn Γ)).Weakens :=
  DCandCtx.ofCandCtx_weakens (CandCtx.sn_weakens Γ)

end DCandCtx

structure TypeInterp (Δ : DCandCtx) (A : Tm) where
  cand : (Var -> Tm) -> Candidate
  type_sn : ∀ σ, Δ.valid σ -> SN Step A.[σ]
  stable_red :
    ∀ {σ τ m}, Δ.valid σ -> SRed σ τ -> (cand τ).mem m -> (cand σ).mem m
  stable_red_fwd :
    ∀ {σ τ m}, Δ.valid σ -> SRed σ τ -> (cand σ).mem m -> (cand τ).mem m
  stable_conv :
    ∀ {σ τ m}, Δ.valid σ -> Δ.valid τ -> SConv σ τ -> (cand σ).mem m -> (cand τ).mem m

namespace TypeInterp

def Weakens {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A) : Prop :=
  ∀ {σ m}, Δ.valid σ -> (I.cand σ).mem m ->
    (I.cand (fun x => (σ x).[shift 1])).mem m.[shift 1]

lemma weakens_iter {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A)
    (hΔ : Δ.Weakens) (hI : I.Weakens) {σ : Var -> Tm} {m : Tm} :
    Δ.valid σ -> (I.cand σ).mem m ->
    ∀ i, (I.cand (shiftSubst σ i)).mem m.[shift i] := by
  intro hσ hm i
  induction i with
  | zero =>
    simpa [shiftSubst_zero, SubstLemmas.shift0, Tm.subst_id] using hm
  | succ i ih =>
    have hvalid : Δ.valid (shiftSubst σ i) :=
      DCandCtx.weakens_iter hΔ hσ i
    have h := hI hvalid ih
    have hsubst :
        (fun x => (shiftSubst σ i x).[shift 1]) = shiftSubst σ (i + 1) := by
      funext x
      simp [shiftSubst, subst_shift_shift]
    simpa [hsubst, subst_shift_shift] using h

def SemTm {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A) (m : Tm) : Prop :=
  ∀ σ, Δ.valid σ -> (I.cand σ).mem m.[σ]

lemma semTm_sn {Δ : DCandCtx} {A m : Tm} (I : TypeInterp Δ A) :
    I.SemTm m -> ∀ σ, (hσ : Δ.valid σ) -> SN Step m.[σ] := by
  intro hm σ hσ
  exact (I.cand σ).sn (hm σ hσ)

lemma semTm_closed_red {Δ : DCandCtx} {A m n : Tm} (I : TypeInterp Δ A) :
    I.SemTm m ->
    (∀ σ, Δ.valid σ -> m.[σ] ~>* n.[σ]) ->
    I.SemTm n := by
  intro hm hred σ hσ
  exact (I.cand σ).closed_red (hm σ hσ) (hred σ hσ)

lemma semTm_conv {Δ : DCandCtx} {A m n : Tm} (I : TypeInterp Δ A) :
    (∀ σ, Δ.valid σ -> Candidate.Expansive (I.cand σ)) ->
    (∀ σ, Δ.valid σ -> SN Step m.[σ]) ->
    (∀ σ, Δ.valid σ -> m.[σ] === n.[σ]) ->
    I.SemTm n ->
    I.SemTm m := by
  intro hI hsn heq hn σ hσ
  exact Candidate.conv_of_expansive (hI σ hσ) (hsn σ hσ) (heq σ hσ) (hn σ hσ)

lemma stable_conv_sym {Δ : DCandCtx} {A m : Tm} (I : TypeInterp Δ A)
    {σ τ : Var -> Tm} :
    Δ.valid σ -> Δ.valid τ -> SConv σ τ ->
    (I.cand τ).mem m -> (I.cand σ).mem m := by
  intro hσ hτ hconv hm
  exact I.stable_conv hτ hσ (fun x => (hconv x).sym) hm

def toTypeCode {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A)
    (i : Nat) (σ : Var -> Tm) (hσ : Δ.valid σ) : TypeCodeInterp i A.[σ] where
  cand := I.cand σ
  type_sn := I.type_sn σ hσ

lemma semUniv {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A) (i : Nat) :
    ∀ σ, (hσ : Δ.valid σ) -> (Candidate.univ i).mem A.[σ] := by
  intro σ hσ
  exact TypeCodeInterp.mem_univ (I.toTypeCode i σ hσ)

def const (Δ : DCandCtx) (A : Tm) (C : Candidate)
    (hA : ∀ σ, Δ.valid σ -> SN Step A.[σ]) : TypeInterp Δ A where
  cand _ := C
  type_sn := hA
  stable_red _ _ hm := hm
  stable_red_fwd _ _ hm := hm
  stable_conv _ _ _ hm := hm

def univ (Δ : DCandCtx) (i : Nat) : TypeInterp Δ (.ty i) :=
  TypeInterp.const Δ (.ty i) (Candidate.univ i)
    (by intro σ hσ; asimp; exact sn_ty)

def bool (Δ : DCandCtx) : TypeInterp Δ .bool :=
  TypeInterp.const Δ .bool Candidate.bool
    (by intro σ hσ; asimp; exact sn_bool)

def bot (Δ : DCandCtx) : TypeInterp Δ .bot :=
  TypeInterp.const Δ .bot Candidate.bot
    (by intro σ hσ; asimp; exact sn_bot)

def idn {Δ : DCandCtx} {A m n : Tm} (I : TypeInterp Δ A)
    (hm : I.SemTm m) (hn : I.SemTm n) :
    TypeInterp Δ (.idn A m n) :=
  TypeInterp.const Δ (.idn A m n) (Candidate.idn Candidate.snCandidate m n)
    (by
      intro σ hσ
      asimp
      exact sn_idn (I.type_sn σ hσ) ((I.cand σ).sn (hm σ hσ))
        ((I.cand σ).sn (hn σ hσ)))

lemma const_weakens {Δ : DCandCtx} {A : Tm} {C : Candidate}
    {hA : ∀ σ, Δ.valid σ -> SN Step A.[σ]} :
    Candidate.Weakens C -> (TypeInterp.const Δ A C hA).Weakens := by
  intro hC σ m hσ hm
  exact hC hm

lemma univ_weakens (Δ : DCandCtx) (i : Nat) :
    (TypeInterp.univ Δ i).Weakens :=
  TypeInterp.const_weakens Candidate.univ_weakens

lemma bool_weakens (Δ : DCandCtx) :
    (TypeInterp.bool Δ).Weakens :=
  TypeInterp.const_weakens Candidate.bool_weakens

lemma bot_weakens (Δ : DCandCtx) :
    (TypeInterp.bot Δ).Weakens :=
  TypeInterp.const_weakens Candidate.bot_weakens

lemma idn_weakens {Δ : DCandCtx} {A m n : Tm} {I : TypeInterp Δ A}
    {hm : I.SemTm m} {hn : I.SemTm n} :
    (TypeInterp.idn I hm hn).Weakens :=
  TypeInterp.const_weakens Candidate.idn_weakens

lemma semTt {Δ : DCandCtx} : (TypeInterp.bool Δ).SemTm .tt := by
  intro σ hσ
  asimp
  exact sn_tt

lemma semFf {Δ : DCandCtx} : (TypeInterp.bool Δ).SemTm .ff := by
  intro σ hσ
  asimp
  exact sn_ff

lemma semRfl {Δ : DCandCtx} {A m : Tm} {I : TypeInterp Δ A}
    (hm : I.SemTm m) :
    (TypeInterp.idn I hm hm).SemTm (.rfl m) := by
  intro σ hσ
  asimp
  exact sn_rfl ((I.cand σ).sn (hm σ hσ))

end TypeInterp

def DCandCtx.extend {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A) : DCandCtx where
  valid σ :=
    Δ.valid (fun x => σ (x + 1)) ∧
    (I.cand (fun x => σ (x + 1))).mem (σ 0)
  closed_red := by
    intro σ τ hσ hred
    constructor
    . exact Δ.closed_red hσ.1 (fun x => hred (x + 1))
    . have htail : SRed (fun x => σ (x + 1)) (fun x => τ (x + 1)) := by
        intro x
        exact hred (x + 1)
      have hhead : (I.cand (fun x => τ (x + 1))).mem (σ 0) :=
        I.stable_red_fwd hσ.1 htail hσ.2
      exact (I.cand (fun x => τ (x + 1))).closed_red hhead (hred 0)

namespace DCandCtx

lemma extend_tail {Δ : DCandCtx} {A : Tm} {I : TypeInterp Δ A}
    {σ : Var -> Tm} :
    (DCandCtx.extend I).valid σ -> Δ.valid (fun x => σ (x + 1)) := by
  intro hσ
  exact hσ.1

lemma extend_head {Δ : DCandCtx} {A : Tm} {I : TypeInterp Δ A}
    {σ : Var -> Tm} :
    (hσ : (DCandCtx.extend I).valid σ) ->
    (I.cand (fun x => σ (x + 1))).mem (σ 0) := by
  intro hσ
  exact hσ.2

lemma extend_cons {Δ : DCandCtx} {A : Tm} {I : TypeInterp Δ A}
    {σ : Var -> Tm} {m : Tm} :
    Δ.valid σ ->
    (I.cand σ).mem m ->
    (DCandCtx.extend I).valid (m .: σ) := by
  intro hσ hm
  constructor
  . exact hσ
  . exact hm

lemma extend_up_valid {Δ : DCandCtx} {A : Tm} {I : TypeInterp Δ A}
    (hΔ : Δ.Weakens) {σ : Var -> Tm} :
    Δ.valid σ -> (DCandCtx.extend I).valid (up σ) := by
  intro hσ
  have htail : (fun x => up σ (x + 1)) = (fun x => (σ x).[shift 1]) := by
    funext x
    asimp [up, Tm.rename_subst]
  constructor
  . rw [htail]
    exact hΔ hσ
  . rw [htail]
    change (I.cand (fun x => (σ x).[shift 1])).mem (.var 0)
    exact Candidate.var _ 0

lemma extend_weakens {Δ : DCandCtx} {A : Tm} {I : TypeInterp Δ A} :
    Δ.Weakens -> I.Weakens -> (DCandCtx.extend I).Weakens := by
  intro hΔ hI σ hσ
  have htail : (fun x => (σ (x + 1)).[shift 1]) =
      (fun x => (fun y => (σ y).[shift 1]) (x + 1)) := by
    rfl
  constructor
  . rw [← htail]
    exact hΔ hσ.1
  . rw [← htail]
    exact hI hσ.1 hσ.2

lemma extend_univ_weakens {Δ : DCandCtx} {i : Nat} :
    Δ.Weakens -> (DCandCtx.extend (TypeInterp.univ Δ i)).Weakens := by
  intro hΔ
  exact DCandCtx.extend_weakens hΔ (TypeInterp.univ_weakens Δ i)

lemma extend_bool_weakens {Δ : DCandCtx} :
    Δ.Weakens -> (DCandCtx.extend (TypeInterp.bool Δ)).Weakens := by
  intro hΔ
  exact DCandCtx.extend_weakens hΔ (TypeInterp.bool_weakens Δ)

lemma extend_bot_weakens {Δ : DCandCtx} :
    Δ.Weakens -> (DCandCtx.extend (TypeInterp.bot Δ)).Weakens := by
  intro hΔ
  exact DCandCtx.extend_weakens hΔ (TypeInterp.bot_weakens Δ)

end DCandCtx

namespace TypeInterp

def family {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) (hσ : Δ.valid σ) : CandidateFamily (IA.cand σ) where
  fiber a := IB.cand (a .: σ)
  stable_step := by
    intro a a' m ha st hm
    have hvalid : (DCandCtx.extend IA).valid (a .: σ) :=
      DCandCtx.extend_cons hσ ha
    have hred : SRed (a .: σ) (a' .: σ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact Star.one st
      | succ x =>
        asimp
        exact Star.R
    exact IB.stable_red hvalid hred hm
  stable_step_fwd := by
    intro a a' m ha st hm
    have hvalid : (DCandCtx.extend IA).valid (a .: σ) :=
      DCandCtx.extend_cons hσ ha
    have hred : SRed (a .: σ) (a' .: σ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact Star.one st
      | succ x =>
        asimp
        exact Star.R
    exact IB.stable_red_fwd hvalid hred hm

lemma family_expansive {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ))
    {σ : Var -> Tm} (hσ : Δ.valid σ) :
    (TypeInterp.family IA IB σ hσ).Expansive := by
  intro a ha
  exact hIB (a .: σ) (DCandCtx.extend_cons hσ ha)

def piCand {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) (hσ : Δ.valid σ) : Candidate :=
  Candidate.pi (IA.cand σ) (TypeInterp.family IA IB σ hσ)

def sigCand {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) (hσ : Δ.valid σ) : Candidate :=
  Candidate.sigma (IA.cand σ) (TypeInterp.family IA IB σ hσ)

noncomputable def piCandTotal {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) : Candidate := by
  classical
  exact if hσ : Δ.valid σ then TypeInterp.piCand IA IB σ hσ else Candidate.snCandidate

lemma piCandTotal_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    {σ : Var -> Tm} (hσ : Δ.valid σ) :
    TypeInterp.piCandTotal IA IB σ = TypeInterp.piCand IA IB σ hσ := by
  classical
  simp [TypeInterp.piCandTotal, hσ]

noncomputable def sigCandTotal {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) : Candidate := by
  classical
  exact if hσ : Δ.valid σ then TypeInterp.sigCand IA IB σ hσ else Candidate.snCandidate

lemma sigCandTotal_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    {σ : Var -> Tm} (hσ : Δ.valid σ) :
    TypeInterp.sigCandTotal IA IB σ = TypeInterp.sigCand IA IB σ hσ := by
  classical
  simp [TypeInterp.sigCandTotal, hσ]

noncomputable def pi {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) : TypeInterp Δ (.pi A B) where
  cand := TypeInterp.piCandTotal IA IB
  type_sn := by
    intro σ hσ
    asimp
    exact sn_pi (IA.type_sn σ hσ)
      (IB.type_sn (up σ) (DCandCtx.extend_up_valid hΔ hσ))
  stable_red := by
    intro σ τ m hσ hred hm
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.piCandTotal_valid IA IB hτ] at hm
    rw [TypeInterp.piCandTotal_valid IA IB hσ]
    dsimp [TypeInterp.piCand, Candidate.pi] at hm ⊢
    rcases hm with ⟨hmSN, hmApp⟩
    constructor
    . exact hmSN
    . intro n hnσ
      have hnτ : (IA.cand τ).mem n :=
        IA.stable_red_fwd hσ hred hnσ
      have happτ := hmApp n hnτ
      have hσext : (DCandCtx.extend IA).valid (n .: σ) :=
        DCandCtx.extend_cons hσ hnσ
      exact IB.stable_red hσext (SRed.scons_same hred) happτ
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.piCandTotal_valid IA IB hσ] at hm
    rw [TypeInterp.piCandTotal_valid IA IB hτ]
    dsimp [TypeInterp.piCand, Candidate.pi] at hm ⊢
    rcases hm with ⟨hmSN, hmApp⟩
    constructor
    . exact hmSN
    . intro n hnτ
      have hnσ : (IA.cand σ).mem n :=
        IA.stable_red hσ hred hnτ
      have happσ := hmApp n hnσ
      have hσext : (DCandCtx.extend IA).valid (n .: σ) :=
        DCandCtx.extend_cons hσ hnσ
      exact IB.stable_red_fwd hσext (SRed.scons_same hred) happσ
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    rw [TypeInterp.piCandTotal_valid IA IB hσ] at hm
    rw [TypeInterp.piCandTotal_valid IA IB hτ]
    dsimp [TypeInterp.piCand, Candidate.pi] at hm ⊢
    rcases hm with ⟨hmSN, hmApp⟩
    constructor
    . exact hmSN
    . intro n hnτ
      have hnσ : (IA.cand σ).mem n :=
        IA.stable_conv_sym hσ hτ hconv hnτ
      have happσ := hmApp n hnσ
      have hσext : (DCandCtx.extend IA).valid (n .: σ) :=
        DCandCtx.extend_cons hσ hnσ
      have hτext : (DCandCtx.extend IA).valid (n .: τ) :=
        DCandCtx.extend_cons hτ hnτ
      exact IB.stable_conv hσext hτext (SConv.scons_same hconv) happσ

noncomputable def sig {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) : TypeInterp Δ (.sig A B) where
  cand := TypeInterp.sigCandTotal IA IB
  type_sn := by
    intro σ hσ
    asimp
    exact sn_sig (IA.type_sn σ hσ)
      (IB.type_sn (up σ) (DCandCtx.extend_up_valid hΔ hσ))
  stable_red := by
    intro σ τ m hσ hred hm
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.sigCandTotal_valid IA IB hτ] at hm
    rw [TypeInterp.sigCandTotal_valid IA IB hσ]
    dsimp [TypeInterp.sigCand, Candidate.sigma] at hm ⊢
    rcases hm with ⟨hmSN, hmPair⟩
    constructor
    . exact hmSN
    . intro a b rd
      have ⟨haτ, hbτ⟩ := hmPair a b rd
      have haσ : (IA.cand σ).mem a :=
        IA.stable_red hσ hred haτ
      have hσext : (DCandCtx.extend IA).valid (a .: σ) :=
        DCandCtx.extend_cons hσ haσ
      exact ⟨haσ, IB.stable_red hσext (SRed.scons_same hred) hbτ⟩
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.sigCandTotal_valid IA IB hσ] at hm
    rw [TypeInterp.sigCandTotal_valid IA IB hτ]
    dsimp [TypeInterp.sigCand, Candidate.sigma] at hm ⊢
    rcases hm with ⟨hmSN, hmPair⟩
    constructor
    . exact hmSN
    . intro a b rd
      have ⟨haσ, hbσ⟩ := hmPair a b rd
      have haτ : (IA.cand τ).mem a :=
        IA.stable_red_fwd hσ hred haσ
      have hσext : (DCandCtx.extend IA).valid (a .: σ) :=
        DCandCtx.extend_cons hσ haσ
      exact ⟨haτ, IB.stable_red_fwd hσext (SRed.scons_same hred) hbσ⟩
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    rw [TypeInterp.sigCandTotal_valid IA IB hσ] at hm
    rw [TypeInterp.sigCandTotal_valid IA IB hτ]
    dsimp [TypeInterp.sigCand, Candidate.sigma] at hm ⊢
    rcases hm with ⟨hmSN, hmPair⟩
    constructor
    . exact hmSN
    . intro a b rd
      have ⟨haσ, hbσ⟩ := hmPair a b rd
      have haτ : (IA.cand τ).mem a :=
        IA.stable_conv hσ hτ hconv haσ
      have hσext : (DCandCtx.extend IA).valid (a .: σ) :=
        DCandCtx.extend_cons hσ haσ
      have hτext : (DCandCtx.extend IA).valid (a .: τ) :=
        DCandCtx.extend_cons hτ haτ
      exact ⟨haτ, IB.stable_conv hσext hτext (SConv.scons_same hconv) hbσ⟩

def piCodeAt {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) (σ : Var -> Tm) (hσ : Δ.valid σ) :
    SN Step B.[up σ] -> TypeCodeInterp i (.pi A B).[σ] := by
  intro hB
  asimp
  exact TypeCodeInterp.pi i A.[σ] B.[up σ]
    (IA.cand σ) (TypeInterp.family IA IB σ hσ)
    (IA.type_sn σ hσ) hB

lemma semPiUnivAt {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) :
    (∀ σ, Δ.valid σ -> SN Step B.[up σ]) ->
    ∀ σ, (hσ : Δ.valid σ) -> (Candidate.univ i).mem (.pi A B).[σ] := by
  intro hB σ hσ
  exact TypeCodeInterp.mem_univ (TypeInterp.piCodeAt IA IB i σ hσ (hB σ hσ))

def sigCodeAt {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) (σ : Var -> Tm) (hσ : Δ.valid σ) :
    SN Step B.[up σ] -> TypeCodeInterp i (.sig A B).[σ] := by
  intro hB
  asimp
  exact TypeCodeInterp.sig i A.[σ] B.[up σ]
    (IA.cand σ) (TypeInterp.family IA IB σ hσ)
    (IA.type_sn σ hσ) hB

lemma semSigUnivAt {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) :
    (∀ σ, Δ.valid σ -> SN Step B.[up σ]) ->
    ∀ σ, (hσ : Δ.valid σ) -> (Candidate.univ i).mem (.sig A B).[σ] := by
  intro hB σ hσ
  exact TypeCodeInterp.mem_univ (TypeInterp.sigCodeAt IA IB i σ hσ (hB σ hσ))

lemma type_sn_up {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B) :
    Δ.Weakens ->
    ∀ σ, (hσ : Δ.valid σ) -> SN Step B.[up σ] := by
  intro hΔ σ hσ
  exact IB.type_sn (up σ) (DCandCtx.extend_up_valid hΔ hσ)

lemma semPiUniv {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) :
    Δ.Weakens ->
    ∀ σ, (hσ : Δ.valid σ) -> (Candidate.univ i).mem (.pi A B).[σ] := by
  intro hΔ
  exact TypeInterp.semPiUnivAt IA IB i (TypeInterp.type_sn_up IA IB hΔ)

lemma semSigUniv {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) :
    Δ.Weakens ->
    ∀ σ, (hσ : Δ.valid σ) -> (Candidate.univ i).mem (.sig A B).[σ] := by
  intro hΔ
  exact TypeInterp.semSigUnivAt IA IB i (TypeInterp.type_sn_up IA IB hΔ)

lemma semPiUniv_empty {A B : Tm}
    (IA : TypeInterp DCandCtx.empty A)
    (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) :
    ∀ σ, (hσ : DCandCtx.empty.valid σ) -> (Candidate.univ i).mem (.pi A B).[σ] := by
  exact TypeInterp.semPiUniv IA IB i DCandCtx.empty_weakens

lemma semSigUniv_empty {A B : Tm}
    (IA : TypeInterp DCandCtx.empty A)
    (IB : TypeInterp (DCandCtx.extend IA) B)
    (i : Nat) :
    ∀ σ, (hσ : DCandCtx.empty.valid σ) -> (Candidate.univ i).mem (.sig A B).[σ] := by
  exact TypeInterp.semSigUniv IA IB i DCandCtx.empty_weakens

def SemBody {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (m : Tm) : Prop :=
  ∀ σ, (hσ : Δ.valid σ) -> ∀ a, (ha : (IA.cand σ).mem a) ->
    (IB.cand (a .: σ)).mem m.[a .: σ]

lemma semBody_of_semTm {Δ : DCandCtx} {A B m : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B) :
    IB.SemTm m -> TypeInterp.SemBody IA IB m := by
  intro hm σ hσ a ha
  exact hm (a .: σ) (DCandCtx.extend_cons hσ ha)

lemma semBody_sn {Δ : DCandCtx} {A B m : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B) :
    TypeInterp.SemBody IA IB m ->
    ∀ σ, (hσ : Δ.valid σ) -> ∀ a, (ha : (IA.cand σ).mem a) ->
      SN Step m.[a .: σ] := by
  intro hm σ hσ a ha
  exact (IB.cand (a .: σ)).sn (hm σ hσ a ha)

lemma semLamPi {Δ : DCandCtx} {A B T m : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B) :
    (∀ σ, Δ.valid σ -> SN Step T.[σ]) ->
    (∀ σ, Δ.valid σ -> SN Step m.[up σ]) ->
    (∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ)) ->
    TypeInterp.SemBody IA IB m ->
    ∀ σ, (hσ : Δ.valid σ) ->
      (TypeInterp.piCand IA IB σ hσ).mem (.lam T m).[σ] := by
  intro hT hm hIB hbody σ hσ
  asimp
  apply Candidate.pi_lam_body (hT σ hσ) (hm σ hσ)
  . exact TypeInterp.family_expansive IA IB hIB hσ
  . intro n hn
    rw[show m.[up σ].[n/] = m.[n .: σ] by asimp]
    exact hbody σ hσ n hn

lemma semLamPiInterp {Δ : DCandCtx} {A B T m : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) :
    (∀ σ, Δ.valid σ -> SN Step T.[σ]) ->
    (∀ σ, Δ.valid σ -> SN Step m.[up σ]) ->
    (∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ)) ->
    TypeInterp.SemBody IA IB m ->
    (TypeInterp.pi IA IB hΔ).SemTm (.lam T m) := by
  intro hT hm hIB hbody σ hσ
  change (TypeInterp.piCandTotal IA IB σ).mem (.lam T m).[σ]
  rw [TypeInterp.piCandTotal_valid IA IB hσ]
  exact TypeInterp.semLamPi IA IB hT hm hIB hbody σ hσ

lemma semAppPi {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B) :
    (∀ σ, (hσ : Δ.valid σ) -> (TypeInterp.piCand IA IB σ hσ).mem m.[σ]) ->
    IA.SemTm n ->
    ∀ σ, (hσ : Δ.valid σ) ->
      (IB.cand (n.[σ] .: σ)).mem (.app m n).[σ] := by
  intro hm hn σ hσ
  asimp
  exact Candidate.pi_app (hm σ hσ) (hn σ hσ)

lemma semAppPiInterp {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) :
    (TypeInterp.pi IA IB hΔ).SemTm m ->
    IA.SemTm n ->
    ∀ σ, (hσ : Δ.valid σ) ->
      (IB.cand (n.[σ] .: σ)).mem (.app m n).[σ] := by
  intro hm hn
  apply TypeInterp.semAppPi IA IB
  . intro σ hσ
    have h := hm σ hσ
    change (TypeInterp.piCandTotal IA IB σ).mem m.[σ] at h
    rw [TypeInterp.piCandTotal_valid IA IB hσ] at h
    exact h
  . exact hn

lemma semTupSigma {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B) :
    IA.SemTm m ->
    (∀ σ, (hσ : Δ.valid σ) -> (IB.cand (m.[σ] .: σ)).mem n.[σ]) ->
    ∀ σ, (hσ : Δ.valid σ) ->
      (TypeInterp.sigCand IA IB σ hσ).mem (.tup m n).[σ] := by
  intro hm hn σ hσ
  asimp
  exact Candidate.sigma_pair (hm σ hσ) (hn σ hσ)

lemma semTupSigmaInterp {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) :
    IA.SemTm m ->
    (∀ σ, (hσ : Δ.valid σ) -> (IB.cand (m.[σ] .: σ)).mem n.[σ]) ->
    (TypeInterp.sig IA IB hΔ).SemTm (.tup m n) := by
  intro hm hn σ hσ
  change (TypeInterp.sigCandTotal IA IB σ).mem (.tup m n).[σ]
  rw [TypeInterp.sigCandTotal_valid IA IB hσ]
  exact TypeInterp.semTupSigma IA IB hm hn σ hσ

end TypeInterp

def SemTm (Δ : CandCtx) (m : Tm) (C : Candidate) : Prop :=
  ∀ σ, CandSubst Δ σ -> C.mem m.[σ]

def SemBody (Δ : CandCtx) (A : Candidate) (B : CandidateFamily A) (m : Tm) : Prop :=
  ∀ σ, CandSubst Δ σ -> ∀ n, (hn : A.mem n) -> (B.fiber n).mem m.[n .: σ]

namespace SemBody

lemma sn_subst {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {m : Tm} :
    SemBody Δ A B m ->
    ∀ σ, CandSubst Δ σ -> ∀ n, (hn : A.mem n) -> SN Step m.[n .: σ] := by
  intro hm σ hσ n hn
  exact (B.fiber n).sn (hm σ hσ n hn)

lemma closed_red {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {m n : Tm} :
    SemBody Δ A B m ->
    (∀ σ, CandSubst Δ σ -> ∀ a, (ha : A.mem a) -> m.[a .: σ] ~>* n.[a .: σ]) ->
    SemBody Δ A B n := by
  intro hm hred σ hσ a ha
  exact (B.fiber a).closed_red (hm σ hσ a ha) (hred σ hσ a ha)

lemma conv_of_expansive {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {m n : Tm} :
    B.Expansive ->
    (∀ σ, CandSubst Δ σ -> ∀ a, A.mem a -> SN Step m.[a .: σ]) ->
    (∀ σ, CandSubst Δ σ -> ∀ a, (ha : A.mem a) -> m.[a .: σ] === n.[a .: σ]) ->
    SemBody Δ A B n ->
    SemBody Δ A B m := by
  intro hB hsn heq hn σ hσ a ha
  exact Candidate.conv_of_expansive (hB ha) (hsn σ hσ a ha) (heq σ hσ a ha) (hn σ hσ a ha)

lemma const {Δ : CandCtx} {A B : Candidate} {m : Tm} :
    SemTm (A :: Δ) m B ->
    SemBody Δ A (CandidateFamily.const A B) m := by
  intro hm σ hσ n hn
  exact hm (n .: σ) (CandSubst.cons hn hσ)

lemma const_sn {Δ : CandCtx} {A B : Candidate} {m : Tm} :
    SemTm (A :: Δ) m B ->
    ∀ σ, CandSubst Δ σ -> ∀ n, A.mem n -> SN Step m.[n .: σ] := by
  intro hm σ hσ n hn
  exact B.sn (hm (n .: σ) (CandSubst.cons hn hσ))

end SemBody

namespace SemTm

lemma sn_subst {Δ : CandCtx} {m : Tm} {C : Candidate} :
    SemTm Δ m C ->
    ∀ σ, (hσ : CandSubst Δ σ) -> SN Step m.[σ] := by
  intro hm σ hσ
  exact C.sn (hm σ hσ)

lemma sn_closed {m : Tm} {C : Candidate} :
    SemTm [] m C -> SN Step m := by
  intro hm
  have h := sn_subst hm ids CandSubst.nil
  asimp at h
  exact h

lemma closed_red {Δ : CandCtx} {m n : Tm} {C : Candidate} :
    SemTm Δ m C ->
    (∀ σ, CandSubst Δ σ -> m.[σ] ~>* n.[σ]) ->
    SemTm Δ n C := by
  intro hm hred σ hσ
  exact C.closed_red (hm σ hσ) (hred σ hσ)

lemma conv_of_expansive {Δ : CandCtx} {m n : Tm} {C : Candidate} :
    Candidate.Expansive C ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[σ]) ->
    (∀ σ, CandSubst Δ σ -> m.[σ] === n.[σ]) ->
    SemTm Δ n C ->
    SemTm Δ m C := by
  intro hC hsn heq hn σ hσ
  exact Candidate.conv_of_expansive hC (hsn σ hσ) (heq σ hσ) (hn σ hσ)

lemma var {Δ : CandCtx} {x C} :
    HasCand Δ x C -> SemTm Δ (.var x) C := by
  intro hs σ hσ
  asimp
  exact hσ hs

lemma var_snCtx {Γ : Ctx} {x : Var} {A : Tm} :
    Has Γ x A -> SemTm (CandCtx.sn Γ) (.var x) Candidate.snCandidate := by
  intro hs
  exact SemTm.var (HasCand.of_has_sn hs)

lemma snCandidate {Δ : CandCtx} {m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step m.[σ]) ->
    SemTm Δ m Candidate.snCandidate := by
  intro hsn σ hσ
  exact hsn σ hσ

lemma app_arrow {Δ : CandCtx} {A B : Candidate} {m n : Tm} :
    SemTm Δ m (Candidate.arrow A B) ->
    SemTm Δ n A ->
    SemTm Δ (.app m n) B := by
  intro hm hn σ hσ
  asimp
  exact Candidate.arrow_app (hm σ hσ) (hn σ hσ)

lemma app_pi {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {m n : Tm} :
    SemTm Δ m (Candidate.pi A B) ->
    SemTm Δ n A ->
    ∀ σ, (hσ : CandSubst Δ σ) -> (B.fiber n.[σ]).mem (.app m n).[σ] := by
  intro hm hn σ hσ
  asimp
  exact Candidate.pi_app (hm σ hσ) (hn σ hσ)

lemma tup_sigma {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {m n : Tm} :
    SemTm Δ m A ->
    (∀ σ, (hσ : CandSubst Δ σ) -> (B.fiber m.[σ]).mem n.[σ]) ->
    SemTm Δ (.tup m n) (Candidate.sigma A B) := by
  intro hm hn σ hσ
  asimp
  exact Candidate.sigma_pair (hm σ hσ) (hn σ hσ)

lemma tt {Δ : CandCtx} : SemTm Δ .tt Candidate.bool := by
  intro σ hσ
  asimp
  exact Candidate.tt

lemma ff {Δ : CandCtx} : SemTm Δ .ff Candidate.bool := by
  intro σ hσ
  asimp
  exact Candidate.ff

lemma rfl {Δ : CandCtx} {A : Candidate} {m : Tm} :
    SemTm Δ m A ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      (Candidate.idn A m.[σ] m.[σ]).mem (.rfl m).[σ] := by
  intro hm σ hσ
  asimp
  exact Candidate.rfl (A.sn (hm σ hσ))

lemma univ_of_sn {Δ : CandCtx} {i : Nat} {m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step m.[σ]) ->
    SemTm Δ m (Candidate.univ i) := by
  intro hsn σ hσ
  exact Candidate.univ_intro (hsn σ hσ)

lemma ty {Δ : CandCtx} {i j : Nat} :
    SemTm Δ (.ty i) (Candidate.univ j) := by
  intro σ hσ
  asimp
  exact Candidate.ty

lemma bool_type {Δ : CandCtx} {i : Nat} :
    SemTm Δ .bool (Candidate.univ i) := by
  intro σ hσ
  asimp
  exact Candidate.bool_type

lemma bot_type {Δ : CandCtx} {i : Nat} :
    SemTm Δ .bot (Candidate.univ i) := by
  intro σ hσ
  asimp
  exact Candidate.bot_type

lemma pi_type {Δ : CandCtx} {i : Nat} {A B : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step A.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step B.[up σ]) ->
    SemTm Δ (.pi A B) (Candidate.univ i) := by
  intro hA hB σ hσ
  asimp
  exact Candidate.pi_type (hA σ hσ) (hB σ hσ)

lemma sig_type {Δ : CandCtx} {i : Nat} {A B : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step A.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step B.[up σ]) ->
    SemTm Δ (.sig A B) (Candidate.univ i) := by
  intro hA hB σ hσ
  asimp
  exact Candidate.sig_type (hA σ hσ) (hB σ hσ)

lemma idn_type {Δ : CandCtx} {i : Nat} {A m n : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step A.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step n.[σ]) ->
    SemTm Δ (.idn A m n) (Candidate.univ i) := by
  intro hA hm hn σ hσ
  asimp
  exact Candidate.idn_type (hA σ hσ) (hm σ hσ) (hn σ hσ)

lemma arrow_lam_step {Δ : CandCtx} {A B : Candidate} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    Candidate.Expansive B ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ T',
      T.[σ] ~> T' -> (Candidate.arrow A B).mem (.lam T' m.[up σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[up σ] ~> m' -> (Candidate.arrow A B).mem (.lam T.[σ] m')) ->
    (∀ σ, CandSubst Δ σ -> ∀ n, A.mem n -> B.mem m.[n .: σ]) ->
    SemTm Δ (.lam T m) (Candidate.arrow A B) := by
  intro hT hm hB hTStep hmStep hβ σ hσ
  asimp
  apply Candidate.arrow_lam_step (hT σ hσ) (hm σ hσ) hB
  . intro T' stT
    exact hTStep σ hσ T' stT
  . intro m' stM
    exact hmStep σ hσ m' stM
  . intro n hn
    rw[show m.[up σ].[n/] = m.[n .: σ] by asimp]
    exact hβ σ hσ n hn

lemma pi_lam_step {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    B.Expansive ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ T',
      T.[σ] ~> T' -> (Candidate.pi A B).mem (.lam T' m.[up σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[up σ] ~> m' -> (Candidate.pi A B).mem (.lam T.[σ] m')) ->
    (∀ σ, CandSubst Δ σ -> ∀ n, (hn : A.mem n) -> (B.fiber n).mem m.[n .: σ]) ->
    SemTm Δ (.lam T m) (Candidate.pi A B) := by
  intro hT hm hB hTStep hmStep hβ σ hσ
  asimp
  apply Candidate.pi_lam_step (hT σ hσ) (hm σ hσ) hB
  . intro T' stT
    exact hTStep σ hσ T' stT
  . intro m' stM
    exact hmStep σ hσ m' stM
  . intro n hn
    rw[show m.[up σ].[n/] = m.[n .: σ] by asimp]
    exact hβ σ hσ n hn

lemma body_const {Δ : CandCtx} {A B : Candidate} {m : Tm} :
    SemTm (A :: Δ) m B ->
    SemBody Δ A (CandidateFamily.const A B) m := by
  intro hm σ hσ n hn
  exact hm (n .: σ) (CandSubst.cons hn hσ)

lemma arrow_lam_step_body {Δ : CandCtx} {A B : Candidate} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    Candidate.Expansive B ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ T',
      T.[σ] ~> T' -> (Candidate.arrow A B).mem (.lam T' m.[up σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[up σ] ~> m' -> (Candidate.arrow A B).mem (.lam T.[σ] m')) ->
    SemTm (A :: Δ) m B ->
    SemTm Δ (.lam T m) (Candidate.arrow A B) := by
  intro hT hm hB hTStep hmStep hbody
  apply arrow_lam_step hT hm hB hTStep hmStep
  intro σ hσ n hn
  exact hbody (n .: σ) (CandSubst.cons hn hσ)

lemma arrow_lam_body {Δ : CandCtx} {A B : Candidate} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    Candidate.Expansive B ->
    (∀ σ, CandSubst Δ σ -> ∀ n, A.mem n -> B.mem m.[n .: σ]) ->
    SemTm Δ (.lam T m) (Candidate.arrow A B) := by
  intro hT hm hB hbody σ hσ
  asimp
  apply Candidate.arrow_lam_body (hT σ hσ) (hm σ hσ) hB
  intro n hn
  rw[show m.[up σ].[n/] = m.[n .: σ] by asimp]
  exact hbody σ hσ n hn

lemma arrow_lam_body_const {Δ : CandCtx} {A B : Candidate} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    Candidate.Expansive B ->
    SemTm (A :: Δ) m B ->
    SemTm Δ (.lam T m) (Candidate.arrow A B) := by
  intro hT hm hB hbody
  apply arrow_lam_body hT hm hB
  intro σ hσ n hn
  exact hbody (n .: σ) (CandSubst.cons hn hσ)

lemma pi_lam_step_body {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    B.Expansive ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ T',
      T.[σ] ~> T' -> (Candidate.pi A B).mem (.lam T' m.[up σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[up σ] ~> m' -> (Candidate.pi A B).mem (.lam T.[σ] m')) ->
    SemBody Δ A B m ->
    SemTm Δ (.lam T m) (Candidate.pi A B) := by
  intro hT hm hB hTStep hmStep hbody
  apply pi_lam_step hT hm hB hTStep hmStep
  intro σ hσ n hn
  exact hbody σ hσ n hn

lemma pi_lam_body {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A} {T m : Tm} :
    (∀ σ, CandSubst Δ σ -> SN Step T.[σ]) ->
    (∀ σ, CandSubst Δ σ -> SN Step m.[up σ]) ->
    B.Expansive ->
    SemBody Δ A B m ->
    SemTm Δ (.lam T m) (Candidate.pi A B) := by
  intro hT hm hB hbody σ hσ
  asimp
  apply Candidate.pi_lam_body (hT σ hσ) (hm σ hσ) hB
  intro n hn
  rw[show m.[up σ].[n/] = m.[n .: σ] by asimp]
  exact hbody σ hσ n hn

lemma sigma_prj {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A}
    {D : Candidate} {C p n : Tm} :
    Candidate.Expansive D ->
    SemTm Δ p (Candidate.sigma A B) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ C',
      C.[up σ] ~> C' -> D.mem (.prj C' p.[σ] n.[upn 2 σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ p',
      p.[σ] ~> p' -> D.mem (.prj C.[up σ] p' n.[upn 2 σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n',
      n.[upn 2 σ] ~> n' -> D.mem (.prj C.[up σ] p.[σ] n')) ->
    (∀ σ, CandSubst Δ σ -> ∀ a b,
      A.mem a -> (B.fiber a).mem b -> D.mem n.[b .: a .: σ]) ->
    SemTm Δ (.prj C p n) D := by
  intro hD hp hC hpStep hn hβ σ hσ
  asimp
  apply Candidate.sigma_prj hD (hp σ hσ)
  . intro C' stC
    exact hC σ hσ C' stC
  . intro p' stP
    exact hpStep σ hσ p' stP
  . intro n' stN
    exact hn σ hσ n' stN
  . intro a b ha hb
    rw[show n.[upn 2 σ].[b,a/] = n.[b .: a .: σ] by asimp]
    exact hβ σ hσ a b ha hb

lemma sigma_prj_dep {Δ : CandCtx} {A : Candidate} {B : CandidateFamily A}
    {D : CandidateFamily (Candidate.sigma A B)} {C p n : Tm} :
    D.Expansive ->
    SemTm Δ p (Candidate.sigma A B) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ C',
      C.[up σ] ~> C' -> (D.fiber p.[σ]).mem (.prj C' p.[σ] n.[upn 2 σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ p',
      p.[σ] ~> p' -> (D.fiber p').mem (.prj C.[up σ] p' n.[upn 2 σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n',
      n.[upn 2 σ] ~> n' -> (D.fiber p.[σ]).mem (.prj C.[up σ] p.[σ] n')) ->
    (∀ σ, CandSubst Δ σ -> ∀ a b,
      A.mem a -> (B.fiber a).mem b -> (D.fiber (.tup a b)).mem n.[b .: a .: σ]) ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      (D.fiber p.[σ]).mem (.prj C p n).[σ] := by
  intro hD hp hC hpStep hn hβ σ hσ
  asimp
  apply Candidate.sigma_prj_dep hD (hp σ hσ)
  . intro C' stC
    exact hC σ hσ C' stC
  . intro p' stP
    exact hpStep σ hσ p' stP
  . intro n' stN
    exact hn σ hσ n' stN
  . intro a b ha hb
    rw[show n.[upn 2 σ].[b,a/] = n.[b .: a .: σ] by asimp]
    exact hβ σ hσ a b ha hb

lemma ite {Δ : CandCtx} {D : Candidate} {A m n1 n2 : Tm} :
    Candidate.Expansive D ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ A',
      A.[up σ] ~> A' -> D.mem (.ite A' m.[σ] n1.[σ] n2.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[σ] ~> m' -> D.mem (.ite A.[up σ] m' n1.[σ] n2.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n1',
      n1.[σ] ~> n1' -> D.mem (.ite A.[up σ] m.[σ] n1' n2.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n2',
      n2.[σ] ~> n2' -> D.mem (.ite A.[up σ] m.[σ] n1.[σ] n2')) ->
    SemTm Δ n1 D ->
    SemTm Δ n2 D ->
    SemTm Δ (.ite A m n1 n2) D := by
  intro hD hA hm hn1 hn2 htt hff σ hσ
  asimp
  apply Candidate.ite hD
  . intro A' stA
    exact hA σ hσ A' stA
  . intro m' stM
    exact hm σ hσ m' stM
  . intro n1' stN1
    exact hn1 σ hσ n1' stN1
  . intro n2' stN2
    exact hn2 σ hσ n2' stN2
  . exact htt σ hσ
  . exact hff σ hσ

lemma ite_bool {Δ : CandCtx} {B : CandidateFamily Candidate.bool} {A m n1 n2 : Tm} :
    B.Expansive ->
    (∀ σ, CandSubst Δ σ -> SN Step A.[up σ]) ->
    SemTm Δ m Candidate.bool ->
    (∀ σ, (hσ : CandSubst Δ σ) -> (B.fiber .tt).mem n1.[σ]) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> (B.fiber .ff).mem n2.[σ]) ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      (B.fiber m.[σ]).mem (.ite A m n1 n2).[σ] := by
  intro hB hA hm hn1 hn2 σ hσ
  asimp
  exact Candidate.bool_ite hB (hA σ hσ) (hm σ hσ) (hn1 σ hσ) (hn2 σ hσ)

lemma ite_bool_cases {Δ : CandCtx} {T F : Candidate} {A m n1 n2 : Tm} :
    Candidate.Expansive T ->
    Candidate.Expansive F ->
    (∀ σ, CandSubst Δ σ -> SN Step A.[up σ]) ->
    SemTm Δ m Candidate.bool ->
    SemTm Δ n1 T ->
    SemTm Δ n2 F ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      ((CandidateFamily.boolCases T F).fiber m.[σ]).mem (.ite A m n1 n2).[σ] := by
  intro hT hF hA hm hn1 hn2 σ hσ
  asimp
  exact Candidate.bool_ite_cases hT hF (hA σ hσ) (hm σ hσ) (hn1 σ hσ) (hn2 σ hσ)

lemma rw {Δ : CandCtx} {D : Candidate} {A m n : Tm} :
    Candidate.Expansive D ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ A',
      A.[upn 2 σ] ~> A' -> D.mem (.rw A' m.[σ] n.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[σ] ~> m' -> D.mem (.rw A.[upn 2 σ] m' n.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n',
      n.[σ] ~> n' -> D.mem (.rw A.[upn 2 σ] m.[σ] n')) ->
    SemTm Δ m D ->
    SemTm Δ (.rw A m n) D := by
  intro hD hA hm hn hrfl σ hσ
  asimp
  apply Candidate.rw hD
  . intro A' stA
    exact hA σ hσ A' stA
  . intro m' stM
    exact hm σ hσ m' stM
  . intro n' stN
    exact hn σ hσ n' stN
  . exact hrfl σ hσ

lemma rw_dep {Δ : CandCtx} {I : Candidate} {a b : Tm}
    {D : CandidateFamily (Candidate.idn I a b)} {A m n : Tm} :
    D.Expansive ->
    SemTm Δ n (Candidate.idn I a b) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ A',
      A.[upn 2 σ] ~> A' -> (D.fiber n.[σ]).mem (.rw A' m.[σ] n.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[σ] ~> m' -> (D.fiber n.[σ]).mem (.rw A.[upn 2 σ] m' n.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n',
      n.[σ] ~> n' -> (D.fiber n').mem (.rw A.[upn 2 σ] m.[σ] n')) ->
    (∀ σ, CandSubst Δ σ -> ∀ c, (D.fiber (.rfl c)).mem m.[σ]) ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      (D.fiber n.[σ]).mem (.rw A m n).[σ] := by
  intro hD hn hA hm hnStep hrfl σ hσ
  asimp
  apply Candidate.rw_dep hD (hn σ hσ)
  . intro A' stA
    exact hA σ hσ A' stA
  . intro m' stM
    exact hm σ hσ m' stM
  . intro n' stN
    exact hnStep σ hσ n' stN
  . intro c
    exact hrfl σ hσ c

lemma rw_idCases {Δ : CandCtx} {I : Candidate} {a b : Tm}
    {R : Tm -> Candidate} {A m n : Tm} :
    (∀ c, Candidate.Expansive (R c)) ->
    SemTm Δ n (Candidate.idn I a b) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ A',
      A.[upn 2 σ] ~> A' ->
        ((CandidateFamily.idCases I a b R).fiber n.[σ]).mem (.rw A' m.[σ] n.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[σ] ~> m' ->
        ((CandidateFamily.idCases I a b R).fiber n.[σ]).mem (.rw A.[upn 2 σ] m' n.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ n',
      n.[σ] ~> n' ->
        ((CandidateFamily.idCases I a b R).fiber n').mem (.rw A.[upn 2 σ] m.[σ] n')) ->
    (∀ σ, CandSubst Δ σ -> ∀ c,
      ((CandidateFamily.idCases I a b R).fiber (.rfl c)).mem m.[σ]) ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      ((CandidateFamily.idCases I a b R).fiber n.[σ]).mem (.rw A m n).[σ] := by
  intro hR hn hA hm hnStep hrfl
  apply rw_dep
  . exact CandidateFamily.idCases_expansive hR
  . exact hn
  . exact hA
  . exact hm
  . exact hnStep
  . exact hrfl

lemma exf {Δ : CandCtx} {D : Candidate} {A m : Tm} :
    Candidate.Expansive D ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ A',
      A.[up σ] ~> A' -> D.mem (.exf A' m.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[σ] ~> m' -> D.mem (.exf A.[up σ] m')) ->
    SemTm Δ (.exf A m) D := by
  intro hD hA hm σ hσ
  asimp
  apply Candidate.exf hD
  . intro A' stA
    exact hA σ hσ A' stA
  . intro m' stM
    exact hm σ hσ m' stM

lemma exf_dep {Δ : CandCtx} {B : CandidateFamily Candidate.bot} {A m : Tm} :
    B.Expansive ->
    SemTm Δ m Candidate.bot ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ A',
      A.[up σ] ~> A' -> (B.fiber m.[σ]).mem (.exf A' m.[σ])) ->
    (∀ σ, (hσ : CandSubst Δ σ) -> ∀ m',
      m.[σ] ~> m' -> (B.fiber m').mem (.exf A.[up σ] m')) ->
    ∀ σ, (hσ : CandSubst Δ σ) ->
      (B.fiber m.[σ]).mem (.exf A m).[σ] := by
  intro hB hm hA hmStep σ hσ
  asimp
  apply Candidate.exf_dep hB (hm σ hσ)
  . intro A' stA
    exact hA σ hσ A' stA
  . intro m' stM
    exact hmStep σ hσ m' stM

end SemTm
