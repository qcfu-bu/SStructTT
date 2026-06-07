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

lemma Neutral.shift {m : Tm} (neu : Neutral m) (i : Nat) :
    Neutral m.[shift i] := by
  induction neu generalizing i with
  | var x =>
    asimp
    exact Neutral.var (x + i)
  | app m n _ ih =>
    asimp
    exact Neutral.app _ _ (ih i)
  | prj A m n _ ih =>
    asimp
    exact Neutral.prj _ _ _ (ih i)
  | ite A m n1 n2 _ ih =>
    asimp
    exact Neutral.ite _ _ _ _ (ih i)
  | rw A m n _ ih =>
    asimp
    exact Neutral.rw _ _ _ (ih i)
  | exf A m _ ih =>
    asimp
    exact Neutral.exf _ _ (ih i)

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

def downN (k : Nat) (x : Var) : Tm :=
  if x < k then .var x else .var (x - k)

lemma downN_shift (k x : Nat) : downN k (x + k) = .var x := by
  unfold downN
  split
  · rename_i h
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_left k x)) h)
  · congr
    exact Nat.add_sub_cancel x k

lemma shift_downN (k : Nat) : (shift k : Var -> Tm) !> downN k = ids := by
  funext x
  asimp [downN_shift]

lemma subst_shiftN_downN (m : Tm) (k : Nat) : m.[shift k].[downN k] = m := by
  rw [Tm.subst_comp, shift_downN, Tm.subst_id]

lemma subst_shift_inj {m n : Tm} {k : Nat} :
    m.[shift k] = n.[shift k] -> m = n := by
  intro h
  have h' := congrArg (fun t : Tm => t.[downN k]) h
  simpa [subst_shiftN_downN] using h'

lemma shift_down1 : (shift 1 : Var -> Tm) !> down1 = ids := by
  funext x
  asimp [down1]

lemma subst_shift1_down1 (m : Tm) : m.[shift 1].[down1] = m := by
  rw [Tm.subst_comp, shift_down1, Tm.subst_id]

lemma subst_shift1_inj {m n : Tm} :
    m.[shift 1] = n.[shift 1] -> m = n := by
  intro h
  have h' := congrArg (fun t : Tm => t.[down1]) h
  simpa [subst_shift1_down1] using h'

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

lemma subst_shiftSubst (m : Tm) (σ : Var -> Tm) (i : Nat) :
    m.[σ].[shift i] = m.[shiftSubst σ i] := by
  rw [Tm.subst_comp]
  rfl

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

lemma SRed.shiftSubst {σ τ : Var -> Tm} :
    SRed σ τ -> ∀ i, SRed (shiftSubst σ i) (shiftSubst τ i) := by
  intro h i x
  exact Red.subst (shift i) (h x)

lemma SConv.shiftSubst {σ τ : Var -> Tm} :
    SConv σ τ -> ∀ i, SConv (shiftSubst σ i) (shiftSubst τ i) := by
  intro h i x
  exact Conv.subst (shift i) (h x)

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

lemma sn_pi_left {A B : Tm} :
    SN Step (.pi A B) -> SN Step A := by
  intro h
  exact SN.preimage (e := Step) (x := A) (f := fun X => Tm.pi X B)
    (by
      intro X Y st
      exact Step.pi_A B st)
    h

lemma sn_pi_right {A B : Tm} :
    SN Step (.pi A B) -> SN Step B := by
  intro h
  exact SN.preimage (e := Step) (x := B) (f := fun Y => Tm.pi A Y)
    (by
      intro X Y st
      exact Step.pi_B A st)
    h

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

lemma sn_sig_left {A B : Tm} :
    SN Step (.sig A B) -> SN Step A := by
  intro h
  exact SN.preimage (e := Step) (x := A) (f := fun X => Tm.sig X B)
    (by
      intro X Y st
      exact Step.sig_A B st)
    h

lemma sn_sig_right {A B : Tm} :
    SN Step (.sig A B) -> SN Step B := by
  intro h
  exact SN.preimage (e := Step) (x := B) (f := fun Y => Tm.sig A Y)
    (by
      intro X Y st
      exact Step.sig_B A st)
    h

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

lemma sn_idn_type {A m n : Tm} :
    SN Step (.idn A m n) -> SN Step A := by
  intro h
  exact SN.preimage (e := Step) (x := A) (f := fun X => Tm.idn X m n)
    (by
      intro X Y st
      exact Step.idn_A m n st)
    h

lemma sn_idn_left {A m n : Tm} :
    SN Step (.idn A m n) -> SN Step m := by
  intro h
  exact SN.preimage (e := Step) (x := m) (f := fun M => Tm.idn A M n)
    (by
      intro X Y st
      exact Step.idn_M A n st)
    h

lemma sn_idn_right {A m n : Tm} :
    SN Step (.idn A m n) -> SN Step n := by
  intro h
  exact SN.preimage (e := Step) (x := n) (f := fun N => Tm.idn A m N)
    (by
      intro X Y st
      exact Step.idn_N A m st)
    h

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

def Expansive {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A) : Prop :=
  ∀ σ, (hσ : Δ.valid σ) -> Candidate.Expansive (I.cand σ)

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

def convType {Δ : DCandCtx} {A B : Tm} (I : TypeInterp Δ A)
    (hB : ∀ σ, Δ.valid σ -> SN Step B.[σ]) : TypeInterp Δ B where
  cand := I.cand
  type_sn := hB
  stable_red := I.stable_red
  stable_red_fwd := I.stable_red_fwd
  stable_conv := I.stable_conv

lemma convType_weakens {Δ : DCandCtx} {A B : Tm} (I : TypeInterp Δ A)
    (hB : ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    I.Weakens -> (I.convType hB).Weakens := by
  intro hI
  exact hI

lemma convType_expansive {Δ : DCandCtx} {A B : Tm} (I : TypeInterp Δ A)
    (hB : ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    I.Expansive -> (I.convType hB).Expansive := by
  intro hI
  exact hI

lemma convType_semTm {Δ : DCandCtx} {A B m : Tm} (I : TypeInterp Δ A)
    (hB : ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    I.SemTm m -> (I.convType hB).SemTm m := by
  intro hm
  exact hm

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

lemma const_expansive {Δ : DCandCtx} {A : Tm} {C : Candidate}
    {hA : ∀ σ, Δ.valid σ -> SN Step A.[σ]} :
    Candidate.Expansive C -> (TypeInterp.const Δ A C hA).Expansive := by
  intro hC σ hσ
  exact hC

lemma univ_weakens (Δ : DCandCtx) (i : Nat) :
    (TypeInterp.univ Δ i).Weakens :=
  TypeInterp.const_weakens Candidate.univ_weakens

lemma univ_expansive (Δ : DCandCtx) (i : Nat) :
    (TypeInterp.univ Δ i).Expansive :=
  TypeInterp.const_expansive Candidate.univ_expansive

lemma bool_weakens (Δ : DCandCtx) :
    (TypeInterp.bool Δ).Weakens :=
  TypeInterp.const_weakens Candidate.bool_weakens

lemma bool_expansive (Δ : DCandCtx) :
    (TypeInterp.bool Δ).Expansive :=
  TypeInterp.const_expansive Candidate.bool_expansive

lemma bot_weakens (Δ : DCandCtx) :
    (TypeInterp.bot Δ).Weakens :=
  TypeInterp.const_weakens Candidate.bot_weakens

lemma bot_expansive (Δ : DCandCtx) :
    (TypeInterp.bot Δ).Expansive :=
  TypeInterp.const_expansive Candidate.bot_expansive

lemma idn_weakens {Δ : DCandCtx} {A m n : Tm} {I : TypeInterp Δ A}
    {hm : I.SemTm m} {hn : I.SemTm n} :
    (TypeInterp.idn I hm hn).Weakens :=
  TypeInterp.const_weakens Candidate.idn_weakens

lemma idn_expansive {Δ : DCandCtx} {A m n : Tm} {I : TypeInterp Δ A}
    {hm : I.SemTm m} {hn : I.SemTm n} :
    (TypeInterp.idn I hm hn).Expansive :=
  TypeInterp.const_expansive Candidate.idn_expansive

lemma semTt {Δ : DCandCtx} : (TypeInterp.bool Δ).SemTm .tt := by
  intro σ hσ
  asimp
  exact sn_tt

lemma semFf {Δ : DCandCtx} : (TypeInterp.bool Δ).SemTm .ff := by
  intro σ hσ
  asimp
  exact sn_ff

lemma semTy {Δ : DCandCtx} (i j : Nat) :
    (TypeInterp.univ Δ j).SemTm (.ty i) := by
  intro σ hσ
  asimp
  exact Candidate.ty

lemma semBoolType {Δ : DCandCtx} (i : Nat) :
    (TypeInterp.univ Δ i).SemTm .bool := by
  intro σ hσ
  asimp
  exact Candidate.bool_type

lemma semBotType {Δ : DCandCtx} (i : Nat) :
    (TypeInterp.univ Δ i).SemTm .bot := by
  intro σ hσ
  asimp
  exact Candidate.bot_type

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

def weakenCtx {Δ : DCandCtx} {A B : Tm}
    (I : TypeInterp Δ A) (J : TypeInterp Δ B) :
    TypeInterp (DCandCtx.extend J) A.[shift 1] where
  cand σ := I.cand (fun x => σ (x + 1))
  type_sn := by
    intro σ hσ
    asimp
    exact I.type_sn (fun x => σ (x + 1)) hσ.1
  stable_red := by
    intro σ τ m hσ hred hm
    exact I.stable_red hσ.1 (fun x => hred (x + 1)) hm
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    exact I.stable_red_fwd hσ.1 (fun x => hred (x + 1)) hm
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    exact I.stable_conv hσ.1 hτ.1 (fun x => hconv (x + 1)) hm

lemma weakenCtx_weakens {Δ : DCandCtx} {A B : Tm}
    {I : TypeInterp Δ A} {J : TypeInterp Δ B} :
    I.Weakens -> (TypeInterp.weakenCtx I J).Weakens := by
  intro hI σ m hσ hm
  have htail : (fun x => (σ (x + 1)).[shift 1]) =
      (fun x => (fun y => (σ y).[shift 1]) (x + 1)) := by
    rfl
  change (I.cand (fun x => ((fun y => (σ y).[shift 1]) (x + 1)))).mem m.[shift 1]
  rw [← htail]
  exact hI hσ.1 hm

lemma semVarZero {Δ : DCandCtx} {A : Tm} (I : TypeInterp Δ A) :
    (TypeInterp.weakenCtx I I).SemTm (.var 0) := by
  intro σ hσ
  asimp
  exact hσ.2

lemma semVarSucc {Δ : DCandCtx} {A B : Tm}
    (I : TypeInterp Δ A) (J : TypeInterp Δ B) {x : Var} :
    I.SemTm (.var x) ->
    (TypeInterp.weakenCtx I J).SemTm (.var (x + 1)) := by
  intro hx σ hσ
  asimp
  exact hx (fun y => σ (y + 1)) hσ.1

lemma semTm_weakenCtx {Δ : DCandCtx} {A B m : Tm}
    (I : TypeInterp Δ A) (J : TypeInterp Δ B) :
    I.SemTm m -> (TypeInterp.weakenCtx I J).SemTm m.[shift 1] := by
  intro hm σ hσ
  asimp
  exact hm (fun y => σ (y + 1)) hσ.1

def idProof {Δ : DCandCtx} {B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) :
    TypeInterp (DCandCtx.extend IB) (.idn B.[shift 1] a.[shift 1] (.var 0)) :=
  TypeInterp.idn (TypeInterp.weakenCtx IB IB)
    (TypeInterp.semTm_weakenCtx IB IB ha)
    (TypeInterp.semVarZero IB)

lemma idProof_weakens {Δ : DCandCtx} {B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) :
    (TypeInterp.idProof IB ha).Weakens :=
  TypeInterp.idn_weakens

lemma idProof_expansive {Δ : DCandCtx} {B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) :
    (TypeInterp.idProof IB ha).Expansive :=
  TypeInterp.idn_expansive

def idBranchSubst (a : Tm) (σ : Var -> Tm) : Var -> Tm :=
  .rfl a.[σ] .: a.[σ] .: σ

lemma idBranchSubst_valid {Δ : DCandCtx} {B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a)
    {σ : Var -> Tm} :
    Δ.valid σ ->
    (DCandCtx.extend (TypeInterp.idProof IB ha)).valid
      (TypeInterp.idBranchSubst a σ) := by
  intro hσ
  have haσ : (IB.cand σ).mem a.[σ] := ha σ hσ
  constructor
  · exact DCandCtx.extend_cons hσ haσ
  · change ((TypeInterp.idProof IB ha).cand (a.[σ] .: σ)).mem (.rfl a.[σ])
    exact sn_rfl ((IB.cand σ).sn haσ)

lemma idBranchSubst_red {a : Tm} {σ τ : Var -> Tm} :
    SRed σ τ ->
    SRed (TypeInterp.idBranchSubst a σ) (TypeInterp.idBranchSubst a τ) := by
  intro hred x
  cases x with
  | zero =>
    asimp [TypeInterp.idBranchSubst]
    exact Red.rfl (Red.compat hred)
  | succ x =>
    cases x with
    | zero =>
      asimp [TypeInterp.idBranchSubst]
      exact Red.compat hred
    | succ x =>
      asimp [TypeInterp.idBranchSubst]
      exact hred x

lemma idBranchSubst_conv {a : Tm} {σ τ : Var -> Tm} :
    SConv σ τ ->
    SConv (TypeInterp.idBranchSubst a σ) (TypeInterp.idBranchSubst a τ) := by
  intro hconv x
  cases x with
  | zero =>
    asimp [TypeInterp.idBranchSubst]
    exact Conv.rfl (Conv.compat a hconv)
  | succ x =>
    cases x with
    | zero =>
      asimp [TypeInterp.idBranchSubst]
      exact Conv.compat a hconv
    | succ x =>
      asimp [TypeInterp.idBranchSubst]
      exact hconv x

def idBranch {Δ : DCandCtx} {A B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A) :
    TypeInterp Δ A.[.rfl a,a/] where
  cand σ := IA.cand (TypeInterp.idBranchSubst a σ)
  type_sn := by
    intro σ hσ
    have hvalid := TypeInterp.idBranchSubst_valid IB ha hσ
    have h := IA.type_sn (TypeInterp.idBranchSubst a σ) hvalid
    rw [Tm.subst_comp]
    have hsubst : (.rfl a .: a .: ids) !> σ =
        TypeInterp.idBranchSubst a σ := by
      funext x
      cases x with
      | zero =>
        asimp [TypeInterp.idBranchSubst]
      | succ x =>
        cases x with
        | zero =>
          asimp [TypeInterp.idBranchSubst]
        | succ x =>
          asimp [TypeInterp.idBranchSubst]
    rw [hsubst]
    exact h
  stable_red := by
    intro σ τ m hσ hred hm
    exact IA.stable_red
      (TypeInterp.idBranchSubst_valid IB ha hσ)
      (TypeInterp.idBranchSubst_red hred) hm
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    exact IA.stable_red_fwd
      (TypeInterp.idBranchSubst_valid IB ha hσ)
      (TypeInterp.idBranchSubst_red hred) hm
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    exact IA.stable_conv
      (TypeInterp.idBranchSubst_valid IB ha hσ)
      (TypeInterp.idBranchSubst_valid IB ha hτ)
      (TypeInterp.idBranchSubst_conv hconv) hm

lemma idBranch_weakens {Δ : DCandCtx} {A B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A) :
    IA.Weakens -> (TypeInterp.idBranch IB ha IA).Weakens := by
  intro hIA σ m hσ hm
  have hvalid := TypeInterp.idBranchSubst_valid IB ha hσ
  have h := hIA hvalid hm
  have hsubst :
      (fun x => (TypeInterp.idBranchSubst a σ x).[shift 1]) =
        TypeInterp.idBranchSubst a (fun x => (σ x).[shift 1]) := by
    funext x
    cases x with
    | zero =>
      asimp [TypeInterp.idBranchSubst]
      apply congrArg (fun ρ : Var -> Tm => a.[ρ])
      funext y
      rfl
    | succ x =>
      cases x with
      | zero =>
        asimp [TypeInterp.idBranchSubst]
        apply congrArg (fun ρ : Var -> Tm => a.[ρ])
        funext y
        rfl
      | succ x =>
        asimp [TypeInterp.idBranchSubst]
  change (IA.cand
    (TypeInterp.idBranchSubst a (fun x => (σ x).[shift 1]))).mem m.[shift 1]
  simpa [hsubst] using h

lemma idBranch_expansive {Δ : DCandCtx} {A B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A) :
    IA.Expansive -> (TypeInterp.idBranch IB ha IA).Expansive := by
  intro hIA σ hσ
  exact hIA (TypeInterp.idBranchSubst a σ)
    (TypeInterp.idBranchSubst_valid IB ha hσ)

def idTargetSubst (b n : Tm) (σ : Var -> Tm) : Var -> Tm :=
  n.[σ] .: b.[σ] .: σ

lemma idTargetSubst_valid {Δ : DCandCtx} {B a b n : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) (hb : IB.SemTm b)
    (hn : (TypeInterp.idn IB ha hb).SemTm n)
    {σ : Var -> Tm} :
    Δ.valid σ ->
    (DCandCtx.extend (TypeInterp.idProof IB ha)).valid
      (TypeInterp.idTargetSubst b n σ) := by
  intro hσ
  have hbσ : (IB.cand σ).mem b.[σ] := hb σ hσ
  constructor
  · exact DCandCtx.extend_cons hσ hbσ
  · change ((TypeInterp.idProof IB ha).cand (b.[σ] .: σ)).mem n.[σ]
    exact hn σ hσ

lemma idTargetSubst_red {b n : Tm} {σ τ : Var -> Tm} :
    SRed σ τ ->
    SRed (TypeInterp.idTargetSubst b n σ) (TypeInterp.idTargetSubst b n τ) := by
  intro hred x
  cases x with
  | zero =>
    asimp [TypeInterp.idTargetSubst]
    exact Red.compat hred
  | succ x =>
    cases x with
    | zero =>
      asimp [TypeInterp.idTargetSubst]
      exact Red.compat hred
    | succ x =>
      asimp [TypeInterp.idTargetSubst]
      exact hred x

lemma idTargetSubst_conv {b n : Tm} {σ τ : Var -> Tm} :
    SConv σ τ ->
    SConv (TypeInterp.idTargetSubst b n σ) (TypeInterp.idTargetSubst b n τ) := by
  intro hconv x
  cases x with
  | zero =>
    asimp [TypeInterp.idTargetSubst]
    exact Conv.compat n hconv
  | succ x =>
    cases x with
    | zero =>
      asimp [TypeInterp.idTargetSubst]
      exact Conv.compat b hconv
    | succ x =>
      asimp [TypeInterp.idTargetSubst]
      exact hconv x

def idTarget {Δ : DCandCtx} {A B a b n : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) (hb : IB.SemTm b)
    (hn : (TypeInterp.idn IB ha hb).SemTm n)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A) :
    TypeInterp Δ A.[n,b/] where
  cand σ := IA.cand (TypeInterp.idTargetSubst b n σ)
  type_sn := by
    intro σ hσ
    have hvalid := TypeInterp.idTargetSubst_valid IB ha hb hn hσ
    have h := IA.type_sn (TypeInterp.idTargetSubst b n σ) hvalid
    rw [Tm.subst_comp]
    have hsubst : (n .: b .: ids) !> σ =
        TypeInterp.idTargetSubst b n σ := by
      funext x
      cases x with
      | zero =>
        asimp [TypeInterp.idTargetSubst]
      | succ x =>
        cases x with
        | zero =>
          asimp [TypeInterp.idTargetSubst]
        | succ x =>
          asimp [TypeInterp.idTargetSubst]
    rw [hsubst]
    exact h
  stable_red := by
    intro σ τ m hσ hred hm
    exact IA.stable_red
      (TypeInterp.idTargetSubst_valid IB ha hb hn hσ)
      (TypeInterp.idTargetSubst_red hred) hm
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    exact IA.stable_red_fwd
      (TypeInterp.idTargetSubst_valid IB ha hb hn hσ)
      (TypeInterp.idTargetSubst_red hred) hm
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    exact IA.stable_conv
      (TypeInterp.idTargetSubst_valid IB ha hb hn hσ)
      (TypeInterp.idTargetSubst_valid IB ha hb hn hτ)
      (TypeInterp.idTargetSubst_conv hconv) hm

lemma idTarget_weakens {Δ : DCandCtx} {A B a b n : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) (hb : IB.SemTm b)
    (hn : (TypeInterp.idn IB ha hb).SemTm n)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A) :
    IA.Weakens -> (TypeInterp.idTarget IB ha hb hn IA).Weakens := by
  intro hIA σ m hσ hm
  have hvalid := TypeInterp.idTargetSubst_valid IB ha hb hn hσ
  have h := hIA hvalid hm
  have hsubst :
      (fun x => (TypeInterp.idTargetSubst b n σ x).[shift 1]) =
        TypeInterp.idTargetSubst b n (fun x => (σ x).[shift 1]) := by
    funext x
    cases x with
    | zero =>
      asimp [TypeInterp.idTargetSubst]
      apply congrArg (fun ρ : Var -> Tm => n.[ρ])
      funext y
      rfl
    | succ x =>
      cases x with
      | zero =>
        asimp [TypeInterp.idTargetSubst]
        apply congrArg (fun ρ : Var -> Tm => b.[ρ])
        funext y
        rfl
      | succ x =>
        asimp [TypeInterp.idTargetSubst]
  change (IA.cand
    (TypeInterp.idTargetSubst b n (fun x => (σ x).[shift 1]))).mem m.[shift 1]
  simpa [hsubst] using h

lemma idTarget_expansive {Δ : DCandCtx} {A B a b n : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a) (hb : IB.SemTm b)
    (hn : (TypeInterp.idn IB ha hb).SemTm n)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A) :
    IA.Expansive -> (TypeInterp.idTarget IB ha hb hn IA).Expansive := by
  intro hIA σ hσ
  exact hIA (TypeInterp.idTargetSubst b n σ)
    (TypeInterp.idTargetSubst_valid IB ha hb hn hσ)

def rwFamily {Δ : DCandCtx} {A B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A)
    (σ : Var -> Tm) (hσ : Δ.valid σ)
    (b0 : Tm) (hb0 : (IB.cand σ).mem b0) :
    CandidateFamily (Candidate.idn (IB.cand σ) a.[σ] b0) where
  fiber p := IA.cand (p .: b0 .: σ)
  stable_step := by
    intro p p' m hp st hm
    have htail : (DCandCtx.extend IB).valid (b0 .: σ) :=
      DCandCtx.extend_cons hσ hb0
    have hvalid : (DCandCtx.extend (TypeInterp.idProof IB ha)).valid (p .: b0 .: σ) := by
      exact ⟨htail, hp⟩
    have hred : SRed (p .: b0 .: σ) (p' .: b0 .: σ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact Star.one st
      | succ x =>
        asimp
        exact Star.R
    exact IA.stable_red hvalid hred hm
  stable_step_fwd := by
    intro p p' m hp st hm
    have htail : (DCandCtx.extend IB).valid (b0 .: σ) :=
      DCandCtx.extend_cons hσ hb0
    have hvalid : (DCandCtx.extend (TypeInterp.idProof IB ha)).valid (p .: b0 .: σ) := by
      exact ⟨htail, hp⟩
    have hred : SRed (p .: b0 .: σ) (p' .: b0 .: σ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact Star.one st
      | succ x =>
        asimp
        exact Star.R
    exact IA.stable_red_fwd hvalid hred hm

lemma rwFamily_expansive {Δ : DCandCtx} {A B a : Tm}
    (IB : TypeInterp Δ B) (ha : IB.SemTm a)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A)
    (hIA : IA.Expansive)
    {σ : Var -> Tm} (hσ : Δ.valid σ)
    {b0 : Tm} (hb0 : (IB.cand σ).mem b0) :
    (TypeInterp.rwFamily IB ha IA σ hσ b0 hb0).Expansive := by
  intro p hp
  have htail : (DCandCtx.extend IB).valid (b0 .: σ) :=
    DCandCtx.extend_cons hσ hb0
  change Candidate.Expansive (IA.cand (p .: b0 .: σ))
  exact hIA (p .: b0 .: σ) ⟨htail, hp⟩

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

def subst1 {Δ : DCandCtx} {A B n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hn : IA.SemTm n) : TypeInterp Δ B.[n/] where
  cand σ := IB.cand (n.[σ] .: σ)
  type_sn := by
    intro σ hσ
    asimp
    exact IB.type_sn (n.[σ] .: σ) (DCandCtx.extend_cons hσ (hn σ hσ))
  stable_red := by
    intro σ τ m hσ hred hm
    have hnσ : (IA.cand σ).mem n.[σ] := hn σ hσ
    have hredn : n.[σ] ~>* n.[τ] := Red.compat hred
    have hredext : SRed (n.[σ] .: σ) (n.[τ] .: τ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact hredn
      | succ x =>
        asimp
        exact hred x
    exact IB.stable_red (DCandCtx.extend_cons hσ hnσ) hredext hm
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    have hnσ : (IA.cand σ).mem n.[σ] := hn σ hσ
    have hredn : n.[σ] ~>* n.[τ] := Red.compat hred
    have hredext : SRed (n.[σ] .: σ) (n.[τ] .: τ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact hredn
      | succ x =>
        asimp
        exact hred x
    exact IB.stable_red_fwd (DCandCtx.extend_cons hσ hnσ) hredext hm
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    have hnσ : (IA.cand σ).mem n.[σ] := hn σ hσ
    have hnτ : (IA.cand τ).mem n.[τ] := hn τ hτ
    have hconvn : n.[σ] === n.[τ] := Conv.compat n hconv
    have hconvext : SConv (n.[σ] .: σ) (n.[τ] .: τ) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact hconvn
      | succ x =>
        asimp
        exact hconv x
    exact IB.stable_conv (DCandCtx.extend_cons hσ hnσ)
      (DCandCtx.extend_cons hτ hnτ) hconvext hm

lemma subst1_weakens {Δ : DCandCtx} {A B n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    {hn : IA.SemTm n} :
    IB.Weakens -> (TypeInterp.subst1 IA IB hn).Weakens := by
  intro hIB σ m hσ hm
  have hnσ : (IA.cand σ).mem n.[σ] := hn σ hσ
  have h := hIB (DCandCtx.extend_cons hσ hnσ) hm
  have hsubst :
      (fun x => ((n.[σ] .: σ) x).[shift 1]) =
        (n.[fun x => (σ x).[shift 1]] .: fun x => (σ x).[shift 1]) := by
    funext x
    cases x with
    | zero =>
      asimp
      apply congrArg (fun ρ : Var -> Tm => n.[ρ])
      funext y
      rfl
    | succ x =>
      asimp
  simpa [TypeInterp.subst1, hsubst] using h

lemma subst1_expansive {Δ : DCandCtx} {A B n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    {hn : IA.SemTm n} :
    IB.Expansive -> (TypeInterp.subst1 IA IB hn).Expansive := by
  intro hIB σ hσ
  exact hIB (n.[σ] .: σ) (DCandCtx.extend_cons hσ (hn σ hσ))

def kpiCand {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ))
    (σ : Var -> Tm) (hσ : Δ.valid σ) : Candidate where
  mem f :=
    SN Step f ∧
    ∀ i n, (IA.cand (shiftSubst σ i)).mem n ->
      (IB.cand (n .: shiftSubst σ i)).mem (.app f.[shift i] n)
  sn hf := hf.1
  closed_step := by
    intro f f' hf st
    constructor
    . exact sn_step hf.1 st
    . intro i n hn
      exact (IB.cand (n .: shiftSubst σ i)).closed_step
        (hf.2 i n hn) (Step.app_M n (Step.subst (shift i) st))
  neutral := by
    intro f neu hsn _hred
    constructor
    . exact hsn
    . intro i n hn
      let σi := shiftSubst σ i
      have hσi : Δ.valid σi := DCandCtx.weakens_iter hΔ hσ i
      have app_mem :
          ∀ {g a}, SN Step g -> SN Step a -> Neutral g -> (IA.cand σi).mem a ->
            (IB.cand (a .: σi)).mem (.app g a) := by
        intro g a sng
        induction sng generalizing a with
        | intro stepG ihG =>
          rename_i g0
          intro sna neug ha
          induction sna with
          | intro stepA ihA =>
            rename_i a0
            apply Candidate.expansive_of_steps
              (hIB (a0 .: σi) (DCandCtx.extend_cons hσi ha))
            intro x st
            cases st with
            | app_M a stG =>
              exact ihG stG (SN.intro stepA) (Neutral.step neug stG) ha
            | app_N g stA =>
              rename_i a1
              have ha' : (IA.cand σi).mem a1 :=
                (IA.cand σi).closed_step ha stA
              have hred : SRed (a0 .: σi) (a1 .: σi) := by
                intro x
                cases x with
                | zero =>
                  asimp
                  exact Star.one stA
                | succ x =>
                  asimp
                  exact Star.R
              exact IB.stable_red (DCandCtx.extend_cons hσi ha) hred (ihA stA ha')
            | beta A body a =>
              exact (Neutral.not_lam neug).elim
      exact app_mem (sn_shiftn i hsn) ((IA.cand σi).sn hn) (neu.shift i) hn

noncomputable def kpiCandTotal {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ))
    (σ : Var -> Tm) : Candidate := by
  classical
  exact if hσ : Δ.valid σ then TypeInterp.kpiCand IA IB hΔ hIB σ hσ
    else Candidate.snCandidate

lemma kpiCandTotal_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ))
    {σ : Var -> Tm} (hσ : Δ.valid σ) :
    TypeInterp.kpiCandTotal IA IB hΔ hIB σ =
      TypeInterp.kpiCand IA IB hΔ hIB σ hσ := by
  classical
  simp [TypeInterp.kpiCandTotal, hσ]

noncomputable def kpi {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ)) :
    TypeInterp Δ (.pi A B) where
  cand := TypeInterp.kpiCandTotal IA IB hΔ hIB
  type_sn := by
    intro σ hσ
    asimp
    exact sn_pi (IA.type_sn σ hσ)
      (IB.type_sn (up σ) (DCandCtx.extend_up_valid hΔ hσ))
  stable_red := by
    intro σ τ f hσ hred hf
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hτ] at hf
    rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ]
    dsimp [TypeInterp.kpiCand] at hf ⊢
    constructor
    . exact hf.1
    . intro i n hnσ
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter hΔ hσ i
      have hred_i : SRed (shiftSubst σ i) (shiftSubst τ i) :=
        SRed.shiftSubst hred i
      have hnτ : (IA.cand (shiftSubst τ i)).mem n :=
        IA.stable_red_fwd hσi hred_i hnσ
      have happτ := hf.2 i n hnτ
      exact IB.stable_red (DCandCtx.extend_cons hσi hnσ)
        (SRed.scons_same hred_i) happτ
  stable_red_fwd := by
    intro σ τ f hσ hred hf
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ] at hf
    rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hτ]
    dsimp [TypeInterp.kpiCand] at hf ⊢
    constructor
    . exact hf.1
    . intro i n hnτ
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter hΔ hσ i
      have hred_i : SRed (shiftSubst σ i) (shiftSubst τ i) :=
        SRed.shiftSubst hred i
      have hnσ : (IA.cand (shiftSubst σ i)).mem n :=
        IA.stable_red hσi hred_i hnτ
      have happσ := hf.2 i n hnσ
      exact IB.stable_red_fwd (DCandCtx.extend_cons hσi hnσ)
        (SRed.scons_same hred_i) happσ
  stable_conv := by
    intro σ τ f hσ hτ hconv hf
    rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ] at hf
    rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hτ]
    dsimp [TypeInterp.kpiCand] at hf ⊢
    constructor
    . exact hf.1
    . intro i n hnτ
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter hΔ hσ i
      have hτi : Δ.valid (shiftSubst τ i) :=
        DCandCtx.weakens_iter hΔ hτ i
      have hconv_i : SConv (shiftSubst σ i) (shiftSubst τ i) :=
        SConv.shiftSubst hconv i
      have hnσ : (IA.cand (shiftSubst σ i)).mem n :=
        IA.stable_conv_sym hσi hτi hconv_i hnτ
      have happσ := hf.2 i n hnσ
      exact IB.stable_conv (DCandCtx.extend_cons hσi hnσ)
        (DCandCtx.extend_cons hτi hnτ) (SConv.scons_same hconv_i) happσ

lemma kpi_weakens {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ)) :
    (TypeInterp.kpi IA IB hΔ hIB).Weakens := by
  intro σ f hσ hf
  have hσ1 : Δ.valid (shiftSubst σ 1) := hΔ hσ
  change (TypeInterp.kpiCandTotal IA IB hΔ hIB (shiftSubst σ 1)).mem f.[shift 1]
  rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ1]
  change (TypeInterp.kpiCandTotal IA IB hΔ hIB σ).mem f at hf
  rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ] at hf
  dsimp [TypeInterp.kpiCand] at hf ⊢
  constructor
  . exact sn_shift hf.1
  . intro i n hn
    have hsubst : shiftSubst (shiftSubst σ 1) i = shiftSubst σ (1 + i) :=
      shiftSubst_add σ 1 i
    rw [hsubst] at hn
    have happ := hf.2 (1 + i) n hn
    simpa [hsubst, subst_shift_shift] using happ

def piCand {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) (hσ : Δ.valid σ) : Candidate :=
  Candidate.pi (IA.cand σ) (TypeInterp.family IA IB σ hσ)

def sigCand {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) (hσ : Δ.valid σ) : Candidate :=
  Candidate.sigma (IA.cand σ) (TypeInterp.family IA IB σ hσ)

def ksigCand {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) : Candidate where
  mem p :=
    SN Step p ∧
    ∀ i a b, p.[shift i] ~>* .tup a b ->
      (IA.cand (shiftSubst σ i)).mem a ∧
      (IB.cand (a .: shiftSubst σ i)).mem b
  sn hp := hp.1
  closed_step := by
    intro p p' hp st
    constructor
    . exact sn_step hp.1 st
    . intro i a b rd
      exact hp.2 i a b (Star.ES (Step.subst (shift i) st) rd)
  neutral := by
    intro p neu hsn _hred
    constructor
    . exact hsn
    . intro i a b rd
      exact (Neutral.not_red_tup (neu.shift i) rd).elim

noncomputable def ksigCandTotal {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (σ : Var -> Tm) : Candidate := by
  classical
  exact if _hσ : Δ.valid σ then TypeInterp.ksigCand IA IB σ
    else Candidate.snCandidate

lemma ksigCandTotal_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    {σ : Var -> Tm} (hσ : Δ.valid σ) :
    TypeInterp.ksigCandTotal IA IB σ =
      TypeInterp.ksigCand IA IB σ := by
  classical
  simp [TypeInterp.ksigCandTotal, hσ]

noncomputable def ksig {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) : TypeInterp Δ (.sig A B) where
  cand := TypeInterp.ksigCandTotal IA IB
  type_sn := by
    intro σ hσ
    asimp
    exact sn_sig (IA.type_sn σ hσ)
      (IB.type_sn (up σ) (DCandCtx.extend_up_valid hΔ hσ))
  stable_red := by
    intro σ τ p hσ hred hp
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.ksigCandTotal_valid IA IB hτ] at hp
    rw [TypeInterp.ksigCandTotal_valid IA IB hσ]
    dsimp [TypeInterp.ksigCand] at hp ⊢
    constructor
    . exact hp.1
    . intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter hΔ hσ i
      have hred_i : SRed (shiftSubst σ i) (shiftSubst τ i) :=
        SRed.shiftSubst hred i
      have ⟨haτ, hbτ⟩ := hp.2 i a b rd
      have haσ : (IA.cand (shiftSubst σ i)).mem a :=
        IA.stable_red hσi hred_i haτ
      exact ⟨haσ,
        IB.stable_red (DCandCtx.extend_cons hσi haσ)
          (SRed.scons_same hred_i) hbτ⟩
  stable_red_fwd := by
    intro σ τ p hσ hred hp
    have hτ : Δ.valid τ := Δ.closed_red hσ hred
    rw [TypeInterp.ksigCandTotal_valid IA IB hσ] at hp
    rw [TypeInterp.ksigCandTotal_valid IA IB hτ]
    dsimp [TypeInterp.ksigCand] at hp ⊢
    constructor
    . exact hp.1
    . intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter hΔ hσ i
      have hred_i : SRed (shiftSubst σ i) (shiftSubst τ i) :=
        SRed.shiftSubst hred i
      have ⟨haσ, hbσ⟩ := hp.2 i a b rd
      have haτ : (IA.cand (shiftSubst τ i)).mem a :=
        IA.stable_red_fwd hσi hred_i haσ
      exact ⟨haτ,
        IB.stable_red_fwd (DCandCtx.extend_cons hσi haσ)
          (SRed.scons_same hred_i) hbσ⟩
  stable_conv := by
    intro σ τ p hσ hτ hconv hp
    rw [TypeInterp.ksigCandTotal_valid IA IB hσ] at hp
    rw [TypeInterp.ksigCandTotal_valid IA IB hτ]
    dsimp [TypeInterp.ksigCand] at hp ⊢
    constructor
    . exact hp.1
    . intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter hΔ hσ i
      have hτi : Δ.valid (shiftSubst τ i) :=
        DCandCtx.weakens_iter hΔ hτ i
      have hconv_i : SConv (shiftSubst σ i) (shiftSubst τ i) :=
        SConv.shiftSubst hconv i
      have ⟨haσ, hbσ⟩ := hp.2 i a b rd
      have haτ : (IA.cand (shiftSubst τ i)).mem a :=
        IA.stable_conv hσi hτi hconv_i haσ
      exact ⟨haτ,
        IB.stable_conv (DCandCtx.extend_cons hσi haσ)
          (DCandCtx.extend_cons hτi haτ) (SConv.scons_same hconv_i) hbσ⟩

lemma ksig_weakens {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) :
    (TypeInterp.ksig IA IB hΔ).Weakens := by
  intro σ p hσ hp
  have hσ1 : Δ.valid (shiftSubst σ 1) := hΔ hσ
  change (TypeInterp.ksigCandTotal IA IB (shiftSubst σ 1)).mem p.[shift 1]
  rw [TypeInterp.ksigCandTotal_valid IA IB hσ1]
  change (TypeInterp.ksigCandTotal IA IB σ).mem p at hp
  rw [TypeInterp.ksigCandTotal_valid IA IB hσ] at hp
  dsimp [TypeInterp.ksigCand] at hp ⊢
  constructor
  . exact sn_shift hp.1
  . intro i a b rd
    have hsubst : shiftSubst (shiftSubst σ 1) i = shiftSubst σ (1 + i) :=
      shiftSubst_add σ 1 i
    have rd' : p.[shift (1 + i)] ~>* .tup a b := by
      simpa [subst_shift_shift] using rd
    rw [hsubst]
    exact hp.2 (1 + i) a b rd'

lemma ksig_pair_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    {σ : Var -> Tm} :
    (DCandCtx.extend IB).valid σ ->
    ((TypeInterp.ksig IA IB hΔ).cand (fun x => σ (x + 2))).mem
      (.tup (σ 1) (σ 0)) := by
  intro hσ
  let tail : Var -> Tm := fun x => σ (x + 2)
  have htail : Δ.valid tail := hσ.1.1
  have ha : (IA.cand tail).mem (σ 1) := hσ.1.2
  have htail1 : (fun x => σ (x + 1)) = (σ 1 .: tail) := by
    funext x
    cases x with
    | zero =>
      rfl
    | succ x =>
      change σ (x + 1 + 1) = σ (x + 2)
      rw [show x + 1 + 1 = x + 2 by omega]
  have hb : (IB.cand (σ 1 .: tail)).mem (σ 0) := by
    simpa [htail1] using hσ.2
  change (TypeInterp.ksigCandTotal IA IB tail).mem (.tup (σ 1) (σ 0))
  rw [TypeInterp.ksigCandTotal_valid IA IB htail]
  dsimp [TypeInterp.ksigCand]
  constructor
  · exact sn_tup ((IA.cand tail).sn ha) ((IB.cand (σ 1 .: tail)).sn hb)
  · intro i a b rd
    have htail_i : Δ.valid (shiftSubst tail i) :=
      DCandCtx.weakens_iter hΔ htail i
    have ha_i : (IA.cand (shiftSubst tail i)).mem (σ 1).[shift i] :=
      TypeInterp.weakens_iter IA hΔ hIA htail ha i
    have htail_cons : (DCandCtx.extend IA).valid (σ 1 .: tail) :=
      DCandCtx.extend_cons htail ha
    have hb_i :
        (IB.cand ((σ 1).[shift i] .: shiftSubst tail i)).mem (σ 0).[shift i] := by
      have h := TypeInterp.weakens_iter IB
        (DCandCtx.extend_weakens hΔ hIA) hIB htail_cons hb i
      have hsubst :
          shiftSubst (σ 1 .: tail) i =
            ((σ 1).[shift i] .: shiftSubst tail i) := by
        funext x
        cases x with
        | zero =>
          asimp [shiftSubst]
        | succ x =>
          asimp [shiftSubst, tail]
      simpa [hsubst] using h
    have rd_tup : .tup (σ 1).[shift i] (σ 0).[shift i] ~>* .tup a b := by
      simpa using rd
    rcases Red.tup_inv rd_tup with ⟨a0, b0, rda, rdb, e⟩
    cases e
    have ha' : (IA.cand (shiftSubst tail i)).mem a :=
      (IA.cand (shiftSubst tail i)).closed_red ha_i rda
    have hb_closed :
        (IB.cand ((σ 1).[shift i] .: shiftSubst tail i)).mem b :=
      (IB.cand ((σ 1).[shift i] .: shiftSubst tail i)).closed_red hb_i rdb
    have hred : SRed ((σ 1).[shift i] .: shiftSubst tail i) (a .: shiftSubst tail i) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact rda
      | succ x =>
        asimp
        exact Star.R
    exact ⟨ha', IB.stable_red_fwd (DCandCtx.extend_cons htail_i ha_i) hred hb_closed⟩

def sigmaBranchSubst (σ : Var -> Tm) : Var -> Tm :=
  .tup (σ 1) (σ 0) .: fun x => σ (x + 2)

lemma sigmaBranchSubst_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    {σ : Var -> Tm} :
    (DCandCtx.extend IB).valid σ ->
    (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)).valid
      (TypeInterp.sigmaBranchSubst σ) := by
  intro hσ
  constructor
  · exact hσ.1.1
  · change ((TypeInterp.ksig IA IB hΔ).cand (fun x => σ (x + 2))).mem
      (.tup (σ 1) (σ 0))
    exact TypeInterp.ksig_pair_valid IA IB hΔ hIA hIB hσ

lemma sigmaBranchSubst_red {σ τ : Var -> Tm} :
    SRed σ τ ->
    SRed (TypeInterp.sigmaBranchSubst σ) (TypeInterp.sigmaBranchSubst τ) := by
  intro hred x
  cases x with
  | zero =>
    asimp [TypeInterp.sigmaBranchSubst]
    exact Red.tup (hred 1) (hred 0)
  | succ x =>
    asimp [TypeInterp.sigmaBranchSubst]
    exact hred (x + 2)

lemma sigmaBranchSubst_conv {σ τ : Var -> Tm} :
    SConv σ τ ->
    SConv (TypeInterp.sigmaBranchSubst σ) (TypeInterp.sigmaBranchSubst τ) := by
  intro hconv x
  cases x with
  | zero =>
    asimp [TypeInterp.sigmaBranchSubst]
    exact Conv.tup (hconv 1) (hconv 0)
  | succ x =>
    asimp [TypeInterp.sigmaBranchSubst]
    exact hconv (x + 2)

def sigmaBranch {Δ : DCandCtx} {A B C : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    (IC : TypeInterp (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)) C) :
    TypeInterp (DCandCtx.extend IB)
      C.[.tup (.var 1) (.var 0) .: shift 2] where
  cand σ := IC.cand (TypeInterp.sigmaBranchSubst σ)
  type_sn := by
    intro σ hσ
    have hvalid :=
      TypeInterp.sigmaBranchSubst_valid IA IB hΔ hIA hIB hσ
    have h := IC.type_sn (TypeInterp.sigmaBranchSubst σ) hvalid
    rw [Tm.subst_comp]
    have hsubst : (.tup (.var 1) (.var 0) .: shift 2) !> σ =
        TypeInterp.sigmaBranchSubst σ := by
      funext x
      cases x with
      | zero =>
        asimp [TypeInterp.sigmaBranchSubst]
      | succ x =>
        asimp [TypeInterp.sigmaBranchSubst]
    rw [hsubst]
    exact h
  stable_red := by
    intro σ τ m hσ hred hm
    exact IC.stable_red
      (TypeInterp.sigmaBranchSubst_valid IA IB hΔ hIA hIB hσ)
      (TypeInterp.sigmaBranchSubst_red hred) hm
  stable_red_fwd := by
    intro σ τ m hσ hred hm
    exact IC.stable_red_fwd
      (TypeInterp.sigmaBranchSubst_valid IA IB hΔ hIA hIB hσ)
      (TypeInterp.sigmaBranchSubst_red hred) hm
  stable_conv := by
    intro σ τ m hσ hτ hconv hm
    exact IC.stable_conv
      (TypeInterp.sigmaBranchSubst_valid IA IB hΔ hIA hIB hσ)
      (TypeInterp.sigmaBranchSubst_valid IA IB hΔ hIA hIB hτ)
      (TypeInterp.sigmaBranchSubst_conv hconv) hm

lemma sigmaBranch_weakens {Δ : DCandCtx} {A B C : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    (IC : TypeInterp (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)) C) :
    IC.Weakens ->
    (TypeInterp.sigmaBranch IA IB hΔ hIA hIB IC).Weakens := by
  intro hIC σ m hσ hm
  have hvalid :=
    TypeInterp.sigmaBranchSubst_valid IA IB hΔ hIA hIB hσ
  have h := hIC hvalid hm
  have hsubst :
      (fun x => (TypeInterp.sigmaBranchSubst σ x).[shift 1]) =
        TypeInterp.sigmaBranchSubst (fun x => (σ x).[shift 1]) := by
    funext x
    cases x with
    | zero =>
      asimp [TypeInterp.sigmaBranchSubst]
    | succ x =>
      asimp [TypeInterp.sigmaBranchSubst]
  change (IC.cand
    (TypeInterp.sigmaBranchSubst (fun x => (σ x).[shift 1]))).mem m.[shift 1]
  simpa [hsubst] using h

lemma sigmaBranch_sem_pair {Δ : DCandCtx} {A B C n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    (IC : TypeInterp (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)) C) :
    (TypeInterp.sigmaBranch IA IB hΔ hIA hIB IC).SemTm n ->
    ∀ σ, (hσ : Δ.valid σ) -> ∀ a, (ha : (IA.cand σ).mem a) ->
      ∀ b, (hb : (IB.cand (a .: σ)).mem b) ->
        (IC.cand (.tup a b .: σ)).mem n.[b .: a .: σ] := by
  intro hn σ hσ a ha b hb
  have hσab : (DCandCtx.extend IB).valid (b .: a .: σ) :=
    DCandCtx.extend_cons (DCandCtx.extend_cons hσ ha) hb
  have h := hn (b .: a .: σ) hσab
  change (IC.cand (TypeInterp.sigmaBranchSubst (b .: a .: σ))).mem
    n.[b .: a .: σ] at h
  simpa [TypeInterp.sigmaBranchSubst] using h

lemma extend_upn2_valid {Δ : DCandCtx} {A B : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens)
    {σ : Var -> Tm} :
    Δ.valid σ -> (DCandCtx.extend IB).valid (upn 2 σ) := by
  intro hσ
  have hσA : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) hΔ hσ
  have hσAB : (DCandCtx.extend IB).valid (up (up σ)) :=
    DCandCtx.extend_up_valid (I := IB) (DCandCtx.extend_weakens hΔ hIA) hσA
  have hup : up (up σ) = upn 2 σ := by
    asimp
  rwa [← hup]

lemma sigmaBranch_sn_upn2 {Δ : DCandCtx} {A B C n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    (IC : TypeInterp (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)) C) :
    (TypeInterp.sigmaBranch IA IB hΔ hIA hIB IC).SemTm n ->
    ∀ σ, Δ.valid σ -> SN Step n.[upn 2 σ] := by
  intro hn σ hσ
  let I := TypeInterp.sigmaBranch IA IB hΔ hIA hIB IC
  have hvalid : (DCandCtx.extend IB).valid (upn 2 σ) :=
    TypeInterp.extend_upn2_valid IA IB hΔ hIA hσ
  exact (I.cand (upn 2 σ)).sn (hn (upn 2 σ) hvalid)

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

lemma semLamKPiInterp {Δ : DCandCtx} {A B T m : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ)) :
    (∀ σ, Δ.valid σ -> SN Step T.[σ]) ->
    (∀ σ, Δ.valid σ -> SN Step m.[up σ]) ->
    TypeInterp.SemBody IA IB m ->
    (TypeInterp.kpi IA IB hΔ hIB).SemTm (.lam T m) := by
  intro hT hm hbody σ hσ
  change (TypeInterp.kpiCandTotal IA IB hΔ hIB σ).mem (.lam T m).[σ]
  rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ]
  dsimp [TypeInterp.kpiCand]
  constructor
  . asimp
    exact sn_lam (hT σ hσ) (hm σ hσ)
  . intro i n hn
    have hσi : Δ.valid (shiftSubst σ i) :=
      DCandCtx.weakens_iter hΔ hσ i
    have hpi := TypeInterp.semLamPi IA IB hT hm hIB hbody (shiftSubst σ i) hσi
    have happ := Candidate.pi_app hpi hn
    simpa [subst_shiftSubst] using happ

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

lemma semAppKPiInterp {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ)) :
    (TypeInterp.kpi IA IB hΔ hIB).SemTm m ->
    IA.SemTm n ->
    ∀ σ, (hσ : Δ.valid σ) ->
      (IB.cand (n.[σ] .: σ)).mem (.app m n).[σ] := by
  intro hm hn σ hσ
  have h := hm σ hσ
  change (TypeInterp.kpiCandTotal IA IB hΔ hIB σ).mem m.[σ] at h
  rw [TypeInterp.kpiCandTotal_valid IA IB hΔ hIB hσ] at h
  dsimp [TypeInterp.kpiCand] at h
  have hn0 : (IA.cand (shiftSubst σ 0)).mem n.[σ] := by
    simpa [shiftSubst_zero] using hn σ hσ
  have happ := h.2 0 n.[σ] hn0
  rw [shiftSubst_zero σ] at happ
  simpa [SubstLemmas.shift0, Tm.subst_id] using happ

lemma semAppKPiSubst1 {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (hIB : ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) -> Candidate.Expansive (IB.cand σ))
    (hm : (TypeInterp.kpi IA IB hΔ hIB).SemTm m)
    (hn : IA.SemTm n) :
    (TypeInterp.subst1 IA IB hn).SemTm (.app m n) := by
  intro σ hσ
  exact TypeInterp.semAppKPiInterp IA IB hΔ hIB hm hn σ hσ

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

lemma semTupKSigmaInterp {Δ : DCandCtx} {A B m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) :
    IA.SemTm m ->
    (∀ σ, (hσ : Δ.valid σ) -> (IB.cand (m.[σ] .: σ)).mem n.[σ]) ->
    (TypeInterp.ksig IA IB hΔ).SemTm (.tup m n) := by
  intro hm hn σ hσ
  change (TypeInterp.ksigCandTotal IA IB σ).mem (.tup m n).[σ]
  rw [TypeInterp.ksigCandTotal_valid IA IB hσ]
  dsimp [TypeInterp.ksigCand]
  constructor
  . asimp
    exact sn_tup ((IA.cand σ).sn (hm σ hσ))
      ((IB.cand (m.[σ] .: σ)).sn (hn σ hσ))
  . intro i a b rd
    let σi := shiftSubst σ i
    have hσi : Δ.valid σi := DCandCtx.weakens_iter hΔ hσ i
    have hm_i : (IA.cand σi).mem m.[σi] := hm σi hσi
    have hn_i : (IB.cand (m.[σi] .: σi)).mem n.[σi] := hn σi hσi
    have rd' : (.tup m n).[σi] ~>* .tup a b := by
      simpa [subst_shiftSubst] using rd
    have rd_tup : .tup m.[σi] n.[σi] ~>* .tup a b := by
      simpa using rd'
    rcases Red.tup_inv rd_tup with ⟨a0, b0, rdm, rdn, e⟩
    cases e
    have ha : (IA.cand σi).mem a :=
      (IA.cand σi).closed_red hm_i rdm
    have hb : (IB.cand (m.[σi] .: σi)).mem b :=
      (IB.cand (m.[σi] .: σi)).closed_red hn_i rdn
    have hred : SRed (m.[σi] .: σi) (a .: σi) := by
      intro x
      cases x with
      | zero =>
        asimp
        exact rdm
      | succ x =>
        asimp
        exact Star.R
    exact ⟨ha, IB.stable_red_fwd (DCandCtx.extend_cons hσi hm_i) hred hb⟩

lemma semIteBoolSubst1 {Δ : DCandCtx} {A m n1 n2 : Tm}
    (IB : TypeInterp (DCandCtx.extend (TypeInterp.bool Δ)) A)
    (hΔ : Δ.Weakens)
    (hIB : IB.Expansive)
    (hm : (TypeInterp.bool Δ).SemTm m)
    (hn1 : (TypeInterp.subst1 (TypeInterp.bool Δ) IB TypeInterp.semTt).SemTm n1)
    (hn2 : (TypeInterp.subst1 (TypeInterp.bool Δ) IB TypeInterp.semFf).SemTm n2) :
    (TypeInterp.subst1 (TypeInterp.bool Δ) IB hm).SemTm (.ite A m n1 n2) := by
  intro σ hσ
  asimp
  change (IB.cand (m.[σ] .: σ)).mem (.ite A.[up σ] m.[σ] n1.[σ] n2.[σ])
  apply Candidate.bool_ite (B := TypeInterp.family (TypeInterp.bool Δ) IB σ hσ)
  · exact TypeInterp.family_expansive (TypeInterp.bool Δ) IB hIB hσ
  · exact IB.type_sn (up σ) (DCandCtx.extend_up_valid (I := TypeInterp.bool Δ) hΔ hσ)
  · exact hm σ hσ
  · simpa [TypeInterp.subst1] using hn1 σ hσ
  · simpa [TypeInterp.subst1] using hn2 σ hσ

lemma semExfBotSubst1 {Δ : DCandCtx} {A m : Tm}
    (IB : TypeInterp (DCandCtx.extend (TypeInterp.bot Δ)) A)
    (hΔ : Δ.Weakens)
    (hIB : IB.Expansive)
    (hm : (TypeInterp.bot Δ).SemTm m) :
    (TypeInterp.subst1 (TypeInterp.bot Δ) IB hm).SemTm (.exf A m) := by
  intro σ hσ
  asimp
  change (IB.cand (m.[σ] .: σ)).mem (.exf A.[up σ] m.[σ])
  have hFam : (TypeInterp.family (TypeInterp.bot Δ) IB σ hσ).Expansive :=
    TypeInterp.family_expansive (TypeInterp.bot Δ) IB hIB hσ
  have go :
      ∀ A0, SN Step A0 -> ∀ p, Candidate.bot.mem p ->
        (IB.cand (p .: σ)).mem (.exf A0 p) := by
    intro A0 snA
    induction snA with
    | intro stepA ihA =>
      rename_i A0
      intro p hp
      have snp : SN Step p := Candidate.bot.sn hp
      induction snp with
      | intro stepP ihP =>
        rename_i p0
        apply Candidate.exf_dep (B := TypeInterp.family (TypeInterp.bot Δ) IB σ hσ)
        · exact hFam
        · exact hp
        · intro A' stA
          exact ihA stA p0 hp
        · intro p' stP
          have hp' : Candidate.bot.mem p' := Candidate.bot.closed_step hp stP
          exact ihP stP hp'
  exact go A.[up σ]
    (IB.type_sn (up σ) (DCandCtx.extend_up_valid (I := TypeInterp.bot Δ) hΔ hσ))
    m.[σ] (hm σ hσ)

lemma semPrjKSigmaSubst1 {Δ : DCandCtx} {A B C m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens)
    (IC : TypeInterp (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)) C)
    (hIC : IC.Expansive)
    (hm : (TypeInterp.ksig IA IB hΔ).SemTm m)
    (hnSN : ∀ σ, (hσ : Δ.valid σ) -> SN Step n.[upn 2 σ])
    (hn : ∀ σ, (hσ : Δ.valid σ) -> ∀ a,
      (ha : (IA.cand σ).mem a) -> ∀ b,
      (hb : (IB.cand (a .: σ)).mem b) ->
      (IC.cand (.tup a b .: σ)).mem n.[b .: a .: σ]) :
    (TypeInterp.subst1 (TypeInterp.ksig IA IB hΔ) IC hm).SemTm (.prj C m n) := by
  intro σ hσ
  asimp
  change (IC.cand (m.[σ] .: σ)).mem
    (.prj C.[up σ] m.[σ] n.[upn 2 σ])
  let K := TypeInterp.ksig IA IB hΔ
  have go :
      ∀ C0, SN Step C0 -> ∀ p, (K.cand σ).mem p ->
        ∀ n0, SN Step n0 -> n.[upn 2 σ] ~>* n0 ->
          (IC.cand (p .: σ)).mem (.prj C0 p n0) := by
    intro C0 snC
    induction snC with
    | intro stepC ihC =>
      rename_i C0
      intro p hp
      have snp : SN Step p := (K.cand σ).sn hp
      induction snp with
      | intro stepP ihP =>
        rename_i p
        intro n0 snN
        induction snN with
        | intro stepN ihN =>
          rename_i n0
          intro rdN
          have hvalid_p : (DCandCtx.extend K).valid (p .: σ) :=
            DCandCtx.extend_cons hσ hp
          apply Candidate.expansive_of_steps (hIC (p .: σ) hvalid_p)
          intro x st
          cases st with
          | prj_A p n stC =>
            exact ihC stC p hp n0 (SN.intro stepN) rdN
          | prj_M C n stP =>
            rename_i p'
            have hp' : (K.cand σ).mem p' :=
              (K.cand σ).closed_step hp stP
            have hred : SRed (p .: σ) (p' .: σ) := by
              intro x
              cases x with
              | zero =>
                asimp
                exact Star.one stP
              | succ x =>
                asimp
                exact Star.R
            exact IC.stable_red hvalid_p hred
              (ihP stP hp' n0 (SN.intro stepN) rdN)
          | prj_N C p stN =>
            exact ihN stN (Star.SE rdN stN)
          | prj_elim C a b branch =>
            have rd0 : (.tup a b).[shift 0] ~>* .tup a b := by
              simpa [SubstLemmas.shift0, Tm.subst_id] using
                (Star.R : (.tup a b) ~>* .tup a b)
            have hpK : (TypeInterp.ksigCand IA IB σ).mem (.tup a b) := by
              have hp0 := hp
              change (TypeInterp.ksigCandTotal IA IB σ).mem (.tup a b) at hp0
              rw [TypeInterp.ksigCandTotal_valid IA IB hσ] at hp0
              exact hp0
            have hcomp := hpK.2 0 a b rd0
            have ha : (IA.cand σ).mem a := by
              simpa [shiftSubst_zero] using hcomp.1
            have hb : (IB.cand (a .: σ)).mem b := by
              simpa [shiftSubst_zero] using hcomp.2
            have hbranch := hn σ hσ a ha b hb
            have rdBranch : n.[b .: a .: σ] ~>* n0.[b,a/] := by
              have h := Red.subst (b .: a .: ids) rdN
              rw [show n.[upn 2 σ].[b,a/] = n.[b .: a .: σ] by asimp] at h
              exact h
            exact (IC.cand (.tup a b .: σ)).closed_red hbranch rdBranch
  exact go C.[up σ]
    (IC.type_sn (up σ) (DCandCtx.extend_up_valid (I := K) hΔ hσ))
    m.[σ] (hm σ hσ) n.[upn 2 σ] (hnSN σ hσ) Star.R

lemma semPrjKSigmaSubst1_branch {Δ : DCandCtx} {A B C m n : Tm}
    (IA : TypeInterp Δ A) (IB : TypeInterp (DCandCtx.extend IA) B)
    (hΔ : Δ.Weakens) (hIA : IA.Weakens) (hIB : IB.Weakens)
    (IC : TypeInterp (DCandCtx.extend (TypeInterp.ksig IA IB hΔ)) C)
    (hIC : IC.Expansive)
    (hm : (TypeInterp.ksig IA IB hΔ).SemTm m)
    (hn : (TypeInterp.sigmaBranch IA IB hΔ hIA hIB IC).SemTm n) :
    (TypeInterp.subst1 (TypeInterp.ksig IA IB hΔ) IC hm).SemTm (.prj C m n) := by
  exact TypeInterp.semPrjKSigmaSubst1 IA IB hΔ IC hIC hm
    (TypeInterp.sigmaBranch_sn_upn2 IA IB hΔ hIA hIB IC hn)
    (TypeInterp.sigmaBranch_sem_pair IA IB hΔ hIA hIB IC hn)

lemma semRwDep {Δ : DCandCtx} {I : Candidate} {a b A m n : Tm}
    {D : CandidateFamily (Candidate.idn I a b)} :
    D.Expansive ->
    (hn : ∀ σ, Δ.valid σ -> (Candidate.idn I a b).mem n.[σ]) ->
    (hA : ∀ σ, Δ.valid σ -> SN Step A.[upn 2 σ]) ->
    (hm : ∀ σ, Δ.valid σ -> SN Step m.[σ]) ->
    (hrfl : ∀ σ, Δ.valid σ -> ∀ c, (D.fiber (.rfl c)).mem m.[σ]) ->
    ∀ σ, (hσ : Δ.valid σ) ->
      (D.fiber n.[σ]).mem (.rw A m n).[σ] := by
  intro hD hn hA hm hrfl σ hσ
  asimp
  have go :
      ∀ A0, SN Step A0 -> ∀ m0, SN Step m0 -> m.[σ] ~>* m0 ->
        ∀ p, (Candidate.idn I a b).mem p -> n.[σ] ~>* p ->
          (D.fiber p).mem (.rw A0 m0 p) := by
    intro A0 snA
    induction snA with
    | intro stepA ihA =>
      rename_i A0
      intro m0 snM
      induction snM with
      | intro stepM ihM =>
        rename_i m0
        intro rdM p hp rdP
        have snP : SN Step p := (Candidate.idn I a b).sn hp
        induction snP with
        | intro stepP ihP =>
          rename_i p
          apply Candidate.rw_dep hD hp
          · intro A' stA
            exact ihA stA m0 (SN.intro stepM) rdM p hp rdP
          · intro m' stM
            exact ihM stM (Star.SE rdM stM) p hp rdP
          · intro p' stP
            have hp' : (Candidate.idn I a b).mem p' :=
              (Candidate.idn I a b).closed_step hp stP
            exact ihP stP hp' (Star.SE rdP stP)
          · intro c
            have hbase := hrfl σ hσ c
            exact (D.fiber (.rfl c)).closed_red hbase rdM
  exact go A.[upn 2 σ] (hA σ hσ) m.[σ] (hm σ hσ) Star.R
    n.[σ] (hn σ hσ) Star.R

lemma semRwIdCases {Δ : DCandCtx} {I : Candidate} {a b A m n : Tm}
    {R : Tm -> Candidate} :
    (∀ c, Candidate.Expansive (R c)) ->
    (hn : ∀ σ, Δ.valid σ -> (Candidate.idn I a b).mem n.[σ]) ->
    (hA : ∀ σ, Δ.valid σ -> SN Step A.[upn 2 σ]) ->
    (hm : ∀ σ, Δ.valid σ -> SN Step m.[σ]) ->
    (hrfl : ∀ σ, Δ.valid σ -> ∀ c,
      ((CandidateFamily.idCases I a b R).fiber (.rfl c)).mem m.[σ]) ->
    ∀ σ, (hσ : Δ.valid σ) ->
      ((CandidateFamily.idCases I a b R).fiber n.[σ]).mem (.rw A m n).[σ] := by
  intro hR
  exact TypeInterp.semRwDep
    (D := CandidateFamily.idCases I a b R)
    (CandidateFamily.idCases_expansive hR)

lemma semRwTarget {Δ : DCandCtx} {A B a b m n : Tm}
    (IB : TypeInterp Δ B) (hΔ : Δ.Weakens) (hIB : IB.Weakens)
    (ha : IB.SemTm a) (hb : IB.SemTm b)
    (hn : (TypeInterp.idn IB ha hb).SemTm n)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A)
    (hIA : IA.Expansive)
    (hrfl : ∀ σ, Δ.valid σ -> ∀ c,
      (IA.cand (.rfl c .: b.[σ] .: σ)).mem m.[σ]) :
    (TypeInterp.idTarget IB ha hb hn IA).SemTm (.rw A m n) := by
  intro σ hσ
  asimp
  let b0 := b.[σ]
  have hb0 : (IB.cand σ).mem b0 := hb σ hσ
  let D := TypeInterp.rwFamily IB ha IA σ hσ b0 hb0
  change (D.fiber n.[σ]).mem (.rw A.[upn 2 σ] m.[σ] n.[σ])
  have hD : D.Expansive :=
    TypeInterp.rwFamily_expansive IB ha IA hIA hσ hb0
  have hIPW : (TypeInterp.idProof IB ha).Weakens :=
    TypeInterp.idProof_weakens IB ha
  have hAvalid : (DCandCtx.extend (TypeInterp.idProof IB ha)).valid (upn 2 σ) :=
    TypeInterp.extend_upn2_valid IB (TypeInterp.idProof IB ha) hΔ hIB hσ
  have snA : SN Step A.[upn 2 σ] := IA.type_sn (upn 2 σ) hAvalid
  have hnσ : (Candidate.idn (IB.cand σ) a.[σ] b0).mem n.[σ] := by
    exact hn σ hσ
  have snM : SN Step m.[σ] := by
    exact (D.fiber (.rfl b0)).sn (hrfl σ hσ b0)
  have go :
      ∀ A0, SN Step A0 -> ∀ m0, SN Step m0 -> m.[σ] ~>* m0 ->
        ∀ p, (Candidate.idn (IB.cand σ) a.[σ] b0).mem p -> n.[σ] ~>* p ->
          (D.fiber p).mem (.rw A0 m0 p) := by
    intro A0 snA0
    induction snA0 with
    | intro stepA ihA =>
      rename_i A0
      intro m0 snM0
      induction snM0 with
      | intro stepM ihM =>
        rename_i m0
        intro rdM p hp rdP
        have snP : SN Step p := (Candidate.idn (IB.cand σ) a.[σ] b0).sn hp
        induction snP with
        | intro stepP ihP =>
          rename_i p
          apply Candidate.rw_dep hD hp
          · intro A' stA
            exact ihA stA m0 (SN.intro stepM) rdM p hp rdP
          · intro m' stM
            exact ihM stM (Star.SE rdM stM) p hp rdP
          · intro p' stP
            have hp' : (Candidate.idn (IB.cand σ) a.[σ] b0).mem p' :=
              (Candidate.idn (IB.cand σ) a.[σ] b0).closed_step hp stP
            exact ihP stP hp' (Star.SE rdP stP)
          · intro c
            exact (D.fiber (.rfl c)).closed_red (hrfl σ hσ c) rdM
  exact go A.[upn 2 σ] snA m.[σ] snM Star.R n.[σ] hnσ Star.R

lemma semRwTargetSN {Δ : DCandCtx} {A B a b m n : Tm}
    (IB : TypeInterp Δ B) (hΔ : Δ.Weakens) (hIB : IB.Weakens)
    (ha : IB.SemTm a) (hb : IB.SemTm b)
    (hn : (TypeInterp.idn IB ha hb).SemTm n)
    (IA : TypeInterp (DCandCtx.extend (TypeInterp.idProof IB ha)) A)
    (hm : (TypeInterp.idBranch IB ha IA).SemTm m) :
    (TypeInterp.const Δ A.[n,b/] Candidate.snCandidate
      (fun σ hσ => (TypeInterp.idTarget IB ha hb hn IA).type_sn σ hσ)).SemTm
        (.rw A m n) := by
  intro σ hσ
  asimp
  have hAvalid : (DCandCtx.extend (TypeInterp.idProof IB ha)).valid (upn 2 σ) :=
    TypeInterp.extend_upn2_valid IB (TypeInterp.idProof IB ha) hΔ hIB hσ
  exact sn_rw
    (IA.type_sn (upn 2 σ) hAvalid)
    (TypeInterp.semTm_sn (TypeInterp.idBranch IB ha IA) hm σ hσ)
    (TypeInterp.semTm_sn (TypeInterp.idn IB ha hb) hn σ hσ)

end TypeInterp

inductive SemCtx : Ctx -> DCandCtx -> Prop where
  | nil : SemCtx [] DCandCtx.empty
  | cons {Γ Δ A} :
    SemCtx Γ Δ ->
    (I : TypeInterp Δ A) ->
    I.Weakens ->
    SemCtx (A :: Γ) (DCandCtx.extend I)

namespace SemCtx

lemma weakens {Γ : Ctx} {Δ : DCandCtx} :
    SemCtx Γ Δ -> Δ.Weakens := by
  intro hΓ
  induction hΓ with
  | nil =>
    exact DCandCtx.empty_weakens
  | cons hΓ I hI ih =>
    exact DCandCtx.extend_weakens ih hI

lemma var {Γ : Ctx} {Δ : DCandCtx} {x : Var} {A : Tm} :
    SemCtx Γ Δ ->
    Has Γ x A ->
    ∃ I : TypeInterp Δ A, I.Weakens ∧ I.SemTm (.var x) := by
  intro hΓ hs
  induction hΓ generalizing x A with
  | nil =>
    cases hs
  | cons hΓ J hJ ih =>
    cases hs with
    | zero Γ A =>
      exact ⟨TypeInterp.weakenCtx J J,
        TypeInterp.weakenCtx_weakens hJ,
        TypeInterp.semVarZero J⟩
    | succ Γ A B x hs =>
      rcases ih hs with ⟨I, hI, hvar⟩
      exact ⟨TypeInterp.weakenCtx I J,
        TypeInterp.weakenCtx_weakens hI,
        TypeInterp.semVarSucc I J hvar⟩

lemma ids_valid {Γ : Ctx} {Δ : DCandCtx} :
    SemCtx Γ Δ -> Δ.valid ids := by
  intro hΓ
  induction hΓ with
  | nil =>
    trivial
  | cons hΓ I hI ih =>
    constructor
    · have h := (SemCtx.weakens hΓ) ih
      have htail :
          (fun x : Var => (ids : Var -> Tm) (x + 1)) =
            (fun x => ((ids : Var -> Tm) x).[shift 1]) := by
        funext x
        asimp
      simpa [htail]
    · exact Candidate.var _ 0

end SemCtx

def SemType (Γ : Ctx) (A : Tm) : Prop :=
  ∀ {Δ : DCandCtx}, SemCtx Γ Δ -> ∃ I : TypeInterp Δ A, I.Weakens

def SemTyped (Γ : Ctx) (m A : Tm) : Prop :=
  ∀ {Δ : DCandCtx}, SemCtx Γ Δ -> ∃ I : TypeInterp Δ A, I.Weakens ∧ I.SemTm m

namespace SemTyped

lemma var {Γ : Ctx} {x : Var} {A : Tm} :
    Has Γ x A -> SemTyped Γ (.var x) A := by
  intro hs Δ hΓ
  exact SemCtx.var hΓ hs

lemma srt {Γ : Ctx} (i : Nat) :
    SemTyped Γ (.ty i) (.ty (i + 1)) := by
  intro Δ hΓ
  exact ⟨TypeInterp.univ Δ (i + 1),
    TypeInterp.univ_weakens Δ (i + 1),
    TypeInterp.semTy i (i + 1)⟩

lemma bool {Γ : Ctx} :
    SemTyped Γ .bool (.ty 0) := by
  intro Δ hΓ
  exact ⟨TypeInterp.univ Δ 0,
    TypeInterp.univ_weakens Δ 0,
    TypeInterp.semBoolType 0⟩

lemma bot {Γ : Ctx} :
    SemTyped Γ .bot (.ty 0) := by
  intro Δ hΓ
  exact ⟨TypeInterp.univ Δ 0,
    TypeInterp.univ_weakens Δ 0,
    TypeInterp.semBotType 0⟩

lemma tt {Γ : Ctx} :
    SemTyped Γ .tt .bool := by
  intro Δ hΓ
  exact ⟨TypeInterp.bool Δ,
    TypeInterp.bool_weakens Δ,
    TypeInterp.semTt⟩

lemma ff {Γ : Ctx} :
    SemTyped Γ .ff .bool := by
  intro Δ hΓ
  exact ⟨TypeInterp.bool Δ,
    TypeInterp.bool_weakens Δ,
    TypeInterp.semFf⟩

lemma rfl {Γ : Ctx} {A m : Tm} :
    SemTyped Γ m A ->
    SemTyped Γ (.rfl m) (.idn A m m) := by
  intro hm Δ hΓ
  rcases hm hΓ with ⟨I, hI, hmI⟩
  exact ⟨TypeInterp.idn I hmI hmI,
    TypeInterp.idn_weakens,
    TypeInterp.semRfl hmI⟩

lemma sn_subst {Γ : Ctx} {m A : Tm} :
    SemTyped Γ m A ->
    ∀ {Δ : DCandCtx}, SemCtx Γ Δ ->
    ∀ σ, Δ.valid σ -> SN Step m.[σ] := by
  intro hm Δ hΓ σ hσ
  rcases hm hΓ with ⟨I, _hI, hmI⟩
  exact (I.cand σ).sn (hmI σ hσ)

lemma sn {Γ : Ctx} {m A : Tm} {Δ : DCandCtx} :
    SemCtx Γ Δ -> SemTyped Γ m A -> SN Step m := by
  intro hΓ hm
  have h := SemTyped.sn_subst hm hΓ ids (SemCtx.ids_valid hΓ)
  simpa [Tm.subst_id] using h

lemma semType_of_typed {Γ : Ctx} {A : Tm} {i : Nat} :
    SemTyped Γ A (.ty i) -> SemType Γ A := by
  intro hA Δ hΓ
  rcases hA hΓ with ⟨I, _hI, hAI⟩
  refine ⟨TypeInterp.const Δ A Candidate.snCandidate ?_, ?_⟩
  · intro σ hσ
    exact (I.cand σ).sn (hAI σ hσ)
  · exact TypeInterp.const_weakens Candidate.snCandidate_weakens

lemma pi {Γ : Ctx} {A B : Tm} {iA iB : Nat} :
    SemTyped Γ A (.ty iA) ->
    SemTyped (A :: Γ) B (.ty iB) ->
    SemTyped Γ (.pi A B) (.ty (max iA iB)) := by
  intro hA hB Δ hΓ
  refine ⟨TypeInterp.univ Δ (max iA iB),
    TypeInterp.univ_weakens Δ (max iA iB), ?_⟩
  intro σ hσ
  asimp
  have hΔ : Δ.Weakens := SemCtx.weakens hΓ
  let IA : TypeInterp Δ A :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro τ hτ
        exact SemTyped.sn_subst hA hΓ τ hτ)
  have hIA : IA.Weakens :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens
  have hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA hIA
  have hσup : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) hΔ hσ
  exact Candidate.pi_type
    (SemTyped.sn_subst hA hΓ σ hσ)
    (SemTyped.sn_subst hB hΓA (up σ) hσup)

lemma sig {Γ : Ctx} {A B : Tm} {iA iB : Nat} :
    SemTyped Γ A (.ty iA) ->
    SemTyped (A :: Γ) B (.ty iB) ->
    SemTyped Γ (.sig A B) (.ty (max iA iB)) := by
  intro hA hB Δ hΓ
  refine ⟨TypeInterp.univ Δ (max iA iB),
    TypeInterp.univ_weakens Δ (max iA iB), ?_⟩
  intro σ hσ
  asimp
  have hΔ : Δ.Weakens := SemCtx.weakens hΓ
  let IA : TypeInterp Δ A :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro τ hτ
        exact SemTyped.sn_subst hA hΓ τ hτ)
  have hIA : IA.Weakens :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens
  have hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA hIA
  have hσup : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) hΔ hσ
  exact Candidate.sig_type
    (SemTyped.sn_subst hA hΓ σ hσ)
    (SemTyped.sn_subst hB hΓA (up σ) hσup)

lemma idn {Γ : Ctx} {A m n : Tm} {i : Nat} :
    SemTyped Γ A (.ty i) ->
    SemTyped Γ m A ->
    SemTyped Γ n A ->
    SemTyped Γ (.idn A m n) (.ty i) := by
  intro hA hm hn Δ hΓ
  refine ⟨TypeInterp.univ Δ i, TypeInterp.univ_weakens Δ i, ?_⟩
  intro σ hσ
  asimp
  exact Candidate.idn_type
    (SemTyped.sn_subst hA hΓ σ hσ)
    (SemTyped.sn_subst hm hΓ σ hσ)
    (SemTyped.sn_subst hn hΓ σ hσ)

lemma lam {Γ : Ctx} {A B m : Tm} {iA : Nat} :
    SemTyped Γ A (.ty iA) ->
    SemTyped (A :: Γ) m B ->
    SemTyped Γ (.lam A m) (.pi A B) := by
  intro hA hm Δ hΓ
  have hΔ : Δ.Weakens := SemCtx.weakens hΓ
  let IA : TypeInterp Δ A :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro σ hσ
        exact SemTyped.sn_subst hA hΓ σ hσ)
  have hIA : IA.Weakens :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens
  have hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA hIA
  rcases hm hΓA with ⟨IBody, _hIBodyW, _hmBody⟩
  let IB : TypeInterp (DCandCtx.extend IA) B :=
    TypeInterp.const (DCandCtx.extend IA) B Candidate.snCandidate
      (by
        intro σ hσ
        exact IBody.type_sn σ hσ)
  have hIBexp :
      ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) ->
        Candidate.Expansive (IB.cand σ) := by
    intro σ hσ
    exact Candidate.snCandidate_expansive
  refine ⟨TypeInterp.kpi IA IB hΔ hIBexp,
    TypeInterp.kpi_weakens IA IB hΔ hIBexp, ?_⟩
  apply TypeInterp.semLamKPiInterp IA IB hΔ hIBexp
  · intro σ hσ
    exact SemTyped.sn_subst hA hΓ σ hσ
  · intro σ hσ
    have hσup : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) hΔ hσ
    exact SemTyped.sn_subst hm hΓA (up σ) hσup
  · intro σ hσ a ha
    exact SemTyped.sn_subst hm hΓA (a .: σ)
      (DCandCtx.extend_cons hσ ha)

end SemTyped

structure SemTypeData (Γ : Ctx) (A : Tm) where
  interp : ∀ {Δ : DCandCtx}, SemCtx Γ Δ -> TypeInterp Δ A
  weakens : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ), (interp hΓ).Weakens

namespace SemTypeData

def Expansive {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ), (TA.interp hΓ).Expansive

def SemTm {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) (m : Tm) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ), (TA.interp hΓ).SemTm m

def Equiv {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData Γ B) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ) σ,
    Δ.valid σ -> ∀ t,
      ((TA.interp hΓ).cand σ).mem t ↔ ((TB.interp hΓ).cand σ).mem t

namespace Equiv

lemma refl {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) :
    SemTypeData.Equiv TA TA := by
  intro Δ hΓ σ hσ t
  exact Iff.rfl

lemma sym {Γ : Ctx} {A B : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B} :
    SemTypeData.Equiv TA TB -> SemTypeData.Equiv TB TA := by
  intro hEq Δ hΓ σ hσ t
  exact (hEq hΓ σ hσ t).symm

lemma trans {Γ : Ctx} {A B C : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B}
    {TC : SemTypeData Γ C} :
    SemTypeData.Equiv TA TB ->
    SemTypeData.Equiv TB TC ->
    SemTypeData.Equiv TA TC := by
  intro hAB hBC Δ hΓ σ hσ t
  exact Iff.trans (hAB hΓ σ hσ t) (hBC hΓ σ hσ t)

lemma semTm {Γ : Ctx} {A B m : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B} :
    SemTypeData.Equiv TA TB -> TA.SemTm m -> TB.SemTm m := by
  intro hEq hm Δ hΓ σ hσ
  exact (hEq hΓ σ hσ m.[σ]).1 (hm hΓ σ hσ)

end Equiv

lemma toSemType {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) :
    SemType Γ A := by
  intro Δ hΓ
  exact ⟨TA.interp hΓ, TA.weakens hΓ⟩

lemma toSemTyped {Γ : Ctx} {A m : Tm} (TA : SemTypeData Γ A) :
    TA.SemTm m -> SemTyped Γ m A := by
  intro hm Δ hΓ
  exact ⟨TA.interp hΓ, TA.weakens hΓ, hm hΓ⟩

lemma semTm_sn {Γ : Ctx} {A m : Tm} {TA : SemTypeData Γ A}
    {Δ : DCandCtx} :
    SemCtx Γ Δ -> TA.SemTm m -> SN Step m := by
  intro hΓ hm
  have hmem := hm hΓ ids (SemCtx.ids_valid hΓ)
  have hsn := (TA.interp hΓ).cand ids |>.sn hmem
  simpa [Tm.subst_id] using hsn

lemma semTm_sn_subst {Γ : Ctx} {A m : Tm} {TA : SemTypeData Γ A}
    {Δ : DCandCtx} :
    SemCtx Γ Δ -> TA.SemTm m -> ∀ σ, Δ.valid σ -> SN Step m.[σ] := by
  intro hΓ hm σ hσ
  exact (TA.interp hΓ).semTm_sn (hm hΓ) σ hσ

lemma semTm_closed_red {Γ : Ctx} {A m n : Tm} (TA : SemTypeData Γ A) :
    TA.SemTm m ->
    (∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ) σ,
      Δ.valid σ -> m.[σ] ~>* n.[σ]) ->
    TA.SemTm n := by
  intro hm hred Δ hΓ
  exact TypeInterp.semTm_closed_red (TA.interp hΓ) (hm hΓ)
    (fun σ hσ => hred hΓ σ hσ)

lemma semTm_conv {Γ : Ctx} {A m n : Tm} (TA : SemTypeData Γ A) :
    TA.Expansive ->
    (∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ) σ,
      Δ.valid σ -> SN Step m.[σ]) ->
    (∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ) σ,
      Δ.valid σ -> m.[σ] === n.[σ]) ->
    TA.SemTm n ->
    TA.SemTm m := by
  intro hTA hsn heq hn Δ hΓ
  exact TypeInterp.semTm_conv (TA.interp hΓ) (hTA hΓ)
    (fun σ hσ => hsn hΓ σ hσ)
    (fun σ hσ => heq hΓ σ hσ)
    (hn hΓ)

lemma semTm_closed_red_syntactic {Γ : Ctx} {A m n : Tm}
    (TA : SemTypeData Γ A) :
    TA.SemTm m -> m ~>* n -> TA.SemTm n := by
  intro hm rd
  exact TA.semTm_closed_red hm (fun _hΓ σ _hσ => Red.subst σ rd)

lemma semTm_conv_syntactic {Γ : Ctx} {A m n : Tm}
    (TA : SemTypeData Γ A) :
    TA.Expansive ->
    (∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ) σ,
      Δ.valid σ -> SN Step m.[σ]) ->
    m === n ->
    TA.SemTm n ->
    TA.SemTm m := by
  intro hTA hsn eq hn
  exact TA.semTm_conv hTA hsn (fun _hΓ σ _hσ => Conv.subst σ eq) hn

def convType {Γ : Ctx} {A B : Tm} (TA : SemTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) : SemTypeData Γ B where
  interp hΓ := (TA.interp hΓ).convType (hB hΓ)
  weakens hΓ := TypeInterp.convType_weakens (TA.interp hΓ) (hB hΓ)
    (TA.weakens hΓ)

lemma convType_expansive {Γ : Ctx} {A B : Tm} (TA : SemTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    TA.Expansive -> (TA.convType hB).Expansive := by
  intro hTA Δ hΓ
  exact TypeInterp.convType_expansive (TA.interp hΓ) (hB hΓ) (hTA hΓ)

lemma convType_semTm {Γ : Ctx} {A B m : Tm} (TA : SemTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    TA.SemTm m -> (TA.convType hB).SemTm m := by
  intro hm Δ hΓ
  exact TypeInterp.convType_semTm (TA.interp hΓ) (hB hΓ) (hm hΓ)

lemma convType_equiv_right {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    SemTypeData.Equiv TA (TA.convType hB) := by
  intro Δ hΓ σ hσ t
  exact Iff.rfl

lemma convType_equiv_left {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    SemTypeData.Equiv (TA.convType hB) TA :=
  SemTypeData.Equiv.sym (SemTypeData.convType_equiv_right TA hB)

lemma convType_equiv_of_equiv {Γ : Ctx} {A B C D : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B}
    (hEq : SemTypeData.Equiv TA TB)
    (hC : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step C.[σ])
    (hD : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step D.[σ]) :
    SemTypeData.Equiv (TA.convType hC) (TB.convType hD) := by
  intro Δ hΓ σ hσ t
  exact hEq hΓ σ hσ t

noncomputable def lookup {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) : SemTypeData Γ A where
  interp hΓ := Classical.choose (SemCtx.var hΓ hs)
  weakens hΓ := (Classical.choose_spec (SemCtx.var hΓ hs)).1

lemma var {Γ : Ctx} {x : Var} {A : Tm} (hs : Has Γ x A) :
    (SemTypeData.lookup hs).SemTm (.var x) := by
  intro Δ hΓ
  exact (Classical.choose_spec (SemCtx.var hΓ hs)).2

def univ (Γ : Ctx) (i : Nat) : SemTypeData Γ (.ty i) where
  interp {Δ} _ := TypeInterp.univ Δ i
  weakens {Δ} _ := TypeInterp.univ_weakens Δ i

lemma univ_expansive (Γ : Ctx) (i : Nat) :
    (SemTypeData.univ Γ i).Expansive := by
  intro Δ hΓ
  exact TypeInterp.univ_expansive Δ i

lemma type {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) (i : Nat) :
    (SemTypeData.univ Γ i).SemTm A := by
  intro Δ hΓ
  exact TypeInterp.semUniv (TA.interp hΓ) i

lemma ty {Γ : Ctx} (i : Nat) :
    (SemTypeData.univ Γ (i + 1)).SemTm (.ty i) :=
  SemTypeData.type (SemTypeData.univ Γ i) (i + 1)

def bool (Γ : Ctx) : SemTypeData Γ .bool where
  interp {Δ} _ := TypeInterp.bool Δ
  weakens {Δ} _ := TypeInterp.bool_weakens Δ

lemma bool_expansive (Γ : Ctx) :
    (SemTypeData.bool Γ).Expansive := by
  intro Δ hΓ
  exact TypeInterp.bool_expansive Δ

lemma bool_type {Γ : Ctx} :
    (SemTypeData.univ Γ 0).SemTm .bool :=
  SemTypeData.type (SemTypeData.bool Γ) 0

lemma tt {Γ : Ctx} : (SemTypeData.bool Γ).SemTm .tt := by
  intro Δ hΓ
  exact TypeInterp.semTt

lemma ff {Γ : Ctx} : (SemTypeData.bool Γ).SemTm .ff := by
  intro Δ hΓ
  exact TypeInterp.semFf

def bot (Γ : Ctx) : SemTypeData Γ .bot where
  interp {Δ} _ := TypeInterp.bot Δ
  weakens {Δ} _ := TypeInterp.bot_weakens Δ

lemma bot_expansive (Γ : Ctx) :
    (SemTypeData.bot Γ).Expansive := by
  intro Δ hΓ
  exact TypeInterp.bot_expansive Δ

lemma bot_type {Γ : Ctx} :
    (SemTypeData.univ Γ 0).SemTm .bot :=
  SemTypeData.type (SemTypeData.bot Γ) 0

noncomputable def idn {Γ : Ctx} {A m n : Tm}
    (TA : SemTypeData Γ A) (hm : TA.SemTm m) (hn : TA.SemTm n) :
    SemTypeData Γ (.idn A m n) where
  interp hΓ := TypeInterp.idn (TA.interp hΓ) (hm hΓ) (hn hΓ)
  weakens hΓ :=
    TypeInterp.idn_weakens (I := TA.interp hΓ)
      (hm := hm hΓ) (hn := hn hΓ)

lemma idn_expansive {Γ : Ctx} {A m n : Tm}
    (TA : SemTypeData Γ A) (hm : TA.SemTm m) (hn : TA.SemTm n) :
    (SemTypeData.idn TA hm hn).Expansive := by
  intro Δ hΓ
  change (TypeInterp.idn (TA.interp hΓ) (hm hΓ) (hn hΓ)).Expansive
  exact TypeInterp.idn_expansive (I := TA.interp hΓ)
    (hm := hm hΓ) (hn := hn hΓ)

lemma idn_equiv {Γ : Ctx} {A B m n m' n' : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B}
    {hm : TA.SemTm m} {hn : TA.SemTm n}
    {hm' : TB.SemTm m'} {hn' : TB.SemTm n'} :
    SemTypeData.Equiv
      (SemTypeData.idn TA hm hn)
      (SemTypeData.idn TB hm' hn') := by
  intro Δ hΓ σ hσ t
  rfl

lemma rfl {Γ : Ctx} {A m : Tm}
    (TA : SemTypeData Γ A) (hm : TA.SemTm m) :
    (SemTypeData.idn TA hm hm).SemTm (.rfl m) := by
  intro Δ hΓ
  exact TypeInterp.semRfl (hm hΓ)

lemma idn_type {Γ : Ctx} {A m n : Tm}
    (TA : SemTypeData Γ A) (hm : TA.SemTm m) (hn : TA.SemTm n)
    (i : Nat) :
    (SemTypeData.univ Γ i).SemTm (.idn A m n) :=
  SemTypeData.type (SemTypeData.idn TA hm hn) i

noncomputable def idBranch {Γ : Ctx} {A B a : Tm}
    (TB : SemTypeData Γ B) (ha : TB.SemTm a)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    SemTypeData Γ A.[.rfl a,a/] where
  interp {Δ} hΓ :=
    let IB := TB.interp hΓ
    let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
      SemCtx.cons hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : SemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    TypeInterp.idBranch IB (ha hΓ) (TA.interp hΓP)
  weakens {Δ} hΓ := by
    let IB := TB.interp hΓ
    let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
      SemCtx.cons hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : SemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    change (TypeInterp.idBranch IB (ha hΓ) (TA.interp hΓP)).Weakens
    exact TypeInterp.idBranch_weakens IB (ha hΓ) (TA.interp hΓP)
      (TA.weakens hΓP)

lemma idBranch_equiv_same {Γ : Ctx} {A B a : Tm}
    (TB : SemTypeData Γ B) (ha ha' : TB.SemTm a)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    SemTypeData.Equiv
      (SemTypeData.idBranch TB ha TA)
      (SemTypeData.idBranch TB ha' TA) := by
  intro Δ hΓ σ hσ t
  simp [SemTypeData.idBranch, TypeInterp.idBranch]

lemma idBranch_equiv_of_family {Γ : Ctx} {A B a : Tm}
    (TB : SemTypeData Γ B) (ha : TB.SemTm a)
    (TA TA' : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    SemTypeData.Equiv TA TA' ->
    SemTypeData.Equiv
      (SemTypeData.idBranch TB ha TA)
      (SemTypeData.idBranch TB ha TA') := by
  intro hA Δ hΓ σ hσ t
  let IB := TB.interp hΓ
  let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : SemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  have hvalid :
      (DCandCtx.extend IP).valid
        (TypeInterp.idBranchSubst a σ) :=
    TypeInterp.idBranchSubst_valid IB (ha hΓ) hσ
  simpa [SemTypeData.idBranch, TypeInterp.idBranch] using
    hA hΓP (TypeInterp.idBranchSubst a σ) hvalid t

lemma idBranch_expansive {Γ : Ctx} {A B a : Tm}
    (TB : SemTypeData Γ B) (ha : TB.SemTm a)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    TA.Expansive -> (SemTypeData.idBranch TB ha TA).Expansive := by
  intro hTA Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : SemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  change (TypeInterp.idBranch IB (ha hΓ) (TA.interp hΓP)).Expansive
  exact TypeInterp.idBranch_expansive IB (ha hΓ) (TA.interp hΓP) (hTA hΓP)

noncomputable def idTarget {Γ : Ctx} {A B a b n : Tm}
    (TB : SemTypeData Γ B) (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    SemTypeData Γ A.[n,b/] where
  interp {Δ} hΓ :=
    let IB := TB.interp hΓ
    let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
      SemCtx.cons hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : SemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ) (TA.interp hΓP)
  weakens {Δ} hΓ := by
    let IB := TB.interp hΓ
    let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
      SemCtx.cons hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : SemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    change (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ)
      (TA.interp hΓP)).Weakens
    exact TypeInterp.idTarget_weakens IB (ha hΓ) (hb hΓ) (hn hΓ)
      (TA.interp hΓP) (TA.weakens hΓP)

lemma idTarget_equiv_same {Γ : Ctx} {A B a b n : Tm}
    (TB : SemTypeData Γ B)
    (ha ha' : TB.SemTm a) (hb hb' : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (hn' : (SemTypeData.idn TB ha' hb').SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    SemTypeData.Equiv
      (SemTypeData.idTarget TB ha hb hn TA)
      (SemTypeData.idTarget TB ha' hb' hn' TA) := by
  intro Δ hΓ σ hσ t
  simp [SemTypeData.idTarget, TypeInterp.idTarget]

lemma idTarget_equiv_of_family {Γ : Ctx} {A B a b n : Tm}
    (TB : SemTypeData Γ B)
    (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA TA' : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    SemTypeData.Equiv TA TA' ->
    SemTypeData.Equiv
      (SemTypeData.idTarget TB ha hb hn TA)
      (SemTypeData.idTarget TB ha hb hn TA') := by
  intro hA Δ hΓ σ hσ t
  let IB := TB.interp hΓ
  let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : SemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  have hvalid :
      (DCandCtx.extend IP).valid
        (TypeInterp.idTargetSubst b n σ) :=
    TypeInterp.idTargetSubst_valid IB (ha hΓ) (hb hΓ) (hn hΓ) hσ
  simpa [SemTypeData.idTarget, TypeInterp.idTarget] using
    hA hΓP (TypeInterp.idTargetSubst b n σ) hvalid t

lemma idTarget_expansive {Γ : Ctx} {A B a b n : Tm}
    (TB : SemTypeData Γ B) (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    TA.Expansive -> (SemTypeData.idTarget TB ha hb hn TA).Expansive := by
  intro hTA Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : SemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  change (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ)
    (TA.interp hΓP)).Expansive
  exact TypeInterp.idTarget_expansive IB (ha hΓ) (hb hΓ) (hn hΓ)
    (TA.interp hΓP) (hTA hΓP)

noncomputable def ofSemTypedType {Γ : Ctx} {A : Tm} {i : Nat}
    (hA : SemTyped Γ A (.ty i)) : SemTypeData Γ A where
  interp {Δ} hΓ :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro σ hσ
        exact SemTyped.sn_subst hA hΓ σ hσ)
  weakens {Δ} hΓ :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens

lemma ofSemTypedType_expansive {Γ : Ctx} {A : Tm} {i : Nat}
    (hA : SemTyped Γ A (.ty i)) :
    (SemTypeData.ofSemTypedType hA).Expansive := by
  intro Δ hΓ
  exact TypeInterp.const_expansive Candidate.snCandidate_expansive

lemma ofSemTypedType_equiv {Γ : Ctx} {A B : Tm} {i j : Nat}
    (hA : SemTyped Γ A (.ty i)) (hB : SemTyped Γ B (.ty j)) :
    SemTypeData.Equiv
      (SemTypeData.ofSemTypedType hA)
      (SemTypeData.ofSemTypedType hB) := by
  intro Δ hΓ σ hσ t
  rfl

noncomputable def kpi {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) : SemTypeData Γ (.pi A B) where
  interp {Δ} hΓ :=
    let IA := TA.interp hΓ
    let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
      SemCtx.cons hΓ IA (TA.weakens hΓ)
    TypeInterp.kpi IA (TB.interp hΓA) (SemCtx.weakens hΓ) (hTB hΓA)
  weakens {Δ} hΓ := by
    let IA := TA.interp hΓ
    let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
      SemCtx.cons hΓ IA (TA.weakens hΓ)
    change (TypeInterp.kpi IA (TB.interp hΓA)
      (SemCtx.weakens hΓ) (hTB hΓA)).Weakens
    exact TypeInterp.kpi_weakens IA (TB.interp hΓA)
      (SemCtx.weakens hΓ) (hTB hΓA)

lemma kpi_equiv_same {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB hTB' : TB.Expansive) :
    SemTypeData.Equiv
      (SemTypeData.kpi TA TB hTB)
      (SemTypeData.kpi TA TB hTB') := by
  intro Δ hΓ σ hσ t
  simp [SemTypeData.kpi, TypeInterp.kpi, TypeInterp.kpiCandTotal, hσ,
    TypeInterp.kpiCand]

lemma kpi_equiv_of_codomain {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A)
    (TB TB' : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) (hTB' : TB'.Expansive) :
    SemTypeData.Equiv TB TB' ->
    SemTypeData.Equiv
      (SemTypeData.kpi TA TB hTB)
      (SemTypeData.kpi TA TB' hTB') := by
  intro hB Δ hΓ σ hσ f
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  constructor
  · intro hf
    simp [SemTypeData.kpi, TypeInterp.kpi, TypeInterp.kpiCandTotal, hσ,
      TypeInterp.kpiCand] at hf ⊢
    constructor
    · exact hf.1
    · intro i n hn
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (SemCtx.weakens hΓ) hσ i
      have hvalid : (DCandCtx.extend IA).valid (n .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi hn
      exact (hB hΓA (n .: shiftSubst σ i) hvalid (.app f.[shift i] n)).1
        (hf.2 i n hn)
  · intro hf
    simp [SemTypeData.kpi, TypeInterp.kpi, TypeInterp.kpiCandTotal, hσ,
      TypeInterp.kpiCand] at hf ⊢
    constructor
    · exact hf.1
    · intro i n hn
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (SemCtx.weakens hΓ) hσ i
      have hvalid : (DCandCtx.extend IA).valid (n .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi hn
      exact (hB hΓA (n .: shiftSubst σ i) hvalid (.app f.[shift i] n)).2
        (hf.2 i n hn)

lemma pi_type {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) (i : Nat) :
    (SemTypeData.univ Γ i).SemTm (.pi A B) :=
  SemTypeData.type (SemTypeData.kpi TA TB hTB) i

noncomputable def ksig {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B) :
    SemTypeData Γ (.sig A B) where
  interp {Δ} hΓ :=
    let IA := TA.interp hΓ
    let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
      SemCtx.cons hΓ IA (TA.weakens hΓ)
    TypeInterp.ksig IA (TB.interp hΓA) (SemCtx.weakens hΓ)
  weakens {Δ} hΓ := by
    let IA := TA.interp hΓ
    let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
      SemCtx.cons hΓ IA (TA.weakens hΓ)
    change (TypeInterp.ksig IA (TB.interp hΓA) (SemCtx.weakens hΓ)).Weakens
    exact TypeInterp.ksig_weakens IA (TB.interp hΓA) (SemCtx.weakens hΓ)

lemma ksig_equiv_of_codomain {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A)
    (TB TB' : SemTypeData (A :: Γ) B) :
    SemTypeData.Equiv TB TB' ->
    SemTypeData.Equiv
      (SemTypeData.ksig TA TB)
      (SemTypeData.ksig TA TB') := by
  intro hB Δ hΓ σ hσ p
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  constructor
  · intro hp
    simp [SemTypeData.ksig, TypeInterp.ksig, TypeInterp.ksigCandTotal, hσ,
      TypeInterp.ksigCand] at hp ⊢
    constructor
    · exact hp.1
    · intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (SemCtx.weakens hΓ) hσ i
      rcases hp.2 i a b rd with ⟨ha, hb⟩
      have hvalid : (DCandCtx.extend IA).valid (a .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi ha
      exact ⟨ha, (hB hΓA (a .: shiftSubst σ i) hvalid b).1 hb⟩
  · intro hp
    simp [SemTypeData.ksig, TypeInterp.ksig, TypeInterp.ksigCandTotal, hσ,
      TypeInterp.ksigCand] at hp ⊢
    constructor
    · exact hp.1
    · intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (SemCtx.weakens hΓ) hσ i
      rcases hp.2 i a b rd with ⟨ha, hb⟩
      have hvalid : (DCandCtx.extend IA).valid (a .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi ha
      exact ⟨ha, (hB hΓA (a .: shiftSubst σ i) hvalid b).2 hb⟩

noncomputable def ksigAt {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    {Δ : DCandCtx} (hΓ : SemCtx Γ Δ) : TypeInterp Δ (.sig A B) :=
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  TypeInterp.ksig IA (TB.interp hΓA) (SemCtx.weakens hΓ)

lemma ksigAt_weakens {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    {Δ : DCandCtx} (hΓ : SemCtx Γ Δ) :
    (SemTypeData.ksigAt TA TB hΓ).Weakens := by
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  change (TypeInterp.ksig IA (TB.interp hΓA) (SemCtx.weakens hΓ)).Weakens
  exact TypeInterp.ksig_weakens IA (TB.interp hΓA) (SemCtx.weakens hΓ)

noncomputable def ksigCtx {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    {Δ : DCandCtx} (hΓ : SemCtx Γ Δ) :
    SemCtx (.sig A B :: Γ) (DCandCtx.extend (SemTypeData.ksigAt TA TB hΓ)) :=
  SemCtx.cons hΓ (SemTypeData.ksigAt TA TB hΓ)
    (SemTypeData.ksigAt_weakens TA TB hΓ)

lemma sigmaBranch_exists {Γ : Ctx} {A B C : Tm}
    (TC : SemTypeData (.sig A B :: Γ) C) :
    ∀ {Δ : DCandCtx}, SemCtx (B :: A :: Γ) Δ ->
      ∃ I : TypeInterp Δ C.[.tup (.var 1) (.var 0) .: shift 2], I.Weakens := by
  intro Δ hΓBA
  cases hΓBA with
  | cons hΓA IB hIB =>
    cases hΓA with
    | cons hΓ IA hIA =>
      let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
      let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
      refine ⟨TypeInterp.sigmaBranch IA IB (SemCtx.weakens hΓ) hIA hIB
        (TC.interp hΓS), ?_⟩
      exact TypeInterp.sigmaBranch_weakens IA IB (SemCtx.weakens hΓ) hIA hIB
        (TC.interp hΓS) (TC.weakens hΓS)

lemma sig_type {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (i : Nat) :
    (SemTypeData.univ Γ i).SemTm (.sig A B) :=
  SemTypeData.type (SemTypeData.ksig TA TB) i

noncomputable def subst1 {Γ : Ctx} {A B n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hn : TA.SemTm n) : SemTypeData Γ B.[n/] where
  interp {Δ} hΓ :=
    let IA := TA.interp hΓ
    let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
      SemCtx.cons hΓ IA (TA.weakens hΓ)
    TypeInterp.subst1 IA (TB.interp hΓA) (hn hΓ)
  weakens {Δ} hΓ := by
    let IA := TA.interp hΓ
    let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
      SemCtx.cons hΓ IA (TA.weakens hΓ)
    change (TypeInterp.subst1 IA (TB.interp hΓA) (hn hΓ)).Weakens
    exact TypeInterp.subst1_weakens IA (TB.interp hΓA)
      (TB.weakens hΓA)

lemma subst1_equiv_same {Γ : Ctx} {A B n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hn hn' : TA.SemTm n) :
    SemTypeData.Equiv
      (SemTypeData.subst1 TA TB hn)
      (SemTypeData.subst1 TA TB hn') := by
  intro Δ hΓ σ hσ t
  simp [SemTypeData.subst1, TypeInterp.subst1]

lemma subst1_equiv_of_family {Γ : Ctx} {A B n : Tm}
    (TA : SemTypeData Γ A)
    (TB TB' : SemTypeData (A :: Γ) B)
    (hn : TA.SemTm n) :
    SemTypeData.Equiv TB TB' ->
    SemTypeData.Equiv
      (SemTypeData.subst1 TA TB hn)
      (SemTypeData.subst1 TA TB' hn) := by
  intro hB Δ hΓ σ hσ t
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  have hvalid : (DCandCtx.extend IA).valid (n.[σ] .: σ) :=
    DCandCtx.extend_cons hσ (hn hΓ σ hσ)
  simpa [SemTypeData.subst1, TypeInterp.subst1] using
    hB hΓA (n.[σ] .: σ) hvalid t

lemma subst1_equiv {Γ : Ctx} {A B n : Tm}
    (TA : SemTypeData Γ A)
    (TB TB' : SemTypeData (A :: Γ) B)
    (hn hn' : TA.SemTm n) :
    SemTypeData.Equiv TB TB' ->
    SemTypeData.Equiv
      (SemTypeData.subst1 TA TB hn)
      (SemTypeData.subst1 TA TB' hn') := by
  intro hB
  exact SemTypeData.Equiv.trans
    (SemTypeData.subst1_equiv_same TA TB hn hn')
    (SemTypeData.subst1_equiv_of_family TA TB TB' hn' hB)

lemma subst1_expansive {Γ : Ctx} {A B n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hn : TA.SemTm n) :
    TB.Expansive -> (SemTypeData.subst1 TA TB hn).Expansive := by
  intro hTB Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  change (TypeInterp.subst1 IA (TB.interp hΓA) (hn hΓ)).Expansive
  exact TypeInterp.subst1_expansive IA (TB.interp hΓA)
    (hn := hn hΓ) (hTB hΓA)

lemma lam {Γ : Ctx} {A B m : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) :
    TB.SemTm m -> (SemTypeData.kpi TA TB hTB).SemTm (.lam A m) := by
  intro hm Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  change (TypeInterp.kpi IA IB (SemCtx.weakens hΓ) (hTB hΓA)).SemTm (.lam A m)
  apply TypeInterp.semLamKPiInterp IA IB (SemCtx.weakens hΓ) (hTB hΓA)
  · intro σ hσ
    exact IA.type_sn σ hσ
  · intro σ hσ
    have hσup : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) (SemCtx.weakens hΓ) hσ
    exact (IB.cand (up σ)).sn (hm hΓA (up σ) hσup)
  · exact TypeInterp.semBody_of_semTm IA IB (hm hΓA)

lemma app {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) :
    (SemTypeData.kpi TA TB hTB).SemTm m ->
    (hn : TA.SemTm n) ->
    (SemTypeData.subst1 TA TB hn).SemTm (.app m n) := by
  intro hm hn Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  change (TypeInterp.subst1 IA IB (hn hΓ)).SemTm (.app m n)
  exact TypeInterp.semAppKPiSubst1 IA IB (SemCtx.weakens hΓ)
    (hTB hΓA) (hm hΓ) (hn hΓ)

lemma tup {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B) :
    (hm : TA.SemTm m) ->
    (SemTypeData.subst1 TA TB hm).SemTm n ->
    (SemTypeData.ksig TA TB).SemTm (.tup m n) := by
  intro hm hn Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  change (TypeInterp.ksig IA IB (SemCtx.weakens hΓ)).SemTm (.tup m n)
  apply TypeInterp.semTupKSigmaInterp IA IB (SemCtx.weakens hΓ)
  · exact hm hΓ
  · intro σ hσ
    exact hn hΓ σ hσ

lemma prj {Γ : Ctx} {A B C m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (hm : (SemTypeData.ksig TA TB).SemTm m)
    (hnSN : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step n.[upn 2 σ])
    (hn : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      ∀ σ, (hσ : Δ.valid σ) -> ∀ a, (ha : (IA.cand σ).mem a) ->
        ∀ b, (hb : (IB.cand (a .: σ)).mem b) ->
          ((TC.interp (SemTypeData.ksigCtx TA TB hΓ)).cand (.tup a b .: σ)).mem
            n.[b .: a .: σ]) :
    (SemTypeData.subst1 (SemTypeData.ksig TA TB) TC hm).SemTm (.prj C m n) := by
  intro Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
  let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
    SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
  change (TypeInterp.subst1 K (TC.interp hΓS) (hm hΓ)).SemTm (.prj C m n)
  exact TypeInterp.semPrjKSigmaSubst1 IA IB (SemCtx.weakens hΓ)
    (TC.interp hΓS) (hTC hΓS) (hm hΓ) (hnSN hΓ)
    (by
      intro σ hσ a ha b hb
      have h := hn hΓ σ hσ a ha b hb
      simpa [SemTypeData.ksigCtx, SemTypeData.ksigAt] using h)

lemma prj_branch {Γ : Ctx} {A B C m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (hm : (SemTypeData.ksig TA TB).SemTm m)
    (hn : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
      let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (SemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    (SemTypeData.subst1 (SemTypeData.ksig TA TB) TC hm).SemTm (.prj C m n) := by
  intro Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
  let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
    SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
  change (TypeInterp.subst1 K (TC.interp hΓS) (hm hΓ)).SemTm (.prj C m n)
  exact TypeInterp.semPrjKSigmaSubst1_branch IA IB (SemCtx.weakens hΓ)
    (TA.weakens hΓ) (TB.weakens hΓA) (TC.interp hΓS) (hTC hΓS)
    (hm hΓ) (hn hΓ)

lemma ite {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : SemTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (hm : (SemTypeData.bool Γ).SemTm m)
    (hn1 : (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.tt).SemTm n1)
    (hn2 : (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.ff).SemTm n2) :
    (SemTypeData.subst1 (SemTypeData.bool Γ) TB hm).SemTm (.ite A m n1 n2) := by
  intro Δ hΓ
  let hΓB : SemCtx (.bool :: Γ) (DCandCtx.extend (TypeInterp.bool Δ)) :=
    SemCtx.cons hΓ (TypeInterp.bool Δ) (TypeInterp.bool_weakens Δ)
  let IB := TB.interp hΓB
  change (TypeInterp.subst1 (TypeInterp.bool Δ) IB (hm hΓ)).SemTm (.ite A m n1 n2)
  exact TypeInterp.semIteBoolSubst1 IB (SemCtx.weakens hΓ) (hTB hΓB)
    (hm hΓ) (hn1 hΓ) (hn2 hΓ)

lemma exf {Γ : Ctx} {A m : Tm}
    (TB : SemTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (hm : (SemTypeData.bot Γ).SemTm m) :
    (SemTypeData.subst1 (SemTypeData.bot Γ) TB hm).SemTm (.exf A m) := by
  intro Δ hΓ
  let hΓB : SemCtx (.bot :: Γ) (DCandCtx.extend (TypeInterp.bot Δ)) :=
    SemCtx.cons hΓ (TypeInterp.bot Δ) (TypeInterp.bot_weakens Δ)
  let IB := TB.interp hΓB
  change (TypeInterp.subst1 (TypeInterp.bot Δ) IB (hm hΓ)).SemTm (.exf A m)
  exact TypeInterp.semExfBotSubst1 IB (SemCtx.weakens hΓ) (hTB hΓB) (hm hΓ)

lemma rw_target {Γ : Ctx} {A B m n a b : Tm}
    (TB : SemTypeData Γ B)
    (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hTA : TA.Expansive)
    (hrfl : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IB := TB.interp hΓ
      let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
        SemCtx.cons hΓ IB (TB.weakens hΓ)
      let IP := TypeInterp.idProof IB (ha hΓ)
      let hΓP : SemCtx
          (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
          (DCandCtx.extend IP) :=
        SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
      let IA := TA.interp hΓP
      ∀ σ, Δ.valid σ -> ∀ c,
        (IA.cand (.rfl c .: b.[σ] .: σ)).mem m.[σ]) :
    SemTyped Γ (.rw A m n) A.[n,b/] := by
  intro Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : SemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  let IA := TA.interp hΓP
  refine ⟨TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ) IA,
    TypeInterp.idTarget_weakens IB (ha hΓ) (hb hΓ) (hn hΓ) IA
      (TA.weakens hΓP), ?_⟩
  exact TypeInterp.semRwTarget IB (SemCtx.weakens hΓ) (TB.weakens hΓ)
    (ha hΓ) (hb hΓ) (hn hΓ) IA (hTA hΓP) (hrfl hΓ)

lemma rw_sn {Γ : Ctx} {A B m n a b : Tm}
    (TB : SemTypeData Γ B)
    (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hm : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IB := TB.interp hΓ
      let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
        SemCtx.cons hΓ IB (TB.weakens hΓ)
      let IP := TypeInterp.idProof IB (ha hΓ)
      let hΓP : SemCtx
          (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
          (DCandCtx.extend IP) :=
        SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
      let IA := TA.interp hΓP
      (TypeInterp.idBranch IB (ha hΓ) IA).SemTm m) :
    SemTyped Γ (.rw A m n) A.[n,b/] := by
  intro Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : SemCtx (B :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : SemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    SemCtx.cons hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  let IA := TA.interp hΓP
  refine ⟨TypeInterp.const Δ A.[n,b/] Candidate.snCandidate
      (fun σ hσ => (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ) IA).type_sn σ hσ),
    TypeInterp.const_weakens Candidate.snCandidate_weakens, ?_⟩
  exact TypeInterp.semRwTargetSN IB (SemCtx.weakens hΓ) (TB.weakens hΓ)
    (ha hΓ) (hb hΓ) (hn hΓ) IA (hm hΓ)

lemma rw_sn_branch {Γ : Ctx} {A B m n a b : Tm}
    (TB : SemTypeData Γ B)
    (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    (SemTypeData.idBranch TB ha TA).SemTm m ->
    SemTyped Γ (.rw A m n) A.[n,b/] := by
  intro hm
  apply SemTypeData.rw_sn TB ha hb hn TA
  intro Δ hΓ
  exact hm hΓ

end SemTypeData

inductive CanSemCtxCore : ∀ (Γ : Ctx) (Δ : DCandCtx), SemCtx Γ Δ -> Type where
  | nil : CanSemCtxCore [] DCandCtx.empty SemCtx.nil
  | cons {Γ : Ctx} {Δ : DCandCtx} {A : Tm} {hΓ : SemCtx Γ Δ} :
    CanSemCtxCore Γ Δ hΓ ->
    (TA : SemTypeData Γ A) ->
    CanSemCtxCore (A :: Γ) (DCandCtx.extend (TA.interp hΓ))
      (SemCtx.cons hΓ (TA.interp hΓ) (TA.weakens hΓ))
  | consInterp {Γ : Ctx} {Δ : DCandCtx} {A : Tm} {hΓ : SemCtx Γ Δ} :
    CanSemCtxCore Γ Δ hΓ ->
    (I : TypeInterp Δ A) ->
    (hI : I.Weakens) ->
    CanSemCtxCore (A :: Γ) (DCandCtx.extend I)
      (SemCtx.cons hΓ I hI)

structure CanSemCtx (Γ : Ctx) (Δ : DCandCtx) where
  semCtx : SemCtx Γ Δ
  canonical : CanSemCtxCore Γ Δ semCtx

namespace CanSemCtx

def nil : CanSemCtx [] DCandCtx.empty where
  semCtx := SemCtx.nil
  canonical := CanSemCtxCore.nil

def cons {Γ : Ctx} {Δ : DCandCtx} {A : Tm}
    (hΓ : CanSemCtx Γ Δ) (TA : SemTypeData Γ A) :
    CanSemCtx (A :: Γ) (DCandCtx.extend (TA.interp hΓ.semCtx)) where
  semCtx := SemCtx.cons hΓ.semCtx (TA.interp hΓ.semCtx) (TA.weakens hΓ.semCtx)
  canonical := CanSemCtxCore.cons hΓ.canonical TA

def consInterp {Γ : Ctx} {Δ : DCandCtx} {A : Tm}
    (hΓ : CanSemCtx Γ Δ) (I : TypeInterp Δ A) (hI : I.Weakens) :
    CanSemCtx (A :: Γ) (DCandCtx.extend I) where
  semCtx := SemCtx.cons hΓ.semCtx I hI
  canonical := CanSemCtxCore.consInterp hΓ.canonical I hI

lemma weakens {Γ : Ctx} {Δ : DCandCtx} :
    CanSemCtx Γ Δ -> Δ.Weakens := by
  intro hΓ
  exact SemCtx.weakens hΓ.semCtx

lemma ids_valid {Γ : Ctx} {Δ : DCandCtx} :
    CanSemCtx Γ Δ -> Δ.valid ids := by
  intro hΓ
  exact SemCtx.ids_valid hΓ.semCtx

lemma var {Γ : Ctx} {Δ : DCandCtx} {x : Var} {A : Tm} :
    CanSemCtx Γ Δ ->
    Has Γ x A ->
    ∃ I : TypeInterp Δ A, I.Weakens ∧ I.SemTm (.var x) := by
  intro hΓ hs
  exact SemCtx.var hΓ.semCtx hs

end CanSemCtx

def CanSemType (Γ : Ctx) (A : Tm) : Prop :=
  ∀ {Δ : DCandCtx}, CanSemCtx Γ Δ -> ∃ I : TypeInterp Δ A, I.Weakens

def CanSemTyped (Γ : Ctx) (m A : Tm) : Prop :=
  ∀ {Δ : DCandCtx}, CanSemCtx Γ Δ -> ∃ I : TypeInterp Δ A, I.Weakens ∧ I.SemTm m

namespace CanSemTyped

lemma sn_subst {Γ : Ctx} {m A : Tm} {Δ : DCandCtx} :
    CanSemTyped Γ m A -> CanSemCtx Γ Δ -> ∀ σ, Δ.valid σ -> SN Step m.[σ] := by
  intro hm hΓ σ hσ
  rcases hm hΓ with ⟨I, _hI, hIm⟩
  exact I.semTm_sn hIm σ hσ

lemma sn {Γ : Ctx} {m A : Tm} {Δ : DCandCtx} :
    CanSemCtx Γ Δ -> CanSemTyped Γ m A -> SN Step m := by
  intro hΓ hm
  have h := CanSemTyped.sn_subst hm hΓ ids (CanSemCtx.ids_valid hΓ)
  simpa [Tm.subst_id] using h

lemma of_sem_typed {Γ : Ctx} {m A : Tm} :
    SemTyped Γ m A -> CanSemTyped Γ m A := by
  intro hm Δ hΓ
  exact hm hΓ.semCtx

lemma var {Γ : Ctx} {x : Var} {A : Tm} :
    Has Γ x A -> CanSemTyped Γ (.var x) A := by
  intro hs Δ hΓ
  exact CanSemCtx.var hΓ hs

lemma srt {Γ : Ctx} (i : Nat) :
    CanSemTyped Γ (.ty i) (.ty (i + 1)) :=
  CanSemTyped.of_sem_typed (SemTyped.srt i)

lemma bool {Γ : Ctx} :
    CanSemTyped Γ .bool (.ty 0) :=
  CanSemTyped.of_sem_typed SemTyped.bool

lemma bot {Γ : Ctx} :
    CanSemTyped Γ .bot (.ty 0) :=
  CanSemTyped.of_sem_typed SemTyped.bot

lemma tt {Γ : Ctx} :
    CanSemTyped Γ .tt .bool :=
  CanSemTyped.of_sem_typed SemTyped.tt

lemma ff {Γ : Ctx} :
    CanSemTyped Γ .ff .bool :=
  CanSemTyped.of_sem_typed SemTyped.ff

lemma rfl {Γ : Ctx} {A m : Tm} :
    CanSemTyped Γ m A ->
    CanSemTyped Γ (.rfl m) (.idn A m m) := by
  intro hm Δ hΓ
  rcases hm hΓ with ⟨I, hI, hmI⟩
  exact ⟨TypeInterp.idn I hmI hmI,
    TypeInterp.idn_weakens,
    TypeInterp.semRfl hmI⟩

lemma convWeak {Γ : Ctx} {A B m : Tm} {i : Nat} :
    A === B ->
    CanSemTyped Γ m A ->
    CanSemTyped Γ B (.ty i) ->
    CanSemTyped Γ m B := by
  intro _eq hm hB Δ hΓ
  rcases hm hΓ with ⟨I, _hI, hmI⟩
  rcases hB hΓ with ⟨IB, _hIB, hBI⟩
  refine ⟨TypeInterp.const Δ B Candidate.snCandidate ?_,
    TypeInterp.const_weakens Candidate.snCandidate_weakens, ?_⟩
  · intro σ hσ
    exact (IB.cand σ).sn (hBI σ hσ)
  · intro σ hσ
    exact I.semTm_sn hmI σ hσ

lemma pi {Γ : Ctx} {A B : Tm} {iA iB : Nat} :
    CanSemTyped Γ A (.ty iA) ->
    CanSemTyped (A :: Γ) B (.ty iB) ->
    CanSemTyped Γ (.pi A B) (.ty (max iA iB)) := by
  intro hA hB Δ hΓ
  refine ⟨TypeInterp.univ Δ (max iA iB),
    TypeInterp.univ_weakens Δ (max iA iB), ?_⟩
  intro σ hσ
  asimp
  have hΔ : Δ.Weakens := CanSemCtx.weakens hΓ
  let IA : TypeInterp Δ A :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro τ hτ
        exact CanSemTyped.sn_subst hA hΓ τ hτ)
  have hIA : IA.Weakens :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens
  have hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA hIA
  have hσup : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) hΔ hσ
  exact Candidate.pi_type
    (CanSemTyped.sn_subst hA hΓ σ hσ)
    (CanSemTyped.sn_subst hB hΓA (up σ) hσup)

lemma sig {Γ : Ctx} {A B : Tm} {iA iB : Nat} :
    CanSemTyped Γ A (.ty iA) ->
    CanSemTyped (A :: Γ) B (.ty iB) ->
    CanSemTyped Γ (.sig A B) (.ty (max iA iB)) := by
  intro hA hB Δ hΓ
  refine ⟨TypeInterp.univ Δ (max iA iB),
    TypeInterp.univ_weakens Δ (max iA iB), ?_⟩
  intro σ hσ
  asimp
  have hΔ : Δ.Weakens := CanSemCtx.weakens hΓ
  let IA : TypeInterp Δ A :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro τ hτ
        exact CanSemTyped.sn_subst hA hΓ τ hτ)
  have hIA : IA.Weakens :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens
  have hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA hIA
  have hσup : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) hΔ hσ
  exact Candidate.sig_type
    (CanSemTyped.sn_subst hA hΓ σ hσ)
    (CanSemTyped.sn_subst hB hΓA (up σ) hσup)

lemma idn {Γ : Ctx} {A m n : Tm} {i : Nat} :
    CanSemTyped Γ A (.ty i) ->
    CanSemTyped Γ m A ->
    CanSemTyped Γ n A ->
    CanSemTyped Γ (.idn A m n) (.ty i) := by
  intro hA hm hn Δ hΓ
  refine ⟨TypeInterp.univ Δ i, TypeInterp.univ_weakens Δ i, ?_⟩
  intro σ hσ
  asimp
  exact Candidate.idn_type
    (CanSemTyped.sn_subst hA hΓ σ hσ)
    (CanSemTyped.sn_subst hm hΓ σ hσ)
    (CanSemTyped.sn_subst hn hΓ σ hσ)

lemma lam {Γ : Ctx} {A B m : Tm} {iA : Nat} :
    CanSemTyped Γ A (.ty iA) ->
    CanSemTyped (A :: Γ) m B ->
    CanSemTyped Γ (.lam A m) (.pi A B) := by
  intro hA hm Δ hΓ
  have hΔ : Δ.Weakens := CanSemCtx.weakens hΓ
  let IA : TypeInterp Δ A :=
    TypeInterp.const Δ A Candidate.snCandidate
      (by
        intro σ hσ
        exact CanSemTyped.sn_subst hA hΓ σ hσ)
  have hIA : IA.Weakens :=
    TypeInterp.const_weakens Candidate.snCandidate_weakens
  have hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA hIA
  rcases hm hΓA with ⟨IBody, _hIBodyW, _hmBody⟩
  let IB : TypeInterp (DCandCtx.extend IA) B :=
    TypeInterp.const (DCandCtx.extend IA) B Candidate.snCandidate
      (by
        intro σ hσ
        exact IBody.type_sn σ hσ)
  have hIBexp :
      ∀ σ, (hσ : (DCandCtx.extend IA).valid σ) ->
        Candidate.Expansive (IB.cand σ) := by
    intro σ hσ
    exact Candidate.snCandidate_expansive
  refine ⟨TypeInterp.kpi IA IB hΔ hIBexp,
    TypeInterp.kpi_weakens IA IB hΔ hIBexp, ?_⟩
  apply TypeInterp.semLamKPiInterp IA IB hΔ hIBexp
  · intro σ hσ
    exact CanSemTyped.sn_subst hA hΓ σ hσ
  · intro σ hσ
    have hσup : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) hΔ hσ
    exact CanSemTyped.sn_subst hm hΓA (up σ) hσup
  · intro σ hσ a ha
    exact CanSemTyped.sn_subst hm hΓA (a .: σ)
      (DCandCtx.extend_cons hσ ha)

lemma iteSN {Γ : Ctx} {A m n1 n2 : Tm} {i : Nat} :
    CanSemTyped (.bool :: Γ) A (.ty i) ->
    CanSemTyped Γ m .bool ->
    CanSemTyped Γ n1 A.[.tt/] ->
    CanSemTyped Γ n2 A.[.ff/] ->
    CanSemTyped Γ (.ite A m n1 n2) A.[m/] := by
  intro hA hm hn1 hn2 Δ hΓ
  let hΓB : CanSemCtx (.bool :: Γ) (DCandCtx.extend (TypeInterp.bool Δ)) :=
    CanSemCtx.consInterp hΓ (TypeInterp.bool Δ) (TypeInterp.bool_weakens Δ)
  refine ⟨TypeInterp.const Δ A.[m/] Candidate.snCandidate ?_,
    TypeInterp.const_weakens Candidate.snCandidate_weakens, ?_⟩
  · intro σ hσ
    have snm : SN Step m.[σ] := CanSemTyped.sn_subst hm hΓ σ hσ
    have hσm : (DCandCtx.extend (TypeInterp.bool Δ)).valid (m.[σ] .: σ) :=
      DCandCtx.extend_cons hσ snm
    have hsn := CanSemTyped.sn_subst hA hΓB (m.[σ] .: σ) hσm
    rw [show A.[m/].[σ] = A.[m.[σ] .: σ] by asimp]
    exact hsn
  · intro σ hσ
    have hσB : (DCandCtx.extend (TypeInterp.bool Δ)).valid (up σ) :=
      DCandCtx.extend_up_valid (I := TypeInterp.bool Δ) (CanSemCtx.weakens hΓ) hσ
    have snA : SN Step A.[up σ] :=
      CanSemTyped.sn_subst hA hΓB (up σ) hσB
    have snm : SN Step m.[σ] :=
      CanSemTyped.sn_subst hm hΓ σ hσ
    have sn1 : SN Step n1.[σ] :=
      CanSemTyped.sn_subst hn1 hΓ σ hσ
    have sn2 : SN Step n2.[σ] :=
      CanSemTyped.sn_subst hn2 hΓ σ hσ
    change SN Step (.ite A.[up σ] m.[σ] n1.[σ] n2.[σ])
    exact sn_ite snA snm sn1 sn2

lemma exfSN {Γ : Ctx} {A m : Tm} {i : Nat} :
    CanSemTyped (.bot :: Γ) A (.ty i) ->
    CanSemTyped Γ m .bot ->
    CanSemTyped Γ (.exf A m) A.[m/] := by
  intro hA hm Δ hΓ
  let hΓB : CanSemCtx (.bot :: Γ) (DCandCtx.extend (TypeInterp.bot Δ)) :=
    CanSemCtx.consInterp hΓ (TypeInterp.bot Δ) (TypeInterp.bot_weakens Δ)
  refine ⟨TypeInterp.const Δ A.[m/] Candidate.snCandidate ?_,
    TypeInterp.const_weakens Candidate.snCandidate_weakens, ?_⟩
  · intro σ hσ
    have snm : SN Step m.[σ] := CanSemTyped.sn_subst hm hΓ σ hσ
    have hσm : (DCandCtx.extend (TypeInterp.bot Δ)).valid (m.[σ] .: σ) :=
      DCandCtx.extend_cons hσ snm
    have hsn := CanSemTyped.sn_subst hA hΓB (m.[σ] .: σ) hσm
    rw [show A.[m/].[σ] = A.[m.[σ] .: σ] by asimp]
    exact hsn
  · intro σ hσ
    have hσB : (DCandCtx.extend (TypeInterp.bot Δ)).valid (up σ) :=
      DCandCtx.extend_up_valid (I := TypeInterp.bot Δ) (CanSemCtx.weakens hΓ) hσ
    have snA : SN Step A.[up σ] :=
      CanSemTyped.sn_subst hA hΓB (up σ) hσB
    have snm : SN Step m.[σ] :=
      CanSemTyped.sn_subst hm hΓ σ hσ
    change SN Step (.exf A.[up σ] m.[σ])
    exact sn_exf snA snm

end CanSemTyped

namespace SemTypeData

def CanSemTm {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) (m : Tm) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ), (TA.interp hΓ.semCtx).SemTm m

def CanEquiv {Γ : Ctx} {A B : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData Γ B) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ) σ,
    Δ.valid σ -> ∀ t,
      ((TA.interp hΓ.semCtx).cand σ).mem t ↔
        ((TB.interp hΓ.semCtx).cand σ).mem t

namespace CanEquiv

lemma refl {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) :
    SemTypeData.CanEquiv TA TA := by
  intro Δ hΓ σ hσ t
  exact Iff.rfl

lemma sym {Γ : Ctx} {A B : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B} :
    SemTypeData.CanEquiv TA TB -> SemTypeData.CanEquiv TB TA := by
  intro hEq Δ hΓ σ hσ t
  exact (hEq hΓ σ hσ t).symm

lemma trans {Γ : Ctx} {A B C : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B}
    {TC : SemTypeData Γ C} :
    SemTypeData.CanEquiv TA TB ->
    SemTypeData.CanEquiv TB TC ->
    SemTypeData.CanEquiv TA TC := by
  intro hAB hBC Δ hΓ σ hσ t
  exact Iff.trans (hAB hΓ σ hσ t) (hBC hΓ σ hσ t)

lemma semTm {Γ : Ctx} {A B m : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B} :
    SemTypeData.CanEquiv TA TB -> TA.CanSemTm m -> TB.CanSemTm m := by
  intro hEq hm Δ hΓ σ hσ
  exact (hEq hΓ σ hσ m.[σ]).1 (hm hΓ σ hσ)

end CanEquiv

lemma Equiv.toCanEquiv {Γ : Ctx} {A B : Tm}
    {TA : SemTypeData Γ A} {TB : SemTypeData Γ B} :
    SemTypeData.Equiv TA TB -> SemTypeData.CanEquiv TA TB := by
  intro hEq Δ hΓ σ hσ t
  exact hEq hΓ.semCtx σ hσ t

lemma CanSemTm.toCanSemTyped {Γ : Ctx} {A m : Tm}
    (TA : SemTypeData Γ A) :
    TA.CanSemTm m -> CanSemTyped Γ m A := by
  intro hm Δ hΓ
  exact ⟨TA.interp hΓ.semCtx, TA.weakens hΓ.semCtx, hm hΓ⟩

lemma CanSemTm.sn_subst {Γ : Ctx} {A m : Tm}
    {TA : SemTypeData Γ A} :
    TA.CanSemTm m ->
    ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step m.[σ] := by
  intro hm Δ hΓ σ hσ
  exact (TA.interp hΓ.semCtx).semTm_sn (hm hΓ) σ hσ

lemma canAppKPi {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) :
    (SemTypeData.kpi TA TB hTB).CanSemTm m ->
    TA.CanSemTm n ->
    CanSemTyped Γ (.app m n) B.[n/] := by
  intro hm hn Δ hΓ
  let IA := TA.interp hΓ.semCtx
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ.semCtx IA (TA.weakens hΓ.semCtx)
  let IB := TB.interp hΓA
  let hnI : IA.SemTm n := hn hΓ
  refine ⟨TypeInterp.subst1 IA IB hnI,
    TypeInterp.subst1_weakens IA IB (TB.weakens hΓA), ?_⟩
  change (TypeInterp.subst1 IA IB hnI).SemTm (.app m n)
  exact TypeInterp.semAppKPiSubst1 IA IB (SemCtx.weakens hΓ.semCtx)
    (hTB hΓA) (hm hΓ) hnI

lemma canLamKPi {Γ : Ctx} {A B m : Tm}
    (TA : SemTypeData Γ A)
    (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive) :
    TB.CanSemTm m ->
    (SemTypeData.kpi TA TB hTB).CanSemTm (.lam A m) := by
  intro hm Δ hΓ
  let IA := TA.interp hΓ.semCtx
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.cons hΓ TA
  let IB := TB.interp hΓA.semCtx
  change (TypeInterp.kpi IA IB (SemCtx.weakens hΓ.semCtx) (hTB hΓA.semCtx)).SemTm
    (.lam A m)
  apply TypeInterp.semLamKPiInterp IA IB (SemCtx.weakens hΓ.semCtx) (hTB hΓA.semCtx)
  · intro σ hσ
    exact IA.type_sn σ hσ
  · intro σ hσ
    have hσup : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) (SemCtx.weakens hΓ.semCtx) hσ
    exact (IB.cand (up σ)).sn (hm hΓA (up σ) hσup)
  · intro σ hσ a ha
    exact hm hΓA (a .: σ) (DCandCtx.extend_cons hσ ha)

lemma canTupKSig {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hm : TA.CanSemTm m)
    (hn : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IA := TA.interp hΓ.semCtx
      let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ.semCtx IA (TA.weakens hΓ.semCtx)
      let IB := TB.interp hΓA
      (TypeInterp.subst1 IA IB (hm hΓ)).SemTm n) :
    (SemTypeData.ksig TA TB).CanSemTm (.tup m n) := by
  intro Δ hΓ
  let IA := TA.interp hΓ.semCtx
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ.semCtx IA (TA.weakens hΓ.semCtx)
  let IB := TB.interp hΓA
  change (TypeInterp.ksig IA IB (SemCtx.weakens hΓ.semCtx)).SemTm (.tup m n)
  apply TypeInterp.semTupKSigmaInterp IA IB (SemCtx.weakens hΓ.semCtx)
  · exact hm hΓ
  · intro σ hσ
    exact hn hΓ σ hσ

end SemTypeData

structure CanTypeData (Γ : Ctx) (A : Tm) where
  interp : ∀ {Δ : DCandCtx}, CanSemCtx Γ Δ -> TypeInterp Δ A
  weakens : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ), (interp hΓ).Weakens

namespace CanTypeData

def Expansive {Γ : Ctx} {A : Tm} (TA : CanTypeData Γ A) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ), (TA.interp hΓ).Expansive

def CanSemTm {Γ : Ctx} {A : Tm} (TA : CanTypeData Γ A) (m : Tm) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ), (TA.interp hΓ).SemTm m

def Equiv {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData Γ B) : Prop :=
  ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ) σ,
    Δ.valid σ -> ∀ t,
      ((TA.interp hΓ).cand σ).mem t ↔ ((TB.interp hΓ).cand σ).mem t

namespace Equiv

lemma refl {Γ : Ctx} {A : Tm} (TA : CanTypeData Γ A) :
    CanTypeData.Equiv TA TA := by
  intro Δ hΓ σ hσ t
  exact Iff.rfl

lemma sym {Γ : Ctx} {A B : Tm}
    {TA : CanTypeData Γ A} {TB : CanTypeData Γ B} :
    CanTypeData.Equiv TA TB -> CanTypeData.Equiv TB TA := by
  intro hEq Δ hΓ σ hσ t
  exact (hEq hΓ σ hσ t).symm

lemma trans {Γ : Ctx} {A B C : Tm}
    {TA : CanTypeData Γ A} {TB : CanTypeData Γ B}
    {TC : CanTypeData Γ C} :
    CanTypeData.Equiv TA TB ->
    CanTypeData.Equiv TB TC ->
    CanTypeData.Equiv TA TC := by
  intro hAB hBC Δ hΓ σ hσ t
  exact Iff.trans (hAB hΓ σ hσ t) (hBC hΓ σ hσ t)

lemma semTm {Γ : Ctx} {A B m : Tm}
    {TA : CanTypeData Γ A} {TB : CanTypeData Γ B} :
    CanTypeData.Equiv TA TB -> TA.CanSemTm m -> TB.CanSemTm m := by
  intro hEq hm Δ hΓ σ hσ
  exact (hEq hΓ σ hσ m.[σ]).1 (hm hΓ σ hσ)

end Equiv

def convType {Γ : Ctx} {A B : Tm} (TA : CanTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    CanTypeData Γ B where
  interp hΓ := (TA.interp hΓ).convType (hB hΓ)
  weakens hΓ := TypeInterp.convType_weakens (TA.interp hΓ) (hB hΓ)
    (TA.weakens hΓ)

lemma convType_expansive {Γ : Ctx} {A B : Tm} (TA : CanTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    TA.Expansive -> (TA.convType hB).Expansive := by
  intro hTA Δ hΓ
  exact TypeInterp.convType_expansive (TA.interp hΓ) (hB hΓ) (hTA hΓ)

lemma convType_semTm {Γ : Ctx} {A B m : Tm} (TA : CanTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    TA.CanSemTm m -> (TA.convType hB).CanSemTm m := by
  intro hm Δ hΓ
  exact TypeInterp.convType_semTm (TA.interp hΓ) (hB hΓ) (hm hΓ)

lemma convType_equiv_right {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    CanTypeData.Equiv TA (TA.convType hB) := by
  intro Δ hΓ σ hσ t
  rfl

lemma convType_equiv_left {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    CanTypeData.Equiv (TA.convType hB) TA :=
  CanTypeData.Equiv.sym (CanTypeData.convType_equiv_right TA hB)

lemma convType_equiv_of_equiv {Γ : Ctx} {A B C D : Tm}
    {TA : CanTypeData Γ A} {TB : CanTypeData Γ B}
    (hEq : CanTypeData.Equiv TA TB)
    (hC : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step C.[σ])
    (hD : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step D.[σ]) :
    CanTypeData.Equiv (TA.convType hC) (TB.convType hD) := by
  intro Δ hΓ σ hσ t
  exact hEq hΓ σ hσ t

def ofSemTypeData {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) :
    CanTypeData Γ A where
  interp hΓ := TA.interp hΓ.semCtx
  weakens hΓ := TA.weakens hΓ.semCtx

lemma ofSemTypeData_expansive {Γ : Ctx} {A : Tm} (TA : SemTypeData Γ A) :
    TA.Expansive -> (CanTypeData.ofSemTypeData TA).Expansive := by
  intro hTA Δ hΓ
  exact hTA hΓ.semCtx

noncomputable def weaken {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) : CanTypeData (B :: Γ) A.[shift 1] where
  interp {Δ} hΓB := by
    rcases hΓB with ⟨_hSem, hCan⟩
    cases hCan with
    | cons hTail TB =>
      let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
      exact TypeInterp.weakenCtx (TA.interp hTailCtx)
        (TB.interp hTailCtx.semCtx)
    | consInterp hTail I _hI =>
      let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
      exact TypeInterp.weakenCtx (TA.interp hTailCtx) I
  weakens {Δ} hΓB := by
    rcases hΓB with ⟨_hSem, hCan⟩
    cases hCan with
    | cons hTail TB =>
      let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
      change (TypeInterp.weakenCtx (TA.interp hTailCtx)
        (TB.interp hTailCtx.semCtx)).Weakens
      exact TypeInterp.weakenCtx_weakens (TA.weakens hTailCtx)
    | consInterp hTail I _hI =>
      let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
      change (TypeInterp.weakenCtx (TA.interp hTailCtx) I).Weakens
      exact TypeInterp.weakenCtx_weakens (TA.weakens hTailCtx)

lemma weaken_semTm {Γ : Ctx} {A B m : Tm}
    (TA : CanTypeData Γ A) :
    TA.CanSemTm m -> (TA.weaken (B := B)).CanSemTm m.[shift 1] := by
  intro hm Δ hΓB
  rcases hΓB with ⟨_hSem, hCan⟩
  cases hCan with
  | cons hTail TB =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    change (TypeInterp.weakenCtx (TA.interp hTailCtx)
      (TB.interp hTailCtx.semCtx)).SemTm m.[shift 1]
    exact TypeInterp.semTm_weakenCtx (TA.interp hTailCtx)
      (TB.interp hTailCtx.semCtx) (hm hTailCtx)
  | consInterp hTail I _hI =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    change (TypeInterp.weakenCtx (TA.interp hTailCtx) I).SemTm m.[shift 1]
    exact TypeInterp.semTm_weakenCtx (TA.interp hTailCtx) I (hm hTailCtx)

lemma weaken_expansive {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) :
    TA.Expansive -> (TA.weaken (B := B)).Expansive := by
  intro hTA Δ hΓB σ hσ
  rcases hΓB with ⟨_hSem, hCan⟩
  cases hCan with
  | cons hTail TB =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    change Candidate.Expansive
      ((TA.interp hTailCtx).cand (fun x => σ (x + 1)))
    exact hTA hTailCtx (fun x => σ (x + 1)) hσ.1
  | consInterp hTail I _hI =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    change Candidate.Expansive
      ((TA.interp hTailCtx).cand (fun x => σ (x + 1)))
    exact hTA hTailCtx (fun x => σ (x + 1)) hσ.1

lemma weaken_equiv {Γ : Ctx} {A B : Tm}
    {TA TB : CanTypeData Γ A} :
    CanTypeData.Equiv TA TB ->
    CanTypeData.Equiv (CanTypeData.weaken (B := B) TA)
      (CanTypeData.weaken (B := B) TB) := by
  intro hEq Δ hΓB σ hσ t
  rcases hΓB with ⟨_hSem, hCan⟩
  cases hCan with
  | cons hTail TH =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    change ((TA.interp hTailCtx).cand (fun x => σ (x + 1))).mem t ↔
      ((TB.interp hTailCtx).cand (fun x => σ (x + 1))).mem t
    exact hEq hTailCtx (fun x => σ (x + 1)) hσ.1 t
  | consInterp hTail I _hI =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    change ((TA.interp hTailCtx).cand (fun x => σ (x + 1))).mem t ↔
      ((TB.interp hTailCtx).cand (fun x => σ (x + 1))).mem t
    exact hEq hTailCtx (fun x => σ (x + 1)) hσ.1 t

lemma weaken_var {Γ : Ctx} {A B : Tm} {x : Var}
    (TA : CanTypeData Γ A) :
    TA.CanSemTm (.var x) ->
    (CanTypeData.weaken (B := B) TA).CanSemTm (.var (x + 1)) := by
  intro hvar Δ hΓ
  have h := CanTypeData.weaken_semTm (B := B) TA hvar hΓ
  simpa using h

noncomputable def varZero (Γ : Ctx) (A : Tm) :
    CanTypeData (A :: Γ) A.[shift 1] where
  interp {Δ} hΓA := by
    rcases hΓA with ⟨_hSem, hCan⟩
    cases hCan with
    | cons hTail TA =>
      let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
      let I := TA.interp hTailCtx.semCtx
      exact TypeInterp.weakenCtx I I
    | consInterp hTail I _hI =>
      exact TypeInterp.weakenCtx I I
  weakens {Δ} hΓA := by
    rcases hΓA with ⟨_hSem, hCan⟩
    cases hCan with
    | cons hTail TA =>
      let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
      let I := TA.interp hTailCtx.semCtx
      change (TypeInterp.weakenCtx I I).Weakens
      exact TypeInterp.weakenCtx_weakens (TA.weakens hTailCtx.semCtx)
    | consInterp hTail I hI =>
      change (TypeInterp.weakenCtx I I).Weakens
      exact TypeInterp.weakenCtx_weakens hI

lemma varZero_semTm (Γ : Ctx) (A : Tm) :
    (CanTypeData.varZero Γ A).CanSemTm (.var 0) := by
  intro Δ hΓA
  rcases hΓA with ⟨_hSem, hCan⟩
  cases hCan with
  | cons hTail TA =>
    let hTailCtx : CanSemCtx Γ _ := ⟨_, hTail⟩
    let I := TA.interp hTailCtx.semCtx
    change (TypeInterp.weakenCtx I I).SemTm (.var 0)
    exact TypeInterp.semVarZero I
  | consInterp hTail I hI =>
    change (TypeInterp.weakenCtx I I).SemTm (.var 0)
    exact TypeInterp.semVarZero I

inductive Lookup : ∀ {Γ : Ctx} {x : Var} {A : Tm},
    Has Γ x A -> CanTypeData Γ A -> Prop where
  | zero (Γ : Ctx) (A : Tm) :
    Lookup (Has.zero Γ A) (CanTypeData.varZero Γ A)
  | succ {Γ : Ctx} {A B : Tm} {x : Var} {hs : Has Γ x A}
      {TA : CanTypeData Γ A} :
    Lookup hs TA ->
    Lookup (Has.succ Γ A B x hs) (CanTypeData.weaken (B := B) TA)

namespace Lookup

lemma semTm {Γ : Ctx} {x : Var} {A : Tm} {hs : Has Γ x A}
    {TA : CanTypeData Γ A} :
    CanTypeData.Lookup hs TA -> TA.CanSemTm (.var x) := by
  intro h
  induction h with
  | zero Γ A =>
    exact CanTypeData.varZero_semTm Γ A
  | succ h ih =>
    exact CanTypeData.weaken_var _ ih

end Lookup

lemma exists_lookup {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) :
    ∃ TA : CanTypeData Γ A, CanTypeData.Lookup hs TA := by
  induction hs with
  | zero Γ A =>
    exact ⟨CanTypeData.varZero Γ A, CanTypeData.Lookup.zero Γ A⟩
  | succ Γ A B x hs ih =>
    rcases ih with ⟨TA, hTA⟩
    exact ⟨CanTypeData.weaken (B := B) TA,
      CanTypeData.Lookup.succ hTA⟩

noncomputable def lookup {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) : CanTypeData Γ A :=
  Classical.choose (CanTypeData.exists_lookup hs)

lemma lookup_spec {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) :
    CanTypeData.Lookup hs (CanTypeData.lookup hs) :=
  Classical.choose_spec (CanTypeData.exists_lookup hs)

lemma lookup_var {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) :
    (CanTypeData.lookup hs).CanSemTm (.var x) :=
  CanTypeData.Lookup.semTm (CanTypeData.lookup_spec hs)

noncomputable def ofCanSemTypedType {Γ : Ctx} {A : Tm} {i : Nat}
    (hA : CanSemTyped Γ A (.ty i)) : CanTypeData Γ A where
  interp hΓ := TypeInterp.const _ A Candidate.snCandidate
    (fun σ hσ => CanSemTyped.sn_subst hA hΓ σ hσ)
  weakens _hΓ := TypeInterp.const_weakens Candidate.snCandidate_weakens

lemma ofCanSemTypedType_expansive {Γ : Ctx} {A : Tm} {i : Nat}
    (hA : CanSemTyped Γ A (.ty i)) :
    (CanTypeData.ofCanSemTypedType hA).Expansive := by
  intro Δ hΓ
  exact TypeInterp.const_expansive Candidate.snCandidate_expansive

def univ (Γ : Ctx) (i : Nat) : CanTypeData Γ (.ty i) :=
  CanTypeData.ofSemTypeData (SemTypeData.univ Γ i)

lemma univ_expansive (Γ : Ctx) (i : Nat) :
    (CanTypeData.univ Γ i).Expansive :=
  CanTypeData.ofSemTypeData_expansive (SemTypeData.univ Γ i)
    (SemTypeData.univ_expansive Γ i)

def bool (Γ : Ctx) : CanTypeData Γ .bool :=
  CanTypeData.ofSemTypeData (SemTypeData.bool Γ)

lemma bool_expansive (Γ : Ctx) :
    (CanTypeData.bool Γ).Expansive :=
  CanTypeData.ofSemTypeData_expansive (SemTypeData.bool Γ)
    (SemTypeData.bool_expansive Γ)

def bot (Γ : Ctx) : CanTypeData Γ .bot :=
  CanTypeData.ofSemTypeData (SemTypeData.bot Γ)

lemma bot_expansive (Γ : Ctx) :
    (CanTypeData.bot Γ).Expansive :=
  CanTypeData.ofSemTypeData_expansive (SemTypeData.bot Γ)
    (SemTypeData.bot_expansive Γ)

lemma type {Γ : Ctx} {A : Tm} (TA : CanTypeData Γ A) (i : Nat) :
    (CanTypeData.univ Γ i).CanSemTm A := by
  intro Δ hΓ
  exact TypeInterp.semUniv (TA.interp hΓ) i

lemma ty {Γ : Ctx} (i : Nat) :
    (CanTypeData.univ Γ (i + 1)).CanSemTm (.ty i) :=
  CanTypeData.type (CanTypeData.univ Γ i) (i + 1)

lemma bool_type {Γ : Ctx} :
    (CanTypeData.univ Γ 0).CanSemTm .bool :=
  CanTypeData.type (CanTypeData.bool Γ) 0

lemma bot_type {Γ : Ctx} :
    (CanTypeData.univ Γ 0).CanSemTm .bot :=
  CanTypeData.type (CanTypeData.bot Γ) 0

lemma tt {Γ : Ctx} :
    (CanTypeData.bool Γ).CanSemTm .tt := by
  intro Δ hΓ
  exact TypeInterp.semTt

lemma ff {Γ : Ctx} :
    (CanTypeData.bool Γ).CanSemTm .ff := by
  intro Δ hΓ
  exact TypeInterp.semFf

noncomputable def idn {Γ : Ctx} {A m n : Tm}
    (TA : CanTypeData Γ A) (hm : TA.CanSemTm m) (hn : TA.CanSemTm n) :
    CanTypeData Γ (.idn A m n) where
  interp hΓ := TypeInterp.idn (TA.interp hΓ) (hm hΓ) (hn hΓ)
  weakens _hΓ := TypeInterp.idn_weakens

lemma idn_expansive {Γ : Ctx} {A m n : Tm}
    (TA : CanTypeData Γ A) (hm : TA.CanSemTm m) (hn : TA.CanSemTm n) :
    (CanTypeData.idn TA hm hn).Expansive := by
  intro Δ hΓ
  change (TypeInterp.idn (TA.interp hΓ) (hm hΓ) (hn hΓ)).Expansive
  exact TypeInterp.idn_expansive (I := TA.interp hΓ)

lemma idn_type {Γ : Ctx} {A m n : Tm}
    (TA : CanTypeData Γ A) (hm : TA.CanSemTm m) (hn : TA.CanSemTm n)
    (i : Nat) :
    (CanTypeData.univ Γ i).CanSemTm (.idn A m n) :=
  CanTypeData.type (CanTypeData.idn TA hm hn) i

lemma idn_equiv {Γ : Ctx} {A B m n m' n' : Tm}
    {TA : CanTypeData Γ A} {TB : CanTypeData Γ B}
    {hm : TA.CanSemTm m} {hn : TA.CanSemTm n}
    {hm' : TB.CanSemTm m'} {hn' : TB.CanSemTm n'} :
    CanTypeData.Equiv
      (CanTypeData.idn TA hm hn)
      (CanTypeData.idn TB hm' hn') := by
  intro Δ hΓ σ hσ t
  rfl

noncomputable def idBranch {Γ : Ctx} {A B a : Tm}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    CanTypeData Γ A.[.rfl a,a/] where
  interp hΓ :=
    let IB := TB.interp hΓ
    let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
      CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : CanSemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    TypeInterp.idBranch IB (ha hΓ) (TA.interp hΓP)
  weakens hΓ := by
    let IB := TB.interp hΓ
    let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
      CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : CanSemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    change (TypeInterp.idBranch IB (ha hΓ) (TA.interp hΓP)).Weakens
    exact TypeInterp.idBranch_weakens IB (ha hΓ) (TA.interp hΓP)
      (TA.weakens hΓP)

lemma idBranch_equiv_same {Γ : Ctx} {A B a : Tm}
    (TB : CanTypeData Γ B) (ha ha' : TB.CanSemTm a)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    CanTypeData.Equiv
      (CanTypeData.idBranch TB ha TA)
      (CanTypeData.idBranch TB ha' TA) := by
  intro Δ hΓ σ hσ t
  simp [CanTypeData.idBranch, TypeInterp.idBranch]

lemma idBranch_equiv_of_family {Γ : Ctx} {A B a : Tm}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a)
    (TA TA' : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    CanTypeData.Equiv TA TA' ->
    CanTypeData.Equiv
      (CanTypeData.idBranch TB ha TA)
      (CanTypeData.idBranch TB ha TA') := by
  intro hA Δ hΓ σ hσ t
  let IB := TB.interp hΓ
  let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : CanSemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  have hvalid :
      (DCandCtx.extend IP).valid
        (TypeInterp.idBranchSubst a σ) :=
    TypeInterp.idBranchSubst_valid IB (ha hΓ) hσ
  simpa [CanTypeData.idBranch, TypeInterp.idBranch] using
    hA hΓP (TypeInterp.idBranchSubst a σ) hvalid t

lemma idBranch_expansive {Γ : Ctx} {A B a : Tm}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    TA.Expansive -> (CanTypeData.idBranch TB ha TA).Expansive := by
  intro hTA Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : CanSemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  change (TypeInterp.idBranch IB (ha hΓ) (TA.interp hΓP)).Expansive
  exact TypeInterp.idBranch_expansive IB (ha hΓ) (TA.interp hΓP) (hTA hΓP)

noncomputable def idTarget {Γ : Ctx} {A B a b n : Tm}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    CanTypeData Γ A.[n,b/] where
  interp hΓ :=
    let IB := TB.interp hΓ
    let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
      CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : CanSemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ) (TA.interp hΓP)
  weakens hΓ := by
    let IB := TB.interp hΓ
    let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
      CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
    let IP := TypeInterp.idProof IB (ha hΓ)
    let hΓP : CanSemCtx
        (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
        (DCandCtx.extend IP) :=
      CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
    change (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ)
      (TA.interp hΓP)).Weakens
    exact TypeInterp.idTarget_weakens IB (ha hΓ) (hb hΓ) (hn hΓ)
      (TA.interp hΓP) (TA.weakens hΓP)

lemma idTarget_equiv_same {Γ : Ctx} {A B a b n : Tm}
    (TB : CanTypeData Γ B)
    (ha ha' : TB.CanSemTm a) (hb hb' : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (hn' : (CanTypeData.idn TB ha' hb').CanSemTm n)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    CanTypeData.Equiv
      (CanTypeData.idTarget TB ha hb hn TA)
      (CanTypeData.idTarget TB ha' hb' hn' TA) := by
  intro Δ hΓ σ hσ t
  simp [CanTypeData.idTarget, TypeInterp.idTarget]

lemma idTarget_equiv_of_family {Γ : Ctx} {A B a b n : Tm}
    (TB : CanTypeData Γ B)
    (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA TA' : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    CanTypeData.Equiv TA TA' ->
    CanTypeData.Equiv
      (CanTypeData.idTarget TB ha hb hn TA)
      (CanTypeData.idTarget TB ha hb hn TA') := by
  intro hA Δ hΓ σ hσ t
  let IB := TB.interp hΓ
  let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : CanSemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  have hvalid :
      (DCandCtx.extend IP).valid
        (TypeInterp.idTargetSubst b n σ) :=
    TypeInterp.idTargetSubst_valid IB (ha hΓ) (hb hΓ) (hn hΓ) hσ
  simpa [CanTypeData.idTarget, TypeInterp.idTarget] using
    hA hΓP (TypeInterp.idTargetSubst b n σ) hvalid t

lemma idTarget_expansive {Γ : Ctx} {A B a b n : Tm}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    TA.Expansive -> (CanTypeData.idTarget TB ha hb hn TA).Expansive := by
  intro hTA Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : CanSemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  change (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ)
    (TA.interp hΓP)).Expansive
  exact TypeInterp.idTarget_expansive IB (ha hΓ) (hb hΓ) (hn hΓ)
    (TA.interp hΓP) (hTA hΓP)

noncomputable def kpi {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive) : CanTypeData Γ (.pi A B) where
  interp hΓ :=
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    TypeInterp.kpi IA (TB.interp hΓA) (CanSemCtx.weakens hΓ) (hTB hΓA)
  weakens hΓ := by
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    change (TypeInterp.kpi IA (TB.interp hΓA)
      (CanSemCtx.weakens hΓ) (hTB hΓA)).Weakens
    exact TypeInterp.kpi_weakens IA (TB.interp hΓA)
      (CanSemCtx.weakens hΓ) (hTB hΓA)

noncomputable def ksig {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B) :
    CanTypeData Γ (.sig A B) where
  interp hΓ :=
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    TypeInterp.ksig IA (TB.interp hΓA) (CanSemCtx.weakens hΓ)
  weakens hΓ := by
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    change (TypeInterp.ksig IA (TB.interp hΓA) (CanSemCtx.weakens hΓ)).Weakens
    exact TypeInterp.ksig_weakens IA (TB.interp hΓA) (CanSemCtx.weakens hΓ)

lemma pi_type {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive) (i : Nat) :
    (CanTypeData.univ Γ i).CanSemTm (.pi A B) :=
  CanTypeData.type (CanTypeData.kpi TA TB hTB) i

lemma sig_type {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (i : Nat) :
    (CanTypeData.univ Γ i).CanSemTm (.sig A B) :=
  CanTypeData.type (CanTypeData.ksig TA TB) i

noncomputable def subst1 {Γ : Ctx} {A B n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hn : TA.CanSemTm n) : CanTypeData Γ B.[n/] where
  interp hΓ :=
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    TypeInterp.subst1 IA (TB.interp hΓA) (hn hΓ)
  weakens hΓ := by
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    change (TypeInterp.subst1 IA (TB.interp hΓA) (hn hΓ)).Weakens
    exact TypeInterp.subst1_weakens IA (TB.interp hΓA)
      (TB.weakens hΓA)

lemma kpi_equiv_same {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB hTB' : TB.Expansive) :
    CanTypeData.Equiv
      (CanTypeData.kpi TA TB hTB)
      (CanTypeData.kpi TA TB hTB') := by
  intro Δ hΓ σ hσ t
  simp [CanTypeData.kpi, TypeInterp.kpi, TypeInterp.kpiCandTotal, hσ,
    TypeInterp.kpiCand]

lemma kpi_equiv_of_codomain {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A)
    (TB TB' : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive) (hTB' : TB'.Expansive) :
    CanTypeData.Equiv TB TB' ->
    CanTypeData.Equiv
      (CanTypeData.kpi TA TB hTB)
      (CanTypeData.kpi TA TB' hTB') := by
  intro hB Δ hΓ σ hσ f
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  constructor
  · intro hf
    simp [CanTypeData.kpi, TypeInterp.kpi, TypeInterp.kpiCandTotal, hσ,
      TypeInterp.kpiCand] at hf ⊢
    constructor
    · exact hf.1
    · intro i n hn
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (CanSemCtx.weakens hΓ) hσ i
      have hvalid : (DCandCtx.extend IA).valid (n .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi hn
      exact (hB hΓA (n .: shiftSubst σ i) hvalid (.app f.[shift i] n)).1
        (hf.2 i n hn)
  · intro hf
    simp [CanTypeData.kpi, TypeInterp.kpi, TypeInterp.kpiCandTotal, hσ,
      TypeInterp.kpiCand] at hf ⊢
    constructor
    · exact hf.1
    · intro i n hn
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (CanSemCtx.weakens hΓ) hσ i
      have hvalid : (DCandCtx.extend IA).valid (n .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi hn
      exact (hB hΓA (n .: shiftSubst σ i) hvalid (.app f.[shift i] n)).2
        (hf.2 i n hn)

lemma ksig_equiv_of_codomain {Γ : Ctx} {A B : Tm}
    (TA : CanTypeData Γ A)
    (TB TB' : CanTypeData (A :: Γ) B) :
    CanTypeData.Equiv TB TB' ->
    CanTypeData.Equiv
      (CanTypeData.ksig TA TB)
      (CanTypeData.ksig TA TB') := by
  intro hB Δ hΓ σ hσ p
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  constructor
  · intro hp
    simp [CanTypeData.ksig, TypeInterp.ksig, TypeInterp.ksigCandTotal, hσ,
      TypeInterp.ksigCand] at hp ⊢
    constructor
    · exact hp.1
    · intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (CanSemCtx.weakens hΓ) hσ i
      rcases hp.2 i a b rd with ⟨ha, hb⟩
      have hvalid : (DCandCtx.extend IA).valid (a .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi ha
      exact ⟨ha, (hB hΓA (a .: shiftSubst σ i) hvalid b).1 hb⟩
  · intro hp
    simp [CanTypeData.ksig, TypeInterp.ksig, TypeInterp.ksigCandTotal, hσ,
      TypeInterp.ksigCand] at hp ⊢
    constructor
    · exact hp.1
    · intro i a b rd
      have hσi : Δ.valid (shiftSubst σ i) :=
        DCandCtx.weakens_iter (CanSemCtx.weakens hΓ) hσ i
      rcases hp.2 i a b rd with ⟨ha, hb⟩
      have hvalid : (DCandCtx.extend IA).valid (a .: shiftSubst σ i) :=
        DCandCtx.extend_cons hσi ha
      exact ⟨ha, (hB hΓA (a .: shiftSubst σ i) hvalid b).2 hb⟩

noncomputable def sigmaBranchInterp {Γ : Ctx} {A B C : Tm}
    (TC : CanTypeData (.sig A B :: Γ) C)
    {Δ : DCandCtx} (hΓBA : CanSemCtx (B :: A :: Γ) Δ) :
    TypeInterp Δ C.[.tup (.var 1) (.var 0) .: shift 2] := by
  rcases hΓBA with ⟨_hSemBA, hCanBA⟩
  cases hCanBA with
  | cons hΓA_core TB =>
    cases hΓA_core with
    | cons hΓ_core TA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let IA := TA.interp hΓ.semCtx
      let hSemA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ.semCtx IA (TA.weakens hΓ.semCtx)
      let IB := TB.interp hSemA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      exact TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ)
        (TA.weakens hΓ.semCtx) (TB.weakens hSemA) (TC.interp hΓS)
    | consInterp hΓ_core IA hIA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let hSemA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ.semCtx IA hIA
      let IB := TB.interp hSemA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      exact TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ)
        hIA (TB.weakens hSemA) (TC.interp hΓS)
  | consInterp hΓA_core IB hIB =>
    cases hΓA_core with
    | cons hΓ_core TA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let IA := TA.interp hΓ.semCtx
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      exact TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ)
        (TA.weakens hΓ.semCtx) hIB (TC.interp hΓS)
    | consInterp hΓ_core IA hIA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      exact TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ)
        hIA hIB (TC.interp hΓS)

lemma sigmaBranchInterp_weakens {Γ : Ctx} {A B C : Tm}
    (TC : CanTypeData (.sig A B :: Γ) C)
    {Δ : DCandCtx} (hΓBA : CanSemCtx (B :: A :: Γ) Δ) :
    (CanTypeData.sigmaBranchInterp TC hΓBA).Weakens := by
  intro σ m hσ hm
  rcases hΓBA with ⟨_hSemBA, hCanBA⟩
  cases hCanBA with
  | cons hΓA_core TB =>
    cases hΓA_core with
    | cons hΓ_core TA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let IA := TA.interp hΓ.semCtx
      let hSemA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ.semCtx IA (TA.weakens hΓ.semCtx)
      let IB := TB.interp hSemA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      dsimp [CanTypeData.sigmaBranchInterp] at hm ⊢
      exact TypeInterp.sigmaBranch_weakens IA IB (CanSemCtx.weakens hΓ)
        (TA.weakens hΓ.semCtx) (TB.weakens hSemA)
        (TC.interp hΓS) (TC.weakens hΓS) hσ hm
    | consInterp hΓ_core IA hIA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let hSemA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ.semCtx IA hIA
      let IB := TB.interp hSemA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      dsimp [CanTypeData.sigmaBranchInterp] at hm ⊢
      exact TypeInterp.sigmaBranch_weakens IA IB (CanSemCtx.weakens hΓ)
        hIA (TB.weakens hSemA) (TC.interp hΓS) (TC.weakens hΓS) hσ hm
  | consInterp hΓA_core IB hIB =>
    cases hΓA_core with
    | cons hΓ_core TA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let IA := TA.interp hΓ.semCtx
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      dsimp [CanTypeData.sigmaBranchInterp] at hm ⊢
      exact TypeInterp.sigmaBranch_weakens IA IB (CanSemCtx.weakens hΓ)
        (TA.weakens hΓ.semCtx) hIB (TC.interp hΓS) (TC.weakens hΓS) hσ hm
    | consInterp hΓ_core IA hIA =>
      let hΓ : CanSemCtx Γ _ := ⟨_, hΓ_core⟩
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      dsimp [CanTypeData.sigmaBranchInterp] at hm ⊢
      exact TypeInterp.sigmaBranch_weakens IA IB (CanSemCtx.weakens hΓ)
        hIA hIB (TC.interp hΓS) (TC.weakens hΓS) hσ hm

noncomputable def sigmaBranch {Γ : Ctx} {A B C : Tm}
    (TC : CanTypeData (.sig A B :: Γ) C) :
    CanTypeData (B :: A :: Γ) C.[.tup (.var 1) (.var 0) .: shift 2] where
  interp hΓBA := CanTypeData.sigmaBranchInterp TC hΓBA
  weakens hΓBA := CanTypeData.sigmaBranchInterp_weakens TC hΓBA

lemma subst1_equiv_same {Γ : Ctx} {A B n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hn hn' : TA.CanSemTm n) :
    CanTypeData.Equiv
      (CanTypeData.subst1 TA TB hn)
      (CanTypeData.subst1 TA TB hn') := by
  intro Δ hΓ σ hσ t
  simp [CanTypeData.subst1, TypeInterp.subst1]

lemma subst1_equiv_of_family {Γ : Ctx} {A B n : Tm}
    (TA : CanTypeData Γ A)
    (TB TB' : CanTypeData (A :: Γ) B)
    (hn : TA.CanSemTm n) :
    CanTypeData.Equiv TB TB' ->
    CanTypeData.Equiv
      (CanTypeData.subst1 TA TB hn)
      (CanTypeData.subst1 TA TB' hn) := by
  intro hB Δ hΓ σ hσ t
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  have hvalid : (DCandCtx.extend IA).valid (n.[σ] .: σ) :=
    DCandCtx.extend_cons hσ (hn hΓ σ hσ)
  simpa [CanTypeData.subst1, TypeInterp.subst1] using
    hB hΓA (n.[σ] .: σ) hvalid t

lemma subst1_equiv {Γ : Ctx} {A B n : Tm}
    (TA : CanTypeData Γ A)
    (TB TB' : CanTypeData (A :: Γ) B)
    (hn hn' : TA.CanSemTm n) :
    CanTypeData.Equiv TB TB' ->
    CanTypeData.Equiv
      (CanTypeData.subst1 TA TB hn)
      (CanTypeData.subst1 TA TB' hn') := by
  intro hB
  exact CanTypeData.Equiv.trans
    (CanTypeData.subst1_equiv_same TA TB hn hn')
    (CanTypeData.subst1_equiv_of_family TA TB TB' hn' hB)

lemma subst1_expansive {Γ : Ctx} {A B n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hn : TA.CanSemTm n) :
    TB.Expansive -> (CanTypeData.subst1 TA TB hn).Expansive := by
  intro hTB Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  change (TypeInterp.subst1 IA (TB.interp hΓA) (hn hΓ)).Expansive
  exact TypeInterp.subst1_expansive IA (TB.interp hΓA)
    (hn := hn hΓ) (hTB hΓA)

lemma lamKPi {Γ : Ctx} {A B m : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive) :
    TB.CanSemTm m ->
    (CanTypeData.kpi TA TB hTB).CanSemTm (.lam A m) := by
  intro hm Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  change (TypeInterp.kpi IA IB (CanSemCtx.weakens hΓ) (hTB hΓA)).SemTm (.lam A m)
  apply TypeInterp.semLamKPiInterp IA IB (CanSemCtx.weakens hΓ) (hTB hΓA)
  · intro σ hσ
    exact IA.type_sn σ hσ
  · intro σ hσ
    have hσup : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) (CanSemCtx.weakens hΓ) hσ
    exact (IB.cand (up σ)).sn (hm hΓA (up σ) hσup)
  · intro σ hσ a ha
    exact hm hΓA (a .: σ) (DCandCtx.extend_cons hσ ha)

lemma appKPi {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (hm : (CanTypeData.kpi TA TB hTB).CanSemTm m)
    (hn : TA.CanSemTm n) :
    (CanTypeData.subst1 TA TB hn).CanSemTm (.app m n) := by
  intro Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  let hnI : IA.SemTm n := hn hΓ
  change (TypeInterp.subst1 IA IB hnI).SemTm (.app m n)
  exact TypeInterp.semAppKPiSubst1 IA IB (CanSemCtx.weakens hΓ)
    (hTB hΓA) (hm hΓ) hnI

lemma tupKSig {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hm : TA.CanSemTm m)
    (hn : (CanTypeData.subst1 TA TB hm).CanSemTm n) :
    (CanTypeData.ksig TA TB).CanSemTm (.tup m n) := by
  intro Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  change (TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)).SemTm (.tup m n)
  apply TypeInterp.semTupKSigmaInterp IA IB (CanSemCtx.weakens hΓ)
  · exact hm hΓ
  · intro σ hσ
    exact hn hΓ σ hσ

lemma prj_branch {Γ : Ctx} {A B C m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (hm : (CanTypeData.ksig TA TB).CanSemTm m)
    (hn : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
        CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    (CanTypeData.subst1 (CanTypeData.ksig TA TB) TC hm).CanSemTm
      (.prj C m n) := by
  intro Δ hΓ
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
  let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
    CanSemCtx.consInterp hΓ K
      (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
  change (TypeInterp.subst1 K (TC.interp hΓS) (hm hΓ)).SemTm
    (.prj C m n)
  exact TypeInterp.semPrjKSigmaSubst1_branch IA IB (CanSemCtx.weakens hΓ)
    (TA.weakens hΓ) (TB.weakens hΓA) (TC.interp hΓS) (hTC hΓS)
    (hm hΓ) (hn hΓ)

lemma iteBool {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : CanTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (hm : (CanTypeData.bool Γ).CanSemTm m)
    (hn1 : (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.tt).CanSemTm n1)
    (hn2 : (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.ff).CanSemTm n2) :
    (CanTypeData.subst1 (CanTypeData.bool Γ) TB hm).CanSemTm
      (.ite A m n1 n2) := by
  intro Δ hΓ
  let hΓB : CanSemCtx (.bool :: Γ) (DCandCtx.extend (TypeInterp.bool Δ)) :=
    CanSemCtx.consInterp hΓ (TypeInterp.bool Δ) (TypeInterp.bool_weakens Δ)
  let IB := TB.interp hΓB
  change (TypeInterp.subst1 (TypeInterp.bool Δ) IB (hm hΓ)).SemTm
    (.ite A m n1 n2)
  exact TypeInterp.semIteBoolSubst1 IB (CanSemCtx.weakens hΓ) (hTB hΓB)
    (hm hΓ) (hn1 hΓ) (hn2 hΓ)

lemma exfBot {Γ : Ctx} {A m : Tm}
    (TB : CanTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (hm : (CanTypeData.bot Γ).CanSemTm m) :
    (CanTypeData.subst1 (CanTypeData.bot Γ) TB hm).CanSemTm
      (.exf A m) := by
  intro Δ hΓ
  let hΓB : CanSemCtx (.bot :: Γ) (DCandCtx.extend (TypeInterp.bot Δ)) :=
    CanSemCtx.consInterp hΓ (TypeInterp.bot Δ) (TypeInterp.bot_weakens Δ)
  let IB := TB.interp hΓB
  change (TypeInterp.subst1 (TypeInterp.bot Δ) IB (hm hΓ)).SemTm (.exf A m)
  exact TypeInterp.semExfBotSubst1 IB (CanSemCtx.weakens hΓ) (hTB hΓB) (hm hΓ)

lemma rw_target {Γ : Ctx} {A B m n a b : Tm}
    (TB : CanTypeData Γ B)
    (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hTA : TA.Expansive)
    (hrfl : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IB := TB.interp hΓ
      let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
        CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
      let IP := TypeInterp.idProof IB (ha hΓ)
      let hΓP : CanSemCtx
          (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
          (DCandCtx.extend IP) :=
        CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
      let IA := TA.interp hΓP
      ∀ σ, Δ.valid σ -> ∀ c,
        (IA.cand (.rfl c .: b.[σ] .: σ)).mem m.[σ]) :
    (CanTypeData.idTarget TB ha hb hn TA).CanSemTm (.rw A m n) := by
  intro Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : CanSemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  let IA := TA.interp hΓP
  change (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ) IA).SemTm
    (.rw A m n)
  exact TypeInterp.semRwTarget IB (CanSemCtx.weakens hΓ) (TB.weakens hΓ)
    (ha hΓ) (hb hΓ) (hn hΓ) IA (hTA hΓP) (hrfl hΓ)

lemma rw_sn {Γ : Ctx} {A B m n a b : Tm}
    (TB : CanTypeData Γ B)
    (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hm : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IB := TB.interp hΓ
      let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
        CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
      let IP := TypeInterp.idProof IB (ha hΓ)
      let hΓP : CanSemCtx
          (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
          (DCandCtx.extend IP) :=
        CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
      let IA := TA.interp hΓP
      (TypeInterp.idBranch IB (ha hΓ) IA).SemTm m) :
    CanSemTyped Γ (.rw A m n) A.[n,b/] := by
  intro Δ hΓ
  let IB := TB.interp hΓ
  let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
  let IP := TypeInterp.idProof IB (ha hΓ)
  let hΓP : CanSemCtx
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
      (DCandCtx.extend IP) :=
    CanSemCtx.consInterp hΓB IP (TypeInterp.idProof_weakens IB (ha hΓ))
  let IA := TA.interp hΓP
  refine ⟨TypeInterp.const Δ A.[n,b/] Candidate.snCandidate
      (fun σ hσ => (TypeInterp.idTarget IB (ha hΓ) (hb hΓ) (hn hΓ) IA).type_sn σ hσ),
    TypeInterp.const_weakens Candidate.snCandidate_weakens, ?_⟩
  exact TypeInterp.semRwTargetSN IB (CanSemCtx.weakens hΓ) (TB.weakens hΓ)
    (ha hΓ) (hb hΓ) (hn hΓ) IA (hm hΓ)

lemma rw_sn_branch {Γ : Ctx} {A B m n a b : Tm}
    (TB : CanTypeData Γ B)
    (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A) :
    (CanTypeData.idBranch TB ha TA).CanSemTm m ->
    CanSemTyped Γ (.rw A m n) A.[n,b/] := by
  intro hm
  apply CanTypeData.rw_sn TB ha hb hn TA
  intro Δ hΓ
  exact hm hΓ

end CanTypeData

structure CanTermData (Γ : Ctx) (m A : Tm) where
  typeData : CanTypeData Γ A
  canSemTm : typeData.CanSemTm m

structure CanTypeJudgment (Γ : Ctx) (A : Tm) (i : Nat) where
  typeData : CanTypeData Γ A
  inUniv : (CanTypeData.univ Γ i).CanSemTm A

namespace CanTermData

lemma toCanSemTyped {Γ : Ctx} {m A : Tm} (J : CanTermData Γ m A) :
    CanSemTyped Γ m A := by
  intro Δ hΓ
  exact ⟨J.typeData.interp hΓ, J.typeData.weakens hΓ, J.canSemTm hΓ⟩

def ofTypeData {Γ : Ctx} {m A : Tm}
    (TA : CanTypeData Γ A) (hm : TA.CanSemTm m) :
    CanTermData Γ m A where
  typeData := TA
  canSemTm := hm

noncomputable def weaken {Γ : Ctx} {m A B : Tm}
    (J : CanTermData Γ m A) : CanTermData (B :: Γ) m.[shift 1] A.[shift 1] where
  typeData := CanTypeData.weaken (B := B) J.typeData
  canSemTm := CanTypeData.weaken_semTm J.typeData J.canSemTm

def retagCanEquiv {Γ : Ctx} {A B m : Tm}
    (J : CanTermData Γ m A) (TB : CanTypeData Γ B)
    (hEq : CanTypeData.Equiv J.typeData TB) :
    CanTermData Γ m B where
  typeData := TB
  canSemTm := CanTypeData.Equiv.semTm hEq J.canSemTm

def convType {Γ : Ctx} {A B m : Tm} (J : CanTermData Γ m A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    CanTermData Γ m B where
  typeData := J.typeData.convType hB
  canSemTm := J.typeData.convType_semTm hB J.canSemTm

def retagWeak {Γ : Ctx} {A B m : Tm}
    (J : CanTermData Γ m A) (TB : CanTypeData Γ B) :
    CanTermData Γ m B :=
  J.convType (fun hΓ σ hσ => (TB.interp hΓ).type_sn σ hσ)

lemma retagWeak_equiv_source {Γ : Ctx} {A B m : Tm}
    (J : CanTermData Γ m A) (TB : CanTypeData Γ B) :
    CanTypeData.Equiv (J.retagWeak TB).typeData J.typeData :=
  CanTypeData.convType_equiv_left J.typeData
    (fun hΓ σ hσ => (TB.interp hΓ).type_sn σ hσ)

lemma source_equiv_retagWeak {Γ : Ctx} {A B m : Tm}
    (J : CanTermData Γ m A) (TB : CanTypeData Γ B) :
    CanTypeData.Equiv J.typeData (J.retagWeak TB).typeData :=
  CanTypeData.convType_equiv_right J.typeData
    (fun hΓ σ hσ => (TB.interp hΓ).type_sn σ hσ)

noncomputable def retagTypeJudgment {Γ : Ctx} {A B m : Tm} {i : Nat}
    (J : CanTermData Γ m A) (TB : CanTypeJudgment Γ B i) :
    CanTermData Γ m B :=
  J.retagWeak TB.typeData

lemma retagTypeJudgment_equiv_source {Γ : Ctx} {A B m : Tm} {i : Nat}
    (J : CanTermData Γ m A) (TB : CanTypeJudgment Γ B i) :
    CanTypeData.Equiv (J.retagTypeJudgment TB).typeData J.typeData :=
  J.retagWeak_equiv_source TB.typeData

lemma retagTypeJudgment_equiv_trans {Γ : Ctx} {A B C m : Tm} {i : Nat}
    (J : CanTermData Γ m A) (TB : CanTypeJudgment Γ B i)
    (TC : CanTypeData Γ C) :
    CanTypeData.Equiv J.typeData TC ->
    CanTypeData.Equiv (J.retagTypeJudgment TB).typeData TC :=
  fun hEq => CanTypeData.Equiv.trans (J.retagTypeJudgment_equiv_source TB) hEq

noncomputable def rfl {Γ : Ctx} {A m : Tm}
    (J : CanTermData Γ m A) :
    CanTermData Γ (.rfl m) (.idn A m m) where
  typeData := CanTypeData.idn J.typeData J.canSemTm J.canSemTm
  canSemTm := by
    intro Δ hΓ
    exact TypeInterp.semRfl (J.canSemTm hΓ)

noncomputable def lam {Γ : Ctx} {A B m : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanTermData (A :: Γ) m B)
    (hmEq : CanTypeData.Equiv Jm.typeData TB) :
    CanTermData Γ (.lam A m) (.pi A B) where
  typeData := CanTypeData.kpi TA TB hTB
  canSemTm := CanTypeData.lamKPi TA TB hTB
    (CanTypeData.Equiv.semTm hmEq Jm.canSemTm)

noncomputable def app {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanTermData Γ m (.pi A B)) (Jn : CanTermData Γ n A)
    (hmEq : CanTypeData.Equiv Jm.typeData (CanTypeData.kpi TA TB hTB))
    (hnEq : CanTypeData.Equiv Jn.typeData TA) :
    CanTermData Γ (.app m n) B.[n/] := by
  let hn : TA.CanSemTm n := CanTypeData.Equiv.semTm hnEq Jn.canSemTm
  exact
    { typeData := CanTypeData.subst1 TA TB hn
      canSemTm := CanTypeData.appKPi TA TB hTB
        (CanTypeData.Equiv.semTm hmEq Jm.canSemTm) hn }

noncomputable def appRetagByEquiv {Γ : Ctx} {P A B m n : Tm} {iP : Nat}
    (TP : CanTypeJudgment Γ (.pi A B) iP)
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanTermData Γ m P) (Jn : CanTermData Γ n A)
    (hmEq : CanTypeData.Equiv Jm.typeData (CanTypeData.kpi TA TB hTB))
    (hnEq : CanTypeData.Equiv Jn.typeData TA) :
    CanTermData Γ (.app m n) B.[n/] :=
  CanTermData.app TA TB hTB (Jm.retagTypeJudgment TP) Jn
    (Jm.retagTypeJudgment_equiv_trans TP (CanTypeData.kpi TA TB hTB) hmEq)
    hnEq

noncomputable def tup {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (Jm : CanTermData Γ m A) (Jn : CanTermData Γ n B.[m/])
    (hmEq : CanTypeData.Equiv Jm.typeData TA)
    (hnEq : CanTypeData.Equiv Jn.typeData
      (CanTypeData.subst1 TA TB
        (CanTypeData.Equiv.semTm hmEq Jm.canSemTm))) :
    CanTermData Γ (.tup m n) (.sig A B) where
  typeData := CanTypeData.ksig TA TB
  canSemTm := CanTypeData.tupKSig TA TB
    (CanTypeData.Equiv.semTm hmEq Jm.canSemTm)
    (CanTypeData.Equiv.semTm hnEq Jn.canSemTm)

noncomputable def ite {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : CanTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanTermData Γ m .bool)
    (Jn1 : CanTermData Γ n1 A.[.tt/])
    (Jn2 : CanTermData Γ n2 A.[.ff/])
    (hmEq : CanTypeData.Equiv Jm.typeData (CanTypeData.bool Γ))
    (hn1Eq : CanTypeData.Equiv Jn1.typeData
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.tt))
    (hn2Eq : CanTypeData.Equiv Jn2.typeData
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.ff)) :
    CanTermData Γ (.ite A m n1 n2) A.[m/] := by
  let hm : (CanTypeData.bool Γ).CanSemTm m :=
    CanTypeData.Equiv.semTm hmEq Jm.canSemTm
  exact
    { typeData := CanTypeData.subst1 (CanTypeData.bool Γ) TB hm
      canSemTm := CanTypeData.iteBool TB hTB hm
        (CanTypeData.Equiv.semTm hn1Eq Jn1.canSemTm)
        (CanTypeData.Equiv.semTm hn2Eq Jn2.canSemTm) }

noncomputable def exf {Γ : Ctx} {A m : Tm}
    (TB : CanTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanTermData Γ m .bot)
    (hmEq : CanTypeData.Equiv Jm.typeData (CanTypeData.bot Γ)) :
    CanTermData Γ (.exf A m) A.[m/] := by
  let hm : (CanTypeData.bot Γ).CanSemTm m :=
    CanTypeData.Equiv.semTm hmEq Jm.canSemTm
  exact
    { typeData := CanTypeData.subst1 (CanTypeData.bot Γ) TB hm
      canSemTm := CanTypeData.exfBot TB hTB hm }

end CanTermData

structure CanTermDataAt (Γ : Ctx) (m A : Tm) (TA : CanTypeData Γ A) where
  termData : CanTermData Γ m A
  equiv : CanTypeData.Equiv termData.typeData TA

namespace CanTermDataAt

def ofTermData {Γ : Ctx} {m A : Tm}
    (TA : CanTypeData Γ A) (J : CanTermData Γ m A)
    (hEq : CanTypeData.Equiv J.typeData TA) :
    CanTermDataAt Γ m A TA where
  termData := J
  equiv := hEq

def ofTypeData {Γ : Ctx} {m A : Tm}
    (TA : CanTypeData Γ A) (hm : TA.CanSemTm m) :
    CanTermDataAt Γ m A TA :=
  CanTermDataAt.ofTermData TA (CanTermData.ofTypeData TA hm)
    (CanTypeData.Equiv.refl TA)

def toTermData {Γ : Ctx} {m A : Tm} {TA : CanTypeData Γ A}
    (J : CanTermDataAt Γ m A TA) : CanTermData Γ m A :=
  J.termData

lemma canSemTm {Γ : Ctx} {m A : Tm} {TA : CanTypeData Γ A}
    (J : CanTermDataAt Γ m A TA) : TA.CanSemTm m :=
  CanTypeData.Equiv.semTm J.equiv J.termData.canSemTm

def retag {Γ : Ctx} {m A : Tm} {TA TB : CanTypeData Γ A}
    (J : CanTermDataAt Γ m A TA)
    (hEq : CanTypeData.Equiv TA TB) :
    CanTermDataAt Γ m A TB :=
  CanTermDataAt.ofTermData TB J.termData
    (CanTypeData.Equiv.trans J.equiv hEq)

def convType {Γ : Ctx} {A B m : Tm} {TA : CanTypeData Γ A}
    (J : CanTermDataAt Γ m A TA)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    CanTermDataAt Γ m B (TA.convType hB) :=
  CanTermDataAt.ofTermData (TA.convType hB)
    (J.termData.convType hB)
    (CanTypeData.convType_equiv_of_equiv J.equiv hB hB)

noncomputable def weaken {Γ : Ctx} {m A B : Tm} {TA : CanTypeData Γ A}
    (J : CanTermDataAt Γ m A TA) :
    CanTermDataAt (B :: Γ) m.[shift 1] A.[shift 1]
      (CanTypeData.weaken (B := B) TA) :=
  CanTermDataAt.ofTermData (CanTypeData.weaken (B := B) TA)
    (CanTermData.weaken (B := B) J.termData)
    (CanTypeData.weaken_equiv (B := B) J.equiv)

noncomputable def varZero {Γ : Ctx} {A : Tm} :
    CanTermDataAt (A :: Γ) (.var 0) A.[shift 1]
      (CanTypeData.varZero Γ A) :=
  CanTermDataAt.ofTypeData (CanTypeData.varZero Γ A)
    (CanTypeData.varZero_semTm Γ A)

noncomputable def varSucc {Γ : Ctx} {A B : Tm} {x : Var}
    {TA : CanTypeData Γ A}
    (J : CanTermDataAt Γ (.var x) A TA) :
    CanTermDataAt (B :: Γ) (.var (x + 1)) A.[shift 1]
      (CanTypeData.weaken (B := B) TA) :=
  CanTermDataAt.ofTypeData (CanTypeData.weaken (B := B) TA)
    (CanTypeData.weaken_var TA J.canSemTm)

noncomputable def rfl {Γ : Ctx} {A m : Tm}
    (TA : CanTypeData Γ A)
    (Jm : CanTermDataAt Γ m A TA) :
    CanTermDataAt Γ (.rfl m) (.idn A m m)
      (CanTypeData.idn TA Jm.canSemTm Jm.canSemTm) :=
  let Jm' := Jm.termData.retagCanEquiv TA Jm.equiv
  CanTermDataAt.ofTermData
    (CanTypeData.idn TA Jm.canSemTm Jm.canSemTm)
    (CanTermData.rfl Jm')
    (CanTypeData.Equiv.refl (CanTypeData.idn TA Jm.canSemTm Jm.canSemTm))

noncomputable def lam {Γ : Ctx} {A B m : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanTermDataAt (A :: Γ) m B TB) :
    CanTermDataAt Γ (.lam A m) (.pi A B) (CanTypeData.kpi TA TB hTB) :=
  CanTermDataAt.ofTermData (CanTypeData.kpi TA TB hTB)
    (CanTermData.lam TA TB hTB Jm.termData Jm.equiv)
    (CanTypeData.Equiv.refl (CanTypeData.kpi TA TB hTB))

noncomputable def app {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanTermDataAt Γ m (.pi A B) (CanTypeData.kpi TA TB hTB))
    (Jn : CanTermDataAt Γ n A TA) :
    CanTermDataAt Γ (.app m n) B.[n/]
      (CanTypeData.subst1 TA TB Jn.canSemTm) :=
  CanTermDataAt.ofTermData
    (CanTypeData.subst1 TA TB Jn.canSemTm)
    (CanTermData.app TA TB hTB Jm.termData Jn.termData Jm.equiv Jn.equiv)
    (CanTypeData.Equiv.refl (CanTypeData.subst1 TA TB Jn.canSemTm))

noncomputable def tup {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (Jm : CanTermDataAt Γ m A TA)
    (Jn : CanTermDataAt Γ n B.[m/] (CanTypeData.subst1 TA TB Jm.canSemTm)) :
    CanTermDataAt Γ (.tup m n) (.sig A B) (CanTypeData.ksig TA TB) :=
  CanTermDataAt.ofTermData (CanTypeData.ksig TA TB)
    (CanTermData.tup TA TB Jm.termData Jn.termData Jm.equiv Jn.equiv)
    (CanTypeData.Equiv.refl (CanTypeData.ksig TA TB))

noncomputable def prjBranch {Γ : Ctx} {A B C m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (Jm : CanTermDataAt Γ m (.sig A B) (CanTypeData.ksig TA TB))
    (hn : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
        CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    CanTermDataAt Γ (.prj C m n) C.[m/]
      (CanTypeData.subst1 (CanTypeData.ksig TA TB) TC Jm.canSemTm) :=
  CanTermDataAt.ofTypeData
    (CanTypeData.subst1 (CanTypeData.ksig TA TB) TC Jm.canSemTm)
    (CanTypeData.prj_branch TA TB TC hTC Jm.canSemTm hn)

noncomputable def prjBranchExact {Γ : Ctx} {A B C m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (Jm : CanTermDataAt Γ m (.sig A B) (CanTypeData.ksig TA TB))
    (Jn : CanTermDataAt (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2]
      (CanTypeData.sigmaBranch TC)) :
    CanTermDataAt Γ (.prj C m n) C.[m/]
      (CanTypeData.subst1 (CanTypeData.ksig TA TB) TC Jm.canSemTm) :=
  CanTermDataAt.prjBranch TA TB TC hTC Jm
    (by
      intro Δ hΓ
      let IA := TA.interp hΓ
      let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
        CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      let hΓBA : CanSemCtx (B :: A :: Γ) (DCandCtx.extend IB) :=
        CanSemCtx.consInterp hΓA IB (TB.weakens hΓA)
      change (TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ)
        (TA.weakens hΓ) (TB.weakens hΓA) (TC.interp hΓS)).SemTm n
      exact Jn.canSemTm hΓBA)

noncomputable def rwTarget {Γ : Ctx} {A B m n a b : Tm}
    (TB : CanTypeData Γ B)
    (Ja : CanTermDataAt Γ a B TB)
    (Jb : CanTermDataAt Γ b B TB)
    (Jn : CanTermDataAt Γ n (.idn B a b)
      (CanTypeData.idn TB Ja.canSemTm Jb.canSemTm))
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hTA : TA.Expansive)
    (hrfl : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IB := TB.interp hΓ
      let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
        CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
      let IP := TypeInterp.idProof IB (Ja.canSemTm hΓ)
      let hΓP : CanSemCtx
          (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
          (DCandCtx.extend IP) :=
        CanSemCtx.consInterp hΓB IP
          (TypeInterp.idProof_weakens IB (Ja.canSemTm hΓ))
      let IA := TA.interp hΓP
      ∀ σ, Δ.valid σ -> ∀ c,
        (IA.cand (.rfl c .: b.[σ] .: σ)).mem m.[σ]) :
    CanTermDataAt Γ (.rw A m n) A.[n,b/]
      (CanTypeData.idTarget TB Ja.canSemTm Jb.canSemTm Jn.canSemTm TA) :=
  CanTermDataAt.ofTypeData
    (CanTypeData.idTarget TB Ja.canSemTm Jb.canSemTm Jn.canSemTm TA)
    (CanTypeData.rw_target TB Ja.canSemTm Jb.canSemTm Jn.canSemTm TA
      hTA hrfl)

noncomputable def ite {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : CanTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanTermDataAt Γ m .bool (CanTypeData.bool Γ))
    (Jn1 : CanTermDataAt Γ n1 A.[.tt/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.tt))
    (Jn2 : CanTermDataAt Γ n2 A.[.ff/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.ff)) :
    CanTermDataAt Γ (.ite A m n1 n2) A.[m/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB Jm.canSemTm) :=
  CanTermDataAt.ofTermData
    (CanTypeData.subst1 (CanTypeData.bool Γ) TB Jm.canSemTm)
    (CanTermData.ite TB hTB Jm.termData Jn1.termData Jn2.termData
      Jm.equiv Jn1.equiv Jn2.equiv)
    (CanTypeData.Equiv.refl
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB Jm.canSemTm))

noncomputable def exf {Γ : Ctx} {A m : Tm}
    (TB : CanTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanTermDataAt Γ m .bot (CanTypeData.bot Γ)) :
    CanTermDataAt Γ (.exf A m) A.[m/]
      (CanTypeData.subst1 (CanTypeData.bot Γ) TB Jm.canSemTm) :=
  CanTermDataAt.ofTermData
    (CanTypeData.subst1 (CanTypeData.bot Γ) TB Jm.canSemTm)
    (CanTermData.exf TB hTB Jm.termData Jm.equiv)
    (CanTypeData.Equiv.refl
      (CanTypeData.subst1 (CanTypeData.bot Γ) TB Jm.canSemTm))

end CanTermDataAt

namespace CanTermData

noncomputable def rwSNBranch {Γ : Ctx} {A B m n a b : Tm} {i : Nat}
    (TB : CanTypeData Γ B)
    (Ja : CanTermDataAt Γ a B TB)
    (Jb : CanTermDataAt Γ b B TB)
    (Jn : CanTermDataAt Γ n (.idn B a b)
      (CanTypeData.idn TB Ja.canSemTm Jb.canSemTm))
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (Jm : CanTermDataAt Γ m A.[.rfl a,a/]
      (CanTypeData.idBranch TB Ja.canSemTm TA)) :
    CanTermData Γ (.rw A m n) A.[n,b/] := by
  let hRw : CanSemTyped Γ (.rw A m n) A.[n,b/] :=
    CanTypeData.rw_sn_branch TB Ja.canSemTm Jb.canSemTm Jn.canSemTm TA
      Jm.canSemTm
  let TTargetExact : CanTypeData Γ A.[n,b/] :=
    CanTypeData.idTarget TB Ja.canSemTm Jb.canSemTm Jn.canSemTm TA
  let hTargetType : CanSemTyped Γ A.[n,b/] (.ty i) := by
    intro Δ hΓ
    exact ⟨(CanTypeData.univ Γ i).interp hΓ,
      (CanTypeData.univ Γ i).weakens hΓ,
      CanTypeData.type TTargetExact i hΓ⟩
  exact CanTermData.ofTypeData (CanTypeData.ofCanSemTypedType hTargetType)
    (by
      intro Δ hΓ σ hσ
      exact CanSemTyped.sn_subst hRw hΓ σ hσ)

noncomputable def prjSNBranch {Γ : Ctx} {A B C m n : Tm} {iC : Nat}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (Jm : CanTermDataAt Γ m (.sig A B) (CanTypeData.ksig TA TB))
    (Jn : CanTermData (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2]) :
    CanTermData Γ (.prj C m n) C.[m/] := by
  let TS : CanTypeData Γ (.sig A B) := CanTypeData.ksig TA TB
  let TTarget : CanTypeData Γ C.[m/] := CanTypeData.subst1 TS TC Jm.canSemTm
  let hTargetType : CanSemTyped Γ C.[m/] (.ty iC) := by
    intro Δ hΓ
    exact ⟨(CanTypeData.univ Γ iC).interp hΓ,
      (CanTypeData.univ Γ iC).weakens hΓ,
      CanTypeData.type TTarget iC hΓ⟩
  refine CanTermData.ofTypeData (CanTypeData.ofCanSemTypedType hTargetType) ?_
  intro Δ hΓ σ hσ
  let IA := TA.interp hΓ
  let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
    CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
  let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
    CanSemCtx.consInterp hΓ K
      (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
  let hΓBA : CanSemCtx (B :: A :: Γ) (DCandCtx.extend IB) :=
    CanSemCtx.consInterp hΓA IB (TB.weakens hΓA)
  have hσS : (DCandCtx.extend K).valid (up σ) :=
    DCandCtx.extend_up_valid (I := K) (CanSemCtx.weakens hΓ) hσ
  have hσA : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) (CanSemCtx.weakens hΓ) hσ
  have hσBA_up : (DCandCtx.extend IB).valid (up (up σ)) :=
    DCandCtx.extend_up_valid (I := IB) (CanSemCtx.weakens hΓA) hσA
  have snC : SN Step C.[up σ] := (TC.interp hΓS).type_sn (up σ) hσS
  have hmK : (K.cand σ).mem m.[σ] := Jm.canSemTm hΓ σ hσ
  have snm : SN Step m.[σ] := (K.cand σ).sn hmK
  have snn : SN Step n.[upn 2 σ] := by
    have hsn := CanSemTyped.sn_subst Jn.toCanSemTyped hΓBA
      (up (up σ)) hσBA_up
    simpa using hsn
  change SN Step (.prj C.[up σ] m.[σ] n.[upn 2 σ])
  apply sn_prj snC snm snn
  intro m1 m2 n' rdM rdN
  have hmK' : (TypeInterp.ksigCand IA IB σ).mem m.[σ] := by
    change (TypeInterp.ksigCandTotal IA IB σ).mem m.[σ] at hmK
    rwa [TypeInterp.ksigCandTotal_valid IA IB hσ] at hmK
  have hcomp :
      (IA.cand σ).mem m1 ∧ (IB.cand (m1 .: σ)).mem m2 := by
    have h := hmK'.2 0 m1 m2 ?_
    · simpa [shiftSubst_zero, SubstLemmas.shift0, Tm.subst_id] using h
    · simpa [SubstLemmas.shift0, Tm.subst_id] using rdM
  have hσBA : (DCandCtx.extend IB).valid (m2 .: m1 .: σ) :=
    DCandCtx.extend_cons (DCandCtx.extend_cons hσ hcomp.1) hcomp.2
  have snBranch : SN Step n.[m2 .: m1 .: σ] :=
    CanSemTyped.sn_subst Jn.toCanSemTyped hΓBA
      (m2 .: m1 .: σ) hσBA
  have rdNsubst : n.[upn 2 σ].[m2,m1/] ~>* n'.[m2,m1/] :=
    Red.subst (m2 .: m1 .: ids) rdN
  have hsubst : n.[upn 2 σ].[m2,m1/] = n.[m2 .: m1 .: σ] := by
    asimp
  have rdNtarget : n.[m2 .: m1 .: σ] ~>* n'.[m2,m1/] := by
    simpa [hsubst] using rdNsubst
  exact sn_red snBranch rdNtarget

end CanTermData

namespace CanTypeJudgment

def toTermData {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeJudgment Γ A i) : CanTermData Γ A (.ty i) where
  typeData := CanTypeData.univ Γ i
  canSemTm := J.inUniv

def ofTypeData {Γ : Ctx} {A : Tm} {i : Nat}
    (TA : CanTypeData Γ A) : CanTypeJudgment Γ A i where
  typeData := TA
  inUniv := CanTypeData.type TA i

noncomputable def weaken {Γ : Ctx} {A B : Tm} {i : Nat}
    (J : CanTypeJudgment Γ A i) :
    CanTypeJudgment (B :: Γ) A.[shift 1] i :=
  CanTypeJudgment.ofTypeData (CanTypeData.weaken (B := B) J.typeData)

def ofSemTypeData {Γ : Ctx} {A : Tm} {i : Nat}
    (TA : SemTypeData Γ A) : CanTypeJudgment Γ A i :=
  CanTypeJudgment.ofTypeData (CanTypeData.ofSemTypeData TA)

noncomputable def ofCanSemTypedType {Γ : Ctx} {A : Tm} {i : Nat}
    (hA : CanSemTyped Γ A (.ty i)) : CanTypeJudgment Γ A i :=
  CanTypeJudgment.ofTypeData (CanTypeData.ofCanSemTypedType hA)

noncomputable def ofTermDataWeak {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTermData Γ A (.ty i)) : CanTypeJudgment Γ A i :=
  CanTypeJudgment.ofCanSemTypedType J.toCanSemTyped

def ty (Γ : Ctx) (i : Nat) : CanTypeJudgment Γ (.ty i) (i + 1) :=
  CanTypeJudgment.ofTypeData (CanTypeData.univ Γ i)

def bool (Γ : Ctx) : CanTypeJudgment Γ .bool 0 :=
  CanTypeJudgment.ofTypeData (CanTypeData.bool Γ)

def bot (Γ : Ctx) : CanTypeJudgment Γ .bot 0 :=
  CanTypeJudgment.ofTypeData (CanTypeData.bot Γ)

noncomputable def pi {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    CanTypeJudgment Γ (.pi A B) (max iA iB) :=
  CanTypeJudgment.ofTypeData (CanTypeData.kpi TA.typeData TB.typeData hTB)

noncomputable def piAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    CanTypeJudgment Γ (.pi A B) i :=
  CanTypeJudgment.ofTypeData (CanTypeData.kpi TA.typeData TB.typeData hTB)

noncomputable def sig {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB) :
    CanTypeJudgment Γ (.sig A B) (max iA iB) :=
  CanTypeJudgment.ofTypeData (CanTypeData.ksig TA.typeData TB.typeData)

noncomputable def sigAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB) :
    CanTypeJudgment Γ (.sig A B) i :=
  CanTypeJudgment.ofTypeData (CanTypeData.ksig TA.typeData TB.typeData)

noncomputable def sigmaBranch {Γ : Ctx} {A B C : Tm} {i : Nat}
    (TC : CanTypeJudgment (.sig A B :: Γ) C i) :
    CanTypeJudgment (B :: A :: Γ)
      C.[.tup (.var 1) (.var 0) .: shift 2] i :=
  CanTypeJudgment.ofTypeData (CanTypeData.sigmaBranch TC.typeData)

noncomputable def idn {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeJudgment Γ A i)
    (hm : TA.typeData.CanSemTm m) (hn : TA.typeData.CanSemTm n) :
    CanTypeJudgment Γ (.idn A m n) i :=
  CanTypeJudgment.ofTypeData (CanTypeData.idn TA.typeData hm hn)

noncomputable def idnByEquiv {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeJudgment Γ A i)
    (Jm : CanTermDataAt Γ m A TA.typeData)
    (Jn : CanTermDataAt Γ n A TA.typeData) :
    CanTypeJudgment Γ (.idn A m n) i :=
  CanTypeJudgment.idn TA Jm.canSemTm Jn.canSemTm

noncomputable def idBranch {Γ : Ctx} {A B a : Tm} {i : Nat}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a)
    (TA : CanTypeJudgment
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A i) :
    CanTypeJudgment Γ A.[.rfl a,a/] i :=
  CanTypeJudgment.ofTypeData (CanTypeData.idBranch TB ha TA.typeData)

noncomputable def idTarget {Γ : Ctx} {A B a b n : Tm} {i : Nat}
    (TB : CanTypeData Γ B) (ha : TB.CanSemTm a) (hb : TB.CanSemTm b)
    (hn : (CanTypeData.idn TB ha hb).CanSemTm n)
    (TA : CanTypeJudgment
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A i) :
    CanTypeJudgment Γ A.[n,b/] i :=
  CanTypeJudgment.ofTypeData (CanTypeData.idTarget TB ha hb hn TA.typeData)

end CanTypeJudgment

inductive FundSemCtxCore : ∀ (Γ : Ctx) (Δ : DCandCtx), CanSemCtx Γ Δ -> Type where
  | nil : FundSemCtxCore [] DCandCtx.empty CanSemCtx.nil
  | cons {Γ : Ctx} {Δ : DCandCtx} {A : Tm} {hΓ : CanSemCtx Γ Δ} :
    FundSemCtxCore Γ Δ hΓ ->
    (TA : CanTypeData Γ A) ->
    FundSemCtxCore (A :: Γ) (DCandCtx.extend (TA.interp hΓ))
      (CanSemCtx.consInterp hΓ (TA.interp hΓ) (TA.weakens hΓ))

structure FundSemCtx (Γ : Ctx) (Δ : DCandCtx) where
  canCtx : CanSemCtx Γ Δ
  canonical : FundSemCtxCore Γ Δ canCtx

namespace FundSemCtx

def nil : FundSemCtx [] DCandCtx.empty where
  canCtx := CanSemCtx.nil
  canonical := FundSemCtxCore.nil

def cons {Γ : Ctx} {Δ : DCandCtx} {A : Tm}
    (hΓ : FundSemCtx Γ Δ) (TA : CanTypeData Γ A) :
    FundSemCtx (A :: Γ) (DCandCtx.extend (TA.interp hΓ.canCtx)) where
  canCtx := CanSemCtx.consInterp hΓ.canCtx (TA.interp hΓ.canCtx)
    (TA.weakens hΓ.canCtx)
  canonical := FundSemCtxCore.cons hΓ.canonical TA

lemma weakens {Γ : Ctx} {Δ : DCandCtx} :
    FundSemCtx Γ Δ -> Δ.Weakens := by
  intro hΓ
  exact CanSemCtx.weakens hΓ.canCtx

lemma ids_valid {Γ : Ctx} {Δ : DCandCtx} :
    FundSemCtx Γ Δ -> Δ.valid ids := by
  intro hΓ
  exact CanSemCtx.ids_valid hΓ.canCtx

lemma var {Γ : Ctx} {Δ : DCandCtx} {x : Var} {A : Tm} :
    FundSemCtx Γ Δ ->
    Has Γ x A ->
    ∃ I : TypeInterp Δ A, I.Weakens ∧ I.SemTm (.var x) := by
  intro hΓ hs
  exact CanSemCtx.var hΓ.canCtx hs

end FundSemCtx

structure FundTermData (Γ : Ctx) (m A : Tm) where
  typeData : CanTypeData Γ A
  fundSemTm : ∀ {Δ : DCandCtx} (hΓ : FundSemCtx Γ Δ),
    (typeData.interp hΓ.canCtx).SemTm m

namespace FundTermData

lemma sn_subst {Γ : Ctx} {m A : Tm} {Δ : DCandCtx}
    (J : FundTermData Γ m A) (hΓ : FundSemCtx Γ Δ) :
    ∀ σ, Δ.valid σ -> SN Step m.[σ] := by
  intro σ hσ
  exact (J.typeData.interp hΓ.canCtx).semTm_sn (J.fundSemTm hΓ) σ hσ

lemma sn {Γ : Ctx} {m A : Tm} {Δ : DCandCtx}
    (J : FundTermData Γ m A) :
    FundSemCtx Γ Δ -> SN Step m := by
  intro hΓ
  have h := FundTermData.sn_subst J hΓ ids (FundSemCtx.ids_valid hΓ)
  simpa [Tm.subst_id] using h

def ofCanTermData {Γ : Ctx} {m A : Tm}
    (J : CanTermData Γ m A) : FundTermData Γ m A where
  typeData := J.typeData
  fundSemTm hΓ := J.canSemTm hΓ.canCtx

end FundTermData

abbrev FundFund (Γ : Ctx) (m A : Tm) : Prop :=
  Nonempty (FundTermData Γ m A)

namespace FundFund

noncomputable def choose {Γ : Ctx} {m A : Tm}
    (J : FundFund Γ m A) : FundTermData Γ m A :=
  Classical.choice J

lemma ofTermData {Γ : Ctx} {m A : Tm}
    (J : FundTermData Γ m A) : FundFund Γ m A :=
  ⟨J⟩

end FundFund

namespace Wf

lemma canSemCtx_of_type_data
    (fund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> SemTypeData Γ A) :
    ∀ {Γ : Ctx}, Γ ⊢ -> Nonempty (Σ Δ : DCandCtx, CanSemCtx Γ Δ)
  | [], Wf.nil => ⟨⟨DCandCtx.empty, CanSemCtx.nil⟩⟩
  | A :: Γ, Wf.cons tyA wf =>
    by
      rcases canSemCtx_of_type_data fund wf with ⟨⟨Δ, hΓ⟩⟩
      let TA := fund tyA
      exact ⟨⟨DCandCtx.extend (TA.interp hΓ.semCtx), CanSemCtx.cons hΓ TA⟩⟩

lemma canSemCtx_of_can_type_data
    (fund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeData Γ A) :
    ∀ {Γ : Ctx}, Γ ⊢ -> Nonempty (Σ Δ : DCandCtx, CanSemCtx Γ Δ)
  | [], Wf.nil => ⟨⟨DCandCtx.empty, CanSemCtx.nil⟩⟩
  | A :: Γ, Wf.cons tyA wf =>
    by
      rcases canSemCtx_of_can_type_data fund wf with ⟨⟨Δ, hΓ⟩⟩
      let TA := fund tyA
      exact ⟨⟨DCandCtx.extend (TA.interp hΓ), CanSemCtx.consInterp hΓ
        (TA.interp hΓ) (TA.weakens hΓ)⟩⟩

lemma fundSemCtx_of_can_type_data
    (fund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeData Γ A) :
    ∀ {Γ : Ctx}, Γ ⊢ -> Nonempty (Σ Δ : DCandCtx, FundSemCtx Γ Δ)
  | [], Wf.nil => ⟨⟨DCandCtx.empty, FundSemCtx.nil⟩⟩
  | A :: Γ, Wf.cons tyA wf =>
    by
      rcases fundSemCtx_of_can_type_data fund wf with ⟨⟨Δ, hΓ⟩⟩
      let TA := fund tyA
      exact ⟨⟨DCandCtx.extend (TA.interp hΓ.canCtx), FundSemCtx.cons hΓ TA⟩⟩

end Wf

structure SemTermData (Γ : Ctx) (m A : Tm) where
  typeData : SemTypeData Γ A
  semTm : typeData.SemTm m

namespace SemTermData

lemma toSemTyped {Γ : Ctx} {m A : Tm} (J : SemTermData Γ m A) :
    SemTyped Γ m A :=
  J.typeData.toSemTyped J.semTm

lemma sn {Γ : Ctx} {m A : Tm} {Δ : DCandCtx}
    (J : SemTermData Γ m A) :
    SemCtx Γ Δ -> SN Step m :=
  fun hΓ => SemTyped.sn hΓ J.toSemTyped

def ofTypeData {Γ : Ctx} {m A : Tm}
    (TA : SemTypeData Γ A) (hm : TA.SemTm m) : SemTermData Γ m A where
  typeData := TA
  semTm := hm

def convType {Γ : Ctx} {A B m : Tm} (J : SemTermData Γ m A)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) : SemTermData Γ m B where
  typeData := J.typeData.convType hB
  semTm := J.typeData.convType_semTm hB J.semTm

def retag {Γ : Ctx} {A B m : Tm}
    (J : SemTermData Γ m A) (TB : SemTypeData Γ B) :
    SemTermData Γ m B :=
  J.convType (fun hΓ σ hσ => (TB.interp hΓ).type_sn σ hσ)

lemma retag_equiv_source {Γ : Ctx} {A B m : Tm}
    (J : SemTermData Γ m A) (TB : SemTypeData Γ B) :
    SemTypeData.Equiv (J.retag TB).typeData J.typeData :=
  SemTypeData.convType_equiv_left J.typeData
    (fun hΓ σ hσ => (TB.interp hΓ).type_sn σ hσ)

lemma source_equiv_retag {Γ : Ctx} {A B m : Tm}
    (J : SemTermData Γ m A) (TB : SemTypeData Γ B) :
    SemTypeData.Equiv J.typeData (J.retag TB).typeData :=
  SemTypeData.convType_equiv_right J.typeData
    (fun hΓ σ hσ => (TB.interp hΓ).type_sn σ hσ)

def retagEquiv {Γ : Ctx} {A B m : Tm}
    (J : SemTermData Γ m A) (TB : SemTypeData Γ B)
    (hEq : SemTypeData.Equiv J.typeData TB) :
    SemTermData Γ m B where
  typeData := TB
  semTm := SemTypeData.Equiv.semTm hEq J.semTm

end SemTermData

structure SemTypeJudgment (Γ : Ctx) (A : Tm) (i : Nat) where
  typeData : SemTypeData Γ A
  inUniv : (SemTypeData.univ Γ i).SemTm A

abbrev SemFund (Γ : Ctx) (m A : Tm) : Prop :=
  Nonempty (SemTermData Γ m A)

abbrev SemTypeFund (Γ : Ctx) (A : Tm) (i : Nat) : Prop :=
  Nonempty (SemTypeJudgment Γ A i)

abbrev SemFundAt (Γ : Ctx) (m A : Tm) (TA : SemTypeData Γ A) : Prop :=
  Nonempty {J : SemTermData Γ m A // SemTypeData.Equiv J.typeData TA}

namespace SemFundAt

noncomputable def choose {Γ : Ctx} {m A : Tm} {TA : SemTypeData Γ A}
    (J : SemFundAt Γ m A TA) :
    {J : SemTermData Γ m A // SemTypeData.Equiv J.typeData TA} :=
  Classical.choice J

lemma ofTermData {Γ : Ctx} {m A : Tm} {TA : SemTypeData Γ A}
    (J : SemTermData Γ m A)
    (hEq : SemTypeData.Equiv J.typeData TA) :
    SemFundAt Γ m A TA :=
  ⟨⟨J, hEq⟩⟩

lemma ofTypeData {Γ : Ctx} {m A : Tm}
    (TA : SemTypeData Γ A) (hm : TA.SemTm m) :
    SemFundAt Γ m A TA :=
  SemFundAt.ofTermData (SemTermData.ofTypeData TA hm)
    (SemTypeData.Equiv.refl TA)

lemma toSemFund {Γ : Ctx} {m A : Tm} {TA : SemTypeData Γ A} :
    SemFundAt Γ m A TA -> SemFund Γ m A := by
  intro J
  exact ⟨(SemFundAt.choose J).val⟩

lemma semTm {Γ : Ctx} {m A : Tm} {TA : SemTypeData Γ A}
    (J : SemFundAt Γ m A TA) :
    TA.SemTm m :=
  SemTypeData.Equiv.semTm (SemFundAt.choose J).property
    (SemFundAt.choose J).val.semTm

lemma retag {Γ : Ctx} {m A : Tm} {TA TB : SemTypeData Γ A}
    (J : SemFundAt Γ m A TA)
    (hEq : SemTypeData.Equiv TA TB) :
    SemFundAt Γ m A TB :=
  SemFundAt.ofTermData (SemFundAt.choose J).val
    (SemTypeData.Equiv.trans (SemFundAt.choose J).property hEq)

lemma convType {Γ : Ctx} {A B m : Tm} {TA : SemTypeData Γ A}
    (J : SemFundAt Γ m A TA)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    SemFundAt Γ m B (TA.convType hB) :=
  SemFundAt.ofTermData ((SemFundAt.choose J).val.convType hB)
    (SemTypeData.convType_equiv_of_equiv
      (SemFundAt.choose J).property hB hB)

lemma convExactTarget {Γ : Ctx} {A B m : Tm}
    (TB : SemTypeData Γ B)
    (hA : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step A.[σ])
    (hB : ∀ {Δ : DCandCtx} (_hΓ : SemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ])
    (J : SemFundAt Γ m A (TB.convType hA)) :
    SemFundAt Γ m B TB :=
  SemFundAt.retag (SemFundAt.convType J hB)
    (SemTypeData.Equiv.trans
      (SemTypeData.convType_equiv_left (TB.convType hA) hB)
      (SemTypeData.convType_equiv_left TB hA))

end SemFundAt

namespace SemTermData

noncomputable def retagTypeFund {Γ : Ctx} {A B m : Tm} {i : Nat}
    (J : SemTermData Γ m A) (TB : SemTypeFund Γ B i) :
    SemTermData Γ m B :=
  J.retag (Classical.choice TB).typeData

lemma retagTypeFund_equiv_source {Γ : Ctx} {A B m : Tm} {i : Nat}
    (J : SemTermData Γ m A) (TB : SemTypeFund Γ B i) :
    SemTypeData.Equiv (J.retagTypeFund TB).typeData J.typeData :=
  J.retag_equiv_source (Classical.choice TB).typeData

lemma retagTypeFund_equiv_trans {Γ : Ctx} {A B C m : Tm} {i : Nat}
    (J : SemTermData Γ m A) (TB : SemTypeFund Γ B i)
    (TC : SemTypeData Γ C)
    (hEq : SemTypeData.Equiv J.typeData TC) :
    SemTypeData.Equiv (J.retagTypeFund TB).typeData TC :=
  SemTypeData.Equiv.trans (J.retagTypeFund_equiv_source TB) hEq

end SemTermData

namespace SemTypeJudgment

def toTermData {Γ : Ctx} {A : Tm} {i : Nat}
    (J : SemTypeJudgment Γ A i) : SemTermData Γ A (.ty i) where
  typeData := SemTypeData.univ Γ i
  semTm := J.inUniv

def ty (Γ : Ctx) (i : Nat) : SemTypeJudgment Γ (.ty i) (i + 1) where
  typeData := SemTypeData.univ Γ i
  inUniv := SemTypeData.ty i

def bool (Γ : Ctx) : SemTypeJudgment Γ .bool 0 where
  typeData := SemTypeData.bool Γ
  inUniv := SemTypeData.bool_type

def bot (Γ : Ctx) : SemTypeJudgment Γ .bot 0 where
  typeData := SemTypeData.bot Γ
  inUniv := SemTypeData.bot_type

noncomputable def pi {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    SemTypeJudgment Γ (.pi A B) (max iA iB) where
  typeData := SemTypeData.kpi TA.typeData TB.typeData hTB
  inUniv := SemTypeData.pi_type TA.typeData TB.typeData hTB (max iA iB)

noncomputable def sig {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeJudgment (A :: Γ) B iB) :
    SemTypeJudgment Γ (.sig A B) (max iA iB) where
  typeData := SemTypeData.ksig TA.typeData TB.typeData
  inUniv := SemTypeData.sig_type TA.typeData TB.typeData (max iA iB)

noncomputable def idn {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : SemTypeJudgment Γ A i)
    (hm : TA.typeData.SemTm m) (hn : TA.typeData.SemTm n) :
    SemTypeJudgment Γ (.idn A m n) i where
  typeData := SemTypeData.idn TA.typeData hm hn
  inUniv := SemTypeData.idn_type TA.typeData hm hn i

noncomputable def idnByEquiv {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : SemTypeJudgment Γ A i)
    (Jm : SemTermData Γ m A) (Jn : SemTermData Γ n A)
    (hmEq : SemTypeData.Equiv Jm.typeData TA.typeData)
    (hnEq : SemTypeData.Equiv Jn.typeData TA.typeData) :
    SemTypeJudgment Γ (.idn A m n) i :=
  SemTypeJudgment.idn TA
    (SemTypeData.Equiv.semTm hmEq Jm.semTm)
    (SemTypeData.Equiv.semTm hnEq Jn.semTm)

noncomputable def ofSemTypedType {Γ : Ctx} {A : Tm} {i : Nat}
    (hA : SemTyped Γ A (.ty i)) : SemTypeJudgment Γ A i where
  typeData := SemTypeData.ofSemTypedType hA
  inUniv := SemTypeData.type (SemTypeData.ofSemTypedType hA) i

def termDataByEquiv {Γ : Ctx} {A B m : Tm} {i : Nat}
    (TB : SemTypeJudgment Γ B i) (J : SemTermData Γ m A)
    (hEq : SemTypeData.Equiv J.typeData TB.typeData) :
    SemTermData Γ m B :=
  J.retagEquiv TB.typeData hEq

noncomputable def ofTermDataWeak {Γ : Ctx} {A : Tm} {i : Nat}
    (J : SemTermData Γ A (.ty i)) : SemTypeJudgment Γ A i :=
  SemTypeJudgment.ofSemTypedType J.toSemTyped

end SemTypeJudgment

namespace SemTermData

def srt {Γ : Ctx} (i : Nat) : SemTermData Γ (.ty i) (.ty (i + 1)) :=
  (SemTypeJudgment.ty Γ i).toTermData

noncomputable def var {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) : SemTermData Γ (.var x) A :=
  SemTermData.ofTypeData (SemTypeData.lookup hs) (SemTypeData.var hs)

def bool {Γ : Ctx} : SemTermData Γ .bool (.ty 0) :=
  (SemTypeJudgment.bool Γ).toTermData

def bot {Γ : Ctx} : SemTermData Γ .bot (.ty 0) :=
  (SemTypeJudgment.bot Γ).toTermData

def tt {Γ : Ctx} : SemTermData Γ .tt .bool :=
  SemTermData.ofTypeData (SemTypeData.bool Γ) SemTypeData.tt

def ff {Γ : Ctx} : SemTermData Γ .ff .bool :=
  SemTermData.ofTypeData (SemTypeData.bool Γ) SemTypeData.ff

noncomputable def piType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    SemTermData Γ (.pi A B) (.ty (max iA iB)) :=
  (SemTypeJudgment.pi TA TB hTB).toTermData

noncomputable def sigType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeJudgment (A :: Γ) B iB) :
    SemTermData Γ (.sig A B) (.ty (max iA iB)) :=
  (SemTypeJudgment.sig TA TB).toTermData

noncomputable def idnType {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : SemTypeJudgment Γ A i)
    (hm : TA.typeData.SemTm m) (hn : TA.typeData.SemTm n) :
    SemTermData Γ (.idn A m n) (.ty i) :=
  (SemTypeJudgment.idn TA hm hn).toTermData

noncomputable def rfl {Γ : Ctx} {A m : Tm}
    (J : SemTermData Γ m A) :
    SemTermData Γ (.rfl m) (.idn A m m) :=
  SemTermData.ofTypeData
    (SemTypeData.idn J.typeData J.semTm J.semTm)
    (SemTypeData.rfl J.typeData J.semTm)

noncomputable def rflByEquiv {Γ : Ctx} {A m : Tm}
    (TA : SemTypeData Γ A) (J : SemTermData Γ m A)
    (hEq : SemTypeData.Equiv J.typeData TA) :
    SemTermData Γ (.rfl m) (.idn A m m) :=
  let hm : TA.SemTm m := SemTypeData.Equiv.semTm hEq J.semTm
  SemTermData.ofTypeData
    (SemTypeData.idn TA hm hm)
    (SemTypeData.rfl TA hm)

noncomputable def lam {Γ : Ctx} {A B m : Tm} {iA : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (hm : TB.SemTm m) :
    SemTermData Γ (.lam A m) (.pi A B) :=
  SemTermData.ofTypeData
    (SemTypeData.kpi TA.typeData TB hTB)
    (SemTypeData.lam TA.typeData TB hTB hm)

noncomputable def lamByEquiv {Γ : Ctx} {A B m : Tm} {iA : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemTermData (A :: Γ) m B)
    (hmEq : SemTypeData.Equiv Jm.typeData TB) :
    SemTermData Γ (.lam A m) (.pi A B) :=
  SemTermData.lam TA TB hTB
    (SemTypeData.Equiv.semTm hmEq Jm.semTm)

noncomputable def app {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (hm : (SemTypeData.kpi TA TB hTB).SemTm m)
    (hn : TA.SemTm n) :
    SemTermData Γ (.app m n) B.[n/] :=
  SemTermData.ofTypeData
    (SemTypeData.subst1 TA TB hn)
    (SemTypeData.app TA TB hTB hm hn)

noncomputable def appByEquiv {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemTermData Γ m (.pi A B)) (Jn : SemTermData Γ n A)
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.kpi TA TB hTB))
    (hnEq : SemTypeData.Equiv Jn.typeData TA) :
    SemTermData Γ (.app m n) B.[n/] :=
  SemTermData.app TA TB hTB
    (SemTypeData.Equiv.semTm hmEq Jm.semTm)
    (SemTypeData.Equiv.semTm hnEq Jn.semTm)

noncomputable def appRetagByEquiv {Γ : Ctx} {P A B m n : Tm} {iP : Nat}
    (TP : SemTypeFund Γ (.pi A B) iP)
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemTermData Γ m P) (Jn : SemTermData Γ n A)
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.kpi TA TB hTB))
    (hnEq : SemTypeData.Equiv Jn.typeData TA) :
    SemTermData Γ (.app m n) B.[n/] :=
  SemTermData.appByEquiv TA TB hTB (Jm.retagTypeFund TP) Jn
    (Jm.retagTypeFund_equiv_trans TP (SemTypeData.kpi TA TB hTB) hmEq)
    hnEq

noncomputable def tup {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hm : TA.SemTm m)
    (hn : (SemTypeData.subst1 TA TB hm).SemTm n) :
    SemTermData Γ (.tup m n) (.sig A B) :=
  SemTermData.ofTypeData
    (SemTypeData.ksig TA TB)
    (SemTypeData.tup TA TB hm hn)

noncomputable def tupByEquiv {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (Jm : SemTermData Γ m A) (Jn : SemTermData Γ n B.[m/])
    (hmEq : SemTypeData.Equiv Jm.typeData TA)
    (hnEq : SemTypeData.Equiv Jn.typeData
      (SemTypeData.subst1 TA TB (SemTypeData.Equiv.semTm hmEq Jm.semTm))) :
    SemTermData Γ (.tup m n) (.sig A B) :=
  SemTermData.tup TA TB
    (SemTypeData.Equiv.semTm hmEq Jm.semTm)
    (SemTypeData.Equiv.semTm hnEq Jn.semTm)

noncomputable def prjBranch {Γ : Ctx} {A B C m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (hm : (SemTypeData.ksig TA TB).SemTm m)
    (hn : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
      let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (SemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    SemTermData Γ (.prj C m n) C.[m/] :=
  SemTermData.ofTypeData
    (SemTypeData.subst1 (SemTypeData.ksig TA TB) TC hm)
    (SemTypeData.prj_branch TA TB TC hTC hm hn)

noncomputable def prjSNBranch {Γ : Ctx} {A B C m n : Tm} {iC : Nat}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (hm : (SemTypeData.ksig TA TB).SemTm m)
    (Jn : SemFund (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2]) :
    SemTermData Γ (.prj C m n) C.[m/] := by
  let TS := SemTypeData.ksig TA TB
  let TTarget : SemTypeData Γ C.[m/] := SemTypeData.subst1 TS TC hm
  let hTargetType : SemTyped Γ C.[m/] (.ty iC) :=
    (SemTypeData.univ Γ iC).toSemTyped (SemTypeData.type TTarget iC)
  refine SemTermData.ofTypeData (SemTypeData.ofSemTypedType hTargetType) ?_
  intro Δ hΓ σ hσ
  let IA := TA.interp hΓ
  let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
    SemCtx.cons hΓ IA (TA.weakens hΓ)
  let IB := TB.interp hΓA
  let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
  let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
    SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
  let hΓBA : SemCtx (B :: A :: Γ) (DCandCtx.extend IB) :=
    SemCtx.cons hΓA IB (TB.weakens hΓA)
  have hσS : (DCandCtx.extend K).valid (up σ) :=
    DCandCtx.extend_up_valid (I := K) (SemCtx.weakens hΓ) hσ
  have hσA : (DCandCtx.extend IA).valid (up σ) :=
    DCandCtx.extend_up_valid (I := IA) (SemCtx.weakens hΓ) hσ
  have hσBA_up : (DCandCtx.extend IB).valid (up (up σ)) :=
    DCandCtx.extend_up_valid (I := IB) (SemCtx.weakens hΓA) hσA
  have snC : SN Step C.[up σ] := (TC.interp hΓS).type_sn (up σ) hσS
  have hmK : (K.cand σ).mem m.[σ] := hm hΓ σ hσ
  have snm : SN Step m.[σ] := (K.cand σ).sn hmK
  have snn : SN Step n.[upn 2 σ] := by
    have hsn := SemTyped.sn_subst (Classical.choice Jn).toSemTyped hΓBA
      (up (up σ)) hσBA_up
    simpa using hsn
  change SN Step (.prj C.[up σ] m.[σ] n.[upn 2 σ])
  apply sn_prj snC snm snn
  intro m1 m2 n' rdM rdN
  have hmK' : (TypeInterp.ksigCand IA IB σ).mem m.[σ] := by
    change (TypeInterp.ksigCandTotal IA IB σ).mem m.[σ] at hmK
    rwa [TypeInterp.ksigCandTotal_valid IA IB hσ] at hmK
  have hcomp :
      (IA.cand σ).mem m1 ∧ (IB.cand (m1 .: σ)).mem m2 := by
    have h := hmK'.2 0 m1 m2 ?_
    · simpa [shiftSubst_zero, SubstLemmas.shift0, Tm.subst_id] using h
    · simpa [SubstLemmas.shift0, Tm.subst_id] using rdM
  have hσBA : (DCandCtx.extend IB).valid (m2 .: m1 .: σ) :=
    DCandCtx.extend_cons (DCandCtx.extend_cons hσ hcomp.1) hcomp.2
  have snBranch : SN Step n.[m2 .: m1 .: σ] :=
    SemTyped.sn_subst (Classical.choice Jn).toSemTyped hΓBA
      (m2 .: m1 .: σ) hσBA
  have rdNsubst : n.[upn 2 σ].[m2,m1/] ~>* n'.[m2,m1/] :=
    Red.subst (m2 .: m1 .: ids) rdN
  have hsubst : n.[upn 2 σ].[m2,m1/] = n.[m2 .: m1 .: σ] := by
    asimp
  have rdNtarget : n.[m2 .: m1 .: σ] ~>* n'.[m2,m1/] := by
    simpa [hsubst] using rdNsubst
  exact sn_red snBranch rdNtarget

noncomputable def prjBranchByEquiv {Γ : Ctx} {A B C m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (Jm : SemTermData Γ m (.sig A B))
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.ksig TA TB))
    (hn : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
      let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (SemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    SemTermData Γ (.prj C m n) C.[m/] :=
  SemTermData.prjBranch TA TB TC hTC
    (SemTypeData.Equiv.semTm hmEq Jm.semTm) hn

noncomputable def prjSNBranchRetagByEquiv {Γ : Ctx} {P A B C m n : Tm}
    {iP iC : Nat}
    (TP : SemTypeFund Γ (.sig A B) iP)
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (Jm : SemTermData Γ m P)
    (Jn : SemFund (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2])
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.ksig TA TB)) :
    SemTermData Γ (.prj C m n) C.[m/] :=
  SemTermData.prjSNBranch (iC := iC) TA TB TC
    (SemTypeData.Equiv.semTm
      (Jm.retagTypeFund_equiv_trans TP (SemTypeData.ksig TA TB) hmEq)
      (Jm.retagTypeFund TP).semTm)
    Jn

noncomputable def ite {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : SemTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (hm : (SemTypeData.bool Γ).SemTm m)
    (hn1 : (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.tt).SemTm n1)
    (hn2 : (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.ff).SemTm n2) :
    SemTermData Γ (.ite A m n1 n2) A.[m/] :=
  SemTermData.ofTypeData
    (SemTypeData.subst1 (SemTypeData.bool Γ) TB hm)
    (SemTypeData.ite TB hTB hm hn1 hn2)

noncomputable def iteByEquiv {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : SemTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : SemTermData Γ m .bool)
    (Jn1 : SemTermData Γ n1 A.[.tt/])
    (Jn2 : SemTermData Γ n2 A.[.ff/])
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.bool Γ))
    (hn1Eq : SemTypeData.Equiv Jn1.typeData
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.tt))
    (hn2Eq : SemTypeData.Equiv Jn2.typeData
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.ff)) :
    SemTermData Γ (.ite A m n1 n2) A.[m/] :=
  SemTermData.ite TB hTB
    (SemTypeData.Equiv.semTm hmEq Jm.semTm)
    (SemTypeData.Equiv.semTm hn1Eq Jn1.semTm)
    (SemTypeData.Equiv.semTm hn2Eq Jn2.semTm)

noncomputable def iteSN {Γ : Ctx} {A m n1 n2 : Tm} {i : Nat}
    (TB : SemTypeData (.bool :: Γ) A)
    (Jm : SemTermData Γ m .bool)
    (Jn1 : SemFund Γ n1 A.[.tt/])
    (Jn2 : SemFund Γ n2 A.[.ff/])
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.bool Γ)) :
    SemTermData Γ (.ite A m n1 n2) A.[m/] := by
  let hm : (SemTypeData.bool Γ).SemTm m :=
    SemTypeData.Equiv.semTm hmEq Jm.semTm
  let TTarget : SemTypeData Γ A.[m/] :=
    SemTypeData.subst1 (SemTypeData.bool Γ) TB hm
  let hTargetType : SemTyped Γ A.[m/] (.ty i) :=
    (SemTypeData.univ Γ i).toSemTyped (SemTypeData.type TTarget i)
  refine SemTermData.ofTypeData (SemTypeData.ofSemTypedType hTargetType) ?_
  intro Δ hΓ σ hσ
  let hΓB : SemCtx (.bool :: Γ) (DCandCtx.extend (TypeInterp.bool Δ)) :=
    SemCtx.cons hΓ (TypeInterp.bool Δ) (TypeInterp.bool_weakens Δ)
  have hσB : (DCandCtx.extend (TypeInterp.bool Δ)).valid (up σ) :=
    DCandCtx.extend_up_valid (I := TypeInterp.bool Δ) (SemCtx.weakens hΓ) hσ
  have snA : SN Step A.[up σ] := (TB.interp hΓB).type_sn (up σ) hσB
  have snm : SN Step m.[σ] :=
    SemTyped.sn_subst Jm.toSemTyped hΓ σ hσ
  have sn1 : SN Step n1.[σ] :=
    SemTyped.sn_subst (Classical.choice Jn1).toSemTyped hΓ σ hσ
  have sn2 : SN Step n2.[σ] :=
    SemTyped.sn_subst (Classical.choice Jn2).toSemTyped hΓ σ hσ
  change SN Step (.ite A.[up σ] m.[σ] n1.[σ] n2.[σ])
  exact sn_ite snA snm sn1 sn2

noncomputable def iteSNRetagByEquiv {Γ : Ctx} {P A m n1 n2 : Tm}
    {iP i : Nat}
    (TP : SemTypeFund Γ .bool iP)
    (TB : SemTypeData (.bool :: Γ) A)
    (Jm : SemTermData Γ m P)
    (Jn1 : SemFund Γ n1 A.[.tt/])
    (Jn2 : SemFund Γ n2 A.[.ff/])
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.bool Γ)) :
    SemTermData Γ (.ite A m n1 n2) A.[m/] :=
  SemTermData.iteSN (i := i) TB (Jm.retagTypeFund TP) Jn1 Jn2
    (Jm.retagTypeFund_equiv_trans TP (SemTypeData.bool Γ) hmEq)

noncomputable def exf {Γ : Ctx} {A m : Tm}
    (TB : SemTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (hm : (SemTypeData.bot Γ).SemTm m) :
    SemTermData Γ (.exf A m) A.[m/] :=
  SemTermData.ofTypeData
    (SemTypeData.subst1 (SemTypeData.bot Γ) TB hm)
    (SemTypeData.exf TB hTB hm)

noncomputable def exfByEquiv {Γ : Ctx} {A m : Tm}
    (TB : SemTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : SemTermData Γ m .bot)
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.bot Γ)) :
    SemTermData Γ (.exf A m) A.[m/] :=
  SemTermData.exf TB hTB (SemTypeData.Equiv.semTm hmEq Jm.semTm)

noncomputable def exfSN {Γ : Ctx} {A m : Tm} {i : Nat}
    (TB : SemTypeData (.bot :: Γ) A)
    (Jm : SemTermData Γ m .bot)
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.bot Γ)) :
    SemTermData Γ (.exf A m) A.[m/] := by
  let hm : (SemTypeData.bot Γ).SemTm m :=
    SemTypeData.Equiv.semTm hmEq Jm.semTm
  let TTarget : SemTypeData Γ A.[m/] :=
    SemTypeData.subst1 (SemTypeData.bot Γ) TB hm
  let hTargetType : SemTyped Γ A.[m/] (.ty i) :=
    (SemTypeData.univ Γ i).toSemTyped (SemTypeData.type TTarget i)
  refine SemTermData.ofTypeData (SemTypeData.ofSemTypedType hTargetType) ?_
  intro Δ hΓ σ hσ
  let hΓB : SemCtx (.bot :: Γ) (DCandCtx.extend (TypeInterp.bot Δ)) :=
    SemCtx.cons hΓ (TypeInterp.bot Δ) (TypeInterp.bot_weakens Δ)
  have hσB : (DCandCtx.extend (TypeInterp.bot Δ)).valid (up σ) :=
    DCandCtx.extend_up_valid (I := TypeInterp.bot Δ) (SemCtx.weakens hΓ) hσ
  have snA : SN Step A.[up σ] := (TB.interp hΓB).type_sn (up σ) hσB
  have snm : SN Step m.[σ] :=
    SemTyped.sn_subst Jm.toSemTyped hΓ σ hσ
  change SN Step (.exf A.[up σ] m.[σ])
  exact sn_exf snA snm

noncomputable def exfSNRetagByEquiv {Γ : Ctx} {P A m : Tm}
    {iP i : Nat}
    (TP : SemTypeFund Γ .bot iP)
    (TB : SemTypeData (.bot :: Γ) A)
    (Jm : SemTermData Γ m P)
    (hmEq : SemTypeData.Equiv Jm.typeData (SemTypeData.bot Γ)) :
    SemTermData Γ (.exf A m) A.[m/] :=
  SemTermData.exfSN (i := i) TB (Jm.retagTypeFund TP)
    (Jm.retagTypeFund_equiv_trans TP (SemTypeData.bot Γ) hmEq)

noncomputable def rwSNBranch {Γ : Ctx} {A B m n a b : Tm} {i : Nat}
    (TB : SemTypeData Γ B)
    (ha : TB.SemTm a) (hb : TB.SemTm b)
    (hn : (SemTypeData.idn TB ha hb).SemTm n)
    (TA : SemTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hm : (SemTypeData.idBranch TB ha TA).SemTm m) :
    SemTermData Γ (.rw A m n) A.[n,b/] := by
  let TTarget : SemTypeData Γ A.[n,b/] :=
    SemTypeData.idTarget TB ha hb hn TA
  let hTargetType : SemTyped Γ A.[n,b/] (.ty i) :=
    (SemTypeData.univ Γ i).toSemTyped (SemTypeData.type TTarget i)
  let hRw : SemTyped Γ (.rw A m n) A.[n,b/] :=
    SemTypeData.rw_sn_branch TB ha hb hn TA hm
  refine SemTermData.ofTypeData (SemTypeData.ofSemTypedType hTargetType) ?_
  intro Δ hΓ σ hσ
  exact SemTyped.sn_subst hRw hΓ σ hσ

end SemTermData

namespace CanTermData

def ofSemTermData {Γ : Ctx} {m A : Tm}
    (J : SemTermData Γ m A) : CanTermData Γ m A where
  typeData := CanTypeData.ofSemTypeData J.typeData
  canSemTm := fun hΓ => J.semTm hΓ.semCtx

def srt {Γ : Ctx} (i : Nat) : CanTermData Γ (.ty i) (.ty (i + 1)) :=
  (CanTypeJudgment.ty Γ i).toTermData

def bool {Γ : Ctx} : CanTermData Γ .bool (.ty 0) :=
  (CanTypeJudgment.bool Γ).toTermData

def bot {Γ : Ctx} : CanTermData Γ .bot (.ty 0) :=
  (CanTypeJudgment.bot Γ).toTermData

def tt {Γ : Ctx} : CanTermData Γ .tt .bool :=
  CanTermData.ofSemTermData SemTermData.tt

def ff {Γ : Ctx} : CanTermData Γ .ff .bool :=
  CanTermData.ofSemTermData SemTermData.ff

noncomputable def piType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    CanTermData Γ (.pi A B) (.ty (max iA iB)) :=
  (CanTypeJudgment.pi TA TB hTB).toTermData

noncomputable def sigType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB) :
    CanTermData Γ (.sig A B) (.ty (max iA iB)) :=
  (CanTypeJudgment.sig TA TB).toTermData

noncomputable def idnType {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeJudgment Γ A i)
    (Jm : CanTermDataAt Γ m A TA.typeData)
    (Jn : CanTermDataAt Γ n A TA.typeData) :
    CanTermData Γ (.idn A m n) (.ty i) :=
  (CanTypeJudgment.idnByEquiv TA Jm Jn).toTermData

end CanTermData

namespace CanTermDataAt

def srt {Γ : Ctx} (i : Nat) :
    CanTermDataAt Γ (.ty i) (.ty (i + 1)) (CanTypeData.univ Γ (i + 1)) :=
  CanTermDataAt.ofTermData (CanTypeData.univ Γ (i + 1))
    (CanTermData.srt i) (CanTypeData.Equiv.refl (CanTypeData.univ Γ (i + 1)))

def bool {Γ : Ctx} :
    CanTermDataAt Γ .bool (.ty 0) (CanTypeData.univ Γ 0) :=
  CanTermDataAt.ofTermData (CanTypeData.univ Γ 0)
    CanTermData.bool (CanTypeData.Equiv.refl (CanTypeData.univ Γ 0))

def bot {Γ : Ctx} :
    CanTermDataAt Γ .bot (.ty 0) (CanTypeData.univ Γ 0) :=
  CanTermDataAt.ofTermData (CanTypeData.univ Γ 0)
    CanTermData.bot (CanTypeData.Equiv.refl (CanTypeData.univ Γ 0))

def tt {Γ : Ctx} :
    CanTermDataAt Γ .tt .bool (CanTypeData.bool Γ) :=
  CanTermDataAt.ofTermData (CanTypeData.bool Γ)
    CanTermData.tt (CanTypeData.Equiv.refl (CanTypeData.bool Γ))

def ff {Γ : Ctx} :
    CanTermDataAt Γ .ff .bool (CanTypeData.bool Γ) :=
  CanTermDataAt.ofTermData (CanTypeData.bool Γ)
    CanTermData.ff (CanTypeData.Equiv.refl (CanTypeData.bool Γ))

noncomputable def piType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    CanTermDataAt Γ (.pi A B) (.ty (max iA iB))
      (CanTypeData.univ Γ (max iA iB)) :=
  CanTermDataAt.ofTermData (CanTypeData.univ Γ (max iA iB))
    (CanTermData.piType TA TB hTB)
    (CanTypeData.Equiv.refl (CanTypeData.univ Γ (max iA iB)))

noncomputable def sigType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB) :
    CanTermDataAt Γ (.sig A B) (.ty (max iA iB))
      (CanTypeData.univ Γ (max iA iB)) :=
  CanTermDataAt.ofTermData (CanTypeData.univ Γ (max iA iB))
    (CanTermData.sigType TA TB)
    (CanTypeData.Equiv.refl (CanTypeData.univ Γ (max iA iB)))

noncomputable def idnType {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeJudgment Γ A i)
    (Jm : CanTermDataAt Γ m A TA.typeData)
    (Jn : CanTermDataAt Γ n A TA.typeData) :
    CanTermDataAt Γ (.idn A m n) (.ty i) (CanTypeData.univ Γ i) :=
  CanTermDataAt.ofTermData (CanTypeData.univ Γ i)
    (CanTermData.idnType TA Jm Jn)
    (CanTypeData.Equiv.refl (CanTypeData.univ Γ i))

noncomputable def var {Γ : Ctx} {x : Var} {A : Tm} (hs : Has Γ x A) :
    CanTermDataAt Γ (.var x) A
      (CanTypeData.lookup hs) :=
  CanTermDataAt.ofTypeData (CanTypeData.lookup hs)
    (CanTypeData.lookup_var hs)

end CanTermDataAt

abbrev CanFund (Γ : Ctx) (m A : Tm) : Prop :=
  Nonempty (CanTermData Γ m A)

abbrev CanTypeFund (Γ : Ctx) (A : Tm) (i : Nat) : Prop :=
  Nonempty (CanTypeJudgment Γ A i)

abbrev CanTypeFundExp (Γ : Ctx) (A : Tm) (i : Nat) : Prop :=
  Nonempty {J : CanTypeJudgment Γ A i // J.typeData.Expansive}

abbrev CanFundAt (Γ : Ctx) (m A : Tm) (TA : CanTypeData Γ A) : Prop :=
  Nonempty (CanTermDataAt Γ m A TA)

namespace CanFund

noncomputable def choose {Γ : Ctx} {m A : Tm}
    (J : CanFund Γ m A) : CanTermData Γ m A :=
  Classical.choice J

lemma ofTermData {Γ : Ctx} {m A : Tm}
    (J : CanTermData Γ m A) : CanFund Γ m A :=
  ⟨J⟩

lemma weaken {Γ : Ctx} {m A B : Tm} :
    CanFund Γ m A -> CanFund (B :: Γ) m.[shift 1] A.[shift 1] := by
  intro J
  exact CanFund.ofTermData (CanTermData.weaken (B := B) (CanFund.choose J))

lemma toCanSemTyped {Γ : Ctx} {m A : Tm} :
    CanFund Γ m A -> CanSemTyped Γ m A := by
  intro J
  exact (CanFund.choose J).toCanSemTyped

lemma srt {Γ : Ctx} (i : Nat) :
    CanFund Γ (.ty i) (.ty (i + 1)) :=
  CanFund.ofTermData (CanTermData.srt i)

lemma var {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) : CanFund Γ (.var x) A :=
  CanFund.ofTermData (CanTermDataAt.var hs).termData

lemma bool {Γ : Ctx} : CanFund Γ .bool (.ty 0) :=
  CanFund.ofTermData CanTermData.bool

lemma bot {Γ : Ctx} : CanFund Γ .bot (.ty 0) :=
  CanFund.ofTermData CanTermData.bot

lemma tt {Γ : Ctx} : CanFund Γ .tt .bool :=
  CanFund.ofTermData CanTermData.tt

lemma ff {Γ : Ctx} : CanFund Γ .ff .bool :=
  CanFund.ofTermData CanTermData.ff

lemma convWeak {Γ : Ctx} {A B m : Tm} {i : Nat} :
    A === B ->
    CanFund Γ m A ->
    CanTypeFund Γ B i ->
    CanFund Γ m B := by
  intro _eq J TB
  exact CanFund.ofTermData
    ((CanFund.choose J).retagWeak (Classical.choice TB).typeData)

lemma toTypeFundWeak {Γ : Ctx} {A : Tm} {i : Nat} :
    CanFund Γ A (.ty i) -> CanTypeFund Γ A i := by
  intro J
  exact ⟨CanTypeJudgment.ofTermDataWeak (CanFund.choose J)⟩

end CanFund

namespace FundFund

lemma ofCanFund {Γ : Ctx} {m A : Tm}
    (J : CanFund Γ m A) : FundFund Γ m A :=
  FundFund.ofTermData
    (FundTermData.ofCanTermData (CanFund.choose J))

end FundFund

namespace CanTypeFund

noncomputable def choose {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFund Γ A i) : CanTypeJudgment Γ A i :=
  Classical.choice J

lemma ofTypeJudgment {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeJudgment Γ A i) : CanTypeFund Γ A i :=
  ⟨J⟩

lemma weaken {Γ : Ctx} {A B : Tm} {i : Nat} :
    CanTypeFund Γ A i -> CanTypeFund (B :: Γ) A.[shift 1] i := by
  intro J
  exact CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.weaken (B := B) (CanTypeFund.choose J))

lemma toCanFund {Γ : Ctx} {A : Tm} {i : Nat} :
    CanTypeFund Γ A i -> CanFund Γ A (.ty i) := by
  intro J
  exact CanFund.ofTermData (CanTypeFund.choose J).toTermData

lemma ty (Γ : Ctx) (i : Nat) :
    CanTypeFund Γ (.ty i) (i + 1) :=
  CanTypeFund.ofTypeJudgment (CanTypeJudgment.ty Γ i)

lemma bool (Γ : Ctx) :
    CanTypeFund Γ .bool 0 :=
  CanTypeFund.ofTypeJudgment (CanTypeJudgment.bool Γ)

lemma bot (Γ : Ctx) :
    CanTypeFund Γ .bot 0 :=
  CanTypeFund.ofTypeJudgment (CanTypeJudgment.bot Γ)

lemma pi {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeFund Γ A iA)
    (TB : CanTypeFund (A :: Γ) B iB)
    (hTB : (CanTypeFund.choose TB).typeData.Expansive) :
    CanTypeFund Γ (.pi A B) (max iA iB) :=
  CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.pi (CanTypeFund.choose TA) (CanTypeFund.choose TB) hTB)

lemma piAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeFund Γ A iA)
    (TB : CanTypeFund (A :: Γ) B iB)
    (hTB : (CanTypeFund.choose TB).typeData.Expansive) :
    CanTypeFund Γ (.pi A B) i :=
  CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.piAt (i := i)
      (CanTypeFund.choose TA) (CanTypeFund.choose TB) hTB)

lemma sig {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeFund Γ A iA)
    (TB : CanTypeFund (A :: Γ) B iB) :
    CanTypeFund Γ (.sig A B) (max iA iB) :=
  CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.sig (CanTypeFund.choose TA) (CanTypeFund.choose TB))

lemma sigAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeFund Γ A iA)
    (TB : CanTypeFund (A :: Γ) B iB) :
    CanTypeFund Γ (.sig A B) i :=
  CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.sigAt (i := i)
      (CanTypeFund.choose TA) (CanTypeFund.choose TB))

lemma sigmaBranch {Γ : Ctx} {A B C : Tm} {i : Nat}
    (TC : CanTypeFund (.sig A B :: Γ) C i) :
    CanTypeFund (B :: A :: Γ)
      C.[.tup (.var 1) (.var 0) .: shift 2] i :=
  CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.sigmaBranch (CanTypeFund.choose TC))

lemma idnByEquiv {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeFund Γ A i)
    (Jm : CanTermDataAt Γ m A (CanTypeFund.choose TA).typeData)
    (Jn : CanTermDataAt Γ n A (CanTypeFund.choose TA).typeData) :
    CanTypeFund Γ (.idn A m n) i :=
  CanTypeFund.ofTypeJudgment
    (CanTypeJudgment.idnByEquiv (CanTypeFund.choose TA) Jm Jn)

lemma convWeak {Γ : Ctx} {A B : Tm} {i j : Nat} :
    A === B ->
    CanTypeFund Γ A i ->
    CanFund Γ B (.ty j) ->
    CanTypeFund Γ B j := by
  intro _eq _JA JB
  exact CanFund.toTypeFundWeak JB

end CanTypeFund

namespace CanTypeFundExp

noncomputable def choose {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFundExp Γ A i) :
    {J : CanTypeJudgment Γ A i // J.typeData.Expansive} :=
  Classical.choice J

noncomputable def judgment {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFundExp Γ A i) : CanTypeJudgment Γ A i :=
  (CanTypeFundExp.choose J).val

noncomputable def typeData {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFundExp Γ A i) : CanTypeData Γ A :=
  (CanTypeFundExp.judgment J).typeData

lemma expansive {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFundExp Γ A i) :
    (CanTypeFundExp.typeData J).Expansive :=
  (CanTypeFundExp.choose J).property

lemma inUniv {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFundExp Γ A i) :
    (CanTypeData.univ Γ i).CanSemTm A :=
  (CanTypeFundExp.judgment J).inUniv

lemma toCanFundAt {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeFundExp Γ A i) :
    CanFundAt Γ A (.ty i) (CanTypeData.univ Γ i) :=
  ⟨CanTermDataAt.ofTermData (CanTypeData.univ Γ i)
    (CanTypeFundExp.judgment J).toTermData
    (CanTypeData.Equiv.refl (CanTypeData.univ Γ i))⟩

lemma ofTypeJudgment {Γ : Ctx} {A : Tm} {i : Nat}
    (J : CanTypeJudgment Γ A i) (hJ : J.typeData.Expansive) :
    CanTypeFundExp Γ A i :=
  ⟨⟨J, hJ⟩⟩

lemma toCanTypeFund {Γ : Ctx} {A : Tm} {i : Nat} :
    CanTypeFundExp Γ A i -> CanTypeFund Γ A i := by
  intro J
  exact CanTypeFund.ofTypeJudgment (CanTypeFundExp.judgment J)

lemma toCanFund {Γ : Ctx} {A : Tm} {i : Nat} :
    CanTypeFundExp Γ A i -> CanFund Γ A (.ty i) := by
  intro J
  exact CanTypeFund.toCanFund (CanTypeFundExp.toCanTypeFund J)

lemma ofCanFund {Γ : Ctx} {A : Tm} {i : Nat} :
    CanFund Γ A (.ty i) -> CanTypeFundExp Γ A i := by
  intro J
  let hA : CanSemTyped Γ A (.ty i) := (CanFund.choose J).toCanSemTyped
  exact CanTypeFundExp.ofTypeJudgment
    (CanTypeJudgment.ofCanSemTypedType hA)
    (CanTypeData.ofCanSemTypedType_expansive hA)

lemma weaken {Γ : Ctx} {A B : Tm} {i : Nat} :
    CanTypeFundExp Γ A i -> CanTypeFundExp (B :: Γ) A.[shift 1] i := by
  intro J
  let J' := CanTypeFundExp.judgment J
  exact CanTypeFundExp.ofTypeJudgment
    (CanTypeJudgment.weaken (B := B) J')
    (CanTypeData.weaken_expansive J'.typeData (CanTypeFundExp.expansive J))

lemma ty (Γ : Ctx) (i : Nat) :
    CanTypeFundExp Γ (.ty i) (i + 1) :=
  CanTypeFundExp.ofCanFund (CanFund.srt i)

lemma bool (Γ : Ctx) :
    CanTypeFundExp Γ .bool 0 :=
  CanTypeFundExp.ofCanFund CanFund.bool

lemma bot (Γ : Ctx) :
    CanTypeFundExp Γ .bot 0 :=
  CanTypeFundExp.ofCanFund CanFund.bot

lemma pi {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB) :
    CanTypeFundExp Γ (.pi A B) (max iA iB) := by
  let TA' := CanTypeFundExp.choose TA
  let TB' := CanTypeFundExp.choose TB
  exact CanTypeFundExp.ofCanFund
    (CanFund.ofTermData (CanTermData.piType TA'.val TB'.val TB'.property))

noncomputable def piJudgmentAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB) :
    CanTypeJudgment Γ (.pi A B) i :=
  CanTypeJudgment.piAt (i := i)
    (CanTypeFundExp.judgment TA) (CanTypeFundExp.judgment TB)
    (CanTypeFundExp.expansive TB)

lemma sig {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB) :
    CanTypeFundExp Γ (.sig A B) (max iA iB) := by
  let TA' := CanTypeFundExp.choose TA
  let TB' := CanTypeFundExp.choose TB
  exact CanTypeFundExp.ofCanFund
    (CanFund.ofTermData (CanTermData.sigType TA'.val TB'.val))

noncomputable def sigJudgmentAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB) :
    CanTypeJudgment Γ (.sig A B) i :=
  CanTypeJudgment.sigAt (i := i)
    (CanTypeFundExp.judgment TA) (CanTypeFundExp.judgment TB)

noncomputable def sigmaBranchJudgment {Γ : Ctx} {A B C : Tm} {i : Nat}
    (TC : CanTypeFundExp (.sig A B :: Γ) C i) :
    CanTypeJudgment (B :: A :: Γ)
      C.[.tup (.var 1) (.var 0) .: shift 2] i :=
  CanTypeJudgment.sigmaBranch (CanTypeFundExp.judgment TC)

lemma idnByEquiv {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeFundExp Γ A i)
    (Jm : CanTermDataAt Γ m A (CanTypeFundExp.typeData TA))
    (Jn : CanTermDataAt Γ n A (CanTypeFundExp.typeData TA)) :
    CanTypeFundExp Γ (.idn A m n) i := by
  let TA' := CanTypeFundExp.judgment TA
  exact CanTypeFundExp.ofCanFund
    (CanFund.ofTermData (CanTermData.idnType TA' Jm Jn))

noncomputable def idnJudgment {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeFundExp Γ A i)
    (Jm : CanTermDataAt Γ m A (CanTypeFundExp.typeData TA))
    (Jn : CanTermDataAt Γ n A (CanTypeFundExp.typeData TA)) :
    CanTypeJudgment Γ (.idn A m n) i :=
  CanTypeJudgment.idnByEquiv
    (CanTypeFundExp.judgment TA) Jm Jn

noncomputable def idBranchJudgment {Γ : Ctx} {A B a : Tm} {i iB : Nat}
    (TB : CanTypeFundExp Γ B iB)
    (Ja : CanFundAt Γ a B (CanTypeFundExp.typeData TB))
    (TA : CanTypeFundExp
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A i) :
    CanTypeJudgment Γ A.[.rfl a,a/] i :=
  CanTypeJudgment.idBranch (CanTypeFundExp.typeData TB)
    (Classical.choice Ja).canSemTm (CanTypeFundExp.judgment TA)

noncomputable def idTargetJudgment {Γ : Ctx} {A B a b n : Tm} {i iB : Nat}
    (TB : CanTypeFundExp Γ B iB)
    (Ja : CanFundAt Γ a B (CanTypeFundExp.typeData TB))
    (Jb : CanFundAt Γ b B (CanTypeFundExp.typeData TB))
    (Jn : CanFundAt Γ n (.idn B a b)
      (CanTypeFundExp.idnJudgment TB
        (Classical.choice Ja) (Classical.choice Jb)).typeData)
    (TA : CanTypeFundExp
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A i) :
    CanTypeJudgment Γ A.[n,b/] i :=
  CanTypeJudgment.idTarget (CanTypeFundExp.typeData TB)
    (Classical.choice Ja).canSemTm (Classical.choice Jb).canSemTm
    (Classical.choice Jn).canSemTm (CanTypeFundExp.judgment TA)

lemma convWeak {Γ : Ctx} {A B : Tm} {i j : Nat} :
    A === B ->
    CanTypeFundExp Γ A i ->
    CanFund Γ B (.ty j) ->
    CanTypeFundExp Γ B j := by
  intro _eq _JA JB
  exact CanTypeFundExp.ofCanFund JB

end CanTypeFundExp

namespace CanFundAt

noncomputable def choose {Γ : Ctx} {m A : Tm} {TA : CanTypeData Γ A}
    (J : CanFundAt Γ m A TA) : CanTermDataAt Γ m A TA :=
  Classical.choice J

lemma ofTermDataAt {Γ : Ctx} {m A : Tm} {TA : CanTypeData Γ A}
    (J : CanTermDataAt Γ m A TA) : CanFundAt Γ m A TA :=
  ⟨J⟩

lemma ofCanFundEquiv {Γ : Ctx} {m A : Tm} {TA : CanTypeData Γ A}
    (J : CanFund Γ m A)
    (hEq : CanTypeData.Equiv (CanFund.choose J).typeData TA) :
    CanFundAt Γ m A TA :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.ofTermData TA (CanFund.choose J) hEq)

lemma weaken {Γ : Ctx} {m A B : Tm} {TA : CanTypeData Γ A}
    (J : CanFundAt Γ m A TA) :
    CanFundAt (B :: Γ) m.[shift 1] A.[shift 1]
      (CanTypeData.weaken (B := B) TA) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.weaken (B := B) (CanFundAt.choose J))

lemma toCanFund {Γ : Ctx} {m A : Tm} {TA : CanTypeData Γ A} :
    CanFundAt Γ m A TA -> CanFund Γ m A := by
  intro J
  exact CanFund.ofTermData (CanFundAt.choose J).termData

lemma retag {Γ : Ctx} {m A : Tm} {TA TB : CanTypeData Γ A}
    (J : CanFundAt Γ m A TA)
    (hEq : CanTypeData.Equiv TA TB) :
    CanFundAt Γ m A TB :=
  CanFundAt.ofTermDataAt ((CanFundAt.choose J).retag hEq)

lemma convType {Γ : Ctx} {A B m : Tm} {TA : CanTypeData Γ A}
    (J : CanFundAt Γ m A TA)
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ]) :
    CanFundAt Γ m B (TA.convType hB) :=
  CanFundAt.ofTermDataAt ((CanFundAt.choose J).convType hB)

lemma convExactTarget {Γ : Ctx} {A B m : Tm}
    (TB : CanTypeData Γ B)
    (hA : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step A.[σ])
    (hB : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step B.[σ])
    (J : CanFundAt Γ m A (TB.convType hA)) :
    CanFundAt Γ m B TB :=
  CanFundAt.retag (CanFundAt.convType J hB)
    (CanTypeData.Equiv.trans
      (CanTypeData.convType_equiv_left (TB.convType hA) hB)
      (CanTypeData.convType_equiv_left TB hA))

lemma srt {Γ : Ctx} (i : Nat) :
    CanFundAt Γ (.ty i) (.ty (i + 1)) (CanTypeData.univ Γ (i + 1)) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.srt i)

lemma var {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) :
    CanFundAt Γ (.var x) A
      (CanTypeData.lookup hs) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.var hs)

lemma varZero {Γ : Ctx} {A : Tm} :
    CanFundAt (A :: Γ) (.var 0) A.[shift 1]
      (CanTypeData.varZero Γ A) :=
  CanFundAt.ofTermDataAt CanTermDataAt.varZero

lemma varSucc {Γ : Ctx} {A B : Tm} {x : Var}
    {TA : CanTypeData Γ A}
    (J : CanFundAt Γ (.var x) A TA) :
    CanFundAt (B :: Γ) (.var (x + 1)) A.[shift 1]
      (CanTypeData.weaken (B := B) TA) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.varSucc (CanFundAt.choose J))

lemma bool {Γ : Ctx} :
    CanFundAt Γ .bool (.ty 0) (CanTypeData.univ Γ 0) :=
  CanFundAt.ofTermDataAt CanTermDataAt.bool

lemma bot {Γ : Ctx} :
    CanFundAt Γ .bot (.ty 0) (CanTypeData.univ Γ 0) :=
  CanFundAt.ofTermDataAt CanTermDataAt.bot

lemma tt {Γ : Ctx} :
    CanFundAt Γ .tt .bool (CanTypeData.bool Γ) :=
  CanFundAt.ofTermDataAt CanTermDataAt.tt

lemma ff {Γ : Ctx} :
    CanFundAt Γ .ff .bool (CanTypeData.bool Γ) :=
  CanFundAt.ofTermDataAt CanTermDataAt.ff

lemma piType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    CanFundAt Γ (.pi A B) (.ty (max iA iB))
      (CanTypeData.univ Γ (max iA iB)) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.piType TA TB hTB)

lemma piTypeAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    CanFundAt Γ (.pi A B) (.ty i) (CanTypeData.univ Γ i) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.ofTermData (CanTypeData.univ Γ i)
      (CanTypeJudgment.piAt (i := i) TA TB hTB).toTermData
      (CanTypeData.Equiv.refl (CanTypeData.univ Γ i)))

lemma sigType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB) :
    CanFundAt Γ (.sig A B) (.ty (max iA iB))
      (CanTypeData.univ Γ (max iA iB)) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.sigType TA TB)

lemma sigTypeAt {Γ : Ctx} {A B : Tm} {i iA iB : Nat}
    (TA : CanTypeJudgment Γ A iA)
    (TB : CanTypeJudgment (A :: Γ) B iB) :
    CanFundAt Γ (.sig A B) (.ty i) (CanTypeData.univ Γ i) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.ofTermData (CanTypeData.univ Γ i)
      (CanTypeJudgment.sigAt (i := i) TA TB).toTermData
      (CanTypeData.Equiv.refl (CanTypeData.univ Γ i)))

lemma idnType {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeJudgment Γ A i)
    (Jm : CanFundAt Γ m A TA.typeData)
    (Jn : CanFundAt Γ n A TA.typeData) :
    CanFundAt Γ (.idn A m n) (.ty i) (CanTypeData.univ Γ i) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.idnType TA (CanFundAt.choose Jm) (CanFundAt.choose Jn))

lemma piTypeExp {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB) :
    CanFundAt Γ (.pi A B) (.ty (max iA iB))
      (CanTypeData.univ Γ (max iA iB)) :=
  CanTypeFundExp.toCanFundAt (CanTypeFundExp.pi TA TB)

lemma sigTypeExp {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB) :
    CanFundAt Γ (.sig A B) (.ty (max iA iB))
      (CanTypeData.univ Γ (max iA iB)) :=
  CanTypeFundExp.toCanFundAt (CanTypeFundExp.sig TA TB)

lemma idnTypeExp {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : CanTypeFundExp Γ A i)
    (Jm : CanFundAt Γ m A (CanTypeFundExp.typeData TA))
    (Jn : CanFundAt Γ n A (CanTypeFundExp.typeData TA)) :
    CanFundAt Γ (.idn A m n) (.ty i) (CanTypeData.univ Γ i) :=
  CanTypeFundExp.toCanFundAt
    (CanTypeFundExp.idnByEquiv TA (CanFundAt.choose Jm) (CanFundAt.choose Jn))

lemma rfl {Γ : Ctx} {A m : Tm}
    (TA : CanTypeData Γ A)
    (Jm : CanFundAt Γ m A TA) :
    CanFundAt Γ (.rfl m) (.idn A m m)
      (CanTypeData.idn TA (CanFundAt.choose Jm).canSemTm
        (CanFundAt.choose Jm).canSemTm) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.rfl TA (CanFundAt.choose Jm))

lemma rflExp {Γ : Ctx} {A m : Tm} {i : Nat}
    (TA : CanTypeFundExp Γ A i)
    (Jm : CanFundAt Γ m A (CanTypeFundExp.typeData TA)) :
    CanFundAt Γ (.rfl m) (.idn A m m)
      (CanTypeFundExp.idnJudgment TA
        (CanFundAt.choose Jm) (CanFundAt.choose Jm)).typeData :=
  CanFundAt.rfl (CanTypeFundExp.typeData TA) Jm

lemma lam {Γ : Ctx} {A B m : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFundAt (A :: Γ) m B TB) :
    CanFundAt Γ (.lam A m) (.pi A B) (CanTypeData.kpi TA TB hTB) :=
  CanFundAt.ofTermDataAt (CanTermDataAt.lam TA TB hTB (CanFundAt.choose Jm))

lemma lamExp {Γ : Ctx} {A B m : Tm} {i iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt (A :: Γ) m B (CanTypeFundExp.typeData TB)) :
    CanFundAt Γ (.lam A m) (.pi A B)
      (CanTypeFundExp.piJudgmentAt (i := i) TA TB).typeData :=
  CanFundAt.lam (CanTypeFundExp.typeData TA) (CanTypeFundExp.typeData TB)
    (CanTypeFundExp.expansive TB) Jm

lemma app {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m (.pi A B) (CanTypeData.kpi TA TB hTB))
    (Jn : CanFundAt Γ n A TA) :
    CanFundAt Γ (.app m n) B.[n/]
      (CanTypeData.subst1 TA TB (CanFundAt.choose Jn).canSemTm) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.app TA TB hTB (CanFundAt.choose Jm) (CanFundAt.choose Jn))

lemma appRetagTarget {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m (.pi A B) (CanTypeData.kpi TA TB hTB))
    (Jn : CanFundAt Γ n A TA)
    (TC : CanTypeData Γ B.[n/])
    (hTarget : CanTypeData.Equiv
      (CanTypeData.subst1 TA TB (CanFundAt.choose Jn).canSemTm) TC) :
    CanFundAt Γ (.app m n) B.[n/] TC :=
  CanFundAt.retag (CanFundAt.app TA TB hTB Jm Jn) hTarget

lemma appExp {Γ : Ctx} {A B m n : Tm} {i iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt Γ m (.pi A B)
      (CanTypeFundExp.piJudgmentAt (i := i) TA TB).typeData)
    (Jn : CanFundAt Γ n A (CanTypeFundExp.typeData TA)) :
    CanFundAt Γ (.app m n) B.[n/]
      (CanTypeData.subst1 (CanTypeFundExp.typeData TA)
        (CanTypeFundExp.typeData TB) (CanFundAt.choose Jn).canSemTm) :=
  CanFundAt.app (CanTypeFundExp.typeData TA) (CanTypeFundExp.typeData TB)
    (CanTypeFundExp.expansive TB) Jm Jn

lemma appExpRetagTarget {Γ : Ctx} {A B m n : Tm} {i iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt Γ m (.pi A B)
      (CanTypeFundExp.piJudgmentAt (i := i) TA TB).typeData)
    (Jn : CanFundAt Γ n A (CanTypeFundExp.typeData TA))
    (TC : CanTypeData Γ B.[n/])
    (hTarget : CanTypeData.Equiv
      (CanTypeData.subst1 (CanTypeFundExp.typeData TA)
        (CanTypeFundExp.typeData TB) (CanFundAt.choose Jn).canSemTm) TC) :
    CanFundAt Γ (.app m n) B.[n/] TC :=
  CanFundAt.retag (CanFundAt.appExp TA TB Jm Jn) hTarget

lemma tup {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (Jm : CanFundAt Γ m A TA)
    (Jn : CanFundAt Γ n B.[m/]
      (CanTypeData.subst1 TA TB (CanFundAt.choose Jm).canSemTm)) :
    CanFundAt Γ (.tup m n) (.sig A B) (CanTypeData.ksig TA TB) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.tup TA TB (CanFundAt.choose Jm) (CanFundAt.choose Jn))

lemma tupExp {Γ : Ctx} {A B m n : Tm} {i iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt Γ m A (CanTypeFundExp.typeData TA))
    (Jn : CanFundAt Γ n B.[m/]
      (CanTypeData.subst1 (CanTypeFundExp.typeData TA)
        (CanTypeFundExp.typeData TB) (CanFundAt.choose Jm).canSemTm)) :
    CanFundAt Γ (.tup m n) (.sig A B)
      (CanTypeFundExp.sigJudgmentAt (i := i) TA TB).typeData :=
  CanFundAt.tup (CanTypeFundExp.typeData TA)
    (CanTypeFundExp.typeData TB) Jm Jn

lemma prjBranch {Γ : Ctx} {A B C m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (Jm : CanFundAt Γ m (.sig A B) (CanTypeData.ksig TA TB))
    (hn : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
        CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (CanSemCtx.weakens hΓ)
      let hΓS : CanSemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        CanSemCtx.consInterp hΓ K
          (TypeInterp.ksig_weakens IA IB (CanSemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (CanSemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    CanFundAt Γ (.prj C m n) C.[m/]
      (CanTypeData.subst1 (CanTypeData.ksig TA TB) TC
        (CanFundAt.choose Jm).canSemTm) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.prjBranch TA TB TC hTC (CanFundAt.choose Jm) hn)

lemma prjBranchExact {Γ : Ctx} {A B C m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (Jm : CanFundAt Γ m (.sig A B) (CanTypeData.ksig TA TB))
    (Jn : CanFundAt (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2]
      (CanTypeData.sigmaBranch TC)) :
    CanFundAt Γ (.prj C m n) C.[m/]
      (CanTypeData.subst1 (CanTypeData.ksig TA TB) TC
        (CanFundAt.choose Jm).canSemTm) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.prjBranchExact TA TB TC hTC
      (CanFundAt.choose Jm) (CanFundAt.choose Jn))

lemma rwTarget {Γ : Ctx} {A B m n a b : Tm}
    (TB : CanTypeData Γ B)
    (Ja : CanFundAt Γ a B TB)
    (Jb : CanFundAt Γ b B TB)
    (Jn : CanFundAt Γ n (.idn B a b)
      (CanTypeData.idn TB (CanFundAt.choose Ja).canSemTm
        (CanFundAt.choose Jb).canSemTm))
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (hTA : TA.Expansive)
    (hrfl : ∀ {Δ : DCandCtx} (hΓ : CanSemCtx Γ Δ),
      let IB := TB.interp hΓ
      let hΓB : CanSemCtx (B :: Γ) (DCandCtx.extend IB) :=
        CanSemCtx.consInterp hΓ IB (TB.weakens hΓ)
      let IP := TypeInterp.idProof IB ((CanFundAt.choose Ja).canSemTm hΓ)
      let hΓP : CanSemCtx
          (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ)
          (DCandCtx.extend IP) :=
        CanSemCtx.consInterp hΓB IP
          (TypeInterp.idProof_weakens IB ((CanFundAt.choose Ja).canSemTm hΓ))
      let IA := TA.interp hΓP
      ∀ σ, Δ.valid σ -> ∀ c,
        (IA.cand (.rfl c .: b.[σ] .: σ)).mem m.[σ]) :
    CanFundAt Γ (.rw A m n) A.[n,b/]
      (CanTypeData.idTarget TB (CanFundAt.choose Ja).canSemTm
        (CanFundAt.choose Jb).canSemTm (CanFundAt.choose Jn).canSemTm TA) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.rwTarget TB (CanFundAt.choose Ja) (CanFundAt.choose Jb)
      (CanFundAt.choose Jn) TA hTA hrfl)

lemma ite {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : CanTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m .bool (CanTypeData.bool Γ))
    (Jn1 : CanFundAt Γ n1 A.[.tt/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.tt))
    (Jn2 : CanFundAt Γ n2 A.[.ff/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.ff)) :
    CanFundAt Γ (.ite A m n1 n2) A.[m/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB
        (CanFundAt.choose Jm).canSemTm) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.ite TB hTB (CanFundAt.choose Jm)
      (CanFundAt.choose Jn1) (CanFundAt.choose Jn2))

lemma exf {Γ : Ctx} {A m : Tm}
    (TB : CanTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m .bot (CanTypeData.bot Γ)) :
    CanFundAt Γ (.exf A m) A.[m/]
      (CanTypeData.subst1 (CanTypeData.bot Γ) TB
        (CanFundAt.choose Jm).canSemTm) :=
  CanFundAt.ofTermDataAt
    (CanTermDataAt.exf TB hTB (CanFundAt.choose Jm))

end CanFundAt

namespace CanFund

lemma ofSubstSN {Γ : Ctx} {m A : Tm}
    (hA : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step A.[σ])
    (hm : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step m.[σ]) :
    CanFund Γ m A :=
  CanFund.ofTermData
    { typeData :=
        { interp := fun hΓ =>
            TypeInterp.const _ A Candidate.snCandidate (hA hΓ)
          weakens := fun _hΓ =>
            TypeInterp.const_weakens Candidate.snCandidate_weakens }
      canSemTm := by
        intro Δ hΓ σ hσ
        exact hm hΓ σ hσ }

lemma idnTypeSN {Γ : Ctx} {A m n : Tm} {i : Nat}
    (JA : CanFund Γ A (.ty i))
    (Jm : CanFund Γ m A)
    (Jn : CanFund Γ n A) :
    CanFund Γ (.idn A m n) (.ty i) :=
  CanFund.ofTermData
    { typeData := CanTypeData.univ Γ i
      canSemTm := by
        intro Δ hΓ σ hσ
        change (Candidate.univ i).mem (.idn A.[σ] m.[σ] n.[σ])
        refine ⟨TypeCodeInterp.ofSN i _ ?_, trivial⟩
        exact sn_idn
          (CanSemTyped.sn_subst (CanFund.toCanSemTyped JA) hΓ σ hσ)
          (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ σ hσ)
          (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jn) hΓ σ hσ) }

lemma lamSN {Γ : Ctx} {A B m : Tm} {iA : Nat}
    (JA : CanFund Γ A (.ty iA))
    (Jm : CanFund (A :: Γ) m B) :
    CanFund Γ (.lam A m) (.pi A B) := by
  let TA := CanTypeFundExp.typeData (CanTypeFundExp.ofCanFund JA)
  apply CanFund.ofSubstSN
  · intro Δ hΓ σ hσ
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    have hσA : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) (CanSemCtx.weakens hΓ) hσ
    change SN Step (.pi A.[σ] B.[up σ])
    exact sn_pi
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped JA) hΓ σ hσ)
      ((CanFund.choose Jm).typeData.interp hΓA |>.type_sn (up σ) hσA)
  · intro Δ hΓ σ hσ
    let IA := TA.interp hΓ
    let hΓA : CanSemCtx (A :: Γ) (DCandCtx.extend IA) :=
      CanSemCtx.consInterp hΓ IA (TA.weakens hΓ)
    have hσA : (DCandCtx.extend IA).valid (up σ) :=
      DCandCtx.extend_up_valid (I := IA) (CanSemCtx.weakens hΓ) hσ
    change SN Step (.lam A.[σ] m.[up σ])
    exact sn_lam
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped JA) hΓ σ hσ)
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓA (up σ) hσA)

lemma tupSN {Γ : Ctx} {A B m n : Tm} {i : Nat}
    (JS : CanFund Γ (.sig A B) (.ty i))
    (Jm : CanFund Γ m A)
    (Jn : CanFund Γ n B.[m/]) :
    CanFund Γ (.tup m n) (.sig A B) :=
  CanFund.ofSubstSN
    (fun hΓ σ hσ =>
      CanSemTyped.sn_subst (CanFund.toCanSemTyped JS) hΓ σ hσ)
    (fun hΓ σ hσ =>
      sn_tup
        (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ σ hσ)
        (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jn) hΓ σ hσ))

lemma iteSN {Γ : Ctx} {A m n1 n2 : Tm} {i : Nat}
    (JA : CanFund (.bool :: Γ) A (.ty i))
    (Jm : CanFund Γ m .bool)
    (Jn1 : CanFund Γ n1 A.[.tt/])
    (Jn2 : CanFund Γ n2 A.[.ff/]) :
    CanFund Γ (.ite A m n1 n2) A.[m/] := by
  let TA := CanTypeFundExp.typeData (CanTypeFundExp.ofCanFund JA)
  apply CanFund.ofSubstSN
  · intro Δ hΓ σ hσ
    let hΓB : CanSemCtx (.bool :: Γ) (DCandCtx.extend (TypeInterp.bool Δ)) :=
      CanSemCtx.consInterp hΓ (TypeInterp.bool Δ) (TypeInterp.bool_weakens Δ)
    have snm : SN Step m.[σ] :=
      CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ σ hσ
    have hm : (TypeInterp.bool Δ).SemTm m := by
      intro τ hτ
      change Candidate.bool.mem m.[τ]
      exact CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ τ hτ
    have hσm : (DCandCtx.extend (TypeInterp.bool Δ)).valid (m.[σ] .: σ) :=
      DCandCtx.extend_cons hσ (hm σ hσ)
    have hsnA := (TA.interp hΓB).type_sn (m.[σ] .: σ) hσm
    have hsubst : A.[m/].[σ] = A.[m.[σ] .: σ] := by
      asimp
    rw [hsubst]
    exact hsnA
  · intro Δ hΓ σ hσ
    let hΓB : CanSemCtx (.bool :: Γ) (DCandCtx.extend (TypeInterp.bool Δ)) :=
      CanSemCtx.consInterp hΓ (TypeInterp.bool Δ) (TypeInterp.bool_weakens Δ)
    have hσB : (DCandCtx.extend (TypeInterp.bool Δ)).valid (up σ) :=
      DCandCtx.extend_up_valid (I := TypeInterp.bool Δ) (CanSemCtx.weakens hΓ) hσ
    have snA : SN Step A.[up σ] :=
      (TA.interp hΓB).type_sn (up σ) hσB
    change SN Step (.ite A.[up σ] m.[σ] n1.[σ] n2.[σ])
    exact sn_ite snA
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ σ hσ)
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jn1) hΓ σ hσ)
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jn2) hΓ σ hσ)

lemma exfSN {Γ : Ctx} {A m : Tm} {i : Nat}
    (JA : CanFund (.bot :: Γ) A (.ty i))
    (Jm : CanFund Γ m .bot) :
    CanFund Γ (.exf A m) A.[m/] := by
  let TA := CanTypeFundExp.typeData (CanTypeFundExp.ofCanFund JA)
  apply CanFund.ofSubstSN
  · intro Δ hΓ σ hσ
    let hΓB : CanSemCtx (.bot :: Γ) (DCandCtx.extend (TypeInterp.bot Δ)) :=
      CanSemCtx.consInterp hΓ (TypeInterp.bot Δ) (TypeInterp.bot_weakens Δ)
    have hm : (TypeInterp.bot Δ).SemTm m := by
      intro τ hτ
      change Candidate.bot.mem m.[τ]
      exact CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ τ hτ
    have hσm : (DCandCtx.extend (TypeInterp.bot Δ)).valid (m.[σ] .: σ) :=
      DCandCtx.extend_cons hσ (hm σ hσ)
    have hsnA := (TA.interp hΓB).type_sn (m.[σ] .: σ) hσm
    have hsubst : A.[m/].[σ] = A.[m.[σ] .: σ] := by
      asimp
    rw [hsubst]
    exact hsnA
  · intro Δ hΓ σ hσ
    let hΓB : CanSemCtx (.bot :: Γ) (DCandCtx.extend (TypeInterp.bot Δ)) :=
      CanSemCtx.consInterp hΓ (TypeInterp.bot Δ) (TypeInterp.bot_weakens Δ)
    have hσB : (DCandCtx.extend (TypeInterp.bot Δ)).valid (up σ) :=
      DCandCtx.extend_up_valid (I := TypeInterp.bot Δ) (CanSemCtx.weakens hΓ) hσ
    have snA : SN Step A.[up σ] :=
      (TA.interp hΓB).type_sn (up σ) hσB
    change SN Step (.exf A.[up σ] m.[σ])
    exact sn_exf snA
      (CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ σ hσ)

lemma rwSN {Γ : Ctx} {A B m n a b : Tm} {i : Nat}
    (JA : CanFund
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A (.ty i))
    (Jm : CanFund Γ m A.[.rfl a,a/])
    (Jn : CanFund Γ n (.idn B a b)) :
    CanFund Γ (.rw A m n) A.[n,b/] := by
  let hIdTySN : ∀ {Δ : DCandCtx} (_hΓ : CanSemCtx Γ Δ),
      ∀ σ, Δ.valid σ -> SN Step (.idn B a b).[σ] := by
    intro Δ hΓ σ hσ
    exact (CanFund.choose Jn).typeData.interp hΓ |>.type_sn σ hσ
  let TB : CanTypeData Γ B :=
    { interp := fun hΓ =>
        TypeInterp.const _ B Candidate.snCandidate
          (fun σ hσ => by
            exact sn_idn_type (hIdTySN hΓ σ hσ))
      weakens := fun _hΓ =>
        TypeInterp.const_weakens Candidate.snCandidate_weakens }
  let TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A :=
    CanTypeData.ofCanSemTypedType (CanFund.toCanSemTyped JA)
  let JaData : CanTermDataAt Γ a B TB :=
    CanTermDataAt.ofTypeData TB (by
      intro Δ hΓ σ hσ
      change SN Step a.[σ]
      exact sn_idn_left (hIdTySN hΓ σ hσ))
  let JbData : CanTermDataAt Γ b B TB :=
    CanTermDataAt.ofTypeData TB (by
      intro Δ hΓ σ hσ
      change SN Step b.[σ]
      exact sn_idn_right (hIdTySN hΓ σ hσ))
  let JnData : CanTermDataAt Γ n (.idn B a b)
      (CanTypeData.idn TB JaData.canSemTm JbData.canSemTm) :=
    CanTermDataAt.ofTypeData
      (CanTypeData.idn TB JaData.canSemTm JbData.canSemTm) (by
        intro Δ hΓ σ hσ
        change SN Step n.[σ]
        exact CanSemTyped.sn_subst (CanFund.toCanSemTyped Jn) hΓ σ hσ)
  let JmData : CanTermDataAt Γ m A.[.rfl a,a/]
      (CanTypeData.idBranch TB JaData.canSemTm TA) :=
    CanTermDataAt.ofTypeData (CanTypeData.idBranch TB JaData.canSemTm TA) (by
      intro Δ hΓ σ hσ
      change SN Step m.[σ]
      exact CanSemTyped.sn_subst (CanFund.toCanSemTyped Jm) hΓ σ hσ)
  exact CanFund.ofTermData
    (CanTermData.rwSNBranch (i := i) TB JaData JbData JnData TA JmData)

lemma rfl {Γ : Ctx} {A m : Tm} :
    CanFund Γ m A -> CanFund Γ (.rfl m) (.idn A m m) := by
  intro J
  exact CanFund.ofTermData (CanTermData.rfl (CanFund.choose J))

lemma rflByEquiv {Γ : Ctx} {A m : Tm}
    (TA : CanTypeData Γ A)
    (J : CanFund Γ m A)
    (hEq : CanTypeData.Equiv (CanFund.choose J).typeData TA) :
    CanFund Γ (.rfl m) (.idn A m m) :=
  CanFund.ofTermData
    (CanTermData.rfl ((CanFund.choose J).retagCanEquiv TA hEq))

lemma lamAt {Γ : Ctx} {A B m : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFundAt (A :: Γ) m B TB) :
    CanFund Γ (.lam A m) (.pi A B) :=
  CanFundAt.toCanFund (CanFundAt.lam TA TB hTB Jm)

lemma lamExp {Γ : Ctx} {A B m : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt (A :: Γ) m B (CanTypeFundExp.typeData TB)) :
    CanFund Γ (.lam A m) (.pi A B) :=
  CanFund.lamAt (CanTypeFundExp.typeData TA) (CanTypeFundExp.typeData TB)
    (CanTypeFundExp.expansive TB) Jm

lemma lamByEquiv {Γ : Ctx} {A B m : Tm} {iA : Nat}
    (TA : CanTypeFund Γ A iA)
    (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFund (A :: Γ) m B)
    (hmEq : CanTypeData.Equiv (CanFund.choose Jm).typeData TB) :
    CanFund Γ (.lam A m) (.pi A B) :=
  CanFund.ofTermData
    (CanTermData.lam (CanTypeFund.choose TA).typeData TB hTB
      (CanFund.choose Jm) hmEq)

lemma appAt {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m (.pi A B) (CanTypeData.kpi TA TB hTB))
    (Jn : CanFundAt Γ n A TA) :
    CanFund Γ (.app m n) B.[n/] :=
  CanFundAt.toCanFund (CanFundAt.app TA TB hTB Jm Jn)

lemma appExp {Γ : Ctx} {A B m n : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt Γ m (.pi A B)
      (CanTypeData.kpi (CanTypeFundExp.typeData TA)
        (CanTypeFundExp.typeData TB) (CanTypeFundExp.expansive TB)))
    (Jn : CanFundAt Γ n A (CanTypeFundExp.typeData TA)) :
    CanFund Γ (.app m n) B.[n/] :=
  CanFund.appAt (CanTypeFundExp.typeData TA) (CanTypeFundExp.typeData TB)
    (CanTypeFundExp.expansive TB) Jm Jn

lemma appByEquiv {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFund Γ m (.pi A B)) (Jn : CanFund Γ n A)
    (hmEq : CanTypeData.Equiv (CanFund.choose Jm).typeData
      (CanTypeData.kpi TA TB hTB))
    (hnEq : CanTypeData.Equiv (CanFund.choose Jn).typeData TA) :
    CanFund Γ (.app m n) B.[n/] :=
  CanFund.ofTermData
    (CanTermData.app TA TB hTB (CanFund.choose Jm) (CanFund.choose Jn)
      hmEq hnEq)

lemma appRetagByEquiv {Γ : Ctx} {P A B m n : Tm} {iP : Nat}
    (TP : CanTypeFund Γ (.pi A B) iP)
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : CanFund Γ m P) (Jn : CanFund Γ n A)
    (hmEq : CanTypeData.Equiv (CanFund.choose Jm).typeData
      (CanTypeData.kpi TA TB hTB))
    (hnEq : CanTypeData.Equiv (CanFund.choose Jn).typeData TA) :
    CanFund Γ (.app m n) B.[n/] :=
  CanFund.ofTermData
    (CanTermData.appRetagByEquiv (CanTypeFund.choose TP) TA TB hTB
      (CanFund.choose Jm) (CanFund.choose Jn) hmEq hnEq)

lemma tupAt {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (Jm : CanFundAt Γ m A TA)
    (Jn : CanFundAt Γ n B.[m/]
      (CanTypeData.subst1 TA TB (CanFundAt.choose Jm).canSemTm)) :
    CanFund Γ (.tup m n) (.sig A B) :=
  CanFundAt.toCanFund (CanFundAt.tup TA TB Jm Jn)

lemma tupExp {Γ : Ctx} {A B m n : Tm} {iA iB : Nat}
    (TA : CanTypeFundExp Γ A iA)
    (TB : CanTypeFundExp (A :: Γ) B iB)
    (Jm : CanFundAt Γ m A (CanTypeFundExp.typeData TA))
    (Jn : CanFundAt Γ n B.[m/]
      (CanTypeData.subst1 (CanTypeFundExp.typeData TA)
        (CanTypeFundExp.typeData TB) (CanFundAt.choose Jm).canSemTm)) :
    CanFund Γ (.tup m n) (.sig A B) :=
  CanFund.tupAt (CanTypeFundExp.typeData TA) (CanTypeFundExp.typeData TB)
    Jm Jn

lemma tupByEquiv {Γ : Ctx} {A B m n : Tm}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (Jm : CanFund Γ m A) (Jn : CanFund Γ n B.[m/])
    (hmEq : CanTypeData.Equiv (CanFund.choose Jm).typeData TA)
    (hnEq : CanTypeData.Equiv (CanFund.choose Jn).typeData
      (CanTypeData.subst1 TA TB
        (CanTypeData.Equiv.semTm hmEq (CanFund.choose Jm).canSemTm))) :
    CanFund Γ (.tup m n) (.sig A B) :=
  CanFund.ofTermData
    (CanTermData.tup TA TB (CanFund.choose Jm) (CanFund.choose Jn)
      hmEq hnEq)

lemma iteAt {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : CanTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m .bool (CanTypeData.bool Γ))
    (Jn1 : CanFundAt Γ n1 A.[.tt/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.tt))
    (Jn2 : CanFundAt Γ n2 A.[.ff/]
      (CanTypeData.subst1 (CanTypeData.bool Γ) TB CanTypeData.ff)) :
    CanFund Γ (.ite A m n1 n2) A.[m/] :=
  CanFundAt.toCanFund (CanFundAt.ite TB hTB Jm Jn1 Jn2)

lemma exfAt {Γ : Ctx} {A m : Tm}
    (TB : CanTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : CanFundAt Γ m .bot (CanTypeData.bot Γ)) :
    CanFund Γ (.exf A m) A.[m/] :=
  CanFundAt.toCanFund (CanFundAt.exf TB hTB Jm)

lemma convExp {Γ : Ctx} {A B m : Tm} {i : Nat} :
    A === B ->
    CanFund Γ m A ->
    CanTypeFundExp Γ B i ->
    CanFund Γ m B := by
  intro eq J TB
  exact CanFund.convWeak eq J (CanTypeFundExp.toCanTypeFund TB)

lemma prjSNBranchAt {Γ : Ctx} {A B C m n : Tm} {iC : Nat}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (Jm : CanFundAt Γ m (.sig A B) (CanTypeData.ksig TA TB))
    (Jn : CanFund (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2]) :
    CanFund Γ (.prj C m n) C.[m/] :=
  CanFund.ofTermData
    (CanTermData.prjSNBranch (iC := iC) TA TB TC
      (CanFundAt.choose Jm) (CanFund.choose Jn))

lemma prjSNBranchByEquiv {Γ : Ctx} {A B C m n : Tm} {iC : Nat}
    (TA : CanTypeData Γ A) (TB : CanTypeData (A :: Γ) B)
    (TC : CanTypeData (.sig A B :: Γ) C)
    (Jm : CanFund Γ m (.sig A B))
    (Jn : CanFund (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2])
    (hmEq : CanTypeData.Equiv (CanFund.choose Jm).typeData
      (CanTypeData.ksig TA TB)) :
    CanFund Γ (.prj C m n) C.[m/] :=
  CanFund.ofTermData
    (CanTermData.prjSNBranch (iC := iC) TA TB TC
      (CanTermDataAt.ofTermData (CanTypeData.ksig TA TB)
        (CanFund.choose Jm) hmEq)
      (CanFund.choose Jn))

lemma rwSNBranchAt {Γ : Ctx} {A B m n a b : Tm} {i : Nat}
    (TB : CanTypeData Γ B)
    (Ja : CanFundAt Γ a B TB)
    (Jb : CanFundAt Γ b B TB)
    (Jn : CanFundAt Γ n (.idn B a b)
      (CanTypeData.idn TB (CanFundAt.choose Ja).canSemTm
        (CanFundAt.choose Jb).canSemTm))
    (TA : CanTypeData
      (.idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ) A)
    (Jm : CanFundAt Γ m A.[.rfl a,a/]
      (CanTypeData.idBranch TB (CanFundAt.choose Ja).canSemTm TA)) :
    CanFund Γ (.rw A m n) A.[n,b/] :=
  CanFund.ofTermData
    (CanTermData.rwSNBranch (i := i) TB
      (CanFundAt.choose Ja) (CanFundAt.choose Jb) (CanFundAt.choose Jn) TA
      (CanFundAt.choose Jm))

end CanFund

namespace SemFund

noncomputable def choose {Γ : Ctx} {m A : Tm}
    (J : SemFund Γ m A) : SemTermData Γ m A :=
  Classical.choice J

lemma ofTermData {Γ : Ctx} {m A : Tm}
    (J : SemTermData Γ m A) : SemFund Γ m A :=
  ⟨J⟩

lemma toSemTyped {Γ : Ctx} {m A : Tm} :
    SemFund Γ m A -> SemTyped Γ m A := by
  intro J
  exact (SemFund.choose J).toSemTyped

lemma srt {Γ : Ctx} (i : Nat) :
    SemFund Γ (.ty i) (.ty (i + 1)) :=
  SemFund.ofTermData (SemTermData.srt i)

lemma var {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) : SemFund Γ (.var x) A :=
  SemFund.ofTermData (SemTermData.var hs)

lemma bool {Γ : Ctx} : SemFund Γ .bool (.ty 0) :=
  SemFund.ofTermData SemTermData.bool

lemma bot {Γ : Ctx} : SemFund Γ .bot (.ty 0) :=
  SemFund.ofTermData SemTermData.bot

lemma tt {Γ : Ctx} : SemFund Γ .tt .bool :=
  SemFund.ofTermData SemTermData.tt

lemma ff {Γ : Ctx} : SemFund Γ .ff .bool :=
  SemFund.ofTermData SemTermData.ff

lemma rfl {Γ : Ctx} {A m : Tm} :
    SemFund Γ m A -> SemFund Γ (.rfl m) (.idn A m m) := by
  intro J
  exact SemFund.ofTermData (SemTermData.rfl (SemFund.choose J))

lemma rflByEquiv {Γ : Ctx} {A m : Tm}
    (TA : SemTypeData Γ A) (J : SemFund Γ m A)
    (hEq : SemTypeData.Equiv (SemFund.choose J).typeData TA) :
    SemFund Γ (.rfl m) (.idn A m m) :=
  SemFund.ofTermData (SemTermData.rflByEquiv TA (SemFund.choose J) hEq)

lemma appByEquiv {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemFund Γ m (.pi A B)) (Jn : SemFund Γ n A)
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.kpi TA TB hTB))
    (hnEq : SemTypeData.Equiv (SemFund.choose Jn).typeData TA) :
    SemFund Γ (.app m n) B.[n/] :=
  SemFund.ofTermData
    (SemTermData.appByEquiv TA TB hTB (SemFund.choose Jm)
      (SemFund.choose Jn) hmEq hnEq)

lemma appRetagByEquiv {Γ : Ctx} {P A B m n : Tm} {iP : Nat}
    (TP : SemTypeFund Γ (.pi A B) iP)
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemFund Γ m P) (Jn : SemFund Γ n A)
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.kpi TA TB hTB))
    (hnEq : SemTypeData.Equiv (SemFund.choose Jn).typeData TA) :
    SemFund Γ (.app m n) B.[n/] :=
  SemFund.ofTermData
    (SemTermData.appRetagByEquiv TP TA TB hTB (SemFund.choose Jm)
      (SemFund.choose Jn) hmEq hnEq)

lemma lamByEquiv {Γ : Ctx} {A B m : Tm} {iA : Nat}
    (TA : SemTypeFund Γ A iA)
    (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemFund (A :: Γ) m B)
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData TB) :
    SemFund Γ (.lam A m) (.pi A B) :=
  SemFund.ofTermData
    (SemTermData.lamByEquiv (Classical.choice TA) TB hTB
      (SemFund.choose Jm) hmEq)

lemma tupByEquiv {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (Jm : SemFund Γ m A) (Jn : SemFund Γ n B.[m/])
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData TA)
    (hnEq : SemTypeData.Equiv (SemFund.choose Jn).typeData
      (SemTypeData.subst1 TA TB
        (SemTypeData.Equiv.semTm hmEq (SemFund.choose Jm).semTm))) :
    SemFund Γ (.tup m n) (.sig A B) :=
  SemFund.ofTermData
    (SemTermData.tupByEquiv TA TB (SemFund.choose Jm)
      (SemFund.choose Jn) hmEq hnEq)

lemma prjBranchByEquiv {Γ : Ctx} {A B C m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (hTC : TC.Expansive)
    (Jm : SemFund Γ m (.sig A B))
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.ksig TA TB))
    (hn : ∀ {Δ : DCandCtx} (hΓ : SemCtx Γ Δ),
      let IA := TA.interp hΓ
      let hΓA : SemCtx (A :: Γ) (DCandCtx.extend IA) :=
        SemCtx.cons hΓ IA (TA.weakens hΓ)
      let IB := TB.interp hΓA
      let K := TypeInterp.ksig IA IB (SemCtx.weakens hΓ)
      let hΓS : SemCtx (.sig A B :: Γ) (DCandCtx.extend K) :=
        SemCtx.cons hΓ K (TypeInterp.ksig_weakens IA IB (SemCtx.weakens hΓ))
      (TypeInterp.sigmaBranch IA IB (SemCtx.weakens hΓ) (TA.weakens hΓ)
        (TB.weakens hΓA) (TC.interp hΓS)).SemTm n) :
    SemFund Γ (.prj C m n) C.[m/] :=
  SemFund.ofTermData
    (SemTermData.prjBranchByEquiv TA TB TC hTC (SemFund.choose Jm)
      hmEq hn)

lemma prjSNBranchByEquiv {Γ : Ctx} {A B C m n : Tm} {iC : Nat}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (Jm : SemFund Γ m (.sig A B))
    (Jn : SemFund (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2])
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.ksig TA TB)) :
    SemFund Γ (.prj C m n) C.[m/] :=
  SemFund.ofTermData
    (SemTermData.prjSNBranch (iC := iC) TA TB TC
      (SemTypeData.Equiv.semTm hmEq (SemFund.choose Jm).semTm) Jn)

lemma prjSNBranchRetagByEquiv {Γ : Ctx} {P A B C m n : Tm}
    {iP iC : Nat}
    (TP : SemTypeFund Γ (.sig A B) iP)
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (TC : SemTypeData (.sig A B :: Γ) C)
    (Jm : SemFund Γ m P)
    (Jn : SemFund (B :: A :: Γ) n
      C.[.tup (.var 1) (.var 0) .: shift 2])
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.ksig TA TB)) :
    SemFund Γ (.prj C m n) C.[m/] :=
  SemFund.ofTermData
    (SemTermData.prjSNBranchRetagByEquiv (iC := iC) TP TA TB TC
      (SemFund.choose Jm) Jn hmEq)

lemma iteByEquiv {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : SemTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : SemFund Γ m .bool)
    (Jn1 : SemFund Γ n1 A.[.tt/])
    (Jn2 : SemFund Γ n2 A.[.ff/])
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.bool Γ))
    (hn1Eq : SemTypeData.Equiv (SemFund.choose Jn1).typeData
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.tt))
    (hn2Eq : SemTypeData.Equiv (SemFund.choose Jn2).typeData
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.ff)) :
      SemFund Γ (.ite A m n1 n2) A.[m/] :=
    SemFund.ofTermData
      (SemTermData.iteByEquiv TB hTB (SemFund.choose Jm)
        (SemFund.choose Jn1) (SemFund.choose Jn2) hmEq hn1Eq hn2Eq)

  lemma iteSNByEquiv {Γ : Ctx} {A m n1 n2 : Tm} {i : Nat}
      (TB : SemTypeData (.bool :: Γ) A)
      (Jm : SemFund Γ m .bool)
      (Jn1 : SemFund Γ n1 A.[.tt/])
      (Jn2 : SemFund Γ n2 A.[.ff/])
      (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
        (SemTypeData.bool Γ)) :
      SemFund Γ (.ite A m n1 n2) A.[m/] :=
  SemFund.ofTermData
    (SemTermData.iteSN (i := i) TB (SemFund.choose Jm) Jn1 Jn2 hmEq)

lemma iteSNRetagByEquiv {Γ : Ctx} {P A m n1 n2 : Tm}
    {iP i : Nat}
    (TP : SemTypeFund Γ .bool iP)
    (TB : SemTypeData (.bool :: Γ) A)
    (Jm : SemFund Γ m P)
    (Jn1 : SemFund Γ n1 A.[.tt/])
    (Jn2 : SemFund Γ n2 A.[.ff/])
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.bool Γ)) :
    SemFund Γ (.ite A m n1 n2) A.[m/] :=
  SemFund.ofTermData
    (SemTermData.iteSNRetagByEquiv (i := i) TP TB (SemFund.choose Jm)
      Jn1 Jn2 hmEq)

lemma exfByEquiv {Γ : Ctx} {A m : Tm}
    (TB : SemTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : SemFund Γ m .bot)
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.bot Γ)) :
      SemFund Γ (.exf A m) A.[m/] :=
    SemFund.ofTermData
      (SemTermData.exfByEquiv TB hTB (SemFund.choose Jm) hmEq)

  lemma exfSNByEquiv {Γ : Ctx} {A m : Tm} {i : Nat}
      (TB : SemTypeData (.bot :: Γ) A)
      (Jm : SemFund Γ m .bot)
      (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
        (SemTypeData.bot Γ)) :
      SemFund Γ (.exf A m) A.[m/] :=
  SemFund.ofTermData
    (SemTermData.exfSN (i := i) TB (SemFund.choose Jm) hmEq)

lemma exfSNRetagByEquiv {Γ : Ctx} {P A m : Tm}
    {iP i : Nat}
    (TP : SemTypeFund Γ .bot iP)
    (TB : SemTypeData (.bot :: Γ) A)
    (Jm : SemFund Γ m P)
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeData.bot Γ)) :
    SemFund Γ (.exf A m) A.[m/] :=
  SemFund.ofTermData
    (SemTermData.exfSNRetagByEquiv (i := i) TP TB (SemFund.choose Jm) hmEq)

lemma convWeak {Γ : Ctx} {A B m : Tm} {i : Nat} :
    A === B ->
    SemFund Γ m A ->
    SemTypeFund Γ B i ->
    SemFund Γ m B := by
  intro _eq J TB
  exact SemFund.ofTermData ((SemFund.choose J).retag (Classical.choice TB).typeData)

lemma convByEquiv {Γ : Ctx} {A B m : Tm} {i : Nat} :
    A === B ->
    (J : SemFund Γ m A) ->
    (TB : SemTypeFund Γ B i) ->
    SemTypeData.Equiv (SemFund.choose J).typeData
      (Classical.choice TB).typeData ->
    SemFund Γ m B := by
  intro _eq J TB hEq
  exact SemFund.ofTermData
    ((SemFund.choose J).retagEquiv (Classical.choice TB).typeData hEq)

lemma toTypeFundWeak {Γ : Ctx} {A : Tm} {i : Nat} :
    SemFund Γ A (.ty i) -> SemTypeFund Γ A i := by
  intro J
  exact ⟨SemTypeJudgment.ofTermDataWeak (SemFund.choose J)⟩

end SemFund

namespace SemTypeFund

noncomputable def choose {Γ : Ctx} {A : Tm} {i : Nat}
    (J : SemTypeFund Γ A i) : SemTypeJudgment Γ A i :=
  Classical.choice J

lemma ofTypeJudgment {Γ : Ctx} {A : Tm} {i : Nat}
    (J : SemTypeJudgment Γ A i) : SemTypeFund Γ A i :=
  ⟨J⟩

lemma toSemFund {Γ : Ctx} {A : Tm} {i : Nat} :
    SemTypeFund Γ A i -> SemFund Γ A (.ty i) := by
  intro J
  exact SemFund.ofTermData (SemTypeFund.choose J).toTermData

lemma ty (Γ : Ctx) (i : Nat) :
    SemTypeFund Γ (.ty i) (i + 1) :=
  SemTypeFund.ofTypeJudgment (SemTypeJudgment.ty Γ i)

lemma bool (Γ : Ctx) :
    SemTypeFund Γ .bool 0 :=
  SemTypeFund.ofTypeJudgment (SemTypeJudgment.bool Γ)

lemma bot (Γ : Ctx) :
    SemTypeFund Γ .bot 0 :=
  SemTypeFund.ofTypeJudgment (SemTypeJudgment.bot Γ)

lemma pi {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeFund Γ A iA)
    (TB : SemTypeFund (A :: Γ) B iB)
    (hTB : (SemTypeFund.choose TB).typeData.Expansive) :
    SemTypeFund Γ (.pi A B) (max iA iB) :=
  SemTypeFund.ofTypeJudgment
    (SemTypeJudgment.pi (SemTypeFund.choose TA) (SemTypeFund.choose TB) hTB)

lemma sig {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeFund Γ A iA)
    (TB : SemTypeFund (A :: Γ) B iB) :
    SemTypeFund Γ (.sig A B) (max iA iB) :=
  SemTypeFund.ofTypeJudgment
    (SemTypeJudgment.sig (SemTypeFund.choose TA) (SemTypeFund.choose TB))

lemma idnByEquiv {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : SemTypeFund Γ A i)
    (Jm : SemFund Γ m A) (Jn : SemFund Γ n A)
    (hmEq : SemTypeData.Equiv (SemFund.choose Jm).typeData
      (SemTypeFund.choose TA).typeData)
    (hnEq : SemTypeData.Equiv (SemFund.choose Jn).typeData
      (SemTypeFund.choose TA).typeData) :
    SemTypeFund Γ (.idn A m n) i :=
  SemTypeFund.ofTypeJudgment
    (SemTypeJudgment.idnByEquiv (SemTypeFund.choose TA)
      (SemFund.choose Jm) (SemFund.choose Jn) hmEq hnEq)

lemma convWeak {Γ : Ctx} {A B : Tm} {i j : Nat} :
    A === B ->
    SemTypeFund Γ A i ->
    SemFund Γ B (.ty j) ->
    SemTypeFund Γ B j := by
  intro _eq _JA JB
  exact SemFund.toTypeFundWeak JB

end SemTypeFund

namespace SemFundAt

lemma srt {Γ : Ctx} (i : Nat) :
    SemFundAt Γ (.ty i) (.ty (i + 1)) (SemTypeData.univ Γ (i + 1)) :=
  SemFundAt.ofTermData (SemTermData.srt i)
    (SemTypeData.Equiv.refl (SemTypeData.univ Γ (i + 1)))

lemma var {Γ : Ctx} {x : Var} {A : Tm}
    (hs : Has Γ x A) :
    SemFundAt Γ (.var x) A (SemTypeData.lookup hs) :=
  SemFundAt.ofTermData (SemTermData.var hs)
    (SemTypeData.Equiv.refl (SemTypeData.lookup hs))

lemma bool {Γ : Ctx} :
    SemFundAt Γ .bool (.ty 0) (SemTypeData.univ Γ 0) :=
  SemFundAt.ofTermData SemTermData.bool
    (SemTypeData.Equiv.refl (SemTypeData.univ Γ 0))

lemma bot {Γ : Ctx} :
    SemFundAt Γ .bot (.ty 0) (SemTypeData.univ Γ 0) :=
  SemFundAt.ofTermData SemTermData.bot
    (SemTypeData.Equiv.refl (SemTypeData.univ Γ 0))

lemma piType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeJudgment (A :: Γ) B iB)
    (hTB : TB.typeData.Expansive) :
    SemFundAt Γ (.pi A B) (.ty (max iA iB))
      (SemTypeData.univ Γ (max iA iB)) :=
  SemFundAt.ofTermData (SemTermData.piType TA TB hTB)
    (SemTypeData.Equiv.refl (SemTypeData.univ Γ (max iA iB)))

lemma sigType {Γ : Ctx} {A B : Tm} {iA iB : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeJudgment (A :: Γ) B iB) :
    SemFundAt Γ (.sig A B) (.ty (max iA iB))
      (SemTypeData.univ Γ (max iA iB)) :=
  SemFundAt.ofTermData (SemTermData.sigType TA TB)
    (SemTypeData.Equiv.refl (SemTypeData.univ Γ (max iA iB)))

lemma idnType {Γ : Ctx} {A m n : Tm} {i : Nat}
    (TA : SemTypeJudgment Γ A i)
    (Jm : SemFundAt Γ m A TA.typeData)
    (Jn : SemFundAt Γ n A TA.typeData) :
    SemFundAt Γ (.idn A m n) (.ty i) (SemTypeData.univ Γ i) := by
  exact SemFundAt.ofTermData
    (SemTermData.idnType TA (SemFundAt.semTm Jm) (SemFundAt.semTm Jn))
    (SemTypeData.Equiv.refl (SemTypeData.univ Γ i))

lemma tt {Γ : Ctx} :
    SemFundAt Γ .tt .bool (SemTypeData.bool Γ) :=
  SemFundAt.ofTermData SemTermData.tt
    (SemTypeData.Equiv.refl (SemTypeData.bool Γ))

lemma ff {Γ : Ctx} :
    SemFundAt Γ .ff .bool (SemTypeData.bool Γ) :=
  SemFundAt.ofTermData SemTermData.ff
    (SemTypeData.Equiv.refl (SemTypeData.bool Γ))

lemma rfl {Γ : Ctx} {A m : Tm}
    (TA : SemTypeData Γ A)
    (Jm : SemFundAt Γ m A TA) :
    SemFundAt Γ (.rfl m) (.idn A m m)
      (SemTypeData.idn TA (SemFundAt.semTm Jm) (SemFundAt.semTm Jm)) := by
  let Jm' := SemFundAt.choose Jm
  let hm : TA.SemTm m := SemTypeData.Equiv.semTm Jm'.property Jm'.val.semTm
  change SemFundAt Γ (.rfl m) (.idn A m m) (SemTypeData.idn TA hm hm)
  exact SemFundAt.ofTermData
    (SemTermData.rflByEquiv TA Jm'.val Jm'.property)
    (SemTypeData.Equiv.refl (SemTypeData.idn TA hm hm))

lemma lam {Γ : Ctx} {A B m : Tm} {iA : Nat}
    (TA : SemTypeJudgment Γ A iA)
    (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemFundAt (A :: Γ) m B TB) :
    SemFundAt Γ (.lam A m) (.pi A B) (SemTypeData.kpi TA.typeData TB hTB) := by
  let Jm' := SemFundAt.choose Jm
  exact SemFundAt.ofTermData
    (SemTermData.lamByEquiv TA TB hTB Jm'.val Jm'.property)
    (SemTypeData.Equiv.refl (SemTypeData.kpi TA.typeData TB hTB))

lemma app {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemFundAt Γ m (.pi A B) (SemTypeData.kpi TA TB hTB))
    (Jn : SemFundAt Γ n A TA) :
    SemFundAt Γ (.app m n) B.[n/]
      (SemTypeData.subst1 TA TB (SemFundAt.semTm Jn)) := by
  let Jm' := SemFundAt.choose Jm
  let Jn' := SemFundAt.choose Jn
  let hn : TA.SemTm n := SemTypeData.Equiv.semTm Jn'.property Jn'.val.semTm
  change SemFundAt Γ (.app m n) B.[n/] (SemTypeData.subst1 TA TB hn)
  exact SemFundAt.ofTermData
    (SemTermData.appByEquiv TA TB hTB Jm'.val Jn'.val Jm'.property Jn'.property)
    (SemTypeData.Equiv.refl (SemTypeData.subst1 TA TB hn))

lemma appRetagTarget {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (hTB : TB.Expansive)
    (Jm : SemFundAt Γ m (.pi A B) (SemTypeData.kpi TA TB hTB))
    (Jn : SemFundAt Γ n A TA)
    (TC : SemTypeData Γ B.[n/])
    (hTarget : SemTypeData.Equiv
      (SemTypeData.subst1 TA TB (SemFundAt.semTm Jn)) TC) :
    SemFundAt Γ (.app m n) B.[n/] TC :=
  SemFundAt.retag (SemFundAt.app TA TB hTB Jm Jn) hTarget

lemma tup {Γ : Ctx} {A B m n : Tm}
    (TA : SemTypeData Γ A) (TB : SemTypeData (A :: Γ) B)
    (Jm : SemFundAt Γ m A TA)
    (Jn : SemFundAt Γ n B.[m/]
      (SemTypeData.subst1 TA TB (SemFundAt.semTm Jm))) :
    SemFundAt Γ (.tup m n) (.sig A B) (SemTypeData.ksig TA TB) := by
  let Jm' := SemFundAt.choose Jm
  let Jn' := SemFundAt.choose Jn
  let hm : TA.SemTm m := SemTypeData.Equiv.semTm Jm'.property Jm'.val.semTm
  change SemFundAt Γ (.tup m n) (.sig A B) (SemTypeData.ksig TA TB)
  exact SemFundAt.ofTermData
    (SemTermData.tupByEquiv TA TB Jm'.val Jn'.val Jm'.property Jn'.property)
    (SemTypeData.Equiv.refl (SemTypeData.ksig TA TB))

lemma ite {Γ : Ctx} {A m n1 n2 : Tm}
    (TB : SemTypeData (.bool :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : SemFundAt Γ m .bool (SemTypeData.bool Γ))
    (Jn1 : SemFundAt Γ n1 A.[.tt/]
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.tt))
    (Jn2 : SemFundAt Γ n2 A.[.ff/]
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB SemTypeData.ff)) :
    SemFundAt Γ (.ite A m n1 n2) A.[m/]
      (SemTypeData.subst1 (SemTypeData.bool Γ) TB (SemFundAt.semTm Jm)) := by
  let Jm' := SemFundAt.choose Jm
  let Jn1' := SemFundAt.choose Jn1
  let Jn2' := SemFundAt.choose Jn2
  let hm : (SemTypeData.bool Γ).SemTm m :=
    SemTypeData.Equiv.semTm Jm'.property Jm'.val.semTm
  change SemFundAt Γ (.ite A m n1 n2) A.[m/]
    (SemTypeData.subst1 (SemTypeData.bool Γ) TB hm)
  exact SemFundAt.ofTermData
    (SemTermData.iteByEquiv TB hTB Jm'.val Jn1'.val Jn2'.val
      Jm'.property Jn1'.property Jn2'.property)
    (SemTypeData.Equiv.refl (SemTypeData.subst1 (SemTypeData.bool Γ) TB hm))

lemma exf {Γ : Ctx} {A m : Tm}
    (TB : SemTypeData (.bot :: Γ) A)
    (hTB : TB.Expansive)
    (Jm : SemFundAt Γ m .bot (SemTypeData.bot Γ)) :
    SemFundAt Γ (.exf A m) A.[m/]
      (SemTypeData.subst1 (SemTypeData.bot Γ) TB (SemFundAt.semTm Jm)) := by
  let Jm' := SemFundAt.choose Jm
  let hm : (SemTypeData.bot Γ).SemTm m :=
    SemTypeData.Equiv.semTm Jm'.property Jm'.val.semTm
  change SemFundAt Γ (.exf A m) A.[m/]
    (SemTypeData.subst1 (SemTypeData.bot Γ) TB hm)
  exact SemFundAt.ofTermData
    (SemTermData.exfByEquiv TB hTB Jm'.val Jm'.property)
    (SemTypeData.Equiv.refl (SemTypeData.subst1 (SemTypeData.bot Γ) TB hm))

end SemFundAt

namespace Wf

lemma semCtx_of_semantic
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> SemTyped Γ m A) :
    ∀ {Γ : Ctx}, Γ ⊢ -> ∃ Δ : DCandCtx, SemCtx Γ Δ
  | [], Wf.nil => ⟨DCandCtx.empty, SemCtx.nil⟩
  | A :: Γ, Wf.cons tyA wf =>
    by
      rcases semCtx_of_semantic fund wf with ⟨Δ, hΓ⟩
      rcases SemTyped.semType_of_typed (fund tyA) hΓ with ⟨I, hI⟩
      exact ⟨DCandCtx.extend I, SemCtx.cons hΓ I hI⟩

end Wf

theorem Typed.normalize_of_semantic
    {Γ : Ctx} {m A : Tm}
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> SemTyped Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  rcases ty.toWf.semCtx_of_semantic fund with ⟨Δ, hΓ⟩
  exact SemTyped.sn hΓ (fund ty)

theorem Typed.normalize_of_sem_fund_at
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> SemTypeJudgment Γ A i)
    (fund : ∀ {Γ m A i} (_ty : Γ ⊢ m : A),
      (TA : SemTypeJudgment Γ A i) -> SemFundAt Γ m A TA.typeData) :
    Γ ⊢ m : A -> SN Step m := by
  apply Typed.normalize_of_semantic
  intro Γ m A ty
  rcases ty.validity with ⟨i, tyA⟩
  exact SemFund.toSemTyped
    (SemFundAt.toSemFund (fund ty (typeFund tyA)))

theorem Typed.normalize_of_sem_fund_at_validity
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> SemTypeJudgment Γ A i)
    (fund : ∀ {Γ m A i} (_ty : Γ ⊢ m : A) (tyA : Γ ⊢ A : .ty i),
      SemFundAt Γ m A (typeFund tyA).typeData) :
    Γ ⊢ m : A -> SN Step m := by
  apply Typed.normalize_of_semantic
  intro Γ m A ty
  rcases ty.validity with ⟨i, tyA⟩
  exact SemFund.toSemTyped
    (SemFundAt.toSemFund (fund ty tyA))

theorem Typed.normalize_of_can_semantic
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> SemTypeData Γ A)
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> CanSemTyped Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  rcases ty.toWf.canSemCtx_of_type_data typeFund with ⟨Δ, hΓ⟩
  exact CanSemTyped.sn hΓ (fund ty)

theorem Typed.normalize_of_can_term_data
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeJudgment Γ A i)
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> CanTermData Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  rcases ty.toWf.canSemCtx_of_can_type_data
      (fun ty => (typeFund ty).typeData) with ⟨Δ, hΓ⟩
  exact CanSemTyped.sn hΓ (fund ty).toCanSemTyped

theorem Typed.normalize_of_can_term_data_nonempty
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeFund Γ A i)
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> CanFund Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  classical
  exact Typed.normalize_of_can_term_data
    (fun ty => CanTypeFund.choose (typeFund ty))
    (fun ty => CanFund.choose (fund ty))

theorem Typed.normalize_of_can_fund_at
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeJudgment Γ A i)
    (fund : ∀ {Γ m A i} (_ty : Γ ⊢ m : A),
      (TA : CanTypeJudgment Γ A i) -> CanFundAt Γ m A TA.typeData) :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  rcases ty.toWf.canSemCtx_of_can_type_data
      (fun tyA => (typeFund tyA).typeData) with ⟨⟨Δ, hΓ⟩⟩
  rcases ty.validity with ⟨i, tyA⟩
  exact CanSemTyped.sn hΓ
    (CanFund.toCanSemTyped
      (CanFundAt.toCanFund (fund ty (typeFund tyA))))

theorem Typed.normalize_of_can_fund_at_validity
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeJudgment Γ A i)
    (fund : ∀ {Γ m A i} (_ty : Γ ⊢ m : A) (tyA : Γ ⊢ A : .ty i),
      CanFundAt Γ m A (typeFund tyA).typeData) :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  rcases ty.toWf.canSemCtx_of_can_type_data
      (fun tyA => (typeFund tyA).typeData) with ⟨⟨Δ, hΓ⟩⟩
  rcases ty.validity with ⟨i, tyA⟩
  exact CanSemTyped.sn hΓ
    (CanFund.toCanSemTyped
      (CanFundAt.toCanFund (fund ty tyA)))

theorem Typed.normalize_of_can_exp_term_data_nonempty
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeFundExp Γ A i)
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> CanFund Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  exact Typed.normalize_of_can_term_data_nonempty
    (fun ty => CanTypeFundExp.toCanTypeFund (typeFund ty))
    fund

theorem Typed.normalize_of_can_fund
    {Γ : Ctx} {m A : Tm}
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> CanFund Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  exact Typed.normalize_of_can_exp_term_data_nonempty
    (fun ty => CanTypeFundExp.ofCanFund (fund ty))
    fund

theorem Typed.normalize_of_fund_term_data
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeData Γ A)
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> FundTermData Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  intro ty
  rcases ty.toWf.fundSemCtx_of_can_type_data typeFund with ⟨Δ, hΓ⟩
  exact FundTermData.sn (fund ty) hΓ

theorem Typed.normalize_of_fund_term_data_nonempty
    {Γ : Ctx} {m A : Tm}
    (typeFund : ∀ {Γ A i}, Γ ⊢ A : .ty i -> CanTypeFund Γ A i)
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> FundFund Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  classical
  exact Typed.normalize_of_fund_term_data
    (fun ty => (CanTypeFund.choose (typeFund ty)).typeData)
    (fun ty => FundFund.choose (fund ty))

theorem Typed.normalize_of_term_data
    {Γ : Ctx} {m A : Tm}
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> SemTermData Γ m A) :
    Γ ⊢ m : A -> SN Step m :=
  Typed.normalize_of_semantic (fun ty => (fund ty).toSemTyped)

theorem Typed.normalize_of_term_data_nonempty
    {Γ : Ctx} {m A : Tm}
    (fund : ∀ {Γ m A}, Γ ⊢ m : A -> SemFund Γ m A) :
    Γ ⊢ m : A -> SN Step m := by
  classical
  exact Typed.normalize_of_term_data (fun ty => Classical.choice (fund ty))

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
