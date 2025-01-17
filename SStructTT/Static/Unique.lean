import SStructTT.Static.Inversion
open ARS

namespace Static
variable {Srt : Type}

@[aesop safe (rule_sets := [unique]) [constructors]]
inductive HeadSim : Tm Srt -> Tm Srt -> Prop where
  | var {x} : HeadSim (.var x) (.var x)
  | srt {s i1 i2} : HeadSim (.srt s i1) (.srt s i2)
  | pi0 {A1 A2 B1 B2} s :
    HeadSim A1 A2 ->
    HeadSim B1 B2 ->
    HeadSim (.pi0 A1 B1 s) (.pi0 A2 B2 s)
  | pi1 {A1 A2 B1 B2} s :
    HeadSim A1 A2 ->
    HeadSim B1 B2 ->
    HeadSim (.pi1 A1 B1 s) (.pi1 A2 B2 s)
  | lam0 {A m s} : HeadSim (.lam0 A m s) (.lam0 A m s)
  | lam1 {A m s} : HeadSim (.lam1 A m s) (.lam1 A m s)
  | app {m n} : HeadSim (.app m n) (.app m n)
  | sig0 {A1 A2 B1 B2 s} :
    HeadSim (.sig0 A1 B1 s) (.sig0 A2 B2 s)
  | sig1 {A1 A2 B1 B2 s} :
    HeadSim (.sig1 A1 B1 s) (.sig1 A2 B2 s)
  | tup0 {m n s} : HeadSim (.tup0 m n s) (.tup0 m n s)
  | tup1 {m n s} : HeadSim (.tup1 m n s) (.tup1 m n s)
  | proj {A m n} : HeadSim (.proj A m n) (.proj A m n)
  | bool : HeadSim .bool .bool
  | tt : HeadSim .tt .tt
  | ff : HeadSim .ff .ff
  | ite {A m n1 n2} : HeadSim (.ite A m n1 n2) (.ite A m n1 n2)
  | idn {A1 A2} m n :
    HeadSim A1 A2 ->
    HeadSim (.idn A1 m n) (.idn A2 m n)
  | rfl {m} : HeadSim (.rfl m) (.rfl m)
  | rw {A m n} : HeadSim (.rw A m n) (.rw A m n)

@[aesop safe (rule_sets := [unique]) [constructors]]
inductive Sim (m n : Tm Srt) : Prop where
  | intro {x y} : m === x -> HeadSim x y -> y === n -> Sim m n

lemma HeadSim.toSim {m n : Tm Srt} : HeadSim m n -> Sim m n := by
  intro; constructor <;> aesop

@[aesop safe (rule_sets := [unique])]
lemma HeadSim.refl {m : Tm Srt} : HeadSim m m := by
  induction m
  all_goals aesop (rule_sets := [unique])

lemma HeadSim.sym {m n : Tm Srt} : HeadSim m n -> HeadSim n m := by
  intro h; induction h
  all_goals aesop (rule_sets := [unique])

lemma HeadSim.subst {m n : Tm Srt} σ : HeadSim m n -> HeadSim m.[σ] n.[σ] := by
  intro h; induction h generalizing σ
  all_goals try (asimp; aesop (rule_sets := [unique]))

lemma Sim.refl {m : Tm Srt} : Sim m m := by
  aesop (rule_sets := [unique])

lemma Sim.sym {m n : Tm Srt} : Sim m n -> Sim n m := by
  intro sm; cases sm
  constructor
  . apply Conv.sym; assumption
  . apply HeadSim.sym; assumption
  . apply Conv.sym; assumption

lemma Sim.trans_left {x y z : Tm Srt} : Sim x y -> y === z -> Sim x z := by
  intro sm eq; cases sm
  constructor
  . assumption
  . assumption
  . apply Conv.trans <;> assumption

lemma Sim.trans_right {x y z : Tm Srt} : Sim x y -> z === x -> Sim z y := by
  intro sm eq; cases sm
  constructor
  . apply Conv.trans <;> assumption
  . assumption
  . assumption

lemma Sim.subst {x y : Tm Srt} σ : Sim x y -> Sim x.[σ] y.[σ] := by
  intro sm; cases sm
  constructor
  . apply Conv.subst; assumption
  . apply HeadSim.subst; assumption
  . apply Conv.subst; assumption

lemma Sim.srt_inj {s1 s2 : Srt} {i1 i2} :
    Sim (.srt s1 i1) (.srt s2 i2) -> s1 = s2 := by
  intro sm; have ⟨_, h, _⟩ := sm
  cases h; all_goals try false_conv
  case srt eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj eq1
    have ⟨_, _⟩ := Conv.srt_inj eq2
    subst_vars; rfl
  case app eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
  case proj eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
  case ite eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption
  case rw eq1 eq2 =>
    have ⟨_, _⟩ := Conv.srt_inj (Conv.trans eq1 eq2)
    assumption

lemma Sim.pi0_inj {A1 A2 B1 B2 : Tm Srt} {s1 s2} :
    Sim (.pi0 A1 B1 s1) (.pi0 A2 B2 s2) ->
    Sim A1 A2 ∧ Sim B1 B2 ∧ s1 = s2 := by
  intro sm; have ⟨_, h, _⟩ := sm
  cases h; all_goals try false_conv
  case pi0 eq1 eq2 =>
    have ⟨_, eqA1, eqB1⟩ := Conv.pi0_inj eq1
    have ⟨_, eqA2, eqB2⟩ := Conv.pi0_inj eq2
    subst_vars; simp; and_intros
    . constructor <;> assumption
    . constructor <;> assumption
  case app eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi0_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case proj eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi0_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case ite eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi0_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case rw eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi0_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])

lemma Sim.pi1_inj {A1 A2 B1 B2 : Tm Srt} {s1 s2} :
    Sim (.pi1 A1 B1 s1) (.pi1 A2 B2 s2) ->
    Sim A1 A2 ∧ Sim B1 B2 ∧ s1 = s2 := by
  intro sm; have ⟨_, h, _⟩ := sm
  cases h; all_goals try false_conv
  case pi1 eq1 eq2 =>
    have ⟨_, eqA1, eqB1⟩ := Conv.pi1_inj eq1
    have ⟨_, eqA2, eqB2⟩ := Conv.pi1_inj eq2
    subst_vars; simp; and_intros
    . constructor <;> assumption
    . constructor <;> assumption
  case app eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi1_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case proj eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi1_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case ite eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi1_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case rw eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.pi1_inj (Conv.trans eq1 eq2)
    subst_vars; simp; and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])

lemma Sim.idn_inj {A1 A2 m1 m2 n1 n2 : Tm Srt} :
    Sim (.idn A1 m1 n1) (.idn A2 m2 n2) ->
    Sim A1 A2 ∧ m1 === m2 ∧ n1 === n2 := by
  intro sm; have ⟨_, h, _⟩ := sm
  cases h; all_goals try false_conv
  case app eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.idn_inj (Conv.trans eq1 eq2)
    and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case proj eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.idn_inj (Conv.trans eq1 eq2)
    and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case ite eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.idn_inj (Conv.trans eq1 eq2)
    and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
  case idn eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.idn_inj eq1
    have ⟨_, _, _⟩ := Conv.idn_inj eq2
    and_intros
    . aesop (rule_sets := [unique])
    . apply Conv.trans <;> assumption
    . apply Conv.trans <;> assumption
  case rw eq1 eq2 =>
    have ⟨_, _, _⟩ := Conv.idn_inj (Conv.trans eq1 eq2)
    and_intros
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])
    . aesop (rule_sets := [unique])

lemma Has.inj {Γ : Ctx Srt} {x A B} :
    Has Γ x A -> Has Γ x B -> A = B := by
  intro hs; induction hs generalizing B
  case zero =>
    intro hs; cases hs; rfl
  case succ ih =>
    intro
    | succ _ _ _ _ hs => rw[ih hs]

variable [inst : SStruct Srt]

lemma Typed.srt_unique {Γ : Ctx Srt} {s i1 i2 A} :
    Γ ⊢ .srt s i1 : A -> Sim (.srt s0 i2) A := by
  generalize e: Tm.srt s i1 = m
  intro ty; induction ty generalizing s i1
  all_goals try trivial
  case srt => cases e; apply HeadSim.toSim; constructor
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.var_unqiue {Γ : Ctx Srt} {A B x} :
    Γ ⊢ .var x : B -> Has Γ x A -> Sim A B := by
  generalize e: Tm.var x = m
  intro ty; induction ty generalizing x
  all_goals try trivial
  case var h1 _ =>
    cases e; intro h2; rw[Has.inj h1 h2]; apply Sim.refl
  case conv ihm _ =>
    subst_vars; intro hs
    have := ihm (Eq.refl _) hs
    apply Sim.trans_left <;> assumption

lemma Typed.pi0_unique {Γ : Ctx Srt} {A B C s i} :
    Γ ⊢ .pi0 A B s : C -> Sim (.srt s i) C := by
  generalize e: Tm.pi0 A B s = m
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case pi0 => cases e; apply HeadSim.toSim; constructor
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.pi1_unique {Γ : Ctx Srt} {A B C s i} :
    Γ ⊢ .pi1 A B s : C -> Sim (.srt s i) C := by
  generalize e: Tm.pi1 A B s = m
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case pi1 => cases e; apply HeadSim.toSim; constructor
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.lam0_unique {Γ : Ctx Srt} {A B C m s} :
    Γ ⊢ .lam0 A m s : C ->
    (∀ {C}, A :: Γ ⊢ m : C -> Sim B C) -> Sim (.pi0 A B s) C := by
  generalize e: Tm.lam0 A m s = n
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam0 tyA tym ihA ihm =>
    cases e; intro h
    have ⟨eq1, h, eq2⟩ :=h tym
    constructor
    . apply Conv.pi0 _ Conv.R eq1
    . apply HeadSim.pi0 _ HeadSim.refl h
    . apply Conv.pi0 _ Conv.R eq2
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.lam1_unique {Γ : Ctx Srt} {A B C m s} :
    Γ ⊢ .lam1 A m s : C ->
    (∀ {C}, A :: Γ ⊢ m : C -> Sim B C) -> Sim (.pi1 A B s) C := by
  generalize e: Tm.lam1 A m s = n
  intro ty; induction ty generalizing A m s
  all_goals try trivial
  case lam1 tyA tym ihA ihm =>
    cases e; intro h
    have ⟨eq1, h, eq2⟩ :=h tym
    constructor
    . apply Conv.pi1 _ Conv.R eq1
    . apply HeadSim.pi1 _ HeadSim.refl h
    . apply Conv.pi1 _ Conv.R eq2
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.app0_unique {Γ : Ctx Srt} {A B C m n s} :
    Γ ⊢ .app m n : C ->
    (∀ {C}, Γ ⊢ m : C -> Sim (.pi0 A B s) C) -> Sim B.[n/] C := by
  generalize e: Tm.app m n = x
  intro ty; induction ty generalizing m n
  all_goals try trivial
  case app0 tym _ _ _ =>
    cases e; intro h
    have ⟨_, _, _⟩ := (h tym).pi0_inj
    apply Sim.subst; assumption
  case app1 tym _ _ _ =>
    cases e; intro h
    have ⟨_, h, _⟩ := (h tym)
    cases h; all_goals try false_conv
    case proj eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
    case app  eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
    case ite  eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
    case rw   eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.app1_unique {Γ : Ctx Srt} {A B C m n s} :
    Γ ⊢ .app m n : C ->
    (∀ {C}, Γ ⊢ m : C -> Sim (.pi1 A B s) C) -> Sim B.[n/] C := by
  generalize e: Tm.app m n = x
  intro ty; induction ty generalizing m n
  all_goals try trivial
  case app0 tym _ _ _ =>
    cases e; intro h
    have ⟨_, h, _⟩ := (h tym)
    cases h; all_goals try false_conv
    case proj eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
    case app  eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
    case ite  eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
    case rw   eq1 eq2 => have := Conv.trans eq1 eq2; false_conv
  case app1 tym _ _ _ =>
    cases e; intro h
    have ⟨_, _, _⟩ := (h tym).pi1_inj
    apply Sim.subst; assumption
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.sig0_unique {Γ : Ctx Srt} {A B C s i} :
    Γ ⊢ .sig0 A B s : C -> Sim (.srt s i) C := by
  generalize e: Tm.sig0 A B s = m
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case sig0 => cases e; apply HeadSim.toSim; constructor
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.sig1_unique {Γ : Ctx Srt} {A B C s i} :
    Γ ⊢ .sig1 A B s : C -> Sim (.srt s i) C := by
  generalize e: Tm.sig1 A B s = m
  intro ty; induction ty generalizing A B s
  all_goals try trivial
  case sig1 => cases e; apply HeadSim.toSim; constructor
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.tup0_unique {Γ : Ctx Srt} {A B C m n s} :
    Γ ⊢ .tup0 m n s : C ->
    (∀ {X Y}, Γ ⊢ m : X -> Γ ⊢ n : Y -> Sim A X ∧ Sim B.[m/] Y) ->
    Sim (.sig0 A B s) C := by
  generalize e: Tm.tup0 m n s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup0 tym tyn ihm ihn =>
    aesop (rule_sets := [unique])
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.tup1_unique {Γ : Ctx Srt} {A B C m n s} :
    Γ ⊢ .tup1 m n s : C ->
    (∀ {X Y}, Γ ⊢ m : X -> Γ ⊢ n : Y -> Sim A X ∧ Sim B.[m/] Y) ->
    Sim (.sig1 A B s) C := by
  generalize e: Tm.tup1 m n s = x
  intro ty; induction ty generalizing m n s
  all_goals try trivial
  case tup1 tym tyn ihm ihn =>
    aesop (rule_sets := [unique])
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

@[aesop safe (rule_sets := [unique])]
lemma Typed.proj_unique {Γ : Ctx Srt} {A B m n} :
    Γ ⊢ .proj A m n : B -> Sim A.[m/] B := by
  generalize e: Tm.proj A m n = x
  intro ty; induction ty generalizing A m n
  all_goals try trivial
  case proj0 ihA ihm ihn => cases e; apply Sim.refl
  case proj1 ihA ihm ihn => cases e; apply Sim.refl
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.bool_unique {Γ : Ctx Srt} {A} :
    Γ ⊢ .bool : A -> Sim (.srt s0 0) A := by
  generalize e: Tm.bool = m
  intro ty; induction ty
  all_goals try trivial
  case bool => apply Sim.refl
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.tt_unique {Γ : Ctx Srt} {A} :
    Γ ⊢ .tt : A -> Sim .bool A := by
  generalize e: Tm.tt = m
  intro ty; induction ty
  all_goals try trivial
  case tt => apply Sim.refl
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.ff_unique {Γ : Ctx Srt} {A} :
    Γ ⊢ .ff : A -> Sim .bool A := by
  generalize e: Tm.ff = m
  intro ty; induction ty
  all_goals try trivial
  case ff => apply Sim.refl
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.ite_unique {Γ : Ctx Srt} {A B m n1 n2} :
    Γ ⊢ .ite A m n1 n2 : B -> Sim A.[m/] B := by
  generalize e: Tm.ite A m n1 n2 = x
  intro ty; induction ty generalizing A m n1 n2
  all_goals try trivial
  case ite => cases e; apply Sim.refl
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.idn_unique {Γ : Ctx Srt} {A B m n i} :
    Γ ⊢ .idn A m n : B -> Sim (.srt s0 i) B := by
  generalize e: Tm.idn A m n = x
  intro ty; induction ty generalizing A m n
  all_goals try trivial
  case idn => cases e; apply HeadSim.toSim; constructor
  case conv ihm _ =>
    subst_vars
    have := ihm (Eq.refl _)
    apply Sim.trans_left <;> assumption

lemma Typed.rfl_unique {Γ : Ctx Srt} {A B m} :
    Γ ⊢ .rfl m : B ->
    (∀ {X}, Γ ⊢ m : X -> Sim A X) -> Sim (.idn A m m) B := by
  generalize e: Tm.rfl m = x
  intro ty; induction ty generalizing m
  all_goals try trivial
  case rfl tym ihm =>
    cases e; intro h
    have ⟨eq1, h, eq2⟩ := h tym
    constructor
    . apply Conv.idn eq1 Conv.R Conv.R
    . apply HeadSim.idn _ _ h
    . apply Conv.idn eq2 Conv.R Conv.R
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.rw_unique {Γ : Ctx Srt} {A B C m n a b} :
    Γ ⊢ .rw A m n : C ->
    (∀ {X}, Γ ⊢ n : X -> Sim (.idn B a b) X) -> Sim A.[n,b/] C := by
  generalize e: Tm.rw A m n = x
  intro ty; induction ty generalizing A m n
  all_goals try trivial
  case rw n _ b' _ _ _ _ tyn _ _ _ =>
    cases e; intro h
    have ⟨sm, eq1, eq2⟩ := (h tyn).idn_inj
    have sc : SConv (n .: b .: ids) (n .: b' .: ids) := by
      intro
      | .zero => asimp; constructor
      | .succ .zero => asimp; assumption
      | .succ (.succ _) => asimp; constructor
    constructor
    apply Conv.compat _ sc
    all_goals aesop (rule_sets := [unique])
  case conv ihm _ =>
    subst_vars; intro h
    have := ihm (Eq.refl _) h
    apply Sim.trans_left <;> assumption

lemma Typed.unique' {Γ : Ctx Srt} {A B m} :
    Γ ⊢ m : A -> Γ ⊢ m : B -> Sim A B := by
  intro ty; induction ty generalizing B
  all_goals try intro ty
  case srt => apply Typed.srt_unique <;> aesop
  case var => apply Typed.var_unqiue <;> aesop
  case pi0 => apply Typed.pi0_unique <;> aesop
  case pi1 => apply Typed.pi1_unique <;> aesop
  case lam0 => apply Typed.lam0_unique <;> aesop
  case lam1 => apply Typed.lam1_unique <;> aesop
  case app0 => apply Typed.app0_unique <;> aesop
  case app1 => apply Typed.app1_unique <;> aesop
  case sig0 => apply Typed.sig0_unique <;> aesop
  case sig1 => apply Typed.sig1_unique <;> aesop
  case tup0 => apply Typed.tup0_unique <;> aesop
  case tup1 => apply Typed.tup1_unique <;> aesop
  case proj0 => apply Typed.proj_unique <;> aesop
  case proj1 => apply Typed.proj_unique <;> aesop
  case bool => apply Typed.bool_unique <;> aesop
  case tt => apply Typed.tt_unique <;> aesop
  case ff => apply Typed.ff_unique <;> aesop
  case ite => apply Typed.ite_unique <;> aesop
  case idn => apply Typed.idn_unique <;> aesop
  case rfl => apply Typed.rfl_unique <;> aesop
  case rw => apply Typed.rw_unique <;> aesop
  case conv ihm _ =>
    apply Sim.trans_right
    apply ihm ty
    apply Conv.sym; assumption
  all_goals trivial

theorem Typed.unique {Γ : Ctx Srt} {m s1 s2 i1 i2} :
    Γ ⊢ m : .srt s1 i1 -> Γ ⊢ m : .srt s2 i2 -> s1 = s2 := by
  intro ty1 ty2
  apply Sim.srt_inj
  apply Typed.unique' ty1 ty2
