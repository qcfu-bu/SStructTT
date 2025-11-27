import SStructTT.MLTT.Step
open ARS

namespace MLTT

@[aesop safe (rule_sets := [pstep]) [constructors]]
inductive PStep : Tm -> Tm -> Prop where
  | var {x} :
    PStep (.var x) (.var x)
  | ty i :
    PStep (.ty i) (.ty i)
  | pi {A A' B B'} :
    PStep A A' ->
    PStep B B' ->
    PStep (.pi A B) (.pi A' B')
  | lam {A A' m m'} :
    PStep A A' ->
    PStep m m' ->
    PStep (.lam A m) (.lam A' m')
  | app {m m' n n'} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app m n) (.app m' n')
  | beta A {m m' n n'} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app (.lam A m) n) m'.[n'/]
  | sig {A A' B B'} :
    PStep A A' ->
    PStep B B' ->
    PStep (.sig A B) (.sig A' B')
  | tup {m m' n n'} :
    PStep m m' ->
    PStep n n' ->
    PStep (.tup m n) (.tup m' n')
  | prj {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.prj A m n) (.prj A' m' n')
  | prj_elim A {m1 m1' m2 m2' n n'} :
    PStep m1 m1' ->
    PStep m2 m2' ->
    PStep n n' ->
    PStep (.prj A (.tup m1 m2) n) n'.[m2',m1'/]
  | bool : PStep .bool .bool
  | tt : PStep .tt .tt
  | ff : PStep .ff .ff
  | ite {A A' m m' n1 n1' n2 n2'} :
    PStep A A' ->
    PStep m m' ->
    PStep n1 n1' ->
    PStep n2 n2' ->
    PStep (.ite A m n1 n2) (.ite A' m' n1' n2')
  | ite_tt A {n1 n1'} n2 :
    PStep n1 n1' ->
    PStep (.ite A .tt n1 n2) n1'
  | ite_ff A n1 {n2 n2'} :
    PStep n2 n2' ->
    PStep (.ite A .ff n1 n2) n2'
  | idn {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.idn A m n) (.idn A' m' n')
  | rfl {m m'} :
    PStep m m' ->
    PStep (.rfl m) (.rfl m')
  | rw {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.rw A m n) (.rw A' m' n')
  | rw_elim A {m m'} n :
    PStep m m' ->
    PStep (.rw A m (.rfl n)) m'

infix:50 " ≈> " => PStep

def SRed (σ τ : Nat -> Tm) := ∀ x, (σ x) ~>* (τ x)

lemma Step.subst {m n : Tm} σ : m ~> n -> m.[σ] ~> n.[σ] := by
  intro st
  induction st generalizing σ
  all_goals try asimp; aesop
  case beta A m n =>
    rw[show m.[n/].[σ] = m.[up σ].[n.[σ]/] by asimp]
    constructor
  case prj_elim A m1 m2 n =>
    rw[show n.[m2,m1/].[σ] = n.[upn 2 σ].[m2.[σ],m1.[σ]/] by asimp]
    constructor

@[aesop safe (rule_sets := [red])]
lemma Red.pi {A A' B B' : Tm} :
    A ~>* A' -> B ~>* B' -> .pi A B ~>* .pi A' B' := by
  intro rA rB
  apply (@Star.trans _ _ (.pi A' B))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rB; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.lam {A A' m m' : Tm} :
    A ~>* A' -> m ~>* m' -> .lam A m ~>* .lam A' m' := by
  intro rA rm
  apply (@Star.trans _ _ (.lam A' m))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rm; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.app {m m' n n' : Tm} :
    m ~>* m' -> n ~>* n' -> .app m n ~>* .app m' n' := by
  intro rm rn
  apply (@Star.trans _ _ (.app m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.sig {A A' B B' : Tm} :
    A ~>* A' -> B ~>* B' -> .sig A B ~>* .sig A' B' := by
  intro rA rB
  apply (@Star.trans _ _ (.sig A' B))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rB; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.tup {m m' n n' : Tm} :
    m ~>* m' -> n ~>* n' -> .tup m n ~>* .tup m' n' := by
  intro rm rn
  apply (@Star.trans _ _ (.tup m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.prj {A A' m m' n n' : Tm} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .prj A m n ~>* .prj A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (.prj A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.prj A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.ite {A A' m m' n1 n1' n2 n2' : Tm} :
    A ~>* A' -> m ~>* m' -> n1 ~>* n1' -> n2 ~>* n2' ->
    .ite A m n1 n2 ~>* .ite A' m' n1' n2' := by
  intro rA rm rn1 rn2
  apply (@Star.trans _ _ (.ite A' m n1 n2))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.ite A' m' n1 n2))
  apply Star.hom _ _ rm; aesop
  apply (@Star.trans _ _ (.ite A' m' n1' n2))
  apply Star.hom _ _ rn1; aesop
  apply Star.hom _ _ rn2; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.idn {A A' m m' n n' : Tm} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .idn A m n ~>* .idn A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (.idn A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.idn A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.rfl {m m' : Tm} : m ~>* m' -> .rfl m ~>* .rfl m' := by
  intro rm; apply Star.hom _ _ rm; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.rw {A A' m m' n n' : Tm} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .rw A m n ~>* .rw A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (.rw A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.rw A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.subst {m n : Tm} σ : m ~>* n -> m.[σ] ~>* n.[σ] := by
  intro rm
  induction rm with
  | R => constructor
  | SE _ st ih =>
    apply Star.trans ih
    apply Star.one
    apply Step.subst _ st

@[aesop safe (rule_sets := [red])]
lemma SRed.up {σ τ : Var -> Tm} : SRed σ τ -> SRed (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply Red.subst _ (h n)

@[aesop safe (rule_sets := [red])]
lemma SRed.upn n {σ τ : Var -> Tm} :
    SRed σ τ -> SRed (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply SRed.up (ih h)

lemma Red.compat {m : Tm} {σ τ}: SRed σ τ -> m.[σ] ~>* m.[τ] := by
  open SRed in
  induction m generalizing σ τ
  all_goals asimp; try solve| aesop (rule_sets := [red])

def SConv (σ τ : Nat -> Tm) := ∀ x, σ x === τ x

@[aesop safe (rule_sets := [conv])]
lemma Conv.pi {A A' B B' : Tm} :
    A === A' -> B === B' -> .pi A B === .pi A' B' := by
  intro rA rB
  apply (@Conv.trans _ _ (.pi A' B))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rB; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.lam {A A' m m' : Tm} :
    A === A' -> m === m' -> .lam A m === .lam A' m' := by
  intro rA rm
  apply (@Conv.trans _ _ (.lam A' m))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rm; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.app {m m' n n' : Tm} :
    m === m' -> n === n' -> .app m n === .app m' n' := by
  intro rm rn
  apply (@Conv.trans _ _ (.app m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.sig {A A' B B' : Tm} :
    A === A' -> B === B' -> .sig A B === .sig A' B' := by
  intro rA rB
  apply (@Conv.trans _ _ (.sig A' B))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rB; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.tup {m m' n n' : Tm} :
    m === m' -> n === n' -> .tup m n === .tup m' n' := by
  intro rm rn
  apply (@Conv.trans _ _ (.tup m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.prj {A A' m m' n n' : Tm} :
    A === A' -> m === m' -> n === n' -> .prj A m n === .prj A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (.prj A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.prj A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.ite {A A' m m' n1 n1' n2 n2' : Tm} :
    A === A' -> m === m' -> n1 === n1' -> n2 === n2' ->
    .ite A m n1 n2 === .ite A' m' n1' n2' := by
  intro rA rm rn1 rn2
  apply (@Conv.trans _ _ (.ite A' m n1 n2))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.ite A' m' n1 n2))
  apply Conv.hom _ _ rm; aesop
  apply (@Conv.trans _ _ (.ite A' m' n1' n2))
  apply Conv.hom _ _ rn1; aesop
  apply Conv.hom _ _ rn2; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.idn {A A' m m' n n' : Tm} :
    A === A' -> m === m' -> n === n' -> .idn A m n === .idn A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (.idn A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.idn A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.rfl {m m' : Tm} : m === m' -> .rfl m === .rfl m' := by
  intro rm; apply Conv.hom _ _ rm; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.rw {A A' m m' n n' : Tm} :
    A === A' -> m === m' -> n === n' -> .rw A m n === .rw A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (.rw A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.rw A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.subst {m n : Tm} σ : m === n -> m.[σ] === n.[σ] := by
  intros r
  apply Conv.hom _ _ r
  intros x y
  apply Step.subst

@[aesop safe (rule_sets := [conv])]
lemma SConv.up {σ τ : Var -> Tm} : SConv σ τ -> SConv (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply Conv.subst _ (h n)

@[aesop safe (rule_sets := [conv])]
lemma SConv.upn n {σ τ : Var -> Tm} :
    SConv σ τ -> SConv (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply SConv.up (ih h)

lemma Conv.compat (m : Tm) {σ τ}: SConv σ τ -> m.[σ] === m.[τ] := by
  induction m generalizing σ τ
  all_goals asimp; try solve| aesop (rule_sets := [conv])

lemma Conv.subst1 m {n1 n2 : Tm} : n1 === n2 -> m.[n1/] === m.[n2/] := by
  intro h; apply Conv.compat
  intro x
  cases x with
  | zero => asimp; assumption
  | succ => asimp; constructor

@[aesop safe (rule_sets := [pstep])]
lemma PStep.refl {m : Tm} : m ≈> m := by
  induction m
  all_goals try constructor <;> assumption

@[aesop unsafe (rule_sets := [pstep])]
lemma Step.toPStep {m m' : Tm} : m ~> m' -> m ≈> m' := by
  open PStep in
  intro st
  induction st <;> aesop (rule_sets := [pstep])

@[aesop unsafe (rule_sets := [pstep])]
lemma PStep.toRed {m n : Tm} : m ≈> n -> m ~>* n := by
  intro ps
  induction ps
  all_goals try aesop (rule_sets := [red])
  case beta ihm ihn =>
    apply Star.trans
    . apply Red.app (Red.lam Star.R ihm) ihn
    . apply Star.one
      apply Step.beta
  case prj_elim ihm1 ihm2 ihn =>
    apply Star.trans
    . apply Red.prj Star.R (Red.tup ihm1 ihm2) ihn
    . apply Star.one
      apply Step.prj_elim
  case ite_tt ihn1 =>
    apply Star.trans
    . apply Red.ite Star.R Star.R ihn1 Star.R
    . apply Star.one
      apply Step.ite_tt
  case ite_ff ihn2 =>
    apply Star.trans
    . apply Red.ite Star.R Star.R Star.R ihn2
    . apply Star.one
      apply Step.ite_ff
  case rw_elim ihm =>
    apply Star.trans
    . apply Red.rw Star.R ihm Star.R
    . apply Star.one
      apply Step.rw_elim

@[aesop safe (rule_sets := [pstep])]
lemma PStep.subst {m n : Tm} σ : m ≈> n -> m.[σ] ≈> n.[σ] := by
  intro ps
  induction ps generalizing σ
  all_goals try asimp; aesop (rule_sets := [pstep])
  case beta A _ _ _ _ _ _ ihm ihn =>
    have := PStep.beta A.[σ] (ihm (up σ)) (ihn σ)
    asimp; asimp at this; assumption
  case prj_elim A _ _ _ _ _ _ _ _ _ ihm1 ihm2 ihn =>
    have := PStep.prj_elim A.[up σ] (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))
    asimp; asimp at this; assumption

def PSStep (σ τ : Var -> Tm) : Prop := ∀ x, (σ x) ≈> (τ x)

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.refl {σ : Var -> Tm} : PSStep σ σ := by
  intro x; induction x <;>
  apply PStep.refl

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.up {σ τ : Var -> Tm} :
    PSStep σ τ -> PSStep (up σ) (up τ) := by
  intro h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply PStep.subst; apply h

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.upn n {σ τ : Var -> Tm} :
    PSStep σ τ -> PSStep (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply PSStep.up (ih h)

@[aesop safe (rule_sets := [pstep])]
lemma PStep.compat {m n : Tm} {σ τ}:
    m ≈> n -> PSStep σ τ -> m.[σ] ≈> n.[τ] := by
  intro ps;
  induction ps generalizing σ τ
  all_goals asimp; try solve| aesop (rule_sets := [pstep])
  case beta A _ _ _ _ _ _ ihm ihn =>
    intro h
    have := PStep.beta A.[σ] (ihm (h.up)) (ihn h)
    asimp at this; assumption
  case prj_elim A _ _ _ _ _ _ _ _ _ ihm1 ihm2 ihn =>
    intro h
    specialize ihm1 h
    specialize ihm2 h
    specialize ihn (h.upn 2)
    have := PStep.prj_elim A.[up σ] ihm1 ihm2 ihn
    asimp at this; assumption

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.compat {m n : Tm} {σ τ} :
    m ≈> n -> PSStep σ τ -> PSStep (m .: σ) (n .: τ) := by
  intros ps pss x
  cases x with
  | zero => assumption
  | succ n => apply pss

@[aesop safe (rule_sets := [pstep])]
lemma PStep.subst1 m {n n' : Tm} : n ≈> n' -> m.[n/] ≈> m.[n'/] := by
  intro ps
  apply PStep.compat PStep.refl
  apply PSStep.compat ps PSStep.refl

@[aesop safe (rule_sets := [pstep])]
lemma PStep.compat_subst1 {m m' n n' : Tm} :
    m ≈> m' -> n ≈> n' -> m.[n/] ≈> m'.[n'/] := by
  intro ps1 ps2
  apply PStep.compat
  . assumption
  . apply PSStep.compat ps2 PSStep.refl

lemma PStep.diamond : Diamond PStep := by
  intros m m1 m2 ps
  induction ps generalizing m2
  case var =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case ty i =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case pi ihA ihB =>
    intro
    | pi psA psB =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨B, psB1, psB2⟩ := ihB psB
      existsi .pi A B; constructor
      . apply PStep.pi psA1 psB1
      . apply PStep.pi psA2 psB2
  case lam ihA ihm =>
    intro
    | lam psA psm =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      existsi .lam A m; constructor
      . apply PStep.lam psA1 psm1
      . apply PStep.lam psA2 psm2
  case app psm psn ihm ihn =>
    intro
    | app psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .app m n; constructor
      . apply PStep.app psm1 psn1
      . apply PStep.app psm2 psn2
    | beta A psm' psn' =>
      cases psm; case lam _ _ psm =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.lam PStep.refl psm')
      have ⟨n, psn1, psn2⟩ := ihn psn'
      cases psm1; case lam m _ psm1 =>
      cases psm2; case lam _ psm2 =>
      existsi m.[n/]
      constructor
      . apply PStep.beta <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  case beta ihm ihn =>
    intro
    | app psm psn =>
      cases psm; case lam _ psm =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.beta <;> assumption
    | beta _ psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  case sig ihA ihB =>
    intro
    | sig psA psB =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨B, psB1, psB2⟩ := ihB psB
      existsi .sig A B; constructor
      . apply PStep.sig psA1 psB1
      . apply PStep.sig psA2 psB2
  case tup ihm ihn =>
    intro
    | tup psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .tup m n; constructor
      . apply PStep.tup psm1 psn1
      . apply PStep.tup psm2 psn2
  case prj psA psm psn ihA ihm ihn =>
    intro
    | prj psA psm psn =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .prj A m n; constructor
      . apply PStep.prj psA1 psm1 psn1
      . apply PStep.prj psA2 psm2 psn2
    | prj_elim _ psm1 psm2 psn =>
      cases psm; case tup _ _ _ _ =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.tup psm1 psm2)
      have ⟨n, psn1, psn2⟩ := ihn psn
      cases psm1; case tup m1 m2 _ _ =>
      cases psm2; case tup _ _ psm1 psm2 =>
      existsi n.[m2,m1/]
      aesop (rule_sets := [pstep])
  case prj_elim A _ _ _ ihm1 ihm2 ihn =>
    intro
    | prj _ psm psn =>
      cases psm; case tup _ _ psm1 psm2 =>
      have ⟨m1, psm1, _⟩ := ihm1 psm1
      have ⟨m2, psm2, _⟩ := ihm2 psm2
      have ⟨n, psn, _⟩ := ihn psn
      existsi n.[m2,m1/]
      aesop (rule_sets := [pstep])
    | prj_elim _ psm1 psm2 psn =>
      have ⟨m1, psm11, psm12⟩ := ihm1 psm1
      have ⟨m2, psm21, psm22⟩ := ihm2 psm2
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi n.[m2,m1/]
      aesop (rule_sets := [pstep])
  case bool =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case tt =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case ff =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case ite psm _ _ ihA ihm ihn1 ihn2 =>
    intro
    | ite psA psm psn1 psn2 =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n1, psn11, psn12⟩ := ihn1 psn1
      have ⟨n2, psn21, psn22⟩ := ihn2 psn2
      existsi .ite A m n1 n2; constructor
      . apply PStep.ite psA1 psm1 psn11 psn21
      . apply PStep.ite psA2 psm2 psn12 psn22
    | ite_tt _ _ psn =>
      have ⟨n, psn11, psn12⟩ := ihn1 psn
      cases psm; existsi n; constructor
      . apply PStep.ite_tt _ _ psn11
      . assumption
    | ite_ff _ _ psn =>
      have ⟨n, psn21, psn22⟩ := ihn2 psn
      cases psm; existsi n; constructor
      . apply PStep.ite_ff _ _ psn21
      . assumption
  case ite_tt ihn =>
    intro
    | ite _ psm psn _ =>
      have ⟨n, _, psn⟩ := ihn psn
      existsi n; cases psm; constructor
      . assumption
      . apply PStep.ite_tt _ _ psn
    | ite_tt _ _ psn =>
      have ⟨n, _, _⟩ := ihn psn
      exists n
  case ite_ff ihn =>
    intro
    | ite _ psm _ psn =>
      have ⟨n, _, psn⟩ := ihn psn
      existsi n; cases psm; constructor
      . assumption
      . apply PStep.ite_ff _ _ psn
    | ite_ff _ _ psn =>
      have ⟨n, _, _⟩ := ihn psn
      exists n
  case idn ihA ihm ihn =>
    intro
    | idn psA psm psn =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .idn A m n; constructor
      . apply PStep.idn psA1 psm1 psn1
      . apply PStep.idn psA2 psm2 psn2
  case rfl ih =>
    intro
    | rfl ps =>
      have ⟨m, psm1, psm2⟩ := ih ps
      existsi .rfl m; constructor
      . apply PStep.rfl psm1
      . apply PStep.rfl psm2
  case rw psn ihA ihm ihn =>
    intro
    | rw psA psm psn =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .rw A m n; constructor
      . apply PStep.rw psA1 psm1 psn1
      . apply PStep.rw psA2 psm2 psn2
    | rw_elim _ _ psm =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      existsi m; cases psn; constructor
      . apply PStep.rw_elim _ _ psm1
      . assumption
  case rw_elim ih =>
    intro
    | rw _ psm psn =>
      have ⟨m, _, psm⟩ := ih psm
      existsi m; cases psn; constructor
      . assumption
      . apply PStep.rw_elim _ _ psm
    | rw_elim _ _ psm =>
      have ⟨m, psm1, psm2⟩ := ih psm
      exists m

lemma PStep.strip {m m1 m2 : Tm} :
    m ≈> m1 -> m ~>* m2 -> ∃ n, m1 ~>* n ∧ m2 ≈> n := by
  intros p r; induction r generalizing m1 p
  case R =>
    existsi m1; constructor
    . apply Star.R
    . assumption
  case SE s1 ih =>
    have ⟨m2, r, s2⟩ := ih p
    have ⟨m3, p1, p2⟩ := PStep.diamond s1.toPStep s2
    existsi m3; constructor
    . apply Star.trans r p2.toRed
    . assumption

theorem Step.confluent : Confluent Step := by
  intros x y z r; induction r generalizing z
  case R =>
    intro h; existsi z
    constructor
    assumption
    constructor
  case SE s ih =>
    intro h
    have ⟨z1, s1, s2⟩ := ih h
    have ⟨z2, s3, s4⟩ := PStep.strip s.toPStep s1
    existsi z2; constructor
    . assumption
    . apply Star.trans s2 s4.toRed

theorem Step.cr : CR Step := by
  rw[<-Confluent.cr]
  apply Step.confluent

lemma Red.var_inv {x y} : .var x ~>* y -> y = .var x := by
  intro r
  induction r with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.ty_inv {i x} : .ty i ~>* x -> x = .ty i := by
  intro r
  induction r with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.pi_inv {A B x} :
    .pi A B ~>* x ->
    ∃ A' B', A ~>* A' ∧ B ~>* B' ∧ x = .pi A' B' := by
  intro rd; induction rd
  case R => aesop
  case SE rd st ih =>
    have ⟨A1, B1, rA1, rB1, e⟩ := ih
    subst e
    cases st with
    | @pi_A _ A2 =>
      existsi A2, B1
      repeat' apply And.intro
      . apply Star.SE <;> assumption
      . apply rB1
      . rfl
    | @pi_B _ _ B2 =>
      existsi A1, B2
      repeat' apply And.intro
      . apply rA1
      . apply Star.SE <;> assumption
      . rfl

lemma Red.lam_inv {A m x} :
    .lam A m ~>* x ->
    ∃ A' m', A ~>* A' ∧ m ~>* m' ∧ x = .lam A' m' := by
  intro rd; induction rd
  case R => aesop
  case SE rd st ih =>
    have ⟨A1, m1, rA1, rm1, e⟩ := ih
    subst e
    cases st with
    | @lam_A _ A2 =>
      existsi A2, m1
      repeat' apply And.intro
      . apply Star.SE <;> assumption
      . apply rm1
      . rfl
    | @lam_M _ _ m2 =>
      existsi A1, m2
      repeat' apply And.intro
      . apply rA1
      . apply Star.SE <;> assumption
      . rfl

lemma Red.sig_inv {A B x} :
    .sig A B ~>* x ->
    ∃ A' B', A ~>* A' ∧ B ~>* B' ∧ x = .sig A' B' := by
  intro rd; induction rd
  case R => aesop
  case SE rd st ih =>
    have ⟨A1, B1, rA1, rB1, _⟩ := ih
    subst_vars; cases st with
    | @sig_A _ A2 =>
      existsi A2, B1
      repeat' apply And.intro
      . apply Star.SE <;> assumption
      . apply rB1
      . rfl
    | @sig_B _ _ B2 =>
      existsi A1, B2
      repeat' apply And.intro
      . apply rA1
      . apply Star.SE <;> assumption
      . rfl

lemma Red.tup_inv {m n x} :
    .tup m n ~>* x ->
    ∃ m' n', m ~>* m' ∧ n ~>* n' ∧ x = .tup m' n' := by
  intro rd; induction rd
  case R => aesop
  case SE rd st ih =>
    have ⟨m1, n1, rm1, rn1, _⟩ := ih
    subst_vars; cases st with
    | @tup_M _ m2 =>
      existsi m2, n1
      repeat' apply And.intro
      . apply Star.SE <;> assumption
      . apply rn1
      . rfl
    | @tup_N _ _ n2 =>
      existsi m1, n2
      repeat' apply And.intro
      . apply rm1
      . apply Star.SE <;> assumption
      . rfl

lemma Red.bool_inv {x} : .bool ~>* x -> x = .bool := by
  intro rd
  induction rd with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.tt_inv {x} : .tt ~>* x -> x = .tt := by
  intro rd
  induction rd with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.ff_inv {x} : .ff ~>* x -> x = .ff := by
  intro rd
  induction rd with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.idn_inv {A m n x} :
    .idn A m n ~>* x ->
    ∃ A' m' n', A ~>* A' ∧ m ~>* m' ∧ n ~>* n' ∧ x = .idn A' m' n' := by
  intro rd; induction rd
  case R => aesop
  case SE rd st ih =>
    have ⟨A1, m1, n1, rA1, rm1, rn1, _⟩ := ih
    subst_vars; cases st with
    | @idn_A _ A2 =>
      existsi A2, m1, n1
      repeat' apply And.intro
      . apply Star.SE <;> assumption
      . assumption
      . assumption
      . rfl
    | @idn_M _ _ m2 =>
      existsi A1, m2, n1
      repeat' apply And.intro
      . assumption
      . apply Star.SE <;> assumption
      . assumption
      . rfl
    | @idn_N _ _ _ n2 =>
      existsi A1, m1, n2
      repeat' apply And.intro
      . assumption
      . assumption
      . apply Star.SE <;> assumption
      . rfl

lemma Red.rfl_inv {m x} :
    .rfl m ~>* x -> ∃ m', m ~>* m' ∧ x = .rfl m' := by
  intro rd; induction rd
  case R => aesop
  case SE rd st ih =>
    have ⟨m1, rm1, _⟩ := ih
    subst_vars; cases st with
    | @rfl_M _ m2 =>
      existsi m2
      constructor
      . apply Star.SE <;> assumption
      . rfl

lemma Conv.ty_inj {i j} :
    .ty i === .ty j -> i = j := by
  intro eq
  have ⟨_, eq1, eq2⟩ := Step.cr eq
  have e1 := Red.ty_inv eq1
  have e2 := Red.ty_inv eq2
  cases e1; cases e2; trivial

lemma Conv.pi_inj {A1 A2 B1 B2} :
    .pi A1 B1 === .pi A2 B2 ->
    A1 === A2 ∧ B1 === B2 := by
  intro eq
  have ⟨x, eq1, eq2⟩ := Step.cr eq
  have ⟨_, _, _, _, e1⟩ := Red.pi_inv eq1
  have ⟨_, _, _, _, e2⟩ := Red.pi_inv eq2
  subst_vars; cases e2
  and_intros <;> try rfl
  . apply Conv.join <;> assumption
  . apply Conv.join <;> assumption

lemma Conv.sig_inj {A1 A2 B1 B2} :
    .sig A1 B1 === .sig A2 B2 ->
    A1 === A2 ∧ B1 === B2 := by
  intro eq
  have ⟨_, eq1, eq2⟩ := Step.cr eq
  have ⟨_, _, _, _, e1⟩ := Red.sig_inv eq1
  have ⟨_, _, _, _, e2⟩ := Red.sig_inv eq2
  subst_vars; cases e2
  and_intros <;> try rfl
  . apply Conv.join <;> assumption
  . apply Conv.join <;> assumption

lemma Conv.idn_inj {A1 A2 m1 m2 n1 n2} :
    .idn A1 m1 n1 === .idn A2 m2 n2 ->
    A1 === A2 ∧ m1 === m2 ∧ n1 === n2 := by
  intro eq
  have ⟨x, eq1, eq2⟩ := Step.cr eq
  have ⟨_, _, _, _, _, _, e1⟩ := Red.idn_inv eq1
  have ⟨_, _, _, _, _, _, e2⟩ := Red.idn_inv eq2
  subst_vars; cases e2
  and_intros
  . apply Conv.join <;> assumption
  . apply Conv.join <;> assumption
  . apply Conv.join <;> assumption
