import SStructTT.SStruct.Static.Step
open ARS

namespace SStruct.Static
variable {Srt : Type}

@[aesop safe (rule_sets := [pstep]) [constructors]]
inductive PStep : Tm Srt -> Tm Srt -> Prop where
  | var {x} :
    PStep (.var x) (.var x)
  | srt s i :
    PStep (.srt s i) (.srt s i)
  | pi {A A' B B'} r s :
    PStep A A' ->
    PStep B B' ->
    PStep (.pi A B r s) (.pi A' B' r s)
  | lam {A A' m m'} r s :
    PStep A A' ->
    PStep m m' ->
    PStep (.lam A m r s) (.lam A' m' r s)
  | app {m m' n n'} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app m n) (.app m' n')
  | beta A {m m' n n'} r s :
    PStep m m' ->
    PStep n n' ->
    PStep (.app (.lam A m r s) n) m'.[n'/]
  | sig {A A' B B'} r s :
    PStep A A' ->
    PStep B B' ->
    PStep (.sig A B r s) (.sig A' B' r s)
  | tup {m m' n n'} r s :
    PStep m m' ->
    PStep n n' ->
    PStep (.tup m n r s) (.tup m' n' r s)
  | prj {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.prj A m n) (.prj A' m' n')
  | prj_elim A {m1 m1' m2 m2' n n'} r s :
    PStep m1 m1' ->
    PStep m2 m2' ->
    PStep n n' ->
    PStep (.prj A (.tup m1 m2 r s) n) n'.[m2',m1'/]
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

def SRed (σ τ : Nat -> Tm Srt) := ∀ x, (σ x) ~>* (τ x)

lemma Step.subst {m n : Tm Srt} σ : m ~> n -> m.[σ] ~> n.[σ] := by
  intro st
  induction st generalizing σ
  all_goals try asimp; aesop
  case beta A m n r s  =>
    rw[show m.[n/].[σ] = m.[up σ].[n.[σ]/] by asimp]
    constructor
  case prj_elim A m1 m2 n r s =>
    rw[show n.[m2,m1/].[σ] = n.[upn 2 σ].[m2.[σ],m1.[σ]/] by asimp]
    constructor

@[aesop safe (rule_sets := [red])]
lemma Red.pi {A A' B B' : Tm Srt} r s :
    A ~>* A' -> B ~>* B' -> .pi A B r s ~>* .pi A' B' r s := by
  intro rA rB
  apply (@Star.trans _ _ (.pi A' B r s))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rB; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.lam {A A' m m' : Tm Srt} r s :
    A ~>* A' -> m ~>* m' -> .lam A m r s ~>* .lam A' m' r s := by
  intro rA rm
  apply (@Star.trans _ _ (.lam A' m r s))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rm; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.app {m m' n n' : Tm Srt} :
    m ~>* m' -> n ~>* n' -> .app m n ~>* .app m' n' := by
  intro rm rn
  apply (@Star.trans _ _ (.app m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.sig {A A' B B' : Tm Srt} r s :
    A ~>* A' -> B ~>* B' -> .sig A B r s ~>* .sig A' B' r s := by
  intro rA rB
  apply (@Star.trans _ _ (.sig A' B r s))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rB; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.tup {m m' n n' : Tm Srt} r s :
    m ~>* m' -> n ~>* n' -> .tup m n r s ~>* .tup m' n' r s := by
  intro rm rn
  apply (@Star.trans _ _ (.tup m' n r s))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.prj {A A' m m' n n' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .prj A m n ~>* .prj A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (.prj A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.prj A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.ite {A A' m m' n1 n1' n2 n2' : Tm Srt} :
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
lemma Red.idn {A A' m m' n n' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .idn A m n ~>* .idn A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (.idn A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.idn A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.rfl {m m' : Tm Srt} : m ~>* m' -> .rfl m ~>* .rfl m' := by
  intro rm; apply Star.hom _ _ rm; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.rw {A A' m m' n n' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .rw A m n ~>* .rw A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (.rw A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (.rw A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

@[aesop safe (rule_sets := [red])]
lemma Red.subst {m n : Tm Srt} σ : m ~>* n -> m.[σ] ~>* n.[σ] := by
  intro rm
  induction rm with
  | R => constructor
  | SE _ st ih =>
    apply Star.trans ih
    apply Star.one
    apply Step.subst _ st

@[aesop safe (rule_sets := [red])]
lemma SRed.up {σ τ : Var -> Tm Srt} : SRed σ τ -> SRed (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply Red.subst _ (h n)

@[aesop safe (rule_sets := [red])]
lemma SRed.upn n {σ τ : Var -> Tm Srt} :
    SRed σ τ -> SRed (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply SRed.up (ih h)

lemma Red.compat {m : Tm Srt} {σ τ}: SRed σ τ -> m.[σ] ~>* m.[τ] := by
  open SRed in
  induction m generalizing σ τ
  all_goals asimp; try solve| aesop (rule_sets := [red])

def SConv (σ τ : Nat -> Tm Srt) := ∀ x, σ x === τ x

@[aesop safe (rule_sets := [conv])]
lemma Conv.pi {A A' B B' : Tm Srt} r s :
    A === A' -> B === B' -> .pi A B r s === .pi A' B' r s := by
  intro rA rB
  apply (@Conv.trans _ _ (.pi A' B r s))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rB; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.lam {A A' m m' : Tm Srt} r s :
    A === A' -> m === m' -> .lam A m r s === .lam A' m' r s := by
  intro rA rm
  apply (@Conv.trans _ _ (.lam A' m r s))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rm; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.app {m m' n n' : Tm Srt} :
    m === m' -> n === n' -> .app m n === .app m' n' := by
  intro rm rn
  apply (@Conv.trans _ _ (.app m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.sig {A A' B B' : Tm Srt} r s :
    A === A' -> B === B' -> .sig A B r s === .sig A' B' r s := by
  intro rA rB
  apply (@Conv.trans _ _ (.sig A' B r s))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rB; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.tup {m m' n n' : Tm Srt} r s :
    m === m' -> n === n' -> .tup m n r s === .tup m' n' r s := by
  intro rm rn
  apply (@Conv.trans _ _ (.tup m' n r s))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.prj {A A' m m' n n' : Tm Srt} :
    A === A' -> m === m' -> n === n' -> .prj A m n === .prj A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (.prj A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.prj A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.ite {A A' m m' n1 n1' n2 n2' : Tm Srt} :
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
lemma Conv.idn {A A' m m' n n' : Tm Srt} :
    A === A' -> m === m' -> n === n' -> .idn A m n === .idn A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (.idn A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.idn A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.rfl {m m' : Tm Srt} : m === m' -> .rfl m === .rfl m' := by
  intro rm; apply Conv.hom _ _ rm; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.rw {A A' m m' n n' : Tm Srt} :
    A === A' -> m === m' -> n === n' -> .rw A m n === .rw A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (.rw A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (.rw A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

@[aesop safe (rule_sets := [conv])]
lemma Conv.subst {m n : Tm Srt} σ : m === n -> m.[σ] === n.[σ] := by
  intros r
  apply Conv.hom _ _ r
  intros x y
  apply Step.subst

@[aesop safe (rule_sets := [conv])]
lemma SConv.up {σ τ : Var -> Tm Srt} : SConv σ τ -> SConv (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply Conv.subst _ (h n)

@[aesop safe (rule_sets := [conv])]
lemma SConv.upn n {σ τ : Var -> Tm Srt} :
    SConv σ τ -> SConv (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply SConv.up (ih h)

lemma Conv.compat (m : Tm Srt) {σ τ}: SConv σ τ -> m.[σ] === m.[τ] := by
  induction m generalizing σ τ
  all_goals asimp; try solve| aesop (rule_sets := [conv])

lemma Conv.subst1 m {n1 n2 : Tm Srt} : n1 === n2 -> m.[n1/] === m.[n2/] := by
  intro h; apply Conv.compat
  intro x
  cases x with
  | zero => asimp; assumption
  | succ => asimp; constructor

@[aesop safe (rule_sets := [pstep])]
lemma PStep.refl {m : Tm Srt} : m ≈> m := by
  induction m
  all_goals try constructor <;> assumption

@[aesop unsafe (rule_sets := [pstep])]
lemma Step.toPStep {m m' : Tm Srt} : m ~> m' -> m ≈> m' := by
  open PStep in
  intro st
  induction st <;> aesop (rule_sets := [pstep])

@[aesop unsafe (rule_sets := [pstep])]
lemma PStep.toRed {m n : Tm Srt} : m ≈> n -> m ~>* n := by
  intro ps
  induction ps
  all_goals try aesop (rule_sets := [red])
  case beta r s _ _ ihm ihn =>
    apply Star.trans
    . apply Red.app (Red.lam r s Star.R ihm) ihn
    . apply Star.one
      apply Step.beta
  case prj_elim r s _ _ _ ihm1 ihm2 ihn =>
    apply Star.trans
    . apply Red.prj Star.R (Red.tup r s ihm1 ihm2) ihn
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
lemma PStep.subst {m n : Tm Srt} σ : m ≈> n -> m.[σ] ≈> n.[σ] := by
  intro ps
  induction ps generalizing σ
  all_goals try asimp; aesop (rule_sets := [pstep])
  case beta A _ _ _ _ r s _ _ ihm ihn =>
    have := PStep.beta A.[σ] r s (ihm (up σ)) (ihn σ)
    asimp; asimp at this; assumption
  case prj_elim A _ _ _ _ _ _ r s _ _ _ ihm1 ihm2 ihn =>
    have := PStep.prj_elim A.[up σ] r s (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))
    asimp; asimp at this; assumption

def PSStep (σ τ : Var -> Tm Srt) : Prop := ∀ x, (σ x) ≈> (τ x)

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.refl {σ : Var -> Tm Srt} : PSStep σ σ := by
  intro x; induction x <;>
  apply PStep.refl

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.up {σ τ : Var -> Tm Srt} :
    PSStep σ τ -> PSStep (up σ) (up τ) := by
  intro h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply PStep.subst; apply h

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.upn n {σ τ : Var -> Tm Srt} :
    PSStep σ τ -> PSStep (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply PSStep.up (ih h)

@[aesop safe (rule_sets := [pstep])]
lemma PStep.compat {m n : Tm Srt} {σ τ}:
    m ≈> n -> PSStep σ τ -> m.[σ] ≈> n.[τ] := by
  intro ps;
  induction ps generalizing σ τ
  all_goals asimp; try solve| aesop (rule_sets := [pstep])
  case beta A _ _ _ _ r s _ _ ihm ihn =>
    intro h
    have := PStep.beta A.[σ] r s (ihm (h.up)) (ihn h)
    asimp at this; assumption
  case prj_elim A _ _ _ _ _ _ r s _ _ _ ihm1 ihm2 ihn =>
    intro h
    specialize ihm1 h
    specialize ihm2 h
    specialize ihn (h.upn 2)
    have := PStep.prj_elim A.[up σ] r s ihm1 ihm2 ihn
    asimp at this; assumption

@[aesop safe (rule_sets := [pstep])]
lemma PSStep.compat {m n : Tm Srt} {σ τ} :
    m ≈> n -> PSStep σ τ -> PSStep (m .: σ) (n .: τ) := by
  intros ps pss x
  cases x with
  | zero => assumption
  | succ n => apply pss

@[aesop safe (rule_sets := [pstep])]
lemma PStep.subst1 m {n n' : Tm Srt} : n ≈> n' -> m.[n/] ≈> m.[n'/] := by
  intro ps
  apply PStep.compat PStep.refl
  apply PSStep.compat ps PSStep.refl

@[aesop safe (rule_sets := [pstep])]
lemma PStep.compat_subst1 {m m' n n' : Tm Srt} :
    m ≈> m' -> n ≈> n' -> m.[n/] ≈> m'.[n'/] := by
  intro ps1 ps2
  apply PStep.compat
  . assumption
  . apply PSStep.compat ps2 PSStep.refl

lemma PStep.diamond : @Diamond (Tm Srt) PStep := by
  intros m m1 m2 ps
  induction ps generalizing m2
  case var =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case srt i =>
    intro ps; existsi m2; constructor
    . assumption
    . apply PStep.refl
  case pi r s _ _ ihA ihB =>
    intro
    | pi _ _ psA psB =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨B, psB1, psB2⟩ := ihB psB
      existsi .pi A B r s; constructor
      . apply PStep.pi r s psA1 psB1
      . apply PStep.pi r s psA2 psB2
  case lam r s _ _ ihA ihm =>
    intro
    | lam _ _ psA psm =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      existsi .lam A m r s; constructor
      . apply PStep.lam r s psA1 psm1
      . apply PStep.lam r s psA2 psm2
  case app psm psn ihm ihn =>
    intro
    | app psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .app m n; constructor
      . apply PStep.app psm1 psn1
      . apply PStep.app psm2 psn2
    | beta A r s psm' psn' =>
      cases psm; case lam _ _ psm =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.lam r s PStep.refl psm')
      have ⟨n, psn1, psn2⟩ := ihn psn'
      cases psm1; case lam m _ psm1 =>
      cases psm2; case lam _ psm2 =>
      existsi m.[n/]
      constructor
      . apply PStep.beta <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  case beta _ s _ _ ihm ihn =>
    intro
    | app psm psn =>
      cases psm; case lam _ psm =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.beta <;> assumption
    | beta _ _ _ psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  case sig r s _ _ ihA ihB =>
    intro
    | sig _ _ psA psB =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨B, psB1, psB2⟩ := ihB psB
      existsi .sig A B r s; constructor
      . apply PStep.sig r s psA1 psB1
      . apply PStep.sig r s psA2 psB2
  case tup r s _ _ ihm ihn =>
    intro
    | tup _ _ psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .tup m n r s; constructor
      . apply PStep.tup r s psm1 psn1
      . apply PStep.tup r s psm2 psn2
  case prj psA psm psn ihA ihm ihn =>
    intro
    | prj psA psm psn =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      existsi .prj A m n; constructor
      . apply PStep.prj psA1 psm1 psn1
      . apply PStep.prj psA2 psm2 psn2
    | prj_elim _ r s psm1 psm2 psn =>
      cases psm; case tup _ _ _ _ =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.tup r s psm1 psm2)
      have ⟨n, psn1, psn2⟩ := ihn psn
      cases psm1; case tup m1 m2 _ _ =>
      cases psm2; case tup _ _ psm1 psm2 =>
      existsi n.[m2,m1/]
      aesop (rule_sets := [pstep])
  case prj_elim A r s _ _ _ ihm1 ihm2 ihn =>
    intro
    | prj _ psm psn =>
      cases psm; case tup _ _ psm1 psm2 =>
      have ⟨m1, psm1, _⟩ := ihm1 psm1
      have ⟨m2, psm2, _⟩ := ihm2 psm2
      have ⟨n, psn, _⟩ := ihn psn
      existsi n.[m2,m1/]
      aesop (rule_sets := [pstep])
    | prj_elim _ _ _ psm1 psm2 psn =>
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

lemma PStep.strip {m m1 m2 : Tm Srt} :
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

theorem Step.confluent : @Confluent (Tm Srt) Step := by
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

theorem Step.cr : @CR (Tm Srt) Step := by
  rw[<-Confluent.cr]
  apply Step.confluent

lemma Red.var_inv {x : Var} {y : Tm Srt} : .var x ~>* y -> y = .var x := by
  intro r
  induction r with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.srt_inv {s i} {x : Tm Srt} : .srt s i ~>* x -> x = .srt s i := by
  intro r
  induction r with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.pi_inv {A B x : Tm Srt} {r s} :
    .pi A B r s ~>* x ->
    ∃ A' B', A ~>* A' ∧ B ~>* B' ∧ x = .pi A' B' r s := by
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

lemma Red.lam_inv {A m x : Tm Srt} {r s} :
    .lam A m r s ~>* x ->
    ∃ A' m', A ~>* A' ∧ m ~>* m' ∧ x = .lam A' m' r s := by
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

lemma Red.sig_inv {A B x : Tm Srt} {r s} :
    .sig A B r s ~>* x ->
    ∃ A' B', A ~>* A' ∧ B ~>* B' ∧ x = .sig A' B' r s := by
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

lemma Red.tup_inv {m n x : Tm Srt} {r s} :
    .tup m n r s ~>* x ->
    ∃ m' n', m ~>* m' ∧ n ~>* n' ∧ x = .tup m' n' r s := by
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

lemma Red.bool_inv {x : Tm Srt} : .bool ~>* x -> x = .bool := by
  intro rd
  induction rd with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.tt_inv {x : Tm Srt} : .tt ~>* x -> x = .tt := by
  intro rd
  induction rd with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.ff_inv {x : Tm Srt} : .ff ~>* x -> x = .ff := by
  intro rd
  induction rd with
  | R => rfl
  | SE _ st e => subst e; cases st

lemma Red.idn_inv {A m n x : Tm Srt} :
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

lemma Red.rfl_inv {m x : Tm Srt} :
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

lemma Conv.srt_inj {s1 s2 : Srt} {i j} :
    .srt s1 i === .srt s2 j -> s1 = s2 ∧ i = j := by
  intro eq
  have ⟨_, eq1, eq2⟩ := Step.cr eq
  have e1 := Red.srt_inv eq1
  have e2 := Red.srt_inv eq2
  cases e1; cases e2; trivial

lemma Conv.pi_inj {A1 A2 B1 B2 : Tm Srt} {r1 r2 s1 s2} :
    .pi A1 B1 r1 s1 === .pi A2 B2 r2 s2 ->
    r1 = r2 ∧ s1 = s2 ∧ A1 === A2 ∧ B1 === B2 := by
  intro eq
  have ⟨x, eq1, eq2⟩ := Step.cr eq
  have ⟨_, _, _, _, e1⟩ := Red.pi_inv eq1
  have ⟨_, _, _, _, e2⟩ := Red.pi_inv eq2
  subst_vars; cases e2
  and_intros <;> try rfl
  . apply Conv.join <;> assumption
  . apply Conv.join <;> assumption

lemma Conv.sig_inj {A1 A2 B1 B2 : Tm Srt} {r1 r2 s1 s2} :
    .sig A1 B1 r1 s1 === .sig A2 B2 r2 s2 ->
    r1 = r2 ∧ s1 = s2 ∧ A1 === A2 ∧ B1 === B2 := by
  intro eq
  have ⟨_, eq1, eq2⟩ := Step.cr eq
  have ⟨_, _, _, _, e1⟩ := Red.sig_inv eq1
  have ⟨_, _, _, _, e2⟩ := Red.sig_inv eq2
  subst_vars; cases e2
  and_intros <;> try rfl
  . apply Conv.join <;> assumption
  . apply Conv.join <;> assumption

lemma Conv.idn_inj {A1 A2 m1 m2 n1 n2 : Tm Srt} :
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

namespace Tactic
open Lean Elab Tactic Meta

-- Eliminate an `Exists` proof `m` using `elim`.
def existsElim (m : Expr) (elim : Expr -> Expr -> MetaM Expr) : MetaM Expr := do
  let mType <- whnf $ <-inferType m
  match mType.getAppFnArgs with
  | (``Exists, #[a, p]) =>
    withLocalDecl `x BinderInfo.default a fun x =>
    withLocalDecl `y BinderInfo.default (.app p x) fun y => do
      let body <- mkLambdaFVars #[x, y] (<-elim x y)
      mkAppOptM ``Exists.elim #[none, none, none, m, body]
  | _ => throwError "existsElim {mType}"

-- Eliminate an `And` proof `m` using `elim`.
def andElim (m : Expr) (elim : Expr -> Expr -> MetaM Expr) : MetaM Expr := do
  let mType <- whnf $ <-inferType m
  match mType.and? with
  | some (a, b) =>
    withLocalDecl `x BinderInfo.default a fun x =>
    withLocalDecl `y BinderInfo.default b fun y => do
      let body <- mkLambdaFVars #[x, y] (<-elim x y)
      mkAppM ``And.elim #[body, m]
  | none => throwError f!"andElim {mType}"

-- Given a proposition consisting of `Exists` and `And`, find all `Eq`s among the conjuncts.
partial def prjEqs (m : Expr) (elim : Array Expr -> MetaM Expr) : MetaM Expr := do
  let mType <- whnf $ <-inferType m
  match mType.getAppFn.constName? with
  | some ``Exists =>
    existsElim m fun x y => do
      prjEqs x fun eqs1 =>
      prjEqs y fun eqs2 =>
      elim (eqs1 ++ eqs2)
  | some ``And =>
    andElim m fun x y =>
      prjEqs x fun eqs1 =>
      prjEqs y fun eqs2 =>
      elim (eqs1 ++ eqs2)
  | some ``Eq => elim #[m]
  | _ => elim #[]

-- Assuming `id : a === b`, get the associated expression of `id` and the inversion lemmas of `a` and `b`.
def getConvs (goal : MVarId) : MetaM (Array (Expr × Expr × Expr)) := do
  goal.withContext do
    let lctx <- getLCtx
    let mut acc := #[]
    for ldecl in lctx do
      let declExpr := ldecl.toExpr
      let declType <- whnf $ <-inferType declExpr
      match declType.app4? ``Conv with
      | some (_, _, a, b) =>
        acc := acc.push (declExpr, a, b)
      | _ => pure ()
    return acc

-- Apply `church_rosser` theorem to refute impossible conversion.
def applyCR (goal : MVarId) (m l1 l2 : Expr) : MetaM Expr := do
  let cr <- mkAppM ``Step.cr #[m]
  existsElim cr fun _ h =>
  andElim h fun h1 h2 => do
    let h1 <- mkAppM' l1 #[h1]
    let h2 <- mkAppM' l2 #[h2]
    prjEqs h1 fun es1 =>
    prjEqs h2 fun es2 => do
      let e1 <- mkAppM ``Eq.symm #[es1[0]!]
      let e2 <- mkAppM ``Eq.trans #[e1, es2[0]!]
      mkAppOptM ``Tm.noConfusion #[none, <-goal.getType, none, none, e2]

/-
  Get the associated inversion lemma for `m`. For more complex languages, the
  list of inversion lemmas need to be extended. -/
def getInvLemma (m : Expr) : MetaM Expr := do
  match m.getAppFn.constName? with
  | ``Tm.var  => return .const ``Red.var_inv  []
  | ``Tm.srt  => return .const ``Red.srt_inv  []
  | ``Tm.pi   => return .const ``Red.pi_inv   []
  | ``Tm.lam  => return .const ``Red.lam_inv  []
  | ``Tm.sig  => return .const ``Red.sig_inv  []
  | ``Tm.tup  => return .const ``Red.tup_inv  []
  | ``Tm.bool => return .const ``Red.bool_inv []
  | ``Tm.tt   => return .const ``Red.tt_inv   []
  | ``Tm.ff   => return .const ``Red.ff_inv   []
  | ``Tm.idn  => return .const ``Red.idn_inv  []
  | ``Tm.rfl  => return .const ``Red.rfl_inv  []
  | _ => throwError `getInvLemma

/--
  `false_conv` refutes impossible conversion proofs. -/
elab "false_conv" : tactic =>
  withMainContext do
    let goal <- getMainGoal
    let goalType <- getMainTarget
    for (m, a, b) in <-getConvs goal do
      let s <- saveState
      try
        let lemma_a <- getInvLemma a
        let lemma_b <- getInvLemma b
        let pf <- applyCR goal m lemma_a lemma_b
        if <-isDefEq goalType (<-inferType pf) then
          closeMainGoal `false_conv pf
      catch _ => restoreState s
end Tactic

example (a b : Tm Srt) (r : Rlv) (s : Srt) i :
    Conv Step (Tm.srt s i) (Tm.srt s i) ->
    (Tm.lam a b r s) === (Tm.srt s i) ->
    False := by
  intro h1 h2;
  false_conv
