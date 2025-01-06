import SStructTT.Static.Step
open ARS

namespace Static
variable {Srt : Type}

@[aesop safe [constructors]]
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
  | pair {m m' n n'} r s :
    PStep m m' ->
    PStep n n' ->
    PStep (.pair m n r s) (.pair m' n' r s)
  | proj {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.proj A m n) (.proj A' m' n')
  | projE A {m1 m1' m2 m2' n n'} r s :
    PStep m1 m1' ->
    PStep m2 m2' ->
    PStep n n' ->
    PStep (.proj A (.pair m1 m2 r s) n) n'.[m2',m1'/]
  | bool : PStep .bool .bool
  | tt : PStep .tt .tt
  | ff : PStep .ff .ff
  | ite {A A' m m' n1 n1' n2 n2'} :
    PStep A A' ->
    PStep m m' ->
    PStep n1 n1' ->
    PStep n2 n2' ->
    PStep (.ite A m n1 n2) (.ite A' m' n1' n2')
  | iteT A {n1 n1'} n2 :
    PStep n1 n1' ->
    PStep (.ite A .tt n1 n2) n1'
  | iteF A n1 {n2 n2'} :
    PStep n2 n2' ->
    PStep (.ite A .ff n1 n2) n2'
  | id {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.id A m n) (.id A' m' n')
  | rfl {m m'} :
    PStep m m' ->
    PStep (.rfl m) (.rfl m')
  | rw {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.rw A m n) (.rw A' m' n')
  | rwE A {m m'} n :
    PStep m m' ->
    PStep (.rw A m (.rfl n)) m'

infix:50 " ≈> " => PStep

def SRed (σ τ : Nat -> Tm Srt) := ∀ x, (σ x) ~>* (τ x)

lemma Step.subst {m n : Tm Srt} σ : m ~> n -> m.[σ] ~> n.[σ] := by
  intro st
  induction st generalizing σ
  all_goals try asimp; aesop
  case beta A m n r s  =>
    have : m.[n/].[σ] = m.[up σ].[n.[σ]/] := by asimp
    rw[this]; constructor
  case projE A m1 m2 n r s =>
    have : n.[m2,m1/].[σ] = n.[upn 2 σ].[m2.[σ],m1.[σ]/] := by asimp
    rw[this]; constructor

lemma Red.pi {A A' B B' : Tm Srt} r s :
    A ~>* A' -> B ~>* B' -> .pi A B r s ~>* .pi A' B' r s := by
  intro rA rB
  apply (@Star.trans _ _ (Tm.pi A' B r s))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rB; aesop

lemma Red.lam {A A' m m' : Tm Srt} r s :
    A ~>* A' -> m ~>* m' -> .lam A m r s ~>* .lam A' m' r s := by
  intro rA rm
  apply (@Star.trans _ _ (Tm.lam A' m r s))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rm; aesop

lemma Red.app {m m' n n' : Tm Srt} :
    m ~>* m' -> n ~>* n' -> .app m n ~>* .app m' n' := by
  intro rm rn
  apply (@Star.trans _ _ (Tm.app m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.sig {A A' B B' : Tm Srt} r s :
    A ~>* A' -> B ~>* B' -> .sig A B r s ~>* .sig A' B' r s := by
  intro rA rB
  apply (@Star.trans _ _ (Tm.sig A' B r s))
  apply Star.hom _ _ rA; aesop
  apply Star.hom _ _ rB; aesop

lemma Red.pair {m m' n n' : Tm Srt} r s :
    m ~>* m' -> n ~>* n' -> .pair m n r s ~>* .pair m' n' r s := by
  intro rm rn
  apply (@Star.trans _ _ (Tm.pair m' n r s))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.proj {A A' m m' n n' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .proj A m n ~>* .proj A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (Tm.proj A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (Tm.proj A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.ite {A A' m m' n1 n1' n2 n2' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n1 ~>* n1' -> n2 ~>* n2' ->
    .ite A m n1 n2 ~>* .ite A' m' n1' n2' := by
  intro rA rm rn1 rn2
  apply (@Star.trans _ _ (Tm.ite A' m n1 n2))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (Tm.ite A' m' n1 n2))
  apply Star.hom _ _ rm; aesop
  apply (@Star.trans _ _ (Tm.ite A' m' n1' n2))
  apply Star.hom _ _ rn1; aesop
  apply Star.hom _ _ rn2; aesop

lemma Red.id {A A' m m' n n' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .id A m n ~>* .id A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (Tm.id A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (Tm.id A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.rfl {m m' : Tm Srt} : m ~>* m' -> .rfl m ~>* .rfl m' := by
  intro rm; apply Star.hom _ _ rm; aesop

lemma Red.rw {A A' m m' n n' : Tm Srt} :
    A ~>* A' -> m ~>* m' -> n ~>* n' -> .rw A m n ~>* .rw A' m' n' := by
  intro rA rm rn
  apply (@Star.trans _ _ (Tm.rw A' m n))
  apply Star.hom _ _ rA; aesop
  apply (@Star.trans _ _ (Tm.rw A' m' n))
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.subst {m n : Tm Srt} σ : m ~>* n -> m.[σ] ~>* n.[σ] := by
  intro rm
  induction rm with
  | R => constructor
  | SE _ st ih =>
    apply Star.trans ih
    apply Star.one
    apply Step.subst _ st

lemma SRed.up {σ τ : Var -> Tm Srt} : SRed σ τ -> SRed (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply Red.subst _ (h n)

lemma SRed.upn n {σ τ : Var -> Tm Srt} :
    SRed σ τ -> SRed (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply SRed.up (ih h)

lemma Red.compat {m : Tm Srt} {σ τ}: SRed σ τ -> m.[σ] ~>* m.[τ] := by
  induction m generalizing σ τ with
  | var => aesop
  | srt => aesop
  | pi _ _ _ _ _ ihB =>
    asimp; intro
    apply Red.pi
    . aesop
    . apply ihB; apply SRed.up; aesop
  | lam _ _ _ _ _ ihm =>
    asimp; intro
    apply Red.lam
    . aesop
    . apply ihm; apply SRed.up; aesop
  | app =>
    asimp; intro; apply Red.app <;> aesop
  | sig _ _ _ _ _ ihB =>
    asimp; intro
    apply Red.sig
    . aesop
    . apply ihB; apply SRed.up; aesop
  | pair =>
    asimp; intro; apply Red.pair <;> aesop
  | proj _ _ _ ihA _ ihn =>
    asimp; intro h
    apply Red.proj
    . apply ihA; apply SRed.up; aesop
    . aesop
    . apply ihn
      have := SRed.upn 2 h
      asimp at this; assumption
  | bool => aesop
  | tt => aesop
  | ff => aesop
  | ite _ _ _ _ ihA _ _ _ =>
    asimp; intro
    apply Red.ite
    . apply ihA; apply SRed.up; aesop
    all_goals aesop
  | id =>
    asimp; intro; apply Red.id <;> aesop
  | rfl =>
    asimp; intro; apply Red.rfl; aesop
  | rw _ _ _ ihA _ _ =>
    asimp; intro h
    apply Red.rw
    . apply ihA
      have := SRed.upn 2 h
      asimp at this; assumption
    all_goals aesop

def SConv (σ τ : Nat -> Tm Srt) := ∀ x, σ x === τ x

lemma Conv.pi {A A' B B' : Tm Srt} r s :
    A === A' -> B === B' -> .pi A B r s === .pi A' B' r s := by
  intro rA rB
  apply (@Conv.trans _ _ (Tm.pi A' B r s))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rB; aesop

lemma Conv.lam {A A' m m' : Tm Srt} r s :
    A === A' -> m === m' -> .lam A m r s === .lam A' m' r s := by
  intro rA rm
  apply (@Conv.trans _ _ (Tm.lam A' m r s))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rm; aesop

lemma Conv.app {m m' n n' : Tm Srt} :
    m === m' -> n === n' -> .app m n === .app m' n' := by
  intro rm rn
  apply (@Conv.trans _ _ (Tm.app m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

lemma Conv.sig {A A' B B' : Tm Srt} r s :
    A === A' -> B === B' -> .sig A B r s === .sig A' B' r s := by
  intro rA rB
  apply (@Conv.trans _ _ (Tm.sig A' B r s))
  apply Conv.hom _ _ rA; aesop
  apply Conv.hom _ _ rB; aesop

lemma Conv.pair {m m' n n' : Tm Srt} r s :
    m === m' -> n === n' -> .pair m n r s === .pair m' n' r s := by
  intro rm rn
  apply (@Conv.trans _ _ (Tm.pair m' n r s))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

lemma Conv.proj {A A' m m' n n' : Tm Srt} :
    A === A' -> m === m' -> n === n' -> .proj A m n === .proj A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (Tm.proj A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (Tm.proj A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

lemma Conv.ite {A A' m m' n1 n1' n2 n2' : Tm Srt} :
    A === A' -> m === m' -> n1 === n1' -> n2 === n2' ->
    .ite A m n1 n2 === .ite A' m' n1' n2' := by
  intro rA rm rn1 rn2
  apply (@Conv.trans _ _ (Tm.ite A' m n1 n2))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (Tm.ite A' m' n1 n2))
  apply Conv.hom _ _ rm; aesop
  apply (@Conv.trans _ _ (Tm.ite A' m' n1' n2))
  apply Conv.hom _ _ rn1; aesop
  apply Conv.hom _ _ rn2; aesop

lemma Conv.id {A A' m m' n n' : Tm Srt} :
    A === A' -> m === m' -> n === n' -> .id A m n === .id A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (Tm.id A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (Tm.id A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

lemma Conv.rfl {m m' : Tm Srt} : m === m' -> .rfl m === .rfl m' := by
  intro rm; apply Conv.hom _ _ rm; aesop

lemma Conv.rw {A A' m m' n n' : Tm Srt} :
    A === A' -> m === m' -> n === n' -> .rw A m n === .rw A' m' n' := by
  intro rA rm rn
  apply (@Conv.trans _ _ (Tm.rw A' m n))
  apply Conv.hom _ _ rA; aesop
  apply (@Conv.trans _ _ (Tm.rw A' m' n))
  apply Conv.hom _ _ rm; aesop
  apply Conv.hom _ _ rn; aesop

lemma Conv.subst {m n : Tm Srt} σ : m === n -> m.[σ] === n.[σ] := by
  intros r
  apply Conv.hom _ _ r
  intros x y
  apply Step.subst

lemma SConv.up {σ τ : Var -> Tm Srt} : SConv σ τ -> SConv (up σ) (up τ) := by
  intros h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply Conv.subst _ (h n)

lemma SConv.upn n {σ τ : Var -> Tm Srt} :
    SConv σ τ -> SConv (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply SConv.up (ih h)

lemma Conv.compat (m : Tm Srt) {σ τ}: SConv σ τ -> m.[σ] === m.[τ] := by
  induction m generalizing σ τ with
  | var => aesop
  | srt => aesop
  | pi _ _ _ _ _ ihB =>
    asimp; intro
    apply Conv.pi
    . aesop
    . apply ihB; apply SConv.up; aesop
  | lam _ _ _ _ _ ihm =>
    asimp; intro
    apply Conv.lam
    . aesop
    . apply ihm; apply SConv.up; aesop
  | app =>
    asimp; intro; apply Conv.app <;> aesop
  | sig _ _ _ _ _ ihB =>
    asimp; intro
    apply Conv.sig
    . aesop
    . apply ihB; apply SConv.up; aesop
  | pair =>
    asimp; intro; apply Conv.pair <;> aesop
  | proj _ _ _ ihA _ ihn =>
    asimp; intro h
    apply Conv.proj
    . apply ihA; apply SConv.up; aesop
    . aesop
    . apply ihn
      have := SConv.upn 2 h
      asimp at this; assumption
  | bool => aesop
  | tt => aesop
  | ff => aesop
  | ite _ _ _ _ ihA _ _ _ =>
    asimp; intro
    apply Conv.ite
    . apply ihA; apply SConv.up; aesop
    all_goals aesop
  | id =>
    asimp; intro; apply Conv.id <;> aesop
  | rfl =>
    asimp; intro; apply Conv.rfl; aesop
  | rw _ _ _ ihA _ _ =>
    asimp; intro h
    apply Conv.rw
    . apply ihA
      have := SConv.upn 2 h
      asimp at this; assumption
    all_goals aesop

lemma Conv.subst1 m {n1 n2 : Tm Srt} : n1 === n2 -> m.[n1/] === m.[n2/] := by
  intro h; apply Conv.compat
  intro x
  cases x with
  | zero => asimp; assumption
  | succ => asimp; constructor

@[aesop safe]
lemma PStep.refl {m : Tm Srt} : m ≈> m := by
  induction m
  all_goals try constructor <;> assumption

lemma Step.toPStep {m m' : Tm Srt} : m ~> m' -> m ≈> m' := by
  intro st
  induction st <;> aesop

lemma PStep.toRed {m n : Tm Srt} : m ≈> n -> m ~>* n := by
  intro ps
  induction ps with
  | var => constructor
  | srt => constructor
  | pi => apply Red.pi <;> assumption
  | lam => apply Red.lam <;> assumption
  | app => apply Red.app <;> assumption
  | beta _ r s _ _ ihm ihn =>
    apply Star.trans
    . apply Red.app (Red.lam r s Star.R ihm) ihn
    . apply Star.one
      apply Step.beta
  | sig => apply Red.sig <;> assumption
  | pair => apply Red.pair <;> assumption
  | proj => apply Red.proj <;> assumption
  | projE _ r s _ _ _ ihm1 ihm2 ihn =>
    apply Star.trans
    . apply Red.proj Star.R (Red.pair r s ihm1 ihm2) ihn
    . apply Star.one
      apply Step.projE
  | bool => constructor
  | tt => constructor
  | ff => constructor
  | ite => apply Red.ite <;> assumption
  | iteT _ _ _ ihn1 =>
    apply Star.trans
    . apply Red.ite Star.R Star.R ihn1 Star.R
    . apply Star.one
      apply Step.iteT
  | iteF _ _ _ ihn2 =>
    apply Star.trans
    . apply Red.ite Star.R Star.R Star.R ihn2
    . apply Star.one
      apply Step.iteF
  | id => apply Red.id <;> assumption
  | rfl => apply Red.rfl; assumption
  | rw => apply Red.rw <;> assumption
  | rwE _ _ _ ihm =>
    apply Star.trans
    . apply Red.rw Star.R ihm Star.R
    . apply Star.one
      apply Step.rwE

lemma PStep.subst {m n : Tm Srt} σ : m ≈> n -> m.[σ] ≈> n.[σ] := by
  intro ps
  induction ps generalizing σ
  all_goals try asimp; aesop
  case beta A _ _ _ _ r s _ _ ihm ihn =>
    have := PStep.beta A.[σ] r s (ihm (up σ)) (ihn σ)
    asimp; asimp at this; assumption
  case projE A _ _ _ _ _ _ r s _ _ _ ihm1 ihm2 ihn =>
    have := PStep.projE A.[up σ] r s (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))
    asimp; asimp at this; assumption

def PSStep (σ τ : Var -> Tm Srt) : Prop := ∀ x, (σ x) ≈> (τ x)

lemma PSStep.refl {σ : Var -> Tm Srt} : PSStep σ σ := by
  intro x; induction x <;>
  apply PStep.refl

lemma PSStep.up {σ τ : Var -> Tm Srt} :
    PSStep σ τ -> PSStep (up σ) (up τ) := by
  intro h x
  cases x with
  | zero => asimp; constructor
  | succ n => asimp; apply PStep.subst; apply h

lemma PSStep.upn n {σ τ : Var -> Tm Srt} :
    PSStep σ τ -> PSStep (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih => intro h; apply PSStep.up (ih h)

lemma PStep.compat {m n : Tm Srt} {σ τ}:
    m ≈> n -> PSStep σ τ -> m.[σ] ≈> n.[τ] := by
  intro ps;
  induction ps generalizing σ τ with
  | var => aesop
  | srt => aesop
  | pi _ _ _ _ _ ihB =>
    asimp; intro
    constructor
    . aesop
    . apply ihB; apply PSStep.up; aesop
  | lam _ _ _ _ _ ihm =>
    asimp; intro
    constructor
    . aesop
    . apply ihm; apply PSStep.up; aesop
  | app => asimp; aesop
  | beta A r s _ _ ihm ihn =>
    asimp; intro h
    have := PStep.beta A.[σ] r s (ihm (h.up)) (ihn h)
    asimp at this; assumption
  | sig _ _ _ _ _ ihB =>
    asimp; intro
    constructor
    . aesop
    . apply ihB; apply PSStep.up; aesop
  | pair => asimp; aesop
  | proj _ _ _ ihA _ ihn =>
    asimp; intro h
    constructor
    . apply ihA; apply PSStep.up; aesop
    . aesop
    . apply ihn
      have := PSStep.upn 2 h
      asimp at this
      assumption
  | projE A r s _ _ _ ihm1 ihm2 ihn =>
    asimp; intro h
    specialize ihm1 h
    specialize ihm2 h
    specialize ihn (h.upn 2)
    have := PStep.projE A.[up σ] r s ihm1 ihm2 ihn
    asimp at this; assumption
  | bool => aesop
  | tt => aesop
  | ff => aesop
  | ite _ _ _ _ ihA _ _ _ =>
    asimp; intro
    constructor
    . apply ihA; apply PSStep.up; aesop
    all_goals aesop
  | iteT => asimp; aesop
  | iteF => asimp; aesop
  | id => asimp; aesop
  | rfl => asimp; aesop
  | rw _ _ _ ihA _ _ =>
    asimp; intro h
    constructor
    . apply ihA
      have := PSStep.upn 2 h
      asimp at this
      assumption
    all_goals aesop
  | rwE => asimp; aesop

lemma PSStep.compat {m n : Tm Srt} {σ τ} :
    m ≈> n -> PSStep σ τ -> PSStep (m .: σ) (n .: τ) := by
  intros ps pss x
  cases x with
  | zero => assumption
  | succ n => apply pss

lemma PStep.subst1 m {n n' : Tm Srt} : n ≈> n' -> m.[n/] ≈> m.[n'/] := by
  intro ps
  apply PStep.compat PStep.refl
  apply PSStep.compat ps PSStep.refl

lemma PStep.compat_subst1 {m m' n n' : Tm Srt} :
    m ≈> m' -> n ≈> n' -> m.[n/] ≈> m'.[n'/] := by
  intro ps1 ps2
  apply PStep.compat
  . assumption
  . apply PSStep.compat ps2 PSStep.refl

lemma PStep.diamond : @Diamond (Tm Srt) PStep := by
  intros m m1 m2 ps
  induction ps generalizing m2 with
  | var => intro ps; exists m2; aesop
  | srt i => intro ps; exists m2; aesop
  | pi r s _ _ ihA ihB =>
    intro ps; cases ps with
    | pi _ _ psA psB =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨B, psB1, psB2⟩ := ihB psB
      exists .pi A B r s; aesop
  | lam r s _ _ ihA ihm =>
    intro ps; cases ps with
    | lam _ _ psA psm =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      exists .lam A m r s; aesop
  | app psm psn ihm ihn =>
    intro ps; cases ps with
    | app psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists .app m n; aesop
    | beta A r s psm' psn' =>
      cases psm; case lam _ _ _ psm =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.lam r s PStep.refl psm')
      have ⟨n, psn1, psn2⟩ := ihn psn'
      cases psm1; case lam m _ psm1 =>
      cases psm2; case lam _ psm2 =>
      exists m.[n/]
      constructor
      . apply PStep.beta <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  | beta _ r s _ _ ihm ihn =>
    intro ps; cases ps with
    | app psm psn =>
      cases psm; case lam _ psm =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.beta <;> assumption
    | beta _ _ _ psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists m.[n/]
      constructor
      . apply PStep.compat_subst1 <;> assumption
      . apply PStep.compat_subst1 <;> assumption
  | sig r s _ _ ihA ihB =>
    intro ps; cases ps with
    | sig _ _ psA psB =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨B, psB1, psB2⟩ := ihB psB
      exists .sig A B r s; aesop
  | pair r s _ _ ihm ihn =>
    intro ps; cases ps with
    | pair _ _ psm psn =>
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists .pair m n r s; aesop
  | proj psA psm psn ihA ihm ihn =>
    intro ps; cases ps with
    | proj psA psm psn =>
      have ⟨A, psA1, psA2⟩ := ihA psA
      have ⟨m, psm1, psm2⟩ := ihm psm
      have ⟨n, psn1, psn2⟩ := ihn psn
      exists .proj A m n; aesop
    | projE _ r s psm1 psm2 psn =>
      cases psm; case pair _ _ _ _ =>
      have ⟨_, psm1, psm2⟩ := ihm (PStep.pair r s psm1 psm2)
      have ⟨n, psn1, psn2⟩ := ihn psn
      cases psm1; case pair m1 m2 _ _ =>
      cases psm2; case pair _ _ psm1 psm2 =>
      exists n.[m2,m1/]
      constructor
      . apply PStep.projE <;> assumption
      . apply PStep.compat psn2
        apply PSStep.compat psm2
        apply PSStep.compat psm1
        apply PSStep.refl
  | projE A r s _ _ _ ihm1 ihm2 ihn =>
    intro ps; cases ps with
    | proj => sorry
    | projE => sorry
  | _ => sorry
