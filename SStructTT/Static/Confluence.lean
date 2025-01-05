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
  | pi {A A' B B' r s} :
    PStep A A' ->
    PStep B B' ->
    PStep (.pi A B r s) (.pi A' B' r s)
  | lam {A A' m m' r s} :
    PStep A A' ->
    PStep m m' ->
    PStep (.lam A m r s) (.lam A' m' r s)
  | app {m m' n n'} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app m n) (.app m' n')
  | beta {A m m' n n' r s} :
    PStep m m' ->
    PStep n n' ->
    PStep (.app (.lam A m r s) n) m'.[n'/]
  | sig {A A' B B' r s} :
    PStep A A' ->
    PStep B B' ->
    PStep (.sig A B r s) (.sig A' B' r s)
  | pair {m m' n n' r s} :
    PStep m m' ->
    PStep n n' ->
    PStep (.pair m n r s) (.pair m n r s)
  | proj {A A' m m' n n'} :
    PStep A A' ->
    PStep m m' ->
    PStep n n' ->
    PStep (.proj A m n) (.proj A' m' n')
  | projE {A m1 m1' m2 m2' n n' r s} :
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
  | iteT {A n1 n1' n2} :
    PStep n1 n1' ->
    PStep (.ite A .tt n1 n2) n1'
  | iteF {A n1 n2 n2'} :
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
  | rwE {A m m' n} :
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
  | succ n =>
    asimp
    apply Red.subst _ (h n)

lemma SRed.upn n {σ τ : Var -> Tm Srt} : SRed σ τ -> SRed (upn n σ) (upn n τ) := by
  induction n with
  | zero => asimp
  | succ n ih =>
    intro h
    apply SRed.up (ih h)

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
      asimp at this
      assumption
  | bool => aesop
  | tt => aesop
  | ff => aesop
  | ite _ _ _ _ ihA _ _ _ =>
    asimp; intro
    apply Red.ite
    . apply ihA; apply SRed.up; aesop
    . aesop
    . aesop
    . aesop
  | id =>
    asimp; intro; apply Red.id <;> aesop
  | rfl =>
    asimp; intro; apply Red.rfl; aesop
  | rw _ _ _ ihA _ _ =>
    asimp; intro h
    apply Red.rw
    . apply ihA
      have := SRed.upn 2 h
      asimp at this
      assumption
    . aesop
    . aesop
