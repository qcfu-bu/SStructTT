import Mathlib.Tactic

namespace ARS
section Definitions
set_option quotPrecheck false
notation:70 e1:70 " <=2 " e2:70 => (∀ {x y}, e1 x y -> e2 x y)

def Pred (T : Type) := T -> Prop
def Rel (T : Type) := T -> Pred T
attribute [reducible] Pred Rel

variable {T : Type} (e : Rel T)

inductive Star (x : T) : T -> Prop where
  | R : Star x x
  | SE {y z} : Star x y -> e y z -> Star x z

inductive Conv (x : T) : T -> Prop where
  | R : Conv x x
  | SE  {y z} : Conv x y -> e y z -> Conv x z
  | SEi {y z} : Conv x y -> e z y -> Conv x z

attribute [aesop safe] Star.R Conv.R

def Com (R S : Rel T) := ∀ {x y z}, R x y -> S x z -> ∃ u, S y u ∧ R z u
def Joinable (R : Rel T) x y := ∃ z, R x z ∧ R y z
def Diamond := ∀ {x y z}, e x y -> e x z -> ∃ u, e y u ∧ e z u
def Confluent := ∀ {x y z}, Star e x y -> Star e x z -> Joinable (Star e) y z
def CR := ∀ {x y}, Conv e x y -> Joinable (Star e) x y

def Reducible (x : T) := ∃ y, e x y
def Normal (x : T) := ¬ Reducible e x
def NF (x y : T) := Star e x y ∧ Normal e y

inductive SN : T -> Prop where
  | intro x : (∀ y, e x y -> SN y) -> SN x
end Definitions

section Lemmas
variable {T : Type} {e : Rel T}

lemma Star.one {x y} : e x y -> Star e x y := by
  intro h
  apply Star.SE
  apply Star.R
  assumption

lemma Star.trans {y x z} : Star e x y -> Star e y z -> Star e x z := by
  intros h1 h2
  induction h2 with
  | R => exact h1
  | SE _ rel ih => apply Star.SE ih rel

lemma Star.ES {y x z} : e x y -> Star e y z -> Star e x z := by
  intro h
  apply Star.trans
  apply Star.one
  assumption

lemma Star.Conv {x y} : Star e x y -> Conv e x y := by
  intro h
  induction h with
  | R => constructor
  | SE _ rel ih => apply Conv.SE ih rel

lemma Star.img {T1 T2 e1 e2} {f : T1 -> T2} :
    (∀ {x y}, e1 x y -> Star e2 (f x) (f y)) ->
    (∀ {x y}, Star e1 x y -> Star e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | R => constructor
  | @SE y z _ rel ih => apply Star.trans ih (h1 rel)

lemma Star.hom {T1 T2 e1 e2} (f : T1 -> T2) :
    (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
    (∀ {x y}, Star e1 x y -> Star e2 (f x) (f y)) := by
  intro h; apply Star.img
  intros x y h0
  specialize h h0
  apply Star.one h

lemma Star.closure {e1 e2 : Rel T} : e1 <=2 Star e2 -> Star e1 <=2 Star e2 := by
  apply Star.img

lemma Star.monotone {e1 e2 : Rel T} : e1 <=2 e2 -> Star e1 <=2 Star e2 := by
  intro h1; apply Star.closure
  intros x y h2
  specialize h1 h2
  apply Star.one h1

lemma Conv.one {x y} : e x y -> Conv e x y := by
  intro h; apply Conv.SE Conv.R h

lemma Conv.onei {x y} : e y x -> Conv e x y := by
  intro h; apply Conv.SEi Conv.R h

lemma Conv.trans {y x z} : Conv e x y -> Conv e y z -> Conv e x z := by
  intros h1 h2
  induction h2 with
  | R => exact h1
  | SE _ rel ih => apply Conv.SE ih rel
  | SEi _ rel ih => apply Conv.SEi ih rel

lemma Conv.ES {y x z} : e x y -> Conv e y z -> Conv e x z := by
  intro h
  apply Conv.trans
  apply Conv.one
  assumption

lemma Conv.ESi {y x z} : e y x -> Conv e y z -> Conv e x z := by
  intro h
  apply Conv.trans
  apply Conv.onei
  assumption

lemma Conv.sym {x y} : Conv e x y -> Conv e y x := by
  intro h
  induction h with
  | R => constructor
  | SE _ rel ih => apply Conv.ESi rel ih
  | SEi _ rel ih => apply Conv.ES rel ih

lemma Conv.join {y x z} : Star e x y -> Star e z y -> Conv e x z := by
  intro h1 h2
  apply Conv.trans
  apply Star.Conv h1
  apply Conv.sym
  apply Star.Conv h2

lemma Conv.img {T1 T2 e1 e2} {f : T1 -> T2} :
    (∀ {x y}, e1 x y -> Conv e2 (f x) (f y)) ->
    (∀ {x y}, Conv e1 x y -> Conv e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | R => constructor
  | SE _ rel ih =>
    apply Conv.trans ih (h1 rel)
  | SEi _ rel ih =>
    apply Conv.trans ih
    apply Conv.sym
    apply h1 rel

lemma Conv.hom {T1 T2 e1 e2} (f : T1 -> T2) :
    (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
    (∀ {x y}, Conv e1 x y -> Conv e2 (f x) (f y)) := by
  intro h; apply Conv.img
  intros x y h0
  specialize h h0
  apply Conv.one h

lemma Confluent.cr : Confluent e <-> CR e := by
  constructor
  . intro h1 x y h2
    induction h2 with
    | R =>
      exists x
      constructor <;> constructor
    | @SE y z _ r ih =>
      rcases ih with ⟨u, h2, h3⟩
      rcases h1 h3 (Star.one r) with ⟨v, h4, h5⟩
      exists v; constructor
      . apply Star.trans h2 h4
      . apply h5
    | @SEi y z _ r ih =>
      rcases ih with ⟨u, h2, h3⟩
      exists u; constructor
      . apply h2
      . apply Star.ES r h3
  . intro h x y z  h1 h2
    have h1 := Star.Conv h1
    have h2 := Star.Conv h2
    apply h
    apply Conv.trans (Conv.sym h1) h2

lemma Com.strip {e1 e2 : Rel T} : Com e1 e2 -> Com (Star e2) e1 := by
  intros h1 x y z h2
  induction h2 with
  | R =>
    intro h2
    exists z
    constructor
    . assumption
    . constructor
  | SE _ r2 ih =>
    intro h2
    have ⟨u, r1, s1⟩ := ih h2
    have ⟨v, r2, r1⟩ := h1 r1 r2
    exists v; constructor
    . assumption
    . apply Star.SE s1 r2

lemma Com.lift {e1 e2 : Rel T} : Com e1 e2 -> Com (Star e1) (Star e2) := by
  intro h
  have h := @Com.strip _ e1 e2 h
  have h := @Com.strip _ (Star e2) e1 h
  assumption

lemma Diamond.confluent : Diamond e -> Confluent e := by
  apply Com.lift

lemma SN.preimage {x} (f : T -> T) :
    (∀ x y, e x y -> e (f x) (f y)) -> SN e (f x) -> SN e x := by
  generalize e: f x = fx
  intro h1 sn
  induction sn generalizing f x h1
  case intro h2 ih =>
    subst_vars
    constructor; intro y r
    apply ih
    . apply h1 _ _ r
    . rfl
    . apply h1

lemma Normal.star {x y} : Star e x y -> Normal e x -> x = y := by
  intro h1 h2
  induction h1 with
  | R => rfl
  | @SE x y h3 r e =>
    subst_vars; exfalso
    apply h2
    exists y

lemma CR.star_normal {x y} (cr : CR e) : Conv e x y -> Normal e y -> Star e x y := by
  intro cxy ny
  have ⟨z, rxz, ryz⟩ := cr cxy
  rw[Normal.star ryz ny]
  exact rxz

lemma CR.conv_normal {x y} (cr : CR e) : Conv e x y -> Normal e x -> Normal e y -> x = y := by
  intro cxy nx ny
  have ⟨z, rxz, ryz⟩ := cr cxy
  rw[Normal.star rxz nx]
  rw[Normal.star ryz ny]
end Lemmas
