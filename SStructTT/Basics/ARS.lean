import Mathlib.Tactic

namespace ARS
section Definitions
set_option quotPrecheck false
notation:70 e1:70 " <=2 " e2:70 => (∀ {x y}, e1 x y -> e2 x y)

abbrev Pred (T : Type) := T -> Prop
abbrev Rel (T : Type) := T -> Pred T

variable {T : Type} (e : Rel T)

inductive Star (x : T) : T -> Prop where
  | R : Star x x
  | SE {y z} : Star x y -> e y z -> Star x z

inductive Star1 (x : T) : T -> Prop where
  | E  {y} :  e x y -> Star1 x y
  | SE {y z} : Star1 x y -> e y z -> Star1 x z

inductive Conv (x : T) : T -> Prop where
  | R : Conv x x
  | SE  {y z} : Conv x y -> e y z -> Conv x z
  | SEi {y z} : Conv x y -> e z y -> Conv x z

attribute [aesop safe] Star.R Star1.E Conv.R

def Com (R S : Rel T) := ∀ {x y z}, R x y -> S x z -> ∃ u, S y u ∧ R z u
def Union (R S : Rel T) : Rel T := fun x y => R x y ∨ S x y
def Joinable (R : Rel T) x y := ∃ z, R x z ∧ R y z
def Diamond := ∀ {x y z}, e x y -> e x z -> ∃ u, e y u ∧ e z u
def Confluent := ∀ {x y z}, Star e x y -> Star e x z -> Joinable (Star e) y z
def CR := ∀ {x y}, Conv e x y -> Joinable (Star e) x y

def Reducible (x : T) := ∃ y, e x y
def Normal (x : T) := ¬ Reducible e x
def NF (x y : T) := Star e x y ∧ Normal e y
def WN (x : T) := ∃ y, NF e x y

inductive SN : T -> Prop where
  | intro {x} : (∀ {y}, e x y -> SN y) -> SN x
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

lemma Star.ES_split {x z} :
    Star e x z -> x = z ∨ ∃ y, e x y ∧ Star e y z := by
  intro rd; induction rd
  case R => left; rfl
  case SE a b rd st ih =>
    match ih with
    | .inl e => subst_vars; right; existsi b; aesop
    | .inr ⟨x, _, rd⟩ =>
      right; existsi x; and_intros
      . assumption
      . apply Star.SE rd st

lemma Star.conv {x y} : Star e x y -> Conv e x y := by
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

lemma Star.subrelation {e1 e2 : Rel T} :
    Subrelation e1 e2 -> Subrelation (Star e1) (Star e2) := by
  intro h x y rd
  induction rd
  case R => constructor
  case SE st ih =>
    apply Star.SE ih (h st)

lemma Star1.trans {y x z} : Star1 e x y -> Star1 e y z -> Star1 e x z := by
  intros h1 h2
  induction h2 with
  | E => apply Star1.SE <;> assumption
  | SE => apply Star1.SE <;> assumption

lemma Star1.ES {y x z} : e x y -> Star1 e y z -> Star1 e x z := by
  intro h
  apply Star1.trans
  apply Star1.E
  assumption

lemma Star1.conv {x y} : Star1 e x y -> Conv e x y := by
  intro h
  induction h with
  | E h => apply Conv.SE Conv.R h
  | SE _ rel ih => apply Conv.SE ih rel

lemma Star1.img {T1 T2 e1 e2} {f : T1 -> T2} :
    (∀ {x y}, e1 x y -> Star1 e2 (f x) (f y)) ->
    (∀ {x y}, Star1 e1 x y -> Star1 e2 (f x) (f y)) := by
  intros h1 x y h2
  induction h2 with
  | E => aesop
  | @SE y z _ rel ih => apply Star1.trans ih (h1 rel)

lemma Star1.hom {T1 T2 e1 e2} (f : T1 -> T2) :
    (∀ {x y}, e1 x y -> e2 (f x) (f y)) ->
    (∀ {x y}, Star1 e1 x y -> Star1 e2 (f x) (f y)) := by
  intro h; apply Star1.img
  intros x y h0
  specialize h h0
  apply Star1.E h

lemma Star1.closure {e1 e2 : Rel T} : e1 <=2 Star1 e2 -> Star1 e1 <=2 Star1 e2 := by
  apply Star1.img

lemma Star1.monotone {e1 e2 : Rel T} : e1 <=2 e2 -> Star1 e1 <=2 Star1 e2 := by
  intro h1; apply Star1.closure
  intros x y h2
  specialize h1 h2
  apply Star1.E h1

lemma Star1.subrelation {e1 e2 : Rel T} :
    Subrelation e1 e2 -> Subrelation (Star1 e1) (Star1 e2) := by
  intro h x y rd
  induction rd
  case E => constructor; aesop
  case SE st ih =>
    apply Star1.SE ih (h st)

lemma Star1.toStar {x y} :
    Star1 e x y -> Star e x y := by
  intro rd; induction rd
  case E => apply Star.one; assumption
  case SE st ih => apply Star.SE ih st

lemma Star1.SE_join {x y z} :
    Star e x y -> e y z -> Star1 e x z := by
  intro rd st; induction rd generalizing z
  case R => constructor; assumption
  case SE st1 ih => apply Star1.SE (ih st1) st

lemma Star1.ES_join {x y z} :
    e x y -> Star e y z -> Star1 e x z := by
  intro st rd; induction rd generalizing x
  case R => constructor; assumption
  case SE st1 ih => apply Star1.SE (ih st) st1

lemma Star1.SE_split {x z} :
    Star1 e x z -> ∃ y, Star e x y ∧ e y z := by
  intro rd; induction rd
  case E y rd =>
    existsi x; and_intros
    apply Star.R
    assumption
  case SE a b rd st ih =>
    have ⟨y, rd, st⟩ := ih
    existsi a; and_intros
    . apply Star.SE rd st
    . assumption

lemma Star1.ES_split {x z} :
    Star1 e x z -> ∃ y, e x y ∧ Star e y z := by
  intro rd; induction rd
  case E y rd =>
    existsi y; and_intros
    assumption
    apply Star.R
  case SE a b rd st ih =>
    have ⟨y, _, rd⟩ := ih
    existsi y; and_intros
    . assumption
    . apply Star.SE rd st


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
  apply Star.conv h1
  apply Conv.sym
  apply Star.conv h2

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
      existsi x
      constructor <;> constructor
    | @SE y z _ r ih =>
      have ⟨u, h2, h3⟩ := ih
      have ⟨v, h4, h5⟩ := h1 h3 (Star.one r)
      existsi v; constructor
      . apply Star.trans h2 h4
      . apply h5
    | @SEi y z _ r ih =>
      have ⟨u, h2, h3⟩ := ih
      existsi u; constructor
      . apply h2
      . apply Star.ES r h3
  . intro h x y z  h1 h2
    have h1 := Star.conv h1
    have h2 := Star.conv h2
    apply h
    apply Conv.trans (Conv.sym h1) h2

lemma Com.strip {e1 e2 : Rel T} : Com e1 e2 -> Com (Star e2) e1 := by
  intros h1 x y z h2
  induction h2 with
  | R =>
    intro h2
    existsi z
    constructor
    . assumption
    . constructor
  | SE _ r2 ih =>
    intro h2
    have ⟨u, r1, s1⟩ := ih h2
    have ⟨v, r2, r1⟩ := h1 r1 r2
    existsi v; constructor
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

lemma SN.negate {x} :
    ¬SN e x -> ∃ y, e x y ∧ ¬SN e y := by
  intro sn; by_contra h
  simp at h; apply sn
  constructor; assumption

lemma SN.ofAcc {x} : Acc (flip e) x -> SN e x := by
  intro acc; induction acc
  constructor
  assumption

lemma SN.star1 {x} : SN e x -> SN (Star1 e) x := by
  intro sn; induction sn
  case intro h ih =>
    constructor
    intro y rd
    induction rd
    case a.E =>
      apply ih; assumption
    case a.SE st ih =>
      have ⟨h⟩ := ih
      apply h
      apply Star1.E st

lemma SN.wn {x} : SN e x -> WN e x := by
  intro sn; induction sn
  case intro x h ih =>
    by_cases h0 : Reducible e x
    case pos =>
      rcases h0 with ⟨y, h1⟩
      have ⟨z, ⟨h2, h3⟩⟩ := ih h1
      existsi z; and_intros
      . apply Star.ES h1 h2
      . apply h3
    case neg =>
      existsi x; and_intros
      . apply Star.R
      . apply h0

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
