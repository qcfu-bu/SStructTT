import Mathlib.Tactic
import SStructTT.Attr.Register

-------------------------------------------------------------------------------------------------

section Definitions
abbrev Var := Nat
@[reducible]def Binder (T : Type) : Type := T

class Ids (T : Type) where
  ids : Var -> T

class Rename (T : Type) where
  rename : (Var -> Var) -> T -> T

class Subst (T : Type) where
  subst : (Var -> T) -> T -> T

export Ids (ids)
export Rename (rename)
export Subst (subst)

variable {T : Type}

def scons (s : T) (σ : Var -> T) : Var -> T
  | 0 => s
  | x+1 => σ x

@[asimp]def funcomp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x)

def scomp [Subst T] (f g : Var -> T) : Var -> T :=
  funcomp f (subst g)

infixl:56 " !>> " => funcomp
infixl:56 " >> " => scomp
infixr:55 " .: " => scons
notation:max s:2 ".[" σ:2 "]" => subst σ s
syntax:max term:2 ".[" (term:2),+ "/]" : term
macro_rules
| `($m:term .[ $[$ns:term],* /]) => do
  let σ <- ns.foldrM (fun n acc => `($n .: $acc)) (<-`(ids))
  `(subst $σ $m)

def ren [Ids T] (ξ : Var -> Var) : Var -> T :=
  ξ !>> ids

def upren (ξ : Var -> Var) : Var -> Var :=
  0 .: ξ !>> .succ

def up [Ids T] [Rename T] (σ : Var -> T) : Var -> T :=
  ids 0 .: (σ !>> rename .succ)

def upn [Ids T] [Rename T] (n : Var) : (Var -> T) -> Var -> T :=
  n.repeat up

@[asimp]lemma scomp_0 [Subst T] (f g : Var -> T) (x : Var) :
  (f >> g) x = (f x).[g] := by rfl

@[asimp]lemma scons_0 (s : T) (σ : Var -> T) : (s .: σ) 0 = s := by rfl
@[asimp]lemma scons_1 (s : T) (σ : Var -> T) (x : Var) : (s .: σ) x.succ = σ x := by rfl

@[asimp]lemma ren_x  [Ids T] (x : Var) (ξ : Var -> Var) : ren ξ x = @ids T _ (ξ x) := by rfl
@[asimp]lemma ren_id [Ids T] : ren id = @ids T _ := by rfl

@[asimp]lemma upren_0 (ξ : Var -> Var) : upren ξ 0 = 0 := by rfl
@[asimp]lemma upren_1 (ξ : Var -> Var) n : upren ξ (n.succ) = (ξ !>> .succ) n := by simp[upren, scons]
@[asimp]lemma upren_id : upren id = id := by
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[asimp]

@[asimp]lemma up0 [Ids T] [Rename T] (σ : Var -> T) : up σ 0 = ids 0 := by rfl
@[asimp]lemma up1 [Ids T] [Rename T] (σ : Var -> T) n : up σ (n.succ) = rename .succ (σ n) := by rfl

@[asimp]lemma upn0 {T} [Ids T] [Rename T] (σ : Var -> T) : upn 0 σ = σ := by rfl
@[asimp]lemma upn1 {T} [Ids T] [Rename T] (n : Var) σ : @upn T _ _ (n.succ) σ = up (upn n σ) := by
  simp[upn, Nat.repeat]

@[asimp]lemma id_comp {A B} (f : A -> B) : id !>> f = f := by rfl
@[asimp]lemma comp_id {A B} (f : A -> B) : f !>> id = f := by rfl
@[asimp]lemma comp_assoc {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  (f !>> g) !>> h = f !>> (g !>> h) := by rfl

@[asimp]lemma lift0 : (.+0) = id := by rfl
@[asimp]lemma lift_scons x (f : Var -> T) (n : Var) : (.+n.succ) !>> (x .: f) = (.+n) !>> f := by
  funext x0; simp[scons, asimp]
section Definitions

-------------------------------------------------------------------------------------------------

class SubstLemmas (T : Type) [Ids T] [Rename T] [Subst T] where
  rename_subst (ξ : Var -> Var) (m : T) : rename ξ m = m.[ren ξ]
  subst_id (m : T) : m.[ids] = m
  id_subst (σ : Var -> T) (x : Var) : (ids x).[σ] = σ x
  subst_comp (σ τ : Var -> T) (s : T) : s.[σ].[τ] = s.[σ >> τ]

namespace Lemmas
set_option linter.unusedSectionVars false
variable {T : Type} [Ids T] [Rename T] [Subst T] [lemmas: SubstLemmas T]

@[asimp]def rename_subst := lemmas.rename_subst
@[asimp]def subst_id     := lemmas.subst_id
@[asimp]def id_subst     := lemmas.id_subst
@[asimp]def subst_comp   := lemmas.subst_comp

@[asimp]lemma up_shift (σ : Var -> T) : up σ = ids 0 .: (σ >> ren .succ) := by
  simp[up, asimp]
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[scomp, asimp]

@[asimp]lemma upren_up (ξ : Var -> Var) : @ren T _ (upren ξ) = up (ren ξ) := by
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[scomp, asimp]

@[asimp]lemma ids_comp (σ : Var -> T) : ids >> σ = σ := by
  funext x
  simp[scomp, asimp]

@[asimp]lemma ids_shift : (@ids T _ 0) .: ren .succ = ids := by
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[scons, ren, funcomp]

@[asimp]lemma shift_scomp (m : T) (σ : Var -> T) : ren .succ >> (m .: σ) = σ := by
  funext x
  simp[scomp, ren, asimp]

@[asimp]lemma ids0_scons (σ : Var -> T) : (ids 0).[σ] .: (ren .succ >> σ) = σ := by
  funext x
  simp[scons]
  cases x with
  | zero => simp[asimp]
  | succ => simp[scomp, ren, asimp]

@[asimp]lemma comp_ids (σ : Var -> T) : σ >> ids = σ := by
  funext x
  simp[scomp, funcomp, asimp]

@[asimp]lemma scons_scomp m (σ τ : Var -> T) : (m .: σ) >> τ = m.[τ] .: σ >> τ := by
  funext x
  cases x with
  | zero => simp[scomp, funcomp, scons]
  | succ => simp[scomp, funcomp, scons]

@[asimp]lemma scomp_assoc (σ τ θ : Var -> T) : (σ >> τ) >> θ = σ >> (τ >> θ) := by
  funext x
  simp[scomp, funcomp, asimp]

open Lean Parser Tactic in
syntax "asimp"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic

macro_rules
| `(tactic| asimp $[$loc]?) =>
  `(tactic| simp[asimp] $[$loc]?; repeat rw [<-up_shift] $[$loc]?)
| `(tactic| asimp[$xs,*] $[$loc]?) =>
  `(tactic| simp[$xs,*, asimp] $[$loc]?; repeat rw [<-up_shift] $[$loc]?)
end Lemmas
