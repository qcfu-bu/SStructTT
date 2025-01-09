import Mathlib.Tactic
import SStructTT.Util.Attr
import SStructTT.Util.Tactics

-------------------------------------------------------------------------------------------------

section Definitions
abbrev Var := Nat
abbrev Binder (T : Type) : Type := T

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

@[asimp]def fcomp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x)

def scomp [Subst T] (f g : Var -> T) : Var -> T :=
  fcomp f (subst g)

section Notations
open Lean PrettyPrinter

syntax:60 term:60 " !>> " term:61 : term
syntax:60 term:60 " !> " term:61 : term
syntax:60 term:61 " .: " term:60 : term
syntax:max term:2 ".[" term:2 "]" : term
syntax:max term:2 ".[" (term:2),+ "/]" : term
macro_rules
  | `($f:term !>> $g:term) => `(fcomp $f $g)
  | `($σ:term !> $τ:term) => `(scomp $σ $τ)
  | `($m:term .: $σ:term) => `(scons $m $σ)
  | `($m:term .[ $σ:term ]) => `(subst $σ $m)
  | `($m:term .[ $[$ns:term],* /]) => do
    let σ <- ns.foldrM (fun n acc => `($n .: $acc)) (<-`(ids))
    `(subst $σ $m)

@[app_unexpander fcomp]
def unexpandFComp : Unexpander
  | `($(_) $f:term $g:term) => `($f !>> $g)
  | _ => throw ()

@[app_unexpander scomp]
def unexpandSComp : Unexpander
  | `($(_) $σ:term $τ:term) => `($σ !> $τ)
  | _ => throw ()

@[app_unexpander scons]
def unexpandSCons : Unexpander
  | `($(_) $m:term $σ:term) => `($m .: $σ)
  | _ => throw ()

@[app_unexpander subst]
partial def unexpandSubst : Unexpander
  | `($(_) $σ:term $m:term) =>
    let rec gather : TSyntax `term -> Option (List (TSyntax `term))
      | `($n:term .: ids) => [n]
      | `($n:term .: $σ:term) => do
        return (n :: (<-gather σ))
      | _ => none
    match gather σ with
    | some ns => let ns := ns.toArray; `($m.[$ns,*/])
    | _ => `($m.[$σ])
  | _ => throw ()
end Notations

def ren [Ids T] (ξ : Var -> Var) : Var -> T :=
  ξ !>> ids

def upren (ξ : Var -> Var) : Var -> Var :=
  0 .: ξ !>> (.+1)

def up [Ids T] [Rename T] (σ : Var -> T) : Var -> T :=
  ids 0 .: (σ !>> rename (.+1))

def upn [Ids T] [Rename T] (n : Var) : (Var -> T) -> Var -> T :=
  n.repeat up

abbrev shift [Ids T] n := @ren T _ (. + n)

@[asimp]lemma scomp_0 [Subst T] (f g : Var -> T) (x : Var) :
  (f !> g) x = (f x).[g] := by rfl

@[asimp]lemma scons_0 (s : T) (σ : Var -> T) : (s .: σ) 0 = s := by rfl
@[asimp]lemma scons_1 (s : T) (σ : Var -> T) (x : Var) : (s .: σ) (x + 1) = σ x := by rfl

@[asimp]lemma ren_x  [Ids T] (x : Var) (ξ : Var -> Var) : ren ξ x = @ids T _ (ξ x) := by rfl
@[asimp]lemma ren_id [Ids T] : ren id = @ids T _ := by rfl

@[asimp]lemma upren_0 (ξ : Var -> Var) : upren ξ 0 = 0 := by rfl
@[asimp]lemma upren_1 (ξ : Var -> Var) n : upren ξ (n+1) = (ξ !>> (.+1)) n := by simp[upren, scons]
@[asimp]lemma upren_id : upren id = id := by
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[asimp]

@[asimp]lemma up0 [Ids T] [Rename T] (σ : Var -> T) : up σ 0 = ids 0 := by rfl
@[asimp]lemma up1 [Ids T] [Rename T] (σ : Var -> T) n : up σ (n + 1) = rename (.+1) (σ n) := by rfl

@[asimp]lemma upn0 {T} [Ids T] [Rename T] (σ : Var -> T) : upn 0 σ = σ := by rfl
@[asimp]lemma upn1 {T} [Ids T] [Rename T] (n : Var) σ : @upn T _ _ (n + 1) σ = up (upn n σ) := by
  simp[upn, Nat.repeat]

@[asimp]lemma id_comp {A B} (f : A -> B) : id !>> f = f := by rfl
@[asimp]lemma comp_id {A B} (f : A -> B) : f !>> id = f := by rfl
@[asimp]lemma comp_assoc {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  (f !>> g) !>> h = f !>> (g !>> h) := by rfl

@[asimp]lemma lift0 : (.+0) = id := by rfl
@[asimp]lemma lift_scons x (f : Var -> T) (n : Var) : (.+(n + 1)) !>> (x .: f) = (.+n) !>> f := by
  funext x0; simp[scons, asimp]
section Definitions

-------------------------------------------------------------------------------------------------

class SubstLemmas (T : Type) [Ids T] [Rename T] [Subst T] where
  rename_subst (ξ : Var -> Var) (m : T) : rename ξ m = m.[ren ξ]
  subst_id (m : T) : m.[ids] = m
  id_subst (σ : Var -> T) (x : Var) : (ids x).[σ] = σ x
  subst_comp (σ τ : Var -> T) (s : T) : s.[σ].[τ] = s.[σ !> τ]

namespace SubstLemmas
set_option linter.unusedSectionVars false
variable {T : Type} [Ids T] [Rename T] [Subst T] [SubstLemmas T]

attribute [asimp] rename_subst subst_id id_subst subst_comp

@[asimp]lemma up_shift (σ : Var -> T) : up σ = ids 0 .: (σ !> shift 1) := by
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

@[asimp]lemma ids_comp (σ : Var -> T) : ids !> σ = σ := by
  funext x
  simp[scomp, asimp]

@[asimp]lemma ids_shift : (@ids T _ 0) .: shift 1 = ids := by
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[scons, ren, fcomp]

@[asimp]lemma shift_scomp (m : T) (σ : Var -> T) : shift 1 !> (m .: σ) = σ := by
  funext x
  simp[scomp, ren, asimp]

@[asimp]lemma ids0_scons (σ : Var -> T) : (ids 0).[σ] .: (shift 1 !> σ) = σ := by
  funext x
  simp[scons]
  cases x with
  | zero => simp[asimp]
  | succ => simp[scomp, ren, asimp]

@[asimp]lemma comp_ids (σ : Var -> T) : σ !> ids = σ := by
  funext x
  simp[scomp, fcomp, asimp]

@[asimp]lemma scons_scomp m (σ τ : Var -> T) : (m .: σ) !> τ = m.[τ] .: σ !> τ := by
  funext x
  cases x with
  | zero => simp[scomp, fcomp, scons]
  | succ => simp[scomp, fcomp, scons]

@[asimp]lemma scomp_assoc (σ τ θ : Var -> T) : (σ !> τ) !> θ = σ !> (τ !> θ) := by
  funext x
  simp[scomp, fcomp, asimp]

@[asimp]lemma shift0 : @shift T _ 0 = ids := by rfl
@[asimp]lemma shift2 (n : Var) : @shift T _ (n + 2) = shift 1 !> shift 1 !> shift n := by
  funext x
  simp[asimp]
  congr 1; ring

section Tactics
open Lean Parser Tactic

@[asimp,fold1]lemma ids_n_shift (σ : Var -> T) n :
    ids (n + 1) .: σ !> shift 1 = ((ids n .: σ) !> shift 1) := by
  simp[asimp]

@[fold1]lemma shift_upn1 (σ : Var -> T) : ids 0 .: σ !> shift 1 = upn 1 σ := by
  simp[up, asimp]
  funext x
  cases x with
  | zero => simp[asimp]
  | succ => simp[scomp, asimp]

@[fold1]lemma upn_comp (σ : Var -> T) m n : upn m (upn n σ) = upn (m + n) σ := by
  induction m generalizing σ n with
  | zero => simp[asimp]
  | succ m ih =>
    simp[asimp]
    rw[ih,<-up_shift,<-upn1]
    rewrite m + n + 1 to m + 1 + n := by ring
    rfl

@[fold2]lemma upn1_up (σ : Var -> T) : upn 1 σ = up σ := by rfl

@[fold2]lemma shift_comp (m n : Var) : @shift T _ m !> shift n = shift (m + n) := by
  funext x
  simp[asimp]
  congr 1; ring

syntax "fold_up" (location)? : tactic
macro_rules
  | `(tactic| fold_up $[$loc]?) => do
    let fold1 <- `(tactic| try simp[<-scomp_assoc,fold1] $[$loc]?)
    let fold2 <- `(tactic| try simp[scomp_assoc,fold2] $[$loc]?)
    `(tactic| $fold1; $fold2)

syntax "fsimp" (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic
macro_rules
  | `(tactic| fsimp $[[$args,*]]? $[$loc]?) =>
    match args with
    | some args => `(tactic| simp[$args,*, asimp] $[$loc]?)
    | none => `(tactic| simp[asimp] $[$loc]?)

syntax "asimp" (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)? : tactic
macro_rules
  | `(tactic| asimp $[[$args,*]]? $[$loc]?) =>
    `(tactic| (try fsimp $[[$args,*]]? $[$loc]?); fold_up $[$loc]?)
end Tactics
end SubstLemmas
