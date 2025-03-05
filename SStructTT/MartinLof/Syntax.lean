import SStructTT.Basics.Subst

namespace MartinLof

inductive Tm where
  | var  (x : Var)
  | ty   (i : Nat)
  | pi   (A B : Tm)
  | lam  (A m : Tm)
  | app  (m n : Tm)
  | sig  (A B : Tm)
  | tup  (m n : Tm)
  | proj (A m n : Tm)
  | bool | tt | ff
  | ite  (A m n1 n2 : Tm)
  | idn  (A m n : Tm)
  | rfl  (m : Tm)
  | rw   (A m n : Tm)

namespace Tm
instance : Ids Tm where
  ids := var

@[asimp]lemma ids_var x : var x = ids x := by rfl

def rename_rec (ξ : Var -> Var) (m : Tm) : Tm :=
  match m with
  | var x => var (ξ x)
  | ty i => ty i
  | pi A B => pi (rename_rec ξ A) (rename_rec (upren ξ) B)
  | lam A m => lam (rename_rec ξ A) (rename_rec (upren ξ) m)
  | app m n => app (rename_rec ξ m) (rename_rec ξ n)
  | sig A B => sig (rename_rec ξ A) (rename_rec (upren ξ) B)
  | tup m n => tup (rename_rec ξ m) (rename_rec ξ n)
  | proj A m n => proj (rename_rec (upren ξ) A) (rename_rec ξ m) (rename_rec (upren $ upren ξ) n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ite A m n1 n2 => ite (rename_rec (upren ξ) A) (rename_rec ξ m) (rename_rec ξ n1) (rename_rec ξ n2)
  | idn A m n => idn (rename_rec ξ A) (rename_rec ξ m) (rename_rec ξ n)
  | rfl m => rfl (rename_rec ξ m)
  | rw A m n => rw (rename_rec (upren (upren ξ)) A) (rename_rec ξ m) (rename_rec ξ n)

@[irreducible]instance : Rename Tm where
  rename := rename_rec

namespace Rename
variable (ξ : Var -> Var) (A B m n n1 n2 : Tm) (x i : Nat)

@[asimp]lemma ids  : rename ξ (ids x) = @ids Tm _ (ξ x) := by rfl
@[asimp]lemma ty   : rename ξ (ty i) = ty i := by rfl
@[asimp]lemma pi   : rename ξ (pi A B) = pi (rename ξ A) (rename (upren ξ) B) := by rfl
@[asimp]lemma lam  : rename ξ (lam A m) = lam (rename ξ A) (rename (upren ξ) m) := by rfl
@[asimp]lemma app  : rename ξ (app m n) = app (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma sig1 : rename ξ (sig A B) = sig (rename ξ A) (rename (upren ξ) B) := by rfl
@[asimp]lemma tup1 : rename ξ (tup m n) = tup (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma proj : rename ξ (proj A m n) = proj (rename (upren ξ) A) (rename ξ m) (rename (upren $ upren ξ) n) := by rfl
@[asimp]lemma bool : rename ξ bool = bool := by rfl
@[asimp]lemma tt   : rename ξ tt = tt := by rfl
@[asimp]lemma ff   : rename ξ ff = ff := by rfl
@[asimp]lemma ite  : rename ξ (ite A m n1 n2) = ite (rename (upren ξ) A) (rename ξ m) (rename ξ n1) (rename ξ n2) := by rfl
@[asimp]lemma idn  : rename ξ (idn A m n) = idn (rename ξ A) (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma rfl  : rename ξ (rfl m) = rfl (rename ξ m) := by rfl
@[asimp]lemma rw   : rename ξ (rw A m n) = rw (rename (upren $ upren ξ) A) (rename ξ m) (rename ξ n) := by rfl
end Rename

def subst_rec (σ : Var -> Tm) (m : Tm) : Tm :=
  match m with
  | var x => σ x
  | ty i => ty i
  | pi A B => pi (subst_rec σ A) (subst_rec (up σ) B)
  | lam A m => lam (subst_rec σ A) (subst_rec (up σ) m)
  | app m n => app (subst_rec σ m) (subst_rec σ n)
  | sig A B => sig (subst_rec σ A) (subst_rec (up σ) B)
  | tup m n => tup (subst_rec σ m) (subst_rec σ n)
  | proj A m n => proj (subst_rec (up σ) A) (subst_rec σ m) (subst_rec (upn 2 σ) n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ite A m n1 n2 => ite (subst_rec (up σ) A) (subst_rec σ m) (subst_rec σ n1) (subst_rec σ n2)
  | idn A m n => idn (subst_rec σ A) (subst_rec σ m) (subst_rec σ n)
  | rfl m => rfl (subst_rec σ m)
  | rw A m n => rw (subst_rec (upn 2 σ) A) (subst_rec σ m) (subst_rec σ n)

@[irreducible]instance : Subst Tm where
  subst := subst_rec

namespace Subst
variable (σ : Var -> Tm) (A B m n n1 n2 : Tm) (x i : Nat)

@[asimp]lemma ids  : subst σ (ids x) = σ x := by rfl
@[asimp]lemma ty   : subst σ (ty i) = ty i := by rfl
@[asimp]lemma pi   : subst σ (pi A B) = pi (subst σ A) (subst (up σ) B) := by rfl
@[asimp]lemma lam  : subst σ (lam A m) = lam (subst σ A) (subst (up σ) m) := by rfl
@[asimp]lemma app  : subst σ (app m n) = app (subst σ m) (subst σ n) := by rfl
@[asimp]lemma sig  : subst σ (sig A B) = sig (subst σ A) (subst (up σ) B) := by rfl
@[asimp]lemma tup  : subst σ (tup m n) = tup (subst σ m) (subst σ n) := by rfl
@[asimp]lemma proj : subst σ (proj A m n) = proj (subst (up σ) A) (subst σ m) (subst (upn 2 σ) n) := by rfl
@[asimp]lemma bool : subst σ bool = bool := by rfl
@[asimp]lemma tt   : subst σ tt = tt := by rfl
@[asimp]lemma ff   : subst σ ff = ff := by rfl
@[asimp]lemma ite  : subst σ (ite A m n1 n2) = ite (subst (up σ) A) (subst σ m) (subst σ n1) (subst σ n2) := by rfl
@[asimp]lemma idn  : subst σ (idn A m n) = idn (subst σ A) (subst σ m) (subst σ n) := by rfl
@[asimp]lemma rfl  : subst σ (rfl m) = rfl (subst σ m) := by rfl
@[asimp]lemma rw   : subst σ (rw A m n) = rw (subst (upn 2 σ) A) (subst σ m) (subst σ n) := by rfl
end Subst

section SubstLemmas
lemma up_upren (ξ : Var -> Var) :
  @up Tm _ _ (ren ξ) = ren (upren ξ) := by
  funext x; cases x <;> asimp

lemma rename_subst ξ (m : Tm) : rename ξ m = m.[ren ξ] := by
  induction m generalizing ξ with
  | var => asimp
  | ty => asimp
  | pi A B ihA ihB => asimp[up_upren, ihA, ihB]
  | lam A m ihA ihm => asimp[up_upren, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B ihA ihB => asimp[up_upren, ihA, ihB]
  | tup m n ihm ihn => asimp[ihm, ihn]
  | proj A m n ihA ihm ihn => asimp[up_upren, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_upren, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_upren, ihA, ihm, ihn]

lemma up_ids : up ids = @ids Tm _ := by
  funext x
  cases x with
  | zero => asimp
  | succ => asimp

lemma subst_id (m : Tm) : m.[ids] = m := by
  induction m with
  | var => asimp
  | ty => asimp
  | pi A B ihA ihB => asimp[up_ids, ihA, ihB]
  | lam A m ihA ihm => asimp[up_ids, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B ihA ihB => asimp[up_ids, ihA, ihB]
  | tup m n ihm ihn => asimp[ihm, ihn]
  | proj A m n ihA ihm ihn => asimp[up_ids, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_ids, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_ids, ihA, ihm, ihn]

lemma up_comp_upren (ξ : Var -> Var) (σ : Var -> Tm) :
  up (ξ !>> σ) = upren ξ !>> up σ := by
  funext x
  cases x with
  | zero => rfl
  | succ => asimp

lemma ren_subst_comp ξ σ (m : Tm) : m.[ren ξ].[σ] = m.[ξ !>> σ] := by
  induction m generalizing ξ σ with
  | var => asimp
  | ty => asimp
  | pi A B ihA ihB => asimp[up_upren, up_comp_upren, ihA, ihB]
  | lam A m ihA ihm => asimp[up_upren, up_comp_upren, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B ihA ihB => asimp[up_upren, up_comp_upren, ihA, ihB]
  | tup m n ihm ihn => asimp[ihm, ihn]
  | proj A m n ihA ihm ihn => asimp[up_upren, up_comp_upren, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_upren, up_comp_upren, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_upren, up_comp_upren, ihA, ihm, ihn]

lemma up_comp_ren (σ : Var -> Tm) (ξ : Var -> Var) :
    up σ !>> rename (upren ξ) = up (σ !>> rename ξ)  := by
  funext x
  cases x with
  | zero => asimp
  | succ n =>
    asimp[rename_subst]
    have h1 := ren_subst_comp (.+1) (ren (upren ξ)) (σ n); asimp at h1
    have h2 := ren_subst_comp ξ (shift 1) (σ n); asimp at h2
    rw[h1, h2]; rfl

lemma subst_ren_comp σ ξ (m : Tm) : m.[σ].[ren ξ] = m.[σ !>> rename ξ] := by
  induction m generalizing σ ξ with
  | var => asimp[rename_subst]
  | ty => asimp
  | pi A B ihA ihB => asimp[up_upren, up_comp_ren, ihA, ihB]
  | lam A m ihA ihm => asimp[up_upren, up_comp_ren, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B ihA ihB => asimp[up_upren, up_comp_ren, ihA, ihB]
  | tup m n ihm ihn => asimp[ihm, ihn]
  | proj A m n ihA ihm ihn => asimp[up_upren, up_comp_ren, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_upren, up_comp_ren, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_upren, up_comp_ren, ihA, ihm, ihn]

lemma up_comp (σ τ : Var -> Tm) :  up σ !> up τ = up (σ !> τ) := by
  funext x
  cases x with
  | zero => asimp
  | succ n =>
    asimp[rename_subst]
    have h1 := subst_ren_comp τ (.+1) (σ n)
    have h2 := ren_subst_comp (.+1) (up τ) (σ n)
    rw[h1, h2]
    rfl

lemma subst_comp (σ τ : Var -> Tm) m : m.[σ].[τ] = m.[σ !> τ] := by
  induction m generalizing σ τ with
  | var => asimp
  | ty => asimp
  | pi A B ihA ihB => asimp[up_comp, ihA, ihB]
  | lam A m ihA ihm => asimp[up_comp, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B ihA ihB => asimp[up_comp, ihA, ihB]
  | tup m n ihm ihn => asimp[ihm, ihn]
  | proj A m n ihA ihm ihn => asimp[up_comp, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_comp, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_comp, ihA, ihm, ihn]

instance : SubstLemmas Tm where
  rename_subst := rename_subst
  subst_id := subst_id
  id_subst := by intros; asimp
  subst_comp := subst_comp
end SubstLemmas
end Tm
