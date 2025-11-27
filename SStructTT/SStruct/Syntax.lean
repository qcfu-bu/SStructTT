import SStructTT.Basics.Subst

namespace SStruct
-- Sorts
variable (Srt : Type)

inductive Rlv where
  | im | ex

inductive Tm where
  | var (x : Var)
  | srt (s : Srt) (i : Nat)
  | pi  (A B : Tm) (r : Rlv) (s : Srt)
  | lam (A m : Tm) (r : Rlv) (s : Srt)
  | app (m n : Tm)
  | sig (A B : Tm) (r : Rlv) (s : Srt)
  | tup (m n : Tm) (r : Rlv) (s : Srt)
  | prj (A m n : Tm)
  | bool | tt | ff
  | ite (A m n1 n2 : Tm)
  | idn (A m n : Tm)
  | rfl (m : Tm)
  | rw  (A m n : Tm)

namespace Tm
variable {Srt : Type}
instance : Ids (Tm Srt) where
  ids := var

@[asimp]lemma ids_var x : @var Srt x = ids x := by rfl

def rename_rec (ξ : Var -> Var) (m : Tm Srt) : Tm Srt :=
  match m with
  | var x => var (ξ x)
  | srt s i => srt s i
  | pi A B r s => pi (rename_rec ξ A) (rename_rec (upren ξ) B) r s
  | lam A m r s => lam (rename_rec ξ A) (rename_rec (upren ξ) m) r s
  | app m n => app (rename_rec ξ m) (rename_rec ξ n)
  | sig A B r s => sig (rename_rec ξ A) (rename_rec (upren ξ) B) r s
  | tup m n r s => tup (rename_rec ξ m) (rename_rec ξ n) r s
  | prj A m n => prj (rename_rec (upren ξ) A) (rename_rec ξ m) (rename_rec (upren $ upren ξ) n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ite A m n1 n2 => ite (rename_rec (upren ξ) A) (rename_rec ξ m) (rename_rec ξ n1) (rename_rec ξ n2)
  | idn A m n => idn (rename_rec ξ A) (rename_rec ξ m) (rename_rec ξ n)
  | rfl m => rfl (rename_rec ξ m)
  | rw A m n => rw (rename_rec (upren (upren ξ)) A) (rename_rec ξ m) (rename_rec ξ n)

instance : Rename (Tm Srt) where
  rename := rename_rec

namespace Rename
variable (ξ : Var -> Var) (A B m n n1 n2 : Tm Srt) (x i : Nat) (r : Rlv) (s : Srt)

@[asimp]lemma ids  : rename ξ (ids x) = @ids (Tm Srt) _ (ξ x) := by rfl
@[asimp]lemma srt  : rename ξ (srt s i) = srt s i := by rfl
@[asimp]lemma pi   : rename ξ (pi A B r s) = pi (rename ξ A) (rename (upren ξ) B) r s := by rfl
@[asimp]lemma lam  : rename ξ (lam A m r s) = lam (rename ξ A) (rename (upren ξ) m) r s := by rfl
@[asimp]lemma app  : rename ξ (app m n) = app (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma sig1 : rename ξ (sig A B r s) = sig (rename ξ A) (rename (upren ξ) B) r s := by rfl
@[asimp]lemma tup1 : rename ξ (tup m n r s) = tup (rename ξ m) (rename ξ n) r s := by rfl
@[asimp]lemma prj  : rename ξ (prj A m n) = prj (rename (upren ξ) A) (rename ξ m) (rename (upren $ upren ξ) n) := by rfl
@[asimp]lemma bool : rename ξ (@bool Srt) = bool := by rfl
@[asimp]lemma tt   : rename ξ (@tt Srt) = tt := by rfl
@[asimp]lemma ff   : rename ξ (@ff Srt) = ff := by rfl
@[asimp]lemma ite  : rename ξ (ite A m n1 n2) = ite (rename (upren ξ) A) (rename ξ m) (rename ξ n1) (rename ξ n2) := by rfl
@[asimp]lemma idn  : rename ξ (idn A m n) = idn (rename ξ A) (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma rfl  : rename ξ (rfl m) = rfl (rename ξ m) := by rfl
@[asimp]lemma rw   : rename ξ (rw A m n) = rw (rename (upren $ upren ξ) A) (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma rename_rec : rename_rec ξ m = rename ξ m := by rfl
end Rename

def subst_rec (σ : Var -> Tm Srt) (m : Tm Srt) : Tm Srt :=
  match m with
  | var x => σ x
  | srt s i => srt s i
  | pi A B r s => pi (subst_rec σ A) (subst_rec (up σ) B) r s
  | lam A m r s => lam (subst_rec σ A) (subst_rec (up σ) m) r s
  | app m n => app (subst_rec σ m) (subst_rec σ n)
  | sig A B r s => sig (subst_rec σ A) (subst_rec (up σ) B) r s
  | tup m n r s => tup (subst_rec σ m) (subst_rec σ n) r s
  | prj A m n => prj (subst_rec (up σ) A) (subst_rec σ m) (subst_rec (upn 2 σ) n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ite A m n1 n2 => ite (subst_rec (up σ) A) (subst_rec σ m) (subst_rec σ n1) (subst_rec σ n2)
  | idn A m n => idn (subst_rec σ A) (subst_rec σ m) (subst_rec σ n)
  | rfl m => rfl (subst_rec σ m)
  | rw A m n => rw (subst_rec (upn 2 σ) A) (subst_rec σ m) (subst_rec σ n)

instance : Subst (Tm Srt) where
  subst := subst_rec

namespace Subst
variable (σ : Var -> Tm Srt) (A B m n n1 n2 : Tm Srt) (x i : Nat) (r : Rlv) (s : Srt)

@[asimp]lemma ids  : subst σ (ids x) = σ x := by rfl
@[asimp]lemma srt  : subst σ (srt s i) = srt s i := by rfl
@[asimp]lemma pi   : subst σ (pi A B r s) = pi (subst σ A) (subst (up σ) B) r s := by rfl
@[asimp]lemma lam  : subst σ (lam A m r s) = lam (subst σ A) (subst (up σ) m) r s := by rfl
@[asimp]lemma app  : subst σ (app m n) = app (subst σ m) (subst σ n) := by rfl
@[asimp]lemma sig  : subst σ (sig A B r s) = sig (subst σ A) (subst (up σ) B) r s := by rfl
@[asimp]lemma tup  : subst σ (tup m n r s) = tup (subst σ m) (subst σ n) r s := by rfl
@[asimp]lemma prj  : subst σ (prj A m n) = prj (subst (up σ) A) (subst σ m) (subst (upn 2 σ) n) := by rfl
@[asimp]lemma bool : subst σ (@bool Srt) = bool := by rfl
@[asimp]lemma tt   : subst σ (@tt Srt) = tt := by rfl
@[asimp]lemma ff   : subst σ (@ff Srt) = ff := by rfl
@[asimp]lemma ite  : subst σ (ite A m n1 n2) = ite (subst (up σ) A) (subst σ m) (subst σ n1) (subst σ n2) := by rfl
@[asimp]lemma idn  : subst σ (idn A m n) = idn (subst σ A) (subst σ m) (subst σ n) := by rfl
@[asimp]lemma rfl  : subst σ (rfl m) = rfl (subst σ m) := by rfl
@[asimp]lemma rw   : subst σ (rw A m n) = rw (subst (upn 2 σ) A) (subst σ m) (subst σ n) := by rfl
@[asimp]lemma subst_rec : subst_rec σ m = subst σ m := by rfl
end Subst

section SubstLemmas
lemma up_upren (ξ : Var -> Var) :
    @up (Tm Srt) _ _ (ren ξ) = ren (upren ξ) := by
  funext x; cases x <;> asimp

lemma rename_subst ξ (m : Tm Srt) : rename ξ m = m.[ren ξ] := by
  induction m generalizing ξ with
  | var => asimp
  | srt => asimp
  | pi A B r s ihA ihB => asimp[up_upren, ihA, ihB]
  | lam A m r s ihA ihm => asimp[up_upren, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B r s ihA ihB => asimp[up_upren, ihA, ihB]
  | tup m n r s ihm ihn => asimp[ihm, ihn]
  | prj A m n ihA ihm ihn => asimp[up_upren, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_upren, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_upren, ihA, ihm, ihn]

lemma up_ids : up ids = @ids (Tm Srt) _ := by
  funext x
  cases x with
  | zero => asimp
  | succ => asimp

lemma subst_id (m : Tm Srt) : m.[ids] = m := by
  induction m with
  | var => asimp
  | srt => asimp
  | pi A B r s ihA ihB => asimp[up_ids, ihA, ihB]
  | lam A m r s ihA ihm => asimp[up_ids, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B r s ihA ihB => asimp[up_ids, ihA, ihB]
  | tup m n r s ihm ihn => asimp[ihm, ihn]
  | prj A m n ihA ihm ihn => asimp[up_ids, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_ids, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_ids, ihA, ihm, ihn]

lemma up_comp_upren (ξ : Var -> Var) (σ : Var -> Tm Srt) :
    up (ξ !>> σ) = upren ξ !>> up σ := by
  funext x
  cases x with
  | zero => rfl
  | succ => asimp

lemma ren_subst_comp ξ σ (m : Tm Srt) : m.[ren ξ].[σ] = m.[ξ !>> σ] := by
  induction m generalizing ξ σ with
  | var => asimp
  | srt => asimp
  | pi A B r s ihA ihB => asimp[up_upren, up_comp_upren, ihA, ihB]
  | lam A m r s ihA ihm => asimp[up_upren, up_comp_upren, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B r s ihA ihB => asimp[up_upren, up_comp_upren, ihA, ihB]
  | tup m n r s ihm ihn => asimp[ihm, ihn]
  | prj A m n ihA ihm ihn => asimp[up_upren, up_comp_upren, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_upren, up_comp_upren, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_upren, up_comp_upren, ihA, ihm, ihn]

lemma up_comp_ren (σ : Var -> Tm Srt) (ξ : Var -> Var) :
    up σ !>> rename (upren ξ) = up (σ !>> rename ξ)  := by
  funext x
  cases x with
  | zero => asimp
  | succ n =>
    asimp[rename_subst]
    have h1 := ren_subst_comp (.+1) (ren (upren ξ)) (σ n); asimp at h1
    have h2 := ren_subst_comp ξ (shift 1) (σ n); asimp at h2
    rw[h1, h2]; rfl

lemma subst_ren_comp σ ξ (m : Tm Srt) : m.[σ].[ren ξ] = m.[σ !>> rename ξ] := by
  induction m generalizing σ ξ with
  | var => asimp[rename_subst]
  | srt => asimp
  | pi A B r s ihA ihB => asimp[up_upren, up_comp_ren, ihA, ihB]
  | lam A m r s ihA ihm => asimp[up_upren, up_comp_ren, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B r s ihA ihB => asimp[up_upren, up_comp_ren, ihA, ihB]
  | tup m r n s ihm ihn => asimp[ihm, ihn]
  | prj A m n ihA ihm ihn => asimp[up_upren, up_comp_ren, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_upren, up_comp_ren, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_upren, up_comp_ren, ihA, ihm, ihn]

lemma up_comp (σ τ : Var -> Tm Srt) :  up σ !> up τ = up (σ !> τ) := by
  funext x
  cases x with
  | zero => asimp
  | succ n =>
    asimp[rename_subst]
    have h1 := subst_ren_comp τ (.+1) (σ n)
    have h2 := ren_subst_comp (.+1) (up τ) (σ n)
    rw[h1, h2]
    rfl

lemma subst_comp (σ τ : Var -> Tm Srt) m : m.[σ].[τ] = m.[σ !> τ] := by
  induction m generalizing σ τ with
  | var => asimp
  | srt => asimp
  | pi A B r s ihA ihB => asimp[up_comp, ihA, ihB]
  | lam A m r s ihA ihm => asimp[up_comp, ihA, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | sig A B r s ihA ihB => asimp[up_comp, ihA, ihB]
  | tup m n r s ihm ihn => asimp[ihm, ihn]
  | prj A m n ihA ihm ihn => asimp[up_comp, ihm, ihA, ihn]
  | bool => asimp
  | tt => asimp
  | ff => asimp
  | ite A m n1 n2 ihA ihm ihn1 ihn2 => asimp[up_comp, ihA, ihm, ihn1, ihn2]
  | idn A m n ihA ihm ihn => asimp[ihA, ihm, ihn]
  | rfl m ihm => asimp[ihm]
  | rw A m n ihA ihm ihn => asimp[up_comp, ihA, ihm, ihn]

instance : SubstLemmas (Tm Srt) where
  rename_subst := rename_subst
  subst_id := subst_id
  id_subst := by intros; asimp
  subst_comp := subst_comp
end SubstLemmas
end Tm
