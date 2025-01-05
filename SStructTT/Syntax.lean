import SStructTT.Subst

variable (Srt : Type)

-- Computational Relevancy
inductive Rlv where
  | I -- implicit
  | E -- explicit

inductive Tm where
  | var  (x : Var)
  | srt  (s : Srt) (i : Nat)
  | pi   (A B : Tm) (r : Rlv) (s : Srt)
  | lam  (A m : Tm) (r : Rlv) (s : Srt)
  | app  (m n : Tm)
  | sig  (A B : Tm) (r : Rlv) (s : Srt)
  | pair (m n : Tm) (r : Rlv) (s : Srt)
  | proj (A m n : Tm)
  | bool | tt | ff
  | ifte (A m n1 n2 : Tm)
  | id   (A m n : Tm)
  | rfl  (m : Tm)
  | rw   (A h p : Tm)

namespace Tm
instance : Ids (Tm Srt) where
  ids := var

@[asimp]theorem ids_var x : @var Srt x = ids x := by rfl

def rename_rec (ξ : Var -> Var) (m : Tm Srt) : Tm Srt :=
  match m with
  | var x => var (ξ x)
  | srt s i => srt s i
  | pi A B r s => pi (rename_rec ξ A) (rename_rec (upren ξ) B) r s
  | lam A m r s => lam (rename_rec ξ A) (rename_rec (upren ξ) m) r s
  | app m n => app (rename_rec ξ m) (rename_rec ξ n)
  | sig A B r s => sig (rename_rec ξ A) (rename_rec (upren ξ) B) r s
  | pair m n r s => pair (rename_rec ξ m) (rename_rec ξ n) r s
  | proj A m n => proj (rename_rec (upren ξ) A) (rename_rec ξ m) (rename_rec (upren $ upren ξ) n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ifte A m n1 n2 => ifte (rename_rec (upren ξ) A) (rename_rec ξ m) (rename_rec ξ n1) (rename_rec ξ n2)
  | id A m n => id (rename_rec ξ A) (rename_rec ξ m) (rename_rec ξ n)
  | rfl m => rfl (rename_rec ξ m)
  | rw A m n => rw (rename_rec (upren (upren ξ)) A) (rename_rec ξ m) (rename_rec ξ n)

instance : Rename (Tm Srt) where
  rename := rename_rec Srt

section RenameEqns
variable (ξ : Var -> Var) (A B m n n1 n2 : Tm Srt) (x i : Nat) (r : Rlv) (s : Srt)

@[asimp]lemma rename_ids  : rename ξ (ids x) = @ids (Tm Srt) _ (ξ x) := by rfl
@[asimp]lemma rename_srt  : rename ξ (srt s i) = srt s i := by rfl
@[asimp]lemma rename_pi   : rename ξ (pi A B r s) = pi (rename ξ A) (rename (upren ξ) B) r s := by rfl
@[asimp]lemma rename_lam  : rename ξ (lam A m r s) = lam (rename ξ A) (rename (upren ξ) m) r s := by rfl
@[asimp]lemma rename_app  : rename ξ (app m n) = app (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma rename_sig  : rename ξ (sig A B r s) = sig (rename ξ A) (rename (upren ξ) B) r s := by rfl
@[asimp]lemma rename_pair : rename ξ (pair m n r s) = pair (rename ξ m) (rename ξ n) r s := by rfl
@[asimp]lemma rename_proj : rename ξ (proj A m n) = proj (rename (upren ξ) A) (rename ξ m) (rename (upren $ upren ξ) n) := by rfl
@[asimp]lemma rename_bool : rename ξ (@bool Srt) = bool := by rfl
@[asimp]lemma rename_tt   : rename ξ (@tt Srt) = tt := by rfl
@[asimp]lemma rename_ff   : rename ξ (@ff Srt) = ff := by rfl
@[asimp]lemma rename_ifte : rename ξ (ifte A m n1 n2) = ifte (rename (upren ξ) A) (rename ξ m) (rename ξ n1) (rename ξ n2) := by rfl
@[asimp]lemma rename_id   : rename ξ (id A m n) = id (rename ξ A) (rename ξ m) (rename ξ n) := by rfl
@[asimp]lemma rename_rfl  : rename ξ (rfl m) = rfl (rename ξ m) := by rfl
@[asimp]lemma rename_rw   : rename ξ (rw A m n) = rw (rename (upren $ upren ξ) A) (rename ξ m) (rename ξ n) := by rfl
end RenameEqns

def subst_rec (σ : Var -> Tm Srt) (m : Tm Srt) : Tm Srt :=
  match m with
  | var x => σ x
  | srt s i => srt s i
  | pi A B r s => pi (subst_rec σ A) (subst_rec (up σ) B) r s
  | lam A m r s => lam (subst_rec σ A) (subst_rec (up σ) m) r s
  | app m n => app (subst_rec σ m) (subst_rec σ n)
  | sig A B r s => sig (subst_rec σ A) (subst_rec (up σ) B) r s
  | pair m n r s => pair (subst_rec σ m) (subst_rec σ n) r s
  | proj A m n => proj (subst_rec (up σ) A) (subst_rec σ m) (subst_rec (up $ up σ) n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ifte A m n1 n2 => ifte (subst_rec (up σ) A) (subst_rec σ m) (subst_rec σ n1) (subst_rec σ n2)
  | id A m n => id (subst_rec σ A) (subst_rec σ m) (subst_rec σ n)
  | rfl m => rfl (subst_rec σ m)
  | rw A m n => rw (subst_rec (up $ up σ) A) (subst_rec σ m) (subst_rec σ n)

instance : Subst (Tm Srt) where
  subst := subst_rec Srt

section SubstEqns
variable (σ : Var -> Tm Srt) (A B m n n1 n2 : Tm Srt) (x i : Nat) (r : Rlv) (s : Srt)

@[asimp]lemma subst_ids  : subst σ (ids x) = σ x := by rfl
@[asimp]lemma subst_srt  : subst σ (srt s i) = srt s i := by rfl
@[asimp]lemma subst_pi   : subst σ (pi A B r s) = pi (subst σ A) (subst (up σ) B) r s := by rfl
@[asimp]lemma subst_lam  : subst σ (lam A m r s) = lam (subst σ A) (subst (up σ) m) r s := by rfl
@[asimp]lemma subst_app  : subst σ (app m n) = app (subst σ m) (subst σ n) := by rfl
@[asimp]lemma subst_sig  : subst σ (sig A B r s) = sig (subst σ A) (subst (up σ) B) r s := by rfl
@[asimp]lemma subst_pair : subst σ (pair m n r s) = pair (subst σ m) (subst σ n) r s := by rfl
@[asimp]lemma subst_proj : subst σ (proj A m n) = proj (subst (up σ) A) (subst σ m) (subst (up $ up σ) n) := by rfl
@[asimp]lemma subst_bool : subst σ (@bool Srt) = bool := by rfl
@[asimp]lemma subst_tt   : subst σ (@tt Srt) = tt := by rfl
@[asimp]lemma subst_ff   : subst σ (@ff Srt) = ff := by rfl
@[asimp]lemma subst_ifte : subst σ (ifte A m n1 n2) = ifte (subst (up σ) A) (subst σ m) (subst σ n1) (subst σ n2) := by rfl
@[asimp]lemma subst_id   : subst σ (id A m n) = id (subst σ A) (subst σ m) (subst σ n) := by rfl
@[asimp]lemma subst_rfl  : subst σ (rfl m) = rfl (subst σ m) := by rfl
@[asimp]lemma subst_rw   : subst σ (rw A m n) = rw (subst (up $ up σ) A) (subst σ m) (subst σ n) := by rfl
end SubstEqns

section Lemmas
theorem up_upren (ξ : Var -> Var) :
  @up (Tm Srt) _ _ (ren ξ) = ren (upren ξ) := by
  funext x; cases x <;> asimp







end Lemmas

end Tm
