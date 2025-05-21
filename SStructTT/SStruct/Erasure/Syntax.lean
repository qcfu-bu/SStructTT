import SStructTT.SStruct.Static.Typed
import SStructTT.SStruct.Dynamic.Typed

namespace SStruct.Erasure
variable (Srt : Type)

inductive Tm where
  | var  (x : Var)
  | lam  (m : Tm) (s : Srt)
  | app  (m n : Tm)
  | tup  (m n : Tm) (s : Srt)
  | prj  (m n : Tm)
  | tt | ff
  | ite  (m n1 n2 : Tm)
  | rw   (m : Tm)
  | drop (ms : List Tm) (m : Tm)
  | ptr  (l : Nat)
  | null

namespace Tm
variable {Srt : Type}
instance : Ids (Tm Srt) where
  ids := var

@[asimp]lemma ids_var x : @var Srt x = ids x := by rfl

def rename_rec (ξ : Var -> Var) (m : Tm Srt) : Tm Srt :=
  match m with
  | var x => var (ξ x)
  | lam m s => lam (rename_rec (upren ξ) m) s
  | app m n => app (rename_rec ξ m) (rename_rec ξ n)
  | tup m n s => tup (rename_rec ξ m) (rename_rec ξ n) s
  | prj m n => prj (rename_rec ξ m) (rename_rec (upren $ upren ξ) n)
  | tt => tt
  | ff => ff
  | ite m n1 n2 => ite (rename_rec ξ m) (rename_rec ξ n1) (rename_rec ξ n2)
  | rw m => rw (rename_rec ξ m)
  | drop ms m => drop (ms.map (rename_rec ξ)) (rename_rec ξ m)
  | ptr l => ptr l
  | null => null

instance : Rename (Tm Srt) where
  rename := rename_rec

namespace Rename
variable (ξ : Var -> Var) (A B m n n1 n2 : Tm Srt) (ms : List (Tm Srt)) (x i l : Nat) (s : Srt)

@[asimp]lemma ids  : rename ξ (ids x) = @ids (Tm Srt) _ (ξ x) := by apply rename_rec.eq_def
@[asimp]lemma lam  : rename ξ (lam m s) = lam (rename (upren ξ) m) s := by apply rename_rec.eq_def
@[asimp]lemma app  : rename ξ (app m n) = app (rename ξ m) (rename ξ n) := by apply rename_rec.eq_def
@[asimp]lemma tup  : rename ξ (tup m n s) = tup (rename ξ m) (rename ξ n) s := by apply rename_rec.eq_def
@[asimp]lemma prj  : rename ξ (prj m n) = prj (rename ξ m) (rename (upren $ upren ξ) n) := by apply rename_rec.eq_def
@[asimp]lemma tt   : rename ξ (@tt Srt) = tt := by apply rename_rec.eq_def
@[asimp]lemma ff   : rename ξ (@ff Srt) = ff := by apply rename_rec.eq_def
@[asimp]lemma ite  : rename ξ (ite m n1 n2) = ite (rename ξ m) (rename ξ n1) (rename ξ n2) := by apply rename_rec.eq_def
@[asimp]lemma rw   : rename ξ (rw m) = rw (rename ξ m) := by apply rename_rec.eq_def
@[asimp]lemma drop : rename ξ (drop ms m) = drop (ms.map (rename ξ)) (rename ξ m) := by apply rename_rec.eq_def
@[asimp]lemma ptr  : rename ξ (@ptr Srt l) = ptr l := by apply rename_rec.eq_def
@[asimp]lemma null : rename ξ (@null Srt) = null := by apply rename_rec.eq_def
@[asimp]lemma rename_rec : rename_rec ξ m = rename ξ m := by rfl
end Rename

def subst_rec (σ : Var -> Tm Srt) (m : Tm Srt) : Tm Srt :=
  match m with
  | var x => σ x
  | lam m s => lam (subst_rec (up σ) m) s
  | app m n => app (subst_rec σ m) (subst_rec σ n)
  | tup m n s => tup (subst_rec σ m) (subst_rec σ n) s
  | prj m n => prj (subst_rec σ m) (subst_rec (upn 2 σ) n)
  | tt => tt
  | ff => ff
  | ite m n1 n2 => ite (subst_rec σ m) (subst_rec σ n1) (subst_rec σ n2)
  | rw m => rw (subst_rec σ m)
  | ptr l => ptr l
  | drop ms m => drop (ms.map (subst_rec σ)) (subst_rec σ m)
  | null => null

instance : Subst (Tm Srt) where
  subst := subst_rec

namespace Subst
variable (σ : Var -> Tm Srt) (A B m n n1 n2 : Tm Srt) (ms : List (Tm Srt)) (x i l : Nat) (s : Srt)

@[asimp]lemma ids  : subst σ (ids x) = σ x := by apply subst_rec.eq_def
@[asimp]lemma lam  : subst σ (lam m s) = lam (subst (up σ) m) s := by apply subst_rec.eq_def
@[asimp]lemma app  : subst σ (app m n) = app (subst σ m) (subst σ n) := by apply subst_rec.eq_def
@[asimp]lemma tup  : subst σ (tup m n s) = tup (subst σ m) (subst σ n) s := by apply subst_rec.eq_def
@[asimp]lemma prj  : subst σ (prj m n) = prj (subst σ m) (subst (upn 2 σ) n) := by apply subst_rec.eq_def
@[asimp]lemma tt   : subst σ (@tt Srt) = tt := by apply subst_rec.eq_def
@[asimp]lemma ff   : subst σ (@ff Srt) = ff := by apply subst_rec.eq_def
@[asimp]lemma ite  : subst σ (ite m n1 n2) = ite (subst σ m) (subst σ n1) (subst σ n2) := by apply subst_rec.eq_def
@[asimp]lemma rw   : subst σ (rw m) = rw (subst σ m) := by apply subst_rec.eq_def
@[asimp]lemma drop : subst σ (drop ms m) = drop (ms.map (subst σ)) (subst σ m) := by apply subst_rec.eq_def
@[asimp]lemma ptr  : subst σ (@ptr Srt l) = ptr l := by apply subst_rec.eq_def
@[asimp]lemma null : subst σ (@null Srt) = null := by apply subst_rec.eq_def
@[asimp]lemma subst_rec : subst_rec σ m = subst σ m := by rfl
end Subst

section SubstLemmas
lemma up_upren (ξ : Var -> Var) :
    @up (Tm Srt) _ _ (ren ξ) = ren (upren ξ) := by
  funext x; cases x <;> asimp

lemma rename_subst ξ (m : Tm Srt) : rename ξ m = m.[ren ξ] := by
  induction m using
    Tm.rec (motive_2 := fun ms => ∀ξ, ms.map (rename ξ) = ms.map (. .[ren ξ]))
  generalizing ξ with
  | var => asimp
  | lam m s ihm => asimp[up_upren, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | tup m n s ihm ihn => asimp[ihm, ihn]
  | prj m n ihm ihn => asimp[up_upren, ihm, ihn]
  | tt => asimp
  | ff => asimp
  | ite m n1 n2 ihm ihn1 ihn2 => asimp[up_upren, ihm, ihn1, ihn2]
  | rw m ihm => asimp[ihm]
  | drop ms m ihms ihm => asimp[up_upren, ihms, ihm]
  | ptr l => asimp
  | null => asimp
  | nil ξ => simp
  | cons ξ => simp; aesop

lemma up_ids : up ids = @ids (Tm Srt) _ := by
  funext x
  cases x with
  | zero => asimp
  | succ => asimp

lemma subst_id (m : Tm Srt) : m.[ids] = m := by
  induction m using
    Tm.rec (motive_2 := fun ms => ms.map (. .[ids]) = ms)
  with
  | var => asimp
  | lam m s ihm => asimp[up_ids, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | tup m n s ihm ihn => asimp[ihm, ihn]
  | prj m n ihm ihn => asimp[up_ids, ihm, ihn]
  | tt => asimp
  | ff => asimp
  | ite m n1 n2 ihm ihn1 ihn2 => asimp[up_ids, ihm, ihn1, ihn2]
  | rw m ihm => asimp[ihm]
  | drop ms m ihms ihm => asimp[ihms, ihm]
  | ptr l => asimp
  | null => asimp
  | nil => simp
  | cons => simp; aesop

lemma up_comp_upren (ξ : Var -> Var) (σ : Var -> Tm Srt) :
    up (ξ !>> σ) = upren ξ !>> up σ := by
  funext x
  cases x with
  | zero => rfl
  | succ => asimp

lemma ren_subst_comp ξ σ (m : Tm Srt) : m.[ren ξ].[σ] = m.[ξ !>> σ] := by
  induction m using
    Tm.rec (motive_2 := fun ms => ∀ξ σ, (ms.map (. .[ren ξ])).map (. .[σ]) = ms.map (. .[ξ !>> σ]))
  generalizing ξ σ with
  | var => asimp
  | lam m c ihm => asimp[up_upren, up_comp_upren, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | tup m n s ihm ihn => asimp[ihm, ihn]
  | prj m n ihm ihn => asimp[up_upren, up_comp_upren, ihm, ihn]
  | tt => asimp
  | ff => asimp
  | ite m n1 n2 ihm ihn1 ihn2 => asimp[up_upren, up_comp_upren, ihm, ihn1, ihn2]
  | rw m ihm => asimp[ihm]
  | drop ms m ihms ihm => asimp[ihms, ihm]
  | ptr l => asimp
  | null => asimp
  | nil => simp
  | cons => simp; aesop

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
  induction m using
    Tm.rec (motive_2 := fun ms => ∀ξ σ, (ms.map (. .[σ])).map (. .[ren ξ]) = ms.map (. .[σ !>> rename ξ]))
  generalizing σ ξ with
  | var => asimp[rename_subst]
  | lam m s ihm => asimp[up_upren, up_comp_ren, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | tup m n s ihm ihn => asimp[ihm, ihn]
  | prj m n ihm ihn => asimp[up_upren, up_comp_ren, ihm, ihn]
  | tt => asimp
  | ff => asimp
  | ite m n1 n2 ihm ihn1 ihn2 => asimp[up_upren, up_comp_ren, ihm, ihn1, ihn2]
  | rw m ihm => asimp[ihm]
  | drop ms m ihms ihm => asimp[ihms, ihm]
  | ptr l => asimp
  | null => asimp
  | nil => simp
  | cons => simp; aesop

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
  induction m using
    Tm.rec (motive_2 := fun ms => ∀σ τ, (ms.map (. .[σ])).map (. .[τ]) = ms.map (. .[σ !> τ]))
  generalizing σ τ with
  | var => asimp
  | lam m s ihm => asimp[up_comp, ihm]
  | app m n ihm ihn => asimp[ihm, ihn]
  | tup m n s ihm ihn => asimp[ihm, ihn]
  | prj m n ihm ihn => asimp[up_comp, ihm, ihn]
  | tt => asimp
  | ff => asimp
  | ite m n1 n2 ihm ihn1 ihn2 => asimp[up_comp, ihm, ihn1, ihn2]
  | rw m ihm => asimp[ihm]
  | drop ms m ihms ihm => asimp[ihms, ihm]
  | ptr l => asimp
  | null => asimp
  | nil => simp
  | cons => simp; aesop

instance : SubstLemmas (Tm Srt) where
  rename_subst := rename_subst
  subst_id := subst_id
  id_subst := by intros; asimp
  subst_comp := subst_comp
end SubstLemmas
end Tm
