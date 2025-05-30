import SStructTT.SStruct.Runtime.Poised
open ARS

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.progessX {H : Heap Srt} {a b c A} :
    [] ;; [] ;; H ⊢ a ▷ b ◁ c : A -> Poised c ->
    (∃ H' c', Step2 (H, c) (H', c')) ∨ (∃ l, c = .ptr l)  := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro ⟨er, rs⟩ ps; induction er generalizing H c
  case var hs => subst_vars; cases hs
  case lam_im erm ih =>
    subst_vars; clear ih; cases rs
    case lam rs _ =>
      have ⟨l, h⟩ := H.fresh
      have nf := erm.nf; simp at nf
      replace nf := rs.nf_preimage nf
      cases ps
    case ptr => right; aesop
  case lam_ex erm ih =>
    subst_vars; clear ih; cases rs
    case lam rs _ =>
      have ⟨l, h⟩ := H.fresh
      have nf := erm.nf; simp at nf
      replace nf := rs.nf_preimage nf
      cases ps
    case ptr => right; aesop
  case app_im erm tyn ihm =>
    subst_vars; cases rs
    case app rsm rsn =>
      left; cases ps; case app mrg ps1 ps2 =>
      have ⟨_, e⟩ := rsn.null_inv; subst e
      match ihm rfl rfl rsm ps1 with
      | .inl ⟨H, m1, st⟩ =>
        have ⟨Hx, x, st⟩ := st.merge mrg
        existsi Hx, .app x .null
        constructor; assumption
      | .inr ⟨l, e⟩ =>
        subst_vars
        have vl := rsm.ptr_value
        have ⟨m0, e⟩ := erm.pi_canonical Conv.R vl; subst e
        cases rsm; case ptr H0 m1 lk rsm =>
        cases m1
        all_goals simp_all[Cell.tm]; cases rsm
        case lam m1 _ _ _ =>
        have ⟨Hx, lk, _⟩ := lk.merge mrg
        existsi Hx, m1.[.null/]
        constructor
        constructor
        assumption
    case ptr => right; aesop
  case app_ex mrg erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case app m n _ rsm rsn =>
      left; cases ps; case app mrg ps1 ps2 =>
      match ihm rfl rfl rsm ps1 with
      | .inl ⟨H, m1, st⟩ =>
        have ⟨Hx, x, st⟩ := st.merge mrg
        exists Hx, .app x n
        constructor; assumption
      | .inr ⟨l1, e⟩ =>
        subst_vars
        match ihn rfl rfl rsn ps2 with
        | .inl ⟨H, n1, st⟩ =>
          have ⟨Hx, x, st⟩ := st.merge mrg.sym
          exists Hx, .app (.ptr l1) x
          constructor; assumption
        | .inr ⟨l2, e⟩ =>
          clear ihm ihn; subst_vars
          have vl1 := rsm.ptr_value
          have ⟨m, e⟩ := erm.pi_canonical Conv.R vl1; subst e
          cases rsm; case ptr H m1 lk rsm =>
          cases m1
          all_goals simp_all[Cell.tm]; cases rsm
          case lam m1 _ _ _ =>
          have ⟨Hx, lk, _⟩ := lk.merge mrg
          existsi Hx, m1.[.ptr l2/]
          constructor
          constructor
          assumption
    case ptr => right; aesop
  all_goals sorry

lemma Resolved.progess {H : Heap Srt} {a b c A} :
    [] ;; [] ;; H ⊢ a ▷ b ◁ c : A ->
    (∃ H' c', (H, c) ~>> (H', c')) ∨ (∃ H' l, Red01 (H, c) (H', .ptr l))  := by
  intro rs
  have sn := Step01.sn (H, c)
  have ⟨⟨H1, c'⟩, ⟨rd, norm⟩⟩ := sn.wn; clear sn
  have ⟨b', rs, _⟩ := rs.preservationX rd
  have p := rs.normal_poised norm
  match rs.progessX p with
  | .inl ⟨Hx, x, st⟩  =>
    left; existsi Hx, x; apply Step.intro rd norm st
  | .inr ⟨l, e⟩ =>
    subst_vars
    right; exists H1, l
