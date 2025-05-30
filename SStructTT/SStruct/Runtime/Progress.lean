import SStructTT.SStruct.Runtime.Poised
open ARS

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.progressX {H : Heap Srt} {a b c A} :
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
      have cl := erm.closed; simp at cl
      replace cl := rs.closed_preimage cl
      cases ps
    case ptr => right; aesop
  case lam_ex erm ih =>
    subst_vars; clear ih; cases rs
    case lam rs _ =>
      have ⟨l, h⟩ := H.fresh
      have cl := erm.closed; simp at cl
      replace cl := rs.closed_preimage cl
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
        existsi Hx, .app x n
        constructor; assumption
      | .inr ⟨l1, e⟩ =>
        subst_vars
        match ihn rfl rfl rsn ps2 with
        | .inl ⟨H, n1, st⟩ =>
          have ⟨Hx, x, st⟩ := st.merge mrg.sym
          existsi Hx, .app (.ptr l1) x
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
  case tup_im s _ _ _ erm ihm =>
    subst_vars; cases rs
    case tup mrg rsm rsn =>
      have ⟨_, e⟩ := rsn.null_inv; subst e
      cases ps
      case tup_M h ps1 ps2 =>
        match ihm rfl rfl rsm ps1 with
        | .inl ⟨H, m1, st⟩ =>
          have ⟨Hx, x, st⟩ := st.merge mrg
          left; existsi Hx, .tup x .null s
          constructor; assumption
        | .inr ⟨l1, e⟩ =>
          exfalso; apply h; assumption
      case tup_N h _ =>
        exfalso; apply h .null
    case ptr => right; aesop
  case tup_ex s _ mrg _ _ _ ihm ihn =>
    subst_vars; cases mrg; cases rs
    case tup m n mrg rsm rsn =>
      cases ps
      case tup_M h ps1 ps2 =>
        match ihm rfl rfl rsm ps1 with
        | .inl ⟨H, m1, st⟩ =>
          have ⟨Hx, x, st⟩ := st.merge mrg
          left; existsi Hx, .tup x n s
          constructor; assumption
        | .inr ⟨l1, e⟩ =>
          exfalso; apply h; assumption
      case tup_N ps1 h ps2 =>
        match ihn rfl rfl rsn ps2 with
        | .inl ⟨H, m1, st⟩ =>
          have ⟨Hx, x, st⟩ := st.merge mrg.sym
          left; existsi Hx, .tup m x s
          constructor; assumption
        | .inr ⟨l1, e⟩ =>
          exfalso; apply h; subst e; constructor
    case ptr => right; aesop
  case prj_im mrg _ erm _ ihm _ =>
    subst_vars; cases mrg; cases rs
    case prj rsm rsn =>
      left; cases ps; case prj m n mrg ps =>
      match ihm rfl rfl rsm ps with
      | .inl ⟨H, m1, st⟩ =>
        have ⟨Hx, x, st⟩ := st.merge mrg
        existsi Hx, .prj x n
        constructor; assumption
      | .inr ⟨l, e⟩ =>
        subst_vars
        have vl := rsm.ptr_value
        have ⟨m1, m2, e⟩ := erm.sig_canonical Conv.R vl; subst e
        cases rsm; case ptr H m0 lk rsm =>
        cases m0
        all_goals simp_all[Cell.tm]; cases rsm
        case box.tup l _ _ _ rsm rsn =>
          have ⟨Hx, lk, mrg⟩ := lk.merge mrg
          existsi Hx, n.[.null,.ptr l/]
          constructor; assumption
        case tup.tup rsm rsn =>
          have ⟨_, _, _, _, erm⟩ := erm.tup_preimage
          have ⟨_, _, _, _⟩ := erm.toStatic.tup_inv; subst_vars
          have ⟨_, _, _, _⟩ := erm.tup_im_inv; subst_vars
          exfalso; have ⟨_, e⟩ := rsn.null_inv; cases e
    case ptr => right; aesop
  case prj_ex mrg _ erm _ ihm _ =>
    subst_vars; cases mrg; cases rs
    case prj rsm rsn =>
      left; cases ps; case prj m n mrg ps =>
      match ihm rfl rfl rsm ps with
      | .inl ⟨H, m1, st⟩ =>
        have ⟨Hx, x, st⟩ := st.merge mrg
        existsi Hx, .prj x n
        constructor; assumption
      | .inr ⟨l, e⟩ =>
        subst_vars
        have vl := rsm.ptr_value
        have ⟨m1, m2, e⟩ := erm.sig_canonical Conv.R vl; subst e
        cases rsm; case ptr H m0 lk rsm =>
        cases m0
        all_goals simp_all[Cell.tm]; cases rsm
        case tup.tup l1 l2 _ _ _ rsm rsn =>
          have ⟨Hx, lk, mrg⟩ := lk.merge mrg
          existsi Hx, n.[.ptr l2,.ptr l1/]
          constructor; assumption
        case box.tup rsm rsn =>
          have ⟨_, _, _, _, erm⟩ := erm.tup_preimage
          have ⟨_, _, _, _⟩ := erm.toStatic.tup_inv; subst_vars
          have ⟨_, _, _, _, er, _⟩ := erm.tup_ex_inv
          cases rsn; exfalso; apply er.null_preimage
    case ptr => right; aesop
  case tt =>
    subst_vars; cases rs
    case tt => cases ps
    case ptr => right; aesop
  case ff =>
    subst_vars; cases rs
    case ff => cases ps
    case ptr => right; aesop
  case ite mrg _ erm _ _ ihm ihn1 ihn2 =>
    subst_vars; cases mrg; cases rs
    case ite mrg rsm rsn1 rsn2 =>
      left; cases ps; case ite m n1 n2 ps =>
      match ihm rfl rfl rsm ps with
      | .inl ⟨H, m1, st⟩ =>
        have ⟨Hx, x, st⟩ := st.merge mrg
        existsi Hx, .ite x n1 n2
        constructor; assumption
      | .inr ⟨l, e⟩ =>
        subst_vars
        have vl := rsm.ptr_value
        cases erm.bool_canonical Conv.R vl with
        | inl e =>
          subst e
          cases rsm; case ptr m0 lk rsm =>
          cases m0
          all_goals simp_all[Cell.tm]; cases rsm
          case tt =>
            have ⟨Hx, lk, _⟩ := lk.merge mrg
            existsi Hx, n1
            constructor; assumption
        | inr e =>
          cases rsm; case ptr m0 lk rsm =>
          cases m0
          all_goals simp_all[Cell.tm]; cases rsm
          case ff =>
            have ⟨Hx, lk, _⟩ := lk.merge mrg
            existsi Hx, n2
            constructor; assumption
    case ptr => right; aesop
  case drop ihm ihn =>
    subst_vars; clear ihm ihn
    cases rs
    case drop => cases ps
    case ptr => right; aesop
  case rw => subst_vars; aesop
  case conv => subst_vars; aesop

lemma Resolved.progress {H : Heap Srt} {a b c A} :
    [] ;; [] ;; H ⊢ a ▷ b ◁ c : A ->
    (∃ H' c', (H, c) ~>> (H', c')) ∨ (∃ H' l, Red01 (H, c) (H', .ptr l))  := by
  intro rs
  have sn := Step01.sn (H, c)
  have ⟨⟨H1, c'⟩, ⟨rd, norm⟩⟩ := sn.wn; clear sn
  have ⟨b', rs, _⟩ := rs.preservationX rd
  have p := rs.normal_poised norm
  match rs.progressX p with
  | .inl ⟨Hx, x, st⟩  =>
    left; existsi Hx, x; apply Step.intro rd norm st
  | .inr ⟨l, e⟩ =>
    subst_vars
    right; exists H1, l
