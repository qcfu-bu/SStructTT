import SStructTT.SStruct.Runtime.Preservation0
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservation1X {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 -> WR H2 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step1 (H3, c) (H3', c') ->
    ∃ H1', HMerge H1' H2 H3' ∧ [] ;; [] ;; H1' ⊢ a ▷ b ◁ c' : A := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro mrg0 wr2 ⟨er, rs, wr1⟩ st; induction er generalizing H1 H2 H3 H3' c c'
  case var wf hs =>
    subst_vars; cases hs
  case lam_im A B m m' s sA i lw tyA erm ihm =>
    subst_vars; cases rs
    case lam x rsx lwx =>
      cases st
      case alloc s l h vl =>
        cases vl
        have ⟨h1, h2⟩ := mrg0.split_none h
        have nfm := erm.nf; simp at nfm
        have nfx := rsx.nf_preimage wr1 nfm
        exists H1.insert l (x.lam s, s); and_intros
        . apply mrg0.insert_left; assumption
        . constructor
          . apply Erased.lam_im <;> assumption
          . apply Resolve.ptr
            . assumption
            . constructor <;> assumption
          . apply wr1.insert_lam nfx
    case ptr =>
      cases st; case alloc vl =>
      cases vl
  all_goals sorry
