import SStructTT.SStruct.Erasure.Progress
import SStructTT.SStruct.Runtime.Preservation
open ARS

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

@[simp]def measure : Tm Srt -> Nat
  | .var _ => 0
  | .lam _ _ => 1
  | .app m n => measure m + measure n
  | .tup m n _ => measure m + measure n + 1
  | .prj m _ => measure m
  | .tt => 1
  | .ff => 1
  | .ite m _ _ => measure m
  | .drop _ m => measure m + 1
  | .ptr _ => 0
  | .null => 0

def Measure : State Srt -> State Srt -> Prop  :=
  InvImage (. < .) (fun m => measure m.2)

lemma measure_decrease {H1 H2 : Heap Srt} {m1 m2} :
    Step01 (H1, m1) (H2, m2) -> measure m2 < measure m1 := by
  intro st; induction m1 generalizing H1 H2 m2
  all_goals simp_all[Step01]
  case var =>
    cases st with
    | inl st => cases st
    | inr st => cases st
  case lam =>
    cases st with
    | inl st => cases st
    | inr st => cases st; simp
  case app ihm ihn =>
    cases st with
    | inl st =>
      cases st
      case app_M st => simp[ihm (Or.inl st)]
      case app_N st => simp[ihn (Or.inl st)]
    | inr st =>
      cases st
      case app_M st => simp[ihm (Or.inr st)]
      case app_N st => simp[ihn (Or.inr st)]
  case tup ihm ihn =>
    cases st with
    | inl st =>
      cases st
      case tup_M st => simp[ihm (Or.inl st)]
      case tup_N st => simp[ihn (Or.inl st)]
    | inr st =>
      cases st
      case tup_M st => simp[ihm (Or.inr st)]
      case tup_N st => simp[ihn (Or.inr st)]
      case alloc_box => simp
      case alloc_tup => simp
  case prj ihm ihn =>
    cases st with
    | inl st =>
      cases st
      case prj_M st => simp[ihm (Or.inl st)]
    | inr st =>
      cases st
      case prj_M st => simp[ihm (Or.inr st)]
  case tt =>
    cases st with
    | inl st => cases st
    | inr st => cases st; simp
  case ff =>
    cases st with
    | inl st => cases st
    | inr st => cases st; simp
  case ite ihm ihn1 ihn2 =>
    cases st with
    | inl st =>
      cases st
      case ite_M st => simp[ihm (Or.inl st)]
    | inr st =>
      cases st
      case ite_M st => simp[ihm (Or.inr st)]
  case drop ihm ihn =>
    cases st with
    | inl st => cases st; simp
    | inr st => cases st
  case ptr =>
    cases st with
    | inl st => cases st
    | inr st => cases st
  case null =>
    cases st with
    | inl st => cases st
    | inr st => cases st

lemma measure_subrelation :
    Subrelation (flip (@Step01 Srt ord)) Measure := by
  intro ⟨H1, m1⟩ ⟨H2, m2⟩ st
  apply measure_decrease st

lemma Step01.wf : WellFounded (flip (@Step01 Srt ord)) := by
  apply Subrelation.wf (@measure_subrelation Srt ord)
  apply InvImage.wf
  apply Nat.lt_wfRel.wf

lemma Step01.sn (m : State Srt) : SN Step01 m := by
  have ⟨acc⟩ := @Step01.wf Srt ord
  apply SN.ofAcc
  apply acc

lemma Drop.merge {H1 H1' H2 H3 : Heap Srt} {m} :
    Drop H1 m H1' -> HMerge H1 H2 H3 ->
    ∃ H3', Drop H3 m H3' ∧ HMerge H1' H2 H3' := by
  intro dp mrg; induction dp generalizing H2 H3
  case var H1 _ =>
    existsi H3; and_intros
    . constructor
    . assumption
  case lam ih =>
    have ⟨H4, dp, mrg⟩ := ih mrg
    existsi H4; and_intros
    . constructor; assumption
    . assumption
  case app dp1 dp2 ihm ihn =>
    have ⟨H4, dp3, mrg1⟩ := ihm mrg
    have ⟨H5, dp4, mrg2⟩ := ihn mrg1
    existsi H5; and_intros
    . constructor <;> assumption
    . assumption
  case tup dp1 dp2 ihm ihn =>
    have ⟨H4, dp3, mrg1⟩ := ihm mrg
    have ⟨H5, dp4, mrg2⟩ := ihn mrg1
    existsi H5; and_intros
    . constructor <;> assumption
    . assumption
  case prj dp1 dp2 ihm ihn =>
    have ⟨H4, dp3, mrg1⟩ := ihm mrg
    have ⟨H5, dp4, mrg2⟩ := ihn mrg1
    existsi H5; and_intros
    . constructor <;> assumption
    . assumption
  case tt =>
    existsi H3; and_intros
    . constructor
    . assumption
  case ff =>
    existsi H3; and_intros
    . constructor
    . assumption
  case ite dp1 dp2 ihm ihn =>
    have ⟨H4, dp3, mrg1⟩ := ihm mrg
    have ⟨H5, dp4, mrg2⟩ := ihn mrg1
    existsi H5; and_intros
    . constructor <;> assumption
    . assumption
  case drop dp1 dp2 ihm ihn =>
    have ⟨H4, dp3, mrg1⟩ := ihm mrg
    have ⟨H5, dp4, mrg2⟩ := ihn mrg1
    existsi H5; and_intros
    . constructor <;> assumption
    . assumption
  case ptr lk dp ih =>
    have ⟨H3, lk, mrg⟩ := lk.merge mrg
    have ⟨H4, dp1, mrg⟩ := ih mrg
    existsi H4; and_intros
    . constructor
      assumption
      assumption
    . assumption
  case null =>
    existsi H3; and_intros
    . constructor
    . assumption

lemma Step0.merge {H1 H1' H2 H3 : Heap Srt} {m n} :
    Step0 (H1, m) (H1', n) -> HMerge H1 H2 H3 -> ∃ H3' n', Step0 (H3, m) (H3', n') := by
  generalize e1: (H1, m) = t1
  generalize e2: (H1', n) = t2
  intro st mrg; induction st generalizing H1 H1' H2 H3 m n
  case app_M m m' n st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .app x n
    constructor; assumption
  case app_N m n n' st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .app m x
    constructor; assumption
  case tup_M m m' n s st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .tup x n s
    constructor; assumption
  case tup_N m n n' s st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .tup m x s
    constructor; assumption
  case prj_M m m' n st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .prj x n
    constructor; assumption
  case ite_M m m' n1 n2 st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .ite x n1 n2
    constructor; assumption
  case drop_elim m n dp =>
    cases e1; cases e2
    have ⟨Hx, dp, mrg⟩ := dp.merge mrg
    existsi Hx, n
    constructor; assumption

lemma Step1.merge {H1 H1' H2 H3 : Heap Srt} {m n} :
    Step1 (H1, m) (H1', n) -> HMerge H1 H2 H3 -> ∃ H3' n', Step1 (H3, m) (H3', n') := by
  generalize e1: (H1, m) = t1
  generalize e2: (H1', n) = t2
  intro st mrg; induction st generalizing H1 H1' H2 H3 m n
  case app_M m m' n st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .app x n
    constructor; assumption
  case app_N m n n' st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .app m x
    constructor; assumption
  case tup_M m m' n s st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .tup x n s
    constructor; assumption
  case tup_N m n n' s st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .tup m x s
    constructor; assumption
  case prj_M m m' n st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .prj x n
    constructor; assumption
  case ite_M m m' n1 n2 st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .ite x n1 n2
    constructor; assumption
  case alloc_clo H m s l h cl =>
    cases e1; cases e2
    have ⟨l, _⟩ := H3.fresh
    existsi H3.insert l (.clo m s cl), .ptr l
    constructor; assumption
  case alloc_box H s l l1 h =>
    cases e1; cases e2
    have ⟨l, _⟩ := H3.fresh
    existsi H3.insert l (.box l1 s), .ptr l
    constructor; assumption
  case alloc_tup H s l l1 l2 h =>
    cases e1; cases e2
    have ⟨l, _⟩ := H3.fresh
    existsi H3.insert l (.tup l1 l2 s), .ptr l
    constructor; assumption
  case alloc_tt H l h =>
    cases e1; cases e2
    have ⟨l, _⟩ := H3.fresh
    exists H3.insert l .tt, .ptr l
    constructor; assumption
  case alloc_ff H l h =>
    cases e1; cases e2
    have ⟨l, _⟩ := H3.fresh
    exists H3.insert l .ff, .ptr l
    constructor; assumption

lemma Step2.merge {H1 H1' H2 H3 : Heap Srt} {m n} :
    Step2 (H1, m) (H1', n) -> HMerge H1 H2 H3 -> ∃ H3' n', Step2 (H3, m) (H3', n') := by
  generalize e1: (H1, m) = t1
  generalize e2: (H1', n) = t2
  intro st mrg; induction st generalizing H1 H1' H2 H3 m n
  case app_M m m' n st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .app x n
    constructor; assumption
  case app_N m n n' st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .app m x
    constructor; assumption
  case beta Hx Hy m _ _ p _ np lk =>
    cases e1; cases e2
    have ⟨Hz, lk, mrg⟩ := lk.merge mrg
    existsi Hz, m.[p/]
    constructor <;> assumption
  case tup_M m m' n s st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .tup x n s
    constructor; assumption
  case tup_N m n n' s st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .tup m x s
    constructor; assumption
  case prj_M m m' n st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .prj x n
    constructor; assumption
  case prj_box n _ _ l lk =>
    cases e1; cases e2
    have ⟨Hx, lk, mrg⟩ := lk.merge mrg
    existsi Hx, n.[.null,.ptr l/]
    constructor <;> assumption
  case prj_tup n _ _ l1 l2 lk =>
    cases e1; cases e2
    have ⟨Hx, lk, mrg⟩ := lk.merge mrg
    exists Hx, n.[.ptr l2,.ptr l1/]
    constructor; assumption
  case ite_M m m' n1 n2 st ih =>
    cases e1; cases e2
    have ⟨Hx, x, mrg⟩ := ih rfl rfl mrg
    existsi Hx, .ite x n1 n2
    constructor; assumption
  case ite_tt n1 n2 _ lk =>
    cases e1; cases e2
    have ⟨Hx, lk, mrg⟩ := lk.merge mrg
    existsi Hx, n1
    constructor; assumption
  case ite_ff n1 n2 _ lk =>
    cases e1; cases e2
    have ⟨Hx, lk, mrg⟩ := lk.merge mrg
    existsi Hx, n2
    constructor; assumption

inductive Poised : Tm Srt -> Prop where
  | var {x} :
    Poised (.var x)
  | app {m n} :
    Poised m ->
    Poised n ->
    Poised (.app m n)
  | tup_M {m n s} :
    (∀ l, m ≠ .ptr l) ->
    Poised m ->
    Poised n ->
    Poised (.tup m n s)
  | tup_N {m n s} :
    ¬ Nullptr n ->
    Poised m ->
    Poised n ->
    Poised (.tup m n s)
  | prj {m n} :
    Poised m ->
    Poised (.prj m n)
  | ite {m n1 n2} :
    Poised m ->
    Poised (.ite m n1 n2)
  | ptr {l} :
    Poised (.ptr l)
  | null :
    Poised .null

lemma Resolved.normal_poisedX {H1 H2 H3 : Heap Srt} {a b c A} :
    [] ;; H1 ⊢ a ▷ b ◁ c :: A -> HMerge H1 H2 H3 ->
    Normal Step01 (H3, c) -> Poised c := by
  generalize e: [] = Δ
  intro ⟨er, rs⟩ mrg norm; induction er generalizing H1 H2 H3 c
  case var hs => subst_vars; cases hs
  case lam_im erm ihm =>
    subst_vars; cases c
    all_goals cases rs
    case lam rsm _ =>
      have ⟨_, _⟩ := H3.fresh
      have cl := erm.closed; simp at cl
      have cl := rsm.closed_preimage cl
      exfalso; apply norm
      constructor
      right; constructor
      assumption
      assumption
    case ptr => constructor
  case lam_ex erm ihm =>
    subst_vars
    cases c
    all_goals cases rs
    case lam rsm _ =>
      have ⟨_, _⟩ := H3.fresh
      have cl := erm.closed; simp at cl
      have cl := rsm.closed_preimage cl
      exfalso; apply norm
      constructor
      right; constructor
      assumption
      assumption
    case ptr => constructor
  case app_im erm ern ihm =>
    subst_vars; cases c
    all_goals cases rs
    case app m n H1 H2 mrg1 rsm rsn =>
      have ⟨ct, e⟩ := rsn.null_inv; subst e
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        constructor; assumption
        constructor
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.app_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.app_M
          assumption
    case ptr => constructor
  case app_ex mrg0 erm ern ihm ihn =>
    subst_vars; cases mrg0; cases c
    all_goals cases rs
    case app m n H1 H2 mrg1 rsm rsn =>
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        by_cases h2: ARS.Normal Step01 (Hx, n)
        case pos =>
          replace ihn := ihn rfl rsn mrg2 h2
          constructor <;> assumption
        case neg =>
          exfalso; apply norm
          simp[ARS.Normal] at h2
          rcases h2 with ⟨x, st⟩
          cases st with
          | inl st =>
            have ⟨Hx, _, st⟩ := st.merge mrg3
            constructor
            left; apply Step0.app_N
            assumption
          | inr st =>
            have ⟨Hx, _, st⟩ := st.merge mrg3
            constructor
            right; apply Step1.app_N
            assumption
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.app_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.app_M
          assumption
    case ptr => constructor
  case tup_im erm ern ihm =>
    subst_vars; cases c
    all_goals cases rs
    case tup m n H1 H2 mrg1 rsm rsn =>
      have ⟨ct, e⟩ := rsn.null_inv; subst e
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        by_cases h2: ∃ l, m = .ptr l
        case pos =>
          rcases h2 with ⟨l, e⟩; subst e
          exfalso; apply norm
          have ⟨_, _⟩ := H3.fresh
          constructor
          right; apply Step1.alloc_box
          assumption
        case neg =>
          constructor
          simp at h2; assumption
          assumption
          constructor
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.tup_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.tup_M
          assumption
    case ptr => constructor
  case tup_ex mrg0 _ erm ern ihm ihn =>
    subst_vars; cases mrg0; cases c
    all_goals cases rs
    case tup m n H1 H2 mrg1 rsm rsn =>
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        by_cases h2: ARS.Normal Step01 (Hx, n)
        case pos =>
          replace ihn := ihn rfl rsn mrg2 h2
          by_cases h2: ∃ l, m = .ptr l
          case pos =>
            rcases h2 with ⟨l, e⟩; subst e
            by_cases h3: Nullptr n
            case pos =>
              have ⟨_, _⟩ := H3.fresh
              exfalso; apply norm
              cases h3
              case ptr =>
                constructor
                right; apply Step1.alloc_tup
                assumption
              case null =>
                constructor
                right; apply Step1.alloc_box
                assumption
            case neg =>
              apply Poised.tup_N
              asimp at h3; assumption
              assumption
              assumption
          case neg =>
            constructor
            simp at h2; assumption
            assumption
            assumption
        case neg =>
          exfalso; apply norm
          simp[ARS.Normal] at h2
          rcases h2 with ⟨x, st⟩
          cases st with
          | inl st =>
            have ⟨Hx, _, st⟩ := st.merge mrg3
            constructor
            left; apply Step0.tup_N
            assumption
          | inr st =>
            have ⟨Hx, _, st⟩ := st.merge mrg3
            constructor
            right; apply Step1.tup_N
            assumption
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.tup_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.tup_M
          assumption
    case ptr => constructor
  case prj_im mrg0 _ erm ern ihm ihn =>
    subst_vars; cases mrg0; cases c
    all_goals cases rs
    case prj m n H1 H2 mrg1 rsm rsn =>
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        constructor; assumption
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.prj_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.prj_M
          assumption
    case ptr => constructor
  case prj_ex mrg0 _ erm ern ihm ihn =>
    subst_vars; cases mrg0; cases c
    all_goals cases rs
    case prj m n H1 H2 mrg1 rsm rsn =>
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        constructor; assumption
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.prj_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.prj_M
          assumption
    case ptr => constructor
  case tt =>
    subst_vars; cases c
    all_goals cases rs
    case tt =>
      have ⟨_, _⟩ := H3.fresh
      exfalso; apply norm
      constructor; right
      constructor; assumption
    case ptr => constructor
  case ff =>
    subst_vars; cases c
    all_goals cases rs
    case ff =>
      have ⟨_, _⟩ := H3.fresh
      exfalso; apply norm
      constructor; right
      constructor; assumption
    case ptr => constructor
  case ite mrg0 _ erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg0; cases c
    all_goals cases rs
    case ite m n1 n2 H1 H2 mrg1 rsm rsn1 rsn2 =>
      by_cases h1: ARS.Normal Step01 (H3, m)
      case pos =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg.split mrg1.sym
        replace ihm := ihm rfl rsm mrg3.sym h1
        constructor; assumption
      case neg =>
        exfalso; apply norm
        simp[ARS.Normal] at h1
        rcases h1 with ⟨x, st⟩
        cases st with
        | inl st =>
          constructor
          left; apply Step0.ite_M
          assumption
        | inr st =>
          constructor
          right; apply Step1.ite_M
          assumption
    case ptr => constructor
  case rw => subst_vars; aesop
  case drop mrg0 _ _ erm ern ihm ihn =>
    subst_vars; cases mrg0; cases c
    all_goals cases rs
    case drop H4 H5 mrg1 rsm rsn =>
      clear ihm ihn
      have ⟨Hx, mrg1, mrg2⟩ := mrg.split mrg1.sym
      have ⟨_, _,  dp, _⟩ := rsm.drop_safeX mrg2.sym
      exfalso; apply norm
      constructor; left
      constructor
      assumption
    case ptr => constructor
  case conv => subst_vars; aesop

lemma Resolved.normal_poised {H : Heap Srt} {a b c A} :
    [] ;; H ⊢ a ▷ b ◁ c :: A -> Normal Step01 (H, c) -> Poised c := by
  intro rs norm
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H
  apply rs.normal_poisedX mrg norm
