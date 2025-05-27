import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

def Pad (H1 H2 : Heap Srt) : Prop :=
  ∃ H0, Contra H0 ∧ Finmap.Disjoint H1 H0 ∧ H2 = H1 ∪ H0

lemma Pad.refl (H : Heap Srt) : Pad H H := by
  exists ∅; and_intros
  apply Contra.empty
  apply Finmap.Disjoint.symm
  apply Finmap.disjoint_empty
  simp

lemma Pad.insert (H : Heap Srt) l m s :
    l ∉ H -> s ∈ ord.contra_set -> Pad H (H.insert l (m, s)) := by
  intro h1 h2
  exists Finmap.singleton l (m, s); and_intros
  . intro x
    if e: x = l then
      subst_vars; simp
      assumption
    else
      rw[<-Finmap.mem_singleton x l (m, s) (β := fun _ => Tm Srt × Srt)] at e
      rw[Finmap.mem_iff] at e
      split <;> try aesop
  . rw[Finmap.Disjoint.eq_1]
    intro x h0 h1
    simp at h1; subst h1
    contradiction
  . apply Finmap.ext_lookup; intro x
    if e: x = l then
      subst_vars; simp[h1]
    else
      simp[e]
      rw[Finmap.lookup_union_left_of_not_in]
      intro h; simp at h
      contradiction

lemma Contra.union (H1 H2 : Heap Srt) : Contra H1 -> Contra H2 -> Contra (H1 ∪ H2) := by
  intro ct1 ct2 x
  replace ct1 := ct1 x
  replace ct2 := ct2 x
  split <;> try trivial
  case h_1 heq =>
    simp at heq
    cases heq <;> aesop

lemma Pad.contra (H1 H2 : Heap Srt) : Pad H1 H2 -> Contra H1 -> Contra H2 := by
  intro pd c1
  rcases pd with ⟨H0, ct, dsj, mrg⟩
  rw[mrg]
  apply Contra.union <;> assumption

lemma HMerge.split_disjoint' {H0 H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> H3.Disjoint H0 -> H1.Disjoint H0 := by
  intro mrg dsj
  rw[Finmap.Disjoint.eq_1]; intro x h
  have e := mrg.lookup_collision h
  rw[Finmap.mem_iff] at h; rw[e] at h
  rw[<-Finmap.mem_iff (s := H3)] at h
  aesop

lemma HMerge.split_disjoint {H0 H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> H3.Disjoint H0 -> H1.Disjoint H0 ∧ H2.Disjoint H0 := by
  intro mrg dsj; and_intros
  apply mrg.split_disjoint' dsj
  apply mrg.sym.split_disjoint' dsj

lemma Pad.split {H1 H2 H3 H3p : Heap Srt} :
    Pad H3 H3p -> HMerge H1 H2 H3 ->
    ∃ H1p H2p, Pad H1 H1p ∧ Pad H2 H2p ∧ HMerge H1p H2p H3p := by
  intro ⟨H0, ct, dsj, un⟩ mrg; subst_vars
  have ⟨dsj1, dsj2⟩ := mrg.split_disjoint dsj
  exists H1 ∪ H0, H2 ∪ H0; and_intros
  . exists H0
  . exists H0
  . apply HMerge.contra_union

/-

lemma Resolved.preservation1 {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 -> WR H2 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step1 (H3, c) (H3', c') ->
    ∃ H1' H2',
      HMerge H1' H2' H3' ∧ WR H2' ∧ Pad H2 H2' ∧
      [] ;; [] ;; H1' ⊢ a ▷ b ◁ c' : A := by
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
        clear ihm
        cases vl
        sorry
    case ptr =>
      cases st
      case alloc vl => cases vl
  case lam_ex A B m m' s sA i lw tyA erm ihm =>
    subst_vars; cases rs
    case lam x rsx lwx =>
      cases st
      case alloc s l h vl =>
        cases vl
        have ⟨h1, h2⟩ := mrg0.split_none h
        have nfm := erm.nf; simp at nfm
        have nfx := rsx.nf_preimage wr1 nfm
        if h3: s ∈ ord.contra_set then
          replace lwx := lwx h3
          exists H1.insert l (x.lam s, s), H2.insert l (x.lam s, s); and_intros
          . apply mrg0.insert_contra
            assumption
          . apply wr2.insert_lam nfx
          . apply Pad.insert
            simp[<-Finmap.mem_keys,h2]
            assumption
          . constructor
            . apply Erased.lam_ex <;> assumption
            . apply Resolve.ptr
              . unfold HLookup
                simp[h3]; aesop
              . constructor
                intro; apply lwx.insert; assumption
                sorry
            . apply wr1.insert_lam nfx
        else
          exists H1.insert l (x.lam s, s), H2; and_intros
          . apply mrg0.insert_left
            assumption
            assumption
          . assumption
          . apply Pad.refl
          . constructor
            . apply Erased.lam_ex <;> assumption
            . apply Resolve.ptr
              pick_goal 2
              . constructor <;> assumption
              . unfold HLookup
                simp[h3,Heap.erase_insert,h1]
            . apply wr1.insert_lam nfx
    case ptr =>
      cases st
      case alloc vl => cases vl
  all_goals sorry

/-
  case app_im erm tyn ihm =>
    subst_vars; cases rs
    case app mrg1 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg1.split_wr wr1
      cases st
      case app_M st =>
        have ⟨lw, e⟩ := rsn.null_inv wr2'; subst e
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . apply Resolve.app mrg1'.sym
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case app_N st =>
        cases rsn
        case ptr =>
          cases st
          case alloc vl => cases vl
        case null =>
          cases st
          case alloc vl => cases vl
      case alloc vl => cases vl
    case ptr =>
      cases st
      case alloc vl => cases vl
  case app_ex mrg1 erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case app mrg2 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg2.split_wr wr1
      cases st
      case app_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil <;> assumption
          . apply Resolve.app mrg1'.sym
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case app_N st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2
        have wrx := mrg2.merge_wr wr1' wr2
        have ⟨H1', mrg', ⟨ern', rsn', wr'⟩⟩ := ihn rfl rfl mrg3.sym wrx rsn wr2' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil <;> assumption
          . apply Resolve.app mrg1'
            assumption
            assumption
          . apply mrg1'.merge_wr wr1' wr'
      case alloc vl => cases vl
    case ptr =>
      cases st
      case alloc vl => cases vl
  case tup_im s i ty erm tyn ihm =>
    subst_vars; cases rs
    case tup mrg1 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg1.split_wr wr1
      cases st
      case tup_M st =>
        have ⟨lw, e⟩ := rsn.null_inv wr2'; subst e
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . constructor <;> assumption
          . apply Resolve.tup mrg1'.sym
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case tup_N st =>
        cases rsn
        case ptr =>
          cases st
          case alloc vl => cases vl
        case null =>
          cases st
          case alloc vl => cases vl
      case alloc l h vl =>
        have ⟨h1, h2⟩ := mrg0.split_none h
        cases vl
        case tup l1 np =>
          cases np
          case ptr =>
            have ⟨_, _⟩ := rsn.null_inv wr2'
            contradiction
          case null =>
            exists H1.insert l (.tup (.ptr l1) .null s, s); and_intros
            . apply mrg0.insert_left l
              assumption
            . constructor
              . constructor <;> assumption
              . apply Resolve.ptr h1
                constructor <;> assumption
              . apply wr1.insert_tup
                constructor
    case ptr =>
      cases st
      case alloc vl => cases vl
  case tup_ex s i mrg1 ty erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case tup mrg2 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg2.split_wr wr1
      cases st
      case tup_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil <;> assumption
          . apply Resolve.tup mrg1'.sym
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case tup_N st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2
        have wrx := mrg2.merge_wr wr1' wr2
        have ⟨H1', mrg', ⟨ern', rsn', wr'⟩⟩ := ihn rfl rfl mrg3.sym wrx rsn wr2' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil <;> assumption
          . apply Resolve.tup mrg1'
            assumption
            assumption
          . apply mrg1'.merge_wr wr1' wr'
      case alloc vl =>
        cases vl
        case tup l h l1 np =>
          have ⟨h1, h2⟩ := mrg0.split_none h
          cases np
          case ptr l2 =>
            exists H1.insert l (.tup (.ptr l1) (.ptr l2) s, s); and_intros
            . apply mrg0.insert_left l
              assumption
            . constructor
              . apply Erased.tup_ex Merge.nil <;> assumption
              . apply Resolve.ptr h1
                constructor <;> assumption
              . apply wr1.insert_tup
                constructor
          case null =>
            cases rsn
            exfalso; apply ern.null_preimage
    case ptr =>
      cases st
      case alloc vl => cases vl
  case prj_im mrg1 ty erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case prj mrg2 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg2.split_wr wr1
      cases st
      case prj_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.prj_im Merge.nil <;> assumption
          . apply Resolve.prj mrg1'.sym
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case alloc vl => cases vl
    case ptr =>
      cases st
      case alloc vl => cases vl
  case prj_ex mrg1 ty erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case prj mrg2 rsm rsn =>
      have ⟨wr1', wr2'⟩ := mrg2.split_wr wr1
      cases st
      case prj_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.prj_ex Merge.nil <;> assumption
          . apply Resolve.prj mrg1'.sym
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case alloc vl => cases vl
    case ptr =>
      cases st
      case alloc vl => cases vl
  case tt =>
    subst_vars; cases rs
    case tt =>
      cases st
      case alloc s l h vl =>
        cases vl
        have ⟨h1, h2⟩ := mrg0.split_none h
        exists H1.insert l (.tt, ord.e); and_intros
        . apply mrg0.insert_left
          assumption
        . constructor
          . constructor <;> assumption
          . apply Resolve.ptr h1
            constructor; assumption
          . apply wr1.insert_tt
    case ptr =>
      cases st
      case alloc vl => cases vl
  case ff =>
    subst_vars; cases rs
    case ff =>
      cases st
      case alloc s l h vl =>
        cases vl
        have ⟨h1, h2⟩ := mrg0.split_none h
        exists H1.insert l (.ff, ord.e); and_intros
        . apply mrg0.insert_left
          assumption
        . constructor
          . constructor <;> assumption
          . apply Resolve.ptr h1
            constructor; assumption
          . apply wr1.insert_ff
    case ptr =>
      cases st
      case alloc vl => cases vl
  case ite mrg1 ty erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg1; cases rs
    case ite mrg2 rsm rsn1 rsn2 =>
      have ⟨wr1', wr2'⟩ := mrg2.split_wr wr1
      cases st
      case ite_M st =>
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have wrx := mrg2.merge_wr wr2' wr2
        have ⟨H1', mrg', ⟨erm', rsm', wr'⟩⟩ := ihm rfl rfl mrg3.sym wrx rsm wr1' st
        have ⟨H2', mrg1', mrg2'⟩ := mrg'.sym.split mrg2
        exists H2'; and_intros
        . assumption
        . constructor
          . apply Erased.ite Merge.nil <;> assumption
          . apply Resolve.ite mrg1'.sym
            assumption
            assumption
            assumption
          . apply mrg1'.merge_wr wr2' wr'
      case alloc vl => cases vl
    case ptr =>
      cases st
      case alloc vl => cases vl
  case rw tyA erm tyn ih =>
    subst_vars
    have ⟨H1', mrg', ⟨er', rs', wr'⟩⟩ := ih rfl rfl mrg0 wr2 rs wr1 st
    exists H1'; and_intros
    . assumption
    . constructor
      . apply Erased.rw tyA
        assumption
        assumption
      . assumption
      . assumption
  case drop A B s mrg lw h erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case drop =>
      cases st
      case alloc vl => cases vl
    case ptr =>
      cases st
      case alloc vl => cases vl
  case conv eq erm tyB ih =>
    subst_vars
    have ⟨H1', mrg', ⟨er', rs', wr'⟩⟩ := ih rfl rfl mrg0 wr2 rs wr1 st
    exists H1'; and_intros
    . assumption
    . constructor
      . apply Erased.conv eq
        assumption
        assumption
      . assumption
      . assumption

lemma Resolved.preservation1' {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 -> WR H2 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Red1 (H3, c) (H3', c') ->
    ∃ H1', HMerge H1' H2 H3' ∧ [] ;; [] ;; H1' ⊢ a ▷ b ◁ c' : A := by
  generalize e: (H3', c') = t
  intro mrg wr rs rd; induction rd generalizing H1 H2 H3' a b c' A
  case R => cases e; exists H1
  case SE x y rd st ih =>
    subst_vars
    rcases x with ⟨H2, c'⟩
    replace ⟨H1, mrg1, rs1⟩ := ih rfl mrg wr rs
    have ⟨H2, mrg2, st2⟩ := rs1.preservation1 mrg1 wr st
    exists H2

-/

lemma Resolved.preservation1X {H1 H2 : Heap Srt} {a b c c' A} :
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step1 (H1, c) (H2, c') ->
    [] ;; [] ;; H2 ⊢ a ▷ b ◁ c' : A := by
  intro rsm st
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H1
  have ⟨_, _, wr⟩ := rsm
  have wr0 := mrg.sym.split_wr' wr
  have ⟨H1', H2', mrg', wr', pd, rsm'⟩ := rsm.preservation1 mrg wr0 st
  have ct := pd.contra _ _ ct
  sorry
  -- have e := mrg'.sym.contra ct; subst e
  -- assumption

lemma Resolved.preservation1' {H1 H2 : Heap Srt} {a b c c' A} :
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Red1 (H1, c) (H2, c') ->
    [] ;; [] ;; H2 ⊢ a ▷ b ◁ c' : A := by
  generalize e: (H2, c') = t
  intro rs rd; induction rd generalizing H2 a b c' A
  case R => cases e; assumption
  case SE y z rd st ih =>
    subst_vars
    rcases y with ⟨H2, c'⟩
    replace rs' := ih rfl rs
    apply rs'.preservation1X st

-/
