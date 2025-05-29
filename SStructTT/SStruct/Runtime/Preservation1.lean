import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
open ARS

namespace SStruct.Erasure
namespace Runtime
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Resolved.preservation1X {H1 H2 H3 H3' : Heap Srt} {a b c c' A} :
    HMerge H1 H2 H3 ->
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step1 (H3, c) (H3', c') ->
    ∃ H1' H2',
      HMerge H1' H2' H3' ∧ SubHeap H2 H2' ∧
      [] ;; [] ;; H1' ⊢ a ▷ b ◁ c' : A := by
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro mrg0 ⟨er, rs⟩ st; induction er generalizing H1 H2 H3 H3' c c'
  case var wf hs =>
    subst_vars; cases hs
  case lam_im A B m m' s sA i lw tyA erm ihm =>
    subst_vars; cases rs
    case lam x rsx hyp =>
      cases st
      case alloc_clo l h nf =>
        clear ihm
        have ⟨h1, h2⟩ := mrg0.split_none h
        if h3: s ∈ ord.contra_set then
          replace ct := hyp h3
          existsi H1.insert l (.clo x s nf), H2.insert l (.clo x s nf); and_intros
          . apply mrg0.insert_contra
            assumption
          . apply SubHeap.insert
            simp[<-Finmap.mem_keys,h2]
            assumption
          . constructor
            . apply Erased.lam_im <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . constructor
                intro; apply ct.insert; assumption
                simp[Cell.srt]
                apply rsx.insert_contra (by aesop) h1
        else
          existsi H1.insert l (.clo x s nf), H2; and_intros
          . apply mrg0.insert_left
            assumption
            assumption
          . apply SubHeap.refl
          . constructor
            . apply Erased.lam_im <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . simp[Heap.erase_insert,h1]
                constructor <;> assumption
    case ptr => cases st
  case lam_ex A B m m' s sA i lw tyA erm ihm =>
    subst_vars; cases rs
    case lam x rsx hyp =>
      cases st
      case alloc_clo l h nf =>
        have ⟨h1, h2⟩ := mrg0.split_none h
        if h3: s ∈ ord.contra_set then
          replace ct := hyp h3
          existsi H1.insert l (.clo x s nf), H2.insert l (.clo x s nf); and_intros
          . apply mrg0.insert_contra
            assumption
          . apply SubHeap.insert
            simp[<-Finmap.mem_keys,h2]
            assumption
          . constructor
            . apply Erased.lam_ex <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . constructor
                intro; apply ct.insert; assumption; rfl
                apply rsx.insert_contra (by aesop) h1
        else
          existsi H1.insert l (.clo x s nf), H2; and_intros
          . apply mrg0.insert_left
            assumption
            assumption
          . apply SubHeap.refl
          . constructor
            . apply Erased.lam_ex <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . simp[Heap.erase_insert,h1]
                constructor <;> assumption
    case ptr => cases st
  case app_im erm tyn ihm =>
    subst_vars; cases rs
    case app mrg1 rsm rsn =>
      cases st
      case app_M st =>
        have ⟨ct, e⟩ := rsn.null_inv; subst e
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg3.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hx, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hx, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . constructor <;> assumption
          . apply Resolve.app mrg1.sym
            assumption
            apply rsn.subheap sb1
      case app_N st =>
        cases rsn
        case ptr => cases st
        case null => cases st
    case ptr => cases st
  case app_ex mrg1 erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case app mrg2 rsm rsn =>
      cases st
      case app_M st =>
        clear ihn
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg3.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil <;> assumption
          . apply Resolve.app mrg1.sym
            assumption
            apply rsn.subheap sb1
      case app_N st =>
        clear ihm
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2
        have ⟨H1', H2', mrg', sb, ⟨ern', rsn'⟩⟩ := ihn rfl rfl mrg3.sym rsn st
        clear ihn
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.app_ex Merge.nil <;> assumption
          . apply Resolve.app mrg1
            apply rsm.subheap sb1
            assumption
    case ptr => cases st
  case tup_im s i ty erm tyn ihm =>
    subst_vars; cases rs
    case tup mrg1 rsm rsn =>
      cases st
      case tup_M st =>
        have ⟨ct, e⟩ := rsn.null_inv; subst e
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg1.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg3.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.tup_im <;> assumption
          . apply Resolve.tup mrg1.sym
            assumption
            apply rsn.subheap sb1
      case tup_N st =>
        cases rsn
        case ptr => cases st
        case null => cases st
      case alloc_box l l1 h =>
        have ⟨h1, h2⟩ := mrg0.split_none h
        have ⟨h1', h2'⟩ := mrg1.split_none h1
        if h3: s ∈ ord.contra_set then
          existsi H1.insert l (.box l1 s)
          existsi H2.insert l (.box l1 s)
          and_intros
          . apply mrg0.insert_contra
            assumption
          . apply SubHeap.insert
            simp[<-Finmap.mem_keys,h2]
            assumption
          . constructor
            . apply Erased.tup_im <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . apply Resolve.tup (mrg1.insert_contra (by aesop))
                apply rsm.insert_contra (by aesop) h1'
                apply rsn.insert_contra (by aesop) h2'
        else
          existsi H1.insert l (.box l1 s), H2; and_intros
          . apply mrg0.insert_left
            assumption
            assumption
          . apply SubHeap.refl
          . constructor
            . apply Erased.tup_im <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . simp[Heap.erase_insert,h1]
                apply Resolve.tup mrg1 <;> assumption
      case alloc_tup =>
        have ⟨_, e⟩ := rsn.null_inv; cases e
    case ptr => cases st
  case tup_ex s i mrg1 ty erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case tup mrg2 rsm rsn =>
      cases st
      case tup_M st =>
        clear ihn
        have ⟨Hx, mrg3, mrg4⟩ := mrg0.split mrg2.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg4.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg3p⟩ := mrg3.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg3p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil <;> assumption
          . apply Resolve.tup mrg1.sym
            assumption
            apply rsn.subheap sb1
      case tup_N st =>
        clear ihm
        have ⟨Hx, mrg3, mrg4⟩ := mrg0.split mrg2
        have ⟨H1', H2', mrg', sb, ⟨ern', rsn'⟩⟩ := ihn rfl rfl mrg4.sym rsn st
        clear ihn
        have ⟨H1p, H2p, sb1, sb2, mrg3p⟩ := mrg3.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg3p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.tup_ex Merge.nil <;> assumption
          . apply Resolve.tup mrg1
            apply rsm.subheap sb1
            assumption
      case alloc_box => sorry
      case alloc_tup l l1 l2 h =>
        have ⟨h1, h2⟩ := mrg0.split_none h
        have ⟨h1', h2'⟩ := mrg2.split_none h1
        if h3: s ∈ ord.contra_set then
          existsi H1.insert l (.tup l1 l2 s)
          existsi H2.insert l (.tup l1 l2 s)
          and_intros
          . apply mrg0.insert_contra
            assumption
          . apply SubHeap.insert
            simp[<-Finmap.mem_keys,h2]
            assumption
          . constructor
            . apply Erased.tup_ex Merge.nil <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . apply Resolve.tup (mrg2.insert_contra (by aesop))
                apply rsm.insert_contra (by aesop) h1'
                apply rsn.insert_contra (by aesop) h2'
        else
          existsi H1.insert l (.tup l1 l2 s), H2; and_intros
          . apply mrg0.insert_left
            assumption
            assumption
          . apply SubHeap.refl
          . constructor
            . apply Erased.tup_ex Merge.nil <;> assumption
            . apply Resolve.ptr
              . simp[HLookup]; and_intros
                . rfl
                . simp[Cell.srt,h3]; rfl
              . simp[Heap.erase_insert,h1]
                apply Resolve.tup mrg2 <;> assumption
    case ptr => cases st
  case prj_im mrg1 ty erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case prj mrg2 rsm rsn =>
      cases st
      case prj_M st =>
        clear ihn
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg3.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.prj_im Merge.nil <;> assumption
          . apply Resolve.prj mrg1.sym
            assumption
            apply rsn.subheap sb1
    case ptr => cases st
  case prj_ex mrg1 ty erm ern ihm ihn =>
    subst_vars; cases mrg1; cases rs
    case prj mrg2 rsm rsn =>
      cases st
      case prj_M st =>
        clear ihn
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg3.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.prj_ex Merge.nil <;> assumption
          . apply Resolve.prj mrg1.sym
            assumption
            apply rsn.subheap sb1
    case ptr => cases st
  case tt =>
    subst_vars; cases rs
    case tt ct =>
      cases st
      case alloc_tt l h =>
        have ⟨h1, h2⟩ := mrg0.split_none h
        existsi H1.insert l .tt
        existsi H2.insert l .tt
        and_intros
        . apply mrg0.insert_contra
          simp[Cell.srt]; apply ord.e_contra
        . apply SubHeap.intro (Finmap.singleton l .tt)
          apply Contra.empty.insert ord.e_contra (by aesop)
          rw[Finmap.Disjoint.eq_1]; intros; aesop
          apply Finmap.ext_lookup; intro x
          if e: x = l then
            subst_vars; simp[h2]
          else
            simp[e]
            rw[Finmap.lookup_union_left_of_not_in]
            simp[e]
        . constructor
          . constructor <;> assumption
          . apply Resolve.ptr (H2 := H1.insert l .tt)
            simp[HLookup]; and_intros
            . rfl
            . simp[Cell.srt,ord.e_contra]
            . constructor; apply ct.insert ord.e_contra; rfl
    case ptr => cases st
  case ff =>
    subst_vars; cases rs
    case ff ct =>
      cases st
      case alloc_ff l h =>
        have ⟨h1, h2⟩ := mrg0.split_none h
        existsi H1.insert l .ff
        existsi H2.insert l .ff
        and_intros
        . apply mrg0.insert_contra
          simp[Cell.srt]; apply ord.e_contra
        . apply SubHeap.intro (Finmap.singleton l .ff)
          apply Contra.empty.insert ord.e_contra (by aesop)
          rw[Finmap.Disjoint.eq_1]; intros; aesop
          apply Finmap.ext_lookup; intro x
          if e: x = l then
            subst_vars; simp[h2]
          else
            simp[e]
            rw[Finmap.lookup_union_left_of_not_in]
            simp[e]
        . constructor
          . constructor <;> assumption
          . apply Resolve.ptr (H2 := H1.insert l .ff)
            simp[HLookup]; and_intros
            . rfl
            . simp[Cell.srt,ord.e_contra]
            . constructor; apply ct.insert ord.e_contra; rfl
    case ptr => cases st
  case ite mrg1 ty erm ern1 ern2 ihm ihn1 ihn2 =>
    subst_vars; cases mrg1; cases rs
    case ite mrg2 rsm rsn1 rsn2 =>
      cases st
      case ite_M st =>
        clear ihn1 ihn2
        have ⟨Hx, mrg2, mrg3⟩ := mrg0.split mrg2.sym
        have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ihm rfl rfl mrg3.sym rsm st
        clear ihm
        have ⟨H1p, H2p, sb1, sb2, mrg2p⟩ := mrg2.split_subheap sb
        have ⟨Hy, mrg1, mrg2⟩ := mrg'.sym.split mrg2p
        existsi Hy, H2p; and_intros
        . assumption
        . assumption
        . constructor
          . apply Erased.ite Merge.nil <;> assumption
          . apply Resolve.ite mrg1.sym
            assumption
            apply rsn1.subheap sb1
            apply rsn2.subheap sb1
    case ptr => cases st
  case rw tyA erm tyn ih =>
    subst_vars
    have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ih rfl rfl mrg0 rs st
    existsi H1', H2'; and_intros
    . assumption
    . assumption
    . constructor
      . apply Erased.rw tyA
        assumption
        assumption
      . assumption
  case drop A B s mrg lw h erm ern ihm ihn =>
    subst_vars; cases mrg; cases rs
    case drop => cases st
    case ptr => cases st
  case conv eq erm tyB ih =>
    subst_vars
    have ⟨H1', H2', mrg', sb, ⟨erm', rsm'⟩⟩ := ih rfl rfl mrg0 rs st
    existsi H1', H2'; and_intros
    . assumption
    . assumption
    . constructor
      . apply Erased.conv eq
        assumption
        assumption
      . assumption

lemma Resolved.preservation1 {H1 H2 : Heap Srt} {a b c c' A} :
    [] ;; [] ;; H1 ⊢ a ▷ b ◁ c : A -> Step1 (H1, c) (H2, c') ->
    [] ;; [] ;; H2 ⊢ a ▷ b ◁ c' : A := by
  intro rsm st
  have ⟨H0, mrg, ct⟩ := HMerge.exists_self_contra H1
  have ⟨H1', H2', mrg', sb, rsm'⟩ := rsm.preservation1X mrg st
  have ct := sb.contra_image ct
  have e := mrg'.self_contra ct; subst e
  assumption

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
    apply rs'.preservation1 st
