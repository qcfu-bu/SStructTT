import SStructTT.SStruct.Static.Inversion
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Erasure.Step
import SStructTT.SStruct.Erasure.Inversion

namespace SStruct.Erasure
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

namespace Runtime

inductive Resolve : Heap Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {H x} :
    Shareable H ->
    Resolve H (.var x) (.var x)

  | lam {H m m' s} :
    (s ∈ ord.contra_set -> Shareable H) ->
    Resolve H m m' ->
    Resolve H (.lam m s) (.lam m' s)

  | app {H1 H2 H3 m m' n n'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.app m n) (.app m' n')

  | tup {H1 H2 H3 m m' n n' s} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.tup m n s) (.tup m' n' s)

  | prj {H1 H2 H3 m m' n n'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.prj m n) (.prj m' n')

  | tt {H} :
    Shareable H ->
    Resolve H .tt .tt

  | ff {H} :
    Shareable H ->
    Resolve H .ff .ff

  | ite {H1 H2 H3 m m' n1 n1' n2 n2'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n1 n1' ->
    Resolve H2 n2 n2' ->
    Resolve H3 (.ite m n1 n2) (.ite m' n1' n2')

  | drop {H1 H2 H3 m m' n n'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.drop m n) (.drop m' n')

  | ptr {H1 H2 l m m'} :
    HAccess H1 l m H2 ->
    Resolve H2 m.tm m' ->
    Resolve H1 (.ptr l) m'

  | null {H} :
    Shareable H ->
    Resolve H .null .null

notation:50 H:50 " ;; " m:51 " ▷ " m':51 => Resolve H m m'

@[simp]def IsResolved : Tm Srt -> Prop
  | .var _ => True
  | .lam m _ => IsResolved m
  | .app m n => IsResolved m ∧ IsResolved n
  | .tup m n _ => IsResolved m ∧ IsResolved n
  | .prj m n => IsResolved m ∧ IsResolved n
  | .tt => True
  | .ff => True
  | .ite m n1 n2 => IsResolved m ∧ IsResolved n1 ∧ IsResolved n2
  | .drop m n => IsResolved m ∧ IsResolved n
  | .ptr _ => False
  | .null => True

lemma Resolve.is_resolved {H : Heap Srt} {m m'} : H ;; m ▷ m' -> IsResolved m' := by
  intro rs; induction rs
  all_goals aesop

inductive Resolved :
  Ctx Srt -> Heap Srt -> SStruct.Tm Srt -> Tm Srt -> Tm Srt -> SStruct.Tm Srt -> Prop
where
  | intro {Δ H x y z A} :
    Δ ⊢ x ▷ y :: A -> H ;; z ▷ y -> Resolved Δ H x y z A

notation:50 Δ:50 " ;; " H:51 " ⊢ " x:51 " ▷ " y:51 " ◁ " z:81 " :: " A:51 =>
  Resolved Δ H x y z A

lemma HAccess.lookup {H1 H2 : Heap Srt} {l m} :
    HAccess H1 l m H2 ->
    if m.srt ∈ ord.contra_set then H2 = H1 else H2 = H1.erase l := by
  intro lk
  unfold HAccess at lk; split at lk <;> aesop

lemma HAccess.not_mem {H1 H2 : Heap Srt} {l1 l2 m} :
    HAccess H1 l1 m H2 -> l2 ∉ H1 -> l2 ∉ H2 := by
  intro lk h
  rw[HAccess] at lk
  rw[<-Finmap.lookup_eq_none] at h
  rw[<-Finmap.lookup_eq_none]
  split at lk <;> try trivial
  case h_1 opt m' e =>
    have ⟨_, h⟩ := lk; split_ifs at h
    case pos => subst_vars; assumption
    case neg =>
      subst_vars
      cases l2.decEq l1 with
      | isTrue => subst_vars; apply Finmap.lookup_erase
      | isFalse ne => rw[Finmap.lookup_erase_ne ne]; assumption

lemma HAccess.insert {H1 H2 : Heap Srt} {l1 l2 m n} :
    HAccess H1 l1 m H2 -> l2 ∉ H1 ->
    HAccess (H1.insert l2 n) l1 m (H2.insert l2 n) := by
  intro lk h
  rw[<-Finmap.lookup_eq_none] at h
  rw[HAccess]
  cases l1.decEq l2 with
  | isTrue =>
    subst_vars
    rw[HAccess] at lk
    rw[h] at lk; simp at lk
  | isFalse ne =>
    rw[H1.lookup_insert_of_ne ne]
    rw[HAccess] at lk
    split at lk <;> try trivial
    replace ⟨_, lk⟩ := lk; subst_vars; simp
    split_ifs at lk <;> try simp_all
    apply Finmap.ext_lookup
    intro x
    cases x.decEq l2 with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]
      rw[Finmap.lookup_erase_ne (by aesop)]
      rw[Finmap.lookup_insert]
    | isFalse ne2 =>
      rw[Finmap.lookup_insert_of_ne _ ne2]
      cases x.decEq l1 with
      | isTrue =>
        subst_vars
        rw[Finmap.lookup_erase]
        rw[Finmap.lookup_erase]
      | isFalse ne1 =>
        repeat rw[Finmap.lookup_erase_ne ne1]
        rw[Finmap.lookup_insert_of_ne _ ne2]

lemma HAccess.insert_lookup {H H' : Heap Srt} {l m n} :
    HAccess (H.insert l m) l n H' ->
    m = n ∧
      if m.srt ∈ ord.contra_set
      then H' = H.insert l m
      else H' = H.erase l := by
  intro lk
  simp_rw[HAccess,Finmap.lookup_insert] at lk
  replace ⟨_, lk⟩ := lk; subst_vars; simp
  split_ifs at lk
  case pos h => simp[h]; aesop
  case neg h =>
    simp[h,lk]
    apply Finmap.ext_lookup
    intro x
    cases x.decEq l with
    | isTrue => subst_vars; repeat rw[Finmap.lookup_erase]
    | isFalse ne =>
      repeat rw[Finmap.lookup_erase_ne ne]
      rw[Finmap.lookup_insert_of_ne _ ne]

lemma HAccess.merge {H1 H1' H2 H3 : Heap Srt} {l m} :
    HAccess H1 l m H1' -> HMerge H1 H2 H3 ->
    ∃ H3', HAccess H3 l m H3' ∧ HMerge H1' H2 H3' := by
  intro lk mrg
  rw[HAccess] at lk; split at lk <;> try trivial
  case h_1 opt n e =>
    replace ⟨_, lk⟩ := lk; subst_vars
    split_ifs at lk
    case pos h =>
      subst_vars
      existsi H3; and_intros
      . replace mrg := mrg l
        rw[e] at mrg; split at mrg <;> try trivial
        case h_1 e h2 h3 =>
          rcases mrg with ⟨_, _, _⟩
          cases e; subst_vars
          unfold HAccess
          simp_rw[h3]; simp[h]
        case h_2 e h2 h3 =>
          rcases mrg with ⟨_, _, _⟩
          cases e
          unfold HAccess
          simp_rw[h3]; simp[h]
      . assumption
    case neg h =>
      subst_vars
      existsi H3.erase l; and_intros
      . replace mrg := mrg l
        rw[e] at mrg; split at mrg <;> try trivial
        case h_1 e h2 h3 =>
          rcases mrg with ⟨_, _, _⟩
          cases e; subst_vars
          unfold HAccess
          simp_rw[h3]; simp[h]
        case h_2 e h2 h3 =>
          rcases mrg with ⟨_, _, _⟩
          cases e
          unfold HAccess
          simp_rw[h3]; simp[h]
      . intro x
        replace mrg := mrg x
        cases x.decEq l with
        | isTrue =>
          subst_vars
          rw[e] at mrg; split at mrg <;> try trivial
          case h_1 e _ _ =>
            rcases mrg with ⟨_, _, _⟩
            cases e; subst_vars
            contradiction
          case h_2 e h1 h2 =>
            rcases mrg with ⟨_, _⟩
            cases e; simp[h1]
        | isFalse ne =>
          simp[Finmap.lookup_erase_ne ne]
          assumption

lemma HAccess.shareable_image {H H' : Heap Srt} {l m} :
    HAccess H l m H' -> Shareable H -> Shareable H' := by
  intro lk
  unfold HAccess at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk; subst_vars
  split_ifs at lk <;> subst_vars
  . simp
  . intro ct; apply ct.erase

lemma HAccess.unique {H0 H1 H2 : Heap Srt} {l m1 m2} :
    HAccess H0 l m1 H1 -> HAccess H0 l m2 H2 -> m1 = m2 ∧ H1 = H2 := by
  intro lk1 lk2
  unfold HAccess at lk1
  unfold HAccess at lk2
  split at lk1 <;> try trivial
  split at lk2 <;> aesop

lemma HAccess.collision {H1 H1' H2 H3 H3' : Heap Srt} {l m n} :
    HMerge H1 H2 H3 ->
    HAccess H3 l m H3' ->
    HAccess H1 l n H1' ->
    m = n ∧ HMerge H1' H2 H3' := by
  intro mrg lk1 lk2
  unfold HAccess at lk1 lk2
  split at lk1 <;> try trivial
  split at lk2 <;> try trivial
  replace ⟨_, lk1⟩ := lk1; subst_vars
  replace ⟨_, lk2⟩ := lk2; subst_vars
  case h_1 h1 _ _ h2 =>
    have h := Finmap.mem_of_lookup_eq_some h2
    have e := mrg.lookup_collision h
    rw[h1,h2] at e; cases e; simp
    split_ifs at lk1 <;> simp_all
    intro x; replace mrg := mrg x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      simp[Finmap.lookup_erase]
      simp[h1,h2] at mrg
      split at mrg <;> simp_all
    | isFalse ne =>
      simp[Finmap.lookup_erase_ne ne]
      assumption

lemma HAccess.closed {H H' : Heap Srt} {l m} :
    HAccess H l m H' -> Closed 0 m.tm := by
  intro lk
  unfold HAccess at lk; split at lk <;> try trivial
  case h_1 m' h =>
    replace ⟨_, lk⟩ := lk; subst_vars
    split_ifs at lk
    case pos =>
      subst_vars; cases m'
      all_goals simp_all[Cell.tm]
    case neg =>
      subst_vars; cases m'
      all_goals simp_all[Cell.tm]

lemma HAccess.value {H H' : Heap Srt} {l m} :
    HAccess H l m H' -> Value m.tm := by
  intro lk
  revert lk
  unfold HAccess
  generalize H.lookup l = r
  split <;> simp[Cell.tm]; aesop

lemma HAccess.disjoint_image {H0 H1 H2 : Heap Srt} {l m} :
    HAccess H1 l m H2 -> H1.Disjoint H0 -> H2.Disjoint H0 := by
  intro lk dsj
  unfold HAccess at lk; split at lk <;> try trivial
  case h_1 heq =>
    rcases lk with ⟨_, ifq⟩; subst_vars
    split_ifs at ifq
    . aesop
    . rw[Finmap.Disjoint.eq_1]
      rw[Finmap.Disjoint.eq_1] at dsj
      aesop

lemma HAccess.disjoint_union {H0 H1 H2 : Heap Srt} {l m} :
    HAccess H1 l m H2 -> H1.Disjoint H0 ->
    HAccess (H1 ∪ H0) l m (H2 ∪ H0) := by
  intro lk dsj
  rw[Finmap.Disjoint.eq_1] at dsj
  unfold HAccess at lk; split at lk <;> try trivial
  unfold HAccess
  case h_1 heq =>
    have mm := Finmap.mem_of_lookup_eq_some heq
    have nn := dsj _ mm
    rw[Finmap.lookup_union_left,heq]; simp
    rcases lk with ⟨_, ifq⟩; split at ifq <;> subst_vars
    case isTrue => simp; intro; contradiction
    case isFalse h =>
      simp[h]
      apply Finmap.ext_lookup; intro x
      if e: x = l then
        subst_vars; simp
        rw[Finmap.lookup_eq_none]
        apply dsj
        apply Finmap.mem_of_lookup_eq_some
        assumption
      else aesop
    aesop

lemma Erased.resolve_id {Δ} {H : Heap Srt} {x y z A} :
    Δ ⊢ x ▷ y :: A -> H ;; y ▷ z -> y = z := by
  intro ty rs; induction ty generalizing H z
  case var => cases rs; simp
  case lam_im => cases rs; aesop
  case lam_ex => cases rs; aesop
  case app_im ih =>
    cases rs
    case app rsn =>
      cases rsn; aesop
  case app_ex => cases rs; aesop
  case tup_im =>
    cases rs
    case tup rsm _ =>
      cases rsm; aesop
  case tup_ex => cases rs; aesop
  case prj_im => cases rs; aesop
  case prj_ex => cases rs; aesop
  case tt => cases rs; simp
  case ff => cases rs; simp
  case ite => cases rs; aesop
  case rw => aesop
  case drop => cases rs; aesop
  case conv => aesop

lemma Resolve.closed_image {H : Heap Srt} {m m' i} :
    H ;; m ▷ m' -> Closed i m -> Closed i m' := by
  intro rs cl; induction rs generalizing i
  all_goals try (solve|simp_all)
  case ptr H1 H2 l m m' lk erm ihm =>
    cases m <;> simp_all[Cell.tm]
    case clo cl =>
      apply ihm
      apply cl.weaken (by simp)

lemma Resolve.closed_preimage {H : Heap Srt} {m m' i} :
    H ;; m ▷ m' -> Closed i m' -> Closed i m := by
  intro rs cl; induction rs generalizing i
  all_goals simp_all

lemma Resolve.insert_shareable {H : Heap Srt} {l m m' v} :
    H ;; m ▷ m' -> v.srt ∈ ord.contra_set -> l ∉ H ->
    H.insert l v ;; m ▷ m' := by
  intro rs h nn; induction rs
  case var ct => constructor; apply ct.insert h; rfl
  case lam hyp rsm ih =>
    constructor
    . intro h0; apply (hyp h0).insert h; rfl
    . aesop
  case app mrg rsm rsn ihm ihn =>
    have ⟨nn1, nn2⟩ := mrg.split_none nn
    replace ihm := ihm nn1
    replace ihn := ihn nn2
    constructor
    apply mrg.insert_shareable h
    assumption
    assumption
  case tup mrg rsm rsn ihm ihn =>
    have ⟨nn1, nn2⟩ := mrg.split_none nn
    replace ihm := ihm nn1
    replace ihn := ihn nn2
    constructor
    apply mrg.insert_shareable h
    assumption
    assumption
  case prj mrg rsm rsn ihm ihn =>
    have ⟨nn1, nn2⟩ := mrg.split_none nn
    replace ihm := ihm nn1
    replace ihn := ihn nn2
    constructor
    apply mrg.insert_shareable h
    assumption
    assumption
  case tt ct => constructor; apply ct.insert h; rfl
  case ff ct => constructor; apply ct.insert h; rfl
  case ite mrg rsm rsn1 rsn2 ihm ihn1 ihn2 =>
    have ⟨nn1, nn2⟩ := mrg.split_none nn
    replace ihm := ihm nn1
    replace ihn1 := ihn1 nn2
    replace ihn2 := ihn2 nn2
    constructor
    apply mrg.insert_shareable h
    assumption
    assumption
    assumption
  case drop mrg rsm rsn ihm ihn =>
    have ⟨nn1, nn2⟩ := mrg.split_none nn
    replace ihm := ihm nn1
    replace ihn := ihn nn2
    constructor
    apply mrg.insert_shareable h
    assumption
    assumption
  case ptr lk rs ih =>
    have nn2 := lk.not_mem nn
    replace ih := ih nn2
    constructor
    . apply lk.insert nn
    . assumption
  case null ct => constructor; apply ct.insert h; rfl

lemma Resolve.merge_shareable {H1 H2 H3 : Heap Srt} {m m'} :
    HMerge H1 H2 H3 -> Shareable H2 -> H1 ;; m ▷ m' -> H3 ;; m ▷ m' := by
  intro mrg ct2 rsm; induction rsm generalizing H2 H3
  case var H1 x ct1 =>
    have ct := mrg.shareable_image ct1 ct2
    constructor; assumption
  case lam ct1 rsm ihm =>
    replace ihm := ihm mrg ct2
    constructor
    . intro h
      replace ct1 := ct1 h
      apply mrg.shareable_image ct1 ct2
    . assumption
  case app Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have mrg2 := ct2.merge_refl
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga ct2
    replace ihn := ihn mrgb ct2
    constructor <;> assumption
  case tup Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have mrg2 := ct2.merge_refl
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga ct2
    replace ihn := ihn mrgb ct2
    constructor <;> assumption
  case prj Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have mrg2 := ct2.merge_refl
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga ct2
    replace ihn := ihn mrgb ct2
    constructor <;> assumption
  case tt ct1 =>
    have ct := mrg.shareable_image ct1 ct2
    constructor; assumption
  case ff ct1 =>
    have ct := mrg.shareable_image ct1 ct2
    constructor; assumption
  case ite Ha Hb H1 _ _ _ _ _ _ mrg1 rsm rsn1 rsn2 ihm ihn1 ihn2 =>
    have mrg2 := ct2.merge_refl
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga ct2
    replace ihn1 := ihn1 mrgb ct2
    replace ihn2 := ihn2 mrgb ct2
    constructor <;> assumption
  case drop Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have ⟨Hc, mrg2, mrg3⟩ := mrg.split mrg1.sym
    replace ihn := ihn mrg2 ct2
    apply Resolve.drop mrg3.sym <;> assumption
  case ptr l m m' lk rsm ih =>
    have ⟨H, lk, mrg1⟩ := lk.merge mrg
    replace ih := ih mrg1 ct2
    constructor <;> assumption
  case null ct1 =>
    have lw := mrg.shareable_image ct1 ct2
    constructor; assumption

lemma Resolve.subheap {H1 H2 : Heap Srt} {m m'} :
    H1 ;; m ▷ m' -> SubHeap H1 H2 -> H2 ;; m ▷ m' := by
  intro rs sb; induction rs generalizing H2
  case var ct =>
    rcases sb with ⟨H0, ct0, dsj, un⟩; subst un
    constructor; apply ct.union ct0
  case lam hyp rsm ih =>
    constructor
    . intro h
      replace hyp := hyp h
      apply sb.shareable_image hyp
    . aesop
  case app mrg rsm rsn ihm ihn =>
    have ⟨H1p, H2p, sb1, sb2, mrg⟩ := mrg.split_subheap sb
    constructor <;> aesop
  case tup mrg rsm rsn ihm ihn =>
    have ⟨H1p, H2p, sb1, sb2, mrg⟩ := mrg.split_subheap sb
    constructor <;> aesop
  case prj mrg rsm rsn ihm ihn =>
    have ⟨H1p, H2p, sb1, sb2, mrg⟩ := mrg.split_subheap sb
    constructor <;> aesop
  case tt ct =>
    rcases sb with ⟨H0, ct0, dsj, un⟩; subst un
    constructor; apply ct.union ct0
  case ff ct =>
    rcases sb with ⟨H0, ct0, dsj, un⟩; subst un
    constructor; apply ct.union ct0
  case ite mrg rsm rsn1 rsn2 ihm ihn1 ihn2 =>
    have ⟨H1p, H2p, sb1, sb2, mrg⟩ := mrg.split_subheap sb
    constructor <;> aesop
  case drop mrg rsm rsn ihm ihn =>
    have ⟨H1p, H2p, sb1, sb2, mrg⟩ := mrg.split_subheap sb
    constructor <;> aesop
  case ptr lk erm ih =>
    rcases sb with ⟨H0, ct, dsj, e⟩; subst e
    have lk0 := lk.disjoint_union dsj
    have dsj0 := lk.disjoint_image dsj
    have sb := SubHeap.intro H0 ct dsj0 rfl
    replace ih := ih sb
    constructor <;> assumption
  case null ct =>
    rcases sb with ⟨H0, ct0, dsj, un⟩; subst un
    constructor; apply ct.union ct0

lemma HAccess.shareable_tt {H H' : Heap Srt} {l} :
    HAccess H l .tt H' -> H = H' := by
  intro lk
  unfold HAccess at lk
  split at lk <;> simp_all[Cell.srt]
  replace ⟨_, lk⟩ := lk; subst_vars
  simp[ord.ι_contra] at lk
  assumption

lemma HAccess.shareable_ff {H H' : Heap Srt} {l} :
    HAccess H l .ff H' -> H = H' := by
  intro lk
  unfold HAccess at lk
  split at lk <;> simp_all[Cell.srt]
  replace ⟨_, lk⟩ := lk; subst_vars
  simp[ord.ι_contra] at lk
  assumption

lemma Resolve.var_inv {H : Heap Srt} {m x} :
    H ;; m ▷ .var x -> Shareable H := by
  generalize e: Tm.var x = m'
  intro rs; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases m
    all_goals simp_all[Cell.tm]; cases rsm

lemma Resolve.lam_inv {H : Heap Srt} {m m' s} :
    H ;; m ▷ .lam m' s -> (s ∈ ord.contra_set -> Shareable H) := by
  generalize e: Tm.lam m' s = t
  intro rs; induction rs <;> try trivial
  case lam => cases e; assumption
  case ptr l m m' lk rsm ih =>
    subst_vars; cases m
    all_goals simp_all[Cell.tm]; cases rsm
    case lam hyp =>
      have ifq := lk.lookup
      intro h; replace hyp := hyp h
      simp[Cell.srt,h] at ifq; subst ifq
      assumption

lemma Resolve.tt_inv {H : Heap Srt} {m} :
    H ;; m ▷ .tt -> Shareable H := by
  generalize e: Tm.tt = t
  intro rs; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases m
    all_goals simp_all[Cell.tm]; cases rsm
    have ifq := lk.lookup
    simp[Cell.srt,ord.ι_contra] at ifq; subst ifq
    assumption

lemma Resolve.ff_inv {H : Heap Srt} {m} :
    H ;; m ▷ .ff -> Shareable H := by
  generalize e: Tm.ff = t
  intro rs; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases m
    all_goals simp_all[Cell.tm]; cases rsm
    have ifq := lk.lookup
    simp[Cell.srt,ord.ι_contra] at ifq; subst ifq
    assumption

lemma Resolve.null_inv {H : Heap Srt} {m} :
    H ;; m ▷ .null -> Shareable H ∧ m = .null := by
  generalize e: Tm.null = t
  intro rs; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases m
    all_goals simp_all[Cell.tm]

theorem Resolved.resolution {H : Heap Srt} {x y z A s i} :
    [] ;; H ⊢ x ▷ y ◁ z :: A ->
    [] ⊢ A : .srt s i -> Value y -> (s ∈ ord.contra_set -> Shareable H) := by
  intro ⟨er, rs⟩; revert er
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro er ty vl; induction er generalizing H z s i
  all_goals subst_vars; try (solve | cases vl)
  case lam_im =>
    have ⟨_, _, _, _, rd⟩ := ty.pi_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    apply rs.lam_inv
  case lam_ex =>
    have ⟨_, _, _, _, rd⟩ := ty.pi_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    apply rs.lam_inv
  case tup_im tym ern ihn =>
    intro h
    have ⟨_, _, _, _, _, _, le, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp_all; cases rs
    case tup mrg rsm rsn =>
      have ⟨ct1, _⟩ := rsm.null_inv; subst_vars
      have ct2 := ihn rsn (tyB.subst tym) (ord.contra_set.lower le h)
      apply mrg.shareable_image ct1 ct2
    case ptr H l m lk rs =>
      have ifq := lk.lookup
      cases m
      all_goals simp_all[Cell.tm,Cell.srt]; cases rs
      case box mrg rsm rsn =>
        have ⟨ct1, _⟩ := rsm.null_inv
        have ct2 := ihn rsn (tyB.subst tym) (ord.contra_set.lower le h)
        simp[h] at ifq; subst_vars
        apply mrg.shareable_image ct1 ct2
      case tup rsm _ =>
        have ⟨_, e⟩ := rsm.null_inv; cases e
  case tup_ex erm ern ihm ihn mrg _ =>
    intro h; cases mrg
    have ⟨_, _, _, _, _, le1, le2, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp_all; cases rs
    case tup mrg rsm rsn =>
      have ct1 := ihm rsm tyA (ord.contra_set.lower le1 h)
      have ct2 := ihn rsn (tyB.subst erm.toStatic) (ord.contra_set.lower le2 h)
      apply mrg.shareable_image ct1 ct2
    case ptr l m lk rs =>
      have ifq := lk.lookup
      cases m
      all_goals simp_all[Cell.tm,Cell.srt]; cases rs
      case box rsm _ =>
        cases rsm
        exfalso; apply erm.null_preimage
      case tup mrg rsm rsn =>
        have ct1 := ihm rsm tyA (ord.contra_set.lower le1 h)
        have ct2 := ihn rsn (tyB.subst erm.toStatic) (ord.contra_set.lower le2 h)
        simp[h] at ifq; subst_vars
        apply mrg.shareable_image ct1 ct2
  case tt => have ct := rs.tt_inv; aesop
  case ff => have ct := rs.ff_inv; aesop
  case rw tyA erm tyn ihm =>
    have ⟨eq, _⟩ := tyn.closed_idn tyA
    have ⟨s, i, ty'⟩ := erm.validity
    have ⟨x, rd1, rd2⟩ := Static.Step.cr eq.sym
    have ty1 := ty.preservation' rd1
    have ty2 := ty'.preservation' rd2
    have e := Static.Typed.unique ty1 ty2
    simp_all; apply ihm <;> try assumption
  case conv eq erm _ ih =>
    simp_all
    have ⟨s, i, tyA⟩ := erm.validity
    have ⟨x, rd1, rd2⟩ := Static.Step.cr eq
    have tyx1 := tyA.preservation' rd1
    have tyx2 := ty.preservation' rd2
    have e := tyx1.unique tyx2; subst_vars
    aesop

lemma Resolve.value_image {H : Heap Srt} {m m'} :
    H ;; m ▷ m' -> Value m -> Value m' := by
  intro rsm vl; induction rsm <;> try (solve|aesop)
  all_goals try (solve|cases vl)
  case tup mrg rsm rsn ihm ihn =>
    cases vl; case tup vl1 vl2 =>
    replace ihm := ihm vl1
    replace ihn := ihn vl2
    constructor <;> assumption
  case ptr m _ lk rs ih =>
    apply ih; cases m
    all_goals simp_all[Cell.tm]; aesop

lemma Resolve.ptr_value {H : Heap Srt} {n l} :
    H ;; .ptr l ▷ n -> Value n := by
  intro rs; cases rs
  case ptr m lk rs =>
    apply rs.value_image; cases m
    all_goals simp_all[Cell.tm]; aesop

lemma Resolve.ptr_closed {H : Heap Srt} {n l} :
    H ;; .ptr l ▷ n -> Closed 0 n := by
  intro rs; cases rs
  case ptr m lk rs =>
    have cl := lk.closed
    apply Resolve.closed_image rs cl

end Runtime

open Runtime

lemma Erased.resolve_init' {H : Heap Srt} {Δ m n A} :
    Δ ⊢ m ▷ n :: A -> Shareable H -> H ;; n ▷ n := by
  intro er ct
  induction er
  case var => constructor; assumption
  case lam_im ih =>
    constructor
    intro; assumption
    assumption
  case lam_ex ih =>
    constructor
    intro; assumption
    assumption
  case app_im ih =>
    constructor
    . apply ct.merge_refl
    . apply ih
    . constructor
      assumption
  case app_ex =>
    constructor
    . apply ct.merge_refl
    . assumption
    . assumption
  case tup_im ih =>
    constructor
    . apply ct.merge_refl
    . constructor; assumption
    . apply ih
  case tup_ex =>
    constructor
    . apply ct.merge_refl
    . assumption
    . assumption
  case prj_im =>
    constructor
    . apply ct.merge_refl
    . assumption
    . assumption
  case prj_ex =>
    constructor
    . apply ct.merge_refl
    . assumption
    . assumption
  case tt => constructor; assumption
  case ff => constructor; assumption
  case ite =>
    constructor
    . apply ct.merge_refl
    . assumption
    . assumption
    . assumption
  case rw => aesop
  case drop ih =>
    constructor
    . apply ct.merge_refl
    . assumption
    . assumption
  case conv => aesop

lemma Erased.resolve_init {Δ m n A} :
    Δ ⊢ m ▷ n :: A -> (∅ : Heap Srt) ;; n ▷ n := by
  intro erm
  apply erm.resolve_init' Shareable.empty
