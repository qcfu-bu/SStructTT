import SStructTT.SStruct.Erasure.Syntax
import Mathlib.Data.Finmap

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type}

abbrev Heap Srt := Finmap (fun (_ : Nat) => Tm Srt × Srt)

lemma Heap.fresh (H : Heap Srt) : ∃ l, l ∉ H := by
  generalize e1: H.keys = keys
  cases e2: keys.max with
  | bot =>
    rw [keys.max_eq_bot] at e2
    subst e2; exists 0
    simp[<-Finmap.mem_keys,e1]
  | coe x =>
    exists x + 1
    simp[<-Finmap.mem_keys,e1]
    apply keys.not_mem_of_max_lt _ e2
    simp

lemma Heap.erase_insert {H : Heap Srt} {l v} :
    l ∉ H -> (H.insert l v).erase l = H := by
  intro h
  apply Finmap.ext_lookup
  intro x
  cases x.decEq l with
  | isTrue e =>
    subst e; simp
    rw [<-Finmap.lookup_eq_none] at h
    rw [h]
  | isFalse e =>
    rw [Finmap.lookup_erase_ne e]
    rw [Finmap.lookup_insert_of_ne _ e]

lemma Heap.insert_erase {H : Heap Srt} {l v} :
    H.lookup l = some v -> (H.erase l).insert l v = H := by
  intro h
  apply Finmap.ext_lookup; intro x
  cases x.decEq l with
  | isTrue => subst_vars; simp[h]
  | isFalse ne => simp[ne]

lemma Heap.erase_insert_comm {H : Heap Srt} {l1 l2 x} :
    l1 ≠ l2 -> (H.insert l1 x).erase l2 = (H.erase l2).insert l1 x := by
  intro ne
  apply Finmap.ext_lookup; intro x
  if dec1: x = l1 then
    subst_vars; simp
    if dec2: x = l2
    then subst_vars; contradiction
    else rw[Finmap.lookup_erase_ne ne]; simp
  else
    if dec2: x = l2
    then
      subst_vars; simp
      rw[Finmap.lookup_insert_of_ne _ dec1]
      rw[Finmap.lookup_erase]
    else
      rw[Finmap.lookup_insert_of_ne _ dec1]
      rw[Finmap.lookup_erase_ne dec2]
      rw[Finmap.lookup_erase_ne dec2]
      rw[Finmap.lookup_insert_of_ne _ dec1]

lemma Heap.insert_id {H : Heap Srt} {l t} :
    H.lookup l = some t -> H.insert l t = H := by
  intro h
  apply Finmap.ext_lookup; intro x
  cases x.decEq l with
  | isTrue => subst_vars; simp[h]
  | isFalse ne => simp[ne]

variable [ord : SrtOrder Srt]

def Weaken (H : Heap Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | some (_, s) => s ∈ ord.weaken_set
    | none => True

def Contra (H : Heap Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | some (_, s) => s ∈ ord.contra_set
    | none => True

-- def HLower (H : Heap Srt) (s0 : Srt) : Prop :=
--   ∀ l,
--     match H.lookup l with
--     | some (_, s) => s ∈ InterSet s0
--     | none => True

-- lemma HLower.empty {s : Srt} : HLower ∅ s := by
--   intro l; simp

lemma Weaken.empty : Weaken (∅ : Heap Srt) := by
  intro l; simp

lemma Contra.empty : Contra (∅ : Heap Srt) := by
  intro l; simp

lemma Contra.union {H1 H2 : Heap Srt} : Contra H1 -> Contra H2 -> Contra (H1 ∪ H2) := by
  intro ct1 ct2 x
  replace ct1 := ct1 x
  replace ct2 := ct2 x
  split <;> try trivial
  case h_1 heq =>
    simp at heq
    cases heq <;> aesop

-- lemma HLower.insert {H : Heap Srt} {l v s s'} :
--     HLower H s -> s' ∈ InterSet s -> HLower (H.insert l (v, s')) s := by
--   intro lw h x
--   cases x.decEq l with
--   | isTrue => subst_vars; simp[h]
--   | isFalse ne => simp[ne]; apply lw

lemma Weaken.insert {H : Heap Srt} {l v s} :
    Weaken H -> s ∈ ord.weaken_set -> Weaken (H.insert l (v, s)) := by
  intro lw h x
  cases x.decEq l with
  | isTrue => subst_vars; simp[h]
  | isFalse ne => simp[ne]; apply lw

lemma Contra.insert {H : Heap Srt} {l v s} :
    Contra H -> s ∈ ord.contra_set -> Contra (H.insert l (v, s)) := by
  intro lw h x
  cases x.decEq l with
  | isTrue => subst_vars; simp[h]
  | isFalse ne => simp[ne]; apply lw

-- lemma HLower.invert {H : Heap Srt} {l v s s'} :
--     HLower (H.insert l (v, s')) s -> s' ∈ InterSet s := by
--   intro lw
--   replace lw := lw l
--   simp at lw; assumption

lemma Weaken.invert {H : Heap Srt} {l v s} :
    Weaken (H.insert l (v, s)) -> s ∈ ord.weaken_set := by
  intro lw
  replace lw := lw l
  simp at lw; assumption

lemma Contra.invert {H : Heap Srt} {l v s} :
    Contra (H.insert l (v, s)) -> s ∈ ord.contra_set := by
  intro lw
  replace lw := lw l
  simp at lw; assumption

-- lemma HLower.cover {H : Heap Srt} {s1 s2 : Srt} :
--     HLower H s1 -> s1 ∈ InterSet s2 -> HLower H s2 := by
--   intro lw h x
--   replace lw := lw x
--   split at lw <;> try simp
--   apply InterSet.trans h lw

-- lemma HLower.weaken {H : Heap Srt} {s1 s2 : Srt} :
--     HLower H s1 -> s1 ≤ s2 -> HLower H s2 := by
--   intro lw h
--   apply lw.cover (InterSet.lower_mem h)

-- lemma HLower.insert_lower {H} {m : Tm Srt} {l s1 s2} :
--     HLower H s2 -> s1 ≤ s2 ->  HLower (H.insert l (m, s1)) s2 := by
--   intro h lw x
--   split <;> try simp
--   case h_1 opt m1 s3 e =>
--     cases x.decEq l with
--     | isTrue =>
--       subst_vars
--       rw[Finmap.lookup_insert] at e; cases e
--       apply InterSet.lower_mem lw
--     | isFalse ne =>
--       rw[Finmap.lookup_insert_of_ne _ ne] at e
--       replace h := h x
--       simp_rw[e] at h
--       assumption

-- lemma HLower.erase_lower {H : Heap Srt} {s} l :
--     HLower H s -> HLower (H.erase l) s := by
--   intro lw x
--   cases x.decEq l with
--   | isTrue => aesop
--   | isFalse ne =>
--     rw[Finmap.lookup_erase_ne ne]
--     apply lw

lemma Weaken.erase {H : Heap Srt} l :
    Weaken H -> Weaken (H.erase l) := by
  intro ct x
  cases x.decEq l with
  | isTrue => aesop
  | isFalse ne =>
    rw[Finmap.lookup_erase_ne ne]
    apply ct

lemma Contra.erase {H : Heap Srt} l :
    Contra H -> Contra (H.erase l) := by
  intro ct x
  cases x.decEq l with
  | isTrue => aesop
  | isFalse ne =>
    rw[Finmap.lookup_erase_ne ne]
    apply ct

-- lemma HLower.union {H1 H2 : Heap Srt} {s1 s2 : Srt} :
--     HLower H1 s1 ->
--     HLower H2 s2 ->
--     s1 ≤ s2 ->
--     HLower (H1 ∪ H2) s2 := by
--   intro lw1 lw2 lw x
--   split <;> try simp
--   case h_1 opt m s h =>
--     rw[Finmap.mem_lookup_union'] at h
--     match h with
--     | .inl h =>
--       simp at h
--       replace lw1 := lw1 x
--       simp_rw[h] at lw1
--       apply InterSet.lower_subset lw lw1
--     | .inr ⟨_, h⟩ =>
--       simp at h
--       replace lw2 := lw2 x
--       simp_rw[h] at lw2
--       assumption

def HMerge (H1 H2 H3 : Heap Srt) : Prop :=
  ∀ l,
    match H1.lookup l, H2.lookup l, H3.lookup l with
    | some (m1, s1), some (m2, s2), some (m3, s3) =>
      s1 ∈ ord.contra_set ∧
      s1 = s2 ∧ s2 = s3 ∧
      m1 = m2 ∧ m2 = m3
    | some (m1, s1), none, some (m3, s3) =>
      s1 ∉ ord.contra_set ∧
      m1 = m3 ∧ s1 = s3
    | none, some (m2, s2), some (m3, s3) =>
      s2 ∉ ord.contra_set ∧
      m2 = m3 ∧ s2 = s3
    | none, none, none => True
    | _, _, _ => False

-- lemma HLower.merge_refl {H : Heap Srt} : HMerge H H H := by
--   intro lw1 h x
--   replace lw1 := lw1 x
--   split at lw1
--   case h_1 opt m s e =>
--     rw[e]; simp
--     apply InterSet.contra lw1 h
--   case h_2 => aesop

lemma Contra.merge_refl {H : Heap Srt} :
    Contra H -> HMerge H H H := by
  intro lw1 x
  replace lw1 := lw1 x
  split at lw1
  case h_1 opt m s e =>
    rw[e]; simp; assumption
  case h_2 => aesop

lemma HMerge.sym {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> HMerge H2 H1 H3 := by
  intro mrg x
  replace mrg := mrg x
  split at mrg <;> aesop

-- lemma HMerge.empty {H : Heap Srt} : HMerge H ∅ H := by
--   intro l; split <;> try simp_all
--   case h_5 h1 h2 =>
--     revert h1 h2
--     generalize Finmap.lookup l H = opt
--     cases opt
--     . simp
--     . aesop

lemma HMerge.empty_inv {H1 H2 : Heap Srt} : HMerge H1 ∅ H2 -> H1 = H2 := by
  intro mrg
  apply Finmap.ext_lookup
  intro l
  replace mrg := mrg l; split at mrg
  all_goals aesop

-- lemma HMerge.lower_image {H1 H2 H3 : Heap Srt} {s} :
--     HMerge H1 H2 H3 -> HLower H1 s -> HLower H2 s -> HLower H3 s := by
--   intro mrg lw1 lw2 x
--   split <;> try simp
--   case h_1 opt m s h =>
--     replace mrg := mrg x
--     simp_rw[h] at mrg
--     split at mrg <;> try trivial
--     case h_1 h1 h2 e =>
--       cases e; have ⟨_, e1, e2, e3, e4⟩ := mrg; subst_vars
--       replace lw1 := lw1 x; simp_rw[h1] at lw1
--       assumption
--     case h_2 h1 h2 e =>
--       cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
--       replace lw1 := lw1 x; simp_rw[h1] at lw1
--       assumption
--     case h_3 h1 h2 e =>
--       cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
--       replace lw2 := lw2 x; simp_rw[h2] at lw2
--       assumption

lemma HMerge.weaken_image {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Weaken H1 -> Weaken H2 -> Weaken H3 := by
  intro mrg lw1 lw2 x
  split <;> try simp
  case h_1 opt m s h =>
    replace mrg := mrg x
    simp_rw[h] at mrg
    split at mrg <;> try trivial
    case h_1 h1 h2 e =>
      cases e; have ⟨_, e1, e2, e3, e4⟩ := mrg; subst_vars
      replace lw1 := lw1 x; simp_rw[h1] at lw1
      assumption
    case h_2 h1 h2 e =>
      cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
      replace lw1 := lw1 x; simp_rw[h1] at lw1
      assumption
    case h_3 h1 h2 e =>
      cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
      replace lw2 := lw2 x; simp_rw[h2] at lw2
      assumption

lemma HMerge.contra_image {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Contra H1 -> Contra H2 -> Contra H3 := by
  intro mrg lw1 lw2 x
  split <;> try simp
  case h_1 opt m s h =>
    replace mrg := mrg x
    simp_rw[h] at mrg
    split at mrg <;> try trivial
    case h_1 h1 h2 e =>
      cases e; have ⟨_, e1, e2, e3, e4⟩ := mrg; subst_vars
      replace lw1 := lw1 x; simp_rw[h1] at lw1
      assumption
    case h_2 h1 h2 e =>
      cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
      replace lw1 := lw1 x; simp_rw[h1] at lw1
      assumption
    case h_3 h1 h2 e =>
      cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
      replace lw2 := lw2 x; simp_rw[h2] at lw2
      assumption

lemma HMerge.split_weaken_hyp {H1 H2 H3 : Heap Srt} {s} :
    HMerge H1 H2 H3 ->
    (s ∈ ord.weaken_set -> Weaken H1) ->
    (s ∈ ord.weaken_set -> Weaken H2) ->
    (s ∈ ord.weaken_set -> Weaken H3) := by
  intro mrg h1 h2 h
  replace h1 := h1 h
  replace h2 := h2 h
  apply mrg.weaken_image h1 h2

lemma HMerge.split_contra_hyp {H1 H2 H3 : Heap Srt} {s} :
    HMerge H1 H2 H3 ->
    (s ∈ ord.contra_set -> Contra H1) ->
    (s ∈ ord.contra_set -> Contra H2) ->
    (s ∈ ord.contra_set -> Contra H3) := by
  intro mrg h1 h2 h
  replace h1 := h1 h
  replace h2 := h2 h
  apply mrg.contra_image h1 h2

lemma HMerge.split_weaken' {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Weaken H3 -> Weaken H1 := by
  intro mrg wr l
  replace mrg := mrg l; split at mrg <;> try (solve|aesop)
  case h_1 h1 h2 h3 =>
    replace wr := wr l
    rw[h3] at wr; simp_all
  case h_2 h1 h2 h3 =>
    replace wr := wr l
    rw[h3] at wr; simp_all

lemma HMerge.split_weaken {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Weaken H3 -> Weaken H1 ∧ Weaken H2 := by
  intro mrg lw
  have lw1 := mrg.split_weaken' lw
  have lw2 := mrg.sym.split_weaken' lw
  aesop

lemma HMerge.split_contra' {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Contra H3 -> Contra H1 := by
  intro mrg wr l
  replace mrg := mrg l; split at mrg <;> try (solve|aesop)
  -- case h_1 h1 h2 h3 =>
  --   replace wr := wr l
  --   rw[h3] at wr; simp_all
  case h_2 h1 h2 h3 =>
    replace wr := wr l
    rw[h3] at wr; simp_all

lemma HMerge.split_contra {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Contra H3 -> Contra H1 ∧ Contra H2 := by
  intro mrg lw
  have lw1 := mrg.split_contra' lw
  have lw2 := mrg.sym.split_contra' lw
  aesop

lemma HMerge.split_none {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∉ H3 -> l ∉ H1 ∧ l ∉ H2 := by
  intro mrg h3
  apply Classical.byContradiction
  intro h; rw[Classical.not_and_iff_not_or_not] at h; simp at h
  cases h with
  | inl h1 =>
    rw[Finmap.mem_iff] at h1
    replace ⟨⟨m, s⟩, h1⟩ := h1
    rw[<-Finmap.lookup_eq_none] at h3
    replace mrg := mrg l
    simp_rw[h1,h3] at mrg
    split at mrg <;> try trivial
  | inr h2 =>
    rw[Finmap.mem_iff] at h2; replace ⟨⟨m, s⟩, h2⟩ := h2
    rw[<-Finmap.lookup_eq_none] at h3
    replace mrg := mrg l
    simp_rw[h2,h3] at mrg
    split at mrg <;> try trivial

lemma HMerge.mem_left {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∈ H1 -> l ∈ H3 := by
  intro mrg h1
  rw[Finmap.mem_iff] at h1
  replace ⟨⟨m, s⟩, h1⟩ := h1
  replace mrg := mrg l; rw[h1] at mrg
  split at mrg <;> try trivial
  . apply Finmap.mem_of_lookup_eq_some
    assumption
  . apply Finmap.mem_of_lookup_eq_some
    assumption

lemma HMerge.insert_contra {H1 H2 H3 : Heap Srt} {m l s} :
    HMerge H1 H2 H3 -> s ∈ ord.contra_set ->
    HMerge (H1.insert l ⟨m, s⟩) (H2.insert l ⟨m, s⟩) (H3.insert l ⟨m, s⟩) := by
  intro mrg h x
  cases x.decEq l with
  | isTrue =>
    subst_vars
    simp[Finmap.lookup_insert]
    assumption
  | isFalse ne =>
    simp[Finmap.lookup_insert_of_ne _ ne]
    apply mrg

lemma HMerge.union_contra {H0 H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Contra H0 -> H3.Disjoint H0 ->
    HMerge (H1 ∪ H0) (H2 ∪ H0) (H3 ∪ H0) := by
  intro mrg ct dsj x
  rw[Finmap.Disjoint.eq_1] at dsj
  if h: x ∈ H3 then
    have h0 := h
    rw[Finmap.mem_iff] at h
    rcases h with ⟨⟨m, s⟩, h⟩
    if s ∈ ord.contra_set then
      replace mrg := mrg x; rw[h] at mrg
      split at mrg <;> try simp_all
      case h_1 heq1 heq2 heq3 =>
        rw[Finmap.lookup_union_left]
        rw[Finmap.lookup_union_left]
        simp[heq1,heq2]
        assumption
        rw[Finmap.mem_iff]; aesop
        rw[Finmap.mem_iff]; aesop
      case h_2 => aesop
      case h_3 => aesop
    else
      replace mrg := mrg x; rw[h] at mrg
      split at mrg <;> try simp_all
      case h_1 => aesop
      case h_2 heq1 heq2 heq3 =>
        rw[Finmap.lookup_union_left]
        rw[Finmap.lookup_union_right]
        simp[heq1,heq2]
        have h0 := dsj _ h0
        rw[<-Finmap.lookup_eq_none] at h0
        simp[h0]; assumption
        rw[Finmap.mem_iff]; aesop
        rw[Finmap.mem_iff]; aesop
      case h_3 heq1 heq2 =>
        rw[Finmap.lookup_union_right]
        rw[Finmap.lookup_union_left]
        simp[heq1,heq2]
        have h0 := dsj _ h0
        rw[<-Finmap.lookup_eq_none] at h0
        simp[h0]; assumption
        rw[Finmap.mem_iff]; aesop
        rw[Finmap.mem_iff]; aesop
  else
    have ⟨h1, h2⟩ := mrg.split_none h
    rw[Finmap.lookup_union_right h1]
    rw[Finmap.lookup_union_right h2]
    rw[Finmap.lookup_union_right h]
    apply ct.merge_refl

lemma HMerge.insert_lookup {H1 H2 H3 : Heap Srt} {m l s} :
    HMerge (H1.insert l (m, s)) H2 H3 -> H3.lookup l = some (m, s) := by
  intro mrg
  replace mrg := mrg l
  split at mrg <;> simp_all

lemma HMerge.insert_left {H1 H2 H3 : Heap Srt} l m s :
    HMerge H1 H2 H3 -> l ∉ H3 -> s ∉ ord.contra_set ->
    HMerge (H1.insert l ⟨m, s⟩) H2 (H3.insert l ⟨m, s⟩) := by
  intro mrg h1 h2 x
  have ⟨h3, h4⟩ := mrg.split_none h1
  rw [<-Finmap.lookup_eq_none] at h3
  rw [<-Finmap.lookup_eq_none] at h4
  cases x.decEq l with
  | isTrue =>
    subst_vars; simp[Finmap.lookup_insert,h4]
    assumption
  | isFalse ne =>
    simp[Finmap.lookup_insert_of_ne _ ne]
    apply mrg

-- lemma HLower.split_lower {H3 : Heap Srt} {s} :
--     HLower H3 s -> s ∈ ord.contra_set ->
--     ∃ H1 H2, HLower H1 s ∧ HLower H2 s ∧ HMerge H1 H2 H3 := by
--   intro lw h
--   exists H3, H3; and_intros
--   . assumption
--   . assumption
--   . apply lw.merge_refl h

lemma HLower.split_contra {H3 : Heap Srt} :
    Contra H3 ->
    ∃ H1 H2, Contra H1 ∧ Contra H2 ∧ HMerge H1 H2 H3 := by
  intro lw
  exists H3, H3; and_intros
  . assumption
  . assumption
  . apply lw.merge_refl

lemma HMerge.self_contra {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Contra H2 -> H1 = H3 := by
  intro mrg ct
  apply Finmap.ext_lookup; intro x
  replace mrg := mrg x
  replace ct := ct x
  revert mrg ct
  generalize e1: H1.lookup x = opt1
  generalize e2: H2.lookup x = opt2
  generalize e3: H3.lookup x = opt3
  split <;> aesop

lemma HMerge.exists_self_contra (H : Heap Srt) :
    ∃ H0, HMerge H H0 H ∧ Contra H0 :=
  H.induction_on (fun xs => by
    clear H; induction xs
    case H0 =>
      exists ∅; simp; and_intros
      apply Contra.empty.merge_refl
      apply Contra.empty
    case IH l hd tl nn ih =>
      rw[<-Finmap.insert_toFinmap]
      rcases ih with ⟨H0, mrg0, ct0⟩
      rcases hd with ⟨m, s⟩
      if mm: s ∈ ord.contra_set then
        exists H0.insert l (m, s); and_intros
        apply mrg0.insert_contra mm
        apply ct0.insert mm
      else
        exists H0; and_intros
        apply mrg0.insert_left <;> assumption
        assumption)

lemma HMerge.lookup_collision {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∈ H1 -> H1.lookup l = H3.lookup l := by
  intro mrg h
  rw[Finmap.mem_iff] at h
  have ⟨⟨m, s⟩, e⟩ := h
  replace mrg := mrg l
  rw[e] at mrg; split at mrg <;> aesop

lemma HMerge.insert_inv {H1 H2 H3 : Heap Srt} {m l s} :
    HMerge (H1.insert l (m, s)) H2 H3 -> l ∉ H1 -> l ∉ H2 ->
    HMerge H1 H2 (H3.erase l) := by
  intro mrg h1 h2
  have h3 := mrg.insert_lookup
  intro x
  if dec: x = l then
    subst_vars
    rw[<-Finmap.lookup_eq_none] at h1
    rw[<-Finmap.lookup_eq_none] at h2
    simp[h1,h2]
  else
    simp[dec]
    replace mrg := mrg x
    simp[dec] at mrg; assumption

lemma HMerge.erase {H1 H2 H3 : Heap Srt} {m l s} :
    HMerge (H1.insert l (m, s)) H2 H3 -> l ∉ H1 ->
    HMerge H1 (H2.erase l) (H3.erase l) := by
  intro mrg h x
  rw[<-Finmap.lookup_eq_none] at h
  replace mrg := mrg x
  if dec: x = l then
    subst_vars; simp[h]
  else
    simp[dec]
    simp[dec] at mrg
    assumption

lemma HMerge.not_contra_inv {H1 H2 H3 : Heap Srt} {m s} l :
    HMerge H1 H2 H3 -> H1.lookup l = some (m, s) ->
    s ∉ ord.contra_set -> l ∉ H2 := by
  intro mrg e h
  replace mrg := mrg l
  rw[e] at mrg
  split at mrg <;> simp_all
  . aesop
  . rw[Finmap.mem_iff]; aesop

lemma HMerge.shift {H1 H2 H3 : Heap Srt} {l m s} :
    HMerge (Finmap.insert l (m, s) H1) H2 H3 ->
    l ∉ H1 -> s ∉ ord.contra_set ->
    HMerge H1 (Finmap.insert l (m, s) H2) H3 := by
  intro mrg h1 h2 x
  replace mrg := mrg x
  if dec: x = l then
    subst_vars
    simp_all
    rw[<-Finmap.lookup_eq_none] at h1
    rw[h1]; revert mrg
    generalize e: Finmap.lookup x H3 = opt
    split <;> try simp_all
    intros; subst_vars
    assumption
  else simp_all

-- lemma HMerge.compose {H1 H2 H3 Ha Hb Hx Hy : Heap Srt} {s} :
--     HLower Ha s -> s ∈ ord.contra_set ->
--     HMerge Ha Hb H3 ->
--     HMerge Hx Ha H1 ->
--     HMerge Hy Ha H2 ->
--     HMerge Hx Hy Hb ->
--     HMerge H1 H2 H3 := by
--   intro lw h mrg1 mrg2 mrg3 mrg4 x
--   replace lw := lw x
--   replace mrg1 := mrg1 x
--   replace mrg2 := mrg2 x
--   replace mrg3 := mrg3 x
--   replace mrg4 := mrg4 x
--   split at mrg1 <;> simp_all
--   case h_1 =>
--     split at mrg2 <;> simp_all
--     case h_1 => split at mrg3 <;> simp_all; aesop
--     case h_3 => split at mrg3 <;> simp_all; aesop
--   case h_2 =>
--     split at mrg2 <;> simp_all
--     case h_3 =>
--       split at mrg3 <;> simp_all
--       apply InterSet.contra lw h
--   case h_3 =>
--     split at mrg2 <;> simp_all
--     case h_2 =>
--       split at mrg3 <;> simp_all
--       case h_2 =>
--         have ⟨h, _, _, _⟩ := mrg4; subst_vars
--         assumption
--     case h_4 => split at mrg3 <;> simp_all
--   case h_4 =>
--     split at mrg2 <;> simp_all
--     split at mrg3 <;> simp_all

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

lemma HMerge.split {H1 H2 H3 Ha Hb : Heap Srt} :
    HMerge H1 H2 H3 ->
    HMerge Ha Hb H1 ->
    ∃ Hc, HMerge Ha H2 Hc ∧ HMerge Hc Hb H3 := by
  intro mrg1 mrg2; exists Ha ∪ H2; and_intros
  . intro x
    replace mrg1 := mrg1 x
    replace mrg2 := mrg2 x
    split at mrg1 <;> simp_all
    . split at mrg2 <;> simp_all
      case h_1 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; aesop
      case h_2 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; aesop
      case h_3 e _ ne _ _ =>
        rw[Finmap.lookup_eq_none] at ne
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp; aesop
    . split at mrg2 <;> simp_all
      case h_1 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; simp; aesop
      case h_2 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; simp; aesop
      case h_3 e _ ne _ _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp
    . split at mrg2 <;> simp_all
      case h_4 e _ _ _ _ ne _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp; aesop
    . split at mrg2 <;> simp_all
      case h_4 e _ _ _ _ ne _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp
  . intro x
    replace mrg1 := mrg1 x
    replace mrg2 := mrg2 x
    split at mrg1 <;> simp_all
    . split at mrg2 <;> simp_all
      case h_1 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; aesop
      case h_2 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; simp; aesop
      case h_3 e _ ne _ _ =>
        rw[Finmap.lookup_eq_none] at ne
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_right ne]
        rw[e]; aesop
    . split at mrg2 <;> simp_all
      case h_1 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; aesop
      case h_2 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; simp; aesop
      case h_3 e _ ne _ _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp; aesop
    . split at mrg2 <;> simp_all
      case h_4 e _ _ _ _ ne _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp; aesop
    . split at mrg2 <;> simp_all
      case h_4 e _ _ _ _ ne _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp

lemma HMerge.distr {H1 H2 H3 H11 H12 H21 H22 : Heap Srt} :
    HMerge H1 H2 H3 ->
    HMerge H11 H12 H1 ->
    HMerge H21 H22 H2 ->
    ∃ H1' H2',
      HMerge H1' H2' H3 ∧
      HMerge H11 H21 H1' ∧
      HMerge H12 H22 H2' := by
  intro mrg0 mrg1 mrg2
  have ⟨H4, mrg3, mrg4⟩ := mrg0.split mrg1
  have ⟨H5, mrg5, mrg6⟩ := mrg3.sym.split mrg2
  have ⟨H6, mrg7, mrg8⟩ := mrg4.split mrg6.sym
  exists H5, H6; and_intros
  . apply mrg8.sym
  . apply mrg5.sym
  . apply mrg7.sym

inductive SubHeap (H1 H2 : Heap Srt) : Prop where
  | intro (H0 : Heap Srt) :
    Contra H0 -> Finmap.Disjoint H1 H0 -> H2 = H1 ∪ H0 -> SubHeap H1 H2

lemma SubHeap.refl (H : Heap Srt) : SubHeap H H := by
  apply SubHeap.intro ∅
  apply Contra.empty
  apply Finmap.Disjoint.symm
  apply Finmap.disjoint_empty
  simp

lemma SubHeap.insert (H : Heap Srt) l m s :
    l ∉ H -> s ∈ ord.contra_set -> SubHeap H (H.insert l (m, s)) := by
  intro h1 h2
  apply SubHeap.intro (Finmap.singleton l (m, s))
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

lemma SubHeap.contra_image {H1 H2 : Heap Srt} : SubHeap H1 H2 -> Contra H1 -> Contra H2 := by
  intro pd c1
  rcases pd with ⟨H0, ct, dsj, mrg⟩
  rw[mrg]
  apply Contra.union <;> assumption

lemma HMerge.split_subheap {H1 H2 H3 H3p : Heap Srt} :
    HMerge H1 H2 H3 -> SubHeap H3 H3p ->
    ∃ H1p H2p, SubHeap H1 H1p ∧ SubHeap H2 H2p ∧ HMerge H1p H2p H3p := by
  intro mrg ⟨H0, ct, dsj, un⟩; subst_vars
  have ⟨dsj1, dsj2⟩ := mrg.split_disjoint dsj
  exists H1 ∪ H0, H2 ∪ H0; and_intros
  . apply SubHeap.intro H0 <;> trivial
  . apply SubHeap.intro H0 <;> trivial
  . apply mrg.union_contra ct dsj
