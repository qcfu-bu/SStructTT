import SStructTT.SStruct.Erasure.Syntax
import Mathlib.Data.Finmap

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type}

abbrev Heap Srt := Finmap (fun (_ : Nat) => Tm Srt × Srt)

lemma Heap.fresh (H : Heap Srt) : ∃ l, l ∉ H.keys := by
  generalize e1: H.keys = keys
  cases e2: keys.max with
  | bot =>
    rw [keys.max_eq_bot] at e2
    subst e2; exists 0
  | coe x =>
    exists x + 1
    apply keys.not_mem_of_max_lt _ e2
    simp

lemma Heap.erase_insert {H : Heap Srt} {l v} :
    l ∉ H.keys -> (H.insert l v).erase l = H := by
  intro h
  apply Finmap.ext_lookup
  intro x
  cases x.decEq l with
  | isTrue e =>
    subst e; simp
    rw [Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
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

def HLower (H : Heap Srt) (s0 : Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | some (_, s) => s ∈ InterSet s0
    | none => True

lemma HLower.empty {s : Srt} : HLower ∅ s := by
  intro l; simp

lemma HLower.cover {H : Heap Srt} {s1 s2 : Srt} :
    HLower H s1 -> s1 ∈ InterSet s2 -> HLower H s2 := by
  intro lw h x
  replace lw := lw x
  split at lw <;> try simp
  apply InterSet.trans h lw

lemma HLower.weaken {H : Heap Srt} {s1 s2 : Srt} :
    HLower H s1 -> s1 ≤ s2 -> HLower H s2 := by
  intro lw h
  apply lw.cover (InterSet.lower_mem h)

lemma HLower.insert_lower {H} {m : Tm Srt} {l s1 s2} :
    HLower H s2 -> s1 ≤ s2 ->  HLower (H.insert l (m, s1)) s2 := by
  intro h lw x
  split <;> try simp
  case h_1 opt m1 s3 e =>
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert] at e; cases e
      apply InterSet.lower_mem lw
    | isFalse ne =>
      rw[Finmap.lookup_insert_of_ne _ ne] at e
      replace h := h x
      simp_rw[e] at h
      assumption

lemma HLower.erase_lower {H : Heap Srt} {s} l :
    HLower H s -> HLower (H.erase l) s := by
  intro lw x
  cases x.decEq l with
  | isTrue => aesop
  | isFalse ne =>
    rw[Finmap.lookup_erase_ne ne]
    apply lw

lemma HLower.union {H1 H2 : Heap Srt} {s1 s2 : Srt} :
    HLower H1 s1 ->
    HLower H2 s2 ->
    s1 ≤ s2 ->
    HLower (H1 ∪ H2) s2 := by
  intro lw1 lw2 lw x
  split <;> try simp
  case h_1 opt m s h =>
    rw[Finmap.mem_lookup_union'] at h
    match h with
    | .inl h =>
      simp at h
      replace lw1 := lw1 x
      simp_rw[h] at lw1
      apply InterSet.lower_subset lw lw1
    | .inr ⟨_, h⟩ =>
      simp at h
      replace lw2 := lw2 x
      simp_rw[h] at lw2
      assumption

def HMerge (H1 H2 H3 : Heap Srt) : Prop :=
  ∀ l,
    match H1.lookup l, H2.lookup l, H3.lookup l with
    | some (m1, s1), some (m2, s2), some (m3, s3) =>
      s1 ∈ ord.contra_set ∧
      s1 = s2 ∧ s2 = s3 ∧
      m1 = m2 ∧ m2 = m3
    | some (m1, s1), none, some (m3, s3) =>
      m1 = m3 ∧ s1 = s3
    | none, some (m2, s2), some (m3, s3) =>
      m2 = m3 ∧ s2 = s3
    | none, none, none => True
    | _, _, _ => False

lemma HLower.merge_refl {H : Heap Srt} {s} :
    HLower H s -> s ∈ ord.contra_set -> HMerge H H H := by
  intro lw1 h x
  replace lw1 := lw1 x
  split at lw1
  case h_1 opt m s e =>
    rw[e]; simp
    apply InterSet.contra lw1 h
  case h_2 => aesop

lemma HMerge.sym {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> HMerge H2 H1 H3 := by
  intro mrg x
  replace mrg := mrg x
  split at mrg <;> aesop

lemma HMerge.empty {H : Heap Srt} : HMerge H ∅ H := by
  intro l; split <;> try simp_all
  case h_5 h1 h2 =>
    revert h1 h2
    generalize Finmap.lookup l H = opt
    cases opt
    . simp
    . aesop

lemma HMerge.empty_inv {H1 H2 : Heap Srt} : HMerge H1 ∅ H2 -> H1 = H2 := by
  intro mrg
  apply Finmap.ext_lookup
  intro l
  replace mrg := mrg l; split at mrg
  all_goals aesop

lemma HMerge.lower_image {H1 H2 H3 : Heap Srt} {s} :
    HMerge H1 H2 H3 -> HLower H1 s -> HLower H2 s -> HLower H3 s := by
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
      cases e; have ⟨e1, e2⟩ := mrg; subst_vars
      replace lw1 := lw1 x; simp_rw[h1] at lw1
      assumption
    case h_3 h1 h2 e =>
      cases e; have ⟨e1, e2⟩ := mrg; subst_vars
      replace lw2 := lw2 x; simp_rw[h2] at lw2
      assumption

lemma HMerge.split_lower' {H1 H2 H3 : Heap Srt} {s} :
    HMerge H1 H2 H3 -> HLower H3 s -> HLower H1 s := by
  intro mrg wr l
  replace mrg := mrg l; split at mrg <;> try (solve|aesop)
  case h_1 h1 h2 h3 =>
    replace wr := wr l
    rw[h3] at wr; simp_all
  case h_2 h1 h2 h3 =>
    replace wr := wr l
    rw[h3] at wr; simp_all

lemma HMerge.split_lower {H1 H2 H3 : Heap Srt} {s} :
    HMerge H1 H2 H3 -> HLower H3 s -> HLower H1 s ∧ HLower H2 s := by
  intro mrg lw
  have lw1 := mrg.split_lower' lw
  have lw2 := mrg.sym.split_lower' lw
  aesop

lemma HMerge.split_none {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∉ H3.keys -> l ∉ H1.keys ∧ l ∉ H2.keys := by
  intro mrg h3
  apply Classical.byContradiction
  intro h; rw[Classical.not_and_iff_not_or_not] at h; simp at h
  cases h with
  | inl h1 =>
    rw[Finmap.mem_keys,Finmap.mem_iff] at h1
    replace ⟨⟨m, s⟩, h1⟩ := h1
    rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h3
    replace mrg := mrg l
    simp_rw[h1,h3] at mrg
    split at mrg <;> try trivial
  | inr h2 =>
    rw[Finmap.mem_keys] at h2
    rw[Finmap.mem_iff] at h2; replace ⟨⟨m, s⟩, h2⟩ := h2
    rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h3
    replace mrg := mrg l
    simp_rw[h2,h3] at mrg
    split at mrg <;> try trivial

lemma HMerge.mem_left {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∈ H1.keys -> l ∈ H3.keys := by
  intro mrg h1
  rw[Finmap.mem_keys,Finmap.mem_iff] at h1
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

lemma HMerge.insert_lookup {H1 H2 H3 : Heap Srt} {m l s} :
    HMerge (H1.insert l (m, s)) H2 H3 -> H3.lookup l = some (m, s) := by
  intro mrg
  replace mrg := mrg l
  split at mrg <;> simp_all

lemma HMerge.insert_left {H1 H2 H3 : Heap Srt} l m s :
    HMerge H1 H2 H3 -> l ∉ H3.keys ->
    HMerge (H1.insert l ⟨m, s⟩) H2 (H3.insert l ⟨m, s⟩) := by
  intro mrg h x
  have ⟨h1, h2⟩ := mrg.split_none h
  rw [Finmap.mem_keys,<-Finmap.lookup_eq_none] at h1
  rw [Finmap.mem_keys,<-Finmap.lookup_eq_none] at h2
  cases x.decEq l with
  | isTrue => subst_vars; simp[Finmap.lookup_insert,h2]
  | isFalse ne =>
    simp[Finmap.lookup_insert_of_ne _ ne]
    apply mrg

lemma HLower.split_lower {H3 : Heap Srt} {s} :
    HLower H3 s -> s ∈ ord.contra_set ->
    ∃ H1 H2, HLower H1 s ∧ HLower H2 s ∧ HMerge H1 H2 H3 := by
  intro lw h
  exists H3, H3; and_intros
  . assumption
  . assumption
  . apply lw.merge_refl h

lemma HMerge.lookup_collision {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∈ H1.keys -> H1.lookup l = H3.lookup l := by
  intro mrg h
  rw[Finmap.mem_keys,Finmap.mem_iff] at h
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

lemma HMerge.shift {H1 H2 H3 : Heap Srt} {l t} :
    HMerge (Finmap.insert l t H1) H2 H3 -> l ∉ H1 ->
    HMerge H1 (Finmap.insert l t H2) H3 := by
  intro mrg h x
  replace mrg := mrg x
  if dec: x = l then
    subst_vars
    simp_all
    rw[<-Finmap.lookup_eq_none] at h
    rw[h]; revert mrg
    generalize e: Finmap.lookup x H3 = opt
    split <;> try simp_all
  else simp_all

lemma HMerge.compose {H1 H2 H3 Ha Hb Hx Hy : Heap Srt} {s} :
    HLower Ha s -> s ∈ ord.contra_set ->
    HMerge Ha Hb H3 ->
    HMerge Hx Ha H1 ->
    HMerge Hy Ha H2 ->
    HMerge Hx Hy Hb ->
    HMerge H1 H2 H3 := by
  intro lw h mrg1 mrg2 mrg3 mrg4 x
  replace lw := lw x
  replace mrg1 := mrg1 x
  replace mrg2 := mrg2 x
  replace mrg3 := mrg3 x
  replace mrg4 := mrg4 x
  split at mrg1 <;> simp_all
  case h_1 =>
    split at mrg2 <;> simp_all
    case h_1 => split at mrg3 <;> simp_all; aesop
    case h_3 => split at mrg3 <;> simp_all; aesop
  case h_2 =>
    split at mrg2 <;> simp_all
    case h_3 =>
      split at mrg3 <;> simp_all
      apply InterSet.contra lw h
  case h_3 =>
    split at mrg2 <;> simp_all
    case h_2 =>
      split at mrg3 <;> simp_all
      case h_2 =>
        have ⟨h, _, _, _⟩ := mrg4; subst_vars
        assumption
    case h_4 => split at mrg3 <;> simp_all
  case h_4 =>
    split at mrg2 <;> simp_all
    split at mrg3 <;> simp_all

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
        rw[e]; simp
    . split at mrg2 <;> simp_all
      case h_1 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; simp
      case h_2 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; simp
      case h_3 e _ ne _ _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp
    . split at mrg2 <;> simp_all
      case h_4 e _ _ _ _ ne _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp
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
        rw[e]; simp
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
        rw[e]; simp
      case h_3 e _ ne _ _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp
    . split at mrg2 <;> simp_all
      case h_4 e _ _ _ _ ne _ =>
        rw[Finmap.lookup_eq_none] at ne
        rw[Finmap.lookup_union_right ne]
        rw[e]; simp
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
