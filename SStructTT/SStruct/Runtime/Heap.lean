import SStructTT.SStruct.Erasure.Erased
import Mathlib.Data.Finmap

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

inductive Cell Srt where
  | clo (m : Tm Srt)  (s : Srt) (_ : Closed 1 m)
  | box (l : Nat)     (s : Srt)
  | tup (l1 l2 : Nat) (s : Srt)
  | tt | ff

def Cell.tm : Cell Srt -> Tm Srt
  | .clo m s _   => .lam m s
  | .box l s     => .tup .null (.ptr l) s
  | .tup l1 l2 s => .tup (.ptr l1) (.ptr l2) s
  | .tt          => .tt
  | .ff          => .ff

def Cell.srt : Cell Srt -> Srt
  | .clo _ s _ => s
  | .box _ s   => s
  | .tup _ _ s => s
  | .tt        => ord.ι
  | .ff        => ord.ι

abbrev Heap Srt := Finmap fun (_ : Nat) => Cell Srt

omit ord in
lemma Heap.fresh (H : Heap Srt) : ∃ l, l ∉ H := by
  generalize e1: H.keys = keys
  cases e2: keys.max with
  | bot =>
    rw [keys.max_eq_bot] at e2
    subst e2; existsi 0
    simp[<-Finmap.mem_keys,e1]
  | coe x =>
    existsi x + 1
    simp[<-Finmap.mem_keys,e1]
    apply keys.not_mem_of_max_lt _ e2
    simp

omit ord in
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

omit ord in
lemma Heap.insert_erase {H : Heap Srt} {l v} :
    H.lookup l = some v -> (H.erase l).insert l v = H := by
  intro h
  apply Finmap.ext_lookup; intro x
  cases x.decEq l with
  | isTrue => subst_vars; simp[h]
  | isFalse ne => simp[ne]

omit ord in
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

omit ord in
lemma Heap.insert_id {H : Heap Srt} {l t} :
    H.lookup l = some t -> H.insert l t = H := by
  intro h
  apply Finmap.ext_lookup; intro x
  cases x.decEq l with
  | isTrue => subst_vars; simp[h]
  | isFalse ne => simp[ne]

def Weaken (H : Heap Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | some m => m.srt ∈ ord.weaken_set
    | none => True

def Contra (H : Heap Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | some m => m.srt ∈ ord.contra_set
    | none => True

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

lemma Weaken.insert {H : Heap Srt} {l m s} :
    Weaken H -> s ∈ ord.weaken_set -> m.srt = s -> Weaken (H.insert l m) := by
  intro wk h e x
  cases x.decEq l with
  | isTrue =>
    subst_vars
    cases m <;> simp_all
  | isFalse ne => simp[ne]; apply wk

lemma Contra.insert {H : Heap Srt} {l m s} :
    Contra H -> s ∈ ord.contra_set -> m.srt = s -> Contra (H.insert l m) := by
  intro ct h e x
  cases x.decEq l with
  | isTrue =>
    subst_vars
    cases m <;> simp_all
  | isFalse ne => simp[ne]; apply ct

lemma Weaken.invert {H : Heap Srt} {l m} :
    Weaken (H.insert l m) -> m.srt ∈ ord.weaken_set := by
  intro wk
  replace wk := wk l
  simp at wk; assumption

lemma Contra.invert {H : Heap Srt} {l m} :
    Contra (H.insert l m) -> m.srt ∈ ord.contra_set := by
  intro ct
  replace ct := ct l
  simp at ct; assumption

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

def HMerge (H1 H2 H3 : Heap Srt) : Prop :=
  ∀ l,
    match H1.lookup l, H2.lookup l, H3.lookup l with
    | some m1, some m2, some m3 =>
      m3.srt ∈ ord.contra_set ∧ m1 = m2 ∧ m2 = m3
    | some m1, none, some m3 =>
      m3.srt ∉ ord.contra_set ∧ m1 = m3
    | none, some m2, some m3 =>
      m3.srt ∉ ord.contra_set ∧ m2 = m3
    | none, none, none => True
    | _, _, _ => False

lemma Contra.merge_refl {H : Heap Srt} :
    Contra H -> HMerge H H H := by
  intro ct1 x
  replace ct1 := ct1 x
  split at ct1
  case h_1 opt m e =>
    rw[e]; simp; assumption
  case h_2 => aesop

lemma HMerge.sym {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> HMerge H2 H1 H3 := by
  intro mrg x
  replace mrg := mrg x
  split at mrg <;> aesop

lemma HMerge.empty_inv {H1 H2 : Heap Srt} : HMerge H1 ∅ H2 -> H1 = H2 := by
  intro mrg
  apply Finmap.ext_lookup
  intro l
  replace mrg := mrg l; split at mrg
  all_goals aesop

lemma HMerge.weaken_image {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Weaken H1 -> Weaken H2 -> Weaken H3 := by
  intro mrg wk1 wk2 x
  split <;> try simp
  case h_1 opt m h =>
    replace mrg := mrg x
    simp_rw[h] at mrg
    split at mrg <;> try trivial
    case h_1 h1 h2 e =>
      cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
      replace wk1 := wk1 x; simp_rw[h1] at wk1
      assumption
    case h_2 h1 h2 e =>
      cases e; have ⟨_, e1⟩ := mrg; subst_vars
      replace wk1 := wk1 x; simp_rw[h1] at wk1
      assumption
    case h_3 h1 h2 e =>
      cases e; have ⟨_, e1⟩ := mrg; subst_vars
      replace wk2 := wk2 x; simp_rw[h2] at wk2
      assumption

lemma HMerge.contra_image {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> Contra H1 -> Contra H2 -> Contra H3 := by
  intro mrg ct1 ct2 x
  split <;> try simp
  case h_1 opt m h =>
    replace mrg := mrg x
    simp_rw[h] at mrg
    split at mrg <;> try trivial
    case h_1 h1 h2 e =>
      cases e; have ⟨_, e1, e2⟩ := mrg; subst_vars
      replace ct1 := ct1 x; simp_rw[h1] at ct1
      assumption
    case h_2 h1 h2 e =>
      cases e; have ⟨_, e1⟩ := mrg; subst_vars
      replace ct1 := ct1 x; simp_rw[h1] at ct1
      assumption
    case h_3 h1 h2 e =>
      cases e; have ⟨_, e1⟩ := mrg; subst_vars
      replace ct2 := ct2 x; simp_rw[h2] at ct2
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
    replace ⟨m, h1⟩ := h1
    rw[<-Finmap.lookup_eq_none] at h3
    replace mrg := mrg l
    simp_rw[h1,h3] at mrg
    split at mrg <;> try trivial
  | inr h2 =>
    rw[Finmap.mem_iff] at h2; replace ⟨m, h2⟩ := h2
    rw[<-Finmap.lookup_eq_none] at h3
    replace mrg := mrg l
    simp_rw[h2,h3] at mrg
    split at mrg <;> try trivial

lemma HMerge.mem_left {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∈ H1 -> l ∈ H3 := by
  intro mrg h1
  rw[Finmap.mem_iff] at h1
  replace ⟨m, h1⟩ := h1
  replace mrg := mrg l; rw[h1] at mrg
  split at mrg <;> try trivial
  . apply Finmap.mem_of_lookup_eq_some
    assumption
  . apply Finmap.mem_of_lookup_eq_some
    assumption

lemma HMerge.insert_contra {H1 H2 H3 : Heap Srt} {l m} :
    HMerge H1 H2 H3 -> m.srt ∈ ord.contra_set ->
    HMerge (H1.insert l m) (H2.insert l m) (H3.insert l m) := by
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
    rcases h with ⟨m, h⟩
    if m.srt ∈ ord.contra_set then
      replace mrg := mrg x; rw[h] at mrg
      split at mrg <;> try simp_all
      case h_1 heq1 heq2 heq3 =>
        rw[Finmap.lookup_union_left]
        rw[Finmap.lookup_union_left]
        simp[heq1,heq2,mrg]
        rw[Finmap.mem_iff]; aesop
        rw[Finmap.mem_iff]; aesop
    else
      replace mrg := mrg x; rw[h] at mrg
      split at mrg <;> try simp_all
      case h_2 heq1 heq2 heq3 =>
        rw[Finmap.lookup_union_left]
        rw[Finmap.lookup_union_right]
        simp[heq1,heq2]
        have h0 := dsj _ h0
        rw[<-Finmap.lookup_eq_none] at h0
        simp[h0,mrg]
        rw[Finmap.mem_iff]; aesop
        rw[Finmap.mem_iff]; aesop
      case h_3 heq1 heq2 =>
        rw[Finmap.lookup_union_right]
        rw[Finmap.lookup_union_left]
        simp[heq1,heq2]
        have h0 := dsj _ h0
        rw[<-Finmap.lookup_eq_none] at h0
        simp[h0,mrg]
        rw[Finmap.mem_iff]; aesop
        rw[Finmap.mem_iff]; aesop
  else
    have ⟨h1, h2⟩ := mrg.split_none h
    rw[Finmap.lookup_union_right h1]
    rw[Finmap.lookup_union_right h2]
    rw[Finmap.lookup_union_right h]
    apply ct.merge_refl

lemma HMerge.insert_lookup {H1 H2 H3 : Heap Srt} {l m} :
    HMerge (H1.insert l m) H2 H3 -> H3.lookup l = m := by
  intro mrg
  replace mrg := mrg l
  split at mrg <;> simp_all

lemma HMerge.insert_left {H1 H2 H3 : Heap Srt} l m :
    HMerge H1 H2 H3 -> l ∉ H3 -> m.srt ∉ ord.contra_set ->
    HMerge (H1.insert l m) H2 (H3.insert l m) := by
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

lemma HLower.split_contra {H3 : Heap Srt} :
    Contra H3 ->
    ∃ H1 H2, Contra H1 ∧ Contra H2 ∧ HMerge H1 H2 H3 := by
  intro lw
  existsi H3, H3; and_intros
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
  H.induction_on fun xs => by
    clear H; induction xs
    case H0 =>
      existsi ∅; simp; and_intros
      apply Contra.empty.merge_refl
      apply Contra.empty
    case IH l hd tl nn ih =>
      rw[<-Finmap.insert_toFinmap]
      rcases ih with ⟨H0, mrg0, ct0⟩
      if mm: hd.srt ∈ ord.contra_set then
        existsi H0.insert l hd; and_intros
        apply mrg0.insert_contra mm
        apply ct0.insert mm; rfl
      else
        existsi H0; and_intros
        apply mrg0.insert_left <;> assumption
        assumption

lemma HMerge.lookup_collision {H1 H2 H3 : Heap Srt} {l} :
    HMerge H1 H2 H3 -> l ∈ H1 -> H1.lookup l = H3.lookup l := by
  intro mrg h
  rw[Finmap.mem_iff] at h
  have ⟨m, e⟩ := h
  replace mrg := mrg l
  rw[e] at mrg; split at mrg <;> aesop

lemma HMerge.unique {H1 H2 H3 H4 : Heap Srt} :
    HMerge H1 H2 H3 -> HMerge H1 H2 H4 -> H3 = H4 := by
  intro mrg1 mrg2
  apply Finmap.ext_lookup; intro x
  replace mrg1 := mrg1 x
  replace mrg2 := mrg2 x
  split at mrg1
  all_goals split at mrg2 <;> aesop

lemma HMerge.insert_inv {H1 H2 H3 : Heap Srt} {l m} :
    HMerge (H1.insert l m) H2 H3 -> l ∉ H1 -> l ∉ H2 ->
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

lemma HMerge.erase {H1 H2 H3 : Heap Srt} {l m} :
    HMerge (H1.insert l m) H2 H3 -> l ∉ H1 ->
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

lemma HMerge.not_contra_inv {H1 H2 H3 : Heap Srt} {m} l :
    HMerge H1 H2 H3 -> H1.lookup l = some m ->
    m.srt ∉ ord.contra_set -> l ∉ H2 := by
  intro mrg e h
  replace mrg := mrg l
  rw[e] at mrg
  split at mrg <;> simp_all
  rw[Finmap.mem_iff]; aesop

lemma HMerge.shift {H1 H2 H3 : Heap Srt} {l m} :
    HMerge (Finmap.insert l m H1) H2 H3 ->
    l ∉ H1 -> m.srt ∉ ord.contra_set ->
    HMerge H1 (Finmap.insert l m H2) H3 := by
  intro mrg h1 h2 x
  replace mrg := mrg x
  if dec: x = l then
    subst_vars
    simp_all
    rw[<-Finmap.lookup_eq_none] at h1
    rw[h1]; revert mrg
    generalize e: Finmap.lookup x H3 = opt
    split <;> try simp_all
    intros; subst_vars; aesop
  else simp_all

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
  intro mrg1 mrg2; existsi Ha ∪ H2; and_intros
  . intro x
    replace mrg1 := mrg1 x
    replace mrg2 := mrg2 x
    split at mrg1 <;> simp_all
    . split at mrg2 <;> simp_all
      case h_1 e _ _ =>
        have h := Finmap.mem_of_lookup_eq_some e
        rw[Finmap.lookup_union_left h]
        rw[e]; aesop
    . split at mrg2 <;> simp_all
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
    . split at mrg2 <;> simp_all
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
  existsi H5, H6; and_intros
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

lemma SubHeap.insert (H : Heap Srt) l m :
    l ∉ H -> m.srt ∈ ord.contra_set -> SubHeap H (H.insert l m) := by
  intro h1 h2
  apply SubHeap.intro (Finmap.singleton l m)
  . intro x
    if e: x = l then
      subst_vars; simp
      assumption
    else
      rw[<-Finmap.mem_singleton x l m (β := fun _ => Cell Srt)] at e
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
  existsi H1 ∪ H0, H2 ∪ H0; and_intros
  . apply SubHeap.intro H0 <;> trivial
  . apply SubHeap.intro H0 <;> trivial
  . apply mrg.union_contra ct dsj
