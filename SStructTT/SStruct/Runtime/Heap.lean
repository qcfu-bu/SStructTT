import SStructTT.SStruct.Erasure.Syntax
import Mathlib.Data.Finmap

namespace SStruct.Runtime
variable {Srt : Type}

abbrev Heap := Finmap (fun (_ : Nat) => Tm Srt × Srt)

lemma Heap.fresh (H : @Heap Srt) : ∃ l, l ∉ H.keys := by
  generalize e1: H.keys = keys
  cases e2: keys.max with
  | bot =>
    rw [keys.max_eq_bot] at e2
    subst e2; exists 0
  | coe x =>
    exists x + 1
    apply keys.not_mem_of_max_lt _ e2
    simp

lemma Heap.erase_insert {H : @Heap Srt} {l v} :
    l ∉ H.keys -> (H.insert l v).erase l = H := by
  intro h
  apply Finmap.ext_lookup
  intro x
  cases Nat.decEq x l with
  | isTrue e =>
    subst e; simp
    rw [Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
    rw [h]
  | isFalse e =>
    rw [Finmap.lookup_erase_ne e]
    rw [Finmap.lookup_insert_of_ne _ e]

variable [ord : SrtOrder Srt]

def HLower (H : @Heap Srt) (s0 : Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | some (_, s) => s <= s0
    | none => True

lemma Heap.insert_lower {H} {m : Tm Srt} {l s1 s2} :
    s1 ≤ s2 -> HLower H s2 -> HLower (H.insert l (m, s1)) s2 := by
  intro lw; intro h x
  split <;> try simp
  case h_1 opt m1 s3 e =>
    cases x.decEq l with
    | isTrue => aesop
    | isFalse ne =>
      rw[Finmap.lookup_insert_of_ne _ ne] at e
      replace h := h x
      rw[e] at h; simp at h
      assumption

lemma Heap.erase_lower {H : @Heap Srt} {s l} :
    HLower H s -> HLower (H.erase l) s := by
  intro lw x
  cases x.decEq l with
  | isTrue => aesop
  | isFalse ne =>
    rw[Finmap.lookup_erase_ne ne]
    apply lw

lemma Heap.union {H1 H2 : @Heap Srt} {s1 s2 : Srt} :
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
      rw[h] at lw1; simp at lw1
      apply lw1.trans lw
    | .inr ⟨_, h⟩ =>
      simp at h
      replace lw2 := lw2 x
      rw[h] at lw2; simp at lw2
      assumption

def HMerge (H1 H2 H3 : @Heap Srt) : Prop :=
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
