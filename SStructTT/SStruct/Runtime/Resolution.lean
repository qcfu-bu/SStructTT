import SStructTT.SStruct.Runtime.Heap
import SStructTT.SStruct.Erasure.Erased

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

def HLookup (H1 : Heap Srt) (l : Nat) (m : Tm Srt) (H2 : Heap Srt) : Prop :=
  match H1.lookup l with
  | some ⟨n, s⟩ =>
    m = n ∧ if s ∈ ord.contra_set then H1 = H2 else H2 = H1.erase l
  | none => False

inductive Resolve : Heap Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {H x} :
    HLower H ord.e ->
    Resolve H (.var x) (.var x)

  | lam {H m m' c s} :
    HLower H s ->
    Resolve H m m' ->
    Resolve H (.lam m c s) (.lam m' c s)

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

  | prj {H1 H2 H3 m m' n n' c1 c2} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.prj m n c1 c2) (.prj m' n' c1 c2)

  | tt {H} :
    HLower H ord.e ->
    Resolve H .tt .tt

  | ff {H} :
    HLower H ord.e ->
    Resolve H .ff .ff

  | ite {H1 H2 H3 m m' n1 n1' n2 n2'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n1 n1' ->
    Resolve H2 n2 n2' ->
    Resolve H3 (.ite m n1 n2) (.ite m' n1' n2')

  | rw {H m m'} :
    Resolve H m m' ->
    Resolve H (.rw m) (.rw m')

  | ptr {H H' l m m'} :
    HLookup H l m H' ->
    Resolve H' m m' ->
    Resolve H (.ptr l) m'

  | null {H} :
    HLower H ord.e ->
    Resolve H .null .null

notation:50 H:50 " ;; " m:51 " ▷ " m':51 => Resolve H m m'

@[simp]def Resolved : Tm Srt -> Prop
  | .var _ => True
  | .lam m _ _ => Resolved m
  | .app m n => Resolved m ∧ Resolved n
  | .tup m n _ => Resolved m ∧ Resolved n
  | .prj m n _ _ => Resolved m ∧ Resolved n
  | .tt => True
  | .ff => True
  | .ite m n1 n2 => Resolved m ∧ Resolved n1 ∧ Resolved n2
  | .rw m => Resolved m
  | .ptr _ => False
  | .null => True

lemma Resolve.is_resolved {H : Heap Srt} {m m'} : H ;; m ▷ m' -> Resolved m' := by
  intro rs; induction rs
  all_goals aesop

inductive WellResolved :
  Heap Srt -> SStruct.Tm Srt -> Tm Srt -> Tm Srt -> SStruct.Tm Srt -> Prop
where
  | intro {H x y z A} :
    [] ;; [] ⊢ x ▷ y : A ->
    H ;; z ▷ y ->
    WellResolved H x y z A

notation:50 H:50 " ;; " x:51 " ▷ " y:51 " ◁ " z:51 " : " A:51 =>
  WellResolved H x y z A

lemma HLookup.not_mem {H1 H2 : Heap Srt} {l1 l2 m} :
    HLookup H1 l1 m H2 -> l2 ∉ H1.keys -> l2 ∉ H2.keys := by
  intro lk h
  rw[HLookup] at lk
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none]
  split at lk <;> try trivial
  case h_1 opt m' s e =>
    have ⟨e, h⟩ := lk; split_ifs at h
    case pos => subst_vars; assumption
    case neg =>
      subst_vars
      cases l2.decEq l1 with
      | isTrue => subst_vars; apply Finmap.lookup_erase
      | isFalse ne => rw[Finmap.lookup_erase_ne ne]; assumption

lemma HLookup.insert {H1 H2 : Heap Srt} {l1 l2 m n s} :
    HLookup H1 l1 m H2 -> l2 ∉ H1.keys ->
    HLookup (H1.insert l2 ⟨n, s⟩) l1 m (H2.insert l2 ⟨n, s⟩) := by
  intro lk h
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
  rw[HLookup]
  cases l1.decEq l2 with
  | isTrue =>
    subst_vars
    rw[HLookup] at lk
    rw[h] at lk; simp at lk
  | isFalse ne =>
    rw[H1.lookup_insert_of_ne ne]
    rw[HLookup] at lk
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

lemma Resolve.weaken {H : Heap Srt} {m m' n l} :
    H ;; m ▷ m' -> l ∉ H.keys -> H.insert l ⟨n, ord.e⟩ ;; m ▷ m' := by
  intro rs h
  induction rs generalizing l
  case var lw =>
    constructor
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]
    | isFalse ne =>
      rw[Finmap.lookup_insert_of_ne _ ne]
      apply lw
  case lam lw erm ih =>
    constructor <;> try aesop
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]; simp
      apply ord.e_min
    | isFalse ne =>
      rw[Finmap.lookup_insert_of_ne _ ne]
      apply lw
  case app mrg erm ern ihm ihn =>
    have ⟨h1, h2⟩ := mrg.split_none h
    replace ihm := ihm h1
    replace ihn := ihn h2
    apply Resolve.app _ ihm ihn
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]; simp
      apply ord.e_contra
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply mrg
  case tup mrg erm ern ihm ihn =>
    have ⟨h1, h2⟩ := mrg.split_none h
    replace ihm := ihm h1
    replace ihn := ihn h2
    apply Resolve.tup _ ihm ihn
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]; simp
      apply ord.e_contra
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply mrg
  case prj mrg erm ern ihm ihn =>
    have ⟨h1, h2⟩ := mrg.split_none h
    replace ihm := ihm h1
    replace ihn := ihn h2
    apply Resolve.prj _ ihm ihn
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]; simp
      apply ord.e_contra
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply mrg
  case tt lw =>
    constructor
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply lw
  case ff lw =>
    constructor
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply lw
  case ite mrg erm ern1 ern2 ihm ihn1 ihn2 =>
    have ⟨h1, h2⟩ := mrg.split_none h
    replace ihm := ihm h1
    replace ihn1 := ihn1 h2
    replace ihn2 := ihn2 h2
    apply Resolve.ite _ ihm ihn1 ihn2
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      repeat rw[Finmap.lookup_insert]; simp
      apply ord.e_contra
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply mrg
  case rw => constructor; aesop
  case ptr lw erm ih =>
    constructor
    . apply HLookup.insert
      assumption
      assumption
    . apply ih
      apply lw.not_mem h
  case null lw =>
    constructor
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      repeat rw[Finmap.lookup_insert]
    | isFalse ne =>
      rw[Finmap.lookup_insert_of_ne _ ne]
      apply lw
