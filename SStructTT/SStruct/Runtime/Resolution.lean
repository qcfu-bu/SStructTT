import SStructTT.SStruct.Static.Inversion
import SStructTT.SStruct.Runtime.Heap
import SStructTT.SStruct.Erasure.Step
import SStructTT.SStruct.Erasure.Inversion

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

  | lam {H m m' s} :
    HLower H s ->
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

  | drop {H1 H2 H3 m m' n n'} :
    HMerge H1 H2 H3 ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.drop m n) (.drop m' n')

  | ptr {H H' l m m'} :
    HLookup H l m H' ->
    Resolve H' m m' ->
    Resolve H (.ptr l) m'

  | null {H} :
    HLower H ord.e ->
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
  Heap Srt -> SStruct.Tm Srt -> Tm Srt -> Tm Srt -> SStruct.Tm Srt -> Prop
where
  | intro {H x y z A} :
    [] ;; [] ⊢ x ▷ y : A ->
    H ;; z ▷ y ->
    Resolved H x y z A

notation:50 H:50 " ;; " x:51 " ▷ " y:51 " ◁ " z:51 " : " A:51 =>
  Resolved H x y z A

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
  case drop mrg erm ern ihm ihn =>
    have ⟨h1, h2⟩ := mrg.split_none h
    replace ihm := ihm h1
    replace ihn := ihn h2
    apply Resolve.drop _ ihm ihn
    intro x
    cases x.decEq l with
    | isTrue =>
      subst_vars
      rw[Finmap.lookup_insert]; simp
      apply ord.e_contra
    | isFalse ne =>
      repeat rw[Finmap.lookup_insert_of_ne _ ne]
      apply mrg
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

lemma Erased.resolve_refl {Γ Δ} {H : Heap Srt} {m n A} :
    Γ ;; Δ ⊢ m ▷ n : A -> HLower H ord.e -> H ;; n ▷ n := by
  intro er lw
  induction er generalizing H
  case var =>
    constructor; assumption
  case lam_im ih =>
    constructor
    apply lw.trans (ord.e_min _)
    apply ih lw
  case lam_ex ih =>
    constructor
    apply lw.trans (ord.e_min _)
    apply ih lw
  case app_im ih =>
    have mrg := lw.merge_refl
    constructor
    . apply mrg
    . apply ih lw
    . constructor
      assumption
  case app_ex =>
    have mrg := lw.merge_refl
    constructor <;> aesop
  case tup_im ih =>
    have mrg := lw.merge_refl
    constructor
    . apply mrg
    . apply ih lw
    . constructor
      assumption
  case tup_ex =>
    have mrg := lw.merge_refl
    constructor <;> aesop
  case prj_im =>
    have mrg := lw.merge_refl
    constructor <;> aesop
  case prj_ex =>
    have mrg := lw.merge_refl
    constructor <;> aesop
  case tt => constructor; assumption
  case ff => constructor; assumption
  case ite =>
    have mrg := lw.merge_refl
    constructor <;> aesop
  case rw => aesop
  case drop ih =>
    have mrg := lw.merge_refl
    constructor <;> aesop
  case conv => aesop

lemma Erased.resolve_id {Γ Δ} {H : Heap Srt} {x y z A} :
    Γ ;; Δ ⊢ x ▷ y : A -> H ;; y ▷ z -> y = z := by
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
    case tup rsn =>
      cases rsn; aesop
  case tup_ex => cases rs; aesop
  case prj_im => cases rs; aesop
  case prj_ex => cases rs; aesop
  case tt => cases rs; simp
  case ff => cases rs; simp
  case ite => cases rs; aesop
  case rw => aesop
  case drop => cases rs; aesop
  case conv => aesop

lemma HLookup.insert_lookup {H H' : Heap Srt} {m n l s} :
    HLookup (H.insert l ⟨m, s⟩) l n H' ->
    m = n ∧
      if s ∈ ord.contra_set
      then H' = H.insert l ⟨m, s⟩
      else H' = H.erase l := by
  intro lk
  simp_rw[HLookup,Finmap.lookup_insert] at lk
  replace ⟨e, lk⟩ := lk; subst_vars; simp
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

lemma HLookup.merge {H1 H1' H2 H3 : Heap Srt} {m l} :
    HLookup H1 l m H1' -> HMerge H1 H2 H3 ->
    ∃ H3', HLookup H3 l m H3' ∧ HMerge H1' H2 H3' := by
  intro lk mrg
  rw[HLookup] at lk; split at lk <;> try trivial
  case h_1 opt n s e =>
    replace ⟨_, lk⟩ := lk; subst_vars
    split_ifs at lk
    case pos h =>
      subst_vars
      exists H3; and_intros
      . replace mrg := mrg l
        rw[e] at mrg; split at mrg <;> try trivial
        case h_1 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
        case h_2 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
      . assumption
    case neg h =>
      subst_vars
      exists H3.erase l; and_intros
      . replace mrg := mrg l
        rw[e] at mrg; split at mrg <;> try trivial
        case h_1 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
        case h_2 e h2 h3 =>
          rcases mrg with ⟨_, _, _, _, _⟩
          cases e; subst_vars
          unfold HLookup
          simp_rw[h3]; simp[h]
      . intro x
        replace mrg := mrg x
        cases x.decEq l with
        | isTrue =>
          subst_vars
          rw[e] at mrg; split at mrg <;> try trivial
          case h_1 e _ _ =>
            rcases mrg with ⟨_, _, _, _, _⟩
            cases e; subst_vars
            contradiction
          case h_2 e h1 h2 =>
            rcases mrg with ⟨_, _⟩
            cases e; subst_vars
            simp[h1,h2,e]
        | isFalse ne =>
          simp[Finmap.lookup_erase_ne ne]
          assumption

lemma HLookup.lower {H H' : Heap Srt} {m l s} :
    HLookup H l m H' -> HLower H s -> HLower H' s := by
  intro lk
  unfold HLookup at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk; subst_vars
  split_ifs at lk <;> subst_vars
  . simp
  . apply HLower.erase_lower

lemma HLookup.collision {H1 H1' H2 H3 H3' : Heap Srt} {m n l} :
    HMerge H1 H2 H3 ->
    HLookup H3 l m H3' ->
    HLookup H1 l n H1' ->
    m = n ∧ HMerge H1' H2 H3' := by
  intro mrg lk1 lk2
  unfold HLookup at lk1 lk2
  split at lk1 <;> try trivial
  split at lk2 <;> try trivial
  replace ⟨_, lk1⟩ := lk1; subst_vars
  replace ⟨_, lk2⟩ := lk2; subst_vars
  case h_1 h1 _ _ _ h2 =>
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
      aesop
    | isFalse ne =>
      simp[Finmap.lookup_erase_ne ne]
      assumption

lemma HLookup.resolve {H1 H2 H3 H3' : Heap Srt} {l m n} :
    HLookup H3 l m H3' -> H1 ;; .ptr l ▷ n -> HMerge H1 H2 H3 ->
    ∃ H1', HMerge H1' H2 H3' ∧ H1' ;; m ▷ n := by
  intro lk1 rs mrg; cases rs
  case ptr H1' _ lk2 erm =>
    have ⟨_, mrg'⟩ := lk1.collision mrg lk2; subst_vars
    exists H1'

@[simp]def NF (i : Nat) : Tm Srt -> Prop
  | .var x => x < i
  | .lam m _ => NF (i + 1) m
  | .app m n => NF i m ∧ NF i n
  | .tup m n _ => NF i m ∧ NF i n
  | .prj m n => NF i m ∧ NF (i + 2) n
  | .tt => True
  | .ff => True
  | .ite m n1 n2 => NF i m ∧ NF i n1 ∧ NF i n2
  | .drop m n => NF i m ∧ NF i n
  | .ptr _ => True
  | .null => True

def WR (H : Heap Srt) : Prop :=
  ∀ l,
    match H.lookup l with
    | none => True
    | some ⟨.lam m s1, s2⟩ => NF 1 m ∧ s1 = s2
    | some ⟨.tup (.ptr _) .null s1, s2⟩ => s1 = s2
    | some ⟨.tup (.ptr _) (.ptr _) s1, s2⟩ => s1 = s2
    | some ⟨.tt, s⟩ => s = ord.e
    | some ⟨.ff, s⟩ => s = ord.e
    | _ => False

lemma Erased.nf {Γ Δ} {m A : SStruct.Tm Srt} {m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> NF (Γ.length) m' := by
  intro erm; induction erm
  all_goals try (solve | aesop)
  case var wf hs =>
    replace hs := wf.hasStatic hs
    apply hs.var_lt_length

lemma HLookup.nf {H H' : Heap Srt} {m l} :
    HLookup H l m H' -> WR H -> NF 0 m := by
  intro lk wr
  unfold HLookup at lk; split at lk <;> try trivial
  case h_1 m' s h =>
    replace ⟨_, lk⟩ := lk; subst_vars
    split_ifs at lk
    case pos =>
      subst_vars
      replace wr := wr l
      simp[h] at wr; split at wr
      all_goals simp_all
    case neg =>
      subst_vars
      replace wr := wr l
      simp[h] at wr; split at wr
      all_goals simp_all

lemma HMerge.merge_wr {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> WR H1 -> WR H2 -> WR H3 := by
  intro mrg wr1 wr2 x
  replace wr1 := wr1 x
  replace wr2 := wr2 x
  replace mrg := mrg x
  revert wr1 wr2
  generalize e1: H1.lookup x = r1
  generalize e2: H2.lookup x = r2
  generalize e3: H3.lookup x = r3
  rw[e1,e2,e3] at mrg
  split at mrg <;> simp_all

lemma HMerge.split_wr' {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> WR H3 -> WR H1 := by
  intro mrg wr3 x
  replace wr3 := wr3 x
  replace mrg := mrg x
  revert wr3
  generalize e1: H1.lookup x = r1
  generalize e2: H2.lookup x = r2
  generalize e3: H3.lookup x = r3
  rw[e1,e2,e3] at mrg
  split at mrg <;> simp_all

lemma HMerge.split_wr {H1 H2 H3 : Heap Srt} :
    HMerge H1 H2 H3 -> WR H3 -> WR H1 ∧ WR H2 := by
  intro mrg wr; and_intros
  . apply mrg.split_wr' wr
  . apply mrg.sym.split_wr' wr

lemma HLookup.wr_image {H H' : Heap Srt} {m l} :
    HLookup H l m H' -> WR H -> WR H' := by
  intro lk wr x
  replace wr := wr x
  unfold HLookup at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk
  split_ifs at lk <;> simp_all
  subst_vars
  cases x.decEq l with
  | isTrue => subst_vars; simp[Finmap.lookup_erase]
  | isFalse ne =>
    simp[Finmap.lookup_erase_ne ne]
    assumption

omit ord in
lemma NF.weaken {m : Tm Srt} {i j} : NF i m -> i ≤ j -> NF j m := by
  induction m generalizing i j <;> try (solve| aesop)
  case var x =>
    unfold Var at x
    intros h1 h2
    apply h1.trans_le h2

lemma Resolve.nf_image {H : Heap Srt} {m m' i} :
    H ;; m ▷ m' -> WR H -> NF i m -> NF i m' := by
  intro rs wr nf; induction rs generalizing i
  all_goals try (solve | aesop)
  case app mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case tup mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case prj mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case ite mrg erm ern1 ern2 ihm ihn1 ihn2 =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case drop mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case ptr lk erm ihm =>
    have wr' := lk.wr_image wr
    have nf0 := lk.nf wr
    replace nf0 := ihm wr' nf0
    apply nf0.weaken
    simp

lemma Resolve.nf_preimage {H : Heap Srt} {m m' i} :
    H ;; m ▷ m' -> WR H -> NF i m' -> NF i m := by
  intro rs wr nf; induction rs generalizing i
  all_goals try (solve | aesop)
  case app mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case tup mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case prj mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case ite mrg erm ern1 ern2 ihm ihn1 ihn2 =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case drop mrg erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop

lemma HLookup.not_wr_ptr {H H' : Heap Srt} {l i} :
    HLookup H l (.ptr i) H' -> ¬ WR H := by
  intro lk wr
  unfold HLookup at lk
  split at lk <;> try trivial
  case h_1 h =>
    replace ⟨_, lk⟩ := lk; subst_vars
    replace wr := wr l
    simp_rw[h] at wr

lemma HLookup.not_wr_var {H H' : Heap Srt} {l i} :
    HLookup H l (.var i) H' -> ¬ WR H := by
  intro lk wr
  unfold HLookup at lk
  split at lk <;> try trivial
  case h_1 h =>
    replace ⟨_, lk⟩ := lk; subst_vars
    replace wr := wr l
    simp_rw[h] at wr

lemma HLookup.not_wr_null {H H' : Heap Srt} {l} :
    HLookup H l .null H' -> ¬ WR H := by
  intro lk wr
  unfold HLookup at lk
  split at lk <;> try trivial
  case h_1 h =>
    replace ⟨_, lk⟩ := lk; subst_vars
    replace wr := wr l
    simp_rw[h] at wr

lemma HLookup.contra_lam {H H' : Heap Srt} {l m s} :
    HLookup H l (.lam m s) H' -> WR H ->
      if s ∈ ord.contra_set then H = H' else H' = H.erase l := by
  intro lk wr
  unfold HLookup at lk
  replace wr := wr l; aesop

lemma HLookup.contra_tup {H H' : Heap Srt} {l m n s} :
    HLookup H l (.tup m n s) H' -> WR H ->
      if s ∈ ord.contra_set then H = H' else H' = H.erase l := by
  intro lk wr
  unfold HLookup at lk
  replace wr := wr l; aesop

lemma HLookup.contra_tt {H H' : Heap Srt} {l} :
    HLookup H l .tt H' -> WR H -> H = H' := by
  intro lk wr
  unfold HLookup at lk
  replace wr := wr l
  split at lk <;> simp_all
  replace ⟨_, lk⟩ := lk; subst_vars
  simp[ord.e_contra] at lk
  assumption

lemma HLookup.contra_ff {H H' : Heap Srt} {l} :
    HLookup H l .ff H' -> WR H -> H = H' := by
  intro lk wr
  unfold HLookup at lk
  replace wr := wr l
  split at lk <;> simp_all
  replace ⟨_, lk⟩ := lk; subst_vars
  simp[ord.e_contra] at lk
  assumption

lemma Resolve.var_inv {H : Heap Srt} {m x} :
    H ;; m ▷ .var x -> WR H -> HLower H ord.e := by
  generalize e: Tm.var x = m'
  intro rs wr; induction rs <;> try trivial
  case ptr H H' l m m' lkm rsm ih =>
    subst_vars
    cases m <;> cases rsm
    . exfalso; apply lkm.not_wr_var wr
    . exfalso; apply lkm.not_wr_ptr wr

lemma Resolve.lam_inv {H : Heap Srt} {m m' s} :
    H ;; m ▷ .lam m' s -> WR H -> HLower H s := by
  generalize e: Tm.lam m' s = t
  intro rs wr; induction rs <;> try trivial
  case lam => cases e; assumption
  case ptr H H' l m m' lkm rsm ih =>
    subst_vars
    cases m <;> cases rsm
    case lam lw =>
      unfold HLookup at lkm
      split at lkm <;> try trivial
      case h_1 h =>
        replace ⟨_, lkm⟩ := lkm
        split_ifs at lkm
        case pos =>
          subst_vars; assumption
        case neg =>
          subst_vars
          replace wr := wr l
          simp[h] at wr; have ⟨_, _⟩ := wr; subst_vars
          intro x; replace lw := lw x
          cases x.decEq l with
          | isTrue => subst_vars; rw[h]
          | isFalse ne =>
            rw[Finmap.lookup_erase_ne ne] at lw
            assumption
    case ptr =>
      exfalso; apply lkm.not_wr_ptr wr

lemma Resolve.tt_inv {H : Heap Srt} {m} :
    H ;; m ▷ .tt -> WR H -> HLower H ord.e := by
  generalize e: Tm.tt = t
  intro rs wr; induction rs <;> try trivial
  case ptr H H' l m m' lkm rsm ih =>
    subst_vars
    cases m <;> cases rsm
    case tt lw =>
      unfold HLookup at lkm
      split at lkm <;> try trivial
      case h_1 h =>
        replace ⟨_, lkm⟩ := lkm
        split_ifs at lkm
        case pos =>
          subst_vars; assumption
        case neg =>
          subst_vars
          replace wr := wr l
          simp[h] at wr; subst_vars
          intro x; replace lw := lw x
          cases x.decEq l with
          | isTrue => subst_vars; rw[h]
          | isFalse ne =>
            rw[Finmap.lookup_erase_ne ne] at lw
            assumption
    case ptr =>
      exfalso; apply lkm.not_wr_ptr wr

lemma Resolve.null_inv {H : Heap Srt} {m} :
    H ;; m ▷ .null -> WR H -> HLower H ord.e ∧ m = .null := by
  generalize e: Tm.null = t
  intro rs wr; induction rs <;> try trivial
  case ptr H H' l m m' lkm rsm ih =>
    subst_vars
    cases m <;> cases rsm
    case null lw =>
      exfalso
      apply lkm.not_wr_null wr
    case ptr =>
      exfalso; apply lkm.not_wr_ptr wr

lemma Resolve.ff_inv {H : Heap Srt} {m} :
    H ;; m ▷ .ff -> WR H -> HLower H ord.e := by
  generalize e: Tm.ff = t
  intro rs wr; induction rs <;> try trivial
  case ptr H H' l m m' lkm rsm ih =>
    subst_vars
    cases m <;> cases rsm
    case ff lw =>
      unfold HLookup at lkm
      split at lkm <;> try trivial
      case h_1 h =>
        replace ⟨_, lkm⟩ := lkm
        split_ifs at lkm
        case pos =>
          subst_vars; assumption
        case neg =>
          subst_vars
          replace wr := wr l
          simp[h] at wr; subst_vars
          intro x; replace lw := lw x
          cases x.decEq l with
          | isTrue => subst_vars; rw[h]
          | isFalse ne =>
            rw[Finmap.lookup_erase_ne ne] at lw
            assumption
    case ptr =>
      exfalso; apply lkm.not_wr_ptr wr

theorem Resolved.resolution {H : Heap Srt} {x y z A s i} :
    H ;; x ▷ y ◁ z : A ->
    [] ⊢ A : .srt s i ->
    Value y -> WR H -> HLower H s := by
  intro ⟨er, rs⟩
  revert er
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro er ty vl wr; induction er generalizing H z s i
  all_goals subst_vars; try (solve | cases vl)
  case lam_im =>
    have ⟨_, _, _, _, rd⟩ := ty.pi_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    apply rs.lam_inv wr
  case lam_ex =>
    have ⟨_, _, _, _, rd⟩ := ty.pi_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    apply rs.lam_inv wr
  case tup_im ihm =>
    have ⟨_, _, _, _, _, le, _, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp at ihm
    cases z <;> cases rs
    case tup mrg rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg.split_wr wr
      have lw1 := ihm rsm tyA vl1 wr1
      have ⟨lw2, _⟩ := rsn.null_inv wr2; subst_vars
      replace lw1 := lw1.trans le
      replace lw2 := lw2.trans (ord.e_min s)
      apply mrg.lower_image lw1 lw2
    case ptr l _ m lk rs =>
      cases m <;> cases rs
      case tup H1 H2 mrg rsm rsn =>
        have wr' := lk.wr_image wr
        have ⟨wr1, wr2⟩ := mrg.split_wr wr'
        have lw1 := ihm rsm tyA vl1 wr1
        have ⟨lw2, _⟩ := rsn.null_inv wr2; subst_vars
        replace lw1 := lw1.trans le
        replace lw2 := lw2.trans (ord.e_min s)
        have lw := mrg.lower_image lw1 lw2
        unfold HLookup at lk
        split at lk <;> try trivial
        case h_1 h =>
          replace ⟨_, lk⟩ := lk
          split_ifs at lk
          case pos =>
            subst_vars; assumption
          case neg =>
            subst_vars
            replace wr := wr l
            simp[h] at wr; split at wr <;> try simp_all
            case h_3 h =>
              have ⟨⟨_, _⟩, _⟩ := h; subst_vars
              intro x; replace lw := lw x
              cases x.decEq l with
              | isTrue => subst_vars; rw[h]
              | isFalse ne =>
                rw[Finmap.lookup_erase_ne ne] at lw
                assumption
      case ptr =>
        exfalso; apply lk.not_wr_ptr wr
  case tup_ex erm ern ihm ihn mrg =>
    cases mrg
    have ⟨_, _, _, _, _, le1, le2, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp_all
    cases z <;> cases rs
    case tup mrg rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg.split_wr wr
      have lw1 := ihm rsm tyA wr1
      have lw2 := ihn rsn (tyB.subst erm.toStatic) wr2
      replace lw1 := lw1.trans le1
      replace lw2 := lw2.trans le2
      apply mrg.lower_image lw1 lw2
    case ptr l _ m lk rs =>
      cases m <;> cases rs
      case tup H1 H2 mrg rsm rsn =>
        have wr' := lk.wr_image wr
        have ⟨wr1, wr2⟩ := mrg.split_wr wr'
        have lw1 := ihm rsm tyA wr1
        have lw2 := ihn rsn (tyB.subst erm.toStatic) wr2
        replace lw1 := lw1.trans le1
        replace lw2 := lw2.trans le2
        have lw := mrg.lower_image lw1 lw2
        unfold HLookup at lk
        split at lk <;> try trivial
        case h_1 h =>
          replace ⟨_, lk⟩ := lk
          split_ifs at lk
          case pos =>
            subst_vars; assumption
          case neg =>
            subst_vars
            replace wr := wr l
            simp[h] at wr; split at wr <;> try simp_all
            case h_3 h =>
              have ⟨⟨_, _⟩, _⟩ := h; subst_vars
              intro x; replace lw := lw x
              cases x.decEq l with
              | isTrue => subst_vars; rw[h]
              | isFalse ne =>
                rw[Finmap.lookup_erase_ne ne] at lw
                assumption
            case h_4 h =>
              have ⟨⟨_, _⟩, _⟩ := h; subst_vars
              intro x; replace lw := lw x
              cases x.decEq l with
              | isTrue => subst_vars; rw[h]
              | isFalse ne =>
                rw[Finmap.lookup_erase_ne ne] at lw
                assumption
      case ptr =>
        exfalso; apply lk.not_wr_ptr wr
  case tt =>
    have lw := rs.tt_inv wr
    apply lw.trans (ord.e_min s)
  case ff =>
    have lw := rs.ff_inv wr
    apply lw.trans (ord.e_min s)
  case rw tyA tyn erm ihm =>
    have ⟨eq, _⟩ := tyn.closed_idn tyA
    have ⟨s, i, ty'⟩ := erm.validity
    have ⟨x, rd1, rd2⟩ := Static.Step.cr eq.sym
    have ty1 := ty.preservation' rd1
    have ty2 := ty'.preservation' rd2
    have e := Static.Typed.unique ty1 ty2
    simp_all; apply ihm <;> try assumption
  case conv eq _ erm ih =>
    simp_all
    have ⟨s, i, tyA⟩ := erm.validity
    have ⟨x, rd1, rd2⟩ := Static.Step.cr eq
    have tyx1 := tyA.preservation' rd1
    have tyx2 := ty.preservation' rd2
    have e := tyx1.unique tyx2; subst_vars
    aesop

lemma HLookup.wr_value {H H' : Heap Srt} {m l} :
    HLookup H l m H' -> WR H -> Value m := by
  intro lk wr
  replace wr := wr l
  revert lk
  revert wr
  unfold HLookup
  generalize H.lookup l = r
  split <;> aesop

lemma Resolve.value_image {H : Heap Srt} {m m'} :
    H ;; m ▷ m' -> WR H -> Value m -> Value m' := by
  intro rsm wr vl; induction rsm <;> try (solve|aesop)
  all_goals try (solve|cases vl)
  case tup mrg rsm rsn ihm ihn =>
    cases vl; case tup vl1 vl2 =>
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    replace ihm := ihm wr1 vl1
    replace ihn := ihn wr2 vl2
    constructor <;> assumption
  case ptr lw rs ih =>
    have vl := lw.wr_value wr
    have wr := lw.wr_image wr
    apply ih wr vl

lemma Resolve.ptr_value {H : Heap Srt} {n l} :
    H ;; .ptr l ▷ n -> WR H -> Value n := by
  intro rs wr; cases rs
  case ptr lk rs =>
    apply rs.value_image (lk.wr_image wr)
    apply lk.wr_value wr
