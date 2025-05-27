import SStructTT.SStruct.Static.Inversion
import SStructTT.SStruct.Runtime.Heap
import SStructTT.SStruct.Erasure.Step
import SStructTT.SStruct.Erasure.Inversion

namespace SStruct.Erasure
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

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

omit ord in
lemma NF.weaken {m : Tm Srt} {i j} : NF i m -> i ≤ j -> NF j m := by
  induction m generalizing i j <;> try (solve| aesop)
  case var x =>
    unfold Var at x
    intros h1 h2
    apply h1.trans_le h2

lemma Erased.nf {Γ Δ} {m A : SStruct.Tm Srt} {m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> NF (Γ.length) m' := by
  intro erm; induction erm
  all_goals try (solve | aesop)
  case var wf hs =>
    replace hs := wf.hasStatic hs
    apply hs.var_lt_length

lemma Erased.nf_stack {Γ Δ} {m A : SStruct.Tm Srt} {m' i} :
    Γ ;; Δ ⊢ m ▷ m' : A -> NF i m' -> Stack Δ i := by
  intro erm nf; induction erm generalizing i
  case var hs =>
    simp at nf
    apply hs.stack nf
  case lam_im ihm =>
    simp at nf
    have st := ihm nf
    cases st
    case nil im =>
      simp at im
      constructor
      apply im
    case cons => assumption
  case lam_ex ihm =>
    simp at nf
    have st := ihm nf
    cases st
    case nil im => simp at im
    case cons => assumption
  case app_im ihm => simp at nf; aesop
  case app_ex mrg _ _ ihm ihn =>
    simp at nf
    have ⟨nf1, nf2⟩ := nf
    replace ihm := ihm nf1
    replace ihn := ihn nf2
    apply mrg.stack_image ihm ihn
  case tup_im ihm => simp at nf; aesop
  case tup_ex mrg _ _ _ ihm ihn =>
    simp at nf
    have ⟨nf1, nf2⟩ := nf
    replace ihm := ihm nf1
    replace ihn := ihn nf2
    apply mrg.stack_image ihm ihn
  case prj_im mrg _ _ _ ihm ihn =>
    simp at nf
    have ⟨nf1, nf2⟩ := nf
    replace ihm := ihm nf1
    replace ihn := ihn nf2
    cases ihn <;> try simp_all
    case cons ihn =>
      cases ihn <;> try simp_all
      apply mrg.stack_image <;> assumption
  case prj_ex mrg _ _ _ ihm ihn =>
    simp at nf
    have ⟨nf1, nf2⟩ := nf
    replace ihm := ihm nf1
    replace ihn := ihn nf2
    cases ihn <;> try simp_all
    case cons ihn =>
      cases ihn <;> try simp_all
      apply mrg.stack_image <;> assumption
  case tt =>
    constructor
    assumption
  case ff =>
    constructor
    assumption
  case ite mrg _ _ _ _ ihm ihn1 ihn2 =>
    simp at nf
    rcases nf with ⟨nf0, nf1, nf2⟩
    replace ihm := ihm nf0
    replace ihn1 := ihn1 nf1
    apply mrg.stack_image ihm ihn1
  case rw => aesop
  case drop mrg _ _ _ _ ihm ihn =>
    simp at nf
    have ⟨nf1, nf2⟩ := nf
    replace ihm := ihm nf1
    replace ihn := ihn nf2
    apply mrg.stack_image ihm ihn
  case conv => aesop

namespace Runtime

/- Possibly NULL pointers. -/
@[scoped aesop safe [constructors]]
inductive Nullptr : Tm Srt -> Prop where
  | ptr {l} : Nullptr (.ptr l)
  | null    : Nullptr .null

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

def HLookup (H1 : Heap Srt) (l : Nat) (m : Tm Srt) (H2 : Heap Srt) : Prop :=
  match H1.lookup l with
  | some (m', s) =>
    m = m' ∧ if s ∈ ord.contra_set then H1 = H2 else H2 = H1.erase l
  | none => False

inductive Resolve : Heap Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {H x} :
    Contra H ->
    Resolve H (.var x) (.var x)

  | lam {H m m' s} :
    (s ∈ ord.contra_set -> Contra H) ->
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
    Contra H ->
    Resolve H .tt .tt

  | ff {H} :
    Contra H ->
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
    HLookup H1 l m H2 ->
    Resolve H2 m m' ->
    Resolve H1 (.ptr l) m'

  | null {H} :
    Contra H ->
    Resolve H .null .null

notation:50 H:50 " ⊢ " m:51 " ▷ " m':51 => Resolve H m m'

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

lemma Resolve.is_resolved {H : Heap Srt} {m m'} : H ⊢ m ▷ m' -> IsResolved m' := by
  intro rs; induction rs
  all_goals aesop

inductive Resolved :
  Static.Ctx Srt -> Dynamic.Ctx Srt -> Heap Srt ->
  SStruct.Tm Srt -> Tm Srt -> Tm Srt -> SStruct.Tm Srt -> Prop
where
  | intro {Γ Δ H x y z A} :
    Γ ;; Δ ⊢ x ▷ y : A ->
    H ⊢ z ▷ y ->
    WR H ->
    Resolved Γ Δ H x y z A

notation:50 Γ:50 " ;; " Δ:51 " ;; " H:51 " ⊢ " x:51 " ▷ " y:51 " ◁ " z:51 " : " A:51 =>
  Resolved Γ Δ H x y z A

lemma WR.empty : @WR Srt _ ∅ := by intro l; simp

lemma WR.erase {H : Heap Srt} l : WR H -> WR (H.erase l) := by
  intro wr x
  cases x.decEq l with
  | isTrue => subst_vars; simp
  | isFalse ne => simp[ne]; apply wr

lemma WR.nf {H : Heap Srt} l m s :
    WR H -> H.lookup l = some (m, s) -> NF 0 m := by
  intro wr h
  replace wr := wr l
  rw[h] at wr
  split at wr <;> try aesop

lemma WR.lookup {H : Heap Srt} l m s :
    WR H -> H.lookup l = some (m, s) -> Value m := by
  intro wr e
  replace wr := wr l
  rw[e] at wr
  split at wr <;> aesop

lemma WR.insert_lam {H : Heap Srt} {l m s} :
    WR H -> NF 1 m -> WR (H.insert l (.lam m s, s)) := by
  intro wr nf x
  cases x.decEq l with
  | isTrue => subst_vars; simp; assumption
  | isFalse ne => simp[ne]; apply wr

lemma WR.insert_tup {H : Heap Srt} {l l1 p s} :
    WR H -> Nullptr p -> WR (H.insert l (.tup (.ptr l1) p s, s)) := by
  intro wr np x
  cases x.decEq l with
  | isTrue =>
    subst_vars; simp
    cases np <;> simp
  | isFalse ne => simp[ne]; apply wr

lemma WR.insert_tt {H : Heap Srt} {l} :
    WR H -> WR (H.insert l (.tt, ord.e)) := by
  intro wr x
  cases x.decEq l with
  | isTrue => subst_vars; simp
  | isFalse ne => simp[ne]; apply wr

lemma WR.insert_ff {H : Heap Srt} {l} :
    WR H -> WR (H.insert l (.ff, ord.e)) := by
  intro wr x
  cases x.decEq l with
  | isTrue => subst_vars; simp
  | isFalse ne => simp[ne]; apply wr

lemma HLookup.lookup {H1 H2 : Heap Srt} {l m} :
    HLookup H1 l m H2 ->
    ∃ s, H1.lookup l = some (m, s) ∧
      if s ∈ ord.contra_set then H2 = H1 else H2 = H1.erase l := by
  intro lk
  unfold HLookup at lk; split at lk <;> aesop

lemma HLookup.not_mem {H1 H2 : Heap Srt} {l1 l2 m} :
    HLookup H1 l1 m H2 -> l2 ∉ H1.keys -> l2 ∉ H2.keys := by
  intro lk h
  rw[HLookup] at lk
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none] at h
  rw[Finmap.mem_keys,<-Finmap.lookup_eq_none]
  split at lk <;> try trivial
  case h_1 opt m' s e =>
    have ⟨_, h⟩ := lk; split_ifs at h
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

lemma HLookup.insert_lookup {H H' : Heap Srt} {m n l s} :
    HLookup (H.insert l (m, s)) l n H' ->
    m = n ∧
      if s ∈ ord.contra_set
      then H' = H.insert l (m, s)
      else H' = H.erase l := by
  intro lk
  simp_rw[HLookup,Finmap.lookup_insert] at lk
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

lemma HLookup.merge {H1 H1' H2 H3 : Heap Srt} {l m} :
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
            cases e; simp[h1,h2,e]
        | isFalse ne =>
          simp[Finmap.lookup_erase_ne ne]
          assumption

lemma HLookup.weaken_image {H H' : Heap Srt} {l m} :
    HLookup H l m H' -> Weaken H -> Weaken H' := by
  intro lk
  unfold HLookup at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk; subst_vars
  split_ifs at lk <;> subst_vars
  . simp
  . intro wk; apply wk.erase

lemma HLookup.contra_image {H H' : Heap Srt} {l m} :
    HLookup H l m H' -> Contra H -> Contra H' := by
  intro lk
  unfold HLookup at lk
  split at lk <;> try trivial
  replace ⟨_, lk⟩ := lk; subst_vars
  split_ifs at lk <;> subst_vars
  . simp
  . intro ct; apply ct.erase

lemma HLookup.collision {H1 H1' H2 H3 H3' : Heap Srt} {l m n} :
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

lemma HLookup.nf {H H' : Heap Srt} {l m} :
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

lemma HLookup.wr_image {H H' : Heap Srt} {l m} :
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

lemma HLookup.wr_value {H H' : Heap Srt} {m l} :
    HLookup H l m H' -> WR H -> Value m := by
  intro lk wr
  replace wr := wr l
  revert lk
  revert wr
  unfold HLookup
  generalize H.lookup l = r
  split <;> aesop

lemma Erased.resolve_refl {H : Heap Srt} {Γ Δ m n A} :
    Γ ;; Δ ⊢ m ▷ n : A -> Contra H -> Weaken H -> H ⊢ n ▷ n := by
  intro er ct wk
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
    . apply ih
    . constructor
      assumption
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

lemma Erased.resolve_id {Γ Δ} {H : Heap Srt} {x y z A} :
    Γ ;; Δ ⊢ x ▷ y : A -> H ⊢ y ▷ z -> y = z := by
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

lemma Resolve.nf_image {H : Heap Srt} {m m' i} :
    H ⊢ m ▷ m' -> WR H -> NF i m -> NF i m' := by
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
  case ptr H1 H2 l m m' lk erm ihm =>
    have ⟨s, lk0, _⟩ := lk.lookup
    have nf := wr.nf l m _ lk0
    have wr := lk.wr_image wr
    apply ihm wr (nf.weaken (by simp))

lemma Resolve.nf_preimage {H : Heap Srt} {m m' i} :
    H ⊢ m ▷ m' -> WR H -> NF i m' -> NF i m := by
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

lemma Resolve.contra_merge {H1 H2 H3 : Heap Srt} {m m'} :
    HMerge H1 H2 H3 -> Contra H2 -> H1 ⊢ m ▷ m' -> H3 ⊢ m ▷ m' := by
  intro mrg ct2 rsm; induction rsm generalizing H2 H3
  case var H1 x ct1 =>
    have ct := mrg.contra_image ct1 ct2
    constructor; assumption
  case lam ct1 rsm ihm =>
    replace ihm := ihm mrg ct2
    constructor
    . intro h
      replace ct1 := ct1 h
      apply mrg.contra_image ct1 ct2
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
    have ct := mrg.contra_image ct1 ct2
    constructor; assumption
  case ff ct1 =>
    have ct := mrg.contra_image ct1 ct2
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
    have lw := mrg.contra_image ct1 ct2
    constructor; assumption

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
    H ⊢ m ▷ .var x -> WR H -> Contra H := by
  generalize e: Tm.var x = m'
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases rsm
    case var => exfalso; apply lk.not_wr_var wr
    case ptr => exfalso; apply lk.not_wr_ptr wr

lemma Resolve.lam_inv {H : Heap Srt} {m m' s} :
    H ⊢ m ▷ .lam m' s -> WR H -> (s ∈ ord.contra_set -> Contra H) := by
  generalize e: Tm.lam m' s = t
  intro rs wr; induction rs <;> try trivial
  case lam => cases e; assumption
  case ptr l m m' lk rsm ih =>
    subst_vars; cases rsm
    case lam ct =>
      have ⟨s, lk0, ifq⟩ := lk.lookup
      have wr := wr l; simp[lk0] at wr
      rcases wr with ⟨nf, e⟩; subst e
      intro h; replace ct := ct h
      simp[h] at ifq; subst ifq
      assumption
    case ptr => exfalso; apply lk.not_wr_ptr wr

lemma Resolve.tt_inv {H : Heap Srt} {m} :
    H ⊢ m ▷ .tt -> WR H -> Contra H := by
  generalize e: Tm.tt = t
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases rsm
    case tt =>
      have ⟨s, lk0, ifq⟩ := lk.lookup
      have wr := wr l; simp[lk0] at wr; subst wr
      simp[ord.e_contra] at ifq; subst ifq
      assumption
    case ptr => exfalso; apply lk.not_wr_ptr wr

lemma Resolve.ff_inv {H : Heap Srt} {m} :
    H ⊢ m ▷ .ff -> WR H -> Contra H := by
  generalize e: Tm.ff = t
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases rsm
    case ff =>
      have ⟨s, lk0, ifq⟩ := lk.lookup
      have wr := wr l; simp[lk0] at wr; subst wr
      simp[ord.e_contra] at ifq; subst ifq
      assumption
    case ptr => exfalso; apply lk.not_wr_ptr wr

lemma Resolve.null_inv {H : Heap Srt} {m} :
    H ⊢ m ▷ .null -> WR H -> Contra H ∧ m = .null := by
  generalize e: Tm.null = t
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' lk rsm ih =>
    subst_vars; cases rsm
    case ptr => exfalso; apply lk.not_wr_ptr wr
    case null => exfalso; apply lk.not_wr_null wr

theorem Resolved.resolution {H : Heap Srt} {x y z A s i} :
    [] ;; [] ;; H ⊢ x ▷ y ◁ z : A ->
    [] ⊢ A : .srt s i -> Value y -> (s ∈ ord.contra_set -> Contra H) := by
  intro ⟨er, rs, wr⟩; revert er
  generalize e1: [] = Γ
  generalize e2: [] = Δ
  intro er ty vl; induction er generalizing H z s i
  all_goals subst_vars; try (solve | cases vl)
  case lam_im =>
    have ⟨_, _, _, _, rd⟩ := ty.pi_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    apply rs.lam_inv wr
  case lam_ex =>
    have ⟨_, _, _, _, rd⟩ := ty.pi_inv
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    apply rs.lam_inv wr
  case tup_im tyn erm ihm =>
    intro h
    have ⟨_, _, _, _, _, le, _, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp_all; cases rs
    case tup mrg rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg.split_wr wr
      have ct1 := ihm rsm wr1 tyA (ord.contra_set.lower le h)
      have ⟨ct2, _⟩ := rsn.null_inv wr2; subst_vars
      apply mrg.contra_image ct1 ct2
    case ptr H l m lk rs =>
      have ⟨s, lk0, ifq⟩ := lk.lookup
      cases rs
      case tup mrg rsm rsn =>
        have wr0 := lk.wr_image wr
        have ⟨wr1, wr2⟩ := mrg.split_wr wr0
        have wr' := wr l; rw[lk0] at wr'
        split at wr' <;> try (solve|aesop)
        case h_3 heq =>
          cases heq; subst_vars
          have ct1 := ihm rsm wr1 tyA (ord.contra_set.lower le h)
          have ⟨ct2, _⟩ := rsn.null_inv wr2
          intro x
          cases x.decEq l with
          | isTrue => subst_vars; simp[lk0]; assumption
          | isFalse ne =>
            simp[h] at ifq; subst_vars
            apply mrg.contra_image ct1 ct2
        case h_4 heq =>
          cases heq; subst_vars
          have ⟨_, _⟩ := rsn.null_inv wr2
          contradiction
      case ptr => exfalso; apply lk.not_wr_ptr wr
  case tup_ex erm ern ihm ihn mrg =>
    intro h; cases mrg
    have ⟨_, _, _, _, _, le1, le2, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp_all; cases rs
    case tup mrg rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg.split_wr wr
      have ct1 := ihm rsm wr1 tyA (ord.contra_set.lower le1 h)
      have ct2 := ihn rsn wr2 (tyB.subst erm.toStatic) (ord.contra_set.lower le2 h)
      apply mrg.contra_image ct1 ct2
    case ptr l m lk rs =>
      have ⟨s, lk0, ifq⟩ := lk.lookup
      cases rs
      case tup mrg rsm rsn =>
        have wr0 := lk.wr_image wr
        have ⟨wr1, wr2⟩ := mrg.split_wr wr0
        have wr' := wr l; rw[lk0] at wr'
        split at wr' <;> try (solve|aesop)
        case h_4 heq =>
          cases heq; subst_vars
          have ct1 := ihm rsm wr1 tyA (ord.contra_set.lower le1 h)
          have ct2 := ihn rsn wr2 (tyB.subst erm.toStatic) (ord.contra_set.lower le2 h)
          intro x
          cases x.decEq l with
          | isTrue => subst_vars; simp[lk0]; assumption
          | isFalse ne =>
            simp[h] at ifq; subst_vars
            apply mrg.contra_image ct1 ct2
        case h_3 heq =>
          cases heq; subst_vars
          cases rsn; exfalso; apply ern.null_preimage
      case ptr => exfalso; apply lk.not_wr_ptr wr
  case tt => have ct := rs.tt_inv wr; aesop
  case ff => have ct := rs.ff_inv wr; aesop
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

lemma Resolve.value_image {H : Heap Srt} {m m'} :
    H ⊢ m ▷ m' -> WR H -> Value m -> Value m' := by
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
    H ⊢ .ptr l ▷ n -> WR H -> Value n := by
  intro rs wr; cases rs
  case ptr lk rs =>
    apply rs.value_image (lk.wr_image wr)
    apply lk.wr_value wr
