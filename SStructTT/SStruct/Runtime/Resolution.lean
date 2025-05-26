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

  | drop {H1 H2 H3 m m' n n' s} :
    HMerge H1 H2 H3 ->
    HLower H1 s -> s ∈ ord.weaken_set ->
    Resolve H1 m m' ->
    Resolve H2 n n' ->
    Resolve H3 (.drop m n) (.drop m' n')

  | ptr {H l m m' s} :
    l ∉ H.keys ->
    Resolve H m m' ->
    Resolve (H.insert l (m, s)) (.ptr l) m'

  | null {H} :
    HLower H ord.e ->
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
    WR H -> WR (H.insert l (.tt, ord.e)) := by
  intro wr x
  cases x.decEq l with
  | isTrue => subst_vars; simp
  | isFalse ne => simp[ne]; apply wr

lemma Erased.resolve_refl {H : Heap Srt} {Γ Δ m n A} :
    Γ ;; Δ ⊢ m ▷ n : A -> HLower H ord.e -> H ⊢ n ▷ n := by
  intro er lw
  induction er
  case var => constructor; assumption
  case lam_im ih =>
    constructor
    apply HLower.weaken lw (ord.e_min _)
    apply ih
  case lam_ex ih =>
    constructor
    apply HLower.weaken lw (ord.e_min _)
    apply ih
  case app_im ih =>
    constructor
    . apply HMerge.empty
    . apply ih
    . constructor
      apply HLower.empty
  case app_ex =>
    constructor
    . apply lw.merge_refl
      apply ord.e_contra
    . assumption
    . assumption
  case tup_im ih =>
    have mrg := HMerge.empty (H := (∅ : Heap Srt))
    constructor
    . apply HMerge.empty
    . apply ih
    . constructor
      assumption
  case tup_ex =>
    constructor
    . apply lw.merge_refl
      apply ord.e_contra
    . assumption
    . assumption
  case prj_im =>
    constructor
    . apply lw.merge_refl
      apply ord.e_contra
    . assumption
    . assumption
  case prj_ex =>
    constructor
    . apply lw.merge_refl
      apply ord.e_contra
    . assumption
    . assumption
  case tt => constructor; assumption
  case ff => constructor; assumption
  case ite =>
    constructor
    . apply lw.merge_refl
      apply ord.e_contra
    . assumption
    . assumption
    . assumption
  case rw => aesop
  case drop ih =>
    constructor
    . apply lw.merge_refl
      apply ord.e_contra
    . assumption
    . apply ord.e_weaken
    . aesop
    . aesop
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
  case drop mrg lw h erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop
  case ptr H l m n s h erm ihm =>
    have nf := wr.nf l m s
    simp at nf
    replace wr := wr.erase l
    simp[Heap.erase_insert h] at wr
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
  case drop mrg lw h erm ern ihm ihn =>
    have ⟨nfm, nfn⟩ := nf
    have ⟨wr1, wr2⟩ := mrg.split_wr wr
    aesop

lemma Resolve.weaken_merge {H1 H2 H3 : Heap Srt} {m m'} :
    HMerge H1 H2 H3 -> HLower H2 ord.e -> H1 ⊢ m ▷ m' -> H3 ⊢ m ▷ m' := by
  intro mrg lw2 rsm; induction rsm generalizing H2 H3
  case var H1 x lw1 =>
    have lw := mrg.lower_image lw1 lw2
    constructor; assumption
  case lam lw1 rsm ihm =>
    have lw := mrg.lower_image lw1 (lw2.weaken (ord.e_min _))
    replace ihm := ihm mrg lw2
    constructor <;> assumption
  case app Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have ⟨H2a, H2b, lwa, lwb, mrg2⟩ := lw2.split_lower ord.e_contra
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga lwa
    replace ihn := ihn mrgb lwb
    constructor <;> assumption
  case tup Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have ⟨H2a, H2b, lwa, lwb, mrg2⟩ := lw2.split_lower ord.e_contra
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga lwa
    replace ihn := ihn mrgb lwb
    constructor <;> assumption
  case prj Ha Hb H1 _ _ _ _ mrg1 rsm rsn ihm ihn =>
    have ⟨H2a, H2b, lwa, lwb, mrg2⟩ := lw2.split_lower ord.e_contra
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga lwa
    replace ihn := ihn mrgb lwb
    constructor <;> assumption
  case tt lw1 =>
    have lw := mrg.lower_image lw1 lw2
    constructor; assumption
  case ff lw1 =>
    have lw := mrg.lower_image lw1 lw2
    constructor; assumption
  case ite Ha Hb H1 _ _ _ _ _ _ mrg1 rsm rsn1 rsn2 ihm ihn1 ihn2 =>
    have ⟨H2a, H2b, lwa, lwb, mrg2⟩ := lw2.split_lower ord.e_contra
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga lwa
    replace ihn1 := ihn1 mrgb lwb
    replace ihn2 := ihn2 mrgb lwb
    constructor <;> assumption
  case drop Ha Hb H1 _ _ _ _ mrg1 lw mem rsm rsn ihm ihn =>
    have ⟨H2a, H2b, lwa, lwb, mrg2⟩ := lw2.split_lower ord.e_contra
    have ⟨H1', H2', mrg', mrga, mrgb⟩ := mrg.distr mrg1 mrg2
    replace ihm := ihm mrga lwa
    replace ihn := ihn mrgb lwb
    have lw' := mrga.lower_image lw (lwa.weaken (ord.e_min _))
    constructor <;> assumption
  case ptr l m m' s h rsm ih =>
    have lk := mrg.insert_lookup
    have mrg1 := mrg.erase h
    have ih := ih mrg1 (lw2.erase_lower l)
    rw[<-H3.insert_erase lk]; constructor
    simp; assumption
  case null lw1 =>
    have lw := mrg.lower_image lw1 lw2
    constructor; assumption

lemma Resolve.var_inv {H : Heap Srt} {m x} :
    H ⊢ m ▷ .var x -> WR H -> HLower H ord.e := by
  generalize e: Tm.var x = m'
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' s h rsm ih =>
    subst_vars; cases rsm
    case var => replace wr := wr l; simp at wr
    case ptr => replace wr := wr l; simp at wr

lemma Resolve.lam_inv {H : Heap Srt} {m m' s} :
    H ⊢ m ▷ .lam m' s -> WR H -> HLower H s := by
  generalize e: Tm.lam m' s = t
  intro rs wr; induction rs <;> try trivial
  case lam => cases e; assumption
  case ptr l m m' s h rsm ih =>
    subst_vars; cases rsm
    case lam lw =>
      have wr := wr l; simp at wr
      rcases wr with ⟨nf, e⟩; subst e
      intro x
      cases x.decEq l with
      | isTrue =>
        subst_vars; simp
        apply InterSet.self_mem
      | isFalse ne =>
        simp[ne]; apply lw
    case ptr =>
      have wr := wr l; simp at wr

lemma Resolve.tt_inv {H : Heap Srt} {m} :
    H ⊢ m ▷ .tt -> WR H -> HLower H ord.e := by
  generalize e: Tm.tt = t
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' s h rsm ih =>
    subst_vars; cases rsm
    case tt lw =>
      have wr := wr l; simp at wr
      subst wr;
      intro x
      cases x.decEq l with
      | isTrue =>
        subst_vars; simp
        apply InterSet.self_mem
      | isFalse ne => simp[ne]; apply lw
    case ptr =>
      have wr := wr l; simp at wr

lemma Resolve.ff_inv {H : Heap Srt} {m} :
    H ⊢ m ▷ .ff -> WR H -> HLower H ord.e := by
  generalize e: Tm.ff = t
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' s h rsm ih =>
    subst_vars; cases rsm
    case ff lw =>
      have wr := wr l; simp at wr
      subst wr;
      intro x
      cases x.decEq l with
      | isTrue =>
        subst_vars; simp
        apply InterSet.self_mem
      | isFalse ne => simp[ne]; apply lw
    case ptr =>
      have wr := wr l; simp at wr

lemma Resolve.null_inv {H : Heap Srt} {m} :
    H ⊢ m ▷ .null -> WR H -> HLower H ord.e ∧ m = .null := by
  generalize e: Tm.null = t
  intro rs wr; induction rs <;> try trivial
  case ptr l m m' s h rsm ih =>
    subst_vars; cases rsm
    case null => have wr := wr l; simp at wr
    case ptr  => have wr := wr l; simp at wr

theorem Resolved.resolution {H : Heap Srt} {x y z A s i} :
    [] ;; [] ;; H ⊢ x ▷ y ◁ z : A ->
    [] ⊢ A : .srt s i -> Value y -> HLower H s := by
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
    have ⟨_, _, _, _, _, le, _, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp at ihm
    cases z <;> cases rs
    case tup mrg rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg.split_wr wr
      have lw1 := ihm rsm wr1 tyA vl1
      have ⟨lw2, _⟩ := rsn.null_inv wr2; subst_vars
      replace lw1 := lw1.weaken le
      replace lw2 := lw2.weaken (ord.e_min s)
      apply mrg.lower_image lw1 lw2
    case ptr l s H m h rs =>
      cases rs
      case tup mrg rsm rsn =>
        have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
        have ⟨wr1, wr2⟩ := mrg.split_wr wr0
        have wr := wr l; simp at wr; split at wr <;> try simp_all
        case h_3 heq =>
          rcases heq with ⟨⟨_, _, _⟩, _⟩; subst_vars
          have lw1 := ihm rsm wr1 tyA
          have ⟨lw2, _⟩ := rsn.null_inv wr2
          replace lw1 := lw1.weaken le
          intro x
          cases x.decEq l with
          | isTrue =>
            subst_vars
            simp
            apply InterSet.self_mem
          | isFalse ne =>
            simp[ne]
            apply mrg.lower_image lw1
            apply lw2.weaken (ord.e_min _)
        case h_4 heq =>
          have ⟨_, _⟩ := rsn.null_inv wr2
          contradiction
      case ptr => have wr := wr l; simp at wr
  case tup_ex erm ern ihm ihn mrg =>
    cases mrg
    have ⟨_, _, _, _, _, le1, le2, tyA, tyB, rd⟩ := ty.sig_inv'
    have ⟨_, _⟩ := Static.Conv.srt_inj rd; subst_vars
    cases vl; case tup vl1 vl2 =>
    simp_all; cases rs
    case tup mrg rsm rsn =>
      have ⟨wr1, wr2⟩ := mrg.split_wr wr
      have lw1 := ihm rsm wr1 tyA
      have lw2 := ihn rsn wr2 (tyB.subst erm.toStatic)
      replace lw1 := lw1.weaken le1
      replace lw2 := lw2.weaken le2
      apply mrg.lower_image lw1 lw2
    case ptr H l m s h rs =>
      cases rs
      case tup mrg rsm rsn =>
        have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
        have ⟨wr1, wr2⟩ := mrg.split_wr wr0
        have wr := wr l; simp at wr; split at wr <;> try simp_all
        case h_3 heq =>
          rcases heq with ⟨⟨_, _, _⟩, _⟩; subst_vars
          cases rsn; exfalso; apply ern.null_preimage
        case h_4 heq =>
          rcases heq with ⟨⟨_, _, _⟩, _⟩; subst_vars
          have lw1 := ihm rsm wr1 tyA
          have lw2 := ihn rsn wr2 (tyB.subst erm.toStatic)
          replace lw1 := lw1.weaken le1
          replace lw2 := lw2.weaken le2
          intro x
          cases x.decEq l with
          | isTrue =>
            subst_vars
            simp
            apply InterSet.self_mem
          | isFalse ne =>
            simp[ne]
            apply mrg.lower_image lw1 lw2
      case ptr => have wr := wr l; simp at wr
  case tt =>
    have lw := rs.tt_inv wr
    apply lw.weaken (ord.e_min s)
  case ff =>
    have lw := rs.ff_inv wr
    apply lw.weaken (ord.e_min s)
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
  case ptr l _ _ _ h _ _ =>
    have vl := wr.lookup l; simp at vl
    have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
    aesop

lemma Resolve.ptr_value {H : Heap Srt} {n l} :
    H ⊢ .ptr l ▷ n -> WR H -> Value n := by
  intro rs wr; cases rs
  case ptr _ _ _ h rsm =>
    have vl := wr.lookup l; simp at vl
    have wr0 := wr.erase l; simp[Heap.erase_insert,h] at wr0
    apply rsm.value_image wr0 vl
