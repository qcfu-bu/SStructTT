import SStructTT.SStruct.Program.Renaming
import SStructTT.SStruct.Extraction.Syntax

namespace SStruct.Extraction
open Program
variable {Srt : Type} [ord : SrtOrder Srt]

inductive Extract :
  Ctx Srt -> SStruct.Tm Srt -> Extraction.Tm Srt -> SStruct.Tm Srt ->
  Prop
where
  | var {Δ x s A} :
    Wf Δ ->
    Has Δ x s A ->
    Extract Δ (.var x) (.var x) A

  | lam_im {Δ A B m m' s sA iA} :
    Lower Δ s ->
    Δ.logical ⊢ A : .srt sA iA ->
    Extract (A :⟨.im, sA⟩ Δ) m m' B ->
    Extract Δ (.lam A m .im s) (.lam m' s) (.pi A B .im s)

  | lam_ex {Δ A B m m' s sA iA} :
    Lower Δ s ->
    Δ.logical ⊢ A : .srt sA iA ->
    Extract (A :⟨.ex, sA⟩ Δ) m m' B ->
    Extract Δ (.lam A m .ex s) (.lam m' s) (.pi A B .ex s)

  | app_im {Δ A B m m' n s} :
    Extract Δ m m' (.pi A B .im s) ->
    Δ.logical ⊢ n : A ->
    Extract Δ (.app m n) (.app m' .null) B.[n/]

  | app_ex {Δ1 Δ2 Δ3 A B m m' n n' s} :
    Merge Δ1 Δ2 Δ3 ->
    Extract Δ1 m m' (.pi A B .ex s) ->
    Extract Δ2 n n' A ->
    Extract Δ3 (.app m n) (.app m' n') B.[n/]

  | tup_im {Δ : Ctx Srt} {A B m n n' s i} :
    Δ.logical ⊢ .sig A B .im s : .srt s i ->
    Δ.logical ⊢ m : A ->
    Extract Δ n n' B.[m/] ->
    Extract Δ (.tup m n .im s) (.tup .null n' s) (.sig A B .im s)

  | tup_ex {Δ1 Δ2 Δ3 A B m m' n n' s i} :
    Merge Δ1 Δ2 Δ3 ->
    Δ3.logical ⊢ .sig A B .ex s : .srt s i ->
    Extract Δ1 m m' A ->
    Extract Δ2 n n' B.[m/] ->
    Extract Δ3 (.tup m n .ex s) (.tup m' n' s) (.sig A B .ex s)

  | prj_im {Δ1 Δ2 Δ3 A B C m m' n n' s sA sB sC iC} :
    Merge Δ1 Δ2 Δ3 ->
    .sig A B .im s :: Δ3.logical ⊢ C : .srt sC iC ->
    Extract Δ1 m m' (.sig A B .im s) ->
    Extract (B :⟨.ex, sB⟩ A :⟨.im, sA⟩ Δ2) n n' C.[.tup (.var 1) (.var 0) .im s .: shift 2] ->
    Extract Δ3 (.prj C m n) (.prj m' n') C.[m/]

  | prj_ex {Δ1 Δ2 Δ3 A B C m m' n n' s sA sB sC iC} :
    Merge Δ1 Δ2 Δ3 ->
    .sig A B .ex s :: Δ3.logical ⊢ C : .srt sC iC ->
    Extract Δ1 m m' (.sig A B .ex s) ->
    Extract (B :⟨.ex, sB⟩ A :⟨.ex, sA⟩ Δ2) n n' C.[.tup (.var 1) (.var 0) .ex s .: shift 2] ->
    Extract Δ3 (.prj C m n) (.prj m' n') C.[m/]

  | tt {Δ} :
    Wf Δ ->
    Implicit Δ ->
    Extract Δ .tt .tt .bool

  | ff {Δ} :
    Wf Δ ->
    Implicit Δ ->
    Extract Δ .ff .ff .bool

  | ite {Δ1 Δ2 Δ3 A m m' n1 n1' n2 n2' s i} :
    Merge Δ1 Δ2 Δ3 ->
    .bool :: Δ3.logical ⊢ A : .srt s i ->
    Extract Δ1 m m' .bool ->
    Extract Δ2 n1 n1' A.[.tt/] ->
    Extract Δ2 n2 n2' A.[.ff/] ->
    Extract Δ3 (.ite A m n1 n2) (.ite m' n1' n2') A.[m/]

  | rw {Δ A B m m' n a b s i} :
    .idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Δ.logical ⊢ A : .srt s i ->
    Extract Δ m m' A.[.rfl a,a/] ->
    Δ.logical ⊢ n : .idn B a b ->
    Extract Δ (.rw A m n) m' A.[n,b/]

  | exf {Δ A m s i} :
    Wf Δ ->
    Implicit Δ ->
    .bot :: Δ.logical ⊢ A : .srt s i ->
    Δ.logical ⊢ m : .bot ->
    Extract Δ (.exf A m) .dead A.[m/]

  | exf_drop {Δ1 Δ2 Δ3 A m n B s i} {n' b' : Extraction.Tm Srt} :
    Merge Δ1 Δ2 Δ3 ->
    .bot :: Δ3.logical ⊢ A : .srt s i ->
    Δ3.logical ⊢ m : .bot ->
    Extract Δ1 n n' B ->
    Extract Δ2 (.exf A m) b' A.[m/] ->
    Extract Δ3 (.exf A m) (.drop n' b') A.[m/]

  | drop {Δ1 Δ2 Δ3 m m' n n' A B s} :
    Merge Δ1 Δ2 Δ3 ->
    Lower Δ1 s -> s ∈ ord.weaken_set ->
    Extract Δ1 m m' A ->
    Extract Δ2 n n' B ->
    Extract Δ3 n (.drop m' n') B

  | conv {Δ A B m m' s i} :
    A === B ->
    Extract Δ m m' A ->
    Δ.logical ⊢ B : .srt s i ->
    Extract Δ m m' B

notation:50 Δ:50 " ⊢ " m:51 " ▷ " m':81 " :: " A:51 =>
  Extract Δ m m' A

lemma Extract.toProgram {Δ : Ctx Srt} {A m m'} :
    Δ ⊢ m ▷ m' :: A -> Δ ⊢ m :: A := by
  intro ty; induction ty
  all_goals try (solve | constructor <;> assumption)
  case app_ex =>
    apply Typed.app_ex <;> assumption
  case prj_ex =>
    apply Typed.prj_ex <;> assumption
  case exf_drop mrg tyA tym ern _ ihn _ =>
    apply Typed.exf
    . exact (Wf.merge mrg ihn.toWf).right
    . assumption
    . assumption
  case conv =>
    apply Typed.conv <;> assumption

lemma Extract.toLogical {Δ : Ctx Srt} {A m m'} :
    Δ ⊢ m ▷ m' :: A -> Δ.logical ⊢ m : A := by
  intro ty; apply ty.toProgram.toLogical

lemma Extract.toWf {Δ : Ctx Srt} {A m m'} :
    Δ ⊢ m ▷ m' :: A -> Δ ⊢ := by
  intro ty; apply ty.toProgram.toWf

lemma Extract.ctx_inv {Δ : Ctx Srt} {A B m m' r s} :
    A :⟨r, s⟩ Δ ⊢ m ▷ m' :: B -> ∃ i, Δ ⊢ ∧ Δ.logical ⊢ A : .srt s i := by
  intro ty; apply ty.toProgram.ctx_inv

lemma Extract.drop_spine {Δ1 Δ3 : Ctx Srt} {A m m'} :
    Spine Δ1 Δ3 ->
    Δ1 ⊢ m ▷ m' :: A ->
    ∃ m', Δ3 ⊢ m ▷ m' :: A := by
  intro sp erm; induction sp
  case refl => aesop
  case cons Δ1 Δ2 Δ3 x s A mrg h hs sp ih =>
    replace ⟨m', ih⟩ := ih
    have ⟨wf1, wf2⟩ := ih.toWf.merge mrg
    have ⟨i, tyA⟩ := wf1.has_typed hs
    have ern : Δ2 ⊢ .var x ▷ .var x :: A := by
      constructor <;> assumption
    existsi .drop (.var x) m'
    apply Extract.drop mrg.sym
    . apply hs.lower
    . apply h
    . assumption
    . assumption

lemma Extract.drop_merge {Δ1 Δ2 Δ3 : Ctx Srt} {A m m' s} :
    Merge Δ1 Δ2 Δ3 -> Lower Δ2 s -> s ∈ ord.weaken_set ->
    Δ1 ⊢ m ▷ m' :: A ->
    ∃ m', Δ3 ⊢ m ▷ m' :: A := by
  intro mrg lw h tym
  have sp := mrg.toSpine lw h
  apply tym.drop_spine sp

lemma Extract.closed {Δ} {m A : SStruct.Tm Srt} {m'} :
    Δ ⊢ m ▷ m' :: A -> Closed Δ.length m' := by
  intro erm; induction erm
  all_goals try (solve | aesop)
  case var Δ _ _ _ wf hs =>
    replace hs := wf.hasLogical hs
    rw[<-Δ.logical_length]
    apply hs.var_lt_length
  case app_ex mrg _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption
  case tup_ex mrg _ _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption
  case prj_im mrg _ _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption
  case prj_ex mrg _ _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption
  case ite mrg _ _ _ _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption
    . rw[mrg.sym.length]; assumption
  case exf_drop mrg _ _ _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption
  case drop mrg _ _ _ _ _ _ =>
    and_intros
    . rw[mrg.length]; assumption
    . rw[mrg.sym.length]; assumption

@[simp]def NoNull : Tm Srt -> Prop
  | .var _ => True
  | .lam m _ => NoNull m
  | .app m n => NoNull m ∧ NoNull n
  | .tup m n _ => NoNull m ∧ NoNull n
  | .prj m n => NoNull m ∧ NoNull n
  | .tt => True
  | .ff => True
  | .ite m n1 n2 => NoNull m ∧ NoNull n1 ∧ NoNull n2
  | .drop m n => NoNull m ∧ NoNull n
  | .ptr _ => True
  | .null => False
  | .dead => False

lemma Extract.closed_stack {Δ} {m A : SStruct.Tm Srt} {m' i} :
    Δ ⊢ m ▷ m' :: A -> Closed i m' -> NoNull m' -> Stack Δ i := by
  intro erm cl nn; induction erm generalizing i
  case var hs =>
    simp at cl
    apply hs.stack cl
  case lam_im ihm =>
    simp at cl
    simp at nn
    have st := ihm cl nn
    cases st
    case nil im =>
      simp at im
      constructor
      apply im
    case cons => assumption
  case lam_ex ihm =>
    simp at cl
    simp at nn
    have st := ihm cl nn
    cases st
    case nil im => simp at im
    case cons => assumption
  case app_im => simp at nn
  case app_ex mrg _ _ ihm ihn =>
    simp at cl
    simp at nn
    have ⟨cl1, cl2⟩ := cl
    have ⟨nn1, nn2⟩ := nn
    replace ihm := ihm cl1 nn1
    replace ihn := ihn cl2 nn2
    apply mrg.stack_image ihm ihn
  case tup_im => simp at nn
  case tup_ex mrg _ _ _ ihm ihn =>
    simp at cl
    simp at nn
    have ⟨cl1, cl2⟩ := cl
    have ⟨nn1, nn2⟩ := nn
    replace ihm := ihm cl1 nn1
    replace ihn := ihn cl2 nn2
    apply mrg.stack_image ihm ihn
  case prj_im mrg _ _ _ ihm ihn =>
    simp at cl
    simp at nn
    have ⟨cl1, cl2⟩ := cl
    have ⟨nn1, nn2⟩ := nn
    replace ihm := ihm cl1 nn1
    replace ihn := ihn cl2 nn2
    cases ihn <;> try simp_all
    case cons ihn =>
      apply mrg.stack_image; assumption
      cases ihn <;> simp_all
      apply Stack.nil; assumption
  case prj_ex mrg _ _ _ ihm ihn =>
    simp at cl
    simp at nn
    have ⟨cl1, cl2⟩ := cl
    have ⟨nn1, nn2⟩ := nn
    replace ihm := ihm cl1 nn1
    replace ihn := ihn cl2 nn2
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
    simp at cl
    simp at nn
    rcases cl with ⟨cl0, cl1, cl2⟩
    rcases nn with ⟨nn0, nn1, nn2⟩
    replace ihm := ihm cl0 nn0
    replace ihn1 := ihn1 cl1 nn1
    apply mrg.stack_image ihm ihn1
  case rw => aesop
  case exf => simp at nn
  case exf_drop mrg _ _ _ _ ihm ihb =>
    simp at cl
    simp at nn
    have ⟨cl1, cl2⟩ := cl
    have ⟨nn1, nn2⟩ := nn
    replace ihm := ihm cl1 nn1
    replace ihb := ihb cl2 nn2
    apply mrg.stack_image ihm ihb
  case drop mrg _ _ _ _ ihm ihn =>
    simp at cl
    simp at nn
    have ⟨cl1, cl2⟩ := cl
    have ⟨nn1, nn2⟩ := nn
    replace ihm := ihm cl1 nn1
    replace ihn := ihn cl2 nn2
    apply mrg.stack_image ihm ihn
  case conv => aesop

inductive ExfSpine (Δ0 : Ctx Srt) : Ctx Srt -> Prop where
  | refl : ExfSpine Δ0 Δ0
  | cons {Δ1 Δ2 Δ3 x s A} :
    Merge Δ1 Δ2 Δ3 ->
    Has Δ2 x s A ->
    ExfSpine Δ0 Δ1 ->
    ExfSpine Δ0 Δ3

lemma ExfSpine.extend {Δ1 Δ2 : Ctx Srt} {A r s} :
    ExfSpine Δ1 Δ2 -> ExfSpine (A :⟨r, s⟩ Δ1) (A :⟨r, s⟩ Δ2) := by
  intro sp; induction sp
  case refl => constructor
  case cons Δ1 Δ2 Δ3 x _ _ mrg hs sp ih =>
    replace mrg : Merge (A :⟨r, s⟩ Δ1) (A :⟨.im, s⟩ Δ2) (A :⟨r, s⟩ Δ3) := by
      cases r
      . constructor; assumption
      . constructor; assumption
    constructor
    . apply mrg
    . constructor
      assumption
    . assumption

lemma ExfSpine.toImplicit {Δ : Ctx Srt} :
    ExfSpine Δ.toImplicit Δ := by
  induction Δ
  case nil =>
    simp; constructor
  case cons hd tl ih =>
    rcases hd with ⟨A, r, s⟩
    cases r
    · simp
      apply ih.extend
    · simp
      have sp := @ExfSpine.extend Srt ord (Ctx.toImplicit tl) tl A .im s ih
      have mrg : Merge (A :⟨.im, s⟩ tl) (A :⟨.ex, s⟩ Ctx.toImplicit tl) (A :⟨.ex, s⟩ tl) := by
        constructor
        apply Merge.self
      have hs : Has (A :⟨.ex, s⟩ Ctx.toImplicit tl) 0 s A.[shift 1] := by
        constructor
        apply Implicit.toImplicit
      exact ExfSpine.cons mrg hs sp

lemma Extract.exf_drop_spine {Δ1 Δ3 : Ctx Srt} {A m m' s i} :
    ExfSpine Δ1 Δ3 ->
    Δ1 ⊢ .exf A m ▷ m' :: A.[m/] ->
    .bot :: Δ3.logical ⊢ A : .srt s i ->
    Δ3.logical ⊢ m : .bot ->
    ∃ m', Δ3 ⊢ .exf A m ▷ m' :: A.[m/] := by
  intro sp er tyA tym
  induction sp
  case refl =>
    existsi m'; assumption
  case cons Δ1 Δ2 Δ3 x t B mrg hs sp ih =>
    have tyA1 : .bot :: Δ1.logical ⊢ A : .srt s i := by
      rw[<-mrg.logical]; assumption
    have tym1 : Δ1.logical ⊢ m : .bot := by
      rw[<-mrg.logical]; assumption
    have ⟨b', erb⟩ := ih tyA1 tym1
    have ⟨wf1, wf2⟩ := erb.toWf.merge mrg
    have ern : Δ2 ⊢ .var x ▷ .var x :: B := by
      constructor <;> assumption
    existsi .drop (.var x) b'
    apply Extract.exf_drop mrg.sym tyA tym ern erb

end SStruct.Extraction

namespace SStruct.Program
open SStruct.Extraction
variable {Srt : Type} [ord : SrtOrder Srt]

theorem Typed.toExtract {Δ : Ctx Srt} {A m} :
    Δ ⊢ m :: A -> ∃ m', Δ ⊢ m ▷ m' :: A := by
  intro ty; induction ty
  case var x _ _ _ _ _ =>
    existsi (.var x); constructor <;> aesop
  case lam_im s _ _ _ _ _ ihm =>
    have ⟨m', erm⟩ := ihm
    existsi .lam m' s
    constructor <;> aesop
  case lam_ex s sA _ _ _ _ ihm =>
    have ⟨m', erm⟩ := ihm
    existsi .lam m' s; constructor
    all_goals aesop
  case app_im ihm =>
    have ⟨m', erm⟩ := ihm
    existsi .app m' .null
    constructor <;> aesop
  case app_ex ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi .app m' n'
    constructor <;> aesop
  case tup_im s _ _  _ _ ihn =>
    have ⟨n', ern⟩ := ihn
    existsi .tup .null n' s
    constructor <;> aesop
  case tup_ex s _ _ _ _ _ ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi (.tup m' n' s)
    constructor <;> aesop
  case prj_im sA SB _ _ rs _ _ _ _ ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi .prj m' n'; apply Extract.prj_im
    all_goals aesop
  case prj_ex sA sB _ _ rsA rsB _ _ _ _ ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi .prj m' n'; apply Extract.prj_ex
    all_goals aesop
  case tt => existsi .tt; constructor <;> aesop
  case ff => existsi .ff; constructor <;> aesop
  case ite ihm ihn1 ihn2 =>
    have ⟨m', erm⟩ := ihm
    have ⟨n1', ern1⟩ := ihn1
    have ⟨n2', ern2⟩ := ihn2
    existsi (.ite m' n1' n2')
    constructor <;> aesop
  case rw ihm =>
    have ⟨m', erm⟩ := ihm
    existsi m'; constructor <;> aesop
  case exf Δ A m s i wf tyA tym _ =>
    have er : Δ.toImplicit ⊢ .exf A m ▷ .dead :: A.[m/] := by
      apply Extract.exf
      . apply wf.implicit
      . apply Implicit.toImplicit
      . rw[Implicit.logical]; assumption
      . rw[Implicit.logical]; assumption
    apply er.exf_drop_spine ExfSpine.toImplicit tyA tym
  case drop mrg lw h tyn ihn =>
    have ⟨n', ern⟩ := ihn
    apply ern.drop_merge mrg.sym lw h
  case conv ihm =>
    have ⟨m', erm⟩ := ihm
    existsi m'; constructor <;> assumption
  all_goals trivial

end SStruct.Program
