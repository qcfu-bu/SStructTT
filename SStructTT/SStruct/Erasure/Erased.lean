import SStructTT.SStruct.Dynamic.Renaming
import SStructTT.SStruct.Erasure.Syntax

namespace SStruct.Erasure
open Dynamic
variable {Srt : Type} [ord : SrtOrder Srt]

inductive Erased :
  Static.Ctx Srt -> Dynamic.Ctx Srt ->
  SStruct.Tm Srt -> Erasure.Tm Srt ->
  SStruct.Tm Srt ->
  Prop
where
  | var {Γ Δ x s A} :
    Wf Γ Δ ->
    Has Δ x s A ->
    Erased Γ Δ (.var x) (.var x) A

  | lam_im {Γ Δ A B m m' s sA iA} :
    Lower Δ s ->
    Γ ⊢ A : .srt sA iA ->
    Erased (A :: Γ) (A :⟨.im, sA⟩ Δ) m m' B ->
    Erased Γ Δ (.lam A m .im s) (.lam m' s) (.pi A B .im s)

  | lam_ex {Γ Δ A B m m' s sA iA} :
    Lower Δ s ->
    Γ ⊢ A : .srt sA iA ->
    Erased (A :: Γ) (A :⟨.ex, sA⟩ Δ) m m' B ->
    Erased Γ Δ (.lam A m .ex s) (.lam m' s) (.pi A B .ex s)

  | app_im {Γ Δ A B m m' n s} :
    Erased Γ Δ m m' (.pi A B .im s) ->
    Γ ⊢ n : A ->
    Erased Γ Δ (.app m n .im) (.app m' .null) B.[n/]

  | app_ex {Γ Δ1 Δ2 Δ A B m m' n n' s} :
    Merge Δ1 Δ2 Δ ->
    Erased Γ Δ1 m m' (.pi A B .ex s) ->
    Erased Γ Δ2 n n' A ->
    Erased Γ Δ (.app m n .ex) (.app m' n') B.[n/]

  | tup_im {Γ Δ A B m m' n s i} :
    Γ ⊢ .sig A B .im s : .srt s i ->
    Erased Γ Δ m m' A ->
    Γ ⊢ n : B.[m/] ->
    Erased Γ Δ (.tup m n .im s) (.tup m' .null s) (.sig A B .im s)

  | tup_ex {Γ Δ1 Δ2 Δ A B m m' n n' s i} :
    Merge Δ1 Δ2 Δ ->
    Γ ⊢ .sig A B .ex s : .srt s i ->
    Erased Γ Δ1 m m' A ->
    Erased Γ Δ2 n n' B.[m/] ->
    Erased Γ Δ (.tup m n .ex s) (.tup m' n' s) (.sig A B .ex s)

  | prj_im {Γ Δ1 Δ2 Δ A B C m m' n n' s sA sB sC iC} :
    Merge Δ1 Δ2 Δ ->
    .sig A B .im s :: Γ ⊢ C : .srt sC iC ->
    Erased Γ Δ1 m m' (.sig A B .im s) ->
    Erased (B :: A :: Γ) (B :⟨.im, sB⟩ A :⟨.ex, sA⟩ Δ2) n n' C.[.tup (.var 1) (.var 0) .im s .: shift 2] ->
    Erased Γ Δ (.prj C m n .im) (.prj m' n') C.[m/]

  | prj_ex {Γ Δ1 Δ2 Δ A B C m m' n n' s sA sB sC iC} :
    Merge Δ1 Δ2 Δ ->
    .sig A B .ex s :: Γ ⊢ C : .srt sC iC ->
    Erased Γ Δ1 m m' (.sig A B .ex s) ->
    Erased (B :: A :: Γ) (B :⟨.ex, sB⟩ A :⟨.ex, sA⟩ Δ2) n n' C.[.tup (.var 1) (.var 0) .ex s .: shift 2] ->
    Erased Γ Δ (.prj C m n .ex) (.prj m' n') C.[m/]

  | tt {Γ Δ} :
    Wf Γ Δ ->
    Implicit Δ ->
    Erased Γ Δ .tt .tt .bool

  | ff {Γ Δ} :
    Wf Γ Δ ->
    Implicit Δ ->
    Erased Γ Δ .ff .ff .bool

  | ite {Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s i} :
    Merge Δ1 Δ2 Δ ->
    .bool :: Γ ⊢ A : .srt s i ->
    Erased Γ Δ1 m m' .bool ->
    Erased Γ Δ2 n1 n1' A.[.tt/] ->
    Erased Γ Δ2 n2 n2' A.[.ff/] ->
    Erased Γ Δ (.ite A m n1 n2) (.ite m' n1' n2') A.[m/]

  | rw {Γ Δ A B m m' n a b s i} :
    .idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Γ ⊢ A : .srt s i ->
    Erased Γ Δ m m' A.[.rfl a,a/] ->
    Γ ⊢ n : .idn B a b ->
    Erased Γ Δ (.rw A m n) m' A.[n,b/]

  | drop {Γ Δ1 Δ2 Δ3 m m' n n' A B s} :
    Merge Δ1 Δ2 Δ3 ->
    Lower Δ1 s -> s ∈ ord.weaken_set ->
    Erased Γ Δ1 m m' A ->
    Erased Γ Δ2 n n' B ->
    Erased Γ Δ3 n (.drop m' n') B

  | conv {Γ Δ A B m m' s i} :
    A === B ->
    Erased Γ Δ m m' A ->
    Γ ⊢ B : .srt s i ->
    Erased Γ Δ m m' B

notation:50 Γ:50 " ;; " Δ:51 " ⊢ " m:51 " ▷ " m':51 " : " A:51 =>
  Erased Γ Δ m m' A

lemma Erased.toDynamic {Γ} {Δ : Ctx Srt} {A m m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> Γ ;; Δ ⊢ m : A := by
  intro ty; induction ty
  all_goals try (constructor <;> assumption)
  apply Typed.conv <;> assumption


lemma Erased.toStatic {Γ} {Δ : Ctx Srt} {A m m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> Γ ⊢ m : A := by
  intro ty; apply ty.toDynamic.toStatic

lemma Erased.toWf {Γ} {Δ : Ctx Srt} {A m m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> Γ ;; Δ ⊢ := by
  intro ty; apply ty.toDynamic.toWf

lemma Erased.ctx_inv {Γ} {Δ : Ctx Srt} {A B m m' r s} :
    A :: Γ ;; A :⟨r, s⟩ Δ ⊢ m ▷ m' : B -> ∃ i, Γ ;; Δ ⊢ ∧ Γ ⊢ A : .srt s i := by
  intro ty; apply ty.toDynamic.ctx_inv

lemma Erased.drop_spine {Γ} {Δ1 Δ3 : Ctx Srt} {A m m'} :
    Spine Δ1 Δ3 ->
    Γ ;; Δ1 ⊢ m ▷ m' : A ->
    ∃ m', Γ ;; Δ3 ⊢ m ▷ m' : A := by
  intro sp erm; induction sp
  case refl => aesop
  case cons Δ1 Δ2 Δ3 x s A mrg h hs sp ih =>
    replace ⟨m', ih⟩ := ih
    have ⟨wf1, wf2⟩ := ih.toWf.merge mrg
    have ⟨i, tyA⟩ := wf1.has_typed hs
    have ern : Γ ;; Δ2 ⊢ .var x ▷ .var x : A := by
      constructor <;> assumption
    existsi .drop (.var x) m'
    apply Erased.drop mrg.sym
    . apply hs.lower
    . apply h
    . assumption
    . assumption

lemma Erased.drop_merge {Γ} {Δ1 Δ2 Δ3 : Ctx Srt} {A m m' s} :
    Merge Δ1 Δ2 Δ3 -> Lower Δ2 s -> s ∈ ord.weaken_set ->
    Γ ;; Δ1 ⊢ m ▷ m' : A ->
    ∃ m', Γ ;; Δ3 ⊢ m ▷ m' : A := by
  intro mrg lw h tym
  have sp := mrg.toSpine lw h
  apply tym.drop_spine sp

lemma Erased.closed {Γ Δ} {m A : SStruct.Tm Srt} {m'} :
    Γ ;; Δ ⊢ m ▷ m' : A -> Closed Γ.length m' := by
  intro erm; induction erm
  all_goals try (solve | aesop)
  case var wf hs =>
    replace hs := wf.hasStatic hs
    apply hs.var_lt_length

lemma Erased.closed_stack {Γ Δ} {m A : SStruct.Tm Srt} {m' i} :
    Γ ;; Δ ⊢ m ▷ m' : A -> Closed i m' -> Stack Δ i := by
  intro erm cl; induction erm generalizing i
  case var hs =>
    simp at cl
    apply hs.stack cl
  case lam_im ihm =>
    simp at cl
    have st := ihm cl
    cases st
    case nil im =>
      simp at im
      constructor
      apply im
    case cons => assumption
  case lam_ex ihm =>
    simp at cl
    have st := ihm cl
    cases st
    case nil im => simp at im
    case cons => assumption
  case app_im ihm => simp at cl; aesop
  case app_ex mrg _ _ ihm ihn =>
    simp at cl
    have ⟨cl1, cl2⟩ := cl
    replace ihm := ihm cl1
    replace ihn := ihn cl2
    apply mrg.stack_image ihm ihn
  case tup_im ihm => simp at cl; aesop
  case tup_ex mrg _ _ _ ihm ihn =>
    simp at cl
    have ⟨cl1, cl2⟩ := cl
    replace ihm := ihm cl1
    replace ihn := ihn cl2
    apply mrg.stack_image ihm ihn
  case prj_im mrg _ _ _ ihm ihn =>
    simp at cl
    have ⟨cl1, cl2⟩ := cl
    replace ihm := ihm cl1
    replace ihn := ihn cl2
    cases ihn <;> try simp_all
    case cons ihn =>
      cases ihn <;> try simp_all
      apply mrg.stack_image <;> assumption
  case prj_ex mrg _ _ _ ihm ihn =>
    simp at cl
    have ⟨cl1, cl2⟩ := cl
    replace ihm := ihm cl1
    replace ihn := ihn cl2
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
    rcases cl with ⟨cl0, cl1, cl2⟩
    replace ihm := ihm cl0
    replace ihn1 := ihn1 cl1
    apply mrg.stack_image ihm ihn1
  case rw => aesop
  case drop mrg _ _ _ _ ihm ihn =>
    simp at cl
    have ⟨cl1, cl2⟩ := cl
    replace ihm := ihm cl1
    replace ihn := ihn cl2
    apply mrg.stack_image ihm ihn
  case conv => aesop

end SStruct.Erasure

namespace SStruct.Dynamic
open SStruct.Erasure
variable {Srt : Type} [ord : SrtOrder Srt]

lemma Typed.toErased {Γ} {Δ : Ctx Srt} {A m} :
    Γ ;; Δ ⊢ m : A -> ∃ m', Γ ;; Δ ⊢ m ▷ m' : A := by
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
  case tup_im s _ _  _ _ ihm =>
    have ⟨m', erm⟩ := ihm
    existsi .tup m' .null s
    constructor <;> aesop
  case tup_ex s _ _ _ _ _ ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi (.tup m' n' s)
    constructor <;> aesop
  case prj_im sA SB _ _ rs _ _ _ _ ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi .prj m' n'; constructor
    all_goals aesop
  case prj_ex sA sB _ _ rsA rsB _ _ _ _ ihm ihn =>
    have ⟨m', erm⟩ := ihm
    have ⟨n', ern⟩ := ihn
    existsi .prj m' n'; constructor
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
  case drop mrg lw h tyn ihn =>
    have ⟨n', ern⟩ := ihn
    apply ern.drop_merge mrg.sym lw h
  case conv ihm =>
    have ⟨m', erm⟩ := ihm
    existsi m'; constructor <;> assumption
  all_goals trivial

end SStruct.Dynamic
