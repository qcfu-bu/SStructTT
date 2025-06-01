import SStructTT.SStruct.Static.Renaming
import SStructTT.SStruct.Dynamic.Context

namespace SStruct.Dynamic
open Static
variable {Srt : Type} [ord : SrtOrder Srt]

mutual
inductive Typed : Ctx Srt -> Tm Srt -> Tm Srt -> Prop where
  | var {Δ x s A} :
    Wf Δ ->
    Has Δ x s A ->
    Typed Δ (.var x) A

  | lam_im {Δ A B m s sA iA} :
    Lower Δ s ->
    Δ.static ⊢ A : .srt sA iA ->
    Typed (A :⟨.im, sA⟩ Δ) m B ->
    Typed Δ (.lam A m .im s) (.pi A B .im s)

  | lam_ex {Δ A B m s sA iA} :
    Lower Δ s ->
    Δ.static ⊢ A : .srt sA iA ->
    Typed (A :⟨.ex, sA⟩ Δ) m B ->
    Typed Δ (.lam A m .ex s) (.pi A B .ex s)

  | app_im {Δ A B m n s} :
    Typed Δ m (.pi A B .im s) ->
    Δ.static ⊢ n : A ->
    Typed Δ (.app m n .im) B.[n/]

  | app_ex {Δ1 Δ2 Δ3 A B m n s} :
    Merge Δ1 Δ2 Δ3 ->
    Typed Δ1 m (.pi A B .ex s) ->
    Typed Δ2 n A ->
    Typed Δ3 (.app m n .ex) B.[n/]

  | tup_im {Δ A B m n s i} :
    Δ.static ⊢ .sig A B .im s : .srt s i ->
    Typed Δ m A ->
    Δ.static ⊢ n : B.[m/] ->
    Typed Δ (.tup m n .im s) (.sig A B .im s)

  | tup_ex {Δ1 Δ2 Δ3 A B m n s i} :
    Merge Δ1 Δ2 Δ3 ->
    Δ3.static ⊢ .sig A B .ex s : .srt s i ->
    Typed Δ1 m A ->
    Typed Δ2 n B.[m/] ->
    Typed Δ3 (.tup m n .ex s) (.sig A B .ex s)

  | prj_im {Δ1 Δ2 Δ3 A B C m n s sA sB sC iC} :
    Merge Δ1 Δ2 Δ3 ->
    .sig A B .im s :: Δ3.static ⊢ C : .srt sC iC ->
    Typed Δ1 m (.sig A B .im s) ->
    Typed (B :⟨.im, sB⟩ A :⟨.ex, sA⟩ Δ2) n C.[.tup (.var 1) (.var 0) .im s .: shift 2] ->
    Typed Δ3 (.prj C m n .im) C.[m/]

  | prj_ex {Δ1 Δ2 Δ3 A B C m n s sA sB sC iC} :
    Merge Δ1 Δ2 Δ3 ->
    .sig A B .ex s :: Δ3.static ⊢ C : .srt sC iC ->
    Typed Δ1 m (.sig A B .ex s) ->
    Typed (B :⟨.ex, sB⟩ A :⟨.ex, sA⟩ Δ2) n C.[.tup (.var 1) (.var 0) .ex s .: shift 2] ->
    Typed Δ3 (.prj C m n .ex) C.[m/]

  | tt {Δ} :
    Wf Δ ->
    Implicit Δ ->
    Typed Δ .tt .bool

  | ff {Δ} :
    Wf Δ ->
    Implicit Δ ->
    Typed Δ .ff .bool

  | ite {Δ1 Δ2 Δ3 A m n1 n2 s i} :
    Merge Δ1 Δ2 Δ3 ->
    .bool :: Δ3.static ⊢ A : .srt s i ->
    Typed Δ1 m .bool ->
    Typed Δ2 n1 A.[.tt/] ->
    Typed Δ2 n2 A.[.ff/] ->
    Typed Δ3 (.ite A m n1 n2) A.[m/]

  | rw {Δ A B m n a b s i} :
    .idn B.[shift 1] a.[shift 1] (.var 0) :: B :: Δ.static ⊢ A : .srt s i ->
    Typed Δ m A.[.rfl a,a/] ->
    Δ.static ⊢ n : .idn B a b ->
    Typed Δ (.rw A m n) A.[n,b/]

  | drop {Δ1 Δ2 Δ3 n A s} :
    Merge Δ1 Δ2 Δ3 ->
    Lower Δ1 s -> s ∈ ord.weaken_set ->
    Typed Δ2 n A ->
    Typed Δ3 n A

  | conv {Δ A B m s i} :
    A === B ->
    Typed Δ m A ->
    Δ.static ⊢ B : .srt s i ->
    Typed Δ m B

inductive Wf : Ctx Srt -> Prop where
  | nil : Wf []
  | cons {Δ A r s i} :
    Δ.static ⊢ A : .srt s i ->
    Wf Δ ->
    Wf (A :⟨r, s⟩ Δ)
end

notation:50 Δ:50 " ⊢ " m:81 " :: " A:51 => Typed Δ m A
notation:50 Δ:50 " ⊢ " => Wf Δ

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Typed.rec_non_mutual {motive : ∀ Δ m A, @Typed Srt _ Δ m A -> Prop} :=
  Typed.rec (motive_1 := motive) (motive_2 := fun _ _ => True)

-- Register non-mutual recursor as default.
@[induction_eliminator]
def Wf.rec_non_mutual {motive : ∀ Δ, @Wf Srt _ Δ -> Prop} :=
  Wf.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := motive)

lemma Wf.merge {Δ Δ1 Δ2 : Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Δ1 ⊢ -> Δ2 ⊢ ∧ Δ ⊢ := by
  intro mrg wf1
  induction mrg
  case nil => aesop
  case contra mrg ih =>
    cases wf1
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.sym.static]
        rw[<-mrg.static] at tyA
        assumption
        assumption
      . constructor
        rw[<-mrg.static] at tyA
        assumption
        assumption
  case left mrg ih =>
    cases wf1
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.sym.static]
        rw[<-mrg.static] at tyA
        assumption
        assumption
      . constructor
        rw[<-mrg.static] at tyA
        assumption
        assumption
  case right mrg ih =>
    cases wf1
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.sym.static]
        rw[<-mrg.static] at tyA
        assumption
        assumption
      . constructor
        rw[<-mrg.static] at tyA
        assumption
        assumption
  case im mrg ih =>
    cases wf1
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.sym.static]
        rw[<-mrg.static] at tyA
        assumption
        assumption
      . constructor
        rw[<-mrg.static] at tyA
        assumption
        assumption

lemma Wf.split {Δ Δ1 Δ2 : Ctx Srt} :
    Merge Δ1 Δ2 Δ -> Δ ⊢ -> Δ1 ⊢ ∧ Δ2 ⊢ := by
  intro mrg wf
  induction mrg
  case nil => cases wf; aesop (add safe Wf)
  case contra mrg ih =>
    cases wf
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.static]
        assumption
        assumption
      . constructor
        rw[<-mrg.sym.static]
        assumption
        assumption
  case left mrg ih =>
    cases wf
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.static]
        assumption
        assumption
      . constructor
        rw[<-mrg.sym.static]
        assumption
        assumption
  case right mrg ih =>
    cases wf
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.static]
        assumption
        assumption
      . constructor
        rw[<-mrg.sym.static]
        assumption
        assumption
  case im mrg ih =>
    cases wf
    case cons wf tyA =>
      have ⟨wf1, wf2⟩ := ih wf; and_intros
      . constructor
        rw[<-mrg.static]
        assumption
        assumption
      . constructor
        rw[<-mrg.sym.static]
        assumption
        assumption

lemma Typed.toWf {Δ : Ctx Srt} {A m} : Δ ⊢ m :: A -> Δ ⊢ := by
  intro ty
  induction ty <;> try (solve | aesop)
  case lam_im ih =>
    cases ih
    aesop
  case lam_ex ih =>
    cases ih; assumption
  case app_ex mrg _ _ ih1 ih2 =>
    apply (Wf.merge mrg ih1).right
  case tup_ex mrg _ _ _ ih1 ih2 =>
    apply (Wf.merge mrg ih1).right
  case prj_im rs mrg _ _ _ ih1 ih2 =>
    rcases ih2 with _ | ⟨_, ih2⟩
    rcases ih2 with _ | ⟨_, ih2⟩
    apply (Wf.merge mrg ih1).right
  case prj_ex rs1 rs2 mrg _ _ _ ih1 ih2 =>
    rcases ih2 with _ | ⟨_, ih2⟩
    rcases ih2 with _ | ⟨_, ih2⟩
    apply (Wf.merge mrg ih1).right
  case ite mrg _ _ _ _ ih1 ih2 _ =>
    apply (Wf.merge mrg ih1).right
  case drop mrg _ _ _ ih =>
    apply (Wf.merge mrg.sym ih).right

lemma Wf.toStatic {Δ : Ctx Srt} : Δ ⊢ -> Δ.static ⊢ := by
  intro wf; induction wf
  all_goals aesop (add safe Static.Wf)

lemma Wf.hasStatic {Δ : Ctx Srt} {A x s} :
    Δ ⊢ -> Dynamic.Has Δ x s A -> Static.Has Δ.static x A := by
  intro wf hs; induction wf generalizing x s A <;> try trivial
  cases hs <;> aesop (add safe Static.Has)

lemma Wf.implicit {Δ : Ctx Srt} : Δ ⊢ -> Δ.toImplicit ⊢ := by
  intro wf; induction wf <;> try trivial
  case nil => simp; constructor
  case cons =>
    simp; constructor
    . simp; assumption
    . assumption

lemma Wf.has_typed {Δ : Ctx Srt} {A x s} :
    Δ ⊢ -> Has Δ x s A -> ∃ i, Δ.static ⊢ A : .srt s i := by
  intro wf hs; induction hs
  case nil wf =>
    cases wf; case cons i _ tyA =>
    existsi i; apply tyA.weaken tyA
  case cons wf ih =>
    cases wf; case cons i wf tyB =>
    have ⟨i, tyA⟩ := ih wf
    existsi i; apply tyA.weaken tyB

lemma Typed.toStatic {Δ : Ctx Srt} {m A} :
    Δ ⊢ m :: A -> Δ.static ⊢ m : A := by
  intro ty; induction ty
  case var wf hs _ =>
    constructor
    . apply wf.toStatic
    . apply wf.hasStatic hs
  case lam_im => constructor <;> aesop
  case lam_ex => constructor <;> aesop
  case app_im => constructor <;> aesop
  case app_ex mrg _ _ ihm ihn =>
    rw[<-mrg.static] at ihm
    rw[<-mrg.sym.static] at ihn
    constructor <;> aesop
  case tup_im => constructor <;> aesop
  case tup_ex mrg ty _ _ ihm ihn =>
    rw[<-mrg.static] at ihm
    rw[<-mrg.sym.static] at ihn
    constructor <;> aesop
  case prj_im mrg ty _ _ ihm ihn =>
    simp at ihn
    rw[<-mrg.static] at ihm
    rw[<-mrg.sym.static] at ihn
    constructor <;> aesop
  case prj_ex mrg ty _ _ ihm ihn =>
    simp at ihn
    rw[<-mrg.static] at ihm
    rw[<-mrg.sym.static] at ihn
    constructor <;> aesop
  case tt wf _ _ => constructor; apply wf.toStatic
  case ff wf _ _ => constructor; apply wf.toStatic
  case ite mrg ty _ _ _ ihm ihn1 ihn2 =>
    simp at ihn1 ihn2
    rw[<-mrg.static] at ihm
    rw[<-mrg.sym.static] at ihn1
    rw[<-mrg.sym.static] at ihn2
    constructor <;> aesop
  case rw => constructor <;> aesop
  case drop mrg _ _ ihm ihn =>
    rw[<-mrg.sym.static] at ihn
    assumption
  case conv => constructor <;> assumption
  all_goals trivial

lemma Typed.ctx_inv {Δ : Ctx Srt} {A B m r s} :
    A :⟨r, s⟩ Δ ⊢ m :: B -> ∃ i, Δ ⊢ ∧ Δ.static ⊢ A : .srt s i := by
  intro ty
  have wf := ty.toWf
  rcases wf with _ | ⟨ty, wf⟩
  constructor <;> aesop
