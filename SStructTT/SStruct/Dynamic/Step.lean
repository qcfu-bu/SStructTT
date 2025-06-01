import SStructTT.Basics.ARS
import SStructTT.SStruct.Syntax
open ARS

namespace SStruct.Dynamic
variable {Srt : Type}

@[scoped aesop safe [constructors]]
inductive Value : Tm Srt -> Prop where
  | lam_im {A m s} :
    Value (.lam A m .im s)
  | lam_ex {A m s} :
    Value (.lam A m .ex s)
  | tup_im {m n s} :
    Value n ->
    Value (.tup m n .im s)
  | tup_ex {m n s} :
    Value m ->
    Value n ->
    Value (.tup m n .ex s)
  | tt : Value .tt
  | ff : Value .ff

@[scoped aesop safe [constructors]]
inductive Step : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta_im A m n s :
    Step (.app (.lam A m .im s) n) m.[n/]
  | beta_ex A m n s :
    Value n ->
    Step (.app (.lam A m .ex s) n) m.[n/]
  | tup_im_N m {n n'} s :
    Step n n' ->
    Step (.tup m n .im s) (.tup m n' .im s)
  | tup_ex_M {m m'} n s :
    Step m m' ->
    Step (.tup m n .ex s) (.tup m' n .ex s)
  | tup_ex_N m {n n'} s :
    Step n n' ->
    Step (.tup m n .ex s) (.tup m n' .ex s)
  | prj_M A {m m'} n :
    Step m m' ->
    Step (.prj A m n) (.prj A m' n)
  | prj_im_elim A {m1 m2} n {s} :
    Value (.tup m1 m2 .im s) ->
    Step (.prj A (.tup m1 m2 .im s) n) n.[m2,m1/]
  | prj_ex_elim A {m1 m2} n {s} :
    Value (.tup m1 m2 .ex s) ->
    Step (.prj A (.tup m1 m2 .ex s) n) n.[m2,m1/]
  | ite_M A {m m'} n1 n2 :
    Step m m' ->
    Step (.ite A m n1 n2) (.ite A m' n1 n2)
  | ite_tt A n1 n2 :
    Step (.ite A .tt n1 n2) n1
  | ite_ff A n1 n2 :
    Step (.ite A .ff n1 n2) n2
  | rw_elim A m n :
    Step (.rw A m n) m

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n
notation:50 m:50 " ~>>1 " n:50 => ARS.Star1 Step m n

lemma Red.app {m m' n n' : Tm Srt} :
    m ~>>* m' -> n ~>>* n' -> .app m n ~>>* .app m' n' := by
  intro rm rn;
  apply @Star.trans _ _ (.app m' n)
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.tup_im {m n n' : Tm Srt} {s} :
    n ~>>* n' -> .tup m n .im s ~>>* .tup m n' .im s := by
  intro rm; apply Star.hom _ _ rm; aesop

lemma Red.tup_ex {m m' n n' : Tm Srt} {s} :
    m ~>>* m' -> n ~>>* n' -> .tup m n .ex s ~>>* .tup m' n' .ex s := by
  intro rm rn;
  apply @Star.trans _ _ (.tup m' n .ex s)
  apply Star.hom _ _ rm; aesop
  apply Star.hom _ _ rn; aesop

lemma Red.prj {A m m' n : Tm Srt} :
    m ~>>* m' -> .prj A m n ~>>* .prj A m' n := by
  intro rm; apply Star.hom _ _ rm; aesop

lemma Red.ite {A m m' n1 n2 : Tm Srt} :
    m ~>>* m' -> .ite A m n1 n2 ~>>* .ite A m' n1 n2 := by
  intro rm; apply Star.hom _ _ rm; aesop

lemma Red1.app_M {m m' n : Tm Srt} :
    m ~>>1 m' -> .app m n ~>>1 .app m' n := by
  intro rm; apply Star1.hom _ _ rm; aesop

lemma Red1.app_N {m n n' : Tm Srt} :
    n ~>>1 n' -> .app m n ~>>1 .app m n' := by
  intro rn; apply Star1.hom _ _ rn; aesop

lemma Red1.tup_im {m n n' : Tm Srt} {s} :
    n ~>>1 n' -> .tup m n .im s ~>>1 .tup m n' .im s := by
  intro rm; apply Star1.hom _ _ rm; aesop

lemma Red1.tup_ex_M {m m' n : Tm Srt} {s} :
    m ~>>1 m' -> .tup m n .ex s ~>>1 .tup m' n .ex s := by
  intro rm; apply Star1.hom _ _ rm; aesop

lemma Red1.tup_ex_N {m n n' : Tm Srt} {s} :
    n ~>>1 n' -> .tup m n .ex s ~>>1 .tup m n' .ex s := by
  intro rn; apply Star1.hom _ _ rn; aesop

lemma Red1.prj {A m m' n : Tm Srt} :
    m ~>>1 m' -> .prj A m n ~>>1 .prj A m' n := by
  intro rm; apply Star1.hom _ _ rm; aesop

lemma Red1.ite {A m m' n1 n2 : Tm Srt} :
    m ~>>1 m' -> .ite A m n1 n2 ~>>1 .ite A m' n1 n2 := by
  intro rm; apply Star1.hom _ _ rm; aesop
