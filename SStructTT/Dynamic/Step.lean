import SStructTT.Defs.ARS
import SStructTT.Defs.Syntax
open ARS

namespace Dynamic
variable {Srt : Type}

@[scoped aesop safe [constructors]]
inductive Value : Tm Srt -> Prop where
  | lam_im {A B s} :
    Value (.lam A B .im s)
  | lam_ex {A B s} :
    Value (.lam A B .ex s)
  | tup_im {m n s} :
    Value m ->
    Value (.tup m n .im s)
  | tup_ex {m n s} :
    Value m ->
    Value n ->
    Value (.tup m n .ex s)
  | tt : Value .tt
  | ff : Value .ff

@[scoped aesop safe [constructors]]
inductive Step : Tm Srt -> Tm Srt -> Prop where
  | app_im_M {m m'} n :
    Step m m' ->
    Step (.app m n .im) (.app m' n .im)
  | app_ex_M {m m'} n :
    Step m m' ->
    Step (.app m n .ex) (.app m' n .ex)
  | app_ex_N m {n n'} :
    Step n n' ->
    Step (.app m n .ex) (.app m n' .ex)
  | beta_im A m n s :
    Step (.app (.lam A m .im s) n .im) m.[n/]
  | beta_ex A m n s :
    Value n ->
    Step (.app (.lam A m .ex s) n .ex) m.[n/]
  | tup_im_M {m m'} n s :
    Step m m' ->
    Step (.tup m n .im s) (.tup m' n .im s)
  | tup_ex_M {m m'} n s :
    Step m m' ->
    Step (.tup m n .ex s) (.tup m' n .ex s)
  | tup_ex_N m {n n'} s :
    Step n n' ->
    Step (.tup m n .ex s) (.tup m n' .ex s)
  | proj_im_M A {m m'} n :
    Step m m' ->
    Step (.proj A m n .im) (.proj A m' n .im)
  | proj_ex_M A {m m'} n :
    Step m m' ->
    Step (.proj A m n .ex) (.proj A m' n .ex)
  | proj_im_elim A {m1 m2} n {s} :
    Value (.tup m1 m2 .im s) ->
    Step (.proj A (.tup m1 m2 .im s) n .im) n.[m2,m1/]
  | proj_ex_elim A {m1 m2} n {s} :
    Value (.tup m1 m2 .ex s) ->
    Step (.proj A (.tup m1 m2 .ex s) n .ex) n.[m2,m1/]
  | ite_M A {m m'} n1 n2 :
    Step m m' ->
    Step (.ite A m n1 n2) (.ite A m' n1 n2)
  | ite_true A n1 n2 :
    Step (.ite A .tt n1 n2) n1
  | ite_false A n1 n2 :
    Step (.ite A .ff n1 n2) n2
  | rw_elim A m n :
    Step (.rw A m n) m

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n
