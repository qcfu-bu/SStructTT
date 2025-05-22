import SStructTT.Basics.ARS
import SStructTT.SStruct.Erasure.Syntax
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

@[scoped aesop safe [constructors]]
inductive Value : Tm Srt -> Prop where
  | lam {m s} :
    Value (.lam m s)
  | tup {m n s} :
    Value m ->
    Value n ->
    Value (.tup m n s)
  | tt : Value .tt
  | ff : Value .ff
  | ptr {l} : Value (.ptr l)
  | null : Value .null

@[scoped aesop safe [constructors]]
inductive Step : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta m n s :
    Value n ->
    Step (.app (.lam m s) n) m.[n/]
  | tup_M {m m'} n s :
    Step m m' ->
    Step (.tup m n s) (.tup m' n s)
  | tup_N m {n n'} s :
    Step n n' ->
    Step (.tup m n s) (.tup m n' s)
  | prj_M {m m'} n :
    Step m m' ->
    Step (.prj m n) (.prj m' n)
  | prj_elim {m1 m2} n {s} :
    Value (.tup m1 m2 s) ->
    Step (.prj (.tup m1 m2 s) n) n.[m2,m1/]
  | ite_M {m m'} n1 n2 :
    Step m m' ->
    Step (.ite m n1 n2) (.ite m' n1 n2)
  | ite_tt n1 n2 :
    Step (.ite .tt n1 n2) n1
  | ite_ff n1 n2 :
    Step (.ite .ff n1 n2) n2
  | rw_elim m :
    Step (.rw m) m
  | drop_elim m n :
    Step (.drop m n) n

notation:50 m:50 " ~>> " n:50 => Step m n
notation:50 m:50 " ~>>* " n:50 => ARS.Star Step m n
