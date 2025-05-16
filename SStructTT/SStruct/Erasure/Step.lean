import SStructTT.Basics.ARS
import SStructTT.SStruct.Erasure.Syntax
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

def Ctrl.ctrl : Ctrl -> Tm Srt -> Tm Srt
  | .keep => id
  | .drop => fun _ => .none

@[scoped aesop safe [constructors]]
inductive Value : Tm Srt -> Prop where
  | lam {m s c} :
    Value (.lam m c s)
  | tup {m n s} :
    Value m ->
    Value n ->
    Value (.tup m n s)
  | tt : Value .tt
  | ff : Value .ff
  | none : Value .none

@[scoped aesop safe [constructors]]
inductive Step : Tm Srt -> Tm Srt -> Prop where
  | app_M {m m'} n :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta m n n' c s :
    Value n ->
    c.ctrl n = n' ->
    Step (.app (.lam m c s) n) m.[n'/]
  | tup_M {m m'} n s :
    Step m m' ->
    Step (.tup m n s) (.tup m' n s)
  | tup_N m {n n'} s :
    Step n n' ->
    Step (.tup m n s) (.tup m n' s)
  | proj_M {m m'} n c1 c2 :
    Step m m' ->
    Step (.proj m n c1 c2) (.proj m' n c1 c2)
  | proj_elim {m1 m2 m1' m2'} n c1 c2 {s} :
    Value (.tup m1 m2 s) ->
    c1.ctrl m1 = m1' ->
    c2.ctrl m2 = m2' ->
    Step (.proj (.tup m1 m2 s) n c1 c2) n.[m2',m1'/]
  | ite_M {m m'} n1 n2 :
    Step m m' ->
    Step (.ite m n1 n2) (.ite m' n1 n2)
  | ite_tt n1 n2 :
    Step (.ite .tt n1 n2) n1
  | ite_ff n1 n2 :
    Step (.ite .ff n1 n2) n2

notation:50 m:50 " ~>>' " n:50 => Step m n
notation:50 m:50 " ~>>'* " n:50 => ARS.Star Step m n
