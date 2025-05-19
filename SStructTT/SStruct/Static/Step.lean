import SStructTT.Basics.ARS
import SStructTT.SStruct.Syntax
open ARS

namespace SStruct.Static
variable {Srt : Type}

@[scoped aesop safe [constructors]]
inductive Value : Tm Srt -> Prop where
  | srt s i : Value (.srt s i)
  | pi A B r s : Value (.pi A B r s)
  | lam A m r s : Value (.lam A m r s)
  | sig A B r s : Value (.sig A B r s)
  | tup m n r s :
    Value m ->
    Value n ->
    Value (.tup m n r s)
  | bool : Value .bool
  | tt : Value .tt
  | ff : Value .ff
  | idn A m n : Value (.idn A m n)
  | rfl m : Value (.rfl m)

@[scoped aesop safe [constructors]]
inductive Step : Tm Srt -> Tm Srt -> Prop where
  | pi_A {A A'} B r s :
    Step A A' ->
    Step (.pi A B r s) (.pi A' B r s)
  | pi_B A {B B'} r s :
    Step B B' ->
    Step (.pi A B r s) (.pi A B' r s)
  | lam_A {A A'} m r s :
    Step A A' ->
    Step (.lam A m r s) (.lam A' m r s)
  | lam_M A {m m'} r s :
    Step m m' ->
    Step (.lam A m r s) (.lam A m' r s)
  | app_M {m m'} n r :
    Step m m' ->
    Step (.app m n r) (.app m' n r)
  | app_N m {n n'} r :
    Step n n' ->
    Step (.app m n r) (.app m n' r)
  | beta A m n r s :
    Step (.app (.lam A m r s) n r) m.[n/]
  | sig_A {A A'} B r s :
    Step A A' ->
    Step (.sig A B r s) (.sig A' B r s)
  | sig_B A {B B'} r s :
    Step B B' ->
    Step (.sig A B r s) (.sig A B' r s)
  | tup_M {m m'} n r s :
    Step m m' ->
    Step (.tup m n r s) (.tup m' n r s)
  | tup_N m {n n'} r s :
    Step n n' ->
    Step (.tup m n r s) (.tup m n' r s)
  | prj_A {A A'} m n r :
    Step A A' ->
    Step (.prj A m n r) (.prj A' m n r)
  | prj_M A {m m'} n r :
    Step m m' ->
    Step (.prj A m n r) (.prj A m' n r)
  | prj_N A m {n n'} r :
    Step n n' ->
    Step (.prj A m n r) (.prj A m n' r)
  | prj_elim A m1 m2 n r s :
    Step (.prj A (.tup m1 m2 r s) n r) n.[m2,m1/]
  | ite_A {A A'} m n1 n2 :
    Step A A' ->
    Step (.ite A m n1 n2) (.ite A' m n1 n2)
  | ite_M A {m m'} n1 n2 :
    Step m m' ->
    Step (.ite A m n1 n2) (.ite A m' n1 n2)
  | ite_N1 A m {n1 n1'} n2 :
    Step n1 n1' ->
    Step (.ite A m n1 n2) (.ite A m n1' n2)
  | ite_N2 A m n1 {n2 n2'} :
    Step n2 n2' ->
    Step (.ite A m n1 n2) (.ite A m n1 n2')
  | ite_tt A n1 n2 :
    Step (.ite A .tt n1 n2) n1
  | ite_ff A n1 n2 :
    Step (.ite A .ff n1 n2) n2
  | idn_A {A A'} m n :
    Step A A' ->
    Step (.idn A m n) (.idn A' m n)
  | idn_M A {m m'} n :
    Step m m' ->
    Step (.idn A m n) (.idn A m' n)
  | idn_N A m {n n'} :
    Step n n' ->
    Step (.idn A m n) (.idn A m n')
  | rfl_M {m m'} :
    Step m m' ->
    Step (.rfl m) (.rfl m')
  | rw_A {A A'} m n :
    Step A A' ->
    Step (.rw A m n) (.rw A' m n)
  | rw_M A {m m'} n :
    Step m m' ->
    Step (.rw A m n) (.rw A m' n)
  | rw_N A m {n n'} :
    Step n n' ->
    Step (.rw A m n) (.rw A m n')
  | rw_elim A m n :
    Step (.rw A m (.rfl n)) m

notation:50 m:50 " ~> " n:50 => Step m n
notation:50 m:50 " ~>* " n:50 => ARS.Star Step m n
notation:50 m:50 " === " n:50 => ARS.Conv Step m n
