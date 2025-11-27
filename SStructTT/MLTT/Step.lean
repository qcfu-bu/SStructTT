import SStructTT.Basics.ARS
import SStructTT.MLTT.Syntax
open ARS

namespace MLTT

@[scoped aesop safe [constructors]]
inductive Step : Tm -> Tm -> Prop where
  | pi_A {A A'} B :
    Step A A' ->
    Step (.pi A B) (.pi A' B)
  | pi_B A {B B'} :
    Step B B' ->
    Step (.pi A B) (.pi A B')
  | lam_A {A A'} m :
    Step A A' ->
    Step (.lam A m) (.lam A' m)
  | lam_M A {m m'} :
    Step m m' ->
    Step (.lam A m) (.lam A m')
  | app_M {m m'} n :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta A m n :
    Step (.app (.lam A m) n) m.[n/]
  | sig_A {A A'} B :
    Step A A' ->
    Step (.sig A B) (.sig A' B)
  | sig_B A {B B'} :
    Step B B' ->
    Step (.sig A B) (.sig A B')
  | tup_M {m m'} n :
    Step m m' ->
    Step (.tup m n) (.tup m' n)
  | tup_N m {n n'} :
    Step n n' ->
    Step (.tup m n) (.tup m n')
  | prj_A {A A'} m n :
    Step A A' ->
    Step (.prj A m n) (.prj A' m n)
  | prj_M A {m m'} n :
    Step m m' ->
    Step (.prj A m n) (.prj A m' n)
  | prj_N A m {n n'} :
    Step n n' ->
    Step (.prj A m n) (.prj A m n')
  | prj_elim A m1 m2 n :
    Step (.prj A (.tup m1 m2) n) n.[m2,m1/]
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
