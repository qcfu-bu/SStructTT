import SStructTT.Defs.ARS
import SStructTT.Defs.Syntax
open ARS

namespace Static
variable {Srt : Type}

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
  | proj_A {A A'} m n r :
    Step A A' ->
    Step (.proj A m n r) (.proj A' m n r)
  | proj_M A {m m'} n r :
    Step m m' ->
    Step (.proj A m n r) (.proj A m' n r)
  | proj_N A m {n n'} r :
    Step n n' ->
    Step (.proj A m n r) (.proj A m n' r)
  | proj_elim A m1 m2 n r s :
    Step (.proj A (.tup m1 m2 r s) n r) n.[m2,m1/]
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
  | ite_true A n1 n2 :
    Step (.ite A .tt n1 n2) n1
  | ite_false A n1 n2 :
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

abbrev StarStep := Star (@Step Srt)
abbrev ConvStep := Conv (@Step Srt)
infix:50 " ~> " => Step
infix:50 " ~>* " => StarStep
infix:50 " === " => ConvStep
