import SStructTT.Defs.ARS
import SStructTT.Defs.Syntax
open ARS

namespace Static
variable {Srt : Type}

@[scoped aesop safe [constructors]]
inductive Step : Tm Srt -> Tm Srt -> Prop where
  | pi0_A {A A'} B s :
    Step A A' ->
    Step (.pi0 A B s) (.pi0 A' B s)
  | pi0_B A {B B'} s :
    Step B B' ->
    Step (.pi0 A B s) (.pi0 A B' s)
  | pi1_A {A A'} B s :
    Step A A' ->
    Step (.pi1 A B s) (.pi1 A' B s)
  | pi1_B A {B B'} s :
    Step B B' ->
    Step (.pi1 A B s) (.pi1 A B' s)
  | lam0_A {A A'} m s :
    Step A A' ->
    Step (.lam0 A m s) (.lam0 A' m s)
  | lam0_M A {m m'} s :
    Step m m' ->
    Step (.lam0 A m s) (.lam0 A m' s)
  | lam1_A {A A'} m s :
    Step A A' ->
    Step (.lam1 A m s) (.lam1 A' m s)
  | lam1_M A {m m'} s :
    Step m m' ->
    Step (.lam1 A m s) (.lam1 A m' s)
  | app_M {m m'} n :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | app_N m {n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta0 A m n s :
    Step (.app (.lam0 A m s) n) m.[n/]
  | beta1 A m n s :
    Step (.app (.lam1 A m s) n) m.[n/]
  | sig0_A {A A'} B s :
    Step A A' ->
    Step (.sig0 A B s) (.sig0 A' B s)
  | sig0_B A {B B'} s :
    Step B B' ->
    Step (.sig0 A B s) (.sig0 A B' s)
  | sig1_A {A A'} B s :
    Step A A' ->
    Step (.sig1 A B s) (.sig1 A' B s)
  | sig1_B A {B B'} s :
    Step B B' ->
    Step (.sig1 A B s) (.sig1 A B' s)
  | tup0_M {m m'} n s :
    Step m m' ->
    Step (.tup0 m n s) (.tup0 m' n s)
  | tup0_N m {n n'} s :
    Step n n' ->
    Step (.tup0 m n s) (.tup0 m n' s)
  | tup1_M {m m'} n s :
    Step m m' ->
    Step (.tup1 m n s) (.tup1 m' n s)
  | tup1_N m {n n'} s :
    Step n n' ->
    Step (.tup1 m n s) (.tup1 m n' s)
  | proj_A {A A'} m n :
    Step A A' ->
    Step (.proj A m n) (.proj A' m n)
  | proj_M A {m m'} n :
    Step m m' ->
    Step (.proj A m n) (.proj A m' n)
  | proj_N A m {n n'} :
    Step n n' ->
    Step (.proj A m n) (.proj A m n')
  | proj0 A m1 m2 n s :
    Step (.proj A (.tup0 m1 m2 s) n) n.[m2,m1/]
  | proj1 A m1 m2 n s :
    Step (.proj A (.tup1 m1 m2 s) n) n.[m2,m1/]
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
