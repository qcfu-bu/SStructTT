import SStructTT.Defs.ARS
import SStructTT.Defs.Syntax
open ARS

namespace Static
variable {Srt : Type}

inductive Step : Tm Srt -> Tm Srt -> Prop where
  | piA {A A' B r s} :
    Step A A' ->
    Step (.pi A B r s) (.pi A' B r s)
  | piB {A B B' r s} :
    Step B B' ->
    Step (.pi A B r s) (.pi A B' r s)
  | lamA {A A' m r s} :
    Step A A' ->
    Step (.lam A m r s) (.lam A' m r s)
  | lamM {A m m' r s} :
    Step m m' ->
    Step (.lam A m r s) (.lam A m' r s)
  | appM {m m' n} :
    Step m m' ->
    Step (.app m n) (.app m' n)
  | appN {m n n'} :
    Step n n' ->
    Step (.app m n) (.app m n')
  | beta {A m n r s} :
    Step (.app (.lam A m r s) n) m.[n/]
  | sigA {A A' B r s} :
    Step A A' ->
    Step (.sig A B r s) (.sig A' B r s)
  | sigB {A B B' r s} :
    Step B B' ->
    Step (.sig A B r s) (.sig A B' r s)
  | pairM {m m' n r s} :
    Step m m' ->
    Step (.pair m n r s) (.pair m' n r s)
  | pairN {m n n' r s} :
    Step n n' ->
    Step (.pair m n r s) (.pair m n' r s)
  | projA {A A' m n} :
    Step A A' ->
    Step (.proj A m n) (.proj A' m n)
  | projM {A m m' n} :
    Step m m' ->
    Step (.proj A m n) (.proj A m' n)
  | projN {A m n n'} :
    Step n n' ->
    Step (.proj A m n) (.proj A m n')
  | projE {A m1 m2 n r s} :
    Step (.proj A (.pair m1 m2 r s) n) n.[m2,m1/]
  | ifteA {A A' m n1 n2} :
    Step A A' ->
    Step (.ifte A m n1 n2) (.ifte A' m n1 n2)
  | ifteM {A m m' n1 n2} :
    Step m m' ->
    Step (.ifte A m n1 n2) (.ifte A m' n1 n2)
  | ifteN1 {A m n1 n1' n2} :
    Step n1 n1' ->
    Step (.ifte A m n1 n2) (.ifte A m n1' n2)
  | ifteN2 {A m n1 n2 n2'} :
    Step n2 n2' ->
    Step (.ifte A m n1 n2) (.ifte A m n1 n2')
  | ifteT {A n1 n2} :
    Step (.ifte A .tt n1 n2) n1
  | ifteF {A n1 n2} :
    Step (.ifte A .ff n1 n2) n2
  | idA {A A' m n} :
    Step A A' ->
    Step (.id A m n) (.id A' m n)
  | idM {A m m' n} :
    Step m m' ->
    Step (.id A m n) (.id A m' n)
  | idN {A m n n'} :
    Step n n' ->
    Step (.id A m n) (.id A m n')
  | rflM {m m'} :
    Step m m' ->
    Step (.rfl m) (.rfl m')
  | rwA {A A' m n} :
    Step A A' ->
    Step (.rw A m n) (.rw A' m n)
  | rwM {A m m' n} :
    Step m m' ->
    Step (.rw A m n) (.rw A m' n)
  | rwN {A m n n'} :
    Step n n' ->
    Step (.rw A m n) (.rw A m n')
  | rwE {A m n} :
    Step (.rw A m (.rfl n)) n

@[reducible]def StarStep := Star (@Step Srt)
@[reducible]def ConvStep := Conv (@Step Srt)
infix:50 " ~> " => Step
infix:50 " ~>* " => StarStep
infix:50 " === " => ConvStep
