import SStructTT.Basics.Subst

open Autosubst Autosubst.Notation

namespace MLTT

autosubst
  Tm where
    | ty  : Nat → Tm
    | pi  : Tm → (bind Tm in Tm) → Tm
    | lam : Tm → (bind Tm in Tm) → Tm
    | app : Tm → Tm → Tm
    | sig : Tm → (bind Tm in Tm) → Tm
    | tup : Tm → Tm → Tm
    | prj : (bind Tm in Tm) → Tm → (bind Tm, Tm in Tm) → Tm
    | bool : Tm
    | tt : Tm
    | ff : Tm
    | ite : (bind Tm in Tm) → Tm → Tm → Tm → Tm
    | idn : Tm → Tm → Tm → Tm
    | rfl : Tm → Tm
    | rw  : (bind Tm, Tm in Tm) → Tm → Tm → Tm
    | bot : Tm
    | exf : (bind Tm in Tm) → Tm → Tm

end MLTT
