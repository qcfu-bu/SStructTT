import Autosubst
import SStructTT.Basics.Attr.Register

-------------------------------------------------------------------------------------------------

-- The de Bruijn substitution machinery now comes from the `lean-autosubst` library
-- (`import Autosubst`, notations under `Autosubst` / `Autosubst.Notation`). This module only
-- retains the project-wide `Var` alias so the many `Var -> Var` / `Var -> Tm` signatures are
-- unaffected by the migration.
abbrev Var := Nat
