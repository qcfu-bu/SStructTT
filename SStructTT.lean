-- This module serves as the root of the `SStructTT` library.
-- Import modules here that should be built as part of the library.
import SStructTT.Defs.ARS
import SStructTT.Defs.Subst
import SStructTT.Defs.SStruct
import SStructTT.Defs.Syntax

import SStructTT.Static.Context
import SStructTT.Static.Step
import SStructTT.Static.Confluence
import SStructTT.Static.Typed
import SStructTT.Static.Renaming
import SStructTT.Static.Substitution
import SStructTT.Static.Inversion
import SStructTT.Static.Unique
import SStructTT.Static.Preservation
import SStructTT.Static.Progress

import SStructTT.Dynamic.Context
import SStructTT.Dynamic.Step
import SStructTT.Dynamic.Typed
import SStructTT.Dynamic.Renaming
import SStructTT.Dynamic.Substitution
import SStructTT.Dynamic.Inversion
import SStructTT.Dynamic.Preservation
import SStructTT.Dynamic.Progress
