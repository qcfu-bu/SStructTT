-- This module serves as the root of the `SStructTT` library.
-- Import modules here that should be built as part of the library.

-------------------------------------------------------------------------------------------------

import SStructTT.Basics.ARS
import SStructTT.Basics.Subst

-------------------------------------------------------------------------------------------------

import SStructTT.ECC.Syntax
import SStructTT.ECC.Context
import SStructTT.ECC.Step
import SStructTT.ECC.Confluence
import SStructTT.ECC.Typed
import SStructTT.ECC.Renaming
import SStructTT.ECC.Substitution
import SStructTT.ECC.Normalize

-------------------------------------------------------------------------------------------------

import SStructTT.SStruct.SrtOrder
import SStructTT.SStruct.Syntax

import SStructTT.SStruct.Logical.Context
import SStructTT.SStruct.Logical.Step
import SStructTT.SStruct.Logical.Confluence
import SStructTT.SStruct.Logical.Typed
import SStructTT.SStruct.Logical.Renaming
import SStructTT.SStruct.Logical.Substitution
import SStructTT.SStruct.Logical.Inversion
import SStructTT.SStruct.Logical.Unique
import SStructTT.SStruct.Logical.Preservation
import SStructTT.SStruct.Logical.Progress
import SStructTT.SStruct.Logical.Normalize

import SStructTT.SStruct.Program.Context
import SStructTT.SStruct.Program.Step
import SStructTT.SStruct.Program.Typed
import SStructTT.SStruct.Program.Renaming
import SStructTT.SStruct.Program.Substitution
import SStructTT.SStruct.Program.Inversion
import SStructTT.SStruct.Program.Preservation
import SStructTT.SStruct.Program.Progress
import SStructTT.SStruct.Program.Normalize

import SStructTT.SStruct.Extraction.Syntax
import SStructTT.SStruct.Extraction.Step
import SStructTT.SStruct.Extraction.Extract
import SStructTT.SStruct.Extraction.Renaming
import SStructTT.SStruct.Extraction.Substitution
import SStructTT.SStruct.Extraction.Inversion
import SStructTT.SStruct.Extraction.Preservation
import SStructTT.SStruct.Extraction.Progress
import SStructTT.SStruct.Extraction.Normalize

import SStructTT.SStruct.Runtime.Heap
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
import SStructTT.SStruct.Runtime.Substitution
import SStructTT.SStruct.Runtime.DropSafe
import SStructTT.SStruct.Runtime.Preservation0
import SStructTT.SStruct.Runtime.Preservation1
import SStructTT.SStruct.Runtime.Preservation2
import SStructTT.SStruct.Runtime.Preservation
import SStructTT.SStruct.Runtime.Normalize
import SStructTT.SStruct.Runtime.Poised
import SStructTT.SStruct.Runtime.Progress
