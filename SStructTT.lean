-- This module serves as the root of the `SStructTT` library.
-- Import modules here that should be built as part of the library.

-------------------------------------------------------------------------------------------------

import SStructTT.Basics.ARS
import SStructTT.Basics.Subst

-------------------------------------------------------------------------------------------------

import SStructTT.MartinLof.Syntax
import SStructTT.MartinLof.Context
import SStructTT.MartinLof.Step
import SStructTT.MartinLof.Confluence
import SStructTT.MartinLof.Typed
import SStructTT.MartinLof.Renaming
import SStructTT.MartinLof.Substitution
import SStructTT.MartinLof.Normalize

-------------------------------------------------------------------------------------------------

import SStructTT.SStruct.SrtOrder
import SStructTT.SStruct.Syntax

import SStructTT.SStruct.Static.Context
import SStructTT.SStruct.Static.Step
import SStructTT.SStruct.Static.Confluence
import SStructTT.SStruct.Static.Typed
import SStructTT.SStruct.Static.Renaming
import SStructTT.SStruct.Static.Substitution
import SStructTT.SStruct.Static.Inversion
import SStructTT.SStruct.Static.Unique
import SStructTT.SStruct.Static.Preservation
import SStructTT.SStruct.Static.Progress
import SStructTT.SStruct.Static.Normalize

import SStructTT.SStruct.Dynamic.Context
import SStructTT.SStruct.Dynamic.Step
import SStructTT.SStruct.Dynamic.Typed
import SStructTT.SStruct.Dynamic.Renaming
import SStructTT.SStruct.Dynamic.Substitution
import SStructTT.SStruct.Dynamic.Inversion
import SStructTT.SStruct.Dynamic.Preservation
import SStructTT.SStruct.Dynamic.Progress
import SStructTT.SStruct.Dynamic.Normalize

import SStructTT.SStruct.Erasure.Syntax
import SStructTT.SStruct.Erasure.Step
import SStructTT.SStruct.Erasure.Erased
import SStructTT.SStruct.Erasure.Renaming
import SStructTT.SStruct.Erasure.Substitution
import SStructTT.SStruct.Erasure.Inversion
import SStructTT.SStruct.Erasure.Preservation
import SStructTT.SStruct.Erasure.Progress
import SStructTT.SStruct.Erasure.Normalize

import SStructTT.SStruct.Runtime.Heap
import SStructTT.SStruct.Runtime.Step
import SStructTT.SStruct.Runtime.Resolution
import SStructTT.SStruct.Runtime.Substitution
-- import SStructTT.SStruct.Runtime.Preservation
