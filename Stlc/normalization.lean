import Stlc.basics
import Stlc.open_close
import Stlc.context
import Stlc.typing
import Stlc.reductions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

open Typ
open Trm
open multi_red

def normal (t : Trm) : Prop := ∀ u, (multi_red t u) → u = t 

theorem strongly_normalizing : ∀ u, ∃ t, normal t ∧ (multi_red u t) := by
  sorry