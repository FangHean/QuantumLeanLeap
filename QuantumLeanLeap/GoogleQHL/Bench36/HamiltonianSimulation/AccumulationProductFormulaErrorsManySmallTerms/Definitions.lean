import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.AccumulationProductFormulaErrorsManySmallTerms

noncomputable section
open scoped BigOperators
variable {d : ℕ}

def partialSum (H : ℕ → Operator d) (k : ℕ) :
    Operator d :=
  Finset.sum (Finset.Icc 1 k) (fun j => H j)

def orderedExpProduct (M : ℕ) (H : ℕ → Operator d)
    (expm : Operator d → Operator d) :
    Operator d :=
  ((List.range M).map (fun i => expm (H (i + 1)))).prod

end

end QuantumLeanLeap.GoogleQHL.Bench36.AccumulationProductFormulaErrorsManySmallTerms
