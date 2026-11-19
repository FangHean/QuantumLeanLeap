import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.ApproximateTwoDesignDepthHaarLossFluctuations

noncomputable section
open scoped BigOperators

abbrev N (n : ℕ) : ℕ := 2 ^ n

def lossFunction {d : ℕ}
    (U ρ O : Operator d) : ℂ :=
  Matrix.trace (U * ρ * U.conjTranspose * O)

def swapOp (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun ⟨i, j⟩ ⟨k, l⟩ => if i = l ∧ j = k then 1 else 0

end

end QuantumLeanLeap.GoogleQHL.Bench36.ApproximateTwoDesignDepthHaarLossFluctuations
