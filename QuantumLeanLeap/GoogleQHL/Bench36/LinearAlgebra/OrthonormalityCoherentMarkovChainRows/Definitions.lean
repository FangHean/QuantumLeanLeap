import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.OrthonormalityCoherentMarkovChainRows

noncomputable section
open scoped BigOperators

def coherentRowState {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (Fin d × Fin d) → ℂ :=
  fun ⟨a, b⟩ => if a = i then (Real.sqrt (P i b) : ℂ) else 0

end

end QuantumLeanLeap.GoogleQHL.Bench36.OrthonormalityCoherentMarkovChainRows
