import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup


namespace QuantumLeanLeap.GoogleQHL.Bench36.FiniteQFTUnitarity

noncomputable section
variable (M : ℕ+)

def omegaM : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))

def qftMatrix : Matrix (Fin M) (Fin M) ℂ :=
  fun y x =>
    (Real.sqrt (M : ℝ) : ℂ)⁻¹ * omegaM M ^ ((x : ℕ) * (y : ℕ))

end

end QuantumLeanLeap.GoogleQHL.Bench36.FiniteQFTUnitarity
