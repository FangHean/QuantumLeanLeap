import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.PostMeasurementStateObservedQubit

noncomputable section
open scoped BigOperators

def outcomeProbability {Y : Type*} [Fintype Y]
    (ψ : Fin 2 × Y → ℂ) (b : Fin 2) : ℝ :=
  ∑ x : Fin 2 × Y, if x.1 = b then Complex.normSq (ψ x) else 0

def postMeasState {Y : Type*} [Fintype Y]
    (ψ : Fin 2 × Y → ℂ) (b : Fin 2) : Fin 2 × Y → ℂ :=
  fun x =>
    if x.1 = b
    then (↑(Real.sqrt (outcomeProbability ψ b))⁻¹ : ℂ) * ψ x
    else 0

end

end QuantumLeanLeap.GoogleQHL.Bench36.PostMeasurementStateObservedQubit
