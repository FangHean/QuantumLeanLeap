import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup


namespace QuantumLeanLeap.GoogleQHL.Bench36.CoefficientOneNormTruncatedTaylorSimulation

noncomputable section
open scoped BigOperators

def IsPauliUnitary {d : ℕ} (P : Operator d) : Prop :=
  P ∈ Matrix.unitaryGroup (Fin d) ℂ

def hamiltonian {J : Type*} [Fintype J] {d : ℕ}
    (β : J → ℝ) (P : J → Operator d) :
    Operator d :=
  ∑ j : J, (β j : ℂ) • P j

def truncatedTaylorCoeff {J : Type*} {k : ℕ}
    (β : J → ℝ) (t : ℝ) (js : Fin k → J) : ℝ :=
  t ^ k * (∏ r : Fin k, β (js r)) / (Nat.factorial k : ℝ)

def truncatedTaylorLCU {J : Type*} [Fintype J] {d : ℕ}
    (K : ℕ) (β : J → ℝ) (t : ℝ)
    (Pphase : (k : ℕ) → (Fin k → J) → Operator d) :
    Operator d :=
  Finset.sum (Finset.range (K + 1)) fun k =>
    Finset.sum Finset.univ fun js : Fin k → J =>
      (truncatedTaylorCoeff β t js : ℂ) • Pphase k js

def coeffOneNorm {J : Type*} [Fintype J]
    (K : ℕ) (β : J → ℝ) (t : ℝ) : ℝ :=
  Finset.sum (Finset.range (K + 1)) fun k =>
    Finset.sum Finset.univ fun js : Fin k → J => truncatedTaylorCoeff β t js

def rawLCUSegmentCount {J : Type*} [Fintype J]
    (K : ℕ) (β : J → ℝ) (t : ℝ) : ℕ :=
  Nat.ceil (coeffOneNorm K β t)

end

end QuantumLeanLeap.GoogleQHL.Bench36.CoefficientOneNormTruncatedTaylorSimulation
