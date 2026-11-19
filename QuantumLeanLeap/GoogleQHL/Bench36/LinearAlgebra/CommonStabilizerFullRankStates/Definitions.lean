import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup


namespace QuantumLeanLeap.GoogleQHL.Bench36.CommonStabilizerFullRankStates

noncomputable section
open scoped BigOperators

def IsHermitianTraceOne {d : ℕ}
    (ρ : Operator d) : Prop :=
  ρ.conjTranspose = ρ ∧ Matrix.trace ρ = 1

def IsFullRank {d : ℕ}
    (ρ : Operator d) : Prop :=
  ρ.det ≠ 0

def ketbra {d : ℕ} (v w : Fin d → ℂ) :
    Operator d :=
  fun i j => v i * starRingEnd ℂ (w j)

def innerProd {d : ℕ} (v w : Fin d → ℂ) : ℂ :=
  ∑ i : Fin d, starRingEnd ℂ (v i) * w i

def HasSpectralExpansion {d : ℕ}
    (ρ : Operator d)
    (eigenvalues : Fin d → ℝ)
    (eigenvectors : Fin d → Fin d → ℂ) : Prop :=
  ρ = ∑ i, (eigenvalues i : ℂ) • ketbra (eigenvectors i) (eigenvectors i) ∧
    (∀ i j : Fin d, innerProd (eigenvectors i) (eigenvectors j) = if i = j then 1 else 0)

def SimpleSpectrum {d : ℕ} (eigenvalues : Fin d → ℝ) : Prop :=
  ∀ i i' : Fin d, i ≠ i' → eigenvalues i ≠ eigenvalues i'

def IsScalarUnitary {d : ℕ}
    (W : Operator d) : Prop :=
  ∃ θ : ℝ, W = Complex.exp (Complex.I * (θ : ℂ)) • (1 : Operator d)

end

end QuantumLeanLeap.GoogleQHL.Bench36.CommonStabilizerFullRankStates
