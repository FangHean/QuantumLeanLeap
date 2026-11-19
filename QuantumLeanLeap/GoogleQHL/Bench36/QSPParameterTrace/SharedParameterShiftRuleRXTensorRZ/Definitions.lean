import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Kronecker


namespace QuantumLeanLeap.GoogleQHL.Bench36.SharedParameterShiftRuleRXTensorRZ

noncomputable section
open scoped BigOperators

def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

@[nolint defsWithUnderscore]
def R_X (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(↑(Real.cos (θ / 2)) : ℂ),
     -Complex.I * ↑(Real.sin (θ / 2));
     -Complex.I * ↑(Real.sin (θ / 2)),
     (↑(Real.cos (θ / 2)) : ℂ)]

@[nolint defsWithUnderscore]
def R_Z (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * ↑θ / 2), 0;
     0, Complex.exp (Complex.I * ↑θ / 2)]

variable {K : Type*} [Fintype K] [DecidableEq K]

def V (θ : ℝ) : Matrix ((Fin 2 × Fin 2) × K) ((Fin 2 × Fin 2) × K) ℂ :=
  Matrix.kronecker (Matrix.kronecker (R_X θ) (R_Z θ)) (1 : Matrix K K ℂ)

def loss
    (ρ O : Matrix ((Fin 2 × Fin 2) × K) ((Fin 2 × Fin 2) × K) ℂ)
    (θ : ℝ) : ℂ :=
  Matrix.trace (O * V θ * ρ * (V θ).conjTranspose)

end

end QuantumLeanLeap.GoogleQHL.Bench36.SharedParameterShiftRuleRXTensorRZ
