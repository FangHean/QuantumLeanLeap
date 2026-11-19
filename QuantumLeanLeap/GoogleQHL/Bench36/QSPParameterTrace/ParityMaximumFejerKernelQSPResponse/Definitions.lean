import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.ParityMaximumFejerKernelQSPResponse

noncomputable section
open scoped BigOperators

def Wx (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), Complex.I * ↑(Real.sqrt (1 - a ^ 2));
     Complex.I * ↑(Real.sqrt (1 - a ^ 2)), (a : ℂ)]

def Z : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, (-1 : ℂ)]

def phaseZ (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * (φ : ℂ)), 0;
     0, Complex.exp (-Complex.I * (φ : ℂ))]

@[nolint defsWithUnderscore]
def U_phi (a : ℝ) (k : ℕ) (phi : Fin (k + 1) → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let factors : List (Matrix (Fin 2) (Fin 2) ℂ) :=
    List.ofFn (fun j : Fin k => Wx a * phaseZ (phi (Fin.succ j)))
  phaseZ (phi 0) * List.foldl (· * ·) 1 factors

def qspResponse (k : ℕ) (phi : Fin (k + 1) → ℝ) (a : ℝ) : ℂ :=
  (U_phi a k phi) 0 0

def fejerP (k : ℕ) (a : ℝ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
    ((((k : ℝ) - (Int.natAbs ℓ : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) *
      Complex.exp (2 * Complex.I * (ℓ : ℂ) * ↑(Real.arccos a))

def theta (a : ℝ) : ℝ := 2 * Real.arccos a

def fejerGeometricSum (k : ℕ) (θ : ℝ) : ℂ :=
  ∑ m : Fin (k + 1), Complex.exp (Complex.I * ((m : ℕ) : ℂ) * (θ : ℂ))

def fejerPReal (k : ℕ) (a : ℝ) : ℝ := (fejerP k a).re

end

end QuantumLeanLeap.GoogleQHL.Bench36.ParityMaximumFejerKernelQSPResponse
