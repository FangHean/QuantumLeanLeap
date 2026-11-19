import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.PostselectedSpectralTransformationTrigonometricQSP

noncomputable section
open scoped BigOperators

@[nolint defsWithUnderscore]
def R_y (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (α / 2) : ℂ), -(Real.sin (α / 2) : ℂ);
     (Real.sin (α / 2) : ℂ),  (Real.cos (α / 2) : ℂ)]

@[nolint defsWithUnderscore]
def R_z (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * (α : ℂ) / 2), 0;
     0, Complex.exp (Complex.I * (α : ℂ) / 2)]

def gateA (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  R_y θ * R_z φ

def controlledBlock {d : ℕ} (M₀ M₁ : Operator d) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  fun ⟨i, a⟩ ⟨j, b⟩ =>
    if i = j then (if i = 0 then M₀ a b else M₁ a b) else 0

def liftControl {d : ℕ} (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  fun ⟨i, a⟩ ⟨j, b⟩ => if a = b then A i j else 0

def buildScalarQSP
    (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ)
    (Rz : Matrix (Fin 2) (Fin 2) ℂ) :
    ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => A 0
  | n + 1 => A (n + 1) * Rz * buildScalarQSP A Rz n

def scalarQSPCircuit (L : ℕ)
    (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  buildScalarQSP A (R_z x) (2 * L)

def buildSpectralQSP {d : ℕ}
    (U : Operator d)
    (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ)
    (L : ℕ) : ℕ → Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ
  | 0 => liftControl (A 0)
  | n + 1 =>
    let slotIdx := 2 * L - n
    let ctrl := if slotIdx % 2 = 1
      then controlledBlock (1 : Operator d) U
      else controlledBlock U.conjTranspose (1 : Operator d)
    liftControl (A (n + 1)) * ctrl * buildSpectralQSP U A L n

def spectralQSPCircuit {d : ℕ} (L : ℕ)
    (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ)
    (U : Operator d) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  buildSpectralQSP U A L (2 * L)

def trigPolynomial (L : ℕ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
    c m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))

def trigPolynomialOfMatrix {d : ℕ} (L : ℕ) (c : ℤ → ℂ)
    (Upow : ℤ → Operator d) :
    Operator d :=
  ∑ m ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), c m • Upow m

def controlZeroBlock {d : ℕ}
    (M : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ) :
    Operator d :=
  fun a b => M (0, a) (0, b)

def matVec {d : ℕ}
    (A : Operator d) (ψ : Fin d → ℂ) : Fin d → ℂ :=
  fun i => ∑ j, A i j * ψ j

def norm2 {d : ℕ} (ψ : Fin d → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (ψ i))

def normalized {d : ℕ} (ψ : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (↑(1 / norm2 ψ) : ℂ) * ψ i

end

end QuantumLeanLeap.GoogleQHL.Bench36.PostselectedSpectralTransformationTrigonometricQSP
