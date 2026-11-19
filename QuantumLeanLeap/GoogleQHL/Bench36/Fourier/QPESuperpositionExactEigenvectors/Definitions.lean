import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/




namespace QuantumLeanLeap.GoogleQHL.Bench36.QPESuperpositionExactEigenvectors

noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

abbrev TargetReg (τ : Type) := τ

abbrev CountReg (N : ℕ) := Fin N

def tensorKet {τ : Type} [Fintype τ] [DecidableEq τ] {N : ℕ}
    (i : Fin N) (u : Vec (TargetReg τ)) :
    Vec (Fin N × τ) :=
  WithLp.toLp 2 fun p =>
    (ket (ι := CountReg N) i : Vec (CountReg N)) p.1 * u p.2

def countQFT (N : ℕ) : Mat (CountReg N) :=
  fun j k =>
    (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) * (k.val : ℝ) / (N : ℝ)))

def phaseRibbon (N : ℕ) (φ : ℝ) : Vec (CountReg N) :=
  WithLp.toLp 2 fun j : Fin N =>
    (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I * (φ * (j.val : ℝ)))

def iqftCountingFactor {τ : Type} [Fintype τ] [DecidableEq τ] {N : ℕ}
    (countIQFT : Mat (CountReg N))
    (w : Vec (CountReg N)) (u : Vec (TargetReg τ)) :
    Vec (Fin N × τ) :=
  WithLp.toLp 2 fun p =>
    applyVec countIQFT w p.1 * u p.2

end

end QuantumLeanLeap.GoogleQHL.Bench36.QPESuperpositionExactEigenvectors
