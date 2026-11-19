import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.FidelityHammingWeightTruncatedPhaseState

noncomputable section
open scoped BigOperators

def hammingWeight {n : ℕ} (y : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => y i = 1).card

def R (n r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), Nat.choose n i

def phase {n : ℕ} (x y : Fin n → ZMod 2) : ℂ :=
  if (∑ i : Fin n, x i * y i : ZMod 2) = 0 then 1 else -1

def psiX (n : ℕ) (x : Fin n → ZMod 2) : (Fin n → ZMod 2) → ℂ :=
  fun y => ((Real.sqrt (2 ^ n : ℝ))⁻¹ : ℝ) * phase x y

def psiXR (n r : ℕ) (x : Fin n → ZMod 2) : (Fin n → ZMod 2) → ℂ :=
  fun y =>
    if hammingWeight y ≤ r
    then ((Real.sqrt (R n r : ℝ))⁻¹ : ℝ) * phase x y
    else 0

end

end QuantumLeanLeap.GoogleQHL.Bench36.FidelityHammingWeightTruncatedPhaseState
