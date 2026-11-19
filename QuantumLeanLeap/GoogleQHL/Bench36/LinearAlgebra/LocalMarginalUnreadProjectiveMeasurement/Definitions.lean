import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Kronecker


namespace QuantumLeanLeap.GoogleQHL.Bench36.LocalMarginalUnreadProjectiveMeasurement

noncomputable section
open scoped BigOperators

abbrev Qubit := Fin 2

abbrev Bipartite := Qubit × Qubit

def ketbraB (b b' : Qubit) : Matrix Qubit Qubit ℂ :=
  fun i j => if i = b ∧ j = b' then 1 else 0

def jointProjector (b : Qubit) : Matrix Bipartite Bipartite ℂ :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ =>
    if a₁ = a₂ ∧ b₁ = b ∧ b₂ = b then 1 else 0

def blockExpansion
    (ρA : Qubit → Qubit → Matrix Qubit Qubit ℂ) :
    Matrix Bipartite Bipartite ℂ :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => ρA b₁ b₂ a₁ a₂

def postMeasurement
    (ρ : Matrix Bipartite Bipartite ℂ) : Matrix Bipartite Bipartite ℂ :=
  ∑ b : Qubit, jointProjector b * ρ * jointProjector b

def diagonalBlockState
    (ρA : Qubit → Qubit → Matrix Qubit Qubit ℂ) :
    Matrix Bipartite Bipartite ℂ :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ =>
    if b₁ = b₂ then ρA b₁ b₁ a₁ a₂ else 0

def partialTraceB
    (ρ : Matrix Bipartite Bipartite ℂ) : Matrix Qubit Qubit ℂ :=
  fun a a' => ∑ b : Qubit, ρ (a, b) (a', b)

def IsHermitianTraceOne (ρ : Matrix Bipartite Bipartite ℂ) : Prop :=
  ρ.conjTranspose = ρ ∧ Matrix.trace ρ = 1

end

end QuantumLeanLeap.GoogleQHL.Bench36.LocalMarginalUnreadProjectiveMeasurement
