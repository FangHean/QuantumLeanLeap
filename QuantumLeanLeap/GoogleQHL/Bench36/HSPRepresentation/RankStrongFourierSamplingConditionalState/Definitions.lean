import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.RankStrongFourierSamplingConditionalState

noncomputable section
open scoped BigOperators
variable {G V : Type*} [Group G] [Finite G] [Fintype V] [DecidableEq V]

def sigmaSum (H : Subgroup G) (σ : G → Matrix V V ℂ) : Matrix V V ℂ := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, σ h.1

def charSum (H : Subgroup G) (χ : G → ℂ) : ℂ := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, χ h.1

def charSumStar (H : Subgroup G) (χ : G → ℂ) : ℂ := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, star (χ h.1)

@[nolint defsWithUnderscore]
def P_H_sigma (H : Subgroup G) (σ : G → Matrix V V ℂ) : Matrix V V ℂ :=
  (1 / (Nat.card H : ℂ)) • sigmaSum H σ

def rhoHat (H : Subgroup G) (σ : G → Matrix V V ℂ) (χ : G → ℂ) :
    Matrix V V ℂ :=
  (charSumStar H χ)⁻¹ • (sigmaSum H σ).conjTranspose

def IsHInvariant (H : Subgroup G) (σ : G → Matrix V V ℂ) (v : V → ℂ) : Prop :=
  ∀ h : H, (σ h.1).mulVec v = v

def IsOrthogonalProjectorOnto
    (P : Matrix V V ℂ) (S : (V → ℂ) → Prop) : Prop :=
  P.conjTranspose = P ∧ P * P = P ∧ ∀ v : V → ℂ, S v ↔ P.mulVec v = v

end

end QuantumLeanLeap.GoogleQHL.Bench36.RankStrongFourierSamplingConditionalState
