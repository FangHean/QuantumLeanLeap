import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Group.Subgroup.Finite


namespace QuantumLeanLeap.GoogleQHL.Bench36.FidelityBoundHiddenSubgroupCosetStates

noncomputable section
open scoped BigOperators
variable (G : Type*) [Group G] [Finite G]

def cosetState (g : G) (K : Subgroup G) : G → ℂ := by
  classical
  exact fun x =>
    if ∃ k : G, k ∈ K ∧ x = g * k then
      ((1 / Real.sqrt (Nat.card K : ℝ)) : ℂ)
    else 0

def rhoK (K : Subgroup G) : G → G → ℂ := fun x y =>
  letI : Fintype G := Fintype.ofFinite G
  (1 / (Fintype.card G : ℂ)) *
    (∑ g : G, cosetState G g K x * star (cosetState G g K y))

def supportProjector (H : Subgroup G) : G → G → ℂ := by
  classical
  exact fun x y =>
    (1 : ℂ) / (Nat.card H : ℂ) * (if (x⁻¹ * y) ∈ H then 1 else 0)

def matTrace (P ρ : G → G → ℂ) : ℝ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact (∑ x : G, ∑ y : G, P x y * ρ y x).re

def subgroupInterCard (H K : Subgroup G) : ℕ :=
  Nat.card (H ⊓ K : Subgroup G)

def vecInner (f g : G → ℂ) : ℂ := by
  letI : Fintype G := Fintype.ofFinite G
  exact ∑ x : G, starRingEnd ℂ (f x) * g x

def cosetOverlapFinset (g g' : G) (H K : Subgroup G) : Finset G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact (Finset.univ : Finset G).filter (fun x =>
    ∃ h : G, h ∈ H ∧ ∃ k : G, k ∈ K ∧ x = g * h ∧ x = g' * k)

end

end QuantumLeanLeap.GoogleQHL.Bench36.FidelityBoundHiddenSubgroupCosetStates
