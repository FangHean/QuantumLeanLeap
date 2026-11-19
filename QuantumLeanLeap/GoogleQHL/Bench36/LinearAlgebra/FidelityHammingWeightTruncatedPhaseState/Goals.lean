import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.FidelityHammingWeightTruncatedPhaseState.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.FidelityHammingWeightTruncatedPhaseState
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 (n r : ℕ) (x : Fin n → ZMod 2) : Prop :=
  Complex.normSq
      (∑ y : Fin n → ZMod 2,
        starRingEnd ℂ (psiX n x y) * psiXR n r x y) =
      (R n r : ℝ) / (2 : ℝ) ^ n

def obligation_1 (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) : Prop :=
  ∃ c : ℝ, 0 < c ∧
      Filter.liminf
        (fun n : ℕ =>
          (R n ⌊(n : ℝ) / 2 + c * Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 : ℝ) ^ n)
        Filter.atTop ≥ 1 - η

end
end QuantumLeanLeap.GoogleQHL.Bench36.FidelityHammingWeightTruncatedPhaseState
