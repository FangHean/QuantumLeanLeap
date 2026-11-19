import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.UnitaryExtensionMarkovChainIsometry.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.UnitaryExtensionMarkovChainIsometry
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {d : ℕ} [NeZero d]
    (P : Matrix (Fin d) (Fin d) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row_sum : ∀ i, ∑ j : Fin d, P i j = 1) : Prop :=
  ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,

      U.conjTranspose * U = 1 ∧
      U * U.conjTranspose = 1 ∧

      (∀ i : Fin d,
        (fun x => ∑ y, U x y * basisTensorZero i y) =
          coherentRowState P i) ∧

      (∀ a b i : Fin d,
        U (a, b) (i, (0 : Fin d)) =
          if a = i then (Real.sqrt (P i b) : ℂ) else 0)

end
end QuantumLeanLeap.GoogleQHL.Bench36.UnitaryExtensionMarkovChainIsometry
