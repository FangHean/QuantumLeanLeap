import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.OrthonormalityCoherentMarkovChainRows.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.OrthonormalityCoherentMarkovChainRows
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row_sum : ∀ i, ∑ j : Fin d, P i j = 1) : Prop :=
  ∀ i k : Fin d,
      ∑ x : Fin d × Fin d,
        starRingEnd ℂ (coherentRowState P i x) * coherentRowState P k x =
          if i = k then 1 else 0

end
end QuantumLeanLeap.GoogleQHL.Bench36.OrthonormalityCoherentMarkovChainRows
