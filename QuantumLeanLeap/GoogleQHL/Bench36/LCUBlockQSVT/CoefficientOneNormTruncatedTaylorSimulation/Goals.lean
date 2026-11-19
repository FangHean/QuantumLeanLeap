import QuantumLeanLeap.GoogleQHL.Bench36.LCUBlockQSVT.CoefficientOneNormTruncatedTaylorSimulation.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.CoefficientOneNormTruncatedTaylorSimulation
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {J : Type*} [Fintype J] {d : ℕ}
    (K : ℕ) (β : J → ℝ) (t : ℝ)
    (P : J → Operator d)
    (Pphase : (k : ℕ) → (Fin k → J) → Operator d)
    (hβ_pos : ∀ j : J, 0 < β j)
    (ht_nonneg : 0 ≤ t)
    (hP_pauli : ∀ j : J, IsPauliUnitary (P j))
    (hPphase_unitary : ∀ (k : ℕ) (js : Fin k → J),
      Pphase k js ∈ Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  coeffOneNorm K β t ≤ Real.exp (t * ∑ j : J, β j) ∧

      rawLCUSegmentCount K β t ≤
        Nat.ceil (Real.exp (t * ∑ j : J, β j)) ∧

      ∃ C : ℝ, 0 ≤ C ∧
        (rawLCUSegmentCount K β t : ℝ) ≤ C * (t * ∑ j : J, β j + 1)

end
end QuantumLeanLeap.GoogleQHL.Bench36.CoefficientOneNormTruncatedTaylorSimulation
