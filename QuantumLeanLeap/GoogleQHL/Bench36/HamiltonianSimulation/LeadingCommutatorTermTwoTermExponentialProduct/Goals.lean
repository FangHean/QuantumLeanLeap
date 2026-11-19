import QuantumLeanLeap.GoogleQHL.Bench36.HamiltonianSimulation.LeadingCommutatorTermTwoTermExponentialProduct.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.LeadingCommutatorTermTwoTermExponentialProduct
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0  : Prop :=
  ∃ C B : ℝ,
      0 ≤ C ∧ 0 ≤ B ∧
        ∀ (d : ℕ)
          (opnorm : Operator d → ℝ)
          (expm : Operator d → Operator d)
          (H1 H2 : Operator d)
          (γ : ℝ),
          opnorm 0 = 0 →
          (∀ A, 0 ≤ opnorm A) →
          (∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B) →
          (∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B) →
          (∀ (a : ℂ) (X : Operator d), opnorm (a • X) ≤ ‖a‖ * opnorm X) →
          opnorm 1 ≤ 1 →
          expm 0 = 1 →
          (∀ H : Operator d,
              opnorm H ≤ 2 →
                opnorm (expm H - (1 + H + ((1 / 2 : ℂ) • (H * H)))) ≤
                  B * opnorm H ^ 3) →
          0 ≤ γ →
            γ < 1 →
              opnorm H1 ≤ γ →
                opnorm H2 ≤ γ →
                  opnorm (E12 expm H1 H2 - ((1 / 2 : ℂ) • commutator H1 H2)) ≤
                    C * γ ^ 3

end
end QuantumLeanLeap.GoogleQHL.Bench36.LeadingCommutatorTermTwoTermExponentialProduct
