import QuantumLeanLeap.GoogleQHL.Bench36.QSPParameterTrace.SharedParameterShiftRuleRXTensorRZ.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.SharedParameterShiftRuleRXTensorRZ
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

variable {K : Type*} [Fintype K] [DecidableEq K]

def obligation_0 (ρ O : Matrix ((Fin 2 × Fin 2) × K) ((Fin 2 × Fin 2) × K) ℂ)
    (hρ_tr : Matrix.trace ρ = 1)
    (hρ_sa : IsSelfAdjoint ρ)
    (hO : IsSelfAdjoint O)
    (θ : ℝ)
    (derivL : ℂ)
    (h_derivL : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ h : ℝ,
      0 < |h| → |h| < δ →
        ‖(loss ρ O (θ + h) - loss ρ O θ) / (↑h : ℂ) - derivL‖ < ε) : Prop :=
  derivL =
      (↑((2 + Real.sqrt 2) / 4 : ℝ) : ℂ) *
        (loss ρ O (θ + Real.pi / 4) - loss ρ O (θ - Real.pi / 4)) +
      (↑((2 - Real.sqrt 2) / 4 : ℝ) : ℂ) *
        (loss ρ O (θ - 3 * Real.pi / 4) - loss ρ O (θ + 3 * Real.pi / 4))

end
end QuantumLeanLeap.GoogleQHL.Bench36.SharedParameterShiftRuleRXTensorRZ
