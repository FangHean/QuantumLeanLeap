import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.PostMeasurementStateObservedQubit.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.PostMeasurementStateObservedQubit
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {Y : Type*} [Fintype Y]
    (ψ : Fin 2 × Y → ℂ)
    (h_normalized : ∑ x : Fin 2 × Y, Complex.normSq (ψ x) = 1) : Prop :=
  outcomeProbability ψ 1 = ∑ y : Y, Complex.normSq (ψ (1, y)) ∧

    (0 < outcomeProbability ψ 1 →
      ∀ y : Y,
        postMeasState ψ 1 (1, y) =
          (↑(Real.sqrt (outcomeProbability ψ 1))⁻¹ : ℂ) * ψ (1, y) ∧
        postMeasState ψ 1 (0, y) = 0)

end
end QuantumLeanLeap.GoogleQHL.Bench36.PostMeasurementStateObservedQubit
