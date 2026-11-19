import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.SpectralProjectorsBooleanPhaseOracle.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.SpectralProjectorsBooleanPhaseOracle
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {n : ℕ}
    (f : (Fin n → Bool) → Bool) : Prop :=
  piPlus f * piPlus f = piPlus f ∧
    piMinus f * piMinus f = piMinus f ∧
    piPlus f * piMinus f = 0 ∧
    piMinus f * piPlus f = 0 ∧
    piPlus f + piMinus f = 1 ∧

    phaseOracle f * piPlus f = piPlus f ∧

    phaseOracle f * piMinus f = -piMinus f ∧

    Matrix.trace (phaseOracle f) =
      (2 : ℂ) ^ n - 2 * ↑(preimageOneCard f)

end
end QuantumLeanLeap.GoogleQHL.Bench36.SpectralProjectorsBooleanPhaseOracle
