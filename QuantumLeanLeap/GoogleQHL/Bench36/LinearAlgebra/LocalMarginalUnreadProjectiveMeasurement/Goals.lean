import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.LocalMarginalUnreadProjectiveMeasurement.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.LocalMarginalUnreadProjectiveMeasurement
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 (ρ : Matrix Bipartite Bipartite ℂ)
    (ρA : Qubit → Qubit → Matrix Qubit Qubit ℂ)
    (_hρ_density : IsHermitianTraceOne ρ)
    (hblock : ρ = blockExpansion ρA) : Prop :=
  postMeasurement ρ = diagonalBlockState ρA ∧

    partialTraceB (postMeasurement ρ) = partialTraceB ρ

end
end QuantumLeanLeap.GoogleQHL.Bench36.LocalMarginalUnreadProjectiveMeasurement
