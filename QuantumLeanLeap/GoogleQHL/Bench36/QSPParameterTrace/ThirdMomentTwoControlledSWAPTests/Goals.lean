import QuantumLeanLeap.GoogleQHL.Bench36.QSPParameterTrace.ThirdMomentTwoControlledSWAPTests.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ThirdMomentTwoControlledSWAPTests
set_option linter.unusedVariables false
noncomputable section


def obligation_0 {H : Type*} [Fintype H] [DecidableEq H]
    (ρ : Matrix H H ℂ)
    (hρ_sa : ρ.conjTranspose = ρ) (hρ_tr : Matrix.trace ρ = 1) : Prop :=
  Matrix.trace (XXObservable * sigmaOut ρ) =
      Matrix.trace (ρ * ρ * ρ)

end
end QuantumLeanLeap.GoogleQHL.Bench36.ThirdMomentTwoControlledSWAPTests
