import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.HilbertSchmidtTranspositionInvariance.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.HilbertSchmidtTranspositionInvariance
set_option linter.unusedVariables false
noncomputable section


def obligation_0 {d : ℕ}
    (U V : Operator d) : Prop :=
  hsInner U.transpose V.transpose = hsInner U V ∧

    hsNorm (U.transpose - V.transpose) = hsNorm (U - V)

end
end QuantumLeanLeap.GoogleQHL.Bench36.HilbertSchmidtTranspositionInvariance
