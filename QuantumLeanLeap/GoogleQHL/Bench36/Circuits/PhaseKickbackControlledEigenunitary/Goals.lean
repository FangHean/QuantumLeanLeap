import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.PhaseKickbackControlledEigenunitary.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.PhaseKickbackControlledEigenunitary
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n : ℕ}

def obligation_0 (U : Unitary (2 ^ n)) (θ : ℝ)
    (ψ : Vec (Fin (2 ^ n)))
    (hψ_normalized : ‖ψ‖ = 1)
    (h_eigen : applyVec U.matrix (ψ : Vec (Fin (2 ^ n)))
      = Complex.exp (θ * Complex.I) • (ψ : Vec (Fin (2 ^ n))))
    (α β : ℂ) : Prop :=
  applyVec (controlled U.matrix : Operator (2 ^ (1 + n)))
        (tensorVec
          (α • (ket0 : Vec (Fin (2 ^ 1))) + β • (ket1 : Vec (Fin (2 ^ 1))))
          (ψ : Vec (Fin (2 ^ n))))
      = tensorVec
          (α • (ket0 : Vec (Fin (2 ^ 1))) +
           (β * Complex.exp (θ * Complex.I)) • (ket1 : Vec (Fin (2 ^ 1))))
          (ψ : Vec (Fin (2 ^ n)))

end
end QuantumLeanLeap.GoogleQHL.Bench36.PhaseKickbackControlledEigenunitary
