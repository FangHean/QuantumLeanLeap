import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.ControlledUnitaryInvariantSubspaces.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ControlledUnitaryInvariantSubspaces
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n : ℕ}

def obligation_0 (U : Unitary (2 ^ n)) (x : ℝ) (ψ : Vec (Fin (2 ^ n)))
    (h_eigen : applyVec U.matrix ψ = Complex.exp (x * Complex.I) • ψ) : Prop :=
  applyVec (controlled U.matrix : Operator (2 ^ (1 + n)))
        (tensorVec (ket0 : Vec (Fin (2 ^ 1))) ψ)
      = tensorVec (ket0 : Vec (Fin (2 ^ 1))) ψ
    ∧
    applyVec (controlled U.matrix : Operator (2 ^ (1 + n)))
        (tensorVec (ket1 : Vec (Fin (2 ^ 1))) ψ)
      = Complex.exp (x * Complex.I) •
        tensorVec (ket1 : Vec (Fin (2 ^ 1))) ψ

end
end QuantumLeanLeap.GoogleQHL.Bench36.ControlledUnitaryInvariantSubspaces
