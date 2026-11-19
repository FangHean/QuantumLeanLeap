import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.VanishingPauliYExpectationRealCircuits.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.VanishingPauliYExpectationRealCircuits
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n : ℕ}

def obligation_0 (ψ : Vec (Fin (2 ^ n))) (A : Operator (2 ^ n))
    (hψ_real : ∀ i, (ψ i).im = 0)
    (_hA_imag : ∀ i j, (A i j).re = 0)
    (hA_skew : ∀ i j, A j i = -A i j) : Prop :=
  inner ℂ ψ (applyVec A ψ) = 0

def obligation_1 (ψ : Vec (Fin (2 ^ 1)))
    (hψ_real : ∀ i, (ψ i).im = 0) : Prop :=
  inner ℂ ψ (applyVec YOp ψ) = 0

end
end QuantumLeanLeap.GoogleQHL.Bench36.VanishingPauliYExpectationRealCircuits
