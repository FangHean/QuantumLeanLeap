import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.WalshHadamardBooleanCharacter.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.WalshHadamardBooleanCharacter
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n : ℕ}

def obligation_0 (s : Fin n → Bool) : Prop :=
  applyVec hadamardTensorOp (chiState s)
      = (ket (ι := BitReg n) s : Vec (BitReg n))

end
end QuantumLeanLeap.GoogleQHL.Bench36.WalshHadamardBooleanCharacter
