import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.BitOracleUnitaryHermitian.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.BitOracleUnitaryHermitian
set_option linter.unusedVariables false
noncomputable section
variable {n m : ℕ}

def obligation_0 (f : (Fin n → Bool) → (Fin m → Bool)) : Prop :=
  (bitOracle f : Mat (BitReg n m))
      ∈ Matrix.unitaryGroup (BitReg n m) ℂ

def obligation_1 (f : (Fin n → Bool) → (Fin m → Bool)) : Prop :=
  (bitOracle f : Mat (BitReg n m)).conjTranspose
      = (bitOracle f : Mat (BitReg n m))

end
end QuantumLeanLeap.GoogleQHL.Bench36.BitOracleUnitaryHermitian
