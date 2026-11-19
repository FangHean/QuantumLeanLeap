import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.HadamardTensorHadamardMatrix.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.HadamardTensorHadamardMatrix
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

def obligation_0  : Prop :=
  (tensorOp (m := 1) (n := 1) H H : Operator (2 ^ 2)) =
      (2⁻¹ : ℂ) • (!![(1 : ℂ), 1, 1, 1;
                        1, -1, 1, -1;
                        1, 1, -1, -1;
                        1, -1, -1, 1] : Operator (2 ^ 2))

def obligation_1  : Prop :=
  tensorOp (m := 1) (n := 1) H H * tensorOp (m := 1) (n := 1) H H = (1 : Operator (2 ^ 2))

end
end QuantumLeanLeap.GoogleQHL.Bench36.HadamardTensorHadamardMatrix
