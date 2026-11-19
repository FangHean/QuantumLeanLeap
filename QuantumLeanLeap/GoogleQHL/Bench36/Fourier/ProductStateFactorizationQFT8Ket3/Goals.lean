import QuantumLeanLeap.GoogleQHL.Bench36.Fourier.ProductStateFactorizationQFT8Ket3.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ProductStateFactorizationQFT8Ket3
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

def obligation_0 (x2 x1 x0 : Fin 2) : Prop :=
  applyVec qft8
      (ket (ι := Fin (2 ^ 3)) 3 : Vec (Fin (2 ^ 3)))
      (bigEndian x2 x1 x0) =
      factor2 x2 * factor1 x1 * factor0 x0

end
end QuantumLeanLeap.GoogleQHL.Bench36.ProductStateFactorizationQFT8Ket3
