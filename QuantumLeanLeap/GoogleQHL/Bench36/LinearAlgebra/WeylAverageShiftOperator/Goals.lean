import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.WeylAverageShiftOperator.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.WeylAverageShiftOperator
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {d : ℕ} [NeZero d] (hd : 2 ≤ d) : Prop :=
  (clockZ : Operator d) * shiftX =
      omega d • (shiftX * clockZ) ∧

    weylAverage (shiftX : Operator d) = shiftX ∧

    (shiftX : Operator d).transpose =
      (shiftX : Operator d).conjTranspose ∧

    (shiftX : Operator d).conjTranspose =
      shiftX ^ (d - 1) ∧

    (shiftX : Operator d) *
      (shiftX : Operator d).conjTranspose = 1 ∧
    (shiftX : Operator d).conjTranspose *
      (shiftX : Operator d) = 1 ∧

    (2 < d →
      ¬∀ U : Operator d,
        weylAverage U = U.transpose)

end
end QuantumLeanLeap.GoogleQHL.Bench36.WeylAverageShiftOperator
