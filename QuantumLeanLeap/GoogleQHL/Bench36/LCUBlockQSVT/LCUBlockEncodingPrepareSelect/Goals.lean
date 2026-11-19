import QuantumLeanLeap.GoogleQHL.Bench36.LCUBlockQSVT.LCUBlockEncodingPrepareSelect.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.LCUBlockEncodingPrepareSelect
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
open scoped BigOperators
variable {a n : ℕ} {L : Type*} [Fintype L] [DecidableEq L]

def obligation_0 (embed : L ↪ Fin (2 ^ a))
    (αcoeff : L → ℝ)
    (U : L → Operator (2 ^ n))
    (P : Unitary (2 ^ a))
    (W : Unitary (2 ^ (a + n)))
    (hαcoeff_pos : ∀ ℓ, 0 < αcoeff ℓ)
    (hU_unitary : ∀ ℓ, U ℓ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)

    (hPrepare : ∀ j : Fin (2 ^ a),
      P.matrix j 0 =
        ((Real.sqrt (coeffSum αcoeff))⁻¹ : ℝ) *
          ∑ ℓ, if embed ℓ = j then (Real.sqrt (αcoeff ℓ) : ℝ) else 0)

    (hW_eq : W.matrix =
      tensorOp P.matrix.conjTranspose
        (1 : Operator (2 ^ n)) *
      selectOp embed U *
      tensorOp P.matrix
        (1 : Operator (2 ^ n))) : Prop :=
  projectedBlock a n W.matrix =
      ((coeffSum αcoeff : ℂ)⁻¹) • weightedSum αcoeff U

def obligation_1 (embed : L ↪ Fin (2 ^ a))
    (αcoeff : L → ℝ)
    (U : L → Operator (2 ^ n))
    (P : Unitary (2 ^ a))
    (W : Unitary (2 ^ (a + n)))
    (hαcoeff_pos : ∀ ℓ, 0 < αcoeff ℓ)
    (hU_unitary : ∀ ℓ, U ℓ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hPrepare : ∀ j : Fin (2 ^ a),
      P.matrix j 0 =
        ((Real.sqrt (coeffSum αcoeff))⁻¹ : ℝ) *
          ∑ ℓ, if embed ℓ = j then (Real.sqrt (αcoeff ℓ) : ℝ) else 0)
    (hW_eq : W.matrix =
      tensorOp P.matrix.conjTranspose
        (1 : Operator (2 ^ n)) *
      selectOp embed U *
      tensorOp P.matrix
        (1 : Operator (2 ^ n))) : Prop :=
  BlockEncoding (coeffSum αcoeff) a n 0 W (weightedSum αcoeff U)

end
end QuantumLeanLeap.GoogleQHL.Bench36.LCUBlockEncodingPrepareSelect
