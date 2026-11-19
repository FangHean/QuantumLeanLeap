import QuantumLeanLeap.GoogleQHL.Basic

/-! Independent matrix semantics for the closed one-qubit X/Z fragment used by
our feedback-reset benchmark. This is not a general native gate compiler.
Projective measurements below support arbitrary finite qubit registers. -/
namespace QuantumLeanLeap.GoogleQHL.Circuits
open scoped ComplexOrder MatrixOrder

inductive GateKind where
  | x | z
  deriving DecidableEq, Repr

/-- Only one-qubit gates are implemented in this concrete fragment. -/
inductive PrimitiveGate : Nat → Type where
  | x (target : Fin 1) : PrimitiveGate 1
  | z (target : Fin 1) : PrimitiveGate 1

def PrimitiveGate.kind {n : Nat} : PrimitiveGate n → GateKind
  | .x _ => .x | .z _ => .z

def xUnitary : GoogleQHL.Unitary 2 where
  matrix := !![0, 1; 1, 0]
  left_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  right_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def zUnitary : GoogleQHL.Unitary 2 where
  matrix := !![1, 0; 0, -1]
  left_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  right_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def PrimitiveGate.unitary {n : Nat} : PrimitiveGate n → GoogleQHL.Unitary (2 ^ n)
  | .x _ => xUnitary
  | .z _ => zUnitary

def PrimitiveGate.matrixGateCount {n : Nat} (_ : PrimitiveGate n) : Nat := 1

/-- Computational-basis projectors for a physical qubit. -/
def wireProjector {n : Nat} (wire : Fin n) (outcome : Fin 2) : Operator (2 ^ n) :=
  Matrix.diagonal (fun label =>
    if (label.val.testBit (n - 1 - wire.val)).toNat = outcome.val then 1 else 0)

theorem wireProjector_complete {n : Nat} (wire : Fin n) :
    (∑ o : Fin 2, Matrix.conjTranspose (wireProjector wire o) * wireProjector wire o) = 1 := by
  simp only [wireProjector, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Fin.sum_univ_two]
  ext i j
  by_cases hij : i = j
  · subst j
    cases h : i.val.testBit (n - 1 - wire.val) <;> simp [Matrix.diagonal, h]
  · simp [Matrix.diagonal, hij]

def wireMeasurement {n : Nat} (wire : Fin n) : Measurement (2 ^ n) 2 where
  kraus := wireProjector wire
  complete := (wireProjector_complete wire).le

end QuantumLeanLeap.GoogleQHL.Circuits
