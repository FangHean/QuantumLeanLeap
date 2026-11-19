import QuantumLeanLeap.GoogleQHL.Basic
import QuantumAlg.Components.Gates.Construction
import QuantumAlg.Components.Gates.Operator
import QuantumAlg.Components.Gates.Swap.Physical
import QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-! A closed nine-gate source language. Wire numbers use QuantumAlg's
big-endian physical convention. SWAP is one SOURCE occurrence and expands
to three CNOTs in the native backend; these counts are kept distinct. -/
namespace QuantumLeanLeap.GoogleQHL.Circuits
open QuantumAlg
open scoped ComplexOrder MatrixOrder

inductive GateKind where
  | h | x | y | z | s | t | cx | swap | toff
  deriving DecidableEq, Repr

inductive PrimitiveGate (n : Nat) where
  | h (target : Fin n)
  | x (target : Fin n)
  | y (target : Fin n)
  | z (target : Fin n)
  | s (target : Fin n)
  | t (target : Fin n)
  | cx (control target : Fin n) (distinct : control ≠ target)
  | swap (left right : Fin n) (distinct : left ≠ right)
  | toff (a b target : Fin n) (ab : a ≠ b) (aTarget : a ≠ target) (bt : b ≠ target)

def PrimitiveGate.kind {n : Nat} : PrimitiveGate n → GateKind
  | .h _ => .h | .x _ => .x | .y _ => .y | .z _ => .z
  | .s _ => .s | .t _ => .t | .cx .. => .cx | .swap .. => .swap | .toff .. => .toff

abbrev layout (n : Nat) := (QuantumSignature.qubits n).canonicalPlacement.layout

noncomputable def PrimitiveGate.native {n : Nat} : PrimitiveGate n →
    UnitaryCircuit AlgorithmGate.model .empty (layout n)
  | .h q => Gate.singleQubitAt (layout n) .empty Gate.HOp q rfl
  | .x q => Gate.singleQubitAt (layout n) .empty Gate.XOp q rfl
  | .y q => Gate.singleQubitAt (layout n) .empty Gate.YOp q rfl
  | .z q => Gate.singleQubitAt (layout n) .empty Gate.ZOp q rfl
  | .s q => Gate.singleQubitAt (layout n) .empty Gate.SOp q rfl
  | .t q => Gate.singleQubitAt (layout n) .empty Gate.TOp q rfl
  | .cx c target distinct => Gate.cnotAt (layout n) .empty c target distinct rfl rfl
  | .swap a b distinct => Gate.Swap.circuitAt (layout n) a b distinct rfl rfl .empty
  | .toff a b target hab hat hbt => Gate.toffoliAt (layout n) .empty a b target hab hat hbt rfl rfl rfl

/-- The QHL operator is the actual native circuit's matrix, with both
unitarity equations inherited from its checked unitary group membership. -/
noncomputable def PrimitiveGate.unitary {n : Nat} (g : PrimitiveGate n) :
    GoogleQHL.Unitary (2 ^ n) where
  matrix := (g.native.binaryMatrix OracleModel.emptyInterpretation).val
  left_inverse := Matrix.mem_unitaryGroup_iff'.mp
    (g.native.binaryMatrix OracleModel.emptyInterpretation).property
  right_inverse := Matrix.mem_unitaryGroup_iff.mp
    (g.native.binaryMatrix OracleModel.emptyInterpretation).property

def PrimitiveGate.nativeCount {n : Nat} : PrimitiveGate n → Nat
  | .swap .. => 3
  | _ => 1

theorem PrimitiveGate.native_trace_length {n : Nat} (g : PrimitiveGate n) :
    g.native.eventTrace.length = g.nativeCount := by
  cases g <;> rfl

abbrev Circuit (n : Nat) := List (PrimitiveGate n)

noncomputable def Circuit.native {n : Nat} : Circuit n →
    UnitaryCircuit AlgorithmGate.model .empty (layout n)
  | [] => .identity _ _ _
  | g :: rest => g.native.seq (Circuit.native rest)

theorem Circuit.native_trace_length {n : Nat} (c : Circuit n) :
    (Circuit.native c).eventTrace.length = (c.map PrimitiveGate.nativeCount).sum := by
  induction c with
  | nil => rfl
  | cons g rest ih =>
      change (g.native.eventTrace ++ (Circuit.native rest).eventTrace).length = _
      simp only [List.length_append, PrimitiveGate.native_trace_length, ih, List.map_cons, List.sum_cons]

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
