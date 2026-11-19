import QuantumLeanLeap.GoogleQHL.Circuits.Dynamic

namespace QuantumLeanLeap.GoogleQHL.Circuits

/-- Worst-path number of X/Z matrix-gate applications. Measurement is counted separately. -/
def DynamicCircuit.worstMatrixGates {Var : Type} {n : Nat} : DynamicCircuit Var n → Nat
  | .skip => 0
  | .gate g => g.matrixGateCount
  | .measure .. => 0
  | .seq a b => a.worstMatrixGates + b.worstMatrixGates
  | .branch _ a b => max a.worstMatrixGates b.worstMatrixGates

theorem DynamicCircuit.worstMatrixGates_gate {Var : Type} {n : Nat} (g : PrimitiveGate n) :
    (DynamicCircuit.gate g : DynamicCircuit Var n).worstMatrixGates = 1 := rfl

def matrixWeight : GateKind → Nat := fun _ => 1

theorem DynamicCircuit.worstMatrixGates_eq_weighted {Var : Type} {n : Nat}
    (c : DynamicCircuit Var n) : c.worstMatrixGates = c.worstGates matrixWeight := by
  induction c with
  | skip => rfl
  | gate g => cases g <;> rfl
  | measure v q => rfl
  | seq a b iha ihb => simp only [worstMatrixGates, worstGates, iha, ihb]
  | branch g a b iha ihb => simp only [worstMatrixGates, worstGates, iha, ihb]

end QuantumLeanLeap.GoogleQHL.Circuits
