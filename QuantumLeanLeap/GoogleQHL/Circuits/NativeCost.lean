import QuantumLeanLeap.GoogleQHL.Circuits.Dynamic

namespace QuantumLeanLeap.GoogleQHL.Circuits

/-- Worst-path number of native UNITARY events. Measurement and classical
control are counted separately; SWAP expands to three CNOT events. -/
def DynamicCircuit.worstNativeGates {Var : Type} {n : Nat} : DynamicCircuit Var n → Nat
  | .skip => 0
  | .gate g => g.nativeCount
  | .measure .. => 0
  | .seq a b => a.worstNativeGates + b.worstNativeGates
  | .branch _ a b => max a.worstNativeGates b.worstNativeGates

theorem DynamicCircuit.worstNativeGates_gate {Var : Type} {n : Nat} (g : PrimitiveGate n) :
    (DynamicCircuit.gate g : DynamicCircuit Var n).worstNativeGates = g.native.eventTrace.length :=
  (PrimitiveGate.native_trace_length g).symm

def nativeWeight : GateKind → Nat
  | .swap => 3
  | _ => 1

theorem DynamicCircuit.worstNativeGates_eq_weighted {Var : Type} {n : Nat}
    (c : DynamicCircuit Var n) : c.worstNativeGates = c.worstGates nativeWeight := by
  induction c with
  | skip => rfl
  | gate g => cases g <;> rfl
  | measure v q => rfl
  | seq a b iha ihb => simp only [worstNativeGates, worstGates, iha, ihb]
  | branch g a b iha ihb => simp only [worstNativeGates, worstGates, iha, ihb]

end QuantumLeanLeap.GoogleQHL.Circuits
