import QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
import QuantumLeanLeap.GoogleQHL.Circuits.NativeCost
import QuantumAlg.Components.Gates.SingleQubit.Singleton

/-! The submission language's literal matrices agree with the actual
QuantumAlg native gate backend. Measurements and classical control remain
in the dynamic circuit layer; no unitary encoding of measurement is claimed. -/
namespace QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
open QuantumAlg Circuits
open scoped ComplexOrder MatrixOrder

theorem native_x_matrix : (PrimitiveGate.x (0 : Fin 1)).unitary.matrix = xUnitary.matrix := by
  change ((Gate.singleQubitAt (QuantumSignature.qubits 1).canonicalPlacement.layout
    OracleModel.empty Gate.XOp (0 : Fin 1) rfl).binaryMatrix OracleModel.emptyInterpretation).val = _
  rw [Gate.singleQubitAt_singleton_binaryMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gate.XOp, UnitaryOperator.ofPerm, xUnitary]

theorem native_z_matrix : (PrimitiveGate.z (0 : Fin 1)).unitary.matrix = zUnitary.matrix := by
  change ((Gate.singleQubitAt (QuantumSignature.qubits 1).canonicalPlacement.layout
    OracleModel.empty Gate.ZOp (0 : Fin 1) rfl).binaryMatrix OracleModel.emptyInterpretation).val = _
  rw [Gate.singleQubitAt_singleton_binaryMatrix]
  rfl

private theorem unitary_eq_of_matrix_eq {d : Nat} {a b : GoogleQHL.Unitary d}
    (h : a.matrix = b.matrix) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem native_x_unitary : (PrimitiveGate.x (0 : Fin 1)).unitary = xUnitary :=
  unitary_eq_of_matrix_eq native_x_matrix

theorem native_z_unitary : (PrimitiveGate.z (0 : Fin 1)).unitary = zUnitary :=
  unitary_eq_of_matrix_eq native_z_matrix

def Program.toDynamic : Program → DynamicCircuit Unit 1
  | .skip => .skip
  | .x => .gate (.x 0)
  | .z => .gate (.z 0)
  | .measure => .measure () 0
  | .seq a b => .seq a.toDynamic b.toDynamic
  | .ifZero a b => .branch (fun s => decide (s () = 0)) a.toDynamic b.toDynamic

theorem Program.toDynamic_compile (p : Program) : p.toDynamic.compile = p.compile := by
  induction p with
  | skip => rfl
  | x => simp only [toDynamic, DynamicCircuit.compile, compile, native_x_unitary]
  | z => simp only [toDynamic, DynamicCircuit.compile, compile, native_z_unitary]
  | measure => rfl
  | seq a b iha ihb => simp only [toDynamic, DynamicCircuit.compile, compile, iha, ihb]
  | ifZero a b iha ihb => simp only [toDynamic, DynamicCircuit.compile, compile, iha, ihb]

/-- Equality of every measurement history, including its classical store. -/
theorem Program.toDynamic_run (p : Program) (fuel : Nat) (input : Branch Unit 2) :
    p.toDynamic.run input = interpApprox p.compile fuel input := by
  rw [← DynamicCircuit.compile_correct p.toDynamic fuel input, p.toDynamic_compile]

theorem Program.native_contract (p : Program) (h : ResetSpec.Contract p.compile) :
    ResetSpec.Contract p.toDynamic.compile := by
  rw [p.toDynamic_compile]
  exact h

theorem Program.native_output (p : Program) (h : ResetSpec.Contract p.compile)
    (s : Store Unit) (rho : Operator 2) :
    ((p.toDynamic.run (s, rho)).map Prod.snd).sum = resetState 0 rho := by
  rw [p.toDynamic_run 0]
  exact h.1 0 s rho

theorem Program.native_count (p : Program) (fuel : Nat) :
    p.toDynamic.worstNativeGates = worstCost ResetSpec.gateCost p.compile fuel := by
  induction p with
  | skip => rfl
  | x => rfl
  | z => rfl
  | measure => rfl
  | seq a b iha ihb =>
      simp only [toDynamic, DynamicCircuit.worstNativeGates, compile, worstCost, iha, ihb]
  | ifZero a b iha ihb =>
      simp only [toDynamic, DynamicCircuit.worstNativeGates, compile, worstCost, iha, ihb]

theorem Program.native_gate_budget (p : Program) (h : ResetSpec.Contract p.compile) :
    p.toDynamic.worstNativeGates ≤ 1 := by
  rw [p.native_count 0]
  exact h.2.1 0

theorem Program.native_expected_gate_bound (p : Program) (h : ResetSpec.Contract p.compile)
    (input : Branch Unit 2) (hr : input.2.PosSemidef) :
    p.toDynamic.runCost nativeWeight input ≤ input.2.trace.re := by
  have ht : 0 ≤ input.2.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
  have hc := p.toDynamic.runCost_le nativeWeight input hr
  rw [← DynamicCircuit.worstNativeGates_eq_weighted] at hc
  have hb : (p.toDynamic.worstNativeGates : Real) ≤ 1 := by
    exact_mod_cast p.native_gate_budget h
  exact hc.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb ht)

end QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
