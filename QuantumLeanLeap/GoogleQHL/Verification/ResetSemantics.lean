import QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
import QuantumLeanLeap.GoogleQHL.Circuits.GateCost

/-! Independent X/Z matrix semantics, measured histories and gate budgets. -/
namespace QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
open Circuits
open scoped ComplexOrder MatrixOrder

theorem matrix_x_matrix : (PrimitiveGate.x (0 : Fin 1)).unitary.matrix = xUnitary.matrix := rfl

theorem matrix_z_matrix : (PrimitiveGate.z (0 : Fin 1)).unitary.matrix = zUnitary.matrix := rfl

private theorem unitary_eq_of_matrix_eq {d : Nat} {a b : GoogleQHL.Unitary d}
    (h : a.matrix = b.matrix) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem matrix_x_unitary : (PrimitiveGate.x (0 : Fin 1)).unitary = xUnitary :=
  unitary_eq_of_matrix_eq matrix_x_matrix

theorem matrix_z_unitary : (PrimitiveGate.z (0 : Fin 1)).unitary = zUnitary :=
  unitary_eq_of_matrix_eq matrix_z_matrix

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
  | x => simp only [toDynamic, DynamicCircuit.compile, compile, matrix_x_unitary]
  | z => simp only [toDynamic, DynamicCircuit.compile, compile, matrix_z_unitary]
  | measure => rfl
  | seq a b iha ihb => simp only [toDynamic, DynamicCircuit.compile, compile, iha, ihb]
  | ifZero a b iha ihb => simp only [toDynamic, DynamicCircuit.compile, compile, iha, ihb]

/-- Equality of every measurement history, including its classical store. -/
theorem Program.toDynamic_run (p : Program) (fuel : Nat) (input : Branch Unit 2) :
    p.toDynamic.run input = interpApprox p.compile fuel input := by
  rw [← DynamicCircuit.compile_correct p.toDynamic fuel input, p.toDynamic_compile]

theorem Program.matrix_contract (p : Program) (h : ResetSpec.Contract p.compile) :
    ResetSpec.Contract p.toDynamic.compile := by
  rw [p.toDynamic_compile]
  exact h

theorem Program.matrix_output (p : Program) (h : ResetSpec.Contract p.compile)
    (s : Store Unit) (rho : Operator 2) :
    ((p.toDynamic.run (s, rho)).map Prod.snd).sum = resetState 0 rho := by
  rw [p.toDynamic_run 0]
  exact h.1 0 s rho

theorem Program.matrix_count (p : Program) (fuel : Nat) :
    p.toDynamic.worstMatrixGates = worstCost ResetSpec.gateCost p.compile fuel := by
  induction p with
  | skip => rfl
  | x => rfl
  | z => rfl
  | measure => rfl
  | seq a b iha ihb =>
      simp only [toDynamic, DynamicCircuit.worstMatrixGates, compile, worstCost, iha, ihb]
  | ifZero a b iha ihb =>
      simp only [toDynamic, DynamicCircuit.worstMatrixGates, compile, worstCost, iha, ihb]

theorem Program.matrix_gate_budget (p : Program) (h : ResetSpec.Contract p.compile) :
    p.toDynamic.worstMatrixGates ≤ 1 := by
  rw [p.matrix_count 0]
  exact h.2.1 0

theorem Program.matrix_expected_gate_bound (p : Program) (h : ResetSpec.Contract p.compile)
    (input : Branch Unit 2) (hr : input.2.PosSemidef) :
    p.toDynamic.runCost matrixWeight input ≤ input.2.trace.re := by
  have ht : 0 ≤ input.2.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
  have hc := p.toDynamic.runCost_le matrixWeight input hr
  rw [← DynamicCircuit.worstMatrixGates_eq_weighted] at hc
  have hb : (p.toDynamic.worstMatrixGates : Real) ≤ 1 := by
    exact_mod_cast p.matrix_gate_budget h
  exact hc.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb ht)

end QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
