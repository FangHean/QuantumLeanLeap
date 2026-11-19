import QuantumLeanLeap.GoogleQHL.Circuits.Dynamic
import QuantumLeanLeap.GoogleQHL.Examples
import QuantumLeanLeap.GoogleQHL.CostLimits

/-! Semantic regression theorems: measurement normalization, a real measured
feedback reset, loss of mass through divergence, and costs paid before abort. -/
namespace QuantumLeanLeap.GoogleQHL.Regression
open scoped ComplexOrder MatrixOrder
open Matrix
open Examples (Var)

def xGate : Unitary 2 where
  matrix := !![0, 1; 1, 0]
  left_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  right_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def measuredReset : QProg Var 2 :=
  .seq (.measure .outcome 2 (Circuits.wireMeasurement (n := 1) 0))
    (.qif (fun s => decide (s .outcome = 0)) .skip (.apply xGate))

/-- Both measured histories are retained; their quantum states add to a reset
of the entire original trace, including mixed inputs with off-diagonal terms. -/
theorem measuredReset_quantum_output (fuel : Nat) (s : Store Var) (rho : Operator 2) :
    ((interpApprox measuredReset fuel (s, rho)).map Prod.snd).sum = resetState 0 rho := by
  have hf : List.finRange 2 = [0, 1] := rfl
  simp only [measuredReset, interpApprox, hf, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Circuits.wireMeasurement, Circuits.wireProjector, conjugate, xGate,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      resetState, Matrix.single, Matrix.trace, Matrix.diagonal, Matrix.of_apply,
      Matrix.vecMul, dotProduct]

theorem measurement_preserves_mass {V : Type} [DecidableEq V] {d outcomes : Nat}
    (v : V) (M : Measurement d outcomes)
    (hcomplete : (∑ o, Matrix.conjTranspose (M.kraus o) * M.kraus o) = 1)
    (fuel : Nat) (input : Branch V d) :
    branchMass (interpApprox (.measure v outcomes M) fuel input) = input.2.trace.re := by
  unfold branchMass
  rw [expect_wpApprox]
  simp only [wpApprox, Matrix.mul_one, hcomplete, pairing_one]

def diverge : QProg Var 2 := .qwhile (fun _ => true) (.apply (Unitary.identity 2))

theorem identity_step (fuel : Nat) (input : Branch Var 2) :
    interpApprox (.apply (Unitary.identity 2)) fuel input = [input] := by
  cases input
  simp [interpApprox, conjugate, Unitary.identity]

theorem diverge_output (fuel : Nat) (input : Branch Var 2) :
    interpApprox diverge fuel input = [] := by
  induction fuel generalizing input with
  | zero => rfl
  | succ k ih =>
      change interpApprox (.qwhile (fun _ => true) (.apply (Unitary.identity 2))) (k + 1) input = []
      rw [interpApprox_while_succ, identity_step]
      simpa [diverge] using ih input

theorem diverge_expectation (Q : CQPredicate Var 2) (input : Branch Var 2) :
    limitExpectation diverge Q input = 0 := by
  simp [limitExpectation, diverge_output]

def gateCost : CostModel 2 where
  assignmentCost := 0
  resetCost := 0
  unitaryCost := fun _ => 1
  measurementCost := fun _ => 0

theorem diverge_prefix_cost (fuel : Nat) (input : Branch Var 2) :
    expectedCostApprox gateCost diverge fuel input = (fuel : Real) * input.2.trace.re := by
  induction fuel generalizing input with
  | zero => simp [diverge, expectedCostApprox]
  | succ k ih =>
      change expectedCostApprox gateCost (.qwhile (fun _ => true) (.apply (Unitary.identity 2)))
        (k + 1) input = _
      rw [expectedCostApprox_while_succ, identity_step]
      simp only [if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      change (↑(1 : Nat) : Real) * input.2.trace.re + (expectedCostApprox gateCost diverge k input + 0) = _
      rw [ih]
      push_cast
      ring

theorem cost_before_abort (fuel : Nat) (input : Branch Var 2) :
    expectedCostApprox gateCost (.seq (.apply (Unitary.identity 2)) .abort) fuel input =
      input.2.trace.re := by
  simp [expectedCostApprox, interpApprox, gateCost]

theorem diverge_infinite_cost (input : Branch Var 2) (htrace : input.2.trace.re = 1) :
    prefixCostSup gateCost diverge input = ⊤ := by
  simp [prefixCostSup, diverge_prefix_cost, htrace, ENNReal.iSup_natCast]

def branchCounts : Circuits.DynamicCircuit Var 2 :=
  .branch (fun s => decide (s .outcome = 0))
    (.gate (.t 0)) (.seq (.gate (.t 0)) (.gate (.t 1)))

theorem branch_uses_max : branchCounts.gateCount .t = 2 := rfl

theorem swap_source_vs_native :
    (Circuits.DynamicCircuit.gate (.swap (0 : Fin 2) 1 (by decide)) :
      Circuits.DynamicCircuit Var 2).gateCount .swap = 1 ∧
    (Circuits.PrimitiveGate.swap (0 : Fin 2) 1 (by decide)).native.eventTrace.length = 3 :=
  ⟨rfl, Circuits.PrimitiveGate.native_trace_length _⟩

end QuantumLeanLeap.GoogleQHL.Regression
