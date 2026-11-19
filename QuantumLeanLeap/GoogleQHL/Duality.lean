import QuantumLeanLeap.GoogleQHL.Semantics

namespace QuantumLeanLeap.GoogleQHL
variable {Var : Type} {d : Nat}

theorem pairing_conjugate (E K rho : Operator d) :
    pairing E (conjugate K rho) = pairing (Matrix.conjTranspose K * E * K) rho := by
  unfold pairing conjugate
  congr 1
  calc
    (E * (K * rho * Matrix.conjTranspose K)).trace =
        (E * K * rho * Matrix.conjTranspose K).trace := by simp [Matrix.mul_assoc]
    _ = (Matrix.conjTranspose K * (E * K * rho)).trace := Matrix.trace_mul_comm _ _
    _ = (Matrix.conjTranspose K * E * K * rho).trace := by simp [Matrix.mul_assoc]

theorem pairing_reset (E rho : Operator d) (index : Fin d) :
    pairing E (resetState index rho) =
      pairing (Matrix.scalar (Fin d) (E index index)) rho := by
  unfold pairing resetState
  congr 1
  rw [Matrix.trace_mul_single]
  simp [Matrix.scalar, Matrix.trace, Matrix.mul_apply, Matrix.diagonal,
    Finset.mul_sum, mul_comm]

theorem pairing_sum {α : Type} (s : Finset α) (E : α → Operator d) (rho : Operator d) :
    pairing (∑ a ∈ s, E a) rho = ∑ a ∈ s, pairing (E a) rho := by
  simp [pairing, Matrix.sum_mul, Matrix.trace_sum]

/-- Exact expectation duality for EVERY finite unrolling, including nested
loops, subcomplete measurements, classical assignment and reset. This is a
statement about the independently defined forward branch interpreter. -/
theorem expect_wpApprox [DecidableEq Var] (program : QProg Var d) (fuel : Nat)
    (post : CQPredicate Var d) (input : Branch Var d) :
    branchExpectation post (interpApprox program fuel input) =
      pairing (wpApprox program fuel post input.1) input.2 := by
  induction program generalizing fuel post input with
  | skip => simp [interpApprox, wpApprox]
  | abort => simp [interpApprox, wpApprox, pairing]
  | assign target expr => rcases input with ⟨s, r⟩; simp [interpApprox, wpApprox]
  | qset index => rcases input with ⟨s, r⟩; simp [interpApprox, wpApprox, pairing_reset]
  | apply U => rcases input with ⟨s, r⟩; simp [interpApprox, wpApprox, pairing_conjugate]
  | measure target count M =>
      rcases input with ⟨s, r⟩
      simp only [interpApprox, branchExpectation_map, wpApprox, pairing_sum]
      simp [List.finRange, List.map_ofFn, List.sum_ofFn, pairing_conjugate]
  | seq first second ihFirst ihSecond =>
      simp only [interpApprox, wpApprox, branchExpectation_flatMap]
      simp_rw [ihSecond]
      rw [← branchExpectation_eq_sum]
      exact ihFirst fuel _ input
  | qif g first second ihFirst ihSecond =>
      simp only [interpApprox, wpApprox]
      split <;> [apply ihFirst; apply ihSecond]
  | qwhile g body ihBody =>
      induction fuel generalizing input with
      | zero => simp [interpApprox, wpApprox, pairing]
      | succ k ih =>
          rw [interpApprox_while_succ, wpApprox_while_succ]
          by_cases h : g input.1 = true
          · simp only [h, if_true]
            rw [branchExpectation_flatMap]
            simp_rw [ih]
            rw [← branchExpectation_eq_sum]
            exact ihBody k _ input
          · simp [h]

end QuantumLeanLeap.GoogleQHL
