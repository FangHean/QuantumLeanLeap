import QuantumLeanLeap.GoogleQHL.Expectation

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem resetState_positive (i : Fin d) {rho : Operator d} (h : rho.PosSemidef) :
    (resetState i rho).PosSemidef := by
  have eqdiag : resetState i rho = Matrix.diagonal (fun j => if j = i then rho.trace else 0) := by
    ext a b
    by_cases ha : a = i <;> by_cases hb : b = i <;>
      simp [resetState, Matrix.single, Matrix.diagonal, ha, hb] <;> aesop
  rw [eqdiag]
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp only
  split <;> [exact h.trace_nonneg; exact le_rfl]

/-- Every emitted measurement history is a positive (unnormalized) state. -/
theorem interpApprox_positive [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (input : Branch Var d) (hinput : input.2.PosSemidef) :
    ∀ output ∈ interpApprox p fuel input, output.2.PosSemidef := by
  induction p generalizing fuel input with
  | skip => simpa [interpApprox] using hinput
  | abort => simp [interpApprox]
  | assign v e => rcases input with ⟨s, r⟩; simpa [interpApprox] using hinput
  | qset i => rcases input with ⟨s, r⟩; simpa [interpApprox] using resetState_positive i hinput
  | apply U => rcases input with ⟨s, r⟩; simpa [interpApprox, conjugate] using hinput.mul_mul_conjTranspose_same U.matrix
  | measure v n M =>
      rcases input with ⟨s, r⟩
      intro output hout
      obtain ⟨o, _, rfl⟩ := List.mem_map.mp hout
      exact hinput.mul_mul_conjTranspose_same (M.kraus o)
  | seq a b iha ihb =>
      intro output hout
      obtain ⟨mid, hmid, hout⟩ := List.mem_flatMap.mp hout
      exact ihb fuel mid (iha fuel input hinput mid hmid) output hout
  | qif g a b iha ihb =>
      simp only [interpApprox]
      split <;> [exact iha fuel input hinput; exact ihb fuel input hinput]
  | qwhile g body ihBody =>
      induction fuel generalizing input with
      | zero => simp
      | succ k ih =>
          rw [interpApprox_while_succ]
          split
          · intro output hout
            obtain ⟨mid, hmid, hout⟩ := List.mem_flatMap.mp hout
            exact ih mid (ihBody k input hinput mid hmid) output hout
          · simpa using hinput

def branchMass (outputs : List (Branch Var d)) : Real :=
  branchExpectation (fun _ => 1) outputs

theorem interpApprox_trace_nonincreasing [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (input : Branch Var d) (h : input.2.PosSemidef) :
    branchMass (interpApprox p fuel input) ≤ input.2.trace.re :=
  (interpApprox_expectation_bounds p fuel (fun _ => 1)
    (fun _ => ⟨Matrix.PosSemidef.one.nonneg, le_rfl⟩) input.1 input.2 h).2

/-- Finite-history representation, allowing duplicate classical stores. -/
structure FiniteState (Var : Type) (d : Nat) where
  branches : List (Branch Var d)
  positive : ∀ b ∈ branches, b.2.PosSemidef
  mass_le_one : branchMass branches ≤ 1

def interpFinite [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (input : FiniteState Var d) : FiniteState Var d where
  branches := input.branches.flatMap (interpApprox p fuel)
  positive := by
    intro output hout
    obtain ⟨b, hb, hout⟩ := List.mem_flatMap.mp hout
    exact interpApprox_positive p fuel b (input.positive b hb) output hout
  mass_le_one := by
    apply le_trans _ input.mass_le_one
    unfold branchMass
    rw [branchExpectation_flatMap, branchExpectation_eq_sum]
    apply List.sum_le_sum
    intro b hb
    simpa [branchMass] using interpApprox_trace_nonincreasing p fuel b (input.positive b hb)

end QuantumLeanLeap.GoogleQHL
