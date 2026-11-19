import QuantumLeanLeap.GoogleQHL.Composition

/-! Coalescing finite histories into classical--quantum states. Histories
which end in the same store are ADDED, not overwritten. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

noncomputable def storeDensity (outputs : List (Branch Var d)) (s : Store Var) : Operator d := by
  classical
  exact (outputs.map (fun b => if s = b.1 then b.2 else 0)).sum

theorem storeDensity_positive (outputs : List (Branch Var d))
    (h : ∀ b ∈ outputs, b.2.PosSemidef) (s : Store Var) : (storeDensity outputs s).PosSemidef := by
  classical
  induction outputs with
  | nil => simp [storeDensity, Matrix.PosSemidef.zero]
  | cons b rest ih =>
      simp only [storeDensity, List.map_cons, List.sum_cons]
      apply Matrix.PosSemidef.add _ (ih (fun x hx => h x (by simp [hx])))
      split <;> [exact h b (by simp); exact Matrix.PosSemidef.zero]

theorem pairing_storeDensity_hasSum (outputs : List (Branch Var d)) (post : CQPredicate Var d) :
    HasSum (fun s => pairing (post s) (storeDensity outputs s)) (branchExpectation post outputs) := by
  classical
  induction outputs with
  | nil => simp [storeDensity, pairing]
  | cons b rest ih =>
      have hs : HasSum (fun s => pairing (post s) (if s = b.1 then b.2 else 0))
          (pairing (post b.1) b.2) := by
        convert hasSum_ite_eq b.1 (pairing (post b.1) b.2) using 1
        ext s
        by_cases he : s = b.1 <;> simp [he, pairing]
      simpa [storeDensity, pairing, Matrix.mul_add, Matrix.trace_add, branchExpectation] using hs.add ih

theorem storeDensity_trace_hasSum (outputs : List (Branch Var d)) :
    HasSum (fun s => (storeDensity outputs s).trace.re) (branchMass outputs) := by
  simpa only [pairing_one, branchMass] using pairing_storeDensity_hasSum outputs (fun _ => 1)

noncomputable def FiniteState.toCQState (state : FiniteState Var d) : CQState Var d where
  density s := {
    matrix := storeDensity state.branches s
    positive := storeDensity_positive state.branches state.positive s
    trace_le_one := by
      apply le_trans _ state.mass_le_one
      have hs := storeDensity_trace_hasSum state.branches
      rw [← hs.tsum_eq]
      exact hs.summable.le_tsum s (fun t _ =>
        (RCLike.nonneg_iff.mp (storeDensity_positive state.branches state.positive t).trace_nonneg).1) }
  mass := branchMass state.branches
  trace_hasSum := storeDensity_trace_hasSum state.branches
  mass_le_one := state.mass_le_one

theorem FiniteState.expectation_toCQState (state : FiniteState Var d) (Q : CQAssertion Var d) :
    expectation state.toCQState Q = branchExpectation Q.toPredicate state.branches :=
  (pairing_storeDensity_hasSum state.branches Q.toPredicate).tsum_eq

/-- Exact forward/backward duality on bundled states, for finite executions
and finitely supported input histories. -/
theorem expect_interpFinite [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (state : FiniteState Var d) (Q : CQAssertion Var d) :
    expectation (interpFinite p fuel state).toCQState Q =
      expectation state.toCQState (wpBounded p fuel Q) := by
  rw [FiniteState.expectation_toCQState, FiniteState.expectation_toCQState]
  change branchExpectation Q.toPredicate (state.branches.flatMap (interpApprox p fuel)) = _
  rw [branchExpectation_flatMap, branchExpectation_eq_sum]
  congr 1
  apply List.map_congr_left
  intro b _
  exact expect_wpApprox p fuel Q.toPredicate b

/-- Forward expectation for an arbitrary summable input CQ-state.
`Denotational.lean` constructs the output CQState and proves this agrees
with its expectation. -/
noncomputable def operationalExpectation [DecidableEq Var] (p : QProg Var d)
    (state : CQState Var d) (Q : CQAssertion Var d) : Real :=
  ∑' s, limitExpectation p Q.toPredicate (s, (state.density s).matrix)

theorem operationalExpectation_eq [DecidableEq Var] (p : QProg Var d)
    (state : CQState Var d) (Q : CQAssertion Var d) :
    operationalExpectation p state Q = expectation state (wp p Q) := by
  apply tsum_congr
  intro s
  exact expect_wp p Q (s, (state.density s).matrix) (state.density s).positive

theorem operationalExpectation_summable [DecidableEq Var] (p : QProg Var d)
    (state : CQState Var d) (Q : CQAssertion Var d) :
    Summable (fun s => limitExpectation p Q.toPredicate (s, (state.density s).matrix)) := by
  simpa only [fun s => expect_wp p Q (s, (state.density s).matrix) (state.density s).positive] using
    expectation_summable state (wp p Q)

end QuantumLeanLeap.GoogleQHL
