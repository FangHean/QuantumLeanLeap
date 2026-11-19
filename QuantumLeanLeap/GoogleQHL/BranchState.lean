import QuantumLeanLeap.GoogleQHL.StateSup

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem pairing_storeDensity_indicator [DecidableEq (Store Var)]
    (outputs : List (Branch Var d)) (s : Store Var) (E : Operator d) :
    pairing E (storeDensity outputs s) =
      branchExpectation (fun t => if t = s then E else 0) outputs := by
  classical
  induction outputs with
  | nil => simp [storeDensity, pairing]
  | cons b rest ih =>
      simp only [storeDensity, List.map_cons, List.sum_cons, branchExpectation_cons] at ih ⊢
      by_cases he : b.1 = s
      · simpa [he, pairing, Matrix.mul_add, Matrix.trace_add] using congrArg (pairing E b.2 + ·) ih
      · simpa [he, Ne.symm he, pairing, Matrix.mul_add, Matrix.trace_add] using ih

theorem interpApprox_store_mono [DecidableEq Var] (p : QProg Var d) (input : Branch Var d)
    (hr : input.2.PosSemidef) (s : Store Var) :
    Monotone (fun k => storeDensity (interpApprox p k input) s) := by
  classical
  apply monotone_nat_of_le_succ
  intro k
  apply le_of_pairing_le
    (storeDensity_positive _ (interpApprox_positive p k input hr) s).isHermitian
    (storeDensity_positive _ (interpApprox_positive p (k + 1) input hr) s).isHermitian
  intro E hE
  rw [pairing_comm _ E, pairing_comm _ E]
  rw [pairing_storeDensity_indicator, pairing_storeDensity_indicator, expect_wpApprox, expect_wpApprox]
  apply pairing_mono _ hr
  apply wpApprox_fuel_step_nonneg
  intro t
  split <;> [exact hE.nonneg; exact le_rfl]

def singleState (s : Store Var) (rho : PartialDensity d) : FiniteState Var d where
  branches := [(s, rho.matrix)]
  positive := by intro b hb; simpa using (List.mem_singleton.mp hb) ▸ rho.positive
  mass_le_one := by simpa [branchMass] using rho.trace_le_one

noncomputable def approxBranchState [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (s : Store Var) (rho : PartialDensity d) : CQState Var d :=
  (interpFinite p fuel (singleState s rho)).toCQState

theorem approxBranchState_density [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (s t : Store Var) (rho : PartialDensity d) :
    ((approxBranchState p fuel s rho).density t).matrix = storeDensity (interpApprox p fuel (s, rho.matrix)) t := by
  simp [approxBranchState, interpFinite, singleState, FiniteState.toCQState]

theorem approxBranchState_mass_le [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (s : Store Var) (rho : PartialDensity d) : (approxBranchState p fuel s rho).mass ≤ rho.matrix.trace.re := by
  simpa [approxBranchState, interpFinite, singleState, FiniteState.toCQState] using
    interpApprox_trace_nonincreasing p fuel (s, rho.matrix) rho.positive

theorem approxBranchState_mono [DecidableEq Var] (p : QProg Var d) (s : Store Var)
    (rho : PartialDensity d) : ∀ t, Monotone (fun k => ((approxBranchState p k s rho).density t).matrix) := by
  intro t
  simpa only [approxBranchState_density] using interpApprox_store_mono p (s, rho.matrix) rho.positive t

/-- Actual unbounded output state for a classical store and a partial density,
constructed from forward finite executions, before referring to `wp`. -/
noncomputable def interpBranch [DecidableEq Var] (p : QProg Var d) (s : Store Var)
    (rho : PartialDensity d) : CQState Var d :=
  stateSup (fun k => approxBranchState p k s rho) (approxBranchState_mono p s rho)

theorem interpBranch_mass_le [DecidableEq Var] (p : QProg Var d) (s : Store Var)
    (rho : PartialDensity d) : (interpBranch p s rho).mass ≤ rho.matrix.trace.re :=
  (densitySup_trace_summable_bound _ _ _ (fun k => approxBranchState_mass_le p k s rho)).2

theorem expect_interpBranch [DecidableEq Var] (p : QProg Var d) (s : Store Var)
    (rho : PartialDensity d) (Q : CQAssertion Var d) :
    expectation (interpBranch p s rho) Q = limitExpectation p Q.toPredicate (s, rho.matrix) := by
  rw [interpBranch, expectation_stateSup]
  unfold limitExpectation
  congr 1
  funext k
  rw [approxBranchState, FiniteState.expectation_toCQState]
  simp [interpFinite, singleState]

end QuantumLeanLeap.GoogleQHL
