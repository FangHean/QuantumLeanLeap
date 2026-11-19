import QuantumLeanLeap.GoogleQHL.BranchState
import QuantumLeanLeap.GoogleQHL.StateSum

/-! Forward state semantics for arbitrary summable classical--quantum input
states and unbounded programs. The construction sums actual branch output
states; expectation duality is then proved, not used as the definition. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem interpBranch_mass_summable [DecidableEq Var] (p : QProg Var d) (S : CQState Var d) :
    Summable (fun s => (interpBranch p s (S.density s)).mass) :=
  Summable.of_nonneg_of_le (fun s => (interpBranch p s (S.density s)).mass_nonnegative)
    (fun s => interpBranch_mass_le p s (S.density s)) S.trace_hasSum.summable

theorem interpBranch_total_mass_le [DecidableEq Var] (p : QProg Var d) (S : CQState Var d) :
    (∑' s, (interpBranch p s (S.density s)).mass) ≤ S.mass := by
  exact (Summable.tsum_le_tsum (fun s => interpBranch_mass_le p s (S.density s))
    (interpBranch_mass_summable p S) S.trace_hasSum.summable).trans_eq S.trace_hasSum.tsum_eq

noncomputable def interp [DecidableEq Var] (p : QProg Var d) (S : CQState Var d) : CQState Var d :=
  stateSum (fun s => interpBranch p s (S.density s)) (interpBranch_mass_summable p S)
    ((interpBranch_total_mass_le p S).trans S.mass_le_one)

theorem interp_mass_le [DecidableEq Var] (p : QProg Var d) (S : CQState Var d) :
    (interp p S).mass ≤ S.mass := interpBranch_total_mass_le p S

/-- Full state-level forward/backward duality, with a constructed output state. -/
theorem expect_interp [DecidableEq Var] (p : QProg Var d) (S : CQState Var d)
    (Q : CQAssertion Var d) : expectation (interp p S) Q = expectation S (wp p Q) := by
  rw [interp, expectation_stateSum]
  calc
    _ = operationalExpectation p S Q := by
      apply tsum_congr
      intro s
      exact expect_interpBranch p s (S.density s) Q
    _ = _ := operationalExpectation_eq p S Q

/-- The paper's state-quantified form of total correctness. -/
def Triple [DecidableEq Var] (P : CQAssertion Var d) (p : QProg Var d)
    (Q : CQAssertion Var d) : Prop :=
  ∀ S : CQState Var d, expectation S P ≤ expectation (interp p S) Q

theorem wp_state_soundness [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d) :
    Triple (wp p Q) p Q := fun S => (expect_interp p S Q).ge

end QuantumLeanLeap.GoogleQHL
