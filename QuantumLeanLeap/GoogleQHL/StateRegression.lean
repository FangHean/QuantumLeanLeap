import QuantumLeanLeap.GoogleQHL.CostControl
import QuantumLeanLeap.GoogleQHL.Regression

namespace QuantumLeanLeap.GoogleQHL.StateRegression
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

/-- A guard that is false initially returns the full input in the unbounded
semantics, even though the zeroth approximation was the bottom state. -/
theorem false_loop_returns_input [DecidableEq Var] (body : QProg Var d) (S : CQState Var d) :
    interp (.qwhile (fun _ => false) body) S = S := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp]
  simp only [expectation, wp_while_unfold, Bool.false_eq_true, if_false]

/-- Nontermination produces the zero CQ-state, not merely a selected zero
expectation, for every admissible initial mixture. -/
theorem diverge_zero_state (S : CQState Examples.Var 2) :
    interp Regression.diverge S = zeroState Examples.Var 2 := by
  apply CQState.eq_of_expectations
  intro Q
  rw [interp, expectation_stateSum]
  simp only [expect_interpBranch, Regression.diverge_expectation, tsum_zero]
  simp [expectation, zeroState]

theorem overwrite_store_merges_all (S : CQState Unit d) :
    ((interp (.assign () (fun _ => 0)) S).density (fun _ => 0)).matrix =
      ∑' s, (S.density s).matrix := by
  classical
  rw [interp_assign, pushforwardState_density]
  apply tsum_congr
  intro s
  have hu : Function.update s () 0 = fun _ => 0 := by
    funext x
    cases x
    simp
  simp only [hu, if_true]

theorem abort_retains_executed_cost [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : CQState Var d) : expectedCost w (.seq p .abort) S = expectedCost w p S := by
  rw [expectedCost_seq]
  simp [expectedCost, prefixCostSup, expectedCostApprox]

end QuantumLeanLeap.GoogleQHL.StateRegression
