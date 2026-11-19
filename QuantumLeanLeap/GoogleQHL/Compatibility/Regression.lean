import QuantumLeanLeap.GoogleQHL.Compatibility.PaperAPI
import QuantumLeanLeap.GoogleQHL.Compatibility.FixedPoint
import QuantumLeanLeap.GoogleQHL.Compatibility.StateContinuity
import QuantumLeanLeap.GoogleQHL.StateRegression
import QuantumLeanLeap.GoogleQHL.Verification.ResetSemantics

namespace QuantumLeanLeap.GoogleQHL.PaperAPI.Regression

variable {Var : Type} {d : Nat} [NeZero d]

open OmegaCompletePartialOrder

theorem skip_wp_identity [DecidableEq Var] (Q : CQAssertion Var d) : wp .skip Q = Q := by
  funext s
  apply Subtype.ext
  apply HermitianMat.ext
  exact GoogleQHL.wp_skip Q.toCore s

/-- Every assertion is a fixed point of this divergent loop functional.
The fixed-point equation alone therefore cannot select the program semantics. -/
theorem diverge_every_assertion_fixed [DecidableEq Var] (Q R : CQAssertion Var d) :
    loopFunctional (fun _ => True) .skip Q R = R := by
  funext s
  simp only [loopFunctional, if_true, skip_wp_identity]

/-- Leastness selects bottom even when nonzero fixed points also exist. -/
theorem diverge_wp_bottom [DecidableEq Var] (Q : CQAssertion Var d) :
    wp (.qwhile (fun _ => True) .skip) Q = ⊥ := by
  apply le_antisymm
  · apply wp_qwhile_least
    exact (diverge_every_assertion_fixed Q ⊥).le
  · exact bot_le

theorem diverge_kleene_bottom [DecidableEq Var] (Q : CQAssertion Var d) :
    ωSup (loopIterates (fun _ => True) .skip Q) = ⊥ := by
  rw [← wp_qwhile_eq_omegaSup_iterates, diverge_wp_bottom]

theorem false_guard_kleene_post [DecidableEq Var] (body : QProg Var d)
    (Q : CQAssertion Var d) : ωSup (loopIterates (fun _ => False) body Q) = Q := by
  rw [← wp_qwhile_eq_omegaSup_iterates]
  funext s
  simp only [wp_qwhile_unfold, if_false]

/-- False propositional guards return the input state, including arbitrary
summable classical mixtures. This checks guard translation and both state conversions. -/
theorem false_prop_loop_returns_input [DecidableEq Var] (body : QProg Var d) (S : CQState Var d) :
    (interp (.qwhile (fun _ => False) body)).toStateFun S = S := by
  simp only [interp, QProg.toCore, decide_false]
  rw [GoogleQHL.StateRegression.false_loop_returns_input]
  exact state_ofCore_toCore S

/-- The existing JSON candidate language can use the paper-shaped frontend
without altering its operational or matrix backend interpretation. -/
def fromReset : Verification.ResetLanguage.Program → QProg Unit 2
  | .skip => .skip
  | .x => .apply Verification.ResetLanguage.xUnitary
  | .z => .apply Verification.ResetLanguage.zUnitary
  | .measure => .measure () 2 (Circuits.wireMeasurement (n := 1) 0)
  | .seq a b => .seq (fromReset a) (fromReset b)
  | .ifZero a b => .qif (fun s => s () = 0) (fromReset a) (fromReset b)

theorem fromReset_toCore (p : Verification.ResetLanguage.Program) :
    (fromReset p).toCore = p.compile := by
  induction p with
  | skip => rfl
  | x => rfl
  | z => rfl
  | measure => rfl
  | seq a b iha ihb => simp only [fromReset, QProg.toCore, iha, ihb, Verification.ResetLanguage.Program.compile]
  | ifZero a b iha ihb => simp only [fromReset, QProg.toCore, iha, ihb, Verification.ResetLanguage.Program.compile]

theorem fromReset_matrix_histories (p : Verification.ResetLanguage.Program)
    (fuel : Nat) (input : GoogleQHL.Branch Unit 2) :
    GoogleQHL.interpApprox (fromReset p).toCore fuel input = p.toDynamic.run input := by
  rw [fromReset_toCore]
  exact (p.toDynamic_run fuel input).symm

/-- Inner-product expectation in the new interface agrees with the actual
matrix-gate dynamic program on every legal mixed input and assertion. -/
theorem fromReset_matrix_expectation (p : Verification.ResetLanguage.Program)
    (S : GoogleQHL.CQState Unit 2) (Q : GoogleQHL.CQAssertion Unit 2) :
    expect ((interp (fromReset p)).toStateFun (CQState.ofCore S)) (CQAssertion.ofCore Q) =
      GoogleQHL.expectation (GoogleQHL.interp p.toDynamic.compile S) Q := by
  rw [expect_eq_core]
  simp only [interp, state_toCore_ofCore, assertion_toCore_ofCore, fromReset_toCore,
    Verification.ResetLanguage.Program.toDynamic_compile]

end QuantumLeanLeap.GoogleQHL.PaperAPI.Regression
