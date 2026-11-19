import QuantumLeanLeap.GoogleQHL.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem pairing_nonneg {E rho : Operator d} (hE : 0 ≤ E) (hr : rho.PosSemidef) :
    0 ≤ pairing E rho := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE
  have ht := (hr.mul_mul_conjTranspose_same B).trace_nonneg
  have htR : 0 ≤ (B * rho * Matrix.conjTranspose B).trace.re :=
    (RCLike.nonneg_iff.mp ht).1
  unfold pairing
  rw [hB, Matrix.star_eq_conjTranspose]
  have eqtrace : (Matrix.conjTranspose B * B * rho).trace =
      (B * rho * Matrix.conjTranspose B).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  rw [eqtrace]
  exact htR

theorem pairing_mono {A B rho : Operator d} (h : A ≤ B) (hr : rho.PosSemidef) :
    pairing A rho ≤ pairing B rho := by
  have hp := pairing_nonneg (sub_nonneg.mpr h) hr
  simpa [pairing, Matrix.sub_mul, Matrix.trace_sub, sub_nonneg] using hp

@[simp] theorem pairing_one (rho : Operator d) : pairing 1 rho = rho.trace.re := by
  simp [pairing]

theorem pairing_effect_bounds {E rho : Operator d} (h : IsEffect E) (hr : rho.PosSemidef) :
    0 ≤ pairing E rho ∧ pairing E rho ≤ rho.trace.re :=
  ⟨pairing_nonneg h.1 hr, by simpa using pairing_mono h.2 hr⟩

/-- The countable classical-store sum in `expectation` is genuinely summable. -/
theorem expectation_summable (state : CQState Var d) (post : CQAssertion Var d) :
    Summable (fun s => pairing (post s).matrix (state.density s).matrix) := by
  apply Summable.of_nonneg_of_le
    (fun s => pairing_nonneg (post s).nonnegative (state.density s).positive)
    (fun s => (pairing_effect_bounds ⟨(post s).nonnegative, (post s).le_identity⟩
      (state.density s).positive).2)
  exact state.trace_hasSum.summable

theorem expectation_bounds (state : CQState Var d) (post : CQAssertion Var d) :
    0 ≤ expectation state post ∧ expectation state post ≤ 1 := by
  constructor
  · exact tsum_nonneg fun s => pairing_nonneg (post s).nonnegative (state.density s).positive
  · have h := Summable.tsum_le_tsum
      (fun s => (pairing_effect_bounds ⟨(post s).nonnegative, (post s).le_identity⟩
        (state.density s).positive).2)
      (expectation_summable state post) state.trace_hasSum.summable
    rw [state.trace_hasSum.tsum_eq] at h
    exact h.trans state.mass_le_one

/-- The finite forward interpreter cannot produce a negative or excessive
postcondition expectation from a physical branch. -/
theorem interpApprox_expectation_bounds [DecidableEq Var] (p : QProg Var d)
    (fuel : Nat) (post : CQPredicate Var d) (hp : IsAssertion post)
    (s : Store Var) (rho : Operator d) (hr : rho.PosSemidef) :
    0 ≤ branchExpectation post (interpApprox p fuel (s, rho)) ∧
      branchExpectation post (interpApprox p fuel (s, rho)) ≤ rho.trace.re := by
  rw [expect_wpApprox]
  exact pairing_effect_bounds (wpApprox_effect p fuel post hp s) hr

end QuantumLeanLeap.GoogleQHL
