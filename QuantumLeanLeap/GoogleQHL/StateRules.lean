import QuantumLeanLeap.GoogleQHL.Denotational
import QuantumLeanLeap.GoogleQHL.StateExt

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem wp_skip [DecidableEq Var] (Q : CQAssertion Var d) (s : Store Var) :
    (wp .skip Q s).matrix = (Q s).matrix := by
  apply le_antisymm
  · exact wp_le .skip Q s _ (fun _ => le_rfl)
  · exact wpApprox_le_wp .skip Q 0 s

theorem wp_abort [DecidableEq Var] (Q : CQAssertion Var d) (s : Store Var) :
    (wp .abort Q s).matrix = 0 := by
  apply le_antisymm
  · exact wp_le .abort Q s _ (fun _ => le_rfl)
  · exact (wp .abort Q s).nonnegative

theorem wp_if [DecidableEq Var] (g : Store Var → Bool) (a b : QProg Var d)
    (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.qif g a b) Q s).matrix = if g s then (wp a Q s).matrix else (wp b Q s).matrix := by
  by_cases hg : g s = true
  · simp only [hg, if_true]
    apply le_antisymm
    · apply wp_le
      intro k
      simpa only [wpApprox, hg, if_true] using wpApprox_le_wp a Q k s
    · apply wp_le
      intro k
      simpa only [wpApprox, hg, if_true] using wpApprox_le_wp (.qif g a b) Q k s
  · simp only [hg, Bool.false_eq_true, if_false]
    apply le_antisymm
    · apply wp_le
      intro k
      simpa only [wpApprox, hg, Bool.false_eq_true, if_false] using wpApprox_le_wp b Q k s
    · apply wp_le
      intro k
      simpa only [wpApprox, hg, Bool.false_eq_true, if_false] using wpApprox_le_wp (.qif g a b) Q k s

theorem interp_skip [DecidableEq Var] (S : CQState Var d) : interp .skip S = S := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp]
  simp only [expectation, wp_skip]

theorem interp_seq [DecidableEq Var] (a b : QProg Var d) (S : CQState Var d) :
    interp (.seq a b) S = interp b (interp a S) := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp, expect_interp, expect_interp]
  simp only [expectation, wp_seq]

/-- Actual state equality for loop unfolding, not just equality of a selected
observable's expected value. -/
theorem interp_while_unfold [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) :
    interp (.qwhile g body) S = interp (.qif g (.seq body (.qwhile g body)) .skip) S := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp, expect_interp]
  simp only [expectation, wp_if, wp_seq, wp_skip, wp_while_unfold]

/-- A strictly positive scale embeds any PSD matrix into a partial density.
This justifies moving between raw positive tests and physical substates. -/
noncomputable def partialTest (A : Operator d) (hA : A.PosSemidef) : PartialDensity d where
  matrix := (A.trace.re + 1)⁻¹ • A
  positive := hA.smul (inv_nonneg.mpr (by
    have ht : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
    linarith))
  trace_le_one := by
    have ht : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
    have hc : 0 < A.trace.re + 1 := by linarith
    simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    calc
      _ ≤ (A.trace.re + 1)⁻¹ * (A.trace.re + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hc.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)

theorem triple_iff [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d) :
    Triple P p Q ↔ ∀ s, (P s).matrix ≤ (wp p Q s).matrix := by
  constructor
  · intro h s
    apply le_of_pairing_le (Matrix.nonneg_iff_posSemidef.mp (P s).nonnegative).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp (wp p Q s).nonnegative).isHermitian
    intro rho hr
    have hh := h (singleState s (partialTest rho hr)).toCQState
    rw [expect_interp, FiniteState.expectation_toCQState, FiniteState.expectation_toCQState] at hh
    have hc : 0 < (rho.trace.re + 1)⁻¹ := by
      apply inv_pos.mpr
      have ht : 0 ≤ rho.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
      linarith
    have hh' : (rho.trace.re + 1)⁻¹ * pairing (P s).matrix rho ≤
        (rho.trace.re + 1)⁻¹ * pairing (wp p Q s).matrix rho := by
      change pairing (P s).matrix ((rho.trace.re + 1)⁻¹ • rho) + 0 ≤
        pairing (wp p Q s).matrix ((rho.trace.re + 1)⁻¹ • rho) + 0 at hh
      simpa only [pairing_smul_right, add_zero] using hh
    exact le_of_mul_le_mul_left hh' hc
  · intro h S
    rw [expect_interp]
    exact Summable.tsum_le_tsum (fun s => pairing_mono (h s) (S.density s).positive)
      (expectation_summable S P) (expectation_summable S (wp p Q))

theorem wp_state_weakest [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d)
    (h : Triple P p Q) : ∀ s, (P s).matrix ≤ (wp p Q s).matrix :=
  (triple_iff P Q p).mp h

theorem triple_iff_hoare [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d) :
    Triple P p Q ↔ Hoare P p Q := (triple_iff P Q p).trans (hoare_iff P Q p).symm

theorem triple_seq [DecidableEq Var] (P R Q : CQAssertion Var d) (a b : QProg Var d)
    (ha : Triple P a R) (hb : Triple R b Q) : Triple P (.seq a b) Q := by
  intro S
  rw [interp_seq]
  exact (ha S).trans (hb (interp a S))

end QuantumLeanLeap.GoogleQHL
