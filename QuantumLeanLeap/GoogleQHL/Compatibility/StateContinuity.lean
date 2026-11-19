import QuantumLeanLeap.GoogleQHL.Compatibility.Continuity

/-! The forward interpreter as a standard Mathlib continuous order homomorphism. -/
namespace QuantumLeanLeap.GoogleQHL.PaperAPI
open scoped ComplexOrder MatrixOrder
open OmegaCompletePartialOrder
variable {Var : Type} {d : Nat}

theorem state_le_of_expect_le {S T : CQState Var d}
    (h : ∀ Q : CQAssertion Var d, expect S Q ≤ expect T Q) : S ≤ T := by
  apply (state_le_iff _ _).mpr
  intro s
  apply GoogleQHL.le_of_pairing_le (S.toCore.density s).positive.isHermitian
    (T.toCore.density s).positive.isHermitian
  intro rho hr
  let D := GoogleQHL.partialTest rho hr
  let E : GoogleQHL.Observable d := ⟨D.matrix, D.isEffect.1, D.isEffect.2⟩
  have hh := h (CQAssertion.ofCore (GoogleQHL.localizedAssertion s E))
  simp only [expect_eq_core, assertion_toCore_ofCore, GoogleQHL.expectation_localized] at hh
  have hcomm (A B : GoogleQHL.Operator d) : GoogleQHL.pairing A B = GoogleQHL.pairing B A :=
    congrArg Complex.re (Matrix.trace_mul_comm A B)
  rw [hcomm E.matrix _, hcomm E.matrix _] at hh
  change GoogleQHL.pairing (S.toCore.density s).matrix ((rho.trace.re + 1)⁻¹ • rho) ≤
    GoogleQHL.pairing (T.toCore.density s).matrix ((rho.trace.re + 1)⁻¹ • rho) at hh
  simp only [GoogleQHL.pairing_smul_right] at hh
  apply le_of_mul_le_mul_left hh
  apply inv_pos.mpr
  have ht : 0 ≤ rho.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
  linarith

theorem expect_state_mono {S T : CQState Var d} (h : S ≤ T) (Q : CQAssertion Var d) :
    expect S Q ≤ expect T Q := by
  simp only [expect_eq_core]
  apply Summable.tsum_le_tsum _ (GoogleQHL.expectation_summable S.toCore Q.toCore)
    (GoogleQHL.expectation_summable T.toCore Q.toCore)
  intro s
  have hcomm (A B : GoogleQHL.Operator d) : GoogleQHL.pairing A B = GoogleQHL.pairing B A :=
    congrArg Complex.re (Matrix.trace_mul_comm A B)
  rw [hcomm (Q.toCore s).matrix _, hcomm (Q.toCore s).matrix _]
  exact GoogleQHL.pairing_mono ((state_le_iff _ _).mp h s)
    (Matrix.nonneg_iff_posSemidef.mp (Q.toCore s).nonnegative)

theorem state_eq_of_expect_eq {S T : CQState Var d}
    (h : ∀ Q : CQAssertion Var d, expect S Q = expect T Q) : S = T :=
  le_antisymm (state_le_of_expect_le fun Q => (h Q).le)
    (state_le_of_expect_le fun Q => (h Q).ge)

variable [NeZero d] [DecidableEq Var]

theorem interp_mono (p : QProg Var d) : Monotone (interp p).toStateFun := by
  intro S T h
  apply state_le_of_expect_le
  intro Q
  rw [← expect_wp, ← expect_wp]
  exact expect_state_mono h (wp p Q)

noncomputable def interpOrderHom (p : QProg Var d) : CQState Var d →o CQState Var d :=
  ⟨(interp p).toStateFun, interp_mono p⟩

theorem interp_map_omegaSup (p : QProg Var d) (c : Chain (CQState Var d)) :
    (interp p).toStateFun (ωSup c) = ωSup (c.map (interpOrderHom p)) := by
  apply state_eq_of_expect_eq
  intro Q
  rw [← expect_wp, expect_state_omegaSup, expect_state_omegaSup]
  congr 1
  funext n
  exact expect_wp p (c n) Q

noncomputable def interpContinuousHom (p : QProg Var d) : CQState Var d →𝒄 CQState Var d where
  toOrderHom := interpOrderHom p
  map_ωSup' := interp_map_omegaSup p

theorem interp_scottContinuous (p : QProg Var d) : ωScottContinuous (interp p).toStateFun :=
  (interpContinuousHom p).ωScottContinuous

end QuantumLeanLeap.GoogleQHL.PaperAPI
