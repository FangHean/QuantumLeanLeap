import QuantumLeanLeap.GoogleQHL.Compatibility.OmegaOrder

/-! Continuity of the paper-facing weakest-precondition interface, including
arbitrary classical stores with summable mass. -/
namespace QuantumLeanLeap.GoogleQHL.PaperAPI
open scoped ComplexOrder MatrixOrder Topology
open OmegaCompletePartialOrder Filter
variable {Var : Type} {d : Nat}

theorem pairing_assertion_omegaSup (c : Chain (CQAssertion Var d)) (s : Store Var)
    (rho : GoogleQHL.Operator d) (hr : rho.PosSemidef) :
    GoogleQHL.pairing (Observable.toCore (ωSup c s)).matrix rho =
      ⨆ n : Nat, GoogleQHL.pairing (Observable.toCore (c n s)).matrix rho :=
  pairing_observable_omegaSup (c.map (Pi.evalOrderHom s)) rho hr

theorem pairing_assertion_tendsto (c : Chain (CQAssertion Var d)) (s : Store Var)
    (rho : GoogleQHL.Operator d) (hr : rho.PosSemidef) :
    Tendsto (fun n => GoogleQHL.pairing (Observable.toCore (c n s)).matrix rho) atTop
      (𝓝 (GoogleQHL.pairing (Observable.toCore (ωSup c s)).matrix rho)) := by
  rw [pairing_assertion_omegaSup c s rho hr]
  apply tendsto_atTop_ciSup
  · intro i j hij
    exact GoogleQHL.pairing_mono ((observable_le_iff _ _).mp (c.monotone hij s)) hr
  · refine ⟨rho.trace.re, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (GoogleQHL.pairing_effect_bounds
      ⟨(Observable.toCore (c n s)).nonnegative, (Observable.toCore (c n s)).le_identity⟩ hr).2

theorem expect_assertion_omegaSup (S : CQState Var d) (c : Chain (CQAssertion Var d)) :
    expect S (ωSup c) = ⨆ n : Nat, expect S (c n) := by
  simp only [expect_eq_core]
  apply GoogleQHL.tsum_limit_eq_iSup
    (fun n s => GoogleQHL.pairing ((c n).toCore s).matrix (S.toCore.density s).matrix)
    (fun s => GoogleQHL.pairing ((ωSup c).toCore s).matrix (S.toCore.density s).matrix)
  · intro n s
    exact GoogleQHL.pairing_nonneg ((c n).toCore s).nonnegative (S.toCore.density s).positive
  · exact fun n => GoogleQHL.expectation_summable S.toCore (c n).toCore
  · intro s i j hij
    exact GoogleQHL.pairing_mono ((observable_le_iff _ _).mp (c.monotone hij s))
      (S.toCore.density s).positive
  · exact fun s => pairing_assertion_tendsto c s _ (S.toCore.density s).positive
  · exact fun n => (GoogleQHL.expectation_bounds S.toCore (c n).toCore).2

theorem assertion_le_of_expect_le {P Q : CQAssertion Var d}
    (h : ∀ S : CQState Var d, expect S P ≤ expect S Q) : P ≤ Q := by
  classical
  have ht : GoogleQHL.Triple P.toCore .skip Q.toCore := by
    intro T
    rw [GoogleQHL.interp_skip]
    simpa only [expect_eq_core, state_toCore_ofCore] using h (CQState.ofCore T)
  intro s
  apply (observable_le_iff _ _).mpr
  simpa only [GoogleQHL.wp_skip, CQAssertion.toCore] using (GoogleQHL.triple_iff _ _ _).mp ht s

theorem assertion_eq_of_expect_eq {P Q : CQAssertion Var d}
    (h : ∀ S : CQState Var d, expect S P = expect S Q) : P = Q :=
  le_antisymm (assertion_le_of_expect_le fun S => (h S).le)
    (assertion_le_of_expect_le fun S => (h S).ge)

variable [NeZero d] [DecidableEq Var]

theorem wp_map_omegaSup (p : QProg Var d) (c : Chain (CQAssertion Var d)) :
    wp p (ωSup c) = ωSup (c.map (wpOrderHom p)) := by
  apply assertion_eq_of_expect_eq
  intro S
  rw [expect_wp, expect_assertion_omegaSup, expect_assertion_omegaSup]
  congr 1
  funext n
  exact (expect_wp p S (c n)).symm

noncomputable def wpContinuousHom (p : QProg Var d) :
    CQAssertion Var d →𝒄 CQAssertion Var d where
  toOrderHom := wpOrderHom p
  map_ωSup' := wp_map_omegaSup p

theorem wp_scottContinuous (p : QProg Var d) : ωScottContinuous (wp p) :=
  (wpContinuousHom p).ωScottContinuous

end QuantumLeanLeap.GoogleQHL.PaperAPI
