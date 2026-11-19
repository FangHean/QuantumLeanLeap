import QuantumLeanLeap.GoogleQHL.StateRules

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem wp_eq_of_approx_eq [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d)
    (E : CQPredicate Var d) (h : ∀ k s, wpApprox p k Q.toPredicate s = E s) (s : Store Var) :
    (wp p Q s).matrix = E s := by
  apply le_antisymm
  · exact wp_le p Q s _ (fun k => (h k s).le)
  · exact (h 0 s).symm.le.trans (wpApprox_le_wp p Q 0 s)

theorem wp_assign [DecidableEq Var] (v : Var) (e : Store Var → Int)
    (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.assign v e) Q s).matrix = (Q (Function.update s v (e s))).matrix :=
  wp_eq_of_approx_eq (.assign v e) Q
    (fun t => (Q (Function.update t v (e t))).matrix) (fun _ _ => rfl) s

theorem wp_qset [DecidableEq Var] (i : Fin d) (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.qset i) Q s).matrix = Matrix.scalar (Fin d) ((Q s).matrix i i) :=
  wp_eq_of_approx_eq (.qset i) Q
    (fun t => Matrix.scalar (Fin d) ((Q t).matrix i i)) (fun _ _ => rfl) s

theorem wp_apply [DecidableEq Var] (U : Unitary d) (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.apply U) Q s).matrix = Matrix.conjTranspose U.matrix * (Q s).matrix * U.matrix :=
  wp_eq_of_approx_eq (.apply U) Q
    (fun t => Matrix.conjTranspose U.matrix * (Q t).matrix * U.matrix) (fun _ _ => rfl) s

theorem wp_measure [DecidableEq Var] {outcomes : Nat} (v : Var) (M : Measurement d outcomes)
    (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.measure v outcomes M) Q s).matrix = ∑ o, Matrix.conjTranspose (M.kraus o) *
      (Q (Function.update s v (Int.ofNat o.val))).matrix * M.kraus o :=
  wp_eq_of_approx_eq (.measure v outcomes M) Q
    (fun t => ∑ o, Matrix.conjTranspose (M.kraus o) *
      (Q (Function.update t v (Int.ofNat o.val))).matrix * M.kraus o) (fun _ _ => rfl) s

def zeroState (Var : Type) (d : Nat) : CQState Var d where
  density _ := ⟨0, Matrix.PosSemidef.zero, by simp⟩
  mass := 0
  trace_hasSum := by simp
  mass_le_one := zero_le_one

theorem interp_abort [DecidableEq Var] (S : CQState Var d) : interp .abort S = zeroState Var d := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp]
  simp [expectation, wp_abort, zeroState]

def oneAssertion (Var : Type) (d : Nat) : CQAssertion Var d :=
  fun _ => ⟨1, Matrix.PosSemidef.one.nonneg, le_rfl⟩

theorem expectation_one (S : CQState Var d) : expectation S (oneAssertion Var d) = S.mass := by
  simpa [expectation, oneAssertion] using S.trace_hasSum.tsum_eq

theorem interp_mass_eq_of_wp_one [DecidableEq Var] (p : QProg Var d)
    (h : ∀ s, (wp p (oneAssertion Var d) s).matrix = 1) (S : CQState Var d) :
    (interp p S).mass = S.mass := by
  rw [← expectation_one, expect_interp, ← expectation_one S]
  simp only [expectation, h, oneAssertion]

theorem interp_measure_mass [DecidableEq Var] {outcomes : Nat} (v : Var) (M : Measurement d outcomes)
    (hcomplete : (∑ o, Matrix.conjTranspose (M.kraus o) * M.kraus o) = 1) (S : CQState Var d) :
    (interp (.measure v outcomes M) S).mass = S.mass := by
  apply interp_mass_eq_of_wp_one
  intro s
  simpa only [wp_measure, oneAssertion, Matrix.mul_one] using hcomplete

theorem interp_apply_mass [DecidableEq Var] (U : Unitary d) (S : CQState Var d) :
    (interp (.apply U) S).mass = S.mass := by
  apply interp_mass_eq_of_wp_one
  intro s
  simpa only [wp_apply, oneAssertion, Matrix.mul_one] using U.left_inverse

theorem singleState_mass (s : Store Var) (rho : PartialDensity d) :
    (singleState s rho).toCQState.mass = rho.matrix.trace.re := by
  simp [singleState, FiniteState.toCQState, branchMass]

noncomputable def pushforwardState (f : Store Var → Store Var) (S : CQState Var d) : CQState Var d :=
  stateSum (fun s => (singleState (f s) (S.density s)).toCQState)
    (by simpa only [singleState_mass] using S.trace_hasSum.summable)
    (by simpa only [singleState_mass, S.trace_hasSum.tsum_eq] using S.mass_le_one)

theorem expectation_pushforwardState (f : Store Var → Store Var) (S : CQState Var d)
    (Q : CQAssertion Var d) : expectation (pushforwardState f S) Q = expectation S (fun s => Q (f s)) := by
  rw [pushforwardState, expectation_stateSum]
  simp only [FiniteState.expectation_toCQState, singleState, branchExpectation_cons,
    branchExpectation_nil, add_zero, CQAssertion.toPredicate]
  rfl

theorem pushforwardState_density [DecidableEq (Store Var)]
    (f : Store Var → Store Var) (S : CQState Var d) (t : Store Var) :
    ((pushforwardState f S).density t).matrix =
      ∑' s, if f s = t then (S.density s).matrix else 0 := by
  classical
  simp [pushforwardState, stateSum, FiniteState.toCQState, singleState, storeDensity, eq_comm]

theorem interp_assign [DecidableEq Var] (v : Var) (e : Store Var → Int) (S : CQState Var d) :
    interp (.assign v e) S = pushforwardState (fun s => Function.update s v (e s)) S := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp, expectation_pushforwardState]
  simp only [expectation, wp_assign]

end QuantumLeanLeap.GoogleQHL
