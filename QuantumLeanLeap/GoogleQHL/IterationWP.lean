import QuantumLeanLeap.GoogleQHL.Iterations

/-! Continuing a loop is a quantum program in its own right. Its weakest
precondition computes the mass entering each later iteration. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

def guardAssertion (g : Store Var → Bool) (Q : CQAssertion Var d) : CQAssertion Var d :=
  fun s => if g s then Q s else zeroObservable

def guardIndicator (g : Store Var → Bool) : CQAssertion Var d :=
  guardAssertion g (oneAssertion Var d)

theorem expectation_restrictState (g : Store Var → Bool) (S : CQState Var d)
    (Q : CQAssertion Var d) : expectation (restrictState g S) Q = expectation S (guardAssertion g Q) := by
  apply tsum_congr
  intro s
  cases hg : g s <;> simp [restrictState, guardAssertion, zeroDensity, zeroObservable, hg]

theorem restrictState_mass_eq_expectation (g : Store Var → Bool) (S : CQState Var d) :
    (restrictState g S).mass = expectation S (guardIndicator g) := by
  rw [← expectation_one, expectation_restrictState]
  rfl

def continueProgram (g : Store Var → Bool) (body : QProg Var d) : QProg Var d :=
  .qif g body .abort

theorem interp_continueProgram [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) : interp (continueProgram g body) S = loopStep g body S := by
  apply CQState.eq_of_expectations
  intro Q
  rw [expect_interp, loopStep, expect_interp, expectation_restrictState]
  apply tsum_congr
  intro s
  cases hg : g s <;> simp [continueProgram, wp_if, wp_abort, guardAssertion, zeroObservable, hg]

def continueIterate (g : Store Var → Bool) (body : QProg Var d) : Nat → QProg Var d
  | 0 => .skip
  | n + 1 => .seq (continueProgram g body) (continueIterate g body n)

theorem interp_continueIterate [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (n : Nat) (S : CQState Var d) : interp (continueIterate g body n) S = loopState g body n S := by
  induction n generalizing S with
  | zero => exact interp_skip S
  | succ n ih =>
      rw [continueIterate, interp_seq, interp_continueProgram, ih]
      rfl

/-- The indicator is tested after n successful continuations; the test at
n = 0 accounts for the initial guard before charging the first body. -/
theorem entryProbability_eq_wp [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (n : Nat) (S : CQState Var d) : entryProbability g body n S =
      ENNReal.ofReal (expectation S (wp (continueIterate g body n) (guardIndicator g))) := by
  unfold entryProbability loopEntry
  rw [restrictState_mass_eq_expectation, ← interp_continueIterate, expect_interp]

theorem expectedIterations_eq_wp_series [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) : expectedIterations g body S =
      ∑' n, ENNReal.ofReal (expectation S (wp (continueIterate g body n) (guardIndicator g))) :=
  tsum_congr (fun n => entryProbability_eq_wp g body n S)

/-- A uniform one-step continuation estimate implies geometric decay on
the actual reachable states, including mixed and subnormalized inputs. -/
theorem entryProbability_contraction [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (r : ENNReal)
    (h : ∀ T : CQState Var d,
      ENNReal.ofReal (expectation (restrictState g T) (wp body (guardIndicator g))) ≤
        r * ENNReal.ofReal (restrictState g T).mass)
    (S : CQState Var d) (n : Nat) :
    entryProbability g body (n + 1) S ≤ r * entryProbability g body n S := by
  unfold entryProbability loopEntry
  rw [loopState_succ_outer, loopStep, restrictState_mass_eq_expectation, expect_interp]
  exact h (loopState g body n S)

/-- A Loewner bound on the continuation effect suffices; it is required
only at stores satisfying the loop guard. -/
theorem continuation_expectation_le [DecidableEq Var] (g : Store Var → Bool)
    (body : QProg Var d) (q : Real)
    (h : ∀ s, g s = true → (wp body (guardIndicator g) s).matrix ≤ q • (1 : Operator d))
    (S : CQState Var d) :
    expectation (restrictState g S) (wp body (guardIndicator g)) ≤ q * (restrictState g S).mass := by
  let T := restrictState g S
  have hb : ∀ s, pairing (wp body (guardIndicator g) s).matrix (T.density s).matrix ≤
      q * (T.density s).matrix.trace.re := by
    intro s
    cases hg : g s
    · simp [T, restrictState, zeroDensity, hg, pairing]
    · have hm := pairing_mono (h s hg) (T.density s).positive
      simpa only [pairing, smul_mul_assoc, one_mul, Matrix.trace_smul,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hm
  have hs := Summable.tsum_le_tsum hb (expectation_summable T (wp body (guardIndicator g)))
    (T.trace_hasSum.summable.mul_left q)
  change (∑' s, pairing (wp body (guardIndicator g) s).matrix (T.density s).matrix) ≤ q * T.mass
  simpa only [tsum_mul_left, T.trace_hasSum.tsum_eq] using hs

theorem entryProbability_contraction_of_wp [DecidableEq Var] (g : Store Var → Bool)
    (body : QProg Var d) (q : Real) (hq : 0 ≤ q)
    (h : ∀ s, g s = true → (wp body (guardIndicator g) s).matrix ≤ q • (1 : Operator d))
    (S : CQState Var d) (n : Nat) :
    entryProbability g body (n + 1) S ≤ ENNReal.ofReal q * entryProbability g body n S := by
  apply entryProbability_contraction g body (ENNReal.ofReal q) _ S n
  intro T
  rw [← ENNReal.ofReal_mul hq]
  exact ENNReal.ofReal_le_ofReal (continuation_expectation_le g body q h T)

theorem expectedCost_while_le_of_wp [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (C : ENNReal) (q : Real)
    (hq : 0 ≤ q) (hbody : CostBound w body C)
    (h : ∀ s, g s = true → (wp body (guardIndicator g) s).matrix ≤ q • (1 : Operator d))
    (S : CQState Var d) : expectedCost w (.qwhile g body) S ≤
      C * ((1 - ENNReal.ofReal q)⁻¹ * entryProbability g body 0 S) :=
  expectedCost_while_le_geometric w g body C (ENNReal.ofReal q) hbody S
    (entryProbability_contraction_of_wp g body q hq h S)

end QuantumLeanLeap.GoogleQHL
