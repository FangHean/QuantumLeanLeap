import QuantumLeanLeap.GoogleQHL.LoopUnrolling
import Mathlib.Analysis.SpecificLimits.Basic

/-! Entering probability mass, expected iteration counts, and exact loop
cost series. A body that aborts or diverges loses mass from later entries;
cost already paid in that body is still included. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

noncomputable def loopStep [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) : CQState Var d := interp body (restrictState g S)

noncomputable def loopState [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d) :
    Nat → CQState Var d → CQState Var d
  | 0, S => S
  | n + 1, S => loopState g body n (loopStep g body S)

theorem loopState_succ_outer [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (n : Nat) (S : CQState Var d) :
    loopState g body (n + 1) S = loopStep g body (loopState g body n S) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => exact ih (loopStep g body S)

noncomputable def loopEntry [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (n : Nat) (S : CQState Var d) : CQState Var d := restrictState g (loopState g body n S)

noncomputable def entryProbability [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (n : Nat) (S : CQState Var d) : ENNReal := ENNReal.ofReal (loopEntry g body n S).mass

/-- Expected number of body entries. This is subnormalized when S has mass
less than one, and may be infinite. -/
noncomputable def expectedIterations [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) : ENNReal := ∑' n, entryProbability g body n S

theorem expectedCost_unroll_eq_sum [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (n : Nat) (S : CQState Var d) :
    expectedCost w (loopUnroll g body n) S =
      ∑ i ∈ Finset.range n, expectedCost w body (loopEntry g body i S) := by
  induction n generalizing S with
  | zero => simp [loopUnroll, expectedCost, prefixCostSup, expectedCostApprox]
  | succ n ih =>
      rw [loopUnroll, expectedCost_if, expectedCost_seq, expectedCost_skip, add_zero, ih]
      rw [Finset.sum_range_succ']
      simp only [loopEntry, loopState, loopStep]
      exact add_comm _ _

/-- Exact cost equals the sum of body costs on the states that actually
enter each iteration. No almost-sure termination assumption is required. -/
theorem expectedCost_while_eq_tsum [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (S : CQState Var d) :
    expectedCost w (.qwhile g body) S = ∑' n, expectedCost w body (loopEntry g body n S) := by
  rw [expectedCost_while_eq_iSup_unroll]
  simp only [expectedCost_unroll_eq_sum]
  exact ENNReal.tsum_eq_iSup_nat.symm

/-- Per-entry cost times expected number of entries, including infinity. -/
theorem expectedCost_while_le_iterations [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (C : ENNReal)
    (hbody : CostBound w body C) (S : CQState Var d) :
    expectedCost w (.qwhile g body) S ≤ C * expectedIterations g body S := by
  rw [expectedCost_while_eq_tsum, expectedIterations, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun n => hbody (loopEntry g body n S))

/-- A uniform per-entry charge yields equality, not only an upper bound. -/
theorem expectedCost_while_eq_iterations [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (C : ENNReal)
    (hbody : ∀ T : CQState Var d, expectedCost w body T = C * ENNReal.ofReal T.mass)
    (S : CQState Var d) : expectedCost w (.qwhile g body) S = C * expectedIterations g body S := by
  rw [expectedCost_while_eq_tsum, expectedIterations, ← ENNReal.tsum_mul_left]
  exact tsum_congr (fun n => hbody (loopEntry g body n S))

theorem entryProbability_le_geometric [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) (r : ENNReal)
    (h : ∀ n, entryProbability g body (n + 1) S ≤ r * entryProbability g body n S) (n : Nat) :
    entryProbability g body n S ≤ r ^ n * entryProbability g body 0 S := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ ≤ r * entryProbability g body n S := h n
        _ ≤ r * (r ^ n * entryProbability g body 0 S) := mul_le_mul_of_nonneg_left ih bot_le
        _ = _ := by rw [pow_succ', mul_assoc]

/-- The geometric bound is meaningful for r < 1; the statement also remains
valid at r ≥ 1, where the inverse in ENNReal becomes infinity. -/
theorem expectedIterations_le_geometric [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (S : CQState Var d) (r : ENNReal)
    (h : ∀ n, entryProbability g body (n + 1) S ≤ r * entryProbability g body n S) :
    expectedIterations g body S ≤ (1 - r)⁻¹ * entryProbability g body 0 S := by
  calc
    _ ≤ ∑' n, r ^ n * entryProbability g body 0 S :=
      ENNReal.tsum_le_tsum (entryProbability_le_geometric g body S r h)
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

theorem expectedCost_while_le_geometric [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (C r : ENNReal)
    (hbody : CostBound w body C) (S : CQState Var d)
    (h : ∀ n, entryProbability g body (n + 1) S ≤ r * entryProbability g body n S) :
    expectedCost w (.qwhile g body) S ≤ C * ((1 - r)⁻¹ * entryProbability g body 0 S) :=
  (expectedCost_while_le_iterations w g body C hbody S).trans
    (mul_le_mul_of_nonneg_left (expectedIterations_le_geometric g body S r h) bot_le)

end QuantumLeanLeap.GoogleQHL
