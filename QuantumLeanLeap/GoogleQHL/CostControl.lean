import QuantumLeanLeap.GoogleQHL.CostComposition

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

def zeroDensity (d : Nat) : PartialDensity d := ⟨0, Matrix.PosSemidef.zero, by simp⟩

noncomputable def restrictState (g : Store Var → Bool) (S : CQState Var d) : CQState Var d where
  density s := if g s then S.density s else zeroDensity d
  mass := ∑' s, if g s then (S.density s).matrix.trace.re else 0
  trace_hasSum := by
    have hs : Summable (fun s => if g s then (S.density s).matrix.trace.re else 0) := by
      apply Summable.of_nonneg_of_le _ _ S.trace_hasSum.summable
      · intro s; split <;> [exact (RCLike.nonneg_iff.mp (S.density s).positive.trace_nonneg).1; exact le_rfl]
      · intro s; split <;> [exact le_rfl; exact (RCLike.nonneg_iff.mp (S.density s).positive.trace_nonneg).1]
    simpa only [apply_ite, zeroDensity, Matrix.trace_zero, Complex.zero_re] using hs.hasSum
  mass_le_one := by
    apply le_trans _ S.mass_le_one
    have hn : ∀ s, 0 ≤ (if g s then (S.density s).matrix.trace.re else 0) := by
      intro s; split <;> [exact (RCLike.nonneg_iff.mp (S.density s).positive.trace_nonneg).1; exact le_rfl]
    have hb : ∀ s, (if g s then (S.density s).matrix.trace.re else 0) ≤ (S.density s).matrix.trace.re := by
      intro s; split <;> [exact le_rfl; exact (RCLike.nonneg_iff.mp (S.density s).positive.trace_nonneg).1]
    exact (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le hn hb S.trace_hasSum.summable)
      S.trace_hasSum.summable).trans_eq S.trace_hasSum.tsum_eq

theorem prefixCostSup_zero [DecidableEq Var] (w : CostModel d) (p : QProg Var d) (s : Store Var) :
    prefixCostSup w p (s, 0) = 0 := by
  simp [prefixCostSup, expectedCostApprox_pairing, pairing]

theorem prefixCostSup_if [DecidableEq Var] (w : CostModel d) (g : Store Var → Bool)
    (a b : QProg Var d) (input : Branch Var d) :
    prefixCostSup w (.qif g a b) input = if g input.1 then prefixCostSup w a input else prefixCostSup w b input := by
  cases hg : g input.1 <;> simp [prefixCostSup, expectedCostApprox, hg]

theorem expectedCost_skip [DecidableEq Var] (w : CostModel d) (S : CQState Var d) :
    expectedCost w .skip S = 0 := by
  simp [expectedCost, prefixCostSup, expectedCostApprox]

/-- Branches are charged according to their restricted input substates. -/
theorem expectedCost_if [DecidableEq Var] (w : CostModel d) (g : Store Var → Bool)
    (a b : QProg Var d) (S : CQState Var d) :
    expectedCost w (.qif g a b) S = expectedCost w a (restrictState g S) +
      expectedCost w b (restrictState (fun s => !(g s)) S) := by
  unfold expectedCost
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro s
  cases hg : g s <;> simp [prefixCostSup_if, restrictState, zeroDensity, hg, prefixCostSup_zero]

theorem prefixCostSup_while_unfold [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (input : Branch Var d) :
    prefixCostSup w (.qwhile g body) input =
      if g input.1 then prefixCostSup w (.seq body (.qwhile g body)) input else 0 := by
  unfold prefixCostSup
  cases hg : g input.1
  · simp only [Bool.false_eq_true, if_false]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro k
    cases k with
    | zero => simp [expectedCostApprox]
    | succ k => simp [expectedCostApprox_while_succ, hg]
  · simp only [if_true]
    apply le_antisymm
    · apply iSup_le
      intro k
      cases k with
      | zero => simp [expectedCostApprox]
      | succ k =>
          have he : expectedCostApprox w (.qwhile g body) (k + 1) input =
              expectedCostApprox w (.seq body (.qwhile g body)) k input := by
            rw [expectedCostApprox_while_succ]
            simp only [hg, if_true, expectedCostApprox]
          rw [he]
          exact le_iSup (fun j : Nat => ENNReal.ofReal
            (expectedCostApprox w (.seq body (.qwhile g body)) j input)) k
    · apply iSup_le
      intro k
      have he : expectedCostApprox w (.seq body (.qwhile g body)) k input =
          expectedCostApprox w (.qwhile g body) (k + 1) input := by
        rw [expectedCostApprox_while_succ]
        simp only [hg, if_true, expectedCostApprox]
      rw [he]
      exact le_iSup (fun j : Nat => ENNReal.ofReal
        (expectedCostApprox w (.qwhile g body) j input)) (k + 1)

/-- Exact unbounded loop cost recurrence. Entering histories pay the body
cost, and the actual body output is fed to the next iteration. -/
theorem expectedCost_while_unfold [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (S : CQState Var d) :
    expectedCost w (.qwhile g body) S = expectedCost w body (restrictState g S) +
      expectedCost w (.qwhile g body) (interp body (restrictState g S)) := by
  have he : expectedCost w (.qwhile g body) S =
      expectedCost w (.qif g (.seq body (.qwhile g body)) .skip) S := by
    apply tsum_congr
    intro s
    rw [prefixCostSup_while_unfold, prefixCostSup_if]
    simp [prefixCostSup, expectedCostApprox]
  rw [he, expectedCost_if, expectedCost_skip, add_zero, expectedCost_seq]

end QuantumLeanLeap.GoogleQHL
