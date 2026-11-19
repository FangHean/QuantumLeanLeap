import QuantumLeanLeap.GoogleQHL.CostBounds

/-! Outer loop unfoldings leave the body unbounded. Their costs have the
same supremum as the diagonal fuel approximation, including nested loops. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

def loopUnroll (g : Store Var → Bool) (body : QProg Var d) : Nat → QProg Var d
  | 0 => .abort
  | k + 1 => .qif g (.seq body (loopUnroll g body k)) .skip

theorem costPredicate_fuel_mono [DecidableEq Var] (w : CostModel d) (p : QProg Var d) (s : Store Var) :
    Monotone (fun k => costPredicate w p k s) :=
  monotone_nat_of_le_succ (fun k => costPredicate_fuel_step w p k s)

theorem wpApprox_fuel_mono_nonneg [DecidableEq Var] (p : QProg Var d)
    (P : CQPredicate Var d) (hP : ∀ s, 0 ≤ P s) (s : Store Var) :
    Monotone (fun k => wpApprox p k P s) :=
  monotone_nat_of_le_succ (fun k => wpApprox_fuel_step_nonneg p k P hP s)

theorem costPredicate_loop_le_unroll [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (k : Nat) :
    ∀ s, costPredicate w (.qwhile g body) k s ≤ costPredicate w (loopUnroll g body k) k s := by
  induction k with
  | zero => intro s; exact le_rfl
  | succ k ih =>
      intro s
      rw [costPredicate_while_succ]
      change (if g s then costPredicate w body k s + wpApprox body k (costPredicate w (.qwhile g body) k) s else 0) ≤
        (if g s then costPredicate w body (k + 1) s +
          wpApprox body (k + 1) (costPredicate w (loopUnroll g body k) (k + 1)) s else 0)
      split
      · apply add_le_add (costPredicate_fuel_step w body k s)
        apply le_trans (wpApprox_mono body k ih s)
        apply le_trans (wpApprox_mono body k (costPredicate_fuel_step w (loopUnroll g body k) k) s)
        exact wpApprox_fuel_step_nonneg body k _ (costPredicate_nonnegative w (loopUnroll g body k) (k + 1)) s
      · exact le_rfl

theorem costPredicate_unroll_le_loop [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (n k : Nat) :
    ∀ s, costPredicate w (loopUnroll g body n) k s ≤ costPredicate w (.qwhile g body) (n + k) s := by
  induction n with
  | zero =>
      intro s
      simpa [loopUnroll, costPredicate] using costPredicate_nonnegative w (.qwhile g body) k s
  | succ n ih =>
      intro s
      rw [Nat.succ_add, costPredicate_while_succ]
      change (if g s then costPredicate w body k s + wpApprox body k (costPredicate w (loopUnroll g body n) k) s else 0) ≤ _
      split
      · apply add_le_add (costPredicate_fuel_mono w body s (Nat.le_add_left k n))
        apply le_trans (wpApprox_mono body k ih s)
        exact wpApprox_fuel_mono_nonneg body _ (costPredicate_nonnegative w (.qwhile g body) (n + k)) s
          (Nat.le_add_left k n)
      · exact le_rfl

noncomputable def approximateStateCost [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) (S : CQState Var d) : ENNReal :=
  ∑' s, ENNReal.ofReal (expectedCostApprox w p k (s, (S.density s).matrix))

theorem expectedCost_eq_iSup_approx [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : CQState Var d) : expectedCost w p S = ⨆ k, approximateStateCost w p k S := by
  apply ennreal_tsum_iSup_nat
  intro s i j hij
  exact ENNReal.ofReal_le_ofReal (expectedCostApprox_mono w p (s, (S.density s).matrix) (S.density s).positive hij)

theorem approximateStateCost_le [DecidableEq Var] (w : CostModel d) (a b : QProg Var d)
    (j k : Nat) (S : CQState Var d) (h : ∀ s, costPredicate w a j s ≤ costPredicate w b k s) :
    approximateStateCost w a j S ≤ approximateStateCost w b k S := by
  apply ENNReal.tsum_le_tsum
  intro s
  apply ENNReal.ofReal_le_ofReal
  rw [expectedCostApprox_pairing, expectedCostApprox_pairing]
  exact pairing_mono (h s) (S.density s).positive

theorem approximateStateCost_le_expected [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) (S : CQState Var d) : approximateStateCost w p k S ≤ expectedCost w p S := by
  rw [expectedCost_eq_iSup_approx]
  exact le_iSup (fun j => approximateStateCost w p j S) k

/-- This cofinality proof rules out spurious larger solutions of the loop
cost recurrence, which alone would not establish the least solution. -/
theorem expectedCost_while_eq_iSup_unroll [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (S : CQState Var d) :
    expectedCost w (.qwhile g body) S = ⨆ n, expectedCost w (loopUnroll g body n) S := by
  apply le_antisymm
  · rw [expectedCost_eq_iSup_approx]
    apply iSup_le
    intro k
    apply le_iSup_of_le k
    exact (approximateStateCost_le w _ _ k k S (costPredicate_loop_le_unroll w g body k)).trans
      (approximateStateCost_le_expected w (loopUnroll g body k) k S)
  · apply iSup_le
    intro n
    rw [expectedCost_eq_iSup_approx]
    apply iSup_le
    intro k
    exact (approximateStateCost_le w _ _ k (n + k) S (costPredicate_unroll_le_loop w g body n k)).trans
      (approximateStateCost_le_expected w (.qwhile g body) (n + k) S)

end QuantumLeanLeap.GoogleQHL
