import QuantumLeanLeap.GoogleQHL.CostState

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem expectedCost_finiteState [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : FiniteState Var d) : expectedCost w p S.toCQState =
      ⨆ k, ENNReal.ofReal ((S.branches.map (expectedCostApprox w p k)).sum) := by
  unfold expectedCost prefixCostSup
  rw [ennreal_tsum_iSup_nat _ (fun s a b hab => ENNReal.ofReal_le_ofReal
    (expectedCostApprox_mono w p (s, (S.toCQState.density s).matrix) (S.toCQState.density s).positive hab))]
  congr 1
  funext k
  simp only [expectedCostApprox_pairing]
  change (∑' s, ENNReal.ofReal (pairing (costPredicate w p k s) (storeDensity S.branches s))) = _
  have hp : ∀ s, 0 ≤ pairing (costPredicate w p k s) (storeDensity S.branches s) :=
    fun s => pairing_nonneg (costPredicate_nonnegative w p k s) (storeDensity_positive _ S.positive s)
  rw [← ENNReal.ofReal_tsum_of_nonneg hp (pairing_storeDensity_hasSum S.branches (costPredicate w p k)).summable,
    (pairing_storeDensity_hasSum S.branches (costPredicate w p k)).tsum_eq, branchExpectation_eq_sum]
  have he : expectedCostApprox w p k = fun b => pairing (costPredicate w p k b.1) b.2 :=
    funext (fun b => expectedCostApprox_pairing w p k b)
  rw [he]

def continuationCost [DecidableEq Var] (w : CostModel d) (a b : QProg Var d) (j k : Nat)
    (input : Branch Var d) : Real :=
  branchExpectation (costPredicate w b k) (interpApprox a j input)

theorem continuationCost_eq_sum [DecidableEq Var] (w : CostModel d) (a b : QProg Var d) (j k : Nat)
    (input : Branch Var d) : continuationCost w a b j k input =
      ((interpApprox a j input).map (expectedCostApprox w b k)).sum := by
  have he : expectedCostApprox w b k = fun out => pairing (costPredicate w b k out.1) out.2 :=
    funext (fun out => expectedCostApprox_pairing w b k out)
  simp only [continuationCost, branchExpectation_eq_sum, he]

theorem continuationCost_nonneg [DecidableEq Var] (w : CostModel d) (a b : QProg Var d)
    (j k : Nat) (input : Branch Var d) (hr : input.2.PosSemidef) :
    0 ≤ continuationCost w a b j k input := by
  rw [continuationCost, expect_wpApprox]
  exact pairing_nonneg (wpApprox_nonnegative a j _ (costPredicate_nonnegative w b k) input.1) hr

theorem continuationCost_mono_first [DecidableEq Var] (w : CostModel d) (a b : QProg Var d)
    (k : Nat) (input : Branch Var d) (hr : input.2.PosSemidef) :
    Monotone (fun j => continuationCost w a b j k input) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [continuationCost, expect_wpApprox]
  exact pairing_mono (wpApprox_fuel_step_nonneg a j _ (costPredicate_nonnegative w b k) input.1) hr

theorem continuationCost_mono_second [DecidableEq Var] (w : CostModel d) (a b : QProg Var d)
    (j : Nat) (input : Branch Var d) (hr : input.2.PosSemidef) :
    Monotone (fun k => continuationCost w a b j k input) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [continuationCost, expect_wpApprox]
  exact pairing_mono (wpApprox_mono a j (costPredicate_fuel_step w b k) input.1) hr

theorem ennreal_iSup_diagonal (f : Nat → Nat → ENNReal)
    (h₁ : ∀ j, Monotone (fun i => f i j)) (h₂ : ∀ i, Monotone (f i)) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro j
    exact le_iSup_of_le (max i j) ((h₁ j (Nat.le_max_left i j)).trans (h₂ _ (Nat.le_max_right i j)))
  · exact iSup_le (fun k => le_iSup_of_le k (le_iSup _ k))

theorem expectedCost_interpBranch [DecidableEq Var] (w : CostModel d) (a b : QProg Var d)
    (s : Store Var) (rho : PartialDensity d) :
    expectedCost w b (interpBranch a s rho) =
      ⨆ k, ENNReal.ofReal (continuationCost w a b k k (s, rho.matrix)) := by
  rw [interpBranch, expectedCost_stateSup]
  simp only [approxBranchState, expectedCost_finiteState]
  simp only [interpFinite, singleState, List.flatMap_singleton, continuationCost_eq_sum]
  apply ennreal_iSup_diagonal
  · intro k i j hij
    apply ENNReal.ofReal_le_ofReal
    simpa only [continuationCost_eq_sum] using continuationCost_mono_first w a b k (s, rho.matrix) rho.positive hij
  · intro j k l hkl
    apply ENNReal.ofReal_le_ofReal
    simpa only [continuationCost_eq_sum] using continuationCost_mono_second w a b j (s, rho.matrix) rho.positive hkl

theorem prefixCostSup_seq [DecidableEq Var] (w : CostModel d) (a b : QProg Var d)
    (s : Store Var) (rho : PartialDensity d) :
    prefixCostSup w (.seq a b) (s, rho.matrix) =
      prefixCostSup w a (s, rho.matrix) + expectedCost w b (interpBranch a s rho) := by
  rw [expectedCost_interpBranch]
  unfold prefixCostSup
  rw [ENNReal.iSup_add_iSup_of_monotone
    (fun i j hij => ENNReal.ofReal_le_ofReal (expectedCostApprox_mono w a (s, rho.matrix) rho.positive hij))
    (fun i j hij => ENNReal.ofReal_le_ofReal
      ((continuationCost_mono_first w a b i (s, rho.matrix) rho.positive hij).trans
        (continuationCost_mono_second w a b j (s, rho.matrix) rho.positive hij)))]
  congr 1
  funext k
  change ENNReal.ofReal (expectedCostApprox w a k (s, rho.matrix) + _) = _
  rw [← continuationCost_eq_sum]
  exact ENNReal.ofReal_add (expectedCostApprox_nonneg w a k (s, rho.matrix) rho.positive)
    (continuationCost_nonneg w a b k k (s, rho.matrix) rho.positive)

/-- Exact sequential cost equation on arbitrary input CQ-states, allowing
unbounded loops and infinite expected cost in either program. -/
theorem expectedCost_seq [DecidableEq Var] (w : CostModel d) (a b : QProg Var d) (S : CQState Var d) :
    expectedCost w (.seq a b) S = expectedCost w a S + expectedCost w b (interp a S) := by
  calc
    _ = ∑' s, (prefixCostSup w a (s, (S.density s).matrix) + expectedCost w b (interpBranch a s (S.density s))) := by
      apply tsum_congr
      intro s
      exact prefixCostSup_seq w a b s (S.density s)
    _ = _ := by
      rw [ENNReal.tsum_add, interp, expectedCost_stateSum]
      rfl

end QuantumLeanLeap.GoogleQHL
