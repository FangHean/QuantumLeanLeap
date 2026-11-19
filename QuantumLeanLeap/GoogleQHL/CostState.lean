import QuantumLeanLeap.GoogleQHL.StatePrimitives
import QuantumLeanLeap.GoogleQHL.CostLimits

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology
variable {Var : Type} {d : Nat} {ι : Type*}

theorem ennreal_tsum_iSup_nat (f : ι → Nat → ENNReal) (hm : ∀ i, Monotone (f i)) :
    (∑' i, ⨆ k, f i k) = ⨆ k, ∑' i, f i k := by
  simp_rw [ENNReal.tsum_eq_iSup_sum, ENNReal.finsetSum_iSup_of_monotone hm]
  exact iSup_comm

theorem expectedCostApprox_mono_matrix [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) (s : Store Var) {A B : Operator d} (h : A ≤ B) :
    expectedCostApprox w p k (s, A) ≤ expectedCostApprox w p k (s, B) := by
  rw [expectedCostApprox_pairing, expectedCostApprox_pairing, pairing_comm _ A, pairing_comm _ B]
  exact pairing_mono h (Matrix.nonneg_iff_posSemidef.mp (costPredicate_nonnegative w p k s))

theorem prefixCostSup_mono_matrix [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (s : Store Var) {A B : Operator d} (h : A ≤ B) :
    prefixCostSup w p (s, A) ≤ prefixCostSup w p (s, B) := by
  apply iSup_mono
  intro k
  exact ENNReal.ofReal_le_ofReal (expectedCostApprox_mono_matrix w p k s h)

theorem costApprox_stateSup [DecidableEq Var] (w : CostModel d) (p : QProg Var d) (k : Nat)
    (S : Nat → CQState Var d) (hm : ∀ s, Monotone (fun n => ((S n).density s).matrix)) (s : Store Var) :
    ENNReal.ofReal (expectedCostApprox w p k (s, ((stateSup S hm).density s).matrix)) =
      ⨆ n, ENNReal.ofReal (expectedCostApprox w p k (s, ((S n).density s).matrix)) := by
  have ht := densitySup_pairing_tendsto S hm s (costPredicate w p k s)
    (Matrix.nonneg_iff_posSemidef.mp (costPredicate_nonnegative w p k s))
  have ht' : Filter.Tendsto (fun n => ENNReal.ofReal (expectedCostApprox w p k (s, ((S n).density s).matrix)))
      Filter.atTop (𝓝 (ENNReal.ofReal (expectedCostApprox w p k (s, ((stateSup S hm).density s).matrix)))) := by
    simpa only [expectedCostApprox_pairing, stateSup, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  symm
  apply iSup_eq_of_tendsto _ ht'
  intro a b hab
  exact ENNReal.ofReal_le_ofReal (expectedCostApprox_mono_matrix w p k s (hm s hab))

theorem prefixCostSup_stateSup [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : Nat → CQState Var d) (hm : ∀ s, Monotone (fun n => ((S n).density s).matrix)) (s : Store Var) :
    prefixCostSup w p (s, ((stateSup S hm).density s).matrix) =
      ⨆ n, prefixCostSup w p (s, ((S n).density s).matrix) := by
  simp only [prefixCostSup, costApprox_stateSup]
  exact iSup_comm

/-- Expected cost is continuous under increasing state limits, even when the
result is infinite. This is needed for compositional loop-cost reasoning. -/
theorem expectedCost_stateSup [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : Nat → CQState Var d) (hm : ∀ s, Monotone (fun n => ((S n).density s).matrix)) :
    expectedCost w p (stateSup S hm) = ⨆ n, expectedCost w p (S n) := by
  simp only [expectedCost, prefixCostSup_stateSup]
  apply ennreal_tsum_iSup_nat
  intro s a b hab
  exact prefixCostSup_mono_matrix w p s (hm s hab)

theorem costApprox_stateSum [DecidableEq Var] (w : CostModel d) (p : QProg Var d) (k : Nat)
    (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass))
    (hb : (∑' i, (S i).mass) ≤ 1) (s : Store Var) :
    ENNReal.ofReal (expectedCostApprox w p k (s, ((stateSum S hs hb).density s).matrix)) =
      ∑' i, ENNReal.ofReal (expectedCostApprox w p k (s, ((S i).density s).matrix)) := by
  simp only [expectedCostApprox_pairing]
  change ENNReal.ofReal (pairing (costPredicate w p k s) (∑' i, ((S i).density s).matrix)) = _
  rw [pairing_tsum _ _ (stateSum_matrix_summable S hs s)]
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun i => pairing_nonneg (costPredicate_nonnegative w p k s) ((S i).density s).positive)
    ((pairingCLM (costPredicate w p k s)).summable (stateSum_matrix_summable S hs s))

theorem prefixCostSup_stateSum [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass))
    (hb : (∑' i, (S i).mass) ≤ 1) (s : Store Var) :
    prefixCostSup w p (s, ((stateSum S hs hb).density s).matrix) =
      ∑' i, prefixCostSup w p (s, ((S i).density s).matrix) := by
  simp only [prefixCostSup, costApprox_stateSum]
  symm
  apply ennreal_tsum_iSup_nat
  intro i a b hab
  exact ENNReal.ofReal_le_ofReal (expectedCostApprox_mono w p (s, ((S i).density s).matrix)
    ((S i).density s).positive hab)

/-- Additivity over arbitrary summable input mixtures. -/
theorem expectedCost_stateSum [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass))
    (hb : (∑' i, (S i).mass) ≤ 1) :
    expectedCost w p (stateSum S hs hb) = ∑' i, expectedCost w p (S i) := by
  simp only [expectedCost, prefixCostSup_stateSum]
  exact ENNReal.tsum_comm

end QuantumLeanLeap.GoogleQHL
