import QuantumLeanLeap.GoogleQHL.DensityOrder
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace QuantumLeanLeap.GoogleQHL
open scoped Topology
open Filter

/-- A uniform total-mass bound passes to a pointwise nonnegative limit,
including over an uncountable index type. No enumeration is assumed. -/
theorem summable_limit_of_mass_bound {ι : Type*} (f : Nat → ι → Real) (g : ι → Real)
    (hf : ∀ n i, 0 ≤ f n i) (hs : ∀ n, Summable (f n))
    (ht : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i)))
    (C : Real) (hb : ∀ n, ∑' i, f n i ≤ C) : Summable g ∧ (∑' i, g i) ≤ C := by
  have hg : ∀ i, 0 ≤ g i := fun i => ge_of_tendsto' (ht i) (fun n => hf n i)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, g i ≤ C := by
    intro s
    apply le_of_tendsto' (tendsto_finsetSum s (fun i _ => ht i))
    intro n
    exact ((hs n).sum_le_tsum s (fun i _ => hf n i)).trans (hb n)
  exact ⟨summable_of_sum_le hg hfin, Real.tsum_le_of_sum_le hg hfin⟩

/-- Monotone convergence for nonnegative real series with bounded total mass. -/
theorem tsum_limit_eq_iSup {ι : Type*} (f : Nat → ι → Real) (g : ι → Real)
    (hf : ∀ n i, 0 ≤ f n i) (hs : ∀ n, Summable (f n))
    (hm : ∀ i, Monotone (fun n => f n i))
    (ht : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i)))
    (C : Real) (hb : ∀ n, ∑' i, f n i ≤ C) :
    (∑' i, g i) = ⨆ n : Nat, ∑' i, f n i := by
  have hg := (summable_limit_of_mass_bound f g hf hs ht C hb).1
  have hbounded : BddAbove (Set.range (fun n => ∑' i, f n i)) :=
    ⟨C, by rintro _ ⟨n, rfl⟩; exact hb n⟩
  apply le_antisymm
  · exact (summable_limit_of_mass_bound f g hf hs ht _ (fun n => le_ciSup hbounded n)).2
  · apply ciSup_le
    intro n
    exact Summable.tsum_le_tsum (fun i => (hm i).ge_of_tendsto (ht i) n) (hs n) hg

end QuantumLeanLeap.GoogleQHL
