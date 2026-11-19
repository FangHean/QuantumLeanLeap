import QuantumLeanLeap.GoogleQHL.Limits
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences

/-! Increasing sequences of effects have a least upper bound in the Löwner
order. Compactness is used only to construct the operator; its expectation
against every positive input is proved to be the limit of the expectations. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator
open Filter
variable {d : Nat}

theorem continuous_pairing_left (rho : Operator d) :
    Continuous (fun E : Operator d => pairing E rho) := by
  unfold pairing Matrix.trace
  fun_prop

theorem effectChain_cluster (E : Nat → Operator d) (hE : ∀ n, IsEffect (E n)) :
    ∃ A : Operator d, IsEffect A ∧ ∃ φ : Nat → Nat,
      StrictMono φ ∧ Tendsto (E ∘ φ) atTop (𝓝 A) := by
  have hb : ∀ n, E n ∈ Metric.closedBall (0 : Operator d) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg (E n) (hE n).1).mpr (hE n).2
  obtain ⟨A, _, φ, hφ, ht⟩ := (isCompact_closedBall (0 : Operator d) 1).tendsto_subseq hb
  refine ⟨A, ⟨?_, ?_⟩, φ, hφ, ht⟩
  · exact ge_of_tendsto' ht (fun n => (hE (φ n)).1)
  · exact le_of_tendsto' ht (fun n => (hE (φ n)).2)

theorem effectChain_exists_lub (E : Nat → Operator d) (hE : ∀ n, IsEffect (E n))
    (hmono : Monotone E) :
    ∃ A : Operator d, IsEffect A ∧ IsLUB (Set.range E) A ∧
      ∀ rho : Operator d, rho.PosSemidef →
        pairing A rho = ⨆ n : Nat, pairing (E n) rho := by
  obtain ⟨A, hA, φ, hφ, ht⟩ := effectChain_cluster E hE
  refine ⟨A, hA, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hmono (hφ.id_le n)).trans ((hmono.comp hφ.monotone).ge_of_tendsto ht n)
  · intro B hB
    exact le_of_tendsto' ht (fun n => hB (Set.mem_range_self (φ n)))
  · intro rho hr
    have hm : Monotone (fun n => pairing (E n) rho) :=
      fun _ _ hab => pairing_mono (hmono hab) hr
    have hb : BddAbove (Set.range (fun n => pairing (E n) rho)) := by
      refine ⟨rho.trace.re, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (pairing_effect_bounds (hE n) hr).2
    exact tendsto_nhds_unique ((continuous_pairing_left rho).tendsto A |>.comp ht)
      ((tendsto_atTop_ciSup hm hb).comp hφ.tendsto_atTop)

noncomputable def effectSup (E : Nat → Operator d) (hE : ∀ n, IsEffect (E n))
    (hmono : Monotone E) : Observable d :=
  let A := Classical.choose (effectChain_exists_lub E hE hmono)
  let h := Classical.choose_spec (effectChain_exists_lub E hE hmono)
  ⟨A, h.1.1, h.1.2⟩

theorem effectSup_isLUB (E : Nat → Operator d) (hE : ∀ n, IsEffect (E n))
    (hmono : Monotone E) : IsLUB (Set.range E) (effectSup E hE hmono).matrix :=
  (Classical.choose_spec (effectChain_exists_lub E hE hmono)).2.1

theorem pairing_effectSup (E : Nat → Operator d) (hE : ∀ n, IsEffect (E n))
    (hmono : Monotone E) (rho : Operator d) (hr : rho.PosSemidef) :
    pairing (effectSup E hE hmono).matrix rho = ⨆ n : Nat, pairing (E n) rho :=
  (Classical.choose_spec (effectChain_exists_lub E hE hmono)).2.2 rho hr

end QuantumLeanLeap.GoogleQHL
