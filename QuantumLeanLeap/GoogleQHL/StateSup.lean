import QuantumLeanLeap.GoogleQHL.Summation
import QuantumLeanLeap.GoogleQHL.StateBridge

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology
open Filter
variable {Var : Type} {d : Nat}

noncomputable def densitySup (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => (S n).density s |>.matrix)) (s : Store Var) : PartialDensity d where
  matrix := (effectSup (fun n => ((S n).density s).matrix)
    (fun n => ((S n).density s).isEffect) (hmono s)).matrix
  positive := Matrix.nonneg_iff_posSemidef.mp (effectSup _ _ _).nonnegative
  trace_le_one := by
    have he := pairing_effectSup (fun n => ((S n).density s).matrix)
      (fun n => ((S n).density s).isEffect) (hmono s) (1 : Operator d) Matrix.PosSemidef.one
    simp only [pairing, Matrix.mul_one] at he
    rw [he]
    exact ciSup_le (fun n => ((S n).density s).trace_le_one)

theorem densitySup_pairing_tendsto (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => ((S n).density s).matrix))
    (s : Store Var) (E : Operator d) (hE : E.PosSemidef) :
    Tendsto (fun n => pairing E ((S n).density s).matrix)
      atTop (𝓝 (pairing E (densitySup S hmono s).matrix)) := by
  have he := pairing_effectSup (fun n => ((S n).density s).matrix)
    (fun n => ((S n).density s).isEffect) (hmono s) E hE
  change Tendsto _ atTop (𝓝 (pairing E (effectSup (fun n => ((S n).density s).matrix)
    (fun n => ((S n).density s).isEffect) (hmono s)).matrix))
  rw [pairing_comm E, he]
  simp_rw [pairing_comm E]
  apply tendsto_atTop_ciSup
  · intro a b hab
    exact pairing_mono (hmono s hab) hE
  · refine ⟨E.trace.re, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (pairing_effect_bounds ((S n).density s).isEffect hE).2

theorem densitySup_trace_tendsto (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => ((S n).density s).matrix)) (s : Store Var) :
    Tendsto (fun n => ((S n).density s).matrix.trace.re) atTop
      (𝓝 ((densitySup S hmono s).matrix.trace.re)) := by
  simpa only [pairing_one] using densitySup_pairing_tendsto S hmono s 1 Matrix.PosSemidef.one

theorem densitySup_trace_summable_bound (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => ((S n).density s).matrix)) (C : Real)
    (hb : ∀ n, (S n).mass ≤ C) :
    Summable (fun s => (densitySup S hmono s).matrix.trace.re) ∧
      (∑' s, (densitySup S hmono s).matrix.trace.re) ≤ C := by
  apply summable_limit_of_mass_bound (fun n s => ((S n).density s).matrix.trace.re)
    (fun s => (densitySup S hmono s).matrix.trace.re)
    (fun n s => (RCLike.nonneg_iff.mp ((S n).density s).positive.trace_nonneg).1)
    (fun n => (S n).trace_hasSum.summable) (densitySup_trace_tendsto S hmono) C
  intro n
  simpa only [(S n).trace_hasSum.tsum_eq] using hb n

noncomputable def stateSup (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => ((S n).density s).matrix)) : CQState Var d where
  density := densitySup S hmono
  mass := ∑' s, (densitySup S hmono s).matrix.trace.re
  trace_hasSum := (densitySup_trace_summable_bound S hmono 1 (fun n => (S n).mass_le_one)).1.hasSum
  mass_le_one := (densitySup_trace_summable_bound S hmono 1 (fun n => (S n).mass_le_one)).2

theorem stateSup_density_isLUB (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => ((S n).density s).matrix)) (s : Store Var) :
    IsLUB (Set.range (fun n => ((S n).density s).matrix)) ((stateSup S hmono).density s).matrix :=
  effectSup_isLUB (fun n => ((S n).density s).matrix)
    (fun n => ((S n).density s).isEffect) (hmono s)

theorem expectation_stateSup (S : Nat → CQState Var d)
    (hmono : ∀ s, Monotone (fun n => ((S n).density s).matrix)) (Q : CQAssertion Var d) :
    expectation (stateSup S hmono) Q = ⨆ n : Nat, expectation (S n) Q := by
  apply tsum_limit_eq_iSup (fun n s => pairing (Q s).matrix ((S n).density s).matrix)
    (fun s => pairing (Q s).matrix (densitySup S hmono s).matrix)
    (fun n s => pairing_nonneg (Q s).nonnegative ((S n).density s).positive)
    (fun n => expectation_summable (S n) Q)
    (fun s a b hab => by
      simpa only [pairing_comm (Q s).matrix] using
        pairing_mono (hmono s hab) (Matrix.nonneg_iff_posSemidef.mp (Q s).nonnegative))
    (fun s => densitySup_pairing_tendsto S hmono s (Q s).matrix
      (Matrix.nonneg_iff_posSemidef.mp (Q s).nonnegative)) 1
  intro n
  exact (expectation_bounds (S n) Q).2

end QuantumLeanLeap.GoogleQHL
