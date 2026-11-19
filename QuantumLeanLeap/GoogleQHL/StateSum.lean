import QuantumLeanLeap.GoogleQHL.Summation

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator
variable {Var : Type} {d : Nat} {ι : Type*}

theorem CQState.mass_nonnegative (S : CQState Var d) : 0 ≤ S.mass := by
  rw [← S.trace_hasSum.tsum_eq]
  exact tsum_nonneg (fun s => (RCLike.nonneg_iff.mp (S.density s).positive.trace_nonneg).1)

theorem CQState.trace_le_mass (S : CQState Var d) (s : Store Var) :
    (S.density s).matrix.trace.re ≤ S.mass := by
  rw [← S.trace_hasSum.tsum_eq]
  exact S.trace_hasSum.summable.le_tsum s
    (fun t _ => (RCLike.nonneg_iff.mp (S.density t).positive.trace_nonneg).1)

theorem stateSum_matrix_summable (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass))
    (s : Store Var) : Summable (fun i => ((S i).density s).matrix) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _)
    (fun i => (positive_norm_le_trace ((S i).density s).positive).trans ((S i).trace_le_mass s)) hs

theorem stateSum_trace_summable (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass)) :
    Summable (fun pair : ι × Store Var => ((S pair.1).density pair.2).matrix.trace.re) := by
  have hnonneg : ∀ pair : ι × Store Var, 0 ≤ ((S pair.1).density pair.2).matrix.trace.re :=
    fun pair => (RCLike.nonneg_iff.mp ((S pair.1).density pair.2).positive.trace_nonneg).1
  apply (summable_prod_of_nonneg hnonneg).mpr
  refine ⟨fun i => (S i).trace_hasSum.summable, ?_⟩
  simpa only [fun i => (S i).trace_hasSum.tsum_eq] using hs

theorem stateSum_trace (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass)) (s : Store Var) :
    (∑' i, ((S i).density s).matrix).trace.re = ∑' i, ((S i).density s).matrix.trace.re := by
  simpa only [pairing_one] using pairing_tsum 1 _ (stateSum_matrix_summable S hs s)

noncomputable def stateSum (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass))
    (hb : (∑' i, (S i).mass) ≤ 1) : CQState Var d where
  density s := {
    matrix := ∑' i, ((S i).density s).matrix
    positive := Matrix.nonneg_iff_posSemidef.mp (tsum_nonneg (fun i => ((S i).density s).positive.nonneg))
    trace_le_one := by
      rw [stateSum_trace S hs s]
      exact (Summable.tsum_le_tsum (fun i => (S i).trace_le_mass s)
        ((stateSum_trace_summable S hs).prod_symm.prod_factor s) hs).trans hb }
  mass := ∑' i, (S i).mass
  trace_hasSum := by
    have htrace := (stateSum_trace_summable S hs).prod_symm.prod.hasSum
    change HasSum (fun s => ∑' i, ((S i).density s).matrix.trace.re)
      (∑' s, ∑' i, ((S i).density s).matrix.trace.re) at htrace
    have he : (∑' s, ∑' i, ((S i).density s).matrix.trace.re) = ∑' i, (S i).mass := by
      rw [Summable.tsum_comm (f := fun i s => ((S i).density s).matrix.trace.re)
        (stateSum_trace_summable S hs)]
      simp only [fun i => (S i).trace_hasSum.tsum_eq]
    simpa only [stateSum_trace S hs, he] using htrace
  mass_le_one := hb

theorem expectation_le_mass (S : CQState Var d) (Q : CQAssertion Var d) : expectation S Q ≤ S.mass := by
  have hp : ∀ s, pairing (Q s).matrix (S.density s).matrix ≤ (S.density s).matrix.trace.re :=
    fun s => (pairing_effect_bounds ⟨(Q s).nonnegative, (Q s).le_identity⟩ (S.density s).positive).2
  change (∑' s, pairing (Q s).matrix (S.density s).matrix) ≤ S.mass
  exact (Summable.tsum_le_tsum hp (expectation_summable S Q) S.trace_hasSum.summable).trans_eq
    S.trace_hasSum.tsum_eq

theorem expectation_stateSum (S : ι → CQState Var d) (hs : Summable (fun i => (S i).mass))
    (hb : (∑' i, (S i).mass) ≤ 1) (Q : CQAssertion Var d) :
    expectation (stateSum S hs hb) Q = ∑' i, expectation (S i) Q := by
  have hpair : Summable (fun pair : ι × Store Var =>
      pairing (Q pair.2).matrix ((S pair.1).density pair.2).matrix) := by
    have hp : ∀ pair : ι × Store Var,
        pairing (Q pair.2).matrix ((S pair.1).density pair.2).matrix ≤
          ((S pair.1).density pair.2).matrix.trace.re :=
      fun pair => (pairing_effect_bounds ⟨(Q pair.2).nonnegative, (Q pair.2).le_identity⟩
        ((S pair.1).density pair.2).positive).2
    exact Summable.of_nonneg_of_le
      (fun pair => pairing_nonneg (Q pair.2).nonnegative ((S pair.1).density pair.2).positive)
      hp (stateSum_trace_summable S hs)
  change (∑' s, pairing (Q s).matrix (∑' i, ((S i).density s).matrix)) = _
  simp_rw [pairing_tsum _ _ (stateSum_matrix_summable S hs _)]
  exact Summable.tsum_comm (f := fun i s => pairing (Q s).matrix ((S i).density s).matrix) hpair

end QuantumLeanLeap.GoogleQHL
