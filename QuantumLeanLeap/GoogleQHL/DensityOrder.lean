import QuantumLeanLeap.GoogleQHL.Omega

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator
variable {d : Nat}

theorem positive_norm_le_trace {A : Operator d} (hA : A.PosSemidef) : ‖A‖ ≤ A.trace.re := by
  have ht : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have hs : ∀ r ∈ spectrum Real A, r ≤ A.trace.re := by
    intro r hr
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hr
    obtain ⟨i, rfl⟩ := hr
    rw [ht]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap A
    (show 0 ≤ A.trace.re from (RCLike.nonneg_iff.mp hA.trace_nonneg).1) hA.nonneg).mpr
  exact le_algebraMap_of_spectrum_le hs

theorem PartialDensity.isEffect (rho : PartialDensity d) : IsEffect rho.matrix :=
  ⟨rho.positive.nonneg, (CStarAlgebra.norm_le_one_iff_of_nonneg rho.matrix rho.positive.nonneg).mp
    ((positive_norm_le_trace rho.positive).trans rho.trace_le_one)⟩

theorem pairing_comm (A B : Operator d) : pairing A B = pairing B A := by
  unfold pairing
  rw [Matrix.trace_mul_comm]

noncomputable def pairingCLM (E : Operator d) : Operator d →L[Real] Real where
  toFun := pairing E
  map_add' A B := by simp [pairing, Matrix.mul_add, Matrix.trace_add]
  map_smul' c A := by simp [pairing, Matrix.trace_smul]
  cont := by unfold pairing Matrix.trace; fun_prop

theorem pairing_tsum {ι : Type*} (E : Operator d) (f : ι → Operator d) (hf : Summable f) :
    pairing E (∑' i, f i) = ∑' i, pairing E (f i) := (pairingCLM E).map_tsum hf

theorem pairing_smul_right (E A : Operator d) (c : Real) :
    pairing E (c • A) = c * pairing E A := by
  exact (pairingCLM E).map_smul c A

end QuantumLeanLeap.GoogleQHL
