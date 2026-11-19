import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Circuit

/-! Normalised target ancillas for the reversible-bit-oracle implementation. -/
namespace QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
open scoped BigOperators
open Matrix
noncomputable section
variable {N m : Nat}

def splitQuery : QueryBasis N m ≃ (Fin m → Bool) × Address N m where
  toFun a := (fun j => (a j).1, fun j => (a j).2)
  invFun p j := (p.1 j, p.2 j)
  left_inv _ := rfl
  right_inv _ := rfl

theorem minusLift_normSq (v : Address N m → Complex) :
    ∑ a : QueryBasis N m, Complex.normSq (minusLift v a) =
      (2 : Real) ^ m * ∑ x, Complex.normSq (v x) := by
  have hs (b : Bool) : Complex.normSq (sign b) = 1 := by cases b <;> simp [sign]
  have hp (a : QueryBasis N m) : Complex.normSq (minusLift v a) =
      Complex.normSq (v (fun j => (a j).2)) := by
    simp [minusLift, map_mul, map_prod, hs]
  simp only [hp]
  rw [← splitQuery.symm.sum_comp (fun a : QueryBasis N m =>
    Complex.normSq (v (fun j => (a j).2)))]
  simp [splitQuery, Fintype.sum_prod_type, nsmul_eq_mul]

def normalizedMinusLift (v : Address N m → Complex) : QueryBasis N m → Complex :=
  ((Real.sqrt ((2 : Real) ^ m))⁻¹ : Complex) • minusLift v

/-- The address embedding preserves total Born weight, including entangled inputs. -/
theorem normalizedMinusLift_normSq (v : Address N m → Complex) :
    ∑ a, Complex.normSq (normalizedMinusLift v a) = ∑ x, Complex.normSq (v x) := by
  simp only [normalizedMinusLift, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_inv, Complex.normSq_ofReal, ← Finset.mul_sum, minusLift_normSq]
  have hp : 0 < (2 : Real) ^ m := by positivity
  have hn : Real.sqrt ((2 : Real) ^ m) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp
  rw [Real.sq_sqrt hp.le]

theorem normalized_oracle_kickback (marked : Fin N → Bool) (v : Address N m → Complex) :
    oracle marked *ᵥ normalizedMinusLift v = normalizedMinusLift (phaseAction marked v) := by
  rw [normalizedMinusLift, Matrix.mulVec_smul, oracle_phase_kickback]
  rfl

end
end QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
