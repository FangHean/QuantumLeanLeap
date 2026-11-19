import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Specification
import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Embedding

namespace QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Regression
open scoped BigOperators
open Matrix
noncomputable section

/-- Uniform sampling without a query has success probability 1/4, not certainty. -/
theorem no_query_not_exact (target : Fin 4) :
    (∑ x : Fin 4, if singletonMark target x then Complex.normSq (uniformFour x) else 0) = 1 / 4 := by
  simp [singletonMark, uniformFour]
  norm_num

def twoMarks (x : Fin 4) : Bool := decide (x = 0 ∨ x = 1)

/-- The same one-iteration schedule is not an exact two-target solver.
This is a scope regression, not a candidate for the general task. -/
theorem two_targets_not_exact :
    (∑ x : Fin 4, if twoMarks x then
      Complex.normSq ((diffusionFour *ᵥ (fun y => sign (twoMarks y) * uniformFour y)) x)
      else 0) = 1 / 2 := by
  norm_num [twoMarks, diffusionFour, uniformFour, sign, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Fin.succ, Fin.ofNat, Fin.mk.injEq, Complex.normSq_apply]

theorem no_slots_cannot_find_all (target : Fin 4) :
    successWeight (exactFourCircuit 0) (singletonMark target)
      (acceptsAll (singletonMark target)) = 0 := by
  simp [successWeight, acceptsAll, markedSet_singleton]

/-- A concrete parallel instance: two query slots still cost one round. -/
theorem two_slots_one_round : (exactFourCircuit 2).rounds = 1 := exactFourCircuit_rounds 2

theorem two_slots_find_all (target : Fin 4) :
    successWeight (exactFourCircuit 2) (singletonMark target)
      (acceptsAll (singletonMark target)) = 1 := exactFour_findAll 2 target

end
end QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Regression
