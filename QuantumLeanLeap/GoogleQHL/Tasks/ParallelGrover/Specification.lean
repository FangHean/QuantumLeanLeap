import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Circuit

/-! Independent success predicates and Born-weighted round accounting.
The present witness covers n=2, k=1, m>0, not the paper's full parameter grid. -/
namespace QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
open scoped BigOperators
open Matrix
noncomputable section
variable {N m : Nat}

def markedSet (marked : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter fun x => marked x

/-- The paper's promised domain; the power-of-two benchmark grid is an
evaluation restriction, separate from validity of a search instance. -/
structure Instance where
  n : Nat
  width_positive : 0 < n
  slots : Nat
  slots_positive : 0 < slots
  k : Nat
  marked : Fin (2 ^ n) → Bool
  count_eq : (markedSet marked).card = k
  targets_positive : 0 < k

def acceptsAny (marked : Fin N → Bool) (first : Fin m) (x : Address N m) : Prop :=
  marked (x first) = true

def acceptsAll (marked : Fin N → Bool) (x : Address N m) : Prop :=
  Finset.univ.image x = markedSet marked

instance (marked : Fin N → Bool) (first : Fin m) : DecidablePred (acceptsAny marked first) :=
  fun x => inferInstanceAs (Decidable (marked (x first) = true))

instance (marked : Fin N → Bool) : DecidablePred (acceptsAll (m := m) marked) :=
  fun x => inferInstanceAs (Decidable (Finset.univ.image x = markedSet marked))

def outputVector [NeZero N] (c : Circuit N m) (marked : Fin N → Bool) : Address N m → Complex :=
  c.matrix marked *ᵥ (fun x => if x = (fun _ => 0) then 1 else 0)

def outcomeWeight [NeZero N] (c : Circuit N m) (marked : Fin N → Bool) (x : Address N m) : Real :=
  Complex.normSq (outputVector c marked x)

def successWeight [NeZero N] (c : Circuit N m) (marked : Fin N → Bool)
    (accepts : Address N m → Prop) [DecidablePred accepts] : Real :=
  ∑ x, if accepts x then outcomeWeight c marked x else 0

def expectedRounds [NeZero N] (c : Circuit N m) (marked : Fin N → Bool) : Real :=
  ∑ x, outcomeWeight c marked x * c.rounds

theorem exactFour_weight (m : Nat) (target : Fin 4) (x : Address 4 m) :
    outcomeWeight (exactFourCircuit m) (singletonMark target) x =
      if x = (fun _ => target) then 1 else 0 := by
  unfold outcomeWeight outputVector
  rw [exactFourCircuit_output]
  split <;> simp_all

theorem exactFour_terminates (m : Nat) (target : Fin 4) :
    ∑ x, outcomeWeight (exactFourCircuit m) (singletonMark target) x = 1 := by
  simp only [exactFour_weight]
  simp

theorem markedSet_singleton (target : Fin 4) : markedSet (singletonMark target) = {target} := by
  ext x
  simp [markedSet, singletonMark]

def fourInstance (m : Nat) (hm : 0 < m) (target : Fin 4) : Instance where
  n := 2
  width_positive := by decide
  slots := m
  slots_positive := hm
  k := 1
  marked := singletonMark target
  count_eq := by rw [markedSet_singleton]; simp
  targets_positive := by decide

theorem exactFour_findAny (m : Nat) [NeZero m] (target : Fin 4) :
    successWeight (exactFourCircuit m) (singletonMark target)
      (acceptsAny (singletonMark target) 0) = 1 := by
  classical
  unfold successWeight
  rw [Finset.sum_eq_single (fun _ => target)]
  · simp [exactFour_weight, acceptsAny, singletonMark]
  · intro x _ hx
    simp [exactFour_weight, hx]
  · simp

theorem exactFour_findAll (m : Nat) [NeZero m] (target : Fin 4) :
    successWeight (exactFourCircuit m) (singletonMark target)
      (acceptsAll (singletonMark target)) = 1 := by
  classical
  unfold successWeight
  rw [Finset.sum_eq_single (fun _ => target)]
  · have him : Finset.univ.image (fun _ : Fin m => target) = {target} := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · intro hy
        exact ⟨0, hy.symm⟩
    simp [exactFour_weight, acceptsAll, markedSet_singleton, him]
  · intro x _ hx
    simp [exactFour_weight, hx]
  · simp

theorem exactFour_expectedRounds (m : Nat) (target : Fin 4) :
    expectedRounds (exactFourCircuit m) (singletonMark target) = 1 := by
  simp [expectedRounds, exactFourCircuit_rounds, exactFour_terminates]

/-- One fixed circuit, all unknown singleton targets, deterministic termination,
both output tasks and exact expected query depth. -/
theorem exactFour_contract (m : Nat) [NeZero m] (target : Fin 4) :
    (∑ x, outcomeWeight (exactFourCircuit m) (singletonMark target) x) = 1 ∧
    successWeight (exactFourCircuit m) (singletonMark target)
      (acceptsAny (singletonMark target) 0) = 1 ∧
    successWeight (exactFourCircuit m) (singletonMark target)
      (acceptsAll (singletonMark target)) = 1 ∧
    expectedRounds (exactFourCircuit m) (singletonMark target) = 1 :=
  ⟨exactFour_terminates m target, exactFour_findAny m target,
    exactFour_findAll m target, exactFour_expectedRounds m target⟩

end
end QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
