import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.Oracle

/-! A complete exact address-state baseline for N=4, k=1 and any m>0.
The uniform preparation and diffusion do not depend on the unknown mark.
This is not the paper's large-N, multi-target optimisation. -/
namespace QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
open scoped BigOperators
open Matrix
noncomputable section

def singletonMark (target : Fin 4) (x : Fin 4) : Bool := decide (x = target)

def uniformFour : Fin 4 → Complex := fun _ => 1 / 2

/-- H tensor H, independent of the unknown marked element. -/
def prepareFour : Matrix (Fin 4) (Fin 4) Complex :=
  (1 / 2 : Complex) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

theorem prepareFour_unitary : prepareFour.conjTranspose * prepareFour = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [prepareFour, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      map_ofNat, Fin.succ, Fin.ofNat, Fin.mk.injEq]

theorem prepareFour_zero :
    prepareFour *ᵥ (fun x => if x = 0 then 1 else 0) = uniformFour := by
  funext x
  fin_cases x <;> norm_num [prepareFour, uniformFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    map_ofNat, Fin.succ, Fin.ofNat, Fin.mk.injEq]

def diffusionFour : Matrix (Fin 4) (Fin 4) Complex :=
  fun x y => 1 / 2 - if x = y then 1 else 0

theorem diffusionFour_unitary : diffusionFour.conjTranspose * diffusionFour = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diffusionFour, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      map_ofNat, Fin.succ, Fin.ofNat, Fin.mk.injEq]

theorem uniformFour_normalized : ∑ x : Fin 4, Complex.normSq (uniformFour x) = 1 := by
  norm_num [uniformFour, Fin.sum_univ_succ, Complex.normSq_apply]

/-- One actual diffusion following the phase oracle produces the unknown
marked basis state, for all four possible oracle instances. -/
theorem groverFour_exact (target : Fin 4) :
    diffusionFour *ᵥ (fun x => sign (singletonMark target x) * uniformFour x) =
      (fun x => if x = target then 1 else 0) := by
  funext x
  fin_cases target <;> fin_cases x <;>
    norm_num [Matrix.mulVec, dotProduct, diffusionFour, sign, singletonMark,
      uniformFour, Fin.sum_univ_succ, map_ofNat, Fin.succ, Fin.ofNat, Fin.mk.injEq]

noncomputable def tensorPower {N : Nat} (m : Nat) (A : Matrix (Fin N) (Fin N) Complex) :
    Matrix (Address N m) (Address N m) Complex := fun x y => ∏ j, A (x j) (y j)

noncomputable def productState {N : Nat} (m : Nat) (v : Fin N → Complex) :
    Address N m → Complex := fun x => ∏ j, v (x j)

theorem tensorPower_mulVec {N m : Nat} (A : Matrix (Fin N) (Fin N) Complex)
    (v : Fin N → Complex) :
    tensorPower m A *ᵥ productState m v = productState m (A *ᵥ v) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, tensorPower, productState]
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j y => A (x j) y * v y)).symm

theorem phase_productState {N m : Nat} (marked : Fin N → Bool) (v : Fin N → Complex) :
    phaseAction marked (productState m v) = productState m (fun x => sign (marked x) * v x) := by
  funext x
  simp only [phaseAction, productState, Finset.prod_mul_distrib]

theorem productState_delta {N m : Nat} (a : Fin N) :
    productState m (fun x => if x = a then 1 else 0) =
      (fun x => if x = (fun _ => a) then 1 else 0) := by
  funext x
  simp only [productState]
  by_cases hx : x = fun _ => a
  · subst x
    simp
  · have h : ∃ j, x j ≠ a := by
      by_contra! hn
      exact hx (funext hn)
    obtain ⟨j, hj⟩ := h
    rw [if_neg hx]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem tensorPower_mul {N m : Nat} (A B : Matrix (Fin N) (Fin N) Complex) :
    tensorPower m (A * B) = tensorPower m A * tensorPower m B := by
  ext x z
  simp only [tensorPower, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun j y => A (x j) y * B y (z j))

theorem tensorPower_conjTranspose {N m : Nat} (A : Matrix (Fin N) (Fin N) Complex) :
    tensorPower m A.conjTranspose = (tensorPower m A).conjTranspose := by
  ext x y
  simp [tensorPower, Matrix.conjTranspose_apply]

theorem tensorPower_one (N m : Nat) : tensorPower m (1 : Matrix (Fin N) (Fin N) Complex) = 1 := by
  ext x y
  simp only [tensorPower, Matrix.one_apply]
  by_cases h : x = y
  · subst y
    simp
  · rw [if_neg h]
    have hn : ∃ j, x j ≠ y j := by
      by_contra! hn
      exact h (funext hn)
    obtain ⟨j, hj⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem tensorPower_unitary {N m : Nat} (A : Matrix (Fin N) (Fin N) Complex)
    (hA : A.conjTranspose * A = 1) :
    (tensorPower m A).conjTranspose * tensorPower m A = 1 := by
  rw [← tensorPower_conjTranspose, ← tensorPower_mul, hA, tensorPower_one]

noncomputable def exactFourOutput (m : Nat) (target : Fin 4) : Address 4 m → Complex :=
  tensorPower m diffusionFour *ᵥ phaseAction (singletonMark target) (productState m uniformFour)

theorem exactFourOutput_eq (m : Nat) (target : Fin 4) :
    exactFourOutput m target = fun x => if x = (fun _ => target) then 1 else 0 := by
  rw [exactFourOutput, phase_productState, tensorPower_mulVec, groverFour_exact]
  exact productState_delta target

theorem exactFourOutput_normalized (m : Nat) (target : Fin 4) :
    ∑ x : Address 4 m, Complex.normSq (exactFourOutput m target x) = 1 := by
  rw [exactFourOutput_eq]
  simp

end
end QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
