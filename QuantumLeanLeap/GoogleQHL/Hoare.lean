import QuantumLeanLeap.GoogleQHL.Expectation

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem pairing_rankOne (E : Operator d) (x : Fin d → Complex) :
    pairing E (Matrix.vecMulVec x (star x)) =
      (star x ⬝ᵥ E.mulVec x).re := by
  unfold pairing
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_comm, mul_assoc]

/-- Positive matrix tests separate Hermitian operators in the Löwner order. -/
theorem le_of_pairing_le {A B : Operator d} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ rho : Operator d, rho.PosSemidef → pairing A rho ≤ pairing B rho) : A ≤ B := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
  intro x
  apply RCLike.nonneg_iff.mpr
  constructor
  · have hp := h (Matrix.vecMulVec x (star x)) (Matrix.posSemidef_vecMulVec_self_star x)
    have hd : 0 ≤ pairing (B - A) (Matrix.vecMulVec x (star x)) := by
      simpa [pairing, Matrix.sub_mul, Matrix.trace_sub, sub_nonneg] using hp
    simpa [pairing_rankOne] using hd
  · exact (hB.sub hA).im_star_dotProduct_mulVec_self x

/-- Total-correctness contract for the bounded execution. Aborted or truncated
histories contribute zero, so nontermination is NOT counted as success.
Testing all positive unnormalized matrices avoids a gratuitous normalization
side condition; linearity makes this equivalent to testing substates. -/
def HoareBounded [DecidableEq Var] (P : CQAssertion Var d) (p : QProg Var d)
    (fuel : Nat) (Q : CQAssertion Var d) : Prop :=
  ∀ (s : Store Var) (rho : Operator d), rho.PosSemidef →
    pairing (P s).matrix rho ≤ branchExpectation Q.toPredicate (interpApprox p fuel (s, rho))

/-- Characterization by the actual weakest precondition in Löwner order. -/
theorem hoareBounded_iff [DecidableEq Var] (P Q : CQAssertion Var d)
    (p : QProg Var d) (fuel : Nat) :
    HoareBounded P p fuel Q ↔ ∀ s, (P s).matrix ≤ (wpBounded p fuel Q s).matrix := by
  constructor
  · intro h s
    apply le_of_pairing_le (Matrix.nonneg_iff_posSemidef.mp (P s).nonnegative).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp (wpBounded p fuel Q s).nonnegative).isHermitian
    intro rho hr
    simpa only [expect_wpApprox, wpBounded] using h s rho hr
  · intro h s rho hr
    rw [expect_wpApprox]
    exact pairing_mono (h s) hr

theorem wpBounded_soundness [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (Q : CQAssertion Var d) : HoareBounded (wpBounded p fuel Q) p fuel Q :=
  (hoareBounded_iff _ _ _ _).mpr (fun _ => le_rfl)

theorem wpBounded_weakest [DecidableEq Var] (P Q : CQAssertion Var d)
    (p : QProg Var d) (fuel : Nat) (h : HoareBounded P p fuel Q) :
    ∀ s, (P s).matrix ≤ (wpBounded p fuel Q s).matrix :=
  (hoareBounded_iff _ _ _ _).mp h

theorem hoareBounded_seq [DecidableEq Var] (P R Q : CQAssertion Var d)
    (a b : QProg Var d) (fuel : Nat)
    (ha : HoareBounded P a fuel R) (hb : HoareBounded R b fuel Q) :
    HoareBounded P (.seq a b) fuel Q := by
  apply (hoareBounded_iff _ _ _ _).mpr
  intro s
  exact ((hoareBounded_iff _ _ _ _).mp ha s).trans
    (wpApprox_mono a fuel ((hoareBounded_iff _ _ _ _).mp hb) s)

theorem hoareBounded_consequence [DecidableEq Var] (P P' Q Q' : CQAssertion Var d)
    (p : QProg Var d) (fuel : Nat)
    (hp : ∀ s, (P' s).matrix ≤ (P s).matrix)
    (hq : ∀ s, (Q s).matrix ≤ (Q' s).matrix) (h : HoareBounded P p fuel Q) :
    HoareBounded P' p fuel Q' := by
  apply (hoareBounded_iff _ _ _ _).mpr
  intro s
  exact (hp s).trans (((hoareBounded_iff _ _ _ _).mp h s).trans (wpApprox_mono p fuel hq s))

end QuantumLeanLeap.GoogleQHL
