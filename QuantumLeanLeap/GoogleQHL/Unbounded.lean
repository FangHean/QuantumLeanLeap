import QuantumLeanLeap.GoogleQHL.Omega

/-! Unbounded weakest preconditions, defined by the operator least upper bound
of the finite operational approximants. Total-correctness triples use the
independently defined limit of forward execution expectations. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology
variable {Var : Type} {d : Nat}

noncomputable def wp [DecidableEq Var] (p : QProg Var d)
    (Q : CQAssertion Var d) : CQAssertion Var d := fun s =>
  effectSup (fun k => wpApprox p k Q.toPredicate s)
    (fun k => wpApprox_effect p k Q.toPredicate (fun t => ⟨(Q t).nonnegative, (Q t).le_identity⟩) s)
    (wpApprox_fuel_mono p Q.toPredicate (fun t => ⟨(Q t).nonnegative, (Q t).le_identity⟩) s)

theorem wp_isLUB [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d) (s : Store Var) :
    IsLUB (Set.range (fun k => wpApprox p k Q.toPredicate s)) (wp p Q s).matrix :=
  effectSup_isLUB _ _ _

theorem wpApprox_le_wp [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d)
    (k : Nat) (s : Store Var) : wpApprox p k Q.toPredicate s ≤ (wp p Q s).matrix :=
  (wp_isLUB p Q s).1 (Set.mem_range_self k)

theorem wp_le [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d)
    (s : Store Var) (B : Operator d) (h : ∀ k, wpApprox p k Q.toPredicate s ≤ B) :
    (wp p Q s).matrix ≤ B :=
  (wp_isLUB p Q s).2 (by rintro _ ⟨k, rfl⟩; exact h k)

/-- Forward/backward duality for arbitrarily many loop iterations, including
nested loops and loss of trace through abort or nontermination. -/
theorem expect_wp [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d)
    (input : Branch Var d) (hr : input.2.PosSemidef) :
    limitExpectation p Q.toPredicate input = pairing (wp p Q input.1).matrix input.2 := by
  rw [expect_wp_limit]
  exact (pairing_effectSup _ _ _ input.2 hr).symm

def Hoare [DecidableEq Var] (P : CQAssertion Var d) (p : QProg Var d)
    (Q : CQAssertion Var d) : Prop :=
  ∀ (s : Store Var) (rho : Operator d), rho.PosSemidef →
    pairing (P s).matrix rho ≤ limitExpectation p Q.toPredicate (s, rho)

theorem hoare_iff [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d) :
    Hoare P p Q ↔ ∀ s, (P s).matrix ≤ (wp p Q s).matrix := by
  constructor
  · intro h s
    apply le_of_pairing_le (Matrix.nonneg_iff_posSemidef.mp (P s).nonnegative).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp (wp p Q s).nonnegative).isHermitian
    intro rho hr
    simpa only [expect_wp p Q (s, rho) hr] using h s rho hr
  · intro h s rho hr
    rw [expect_wp p Q (s, rho) hr]
    exact pairing_mono (h s) hr

theorem wp_soundness [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d) :
    Hoare (wp p Q) p Q := (hoare_iff _ _ _).mpr (fun _ => le_rfl)

theorem wp_weakest [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d)
    (h : Hoare P p Q) : ∀ s, (P s).matrix ≤ (wp p Q s).matrix :=
  (hoare_iff _ _ _).mp h

theorem wp_mono [DecidableEq Var] (p : QProg Var d) (P Q : CQAssertion Var d)
    (h : ∀ s, (P s).matrix ≤ (Q s).matrix) :
    ∀ s, (wp p P s).matrix ≤ (wp p Q s).matrix := by
  intro s
  apply wp_le
  intro k
  exact (wpApprox_mono p k h s).trans (wpApprox_le_wp p Q k s)

theorem hoare_consequence [DecidableEq Var] (P P' Q Q' : CQAssertion Var d)
    (p : QProg Var d) (hp : ∀ s, (P' s).matrix ≤ (P s).matrix)
    (hq : ∀ s, (Q s).matrix ≤ (Q' s).matrix) (h : Hoare P p Q) : Hoare P' p Q' :=
  (hoare_iff _ _ _).mpr (fun s =>
    (hp s).trans (((hoare_iff _ _ _).mp h s).trans (wp_mono p Q Q' hq s)))

end QuantumLeanLeap.GoogleQHL
