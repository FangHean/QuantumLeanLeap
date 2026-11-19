import QuantumLeanLeap.GoogleQHL.Unbounded
import QuantumLeanLeap.GoogleQHL.Physical

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology
open Filter
variable {Var : Type} {d : Nat}

theorem wpBounded_pairing_tendsto [DecidableEq Var] (p : QProg Var d)
    (Q : CQAssertion Var d) (s : Store Var) (rho : Operator d) (hr : rho.PosSemidef) :
    Tendsto (fun k => pairing (wpBounded p k Q s).matrix rho)
      atTop (𝓝 (pairing (wp p Q s).matrix rho)) := by
  simpa only [expect_wpApprox, expect_wp p Q (s, rho) hr, wpBounded] using
    expectationApprox_tendsto p Q.toPredicate
      (fun t => ⟨(Q t).nonnegative, (Q t).le_identity⟩) (s, rho) hr

theorem branchExpectation_tendsto (P : Nat → CQPredicate Var d) (Q : CQPredicate Var d)
    (h : ∀ s rho, rho.PosSemidef → Tendsto (fun n => pairing (P n s) rho)
      atTop (𝓝 (pairing (Q s) rho)))
    (outputs : List (Branch Var d)) (hout : ∀ b ∈ outputs, b.2.PosSemidef) :
    Tendsto (fun n => branchExpectation (P n) outputs) atTop (𝓝 (branchExpectation Q outputs)) := by
  induction outputs with
  | nil => exact tendsto_const_nhds
  | cons b rest ih =>
      exact (h b.1 b.2 (hout b (by simp))).add (ih (fun x hx => hout x (by simp [hx])))

theorem wpApprox_pairing_tendsto [DecidableEq Var] (p : QProg Var d) (k : Nat)
    (P : Nat → CQPredicate Var d) (Q : CQPredicate Var d)
    (h : ∀ s rho, rho.PosSemidef → Tendsto (fun n => pairing (P n s) rho)
      atTop (𝓝 (pairing (Q s) rho)))
    (s : Store Var) (rho : Operator d) (hr : rho.PosSemidef) :
    Tendsto (fun n => pairing (wpApprox p k (P n) s) rho)
      atTop (𝓝 (pairing (wpApprox p k Q s) rho)) := by
  simpa only [expect_wpApprox] using branchExpectation_tendsto P Q h
    (interpApprox p k (s, rho)) (interpApprox_positive p k (s, rho) hr)

theorem wp_seq [DecidableEq Var] (a b : QProg Var d) (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.seq a b) Q s).matrix = (wp a (wp b Q) s).matrix := by
  apply le_antisymm
  · apply wp_le
    intro k
    exact (wpApprox_mono a k (wpApprox_le_wp b Q k) s).trans (wpApprox_le_wp a (wp b Q) k s)
  · apply wp_le
    intro k
    apply le_of_pairing_le
      (Matrix.nonneg_iff_posSemidef.mp (wpBounded a k (wp b Q) s).nonnegative).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp (wp (.seq a b) Q s).nonnegative).isHermitian
    intro rho hr
    apply le_of_tendsto' (wpApprox_pairing_tendsto a k
      (fun j => (wpBounded b j Q).toPredicate) (wp b Q).toPredicate
      (wpBounded_pairing_tendsto b Q) s rho hr)
    intro j
    apply pairing_mono _ hr
    have hQ : IsAssertion Q.toPredicate := fun t => ⟨(Q t).nonnegative, (Q t).le_identity⟩
    exact ((wpApprox_mono a k
      (fun t => wpApprox_fuel_mono b Q.toPredicate hQ t (Nat.le_max_right k j)) s).trans
      (wpApprox_fuel_mono a _ (wpApprox_effect b (max k j) _ hQ) s
        (Nat.le_max_left k j))).trans (wpApprox_le_wp (.seq a b) Q (max k j) s)

theorem hoare_seq [DecidableEq Var] (P R Q : CQAssertion Var d) (a b : QProg Var d)
    (ha : Hoare P a R) (hb : Hoare R b Q) : Hoare P (.seq a b) Q := by
  apply (hoare_iff _ _ _).mpr
  intro s
  rw [wp_seq]
  exact ((hoare_iff _ _ _).mp ha s).trans (wp_mono a R (wp b Q) ((hoare_iff _ _ _).mp hb) s)

/-- Unbounded loop unfolding, including loops in the body. -/
theorem wp_while_unfold [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (Q : CQAssertion Var d) (s : Store Var) :
    (wp (.qwhile g body) Q s).matrix =
      if g s then (wp body (wp (.qwhile g body) Q) s).matrix else (Q s).matrix := by
  have hQ : IsAssertion Q.toPredicate := fun t => ⟨(Q t).nonnegative, (Q t).le_identity⟩
  apply le_antisymm
  · apply wp_le
    intro k
    cases k with
    | zero =>
        change 0 ≤ _
        split <;> [exact (wp body (wp (.qwhile g body) Q) s).nonnegative; exact (Q s).nonnegative]
    | succ k =>
        simp only [wpApprox_while_succ]
        split
        · exact (wpApprox_mono body k (wpApprox_le_wp (.qwhile g body) Q k) s).trans
            (wpApprox_le_wp body (wp (.qwhile g body) Q) k s)
        · exact le_rfl
  · split
    next hg =>
      apply wp_le
      intro k
      apply le_of_pairing_le
        (Matrix.nonneg_iff_posSemidef.mp (wpBounded body k (wp (.qwhile g body) Q) s).nonnegative).isHermitian
        (Matrix.nonneg_iff_posSemidef.mp (wp (.qwhile g body) Q s).nonnegative).isHermitian
      intro rho hr
      apply le_of_tendsto' (wpApprox_pairing_tendsto body k
        (fun j => (wpBounded (.qwhile g body) j Q).toPredicate) (wp (.qwhile g body) Q).toPredicate
        (wpBounded_pairing_tendsto (.qwhile g body) Q) s rho hr)
      intro j
      apply pairing_mono _ hr
      have hm := ((wpApprox_mono body k (fun t => wpApprox_fuel_mono (.qwhile g body)
        Q.toPredicate hQ t (Nat.le_max_right k j)) s).trans
        (wpApprox_fuel_mono body _ (wpApprox_effect (.qwhile g body) (max k j) _ hQ) s
          (Nat.le_max_left k j)))
      have hb := wpApprox_le_wp (.qwhile g body) Q (max k j + 1) s
      simp only [wpApprox_while_succ, hg, if_true] at hb
      exact hm.trans hb
    next hg =>
      have hb := wpApprox_le_wp (.qwhile g body) Q 1 s
      simpa [wpApprox_while_succ, hg, CQAssertion.toPredicate] using hb

/-- The loop solution is the least prefixed point of its semantic functional. -/
theorem wp_while_least [DecidableEq Var] (g : Store Var → Bool) (body : QProg Var d)
    (Q R : CQAssertion Var d)
    (h : ∀ s, (if g s then (wp body R s).matrix else (Q s).matrix) ≤ (R s).matrix) :
    ∀ s, (wp (.qwhile g body) Q s).matrix ≤ (R s).matrix := by
  intro s
  apply wp_le
  intro k
  induction k generalizing s with
  | zero => exact (R s).nonnegative
  | succ k ih =>
      rw [wpApprox_while_succ]
      dsimp only
      split
      next hg =>
        exact ((wpApprox_mono body k ih s).trans (wpApprox_le_wp body R k s)).trans
          (by simpa only [hg, if_true] using h s)
      next hg => simpa [hg, CQAssertion.toPredicate] using h s

end QuantumLeanLeap.GoogleQHL
