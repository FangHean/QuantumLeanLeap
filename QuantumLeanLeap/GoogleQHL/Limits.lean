import QuantumLeanLeap.GoogleQHL.Hoare
import Mathlib.Topology.Order.MonotoneConvergence

/-! Monotone approximation and scalar limits. This module does NOT assert an
operator-valued omega-CPO or a full `CQState` interpreter for unbounded loops.
It proves the convergent expectation limit for each physical input branch. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology
variable {Var : Type} {d : Nat}

theorem wpApprox_fuel_step_nonneg [DecidableEq Var] (p : QProg Var d) (k : Nat)
    (post : CQPredicate Var d) (hpost : ∀ s, 0 ≤ post s) :
    ∀ s, wpApprox p k post s ≤ wpApprox p (k + 1) post s := by
  induction p generalizing k post with
  | skip => intro s; exact le_rfl
  | abort => intro s; exact le_rfl
  | assign v e => intro s; exact le_rfl
  | qset i => intro s; exact le_rfl
  | apply U => intro s; exact le_rfl
  | measure v n M => intro s; exact le_rfl
  | seq a b iha ihb =>
      intro s
      exact (wpApprox_mono a k (ihb k post hpost) s).trans
        (iha k _ (wpApprox_nonnegative b (k + 1) post hpost) s)
  | qif g a b iha ihb =>
      intro s
      simp only [wpApprox]
      split <;> [exact iha k post hpost s; exact ihb k post hpost s]
  | qwhile g body ihBody =>
      induction k with
      | zero => intro s; exact wpApprox_nonnegative (.qwhile g body) 1 post hpost s
      | succ k ih =>
          intro s
          simp only [wpApprox_while_succ]
          by_cases h : g s = true
          · simp only [h, if_true]
            have hprev : ∀ t, wpApprox (.qwhile g body) k post t ≤
                wpApprox (.qwhile g body) (k + 1) post t := ih
            exact (wpApprox_mono body k hprev s).trans
              (ihBody k _ (wpApprox_nonnegative (.qwhile g body) (k + 1) post hpost) s)
          · simp [h]

theorem wpApprox_fuel_step [DecidableEq Var] (p : QProg Var d) (k : Nat)
    (post : CQPredicate Var d) (hpost : IsAssertion post) :
    ∀ s, wpApprox p k post s ≤ wpApprox p (k + 1) post s :=
  wpApprox_fuel_step_nonneg p k post (fun s => (hpost s).1)

theorem wpApprox_fuel_mono [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (hpost : IsAssertion post) (s : Store Var) :
    Monotone (fun k => wpApprox p k post s) :=
  monotone_nat_of_le_succ (fun k => wpApprox_fuel_step p k post hpost s)

theorem expectationApprox_mono [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (hp : IsAssertion post) (input : Branch Var d)
    (hr : input.2.PosSemidef) :
    Monotone (fun k => branchExpectation post (interpApprox p k input)) := by
  intro a b hab
  dsimp only
  rw [expect_wpApprox, expect_wpApprox]
  exact pairing_mono (wpApprox_fuel_mono p post hp input.1 hab) hr

theorem expectationApprox_bddAbove [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (hp : IsAssertion post) (input : Branch Var d)
    (hr : input.2.PosSemidef) :
    BddAbove (Set.range (fun k => branchExpectation post (interpApprox p k input))) := by
  refine ⟨input.2.trace.re, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (interpApprox_expectation_bounds p k post hp input.1 input.2 hr).2

/-- Supremum of actual finite-execution expectations. Its interpretation as a
limit is justified by `expectationApprox_tendsto`, for physical inputs. -/
noncomputable def limitExpectation [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (input : Branch Var d) : Real :=
  ⨆ k : Nat, branchExpectation post (interpApprox p k input)

theorem expectationApprox_tendsto [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (hp : IsAssertion post) (input : Branch Var d)
    (hr : input.2.PosSemidef) :
    Filter.Tendsto (fun k => branchExpectation post (interpApprox p k input))
      Filter.atTop (𝓝 (limitExpectation p post input)) :=
  tendsto_atTop_ciSup (expectationApprox_mono p post hp input hr)
    (expectationApprox_bddAbove p post hp input hr)

theorem limitExpectation_bounds [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (hp : IsAssertion post) (input : Branch Var d)
    (hr : input.2.PosSemidef) :
    0 ≤ limitExpectation p post input ∧ limitExpectation p post input ≤ input.2.trace.re := by
  constructor
  · exact (interpApprox_expectation_bounds p 0 post hp input.1 input.2 hr).1.trans
      (le_ciSup (expectationApprox_bddAbove p post hp input hr) 0)
  · exact ciSup_le (fun k => (interpApprox_expectation_bounds p k post hp input.1 input.2 hr).2)

/-- Forward/backward duality persists after taking expectation suprema. This
does not interchange an operator supremum and a trace without proof. -/
theorem expect_wp_limit [DecidableEq Var] (p : QProg Var d)
    (post : CQPredicate Var d) (input : Branch Var d) :
    limitExpectation p post input = ⨆ k : Nat, pairing (wpApprox p k post input.1) input.2 := by
  unfold limitExpectation
  congr 1
  funext k
  exact expect_wpApprox p k post input

end QuantumLeanLeap.GoogleQHL
