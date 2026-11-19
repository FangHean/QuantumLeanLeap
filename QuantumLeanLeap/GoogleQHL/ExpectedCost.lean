import QuantumLeanLeap.GoogleQHL.Physical
import QuantumLeanLeap.GoogleQHL.ResourceCounting
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Semantic cost of finite execution prefixes. Cost is paid when a command
executes, even if that history later aborts. This differs from charging only
the terminating output histories. Unbounded prefix cost uses ENNReal so an
infinite execution may have cost infinity. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

def expectedCostApprox [DecidableEq Var] (w : CostModel d) :
    QProg Var d → Nat → Branch Var d → Real
  | .skip, _, _ => 0
  | .abort, _, _ => 0
  | .assign .., _, b => w.assignmentCost * b.2.trace.re
  | .qset .., _, b => w.resetCost * b.2.trace.re
  | .apply U, _, b => w.unitaryCost U * b.2.trace.re
  | .measure _ _ M, _, b => w.measurementCost M * b.2.trace.re
  | .seq a b, k, input => expectedCostApprox w a k input +
      ((interpApprox a k input).map (expectedCostApprox w b k)).sum
  | .qif g a b, k, input =>
      if g input.1 then expectedCostApprox w a k input else expectedCostApprox w b k input
  | .qwhile g body, k, input =>
      Nat.rec (motive := fun _ => Branch Var d → Real) (fun _ => 0)
        (fun j previous current => if g current.1 then expectedCostApprox w body j current +
          ((interpApprox body j current).map previous).sum else 0) k input

@[simp] theorem expectedCostApprox_while_succ [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (k : Nat) (input : Branch Var d) :
    expectedCostApprox w (.qwhile g body) (k + 1) input =
      if g input.1 then expectedCostApprox w body k input +
        ((interpApprox body k input).map (expectedCostApprox w (.qwhile g body) k)).sum else 0 := rfl

theorem expectedCostApprox_nonneg [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) (input : Branch Var d) (hr : input.2.PosSemidef) :
    0 ≤ expectedCostApprox w p k input := by
  have trace0 : 0 ≤ input.2.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
  induction p generalizing k input with
  | skip => exact le_rfl
  | abort => exact le_rfl
  | assign v e => exact mul_nonneg (Nat.cast_nonneg _) trace0
  | qset i => exact mul_nonneg (Nat.cast_nonneg _) trace0
  | apply U => exact mul_nonneg (Nat.cast_nonneg _) trace0
  | measure v n M => exact mul_nonneg (Nat.cast_nonneg _) trace0
  | seq a b iha ihb =>
      apply add_nonneg (iha k input hr trace0)
      apply List.sum_nonneg
      intro x hx
      obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hx
      have ho := interpApprox_positive a k input hr out hout
      exact ihb k out ho (RCLike.nonneg_iff.mp ho.trace_nonneg).1
  | qif g a b iha ihb =>
      simp only [expectedCostApprox]
      split <;> [exact iha k input hr trace0; exact ihb k input hr trace0]
  | qwhile g body ihBody =>
      induction k generalizing input with
      | zero => exact le_rfl
      | succ k ih =>
          rw [expectedCostApprox_while_succ]
          split
          · apply add_nonneg (ihBody k input hr trace0)
            apply List.sum_nonneg
            intro x hx
            obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hx
            have ho := interpApprox_positive body k input hr out hout
            exact ih out ho (RCLike.nonneg_iff.mp ho.trace_nonneg).1
          · exact le_rfl

theorem worstCost_mono (w : CostModel d) (p : QProg Var d) : Monotone (worstCost w p) := by
  induction p with
  | skip => exact monotone_const
  | abort => exact monotone_const
  | assign v e => exact monotone_const
  | qset i => exact monotone_const
  | apply U => exact monotone_const
  | measure v n M => exact monotone_const
  | seq a b iha ihb => exact iha.add ihb
  | qif g a b iha ihb => intro a b hab; exact max_le_max (iha hab) (ihb hab)
  | qwhile g body ih => intro a b hab; exact Nat.mul_le_mul hab (ih hab)

theorem sum_cost_le_mass (outputs : List (Branch Var d)) (cost : Branch Var d → Real)
    (C : Real) (h : ∀ b ∈ outputs, cost b ≤ C * b.2.trace.re) :
    (outputs.map cost).sum ≤ C * branchMass outputs := by
  induction outputs with
  | nil => simp [branchMass]
  | cons b rest ih =>
      simp only [List.map_cons, List.sum_cons, branchMass, branchExpectation_cons, pairing_one]
      rw [mul_add]
      exact add_le_add (h b (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- The previously syntactic budget bounds the state-dependent cost of the
actual forward execution, for every PSD input and every loop unfolding. -/
theorem expectedCostApprox_le [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) (input : Branch Var d) (hr : input.2.PosSemidef) :
    expectedCostApprox w p k input ≤ (worstCost w p k : Real) * input.2.trace.re := by
  have trace0 : 0 ≤ input.2.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
  induction p generalizing k input with
  | skip => simp [expectedCostApprox, worstCost]
  | abort => simp [expectedCostApprox, worstCost]
  | assign v e => exact le_rfl
  | qset i => exact le_rfl
  | apply U => exact le_rfl
  | measure v n M => exact le_rfl
  | seq a b iha ihb =>
      have hs := sum_cost_le_mass (interpApprox a k input) (expectedCostApprox w b k)
        (worstCost w b k) (fun out hout =>
          ihb k out (interpApprox_positive a k input hr out hout)
            (RCLike.nonneg_iff.mp (interpApprox_positive a k input hr out hout).trace_nonneg).1)
      have hm := mul_le_mul_of_nonneg_left (interpApprox_trace_nonincreasing a k input hr)
        (Nat.cast_nonneg (worstCost w b k) : (0 : Real) ≤ _)
      have ha := iha k input hr trace0
      simpa [expectedCostApprox, worstCost, Nat.cast_add, add_mul] using add_le_add ha (hs.trans hm)
  | qif g a b iha ihb =>
      simp only [expectedCostApprox, worstCost]
      split
      · exact (iha k input hr trace0).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_max_left (worstCost w a k) (worstCost w b k)) trace0)
      · exact (ihb k input hr trace0).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_max_right (worstCost w a k) (worstCost w b k)) trace0)
  | qwhile g body ihBody =>
      induction k generalizing input with
      | zero => simp [expectedCostApprox, worstCost]
      | succ k ih =>
          rw [expectedCostApprox_while_succ]
          split
          · have hs := sum_cost_le_mass (interpApprox body k input)
              (expectedCostApprox w (.qwhile g body) k) (worstCost w (.qwhile g body) k)
              (fun out hout => ih out (interpApprox_positive body k input hr out hout)
                (RCLike.nonneg_iff.mp (interpApprox_positive body k input hr out hout).trace_nonneg).1)
            have hm := mul_le_mul_of_nonneg_left (interpApprox_trace_nonincreasing body k input hr)
              (Nat.cast_nonneg (worstCost w (.qwhile g body) k) : (0 : Real) ≤ _)
            have hb := ihBody k input hr trace0
            have hstep : (worstCost w body k : Real) ≤ worstCost w body (k + 1) := by
              exact_mod_cast worstCost_mono w body (Nat.le_succ k)
            have hcount : ((k + 1 : Nat) : Real) * worstCost w body k ≤
                ((k + 1 : Nat) : Real) * worstCost w body (k + 1) :=
              mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
            have total := add_le_add hb (hs.trans hm)
            calc
              _ ≤ ((k + 1 : Nat) : Real) * worstCost w body k * input.2.trace.re := by
                simpa [worstCost, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_mul,
                  mul_add, mul_assoc, add_comm] using total
              _ ≤ _ := by
                simpa [worstCost, Nat.cast_mul] using mul_le_mul_of_nonneg_right hcount trace0
          · exact mul_nonneg (Nat.cast_nonneg _) trace0

/-- Supremum of prefix costs; infinity is a valid result. `CostLimits.lean`
proves monotonicity and convergence. `CostComposition.lean` and
`CostControl.lean` prove the full state-level seq/if/while cost equations. -/
noncomputable def prefixCostSup [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (input : Branch Var d) : ENNReal :=
  ⨆ k : Nat, ENNReal.ofReal (expectedCostApprox w p k input)

end QuantumLeanLeap.GoogleQHL
