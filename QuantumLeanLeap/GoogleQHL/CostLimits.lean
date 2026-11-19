import QuantumLeanLeap.GoogleQHL.ExpectedCost
import QuantumLeanLeap.GoogleQHL.Limits

/-! A positive cost observable represents finite-prefix cost. This gives
monotonicity of prefix costs even when nested loops reveal new histories. -/
namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder Topology
variable {Var : Type} {d : Nat}

def costPredicate [DecidableEq Var] (w : CostModel d) : QProg Var d → Nat → CQPredicate Var d
  | .skip, _ => 0
  | .abort, _ => 0
  | .assign .., _ => fun _ => w.assignmentCost • (1 : Operator d)
  | .qset .., _ => fun _ => w.resetCost • (1 : Operator d)
  | .apply U, _ => fun _ => w.unitaryCost U • (1 : Operator d)
  | .measure _ _ M, _ => fun _ => w.measurementCost M • (1 : Operator d)
  | .seq a b, k => costPredicate w a k + wpApprox a k (costPredicate w b k)
  | .qif g a b, k => fun s => if g s then costPredicate w a k s else costPredicate w b k s
  | .qwhile g body, k => Nat.rec (motive := fun _ => CQPredicate Var d) 0
      (fun j previous s => if g s then costPredicate w body j s + wpApprox body j previous s else 0) k

theorem costPredicate_while_succ [DecidableEq Var] (w : CostModel d) (g : Store Var → Bool)
    (body : QProg Var d) (k : Nat) (s : Store Var) :
    costPredicate w (.qwhile g body) (k + 1) s =
      if g s then costPredicate w body k s + wpApprox body k (costPredicate w (.qwhile g body) k) s
      else 0 := rfl

theorem costPredicate_nonnegative [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) : ∀ s, 0 ≤ costPredicate w p k s := by
  induction p generalizing k with
  | skip => intro s; exact le_rfl
  | abort => intro s; exact le_rfl
  | assign v e => intro s; exact nsmul_nonneg Matrix.PosSemidef.one.nonneg _
  | qset i => intro s; exact nsmul_nonneg Matrix.PosSemidef.one.nonneg _
  | apply U => intro s; exact nsmul_nonneg Matrix.PosSemidef.one.nonneg _
  | measure v n M => intro s; exact nsmul_nonneg Matrix.PosSemidef.one.nonneg _
  | seq a b iha ihb => intro s; exact add_nonneg (iha k s) (wpApprox_nonnegative a k _ (ihb k) s)
  | qif g a b iha ihb => intro s; simp only [costPredicate]; split <;> [exact iha k s; exact ihb k s]
  | qwhile g body ihBody =>
      induction k with
      | zero => intro s; exact le_rfl
      | succ k ih =>
          intro s
          rw [costPredicate_while_succ]
          split
          · exact add_nonneg (ihBody k s) (wpApprox_nonnegative body k _ ih s)
          · exact le_rfl

theorem pairing_nsmul_one (w : Nat) (rho : Operator d) :
    pairing (w • (1 : Operator d)) rho = (w : Real) * rho.trace.re := by
  simp only [pairing, smul_mul_assoc, one_mul, Matrix.trace_smul]
  simp [nsmul_eq_mul]

theorem expectedCostApprox_pairing [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) (input : Branch Var d) :
    expectedCostApprox w p k input = pairing (costPredicate w p k input.1) input.2 := by
  induction p generalizing k input with
  | skip => simp [expectedCostApprox, costPredicate, pairing]
  | abort => simp [expectedCostApprox, costPredicate, pairing]
  | assign v e => exact (pairing_nsmul_one _ _).symm
  | qset i => exact (pairing_nsmul_one _ _).symm
  | apply U => exact (pairing_nsmul_one _ _).symm
  | measure v n M => exact (pairing_nsmul_one _ _).symm
  | seq a b iha ihb =>
      have hb : ((interpApprox a k input).map (expectedCostApprox w b k)).sum =
          pairing (wpApprox a k (costPredicate w b k) input.1) input.2 := by
        rw [← expect_wpApprox, branchExpectation_eq_sum]
        congr 1
        apply List.map_congr_left
        intro out _
        exact ihb k out
      simpa [expectedCostApprox, costPredicate, pairing, Matrix.add_mul, Matrix.trace_add] using
        congrArg₂ (· + ·) (iha k input) hb
  | qif g a b iha ihb =>
      simp only [expectedCostApprox, costPredicate]
      split <;> [exact iha k input; exact ihb k input]
  | qwhile g body ihBody =>
      induction k generalizing input with
      | zero => simp [expectedCostApprox, costPredicate, pairing]
      | succ k ih =>
          rw [expectedCostApprox_while_succ, costPredicate_while_succ]
          split
          · have hb : ((interpApprox body k input).map (expectedCostApprox w (.qwhile g body) k)).sum =
                pairing (wpApprox body k (costPredicate w (.qwhile g body) k) input.1) input.2 := by
              rw [← expect_wpApprox, branchExpectation_eq_sum]
              congr 1
              apply List.map_congr_left
              intro out _
              exact ih out
            simpa [pairing, Matrix.add_mul, Matrix.trace_add] using congrArg₂ (· + ·) (ihBody k input) hb
          · simp [pairing]

theorem costPredicate_fuel_step [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (k : Nat) : ∀ s, costPredicate w p k s ≤ costPredicate w p (k + 1) s := by
  induction p generalizing k with
  | skip => intro s; exact le_rfl
  | abort => intro s; exact le_rfl
  | assign v e => intro s; exact le_rfl
  | qset i => intro s; exact le_rfl
  | apply U => intro s; exact le_rfl
  | measure v n M => intro s; exact le_rfl
  | seq a b iha ihb =>
      intro s
      exact add_le_add (iha k s) ((wpApprox_mono a k (ihb k) s).trans
        (wpApprox_fuel_step_nonneg a k _ (costPredicate_nonnegative w b (k + 1)) s))
  | qif g a b iha ihb => intro s; simp only [costPredicate]; split <;> [exact iha k s; exact ihb k s]
  | qwhile g body ihBody =>
      induction k with
      | zero => exact costPredicate_nonnegative w (.qwhile g body) 1
      | succ k ih =>
          intro s
          simp only [costPredicate_while_succ]
          split
          · exact add_le_add (ihBody k s) ((wpApprox_mono body k ih s).trans
              (wpApprox_fuel_step_nonneg body k _ (costPredicate_nonnegative w (.qwhile g body) (k + 1)) s))
          · exact le_rfl

theorem expectedCostApprox_mono [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (input : Branch Var d) (hr : input.2.PosSemidef) :
    Monotone (fun k => expectedCostApprox w p k input) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [expectedCostApprox_pairing, expectedCostApprox_pairing]
  exact pairing_mono (costPredicate_fuel_step w p k input.1) hr

theorem expectedCostApprox_tendsto [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (input : Branch Var d) (hr : input.2.PosSemidef) :
    Filter.Tendsto (fun k => ENNReal.ofReal (expectedCostApprox w p k input))
      Filter.atTop (𝓝 (prefixCostSup w p input)) := by
  apply tendsto_atTop_iSup
  intro a b hab
  exact ENNReal.ofReal_le_ofReal (expectedCostApprox_mono w p input hr hab)

/-- Arbitrary initial classical mixtures, including infinite expected costs. -/
noncomputable def expectedCost [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (state : CQState Var d) : ENNReal :=
  ∑' s, prefixCostSup w p (s, (state.density s).matrix)

theorem prefixCostSup_le [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (input : Branch Var d) (C : ENNReal)
    (h : ∀ k, ENNReal.ofReal (expectedCostApprox w p k input) ≤ C) :
    prefixCostSup w p input ≤ C := iSup_le h

theorem expectedCost_le_mass [DecidableEq Var] (w : CostModel d) (p : QProg Var d)
    (state : CQState Var d) (C : ENNReal)
    (h : ∀ s, prefixCostSup w p (s, (state.density s).matrix) ≤
      C * ENNReal.ofReal (state.density s).matrix.trace.re) :
    expectedCost w p state ≤ C * ENNReal.ofReal state.mass := by
  have ht : ∀ s, 0 ≤ (state.density s).matrix.trace.re :=
    fun s => (RCLike.nonneg_iff.mp (state.density s).positive.trace_nonneg).1
  calc
    _ ≤ ∑' s, C * ENNReal.ofReal (state.density s).matrix.trace.re := ENNReal.tsum_le_tsum h
    _ = C * ENNReal.ofReal state.mass := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg ht
        state.trace_hasSum.summable, state.trace_hasSum.tsum_eq]

end QuantumLeanLeap.GoogleQHL
