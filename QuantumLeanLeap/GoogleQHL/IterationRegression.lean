import QuantumLeanLeap.GoogleQHL.IterationWP

namespace QuantumLeanLeap.GoogleQHL.IterationRegression
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

theorem false_guard_iterations [DecidableEq Var] (body : QProg Var d) (S : CQState Var d) :
    expectedIterations (fun _ => false) body S = 0 := by
  simp [expectedIterations, entryProbability, loopEntry, restrictState]

theorem loopState_abort_succ [DecidableEq Var] (g : Store Var → Bool)
    (S : CQState Var d) (n : Nat) : loopState g .abort (n + 1) S = zeroState Var d := by
  rw [loopState_succ_outer, loopStep, interp_abort]

/-- Aborting in the first body counts one entry, but produces no subsequent
entries. The initial guard still weights that one entry. -/
theorem abort_iterations [DecidableEq Var] (g : Store Var → Bool) (S : CQState Var d) :
    expectedIterations g .abort S = ENNReal.ofReal (restrictState g S).mass := by
  have hz (n : Nat) : entryProbability g (.abort : QProg Var d) (n + 1) S = 0 := by
    simp [entryProbability, loopEntry, loopState_abort_succ, restrictState, zeroState]
  rw [expectedIterations, tsum_eq_zero_add' ENNReal.summable]
  simp only [hz, tsum_zero, add_zero]
  rfl

theorem fourWay_complete (d : Nat) :
    (∑ _ : Fin 4, Matrix.conjTranspose ((1 / 2 : Real) • (1 : Operator d)) *
      ((1 / 2 : Real) • (1 : Operator d))) = 1 := by
  simp [Matrix.conjTranspose_smul, smul_smul]
  norm_num
  ext i j
  by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.ofNat_apply, Matrix.one_apply, hij]

/-- Four equally likely outcomes, implemented as a complete Kraus
instrument. This semantic regression does not assert a native gate decomposition. -/
noncomputable def fourWay (d : Nat) : Measurement d 4 where
  kraus _ := (1 / 2 : Real) • (1 : Operator d)
  complete := (fourWay_complete d).le

def retryGuard (s : Store Unit) : Bool := decide (s () < 2)

noncomputable def retryBody (d : Nat) : QProg Unit d := .measure () 4 (fourWay d)

theorem retry_continuation_effect (s : Store Unit) :
    (wp (retryBody d) (guardIndicator retryGuard) s).matrix = (1 / 2 : Real) • (1 : Operator d) := by
  simp [retryBody, wp_measure, fourWay, guardIndicator, guardAssertion, retryGuard,
    oneAssertion, zeroObservable, Fin.sum_univ_succ, Matrix.conjTranspose_smul,
    smul_smul, ← add_smul]
  norm_num

theorem retry_expected_iterations_le_two (S : CQState Unit d) :
    expectedIterations retryGuard (retryBody d) S ≤ 2 * entryProbability retryGuard (retryBody d) 0 S := by
  have h := expectedIterations_le_geometric retryGuard (retryBody d) S (ENNReal.ofReal (1 / 2 : Real))
    (entryProbability_contraction_of_wp retryGuard (retryBody d) (1 / 2) (by norm_num)
      (fun s _ => (retry_continuation_effect s).le) S)
  have hh : ENNReal.ofReal (1 / 2 : Real) = (2 : ENNReal)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  simpa [hh, ENNReal.one_sub_inv_two] using h

def measurementCharge (d : Nat) : CostModel d := ⟨0, 0, fun _ => 0, fun _ => 1⟩

theorem retry_body_cost_bound : CostBound (measurementCharge d) (retryBody d) 1 := by
  intro S
  apply expectedCost_le_mass
  intro s
  simp [retryBody, prefixCostSup, expectedCostApprox, measurementCharge]

theorem retry_expected_cost_le_two (S : CQState Unit d) :
    expectedCost (measurementCharge d) (.qwhile retryGuard (retryBody d)) S ≤
      2 * entryProbability retryGuard (retryBody d) 0 S := by
  have h := expectedCost_while_le_iterations (measurementCharge d) retryGuard (retryBody d) 1
    retry_body_cost_bound S
  simp only [one_mul] at h
  exact h.trans (retry_expected_iterations_le_two S)

theorem skip_loop_iterations_infinite [DecidableEq Var] (S : CQState Var d) (hS : 0 < S.mass) :
    expectedIterations (fun _ => true) .skip S = ⊤ := by
  have hr (T : CQState Var d) : restrictState (fun _ => true) T = T := by
    apply CQState.ext
    intro s
    simp [restrictState]
  have hs (n : Nat) : loopState (fun _ => true) (.skip : QProg Var d) n S = S := by
    induction n with
    | zero => rfl
    | succ n ih => rw [loopState_succ_outer, ih, loopStep, interp_skip, hr]
  simp only [expectedIterations, entryProbability, loopEntry, hs, hr]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hS))

end QuantumLeanLeap.GoogleQHL.IterationRegression
