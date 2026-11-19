import QuantumLeanLeap.GoogleVQCC.InvSqrt.Arithmetic

/-! Newton inverse-square-root iteration with an explicit downward-rounding
budget. The theorem is about the implemented rounded iterates, not only an
ideal real-arithmetic limit. No numerical convergence oracle is assumed. -/

namespace QuantumLeanLeap.GoogleVQCC.InvSqrt

noncomputable section

def newtonStep (a y : Real) : Real := y * (3 - a * y ^ 2) / 2

/-- Exact relative-defect recurrence. -/
theorem newton_defect_identity (a r y : Real) (hr : r ^ 2 = a) :
    1 - r * newtonStep a y = (1 - r * y) ^ 2 * (3 - (1 - r * y)) / 2 := by
  rw [← hr]
  unfold newtonStep
  ring

/-- Downward rounding preserves a nonnegative relative defect. The additive
term `eta` is the absolute rounding error multiplied by `sqrt a`. -/
theorem rounded_newton_defect_bound (a r y next bound eta : Real)
    (hr : r ^ 2 = a) (hr0 : 0 ≤ r)
    (hlo : 0 ≤ 1 - r * y) (hhi : 1 - r * y ≤ bound)
    (_hb0 : 0 ≤ bound) (hb1 : bound ≤ 1)
    (hdown : next ≤ newtonStep a y)
    (hround : r * (newtonStep a y - next) ≤ eta) :
    0 ≤ 1 - r * next ∧ 1 - r * next ≤ 3 / 2 * bound ^ 2 + eta := by
  have ident := newton_defect_identity a r y hr
  have hfactor : 0 ≤ 3 - (1 - r * y) := by linarith
  have hp := mul_nonneg (sq_nonneg (1 - r * y)) hfactor
  have hsquare : (1 - r * y) ^ 2 ≤ bound ^ 2 := by nlinarith
  have hcubic := mul_nonneg (sq_nonneg (1 - r * y)) hlo
  have horder := mul_nonneg hr0 (sub_nonneg.mpr hdown)
  constructor <;> nlinarith

/-- Six explicit bounds, selected with slack for 37-bit absolute fixed point.
The domain sqrt(x)<2048 implies relative rounding error <2^-26 per step. -/
def newtonBudget : Nat → Real
  | 0 => 1 / 2
  | 1 => 376 / 1000
  | 2 => 213 / 1000
  | 3 => 69 / 1000
  | 4 => 72 / 10000
  | 5 => 78 / 1000000
  | _ => 1 / 2 ^ 25

theorem newtonBudget_step (i : Nat) (hi : i < 6) :
    0 ≤ newtonBudget i ∧ newtonBudget i ≤ 1 ∧
      3 / 2 * newtonBudget i ^ 2 + 1 / 2 ^ 26 ≤ newtonBudget (i + 1) := by
  interval_cases i <;> norm_num [newtonBudget]

/-- Six rounded steps suffice, provided the seed and each actual rounding
operation meet the explicit local conditions. NewtonFixed discharges these
conditions for the executable integer algorithm. -/
theorem six_rounded_newton_steps (a r : Real) (ys : Nat → Real)
    (hr : r ^ 2 = a) (hr0 : 0 ≤ r)
    (seed : 0 ≤ 1 - r * ys 0 ∧ 1 - r * ys 0 ≤ 1 / 2)
    (down : ∀ i < 6, ys (i + 1) ≤ newtonStep a (ys i))
    (rounding : ∀ i < 6,
      r * (newtonStep a (ys i) - ys (i + 1)) ≤ 1 / 2 ^ 26) :
    0 ≤ 1 - r * ys 6 ∧ 1 - r * ys 6 ≤ 1 / 2 ^ 25 := by
  have all_steps : ∀ i ≤ 6,
      0 ≤ 1 - r * ys i ∧ 1 - r * ys i ≤ newtonBudget i := by
    intro i hi
    induction i with
    | zero => simpa [newtonBudget] using seed
    | succ i ih =>
      have iprev : i < 6 := by omega
      have previous := ih (by omega)
      have bounds := newtonBudget_step i iprev
      have step := rounded_newton_defect_bound a r (ys i) (ys (i + 1))
        (newtonBudget i) (1 / 2 ^ 26) hr hr0 previous.1 previous.2
        bounds.1 bounds.2.1 (down i iprev) (rounding i iprev)
      exact ⟨step.1, step.2.trans bounds.2.2⟩
  simpa [newtonBudget] using all_steps 6 (by omega)

/-- Relative defect bounds imply the original modulo-one-turn task contract. -/
theorem phaseAccurate_of_relative_defect (phase : Input → Real)
    (bound : ∀ x, 0 ≤ 1 - Real.sqrt x.value * phase x ∧
      1 - Real.sqrt x.value * phase x ≤ 1 / 2 ^ 25) :
    PhaseAccurate phase := by
  intro x
  have root_pos : 0 < Real.sqrt (x.value : Real) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast x.positive)
  have root_inv : Real.sqrt (x.value : Real) * (Real.sqrt x.value)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt root_pos)
  have h := bound x
  have below : phase x ≤ targetTurns x := by
    unfold targetTurns
    nlinarith
  apply (turnDistance_le_abs _ _).trans
  rw [abs_of_nonpos (sub_nonpos.mpr below)]
  unfold toleranceTurns targetTurns
  norm_num [precisionBits]
  nlinarith

end
end QuantumLeanLeap.GoogleVQCC.InvSqrt
