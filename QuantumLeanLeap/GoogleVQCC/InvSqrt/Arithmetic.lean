import QuantumLeanLeap.GoogleVQCC.InvSqrt.Specification
import Mathlib.Data.Nat.Sqrt

/-!
Executable inverse-square-root quantization and its exact error certificate.
The phase word is computed using integer division and integer square root only.
No floating-point square root or sampled numerical verification is trusted.
-/

namespace QuantumLeanLeap.GoogleVQCC.InvSqrt

/-- Forty fractional bits leave arithmetic error below the official tolerance. -/
def phaseBits : Nat := 40

/-- Integer scale of the fixed-point phase word. -/
def phaseScale : Nat := 2 ^ phaseBits

/-- Exact integer algorithm for `floor (2^40 / sqrt x)`.
At `x = 1` the value is `2^40`, representing one full turn; an exporter
may reduce it modulo `2^40` to store it in forty bits. -/
def phaseWord (x : Nat) : Nat := Nat.sqrt (phaseScale ^ 2 / x)

/-- Forty-bit representation exported by the circuit generator. In particular,
the full turn at `x = 1` becomes zero without changing the physical phase. -/
def wrappedPhaseWord (x : Nat) : Nat := phaseWord x % phaseScale

noncomputable section

/-- Mathematical phase of the executable integer word, in turns. -/
def quantizedTurns (x : Input) : Real := (phaseWord x.value : Real) / phaseScale

theorem phaseScale_pos : 0 < phaseScale := by norm_num [phaseScale, phaseBits]

/-- Exact lower integer inequality certifying the quantized word. -/
theorem phaseWord_lower (x : Nat) (hx : 0 < x) :
    phaseWord x ^ 2 * x ≤ phaseScale ^ 2 := by
  exact (Nat.le_div_iff_mul_le hx).mp (Nat.sqrt_le' _)

/-- Exact upper integer inequality certifying the quantized word. -/
theorem phaseWord_upper (x : Nat) (hx : 0 < x) :
    phaseScale ^ 2 < (phaseWord x + 1) ^ 2 * x := by
  exact (Nat.div_lt_iff_lt_mul hx).mp (Nat.lt_succ_sqrt' _)

/-- Circular distance never exceeds the ordinary difference of phase lifts. -/
theorem turnDistance_le_abs (a b : Real) : turnDistance a b ≤ |a - b| := by
  unfold turnDistance
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- Squared-integer bounds suffice to prove a real inverse-square-root interval. -/
theorem inverseSqrt_interval (x q scale : Nat) (hx : 0 < x) (hs : 0 < scale)
    (lower : q ^ 2 * x ≤ scale ^ 2)
    (upper : scale ^ 2 < (q + 1) ^ 2 * x) :
    (q : Real) / scale ≤ (Real.sqrt x)⁻¹ ∧
      (Real.sqrt x)⁻¹ < ((q : Real) + 1) / scale := by
  have x_pos : (0 : Real) < x := by exact_mod_cast hx
  have scale_pos : (0 : Real) < scale := by exact_mod_cast hs
  have root_pos : 0 < Real.sqrt (x : Real) := Real.sqrt_pos.mpr x_pos
  have root_sq := Real.sq_sqrt x_pos.le
  have lower_real : (q : Real) ^ 2 * x ≤ (scale : Real) ^ 2 := by exact_mod_cast lower
  have upper_real : (scale : Real) ^ 2 < ((q : Real) + 1) ^ 2 * x := by exact_mod_cast upper
  have q_nonneg : (0 : Real) ≤ q := Nat.cast_nonneg q
  have left_product : (q : Real) * Real.sqrt x ≤ scale := by
    have product_sq : ((q : Real) * Real.sqrt x) ^ 2 ≤ (scale : Real) ^ 2 := by
      nlinarith [sq_nonneg (q : Real)]
    nlinarith
  have right_product : (scale : Real) < ((q : Real) + 1) * Real.sqrt x := by
    have product_sq : (scale : Real) ^ 2 < (((q : Real) + 1) * Real.sqrt x) ^ 2 := by
      nlinarith [sq_nonneg ((q : Real) + 1)]
    have product_nonneg : 0 ≤ ((q : Real) + 1) * Real.sqrt x := by positivity
    nlinarith
  constructor
  · rw [div_le_iff₀ scale_pos, mul_comm, ← div_eq_mul_inv, le_div_iff₀ root_pos]
    exact left_product
  · rw [inv_eq_one_div, div_lt_div_iff₀ root_pos scale_pos, one_mul]
    exact right_product

/-- The executable word approximates the exact target from below. -/
theorem quantizedTurns_interval (x : Input) :
    quantizedTurns x ≤ targetTurns x ∧
      targetTurns x < quantizedTurns x + (phaseScale : Real)⁻¹ := by
  have interval := inverseSqrt_interval x.value (phaseWord x.value) phaseScale
    x.positive phaseScale_pos (phaseWord_lower _ x.positive) (phaseWord_upper _ x.positive)
  simpa [quantizedTurns, targetTurns, add_div, one_div] using interval

/-- The input range implies a uniform lower bound on the allowed phase error. -/
theorem quantizationStep_lt_tolerance (x : Input) :
    (phaseScale : Real)⁻¹ < toleranceTurns x := by
  have hx : (x.value : Real) ≤ 3_133_452 := by
    exact_mod_cast x.le_maxInput
  have root_nonneg := Real.sqrt_nonneg (x.value : Real)
  have root_sq := Real.sq_sqrt (Nat.cast_nonneg x.value : (0 : Real) ≤ x.value)
  have root_pos : 0 < Real.sqrt (x.value : Real) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast x.positive
  have root_bound : Real.sqrt (x.value : Real) < 2048 := by nlinarith
  unfold toleranceTurns targetTurns
  norm_num [phaseScale, phaseBits, precisionBits]
  rw [← div_eq_mul_inv, lt_div_iff₀ root_pos]
  nlinarith

/-- Full-domain Lean proof of the numerical approximation used by the lookup circuit. -/
theorem quantizedTurns_accurate : PhaseAccurate quantizedTurns := by
  intro x
  have interval := quantizedTurns_interval x
  apply (turnDistance_le_abs _ _).trans
  rw [abs_of_nonpos (sub_nonpos.mpr interval.1)]
  have margin := quantizationStep_lt_tolerance x
  linarith [interval.2]

/-- The phase lift used by the exported lookup table. -/
def wrappedTurns (x : Input) : Real := (wrappedPhaseWord x.value : Real) / phaseScale

theorem wrappedTurns_eq (x : Input) :
    wrappedTurns x = quantizedTurns x - (phaseWord x.value / phaseScale : Nat) := by
  have hs : (phaseScale : Real) ≠ 0 := by exact_mod_cast (ne_of_gt phaseScale_pos)
  have division : ((phaseWord x.value % phaseScale : Nat) : Real) +
      (phaseScale : Real) * (phaseWord x.value / phaseScale : Nat) = phaseWord x.value := by
    exact_mod_cast (Nat.mod_add_div (phaseWord x.value) phaseScale)
  unfold wrappedTurns wrappedPhaseWord quantizedTurns
  apply (div_eq_iff hs).mpr
  rw [sub_mul, div_mul_cancel₀ _ hs]
  nlinarith

/-- Reducing the integer word modulo one turn preserves the full-domain bound. -/
theorem wrappedTurns_accurate : PhaseAccurate wrappedTurns := by
  intro x
  have shift := turnDistance_add_int (wrappedTurns x) (targetTurns x)
    (Int.ofNat (phaseWord x.value / phaseScale))
  have cancel : wrappedTurns x +
      ((Int.ofNat (phaseWord x.value / phaseScale)) : Real) = quantizedTurns x := by
    change wrappedTurns x + ((phaseWord x.value / phaseScale : Nat) : Real) = quantizedTurns x
    rw [wrappedTurns_eq]
    exact sub_add_cancel _ _
  rw [cancel] at shift
  rw [← shift]
  exact quantizedTurns_accurate x

end
end QuantumLeanLeap.GoogleVQCC.InvSqrt
