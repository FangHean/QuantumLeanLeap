import QuantumLeanLeap.GoogleVQCC.InvSqrt.Newton
import Mathlib.Data.Nat.Log

namespace QuantumLeanLeap.GoogleVQCC.InvSqrt

def newtonBits : Nat := 37
def newtonScale : Nat := 2 ^ newtonBits

/-- A power-of-two seed, requiring only the position of the leading bit. -/
def newtonSeed (x : Nat) : Nat := newtonScale / 2 ^ (Nat.log 4 x + 1)

/-- One exact integer Newton step. Division is downward truncation, not an
idealized real operation. On the proven invariant the Nat subtraction is exact. -/
def newtonWordStep (x q : Nat) : Nat :=
  q * (3 * newtonScale ^ 2 - x * q ^ 2) / (2 * newtonScale ^ 2)

def newtonWord (x : Nat) : Nat → Nat
  | 0 => newtonSeed x
  | i + 1 => newtonWordStep x (newtonWord x i)

noncomputable section

def newtonTurns (x : Input) : Real := (newtonWord x.value 6 : Real) / newtonScale

theorem newtonScale_pos : 0 < newtonScale := by norm_num [newtonScale, newtonBits]

theorem newton_root_bound (x : Input) : Real.sqrt (x.value : Real) < 2048 := by
  have hx : (x.value : Real) ≤ 3133452 := by exact_mod_cast x.le_maxInput
  have hs := Real.sq_sqrt (Nat.cast_nonneg x.value : (0 : Real) ≤ x.value)
  have hp := Real.sqrt_nonneg (x.value : Real)
  nlinarith

theorem newton_seed_turns (x : Input) :
    (newtonSeed x.value : Real) / newtonScale = 1 / (2 : Real) ^ (Nat.log 4 x.value + 1) := by
  have hk : Nat.log 4 x.value < 11 := by
    apply Nat.log_lt_of_lt_pow (ne_of_gt x.positive)
    have := x.le_maxInput
    norm_num [maxInput, positionBits] at this ⊢
    omega
  have hd : 2 ^ (Nat.log 4 x.value + 1) ∣ newtonScale := by
    apply pow_dvd_pow
    simp only [newtonBits]
    omega
  have hs : (newtonScale : Real) ≠ 0 := by exact_mod_cast ne_of_gt newtonScale_pos
  unfold newtonSeed
  rw [Nat.cast_div hd (by positivity)]
  push_cast
  field_simp

theorem newton_seed_defect (x : Input) :
    0 ≤ 1 - Real.sqrt x.value * ((newtonSeed x.value : Real) / newtonScale) ∧
    1 - Real.sqrt x.value * ((newtonSeed x.value : Real) / newtonScale) ≤ 1 / 2 := by
  have power (k : Nat) : ((2 : Real) ^ k) ^ 2 = (4 : Real) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have lower : (4 : Real) ^ Nat.log 4 x.value ≤ x.value := by
    exact_mod_cast Nat.pow_log_le_self 4 (ne_of_gt x.positive)
  have upper : (x.value : Real) < (4 : Real) ^ (Nat.log 4 x.value + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) x.value
  rw [← power] at lower upper
  have root_sq := Real.sq_sqrt (Nat.cast_nonneg x.value : (0 : Real) ≤ x.value)
  have root_nonneg := Real.sqrt_nonneg (x.value : Real)
  have lp : (0 : Real) < 2 ^ Nat.log 4 x.value := by positivity
  have up : (0 : Real) < 2 ^ (Nat.log 4 x.value + 1) := by positivity
  have root_lower : (2 : Real) ^ Nat.log 4 x.value ≤ Real.sqrt x.value := by nlinarith
  have root_upper : Real.sqrt x.value ≤ (2 : Real) ^ (Nat.log 4 x.value + 1) := by nlinarith
  rw [newton_seed_turns, mul_one_div]
  have a : Real.sqrt x.value / (2 : Real) ^ (Nat.log 4 x.value + 1) ≤ 1 :=
    (div_le_one up).mpr root_upper
  have b : (1 : Real) / 2 ≤ Real.sqrt x.value / (2 : Real) ^ (Nat.log 4 x.value + 1) := by
    apply (le_div_iff₀ up).mpr
    rw [pow_succ]
    nlinarith
  constructor <;> linarith

/-- Exact connection between the Nat implementation and real Newton, including
the truncation interval and the condition ensuring no saturating subtraction. -/
theorem newtonWordStep_interval (x q : Nat) (hq : x * q ^ 2 ≤ newtonScale ^ 2) :
    (newtonWordStep x q : Real) / newtonScale ≤
      newtonStep x ((q : Real) / newtonScale) ∧
    newtonStep x ((q : Real) / newtonScale) <
      (newtonWordStep x q : Real) / newtonScale + (newtonScale : Real)⁻¹ := by
  let numerator := q * (3 * newtonScale ^ 2 - x * q ^ 2)
  let denominator := 2 * newtonScale ^ 2
  have hp : 0 < denominator := by norm_num [denominator, newtonScale, newtonBits]
  have hpR : (0 : Real) < denominator := by exact_mod_cast hp
  have hsR : (0 : Real) < newtonScale := by exact_mod_cast newtonScale_pos
  have hsub : x * q ^ 2 ≤ 3 * newtonScale ^ 2 := by omega
  have numcast : (numerator : Real) =
      (q : Real) * (3 * (newtonScale : Real) ^ 2 - (x : Real) * (q : Real) ^ 2) := by
    dsimp [numerator]
    rw [Nat.cast_mul, Nat.cast_sub hsub]
    push_cast
    rfl
  have identity : (numerator : Real) / denominator / newtonScale =
      newtonStep x ((q : Real) / newtonScale) := by
    rw [numcast]
    dsimp [denominator, newtonStep]
    push_cast
    field_simp
  have low : ((numerator / denominator : Nat) : Real) ≤ (numerator : Real) / denominator := by
    apply (le_div_iff₀ hpR).mpr
    exact_mod_cast Nat.div_mul_le_self numerator denominator
  have high : (numerator : Real) / denominator < ((numerator / denominator : Nat) : Real) + 1 := by
    apply (div_lt_iff₀ hpR).mpr
    have h := Nat.lt_mul_div_succ numerator hp
    rw [Nat.mul_comm denominator] at h
    exact_mod_cast h
  have low' := div_le_div_of_nonneg_right low hsR.le
  have high' := div_lt_div_of_pos_right high hsR
  rw [identity] at low' high'
  constructor
  · exact low'
  · simpa [add_div, one_div, numerator, denominator, newtonWordStep] using high'

theorem newtonWord_defect (x : Input) (i : Nat) (hi : i ≤ 6) :
    0 ≤ 1 - Real.sqrt x.value * ((newtonWord x.value i : Real) / newtonScale) ∧
    1 - Real.sqrt x.value * ((newtonWord x.value i : Real) / newtonScale) ≤ newtonBudget i := by
  induction i with
  | zero => simpa [newtonWord, newtonBudget] using newton_seed_defect x
  | succ i ih =>
    have iprev : i < 6 := by omega
    have previous := ih (by omega)
    have bounds := newtonBudget_step i iprev
    have root_nonneg := Real.sqrt_nonneg (x.value : Real)
    have root_sq := Real.sq_sqrt (Nat.cast_nonneg x.value : (0 : Real) ≤ x.value)
    have hsR : (0 : Real) < newtonScale := by exact_mod_cast newtonScale_pos
    have product : Real.sqrt x.value * (newtonWord x.value i : Real) ≤ newtonScale := by
      have := previous.1
      rw [← mul_div_assoc] at this
      have : Real.sqrt x.value * (newtonWord x.value i : Real) / newtonScale ≤ 1 := by linarith
      exact (div_le_one hsR).mp this
    have invariant : x.value * newtonWord x.value i ^ 2 ≤ newtonScale ^ 2 := by
      have hreal : (x.value : Real) * (newtonWord x.value i : Real) ^ 2 ≤ (newtonScale : Real) ^ 2 := by
        have hprod0 := mul_nonneg root_nonneg (Nat.cast_nonneg (newtonWord x.value i) : (0 : Real) ≤ _)
        have hprodSq : (Real.sqrt x.value * (newtonWord x.value i : Real)) ^ 2 ≤ (newtonScale : Real) ^ 2 := by
          nlinarith
        nlinarith [sq_nonneg (newtonWord x.value i : Real)]
      exact_mod_cast hreal
    have interval := newtonWordStep_interval x.value (newtonWord x.value i) invariant
    have roundBound : Real.sqrt x.value *
        (newtonStep x.value ((newtonWord x.value i : Real) / newtonScale) -
          (newtonWordStep x.value (newtonWord x.value i) : Real) / newtonScale) ≤ 1 / 2 ^ 26 := by
      have root_bound := newton_root_bound x
      have ht := mul_le_mul_of_nonneg_left (le_of_lt interval.2) root_nonneg
      norm_num [newtonScale, newtonBits] at ht ⊢
      nlinarith
    exact rounded_newton_defect_bound _ _ _ _ _ _ root_sq root_nonneg
      previous.1 previous.2 bounds.1 bounds.2.1 interval.1 roundBound |>.imp_right
        (fun h => h.trans bounds.2.2)

/-- Full-domain correctness of the six-step EXECUTABLE integer algorithm. -/
theorem newtonTurns_accurate : PhaseAccurate newtonTurns := by
  apply phaseAccurate_of_relative_defect
  intro x
  simpa [newtonTurns, newtonBudget] using newtonWord_defect x 6 (by omega)

end
end QuantumLeanLeap.GoogleVQCC.InvSqrt
