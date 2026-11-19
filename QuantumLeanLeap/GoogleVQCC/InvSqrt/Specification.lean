import Mathlib.Analysis.Normed.Group.AddCircle
import QuantumAlg.Core.Base.UnitaryCircuit
import QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Google VQCC Benchmark I: inverse-square-root phasing

This file states a proof-oriented contract for the first task of Google Quantum
AI's *Verifiable Quantum Circuit Compilation* competition.  It deliberately
separates the implementation-independent mathematical specification from any
particular fixed-point approximation or circuit construction.

The official task acts on a 22-qubit little-endian register `x`, for

`1 ≤ x ≤ 3 * (2^10 - 2)^2 = 3,133,452`.

For every admitted `x`, a successful circuit must preserve `x`, return every
scratch qubit to zero, and apply a phase whose value in turns differs from
`1 / sqrt x` by at most `2^-24 / sqrt x`, modulo one full turn.

The competition verifier samples measurement branches.  The semantic contract
below is stronger: it quantifies over every valid input and asks for an exact
clean basis-state action together with the permitted phase approximation.
-/

namespace QuantumLeanLeap.GoogleVQCC.InvSqrt

open QuantumAlg

noncomputable section

/-- Number of coordinate bits in the competition instance. -/
def positionBits : Nat := 10

/-- Width of the required little-endian input register `x`. -/
def inputWidth : Nat := 2 * positionBits + 2

/-- Largest squared-distance input in the official `n_p = 10` instance. -/
def maxInput : Nat := 3 * (2 ^ positionBits - 2) ^ 2

/-- Relative phase precision required by the official verifier. -/
def precisionBits : Nat := 24

/-- Number of verifier shots per input in the official instance. -/
def shotsPerInput : Nat := 64

@[simp] theorem positionBits_eq : positionBits = 10 := rfl

@[simp] theorem inputWidth_eq : inputWidth = 22 := by
  norm_num [inputWidth, positionBits]

@[simp] theorem maxInput_eq : maxInput = 3_133_452 := by
  norm_num [maxInput, positionBits]

@[simp] theorem precisionBits_eq : precisionBits = 24 := rfl

@[simp] theorem shotsPerInput_eq : shotsPerInput = 64 := rfl

/-- The official input range fits strictly inside a 22-qubit word. -/
theorem maxInput_lt_wordSize : maxInput < 2 ^ inputWidth := by
  norm_num [maxInput, inputWidth, positionBits]

/-- A valid input is a 22-bit word in the official nonzero range. -/
def Input : Type :=
  {x : Fin (2 ^ inputWidth) // 1 ≤ x.val ∧ x.val ≤ maxInput}

noncomputable instance : Fintype Input :=
  Fintype.ofFinset
    (Finset.univ.filter fun x : Fin (2 ^ inputWidth) => 1 ≤ x.val ∧ x.val ≤ maxInput)
    (by
      intro x
      constructor
      · intro member
        exact (Finset.mem_filter.mp member).2
      · intro bounded
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, bounded⟩)

namespace Input

/-- Natural-number value carried by the input word. -/
def value (x : Input) : Nat := x.1.val

/-- Bit `i` of the official little-endian representation: wire zero is the
least-significant bit, wire one has weight two, and so on. -/
def bit (x : Input) (i : Fin inputWidth) : Bool :=
  x.value.testBit i.val

theorem positive (x : Input) : 0 < x.value := x.2.1

theorem le_maxInput (x : Input) : x.value ≤ maxInput := x.2.2

/-- Construct an admitted input from a natural number and its range proof. -/
def ofNat (x : Nat) (hx : 1 ≤ x ∧ x ≤ maxInput) : Input :=
  ⟨⟨x, lt_of_le_of_lt hx.2 maxInput_lt_wordSize⟩, hx⟩

@[simp] theorem value_ofNat (x : Nat) (hx : 1 ≤ x ∧ x ≤ maxInput) :
    (ofNat x hx).value = x := rfl

end Input

/-- Ideal phase, measured in full turns rather than radians. -/
def targetTurns (x : Input) : Real :=
  (Real.sqrt x.value)⁻¹

/-- Allowed absolute phase error, measured in full turns. -/
def toleranceTurns (x : Input) : Real :=
  ((2 : Real) ^ precisionBits)⁻¹ * targetTurns x

/-- The phase target is positive on every admitted input. -/
theorem targetTurns_pos (x : Input) : 0 < targetTurns x := by
  rw [targetTurns]
  apply inv_pos.mpr
  apply Real.sqrt_pos.2
  exact_mod_cast x.positive

/-- The allowed phase error is positive on every admitted input. -/
theorem toleranceTurns_pos (x : Input) : 0 < toleranceTurns x := by
  rw [toleranceTurns]
  exact mul_pos (inv_pos.mpr (pow_pos (by norm_num) _)) (targetTurns_pos x)

/-- Circular distance between two phases expressed in turns.

Using the quotient `ℝ / ℤ` makes the official "modulo one turn" convention part
of the type rather than an informal side condition. -/
def turnDistance (a b : Real) : Real :=
  dist (a : UnitAddCircle) (b : UnitAddCircle)

@[simp] theorem turnDistance_self (a : Real) : turnDistance a a = 0 := by
  simp [turnDistance]

theorem turnDistance_nonneg (a b : Real) : 0 ≤ turnDistance a b :=
  dist_nonneg

theorem turnDistance_comm (a b : Real) : turnDistance a b = turnDistance b a :=
  dist_comm _ _

/-- Adding a whole number of turns does not change circular phase distance. -/
theorem turnDistance_add_int (a b : Real) (turns : Int) :
    turnDistance (a + turns) b = turnDistance a b := by
  simp [turnDistance]

/-- A proposed phase function meets the official pointwise error target. -/
def PhaseAccurate (phaseTurns : Input → Real) : Prop :=
  ∀ x, turnDistance (phaseTurns x) (targetTurns x) ≤ toleranceTurns x

/-- Exact ideal phases satisfy the approximation requirement. -/
theorem phaseAccurate_target : PhaseAccurate targetTurns := by
  intro x
  simp only [turnDistance_self]
  exact (toleranceTurns_pos x).le

/-- Convert a phase in turns to its unit complex scalar. -/
def phaseScalar (turns : Real) : Complex :=
  Complex.exp (((2 * Real.pi * turns : Real) : Complex) * Complex.I)

@[simp] theorem norm_phaseScalar (turns : Real) : ‖phaseScalar turns‖ = 1 := by
  rw [phaseScalar, Complex.norm_exp]
  simp

/-- Total register width for a candidate with `scratchWidth` auxiliary qubits. -/
def totalWidth (scratchWidth : Nat) : Nat := inputWidth + scratchWidth

/-- Embed the 22-bit input value into the full input-plus-scratch word.

The numeric value is unchanged, so every higher scratch bit is zero. -/
def cleanWord (scratchWidth : Nat) (x : Input) : Fin (2 ^ totalWidth scratchWidth) :=
  ⟨x.value, by
    apply lt_of_lt_of_le x.1.isLt
    simp only [totalWidth, pow_add]
    exact Nat.le_mul_of_pos_right (2 ^ inputWidth) (by positivity)⟩

@[simp] theorem cleanWord_val (scratchWidth : Nat) (x : Input) :
    (cleanWord scratchWidth x).val = x.value := rfl

/-- Computational basis state with numeric label `x`, hence input in the low
bits and scratch in the high bits. In QuantumAlg's big-endian tensor notation
this is `|0...0⟩ ⊗ |x⟩`; exported little-endian wire numbers are reversed by
`physicalPosition` in the restricted circuit compiler. -/
def cleanBasis (scratchWidth : Nat) (x : Input) :
    NormalizedVector (Qubits (totalWidth scratchWidth)) :=
  NormalizedVector.ket (cleanWord scratchWidth x)

/-- Implementation-independent semantic certificate for an inverse-square-root
phase operator.

`basis_action` simultaneously states input restoration, scratch cleanup, and
the retained coherent phase.  Since `operator` is unitary and the statement is
pointwise on a basis, linearity supplies the corresponding action on arbitrary
superpositions of valid inputs. -/
structure SemanticCertificate (scratchWidth : Nat) where
  /-- Complete operator on the input and all scratch qubits. -/
  operator : UnitaryOperator (Qubits (totalWidth scratchWidth))
  /-- Phase actually realized by the operator, in turns. -/
  realizedTurns : Input → Real
  /-- Exact clean action on every admitted computational-basis input. -/
  basis_action : ∀ x,
    operator.applyVec (cleanBasis scratchWidth x).vec =
      phaseScalar (realizedTurns x) • (cleanBasis scratchWidth x).vec
  /-- Pointwise phase error is within the competition tolerance modulo one turn. -/
  accurate : PhaseAccurate realizedTurns

namespace SemanticCertificate

/-- The basis-state contract extends coherently to every superposition supported
on valid competition inputs. -/
theorem apply_superposition {scratchWidth : Nat}
    (certificate : SemanticCertificate scratchWidth) (amplitude : Input → Complex) :
    certificate.operator.applyVec
        (∑ x, amplitude x • (cleanBasis scratchWidth x).vec) =
      ∑ x, (amplitude x * phaseScalar (certificate.realizedTurns x)) •
        (cleanBasis scratchWidth x).vec := by
  classical
  have apply_zero : certificate.operator.applyVec 0 = 0 := by
    ext index
    change (∑ column, certificate.operator index column * 0) = 0
    simp
  have apply_add (left right : HilbertVector (Qubits (totalWidth scratchWidth))) :
      certificate.operator.applyVec (left + right) =
        certificate.operator.applyVec left + certificate.operator.applyVec right := by
    ext index
    change (∑ column, certificate.operator index column * (left column + right column)) =
      (∑ column, certificate.operator index column * left column) +
        ∑ column, certificate.operator index column * right column
    simp only [mul_add, Finset.sum_add_distrib]
  have apply_smul (scalar : Complex)
      (vector : HilbertVector (Qubits (totalWidth scratchWidth))) :
      certificate.operator.applyVec (scalar • vector) =
        scalar • certificate.operator.applyVec vector := by
    ext index
    change (∑ column, certificate.operator index column * (scalar * vector column)) =
      scalar * ∑ column, certificate.operator index column * vector column
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro column _
    ring
  induction (Finset.univ : Finset Input) using Finset.induction_on with
  | empty => simpa using apply_zero
  | @insert x inputs absent induction =>
      simp only [Finset.sum_insert absent]
      rw [apply_add, apply_smul, certificate.basis_action, smul_smul, induction]

end SemanticCertificate

/-- A QuantumAlg unitary circuit certificate.  This is the submission interface
for future measurement-free circuit search; its semantics are tied directly to
the circuit's actual matrix rather than to a separately asserted operator. -/
structure CircuitCertificate (gates : GateModel) (oracles : OracleModel)
    (environment : oracles.Interpretation) (scratchWidth : Nat) where
  /-- Candidate circuit on the canonical input-plus-scratch layout. -/
  circuit : UnitaryCircuit gates oracles
    (QuantumSignature.qubits (totalWidth scratchWidth)).canonicalPlacement.layout
  /-- Phase actually realized by the candidate, in turns. -/
  realizedTurns : Input → Real
  /-- The actual circuit restores the input and cleans scratch on every valid input. -/
  basis_action : ∀ x,
    (circuit.binaryMatrix environment).applyVec
        (NormalizedVector.ket (cleanWord scratchWidth x)).vec =
      phaseScalar (realizedTurns x) •
        (NormalizedVector.ket (cleanWord scratchWidth x)).vec
  /-- The realized phase obeys the official tolerance modulo one turn. -/
  accurate : PhaseAccurate realizedTurns

namespace CircuitCertificate

/-- Forget circuit syntax and retain its complete mathematical action. -/
def toSemantic {gates : GateModel} {oracles : OracleModel}
    {environment : oracles.Interpretation} {scratchWidth : Nat}
    (certificate : CircuitCertificate gates oracles environment scratchWidth) :
    SemanticCertificate scratchWidth where
  operator := certificate.circuit.binaryMatrix environment
  realizedTurns := certificate.realizedTurns
  basis_action := certificate.basis_action
  accurate := certificate.accurate

end CircuitCertificate

/-- The official verifier executes this many shots over its complete input domain. -/
def totalVerifierShots : Nat := maxInput * shotsPerInput

@[simp] theorem totalVerifierShots_eq : totalVerifierShots = 200_540_928 := by
  norm_num [totalVerifierShots, maxInput, shotsPerInput, positionBits]

end

end QuantumLeanLeap.GoogleVQCC.InvSqrt
