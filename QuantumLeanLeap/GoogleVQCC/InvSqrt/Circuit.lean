import QuantumLeanLeap.GoogleVQCC.InvSqrt.Specification
import QuantumAlg.Components.Gates.Construction
import QuantumAlg.Components.Gates.PhaseOperator

/-! A closed, measurement-free competition instruction subset. All parameters
are rational and all wires are bounded. No arbitrary unitary or oracle can be
supplied by a candidate. Compilation uses QuantumAlg's native placed gates.
This subset supports lookup and phase-polynomial baselines; HMR is not modeled. -/

namespace QuantumLeanLeap.GoogleVQCC.InvSqrt
open QuantumAlg

/-- Wire indices in exported circuits are little endian. QuantumAlg's canonical
binary matrix uses big-endian physical positions, so reverse at compilation. -/
def physicalPosition {n : Nat} (wire : Fin n) : Fin n := wire.rev

theorem physicalPosition_injective (n : Nat) :
    Function.Injective (@physicalPosition n) := by
  intro a b same
  have := congrArg Fin.rev same
  simpa [physicalPosition] using this

@[simp] theorem physicalPosition_val {n : Nat} (wire : Fin n) :
    (physicalPosition wire).val = n - 1 - wire.val := by
  simp [physicalPosition, Fin.rev]
  omega

/-- Allowed gates for this first synthesis backend. `zPow` is in HALF turns,
matching kickmix Z_POW: the one branch acquires exp(i*pi*t). -/
inductive Instruction (n : Nat) where
  | x (target : Fin n)
  | cx (control target : Fin n) (distinct : control ≠ target)
  | ccx (a b target : Fin n) (ab : a ≠ b) (aTarget : a ≠ target) (bt : b ≠ target)
  | zPow (target : Fin n) (halfTurns : Rat)

def Instruction.toffolis {n : Nat} : Instruction n → Nat
  | .ccx .. => 1
  | _ => 0

def Instruction.rotations {n : Nat} : Instruction n → Nat
  | .zPow .. => 1
  | _ => 0

noncomputable section

abbrev physicalLayout (n : Nat) :=
  (QuantumSignature.qubits n).canonicalPlacement.layout

/-- One typed instruction becomes one actual QuantumAlg native gate. -/
def Instruction.compile {n : Nat} (gate : Instruction n) :
    UnitaryCircuit AlgorithmGate.model OracleModel.empty (physicalLayout n) :=
  match gate with
  | .x target => Gate.singleQubitAt (physicalLayout n) .empty Gate.XOp
      (physicalPosition target) rfl
  | .cx control target distinct => Gate.cnotAt (physicalLayout n) .empty
      (physicalPosition control) (physicalPosition target)
      (fun same => distinct (physicalPosition_injective n same)) rfl rfl
  | .ccx a b target ab aTarget bt => Gate.toffoliAt (physicalLayout n) .empty
      (physicalPosition a) (physicalPosition b) (physicalPosition target)
      (fun same => ab (physicalPosition_injective n same))
      (fun same => aTarget (physicalPosition_injective n same))
      (fun same => bt (physicalPosition_injective n same)) rfl rfl rfl
  | .zPow target halfTurns => Gate.singleQubitAt (physicalLayout n) .empty
      (phaseGateOp (Real.pi * (halfTurns : Real))) (physicalPosition target) rfl

/-- The circuit and its event trace are both derived from this instruction list. -/
def compile {n : Nat} : List (Instruction n) →
    UnitaryCircuit AlgorithmGate.model OracleModel.empty (physicalLayout n)
  | [] => .identity _ _ _
  | gate :: rest => gate.compile.seq (compile rest)

theorem Instruction.compile_trace_length {n : Nat} (gate : Instruction n) :
    gate.compile.eventTrace.length = 1 := by
  cases gate <;> rfl

/-- Gate accounting observes the same compiled circuit, not a candidate claim. -/
theorem compile_trace_length {n : Nat} (gates : List (Instruction n)) :
    (compile gates).eventTrace.length = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change (gate.compile.eventTrace ++ (compile rest).eventTrace).length = _
      rw [List.length_append, Instruction.compile_trace_length, ih]
      simp [Nat.add_comm]

/-- Closed submission target: restricted gate list, no oracle, and actual
compiled semantics. Construction still requires both nontrivial proofs. -/
structure VerifiedCandidate (scratchWidth : Nat) where
  instructions : List (Instruction (totalWidth scratchWidth))
  realizedTurns : Input → Real
  basis_action : ∀ x,
    ((compile instructions).binaryMatrix OracleModel.emptyInterpretation).applyVec
        (cleanBasis scratchWidth x).vec =
      phaseScalar (realizedTurns x) • (cleanBasis scratchWidth x).vec
  accurate : PhaseAccurate realizedTurns

def VerifiedCandidate.certificate {scratchWidth : Nat}
    (candidate : VerifiedCandidate scratchWidth) :
    CircuitCertificate AlgorithmGate.model OracleModel.empty
      OracleModel.emptyInterpretation scratchWidth where
  circuit := compile candidate.instructions
  realizedTurns := candidate.realizedTurns
  basis_action := candidate.basis_action
  accurate := candidate.accurate

end
end QuantumLeanLeap.GoogleVQCC.InvSqrt
