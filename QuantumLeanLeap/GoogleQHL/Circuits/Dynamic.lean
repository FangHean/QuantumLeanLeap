import QuantumLeanLeap.GoogleQHL.Circuits.Gates
import QuantumLeanLeap.GoogleQHL.Composition
import QuantumLeanLeap.GoogleQHL.ExpectedCost

namespace QuantumLeanLeap.GoogleQHL.Circuits
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {n : Nat}

/-- Concrete gates, mid-circuit projective measurement, and classical control.
No arbitrary unitary, oracle, or supplied cost certificate is a constructor. -/
inductive DynamicCircuit (Var : Type) (n : Nat) where
  | skip
  | gate (g : PrimitiveGate n)
  | measure (target : Var) (wire : Fin n)
  | seq (a b : DynamicCircuit Var n)
  | branch (guard : Store Var → Bool) (a b : DynamicCircuit Var n)

noncomputable def DynamicCircuit.compile : DynamicCircuit Var n → QProg Var (2 ^ n)
  | .skip => .skip
  | .gate g => .apply g.unitary
  | .measure target wire => .measure target 2 (wireMeasurement wire)
  | .seq a b => .seq a.compile b.compile
  | .branch g a b => .qif g a.compile b.compile

/-- Independent structural forward semantics on measurement histories. -/
noncomputable def DynamicCircuit.run [DecidableEq Var] :
    DynamicCircuit Var n → Branch Var (2 ^ n) → List (Branch Var (2 ^ n))
  | .skip, input => [input]
  | .gate g, input => [(input.1, conjugate g.unitary.matrix input.2)]
  | .measure v q, input => (List.finRange 2).map (fun o =>
      (Function.update input.1 v (Int.ofNat o.val), conjugate (wireProjector q o) input.2))
  | .seq a b, input => (a.run input).flatMap b.run
  | .branch g a b, input => if g input.1 then a.run input else b.run input

theorem DynamicCircuit.compile_correct [DecidableEq Var] (c : DynamicCircuit Var n)
    (fuel : Nat) (input : Branch Var (2 ^ n)) :
    interpApprox c.compile fuel input = c.run input := by
  induction c generalizing input with
  | skip => rfl
  | gate g => rfl
  | measure v q => rfl
  | seq a b iha ihb =>
      simp only [compile, interpApprox, run, iha]
      congr 1
      funext x
      exact ihb x
  | branch g a b iha ihb => simp only [compile, interpApprox, run, iha, ihb]

theorem DynamicCircuit.run_positive [DecidableEq Var] (c : DynamicCircuit Var n)
    (input : Branch Var (2 ^ n)) (hr : input.2.PosSemidef) :
    ∀ out ∈ c.run input, out.2.PosSemidef := by
  rw [← c.compile_correct 0 input]
  exact interpApprox_positive c.compile 0 input hr

theorem DynamicCircuit.run_mass_le [DecidableEq Var] (c : DynamicCircuit Var n)
    (input : Branch Var (2 ^ n)) (hr : input.2.PosSemidef) :
    branchMass (c.run input) ≤ input.2.trace.re := by
  rw [← c.compile_correct 0 input]
  exact interpApprox_trace_nonincreasing c.compile 0 input hr

theorem DynamicCircuit.expect_wp [DecidableEq Var] (c : DynamicCircuit Var n)
    (Q : CQAssertion Var (2 ^ n)) (input : Branch Var (2 ^ n)) (hr : input.2.PosSemidef) :
    branchExpectation Q.toPredicate (c.run input) = pairing (wp c.compile Q input.1).matrix input.2 := by
  have h := GoogleQHL.expect_wp c.compile Q input hr
  simpa only [limitExpectation, c.compile_correct, ciSup_const] using h

/-- A configurable weighted worst-path count. Measurements have zero gate cost. -/
def DynamicCircuit.worstGates (w : GateKind → Nat) : DynamicCircuit Var n → Nat
  | .skip => 0
  | .gate g => w g.kind
  | .measure .. => 0
  | .seq a b => a.worstGates w + b.worstGates w
  | .branch _ a b => max (a.worstGates w) (b.worstGates w)

def DynamicCircuit.gateCount (kind : GateKind) (c : DynamicCircuit Var n) : Nat :=
  c.worstGates (fun k => if k = kind then 1 else 0)

/-- Expected gate cost tracks the same histories as `run`; it does not charge
every measured branch as if it had probability one. -/
noncomputable def DynamicCircuit.runCost [DecidableEq Var] (w : GateKind → Nat) :
    DynamicCircuit Var n → Branch Var (2 ^ n) → Real
  | .skip, _ => 0
  | .gate g, input => w g.kind * input.2.trace.re
  | .measure .., _ => 0
  | .seq a b, input => a.runCost w input + ((a.run input).map (b.runCost w)).sum
  | .branch g a b, input => if g input.1 then a.runCost w input else b.runCost w input

theorem DynamicCircuit.runCost_le [DecidableEq Var] (w : GateKind → Nat)
    (c : DynamicCircuit Var n) (input : Branch Var (2 ^ n)) (hr : input.2.PosSemidef) :
    c.runCost w input ≤ c.worstGates w * input.2.trace.re := by
  have ht : 0 ≤ input.2.trace.re := (RCLike.nonneg_iff.mp hr.trace_nonneg).1
  induction c generalizing input with
  | skip => simp [runCost, worstGates]
  | gate g => exact le_rfl
  | measure v q => simp [runCost, worstGates]
  | seq a b iha ihb =>
      have hs := sum_cost_le_mass (a.run input) (b.runCost w) (b.worstGates w)
        (fun out hout => ihb out (a.run_positive input hr out hout)
          (RCLike.nonneg_iff.mp (a.run_positive input hr out hout).trace_nonneg).1)
      have hm := mul_le_mul_of_nonneg_left (a.run_mass_le input hr)
        (Nat.cast_nonneg (b.worstGates w) : (0 : Real) ≤ _)
      simpa [runCost, worstGates, Nat.cast_add, add_mul] using add_le_add (iha input hr ht) (hs.trans hm)
  | branch g a b iha ihb =>
      simp only [runCost, worstGates]
      split
      · exact (iha input hr ht).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_max_left (a.worstGates w) (b.worstGates w)) ht)
      · exact (ihb input hr ht).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_max_right (a.worstGates w) (b.worstGates w)) ht)

end QuantumLeanLeap.GoogleQHL.Circuits
