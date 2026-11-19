import QuantumLeanLeap.GoogleQHL.Compatibility.Physlib
import QuantumLeanLeap.GoogleQHL.StatePrimitives

/-! Public call shapes shown in Appendix A of arXiv:2611.09822v2.
This is a checked adapter, not an assertion of unreleased Google namespace,
constructor ordering, or binary compatibility. -/
namespace QuantumLeanLeap.GoogleQHL.PaperAPI
open scoped ComplexOrder MatrixOrder

abbrev Unitary := GoogleQHL.Unitary
abbrev Measurement := GoogleQHL.Measurement

/-- The paper uses positive dimension, zero reset, and decidable Prop guards. -/
inductive QProg (Var : Type) (d : Nat) [NeZero d] where
  | skip
  | abort
  | assign (target : Var) (expression : Store Var → Int)
  | qset
  | apply (U : Unitary d)
  | measure (target : Var) (outcomes : Nat) (M : Measurement d outcomes)
  | seq (a b : QProg Var d)
  | qif (g : Store Var → Prop) [DecidablePred g] (a b : QProg Var d)
  | qwhile (g : Store Var → Prop) [DecidablePred g] (body : QProg Var d)

variable {Var : Type} {d : Nat} [NeZero d]

def QProg.toCore : QProg Var d → GoogleQHL.QProg Var d
  | .skip => .skip
  | .abort => .abort
  | .assign v e => .assign v e
  | .qset => .qset 0
  | .apply U => .apply U
  | .measure v n M => .measure v n M
  | .seq a b => .seq a.toCore b.toCore
  | @QProg.qif _ _ _ g dec a b => .qif (fun s => @decide (g s) (dec s)) a.toCore b.toCore
  | @QProg.qwhile _ _ _ g dec body => .qwhile (fun s => @decide (g s) (dec s)) body.toCore

/-- Only the paper's exposed toStateFun projection is specified here. -/
structure StateTransformer (Var : Type) (d : Nat) where
  toStateFun : CQState Var d → CQState Var d

noncomputable def interp [DecidableEq Var] (p : QProg Var d) : StateTransformer Var d :=
  ⟨fun S => CQState.ofCore (GoogleQHL.interp p.toCore S.toCore)⟩

noncomputable def wp [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d) : CQAssertion Var d :=
  CQAssertion.ofCore (GoogleQHL.wp p.toCore Q.toCore)

def Triple [DecidableEq Var] (P : CQAssertion Var d) (p : QProg Var d)
    (Q : CQAssertion Var d) : Prop :=
  ∀ S : CQState Var d, expect S P ≤ expect ((interp p).toStateFun S) Q

/-- Same argument order and equality direction as the printed paper theorem. -/
theorem expect_wp [DecidableEq Var] (p : QProg Var d) (S : CQState Var d)
    (Q : CQAssertion Var d) :
    expect S (wp p Q) = expect ((interp p).toStateFun S) Q := by
  rw [expect_eq_core, expect_eq_core]
  simp only [wp, interp, assertion_toCore_ofCore, state_toCore_ofCore]
  exact (GoogleQHL.expect_interp p.toCore S.toCore Q.toCore).symm

theorem triple_iff_core [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d) :
    Triple P p Q ↔ GoogleQHL.Triple P.toCore p.toCore Q.toCore := by
  constructor
  · intro h S
    have hh := h (CQState.ofCore S)
    simpa only [expect_eq_core, interp, state_toCore_ofCore] using hh
  · intro h S
    simpa only [expect_eq_core, interp, state_toCore_ofCore] using h S.toCore

theorem triple_iff [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d) :
    Triple P p Q ↔ P ≤ wp p Q := by
  rw [triple_iff_core, GoogleQHL.triple_iff]
  constructor
  · intro h s
    apply (observable_le_iff _ _).mpr
    exact h s
  · intro h s
    exact (observable_le_iff _ _).mp (h s)

theorem wp_soundness [DecidableEq Var] (p : QProg Var d) (Q : CQAssertion Var d) :
    Triple (wp p Q) p Q := (triple_iff _ _ _).mpr le_rfl

theorem wp_weakest [DecidableEq Var] (P Q : CQAssertion Var d) (p : QProg Var d)
    (h : Triple P p Q) : P ≤ wp p Q := (triple_iff _ _ _).mp h

theorem wp_mono [DecidableEq Var] (p : QProg Var d) : Monotone (wp p) := by
  intro P Q h s
  apply (observable_le_iff _ _).mpr
  exact GoogleQHL.wp_mono p.toCore P.toCore Q.toCore
    (fun s => (observable_le_iff _ _).mp (h s)) s

theorem interp_seq [DecidableEq Var] (a b : QProg Var d) (S : CQState Var d) :
    (interp (.seq a b)).toStateFun S = (interp b).toStateFun ((interp a).toStateFun S) := by
  simp only [interp, QProg.toCore, state_toCore_ofCore, GoogleQHL.interp_seq]

theorem wp_seq [DecidableEq Var] (a b : QProg Var d) (Q : CQAssertion Var d) :
    wp (.seq a b) Q = wp a (wp b Q) := by
  funext s
  apply Subtype.ext
  apply HermitianMat.ext
  simpa only [wp, QProg.toCore, assertion_toCore_ofCore, CQAssertion.ofCore, Observable.ofCore,
    HermitianMat.mat_mk] using GoogleQHL.wp_seq a.toCore b.toCore Q.toCore s

theorem wp_qif [DecidableEq Var] (g : Store Var → Prop) [DecidablePred g]
    (a b : QProg Var d) (Q : CQAssertion Var d) (s : Store Var) :
    wp (.qif g a b) Q s = if g s then wp a Q s else wp b Q s := by
  apply Subtype.ext
  apply HermitianMat.ext
  by_cases hg : g s <;>
    simp [wp, QProg.toCore, CQAssertion.ofCore, Observable.ofCore, GoogleQHL.wp_if, hg]
  all_goals rfl

noncomputable def wpOrderHom [DecidableEq Var] (p : QProg Var d) :
    CQAssertion Var d →o CQAssertion Var d := ⟨wp p, wp_mono p⟩

theorem wp_qwhile_unfold [DecidableEq Var] (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) (s : Store Var) :
    wp (.qwhile g body) Q s = if g s then wp body (wp (.qwhile g body) Q) s else Q s := by
  apply Subtype.ext
  apply HermitianMat.ext
  by_cases hg : g s <;>
    simp [wp, QProg.toCore, CQAssertion.ofCore, Observable.ofCore, GoogleQHL.wp_while_unfold,
      assertion_toCore_ofCore, hg]
  all_goals rfl

end QuantumLeanLeap.GoogleQHL.PaperAPI
