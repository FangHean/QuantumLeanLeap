import QuantumLeanLeap.GoogleQHL.Compatibility.PaperAPI
import Mathlib.Order.OmegaCompletePartialOrder

/-! Standard Mathlib omega-CPO instances for the paper-facing interface.
Only increasing chains have suprema here; no arbitrary lattice join of
noncommuting effects is assumed. -/
namespace QuantumLeanLeap.GoogleQHL.PaperAPI
open scoped ComplexOrder MatrixOrder
open OmegaCompletePartialOrder
variable {Var : Type} {d : Nat}

noncomputable def observableChainMatrix (c : Chain (Observable d)) (n : Nat) : GoogleQHL.Operator d :=
  (Observable.toCore (c n)).matrix

theorem observableChain_effect (c : Chain (Observable d)) (n : Nat) :
    GoogleQHL.IsEffect (observableChainMatrix c n) :=
  ⟨(Observable.toCore (c n)).nonnegative, (Observable.toCore (c n)).le_identity⟩

theorem observableChain_mono (c : Chain (Observable d)) : Monotone (observableChainMatrix c) :=
  fun _ _ h => (observable_le_iff _ _).mp (c.monotone h)

noncomputable def observableSup (c : Chain (Observable d)) : Observable d :=
  Observable.ofCore (GoogleQHL.effectSup (observableChainMatrix c)
    (observableChain_effect c) (observableChain_mono c))

theorem observableSup_isLUB (c : Chain (Observable d)) :
    IsLUB (Set.range c) (observableSup c) := by
  have h := GoogleQHL.effectSup_isLUB (observableChainMatrix c)
    (observableChain_effect c) (observableChain_mono c)
  constructor
  · rintro _ ⟨n, rfl⟩
    exact (observable_le_iff _ _).mpr (h.1 (Set.mem_range_self n))
  · intro B hB
    apply (observable_le_iff _ _).mpr
    apply h.2
    rintro _ ⟨n, rfl⟩
    exact (observable_le_iff _ _).mp (hB (Set.mem_range_self n))

noncomputable instance observableOmegaCPO : OmegaCompletePartialOrder (Observable d) where
  ωSup := observableSup
  le_ωSup c n := (observableSup_isLUB c).1 (Set.mem_range_self n)
  ωSup_le c B h := (observableSup_isLUB c).2 (by rintro _ ⟨n, rfl⟩; exact h n)

instance observableOrderBot : OrderBot (Observable d) where
  bot := ⟨0, le_rfl, HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one⟩
  bot_le E := E.property.1

/-- CQAssertion obtains the pointwise omega-CPO and bottom from Mathlib's Pi instances. -/
example : Nonempty (OmegaCompletePartialOrder (CQAssertion Var d)) := ⟨inferInstance⟩

theorem stateChain_mono (c : Chain (CQState Var d)) (s : Store Var) :
    Monotone (fun n => ((c n).toCore.density s).matrix) :=
  fun _ _ h => (state_le_iff _ _).mp (c.monotone h) s

noncomputable def cqStateSup (c : Chain (CQState Var d)) : CQState Var d :=
  CQState.ofCore (GoogleQHL.stateSup (fun n => (c n).toCore) (stateChain_mono c))

theorem cqStateSup_isLUB (c : Chain (CQState Var d)) : IsLUB (Set.range c) (cqStateSup c) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    apply (state_le_iff _ _).mpr
    intro s
    simp only [cqStateSup, state_toCore_ofCore]
    exact (GoogleQHL.stateSup_density_isLUB _ (stateChain_mono c) s).1 (Set.mem_range_self n)
  · intro T hT
    apply (state_le_iff _ _).mpr
    intro s
    simp only [cqStateSup, state_toCore_ofCore]
    apply (GoogleQHL.stateSup_density_isLUB _ (stateChain_mono c) s).2
    rintro _ ⟨n, rfl⟩
    exact (state_le_iff _ _).mp (hT (Set.mem_range_self n)) s

noncomputable instance cqStateOmegaCPO : OmegaCompletePartialOrder (CQState Var d) where
  ωSup := cqStateSup
  le_ωSup c n := (cqStateSup_isLUB c).1 (Set.mem_range_self n)
  ωSup_le c T h := (cqStateSup_isLUB c).2 (by rintro _ ⟨n, rfl⟩; exact h n)

instance cqStateOrderBot : OrderBot (CQState Var d) where
  bot := CQState.ofCore (GoogleQHL.zeroState Var d)
  bot_le S := by
    apply (state_le_iff _ _).mpr
    intro s
    rw [state_toCore_ofCore]
    exact (S.toCore.density s).positive.nonneg

theorem expect_state_omegaSup (c : Chain (CQState Var d)) (Q : CQAssertion Var d) :
    expect (ωSup c) Q = ⨆ n : Nat, expect (c n) Q := by
  simp only [expect_eq_core]
  change GoogleQHL.expectation (cqStateSup c).toCore Q.toCore = _
  rw [cqStateSup, state_toCore_ofCore]
  exact GoogleQHL.expectation_stateSup _ (stateChain_mono c) Q.toCore

theorem pairing_observable_omegaSup (c : Chain (Observable d)) (rho : GoogleQHL.Operator d)
    (hr : rho.PosSemidef) :
    GoogleQHL.pairing (Observable.toCore (ωSup c)).matrix rho =
      ⨆ n : Nat, GoogleQHL.pairing (Observable.toCore (c n)).matrix rho :=
  GoogleQHL.pairing_effectSup _ (observableChain_effect c) (observableChain_mono c) rho hr

end QuantumLeanLeap.GoogleQHL.PaperAPI
