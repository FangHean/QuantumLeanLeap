import QuantumLeanLeap.GoogleQHL.Compatibility.Continuity

/-! The paper-facing loop WP as Mathlib's Kleene chain supremum. -/
namespace QuantumLeanLeap.GoogleQHL.PaperAPI
open scoped ComplexOrder MatrixOrder
open OmegaCompletePartialOrder
variable {Var : Type} {d : Nat} [NeZero d] [DecidableEq Var]

noncomputable def loopFunctional (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q R : CQAssertion Var d) : CQAssertion Var d :=
  fun s => if g s then wp body R s else Q s

theorem loopFunctional_mono (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) : Monotone (loopFunctional g body Q) := by
  intro P R h s
  by_cases hg : g s
  · simpa only [loopFunctional, if_pos hg] using wp_mono body h s
  · simp only [loopFunctional, if_neg hg, le_refl]

noncomputable def loopOrderHom (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) : CQAssertion Var d →o CQAssertion Var d :=
  ⟨loopFunctional g body Q, loopFunctional_mono g body Q⟩

theorem loop_map_omegaSup (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) (c : Chain (CQAssertion Var d)) :
    loopFunctional g body Q (ωSup c) = ωSup (c.map (loopOrderHom g body Q)) := by
  funext s
  apply le_antisymm
  · by_cases hg : g s
    · simp only [loopFunctional, if_pos hg, wp_map_omegaSup]
      change ωSup ((c.map (wpOrderHom body)).map (Pi.evalOrderHom s)) ≤ _
      apply ωSup_le
      intro n
      have h := le_ωSup (c.map (loopOrderHom g body Q)) n s
      change (if g s then wp body (c n) s else Q s) ≤ _ at h
      change wp body (c n) s ≤ _
      simpa only [if_pos hg] using h
    · simp only [loopFunctional, if_neg hg]
      have h := le_ωSup (c.map (loopOrderHom g body Q)) 0 s
      change (if g s then wp body (c 0) s else Q s) ≤ _ at h
      simpa only [if_neg hg] using h
  · change ωSup ((c.map (loopOrderHom g body Q)).map (Pi.evalOrderHom s)) ≤ _
    apply ωSup_le
    intro n
    exact loopFunctional_mono g body Q (le_ωSup c n) s

noncomputable def loopContinuousHom (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) : CQAssertion Var d →𝒄 CQAssertion Var d where
  toOrderHom := loopOrderHom g body Q
  map_ωSup' := loop_map_omegaSup g body Q

theorem wp_qwhile_fixedPoint (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) :
    loopFunctional g body Q (wp (.qwhile g body) Q) = wp (.qwhile g body) Q := by
  funext s
  exact (wp_qwhile_unfold g body Q s).symm

theorem wp_qwhile_least (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q R : CQAssertion Var d)
    (h : loopFunctional g body Q R ≤ R) : wp (.qwhile g body) Q ≤ R := by
  have hc : ∀ s, (if decide (g s) then (GoogleQHL.wp body.toCore R.toCore s).matrix
      else (Q.toCore s).matrix) ≤ (R.toCore s).matrix := by
    intro s
    by_cases hg : g s
    · have hs : wp body R s ≤ R s := by simpa only [loopFunctional, if_pos hg] using h s
      have hm := (observable_le_iff _ _).mp hs
      change (GoogleQHL.wp body.toCore R.toCore s).matrix ≤ (R.toCore s).matrix at hm
      simpa only [decide_eq_true hg, if_true] using hm
    · have hs : Q s ≤ R s := by simpa only [loopFunctional, if_neg hg] using h s
      simpa only [decide_eq_false hg, Bool.false_eq_true, if_false, CQAssertion.toCore] using
        (observable_le_iff _ _).mp hs
  intro s
  exact (observable_le_iff _ _).mpr
    (GoogleQHL.wp_while_least (fun s => decide (g s)) body.toCore Q.toCore R.toCore hc s)

/-- The body has its full unbounded semantics at each iteration. -/
noncomputable def loopIterates (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) : Chain (CQAssertion Var d) :=
  fixedPoints.iterateChain (loopContinuousHom g body Q) ⊥ bot_le

theorem wp_qwhile_eq_omegaSup_iterates (g : Store Var → Prop) [DecidablePred g]
    (body : QProg Var d) (Q : CQAssertion Var d) :
    wp (.qwhile g body) Q = ωSup (loopIterates g body Q) := by
  apply le_antisymm
  · apply wp_qwhile_least
    exact (fixedPoints.ωSup_iterate_mem_fixedPoint (loopContinuousHom g body Q) ⊥ bot_le).le
  · exact fixedPoints.ωSup_iterate_le_prefixedPoint (loopContinuousHom g body Q) ⊥ bot_le
      (wp_qwhile_fixedPoint g body Q).le bot_le

end QuantumLeanLeap.GoogleQHL.PaperAPI
