import QuantumLeanLeap.GoogleQHL.CostControl

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

/-- A state-independent expected-cost bound per unit of input mass. -/
def CostBound [DecidableEq Var] (w : CostModel d) (p : QProg Var d) (C : ENNReal) : Prop :=
  ∀ S : CQState Var d, expectedCost w p S ≤ C * ENNReal.ofReal S.mass

theorem costBound_seq [DecidableEq Var] (w : CostModel d) (a b : QProg Var d) (A B : ENNReal)
    (ha : CostBound w a A) (hb : CostBound w b B) : CostBound w (.seq a b) (A + B) := by
  intro S
  rw [expectedCost_seq, add_mul]
  exact add_le_add (ha S) ((hb (interp a S)).trans
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (interp_mass_le a S)) bot_le))

theorem restrictState_mass_partition (g : Store Var → Bool) (S : CQState Var d) :
    (restrictState g S).mass + (restrictState (fun s => !(g s)) S).mass = S.mass := by
  have h := (restrictState g S).trace_hasSum.add (restrictState (fun s => !(g s)) S).trace_hasSum
  have he : (fun s => ((restrictState g S).density s).matrix.trace.re +
      ((restrictState (fun t => !(g t)) S).density s).matrix.trace.re) =
      (fun s => (S.density s).matrix.trace.re) := by
    funext s
    cases hg : g s <;> simp [restrictState, zeroDensity, hg]
  rw [he] at h
  exact h.unique S.trace_hasSum

theorem costBound_if [DecidableEq Var] (w : CostModel d) (g : Store Var → Bool)
    (a b : QProg Var d) (A B : ENNReal) (ha : CostBound w a A) (hb : CostBound w b B) :
    CostBound w (.qif g a b) (max A B) := by
  intro S
  rw [expectedCost_if]
  calc
    _ ≤ max A B * ENNReal.ofReal (restrictState g S).mass +
        max A B * ENNReal.ofReal (restrictState (fun s => !(g s)) S).mass :=
      add_le_add ((ha _).trans (mul_le_mul_of_nonneg_right (le_max_left A B) bot_le))
        ((hb _).trans (mul_le_mul_of_nonneg_right (le_max_right A B) bot_le))
    _ = max A B * ENNReal.ofReal S.mass := by
      rw [← mul_add, ← ENNReal.ofReal_add (restrictState g S).mass_nonnegative
        (restrictState (fun s => !(g s)) S).mass_nonnegative, restrictState_mass_partition]

/-- An operator potential pays for each entering iteration and its remaining
work. This is a sufficient invariant, not an assumed termination fact. -/
def LoopCostPotential [DecidableEq Var] (w : CostModel d) (g : Store Var → Bool)
    (body : QProg Var d) (V : CQPredicate Var d) : Prop :=
  (∀ s, 0 ≤ V s) ∧ ∀ k s, g s = true →
    costPredicate w body k s + wpApprox body k V s ≤ V s

theorem loop_costPredicate_le [DecidableEq Var] (w : CostModel d) (g : Store Var → Bool)
    (body : QProg Var d) (V : CQPredicate Var d) (h : LoopCostPotential w g body V)
    (k : Nat) : ∀ s, costPredicate w (.qwhile g body) k s ≤ V s := by
  obtain ⟨h0, hstep⟩ := h
  induction k with
  | zero => exact h0
  | succ k ih =>
      intro s
      rw [costPredicate_while_succ]
      split
      next hg =>
        have hm : wpApprox body k (costPredicate w (.qwhile g body) k) s ≤ wpApprox body k V s :=
          wpApprox_mono body k ih s
        have hb : costPredicate w body k s + wpApprox body k V s ≤ V s := hstep k s hg
        apply le_trans (b := costPredicate w body k s + wpApprox body k V s) _ hb
        exact add_le_add le_rfl hm
      next _ => exact h0 s

theorem expectedCost_while_le_potential [DecidableEq Var] (w : CostModel d)
    (g : Store Var → Bool) (body : QProg Var d) (V : CQPredicate Var d)
    (h : LoopCostPotential w g body V) (S : CQState Var d) :
    expectedCost w (.qwhile g body) S ≤ ∑' s, ENNReal.ofReal (pairing (V s) (S.density s).matrix) := by
  apply ENNReal.tsum_le_tsum
  intro s
  apply iSup_le
  intro k
  apply ENNReal.ofReal_le_ofReal
  rw [expectedCostApprox_pairing]
  exact pairing_mono (loop_costPredicate_le w g body V h k s) (S.density s).positive

end QuantumLeanLeap.GoogleQHL
