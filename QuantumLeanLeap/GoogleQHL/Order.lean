import QuantumLeanLeap.GoogleQHL.Duality

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

def IsEffect (E : Operator d) : Prop := 0 ≤ E ∧ E ≤ 1
def IsAssertion (P : CQPredicate Var d) : Prop := ∀ s, IsEffect (P s)

theorem pull_mono (K : Operator d) {A B : Operator d} (h : A ≤ B) :
    Matrix.conjTranspose K * A * K ≤ Matrix.conjTranspose K * B * K := by
  rw [Matrix.le_iff] at h ⊢
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using h.conjTranspose_mul_mul_same K

theorem scalar_mono {a b : Complex} (h : a ≤ b) :
    Matrix.scalar (Fin d) a ≤ Matrix.scalar (Fin d) b := by
  rw [Matrix.le_iff]
  change (Matrix.diagonal (fun _ : Fin d => b) - Matrix.diagonal (fun _ => a)).PosSemidef
  rw [Matrix.diagonal_sub]
  exact Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr h)

theorem diagonal_mono {A B : Operator d} (h : A ≤ B) (i : Fin d) : A i i ≤ B i i := by
  have := (Matrix.le_iff.mp h).diag_nonneg (i := i)
  exact sub_nonneg.mp this

theorem reset_effect {E : Operator d} (h : IsEffect E) (i : Fin d) :
    IsEffect (Matrix.scalar (Fin d) (E i i)) := by
  constructor
  · have := scalar_mono (d := d) (diagonal_mono h.1 i)
    simpa using this
  · have := scalar_mono (d := d) (diagonal_mono h.2 i)
    simpa using this

theorem measurement_effect {n : Nat} (M : Measurement d n) (E : Fin n → Operator d)
    (h : ∀ o, IsEffect (E o)) :
    IsEffect (∑ o, Matrix.conjTranspose (M.kraus o) * E o * M.kraus o) := by
  constructor
  · exact Finset.sum_nonneg fun o _ => by
      simpa using pull_mono (M.kraus o) (h o).1
  · apply le_trans (Finset.sum_le_sum fun o _ => pull_mono (M.kraus o) (h o).2)
    simpa using M.complete

/-- All instructions, including nested loop approximants, preserve effects. -/
theorem wpApprox_effect [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (post : CQPredicate Var d) (hpost : IsAssertion post) :
    IsAssertion (wpApprox p fuel post) := by
  induction p generalizing fuel post with
  | skip => exact hpost
  | abort => intro s; exact ⟨le_rfl, Matrix.PosSemidef.one.nonneg⟩
  | assign v e => intro s; exact hpost _
  | qset i => intro s; exact reset_effect (hpost s) i
  | apply U =>
      intro s
      exact ⟨(Observable.pullback ⟨post s, (hpost s).1, (hpost s).2⟩ U).nonnegative,
        (Observable.pullback ⟨post s, (hpost s).1, (hpost s).2⟩ U).le_identity⟩
  | measure v n M => intro s; exact measurement_effect M _ (fun _ => hpost _)
  | seq a b iha ihb => exact iha fuel _ (ihb fuel post hpost)
  | qif g a b iha ihb => intro s; simp only [wpApprox]; split <;> [exact iha fuel post hpost s; exact ihb fuel post hpost s]
  | qwhile g body ihBody =>
      induction fuel with
      | zero => intro s; exact ⟨le_rfl, Matrix.PosSemidef.one.nonneg⟩
      | succ k ih =>
          intro s
          rw [wpApprox_while_succ]
          dsimp only
          split <;> [exact ihBody k _ ih s; exact hpost s]

/-- Monotonicity is in the Löwner order, NOT pointwise order on entries. -/
theorem wpApprox_mono [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    {P Q : CQPredicate Var d} (h : ∀ s, P s ≤ Q s) :
    ∀ s, wpApprox p fuel P s ≤ wpApprox p fuel Q s := by
  induction p generalizing fuel P Q with
  | skip => exact h
  | abort => intro s; exact le_rfl
  | assign v e => intro s; exact h _
  | qset i => intro s; exact scalar_mono (diagonal_mono (h s) i)
  | apply U => intro s; exact pull_mono U.matrix (h s)
  | measure v n M => intro s; exact Finset.sum_le_sum fun o _ => pull_mono (M.kraus o) (h _)
  | seq a b iha ihb => exact iha fuel (ihb fuel h)
  | qif g a b iha ihb => intro s; simp only [wpApprox]; split <;> [exact iha fuel h s; exact ihb fuel h s]
  | qwhile g body ihBody =>
      induction fuel with
      | zero => intro s; exact le_rfl
      | succ k ih =>
          intro s
          simp only [wpApprox_while_succ]
          split <;> [exact ihBody k ih s; exact h s]

@[simp] theorem wpApprox_zero [DecidableEq Var] (p : QProg Var d) (k : Nat) :
    wpApprox p k 0 = 0 := by
  induction p generalizing k with
  | skip => rfl
  | abort => rfl
  | assign v e => rfl
  | qset i => ext s a b; simp [wpApprox]
  | apply U => ext s a b; simp [wpApprox]
  | measure v n M => ext s a b; simp [wpApprox]
  | seq a b iha ihb => simp only [wpApprox_seq, ihb, iha]
  | qif g a b iha ihb => funext s; simp [wpApprox, iha, ihb]
  | qwhile g body ihBody =>
      induction k with
      | zero => rfl
      | succ k ih => funext s; simp only [wpApprox_while_succ, ih, ihBody]; split <;> rfl

theorem wpApprox_nonnegative [DecidableEq Var] (p : QProg Var d) (k : Nat)
    (post : CQPredicate Var d) (hpost : ∀ s, 0 ≤ post s) :
    ∀ s, 0 ≤ wpApprox p k post s := by
  intro s
  simpa only [wpApprox_zero, Pi.zero_apply] using
    wpApprox_mono p k (P := (0 : CQPredicate Var d)) hpost s

/-- Bundled bounded WP with positivity and upper bound proved, not assumed. -/
def wpBounded [DecidableEq Var] (p : QProg Var d) (fuel : Nat)
    (post : CQAssertion Var d) : CQAssertion Var d := fun s =>
  ⟨wpApprox p fuel post.toPredicate s,
    (wpApprox_effect p fuel _ (fun t => ⟨(post t).nonnegative, (post t).le_identity⟩) s).1,
    (wpApprox_effect p fuel _ (fun t => ⟨(post t).nonnegative, (post t).le_identity⟩) s).2⟩

end QuantumLeanLeap.GoogleQHL
