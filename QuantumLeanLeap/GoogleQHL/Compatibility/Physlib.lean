import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumLeanLeap.GoogleQHL.StateExt

/-! An actual Physlib type bridge, not a replacement definition of HermitianMat.
The density/effect subtypes follow the paper; their names here are local.
See docs/GoogleQHL-interface-alignment.md for the pinned version and scope. -/
namespace QuantumLeanLeap.GoogleQHL.PaperAPI
open scoped ComplexOrder MatrixOrder

abbrev Store := GoogleQHL.Store
abbrev Hermitian (d : Nat) := HermitianMat (Fin d) Complex
abbrev Density (d : Nat) := {rho : Hermitian d // 0 ≤ rho ∧ rho.trace ≤ (1 : Real)}
abbrev Observable (d : Nat) := {E : Hermitian d // 0 ≤ E ∧ E ≤ 1}
abbrev CQAssertion (Var : Type) (d : Nat) := Store Var → Observable d

def CQState (Var : Type) (d : Nat) :=
  {S : Store Var → Density d // ∃ c : Real, HasSum (fun s => (S s).val.trace) c ∧ c ≤ 1}

instance {Var : Type} {d : Nat} : PartialOrder (CQState Var d) :=
  inferInstanceAs (PartialOrder
    {S : Store Var → Density d // ∃ c : Real, HasSum (fun s => (S s).val.trace) c ∧ c ≤ 1})

variable {Var : Type} {d : Nat}

theorem hermitian_trace (A : Hermitian d) : (A.trace : Real) = A.mat.trace.re :=
  HermitianMat.trace_eq_re_trace (𝕜 := Complex) A

def Density.toCore (rho : Density d) : GoogleQHL.PartialDensity d where
  matrix := rho.val.mat
  positive := HermitianMat.zero_le_iff.mp rho.property.1
  trace_le_one := by simpa only [hermitian_trace] using rho.property.2

def Density.ofCore (rho : GoogleQHL.PartialDensity d) : Density d :=
  ⟨⟨rho.matrix, rho.positive.isHermitian⟩,
    HermitianMat.zero_le_iff.mpr rho.positive,
    by change rho.matrix.trace.re ≤ 1; exact rho.trace_le_one⟩

def densityEquiv : Density d ≃ GoogleQHL.PartialDensity d where
  toFun := Density.toCore
  invFun := Density.ofCore
  left_inv rho := by apply Subtype.ext; apply HermitianMat.ext; rfl
  right_inv rho := by apply GoogleQHL.PartialDensity.ext; rfl

def Observable.toCore (E : Observable d) : GoogleQHL.Observable d where
  matrix := E.val.mat
  nonnegative := (HermitianMat.zero_le_iff.mp E.property.1).nonneg
  le_identity := by
    have h := HermitianMat.le_iff.mp E.property.2
    apply sub_nonneg.mp
    exact h.nonneg

def Observable.ofCore (E : GoogleQHL.Observable d) : Observable d :=
  ⟨⟨E.matrix, (Matrix.nonneg_iff_posSemidef.mp E.nonnegative).isHermitian⟩,
    HermitianMat.zero_le_iff.mpr (Matrix.nonneg_iff_posSemidef.mp E.nonnegative), by
      apply HermitianMat.le_iff.mpr
      change (1 - E.matrix).PosSemidef
      exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr E.le_identity)⟩

def observableEquiv : Observable d ≃ GoogleQHL.Observable d where
  toFun := Observable.toCore
  invFun := Observable.ofCore
  left_inv E := by apply Subtype.ext; apply HermitianMat.ext; rfl
  right_inv E := by cases E; rfl

def CQAssertion.toCore (Q : CQAssertion Var d) : GoogleQHL.CQAssertion Var d :=
  fun s => Observable.toCore (Q s)

def CQAssertion.ofCore (Q : GoogleQHL.CQAssertion Var d) : CQAssertion Var d :=
  fun s => Observable.ofCore (Q s)

@[simp] theorem assertion_toCore_ofCore (Q : GoogleQHL.CQAssertion Var d) :
    (CQAssertion.ofCore Q).toCore = Q := by
  funext s
  exact observableEquiv.apply_symm_apply (Q s)

@[simp] theorem assertion_ofCore_toCore (Q : CQAssertion Var d) :
    CQAssertion.ofCore Q.toCore = Q := by
  funext s
  exact observableEquiv.symm_apply_apply (Q s)

noncomputable def CQState.toCore (S : CQState Var d) : GoogleQHL.CQState Var d where
  density s := Density.toCore (S.val s)
  mass := Classical.choose S.property
  trace_hasSum := by
    simpa only [Density.toCore, hermitian_trace] using
      (Classical.choose_spec S.property).1
  mass_le_one := (Classical.choose_spec S.property).2

def CQState.ofCore (S : GoogleQHL.CQState Var d) : CQState Var d :=
  ⟨fun s => Density.ofCore (S.density s), S.mass,
    by change HasSum (fun s => (S.density s).matrix.trace.re) S.mass; exact S.trace_hasSum,
    S.mass_le_one⟩

noncomputable def stateEquiv : CQState Var d ≃ GoogleQHL.CQState Var d where
  toFun := CQState.toCore
  invFun := CQState.ofCore
  left_inv S := by
    apply Subtype.ext
    funext s
    exact densityEquiv.symm_apply_apply (S.val s)
  right_inv S := by apply GoogleQHL.CQState.ext; intro s; rfl

@[simp] theorem state_toCore_ofCore (S : GoogleQHL.CQState Var d) :
    (CQState.ofCore S).toCore = S := stateEquiv.apply_symm_apply S

@[simp] theorem state_ofCore_toCore (S : CQState Var d) :
    CQState.ofCore S.toCore = S := stateEquiv.symm_apply_apply S

/-- Paper's real Hilbert-Schmidt inner product, using Physlib's actual instance. -/
noncomputable def expect (S : CQState Var d) (Q : CQAssertion Var d) : Real :=
  ∑' s, inner Real (Q s).val (S.val s).val

theorem expect_eq_core (S : CQState Var d) (Q : CQAssertion Var d) :
    expect S Q = GoogleQHL.expectation S.toCore Q.toCore := by
  apply tsum_congr
  intro s
  exact HermitianMat.inner_eq_re_trace (Q s).val (S.val s).val

theorem observable_le_iff (A B : Observable d) :
    A ≤ B ↔ (Observable.toCore A).matrix ≤ (Observable.toCore B).matrix := by
  change A.val ≤ B.val ↔ A.val.mat ≤ B.val.mat
  rw [HermitianMat.le_iff, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]
  rfl

theorem density_le_iff (A B : Density d) :
    A ≤ B ↔ (Density.toCore A).matrix ≤ (Density.toCore B).matrix := by
  change A.val ≤ B.val ↔ A.val.mat ≤ B.val.mat
  rw [HermitianMat.le_iff, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]
  rfl

theorem state_le_iff (S T : CQState Var d) :
    S ≤ T ↔ ∀ s, (S.toCore.density s).matrix ≤ (T.toCore.density s).matrix := by
  change (∀ s, S.val s ≤ T.val s) ↔ _
  exact forall_congr' (fun s => density_le_iff (S.val s) (T.val s))

end QuantumLeanLeap.GoogleQHL.PaperAPI
