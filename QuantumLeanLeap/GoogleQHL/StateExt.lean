import QuantumLeanLeap.GoogleQHL.DensityOrder

namespace QuantumLeanLeap.GoogleQHL
open scoped ComplexOrder MatrixOrder
variable {Var : Type} {d : Nat}

@[ext] theorem PartialDensity.ext {A B : PartialDensity d} (h : A.matrix = B.matrix) : A = B := by
  cases A
  cases B
  cases h
  rfl

@[ext] theorem CQState.ext {S T : CQState Var d}
    (h : ∀ s, (S.density s).matrix = (T.density s).matrix) : S = T := by
  have hd : S.density = T.density := funext (fun s => PartialDensity.ext (h s))
  cases S with
  | mk ds ms hs bs =>
      cases T with
      | mk dt mt ht bt =>
          dsimp at hd
          cases hd
          have hm := hs.unique ht
          cases hm
          rfl

def zeroObservable : Observable d := ⟨0, le_rfl, Matrix.PosSemidef.one.nonneg⟩

noncomputable def localizedAssertion (s : Store Var) (E : Observable d) : CQAssertion Var d := by
  classical
  exact fun t => if t = s then E else zeroObservable

theorem expectation_localized (S : CQState Var d) (s : Store Var) (E : Observable d) :
    expectation S (localizedAssertion s E) = pairing E.matrix (S.density s).matrix := by
  classical
  simp [expectation, localizedAssertion, zeroObservable, pairing, ite_mul, apply_ite]

theorem PartialDensity.eq_of_effect_tests (A B : PartialDensity d)
    (h : ∀ E : Observable d, pairing E.matrix A.matrix = pairing E.matrix B.matrix) : A = B := by
  have ha := h ⟨A.matrix, A.isEffect.1, A.isEffect.2⟩
  have hb := h ⟨B.matrix, B.isEffect.1, B.isEffect.2⟩
  have hp := Matrix.posSemidef_conjTranspose_mul_self (A.matrix - B.matrix)
  have ht : (Matrix.conjTranspose (A.matrix - B.matrix) * (A.matrix - B.matrix)).trace = 0 := by
    apply Complex.ext
    · rw [(A.positive.isHermitian.sub B.positive.isHermitian).eq]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Complex.zero_re]
      change pairing A.matrix A.matrix - pairing B.matrix A.matrix -
        (pairing A.matrix B.matrix - pairing B.matrix B.matrix) = 0
      dsimp only at ha hb
      rw [ha, hb]
      ring
    · exact (RCLike.nonneg_iff.mp hp.trace_nonneg).2
  apply PartialDensity.ext
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)

theorem CQState.eq_of_expectations (S T : CQState Var d)
    (h : ∀ Q : CQAssertion Var d, expectation S Q = expectation T Q) : S = T := by
  apply CQState.ext
  intro s
  have hd := PartialDensity.eq_of_effect_tests (S.density s) (T.density s) (fun E => by
    simpa only [expectation_localized] using h (localizedAssertion s E))
  exact congrArg PartialDensity.matrix hd

end QuantumLeanLeap.GoogleQHL
