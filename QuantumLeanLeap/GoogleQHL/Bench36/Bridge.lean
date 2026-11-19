import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
import QuantumLeanLeap.GoogleQHL.StatePrimitives

namespace QuantumLeanLeap.GoogleQHL.Bench36

/-- A certified matrix has the actual QHL weakest-precondition semantics. -/
theorem certifiedProgram_wp {d : ℕ} (A : Operator d)
    (h : A ∈ Matrix.unitaryGroup (Fin d) ℂ) (Q : CQAssertion Unit d) (s : Store Unit) :
    (wp (certifiedProgram A h) Q s).matrix = Matrix.conjTranspose A * (Q s).matrix * A :=
  wp_apply (certifiedUnitary A h) Q s

/-- Equality established by a matrix task preserves the QHL operation. -/
theorem certifiedProgram_eq {d : ℕ} {A B : Operator d}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) ℂ) (h : A = B) :
    certifiedProgram A hA = certifiedProgram B hB := by
  subst B
  rfl

end QuantumLeanLeap.GoogleQHL.Bench36
