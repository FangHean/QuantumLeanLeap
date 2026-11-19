import QuantumLeanLeap.GoogleQHL.Bench36.QSPParameterTrace.ParityMaximumFejerKernelQSPResponse.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ParityMaximumFejerKernelQSPResponse
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 (k : ℕ) (phi : Fin (k + 1) → ℝ) : Prop :=
  (∃ p : Polynomial ℂ,
      p.natDegree ≤ k ∧
      ∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
        p.eval (a : ℂ) = qspResponse k phi a) ∧

    (∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      qspResponse k phi (-a) = (-1 : ℂ) ^ k * qspResponse k phi a) ∧

    (∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      fejerP k a =
        ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 *
          Complex.normSq (fejerGeometricSum k (theta a)) : ℝ)) ∧

    (∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      0 ≤ fejerPReal k a ∧ fejerPReal k a ≤ 1) ∧

    fejerPReal k 1 = 1

end
end QuantumLeanLeap.GoogleQHL.Bench36.ParityMaximumFejerKernelQSPResponse
