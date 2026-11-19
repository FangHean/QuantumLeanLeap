import QuantumLeanLeap.GoogleQHL.Bench36.Fourier.EigenvectorsModularMultiplicationShor.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.EigenvectorsModularMultiplicationShor
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

variable {N : ℕ} [NeZero N]

def obligation_0 (x : ℕ)
    (hx_pos : 0 < x) (hx_lt : x < N)
    (hcoprime : Nat.Coprime x N)
    (hunit : IsUnit (x : ZMod N))
    (r : ℕ) (hr : r = orderOf hunit.unit)
    (s : ℕ) (hs : s < r) : Prop :=
  applyVec (UxOp (N := N) x) (psiS (N := N) x r s) =
      Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) / (r : ℂ)) •
        psiS (N := N) x r s

end
end QuantumLeanLeap.GoogleQHL.Bench36.EigenvectorsModularMultiplicationShor
