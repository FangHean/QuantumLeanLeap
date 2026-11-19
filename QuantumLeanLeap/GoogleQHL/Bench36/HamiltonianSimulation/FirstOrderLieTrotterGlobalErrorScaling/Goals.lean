import QuantumLeanLeap.GoogleQHL.Bench36.HamiltonianSimulation.FirstOrderLieTrotterGlobalErrorScaling.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.FirstOrderLieTrotterGlobalErrorScaling
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators
variable {d : ℕ}

def obligation_0 (A B : Operator d)
    (opnorm : Operator d → ℝ)
    (expm : Operator d → Operator d)
    (ν c C t ε : ℝ)
    (m : ℕ)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_opnorm_nonneg : ∀ X, 0 ≤ opnorm X)
    (h_opnorm_subadd : ∀ X Y, opnorm (X + Y) ≤ opnorm X + opnorm Y)
    (h_opnorm_submul : ∀ X Y, opnorm (X * Y) ≤ opnorm X * opnorm Y)
    (h_opnorm_scalar : ∀ (a : ℂ) (X : Operator d),
      opnorm (a • X) ≤ ‖a‖ * opnorm X)
    (h_expm_zero : expm 0 = 1)
    (h_expm_unitary : ∀ (X : Operator d) (τ : ℝ),
      IsSelfAdjoint X → expm ((-Complex.I * (τ : ℂ)) • X) ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h_expm_add : ∀ (X : Operator d) (τ₁ τ₂ : ℝ),
      expm ((-Complex.I * (τ₁ : ℂ)) • X) * expm ((-Complex.I * (τ₂ : ℂ)) • X) =
        expm ((-Complex.I * ((τ₁ + τ₂ : ℝ) : ℂ)) • X))
    (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B)
    (hν : ν = max (opnorm A) (opnorm B))
    (h_nu_pos : 0 < ν)
    (hc_pos : 0 < c)
    (hC_pos : 0 < C)
    (ht_pos : 0 < t)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1)

    (h_local :
      ∀ τ : ℝ,
        ν * |τ| ≤ c →
          opnorm
            (S1 expm A B τ - expm ((-Complex.I * (τ : ℂ)) • (A + B)) +
              ((τ ^ 2 : ℝ) / 2 : ℂ) • commutator A B) ≤
            C * ν ^ 3 * |τ| ^ 3)

    (h_telescoping :
      ∀ (r : ℕ) (U V : ℕ → Operator d),
        (∀ j ∈ Finset.Icc 1 r,
          U j ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
          V j ∈ Matrix.unitaryGroup (Fin d) ℂ) →
          opnorm
            (((List.range r).map (fun i => U (i + 1))).prod -
              ((List.range r).map (fun i => V (i + 1))).prod) ≤
          Finset.sum (Finset.Icc 1 r) (fun j => opnorm (U j - V j)))
    (h_m_pos : 0 < m)
    (h_step_small : ν * t / (m : ℝ) ≤ c) : Prop :=
  ∃ K : ℝ,
      0 ≤ K ∧
        opnorm (((List.range m).map (fun _ => S1 expm A B (t / (m : ℝ)))).prod -
          expm ((-Complex.I * (t : ℂ)) • (A + B))) ≤
        K * (ν ^ 2 * t ^ 2 / (m : ℝ)) ∧

        ∃ Kstep : ℝ,
          0 ≤ Kstep ∧
            ∀ m' : ℕ,
              Kstep * (ν ^ 2 * t ^ 2 / ε) ≤ (m' : ℝ) →
                opnorm (((List.range m').map
                  (fun _ => S1 expm A B (t / (m' : ℝ)))).prod -
                  expm ((-Complex.I * (t : ℂ)) • (A + B))) ≤ ε

end
end QuantumLeanLeap.GoogleQHL.Bench36.FirstOrderLieTrotterGlobalErrorScaling
