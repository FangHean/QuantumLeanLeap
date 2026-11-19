import QuantumLeanLeap.GoogleQHL.Basic
import QuantumLeanLeap.GoogleQHL.Syntax
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Small matrix vocabulary for the 36 translated problem specifications.
No algorithm-library types or implementations are imported. Checked program
operations use the existing QHL `Unitary`; unproved matrix identities remain
benchmark obligations, never axioms of the library. -/
namespace QuantumLeanLeap.GoogleQHL.Bench36
noncomputable section
abbrev Mat (ι : Type*) := Matrix ι ι ℂ
abbrev Vec (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι

def applyVec {ι : Type*} [Fintype ι] (A : Mat ι) (v : Vec ι) : Vec ι :=
  WithLp.toLp 2 (A.mulVec v.ofLp)

def ket {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : Vec ι :=
  WithLp.toLp 2 (fun j => if j = i then 1 else 0)

def prodEquiv {m n : ℕ} : Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n)) :=
  finProdFinEquiv.trans (finCongr (pow_add (2 : ℕ) m n).symm)

def tensorOp {m n : ℕ} (A : Operator (2 ^ m)) (B : Operator (2 ^ n)) :
    Operator (2 ^ (m + n)) :=
  fun i j => A (prodEquiv.symm i).1 (prodEquiv.symm j).1 *
    B (prodEquiv.symm i).2 (prodEquiv.symm j).2

def tensorVec {m n : ℕ} (u : Vec (Fin (2 ^ m))) (v : Vec (Fin (2 ^ n))) :
    Vec (Fin (2 ^ (m + n))) :=
  WithLp.toLp 2 (fun i => u (prodEquiv.symm i).1 * v (prodEquiv.symm i).2)

def controlled {n : ℕ} (U : Operator (2 ^ n)) : Operator (2 ^ (1 + n)) :=
  fun i j =>
    let a := prodEquiv.symm i; let b := prodEquiv.symm j
    if a.1 = b.1 then
      if a.1 = 0 then (if a.2 = b.2 then 1 else 0) else U a.2 b.2
    else 0

def H : Operator 2 := (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]
def Z : Operator 2 := !![1, 0; 0, -1]
def X : Operator 2 := !![0, 1; 1, 0]
def YOp : Operator 2 := !![0, -Complex.I; Complex.I, 0]
def CNOT : Operator (2 ^ (1 + 1)) := controlled X

def rotY (θ : ℝ) : Operator 2 :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
     (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]
def ket0 : Vec (Fin 2) := ket 0
def ket1 : Vec (Fin 2) := ket 1

def permMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (p : Equiv.Perm ι) : Mat ι :=
  fun i j => if i = p j then 1 else 0

def projectedBlock (a n : ℕ) (U : Operator (2 ^ (a + n))) : Operator (2 ^ n) :=
  fun i j => U (prodEquiv ((0 : Fin (2 ^ a)), i)) (prodEquiv ((0 : Fin (2 ^ a)), j))

def blockEncodingErrorSq (a n : ℕ) (alpha : ℝ) (U : Unitary (2 ^ (a + n)))
    (A : Operator (2 ^ n)) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j - (alpha : ℂ) * projectedBlock a n U.matrix i j)

structure BlockEncoding (alpha : ℝ) (a n : ℕ) (epsilon : ℝ)
    (U : Unitary (2 ^ (a + n))) (A : Operator (2 ^ n)) : Prop where
  alpha_pos : 0 < alpha
  epsilon_nonneg : 0 ≤ epsilon
  block_error : blockEncodingErrorSq a n alpha U A ≤ epsilon ^ 2

/-- A matrix certificate constructs an actual operation of this library's QHL. -/
def certifiedUnitary {d : ℕ} (A : Operator d) (h : A ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Unitary d where
  matrix := A
  left_inverse := Matrix.mem_unitaryGroup_iff'.mp h
  right_inverse := Matrix.mem_unitaryGroup_iff.mp h

def certifiedProgram {d : ℕ} (A : Operator d) (h : A ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    QProg Unit d := .apply (certifiedUnitary A h)

theorem certifiedUnitary_matrix {d : ℕ} (A : Operator d)
    (h : A ∈ Matrix.unitaryGroup (Fin d) ℂ) : (certifiedUnitary A h).matrix = A := rfl
end
end QuantumLeanLeap.GoogleQHL.Bench36
