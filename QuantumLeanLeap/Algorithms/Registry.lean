import Mathlib.Data.List.Nodup

/-!
# Machine-checked algorithm registry

"Complete" is made precise relative to the declared core scope below.  Every
core family occurs exactly once in `verifiedCatalog`; algorithms outside this
scope must be added explicitly rather than being silently counted as covered.
-/

namespace QuantumLeanLeap.Algorithms

/-- The first stable public scope of the algorithm library. -/
inductive CoreFamily where
  | bernsteinVazirani
  | deutschJozsa
  | simon
  | groverSearch
  | quantumPhaseEstimation
  | amplitudeEstimation
  | teleportation
  | superdenseCoding
  | orderFinding
  | integerFactoring
  | finiteCyclicDLP
  | ellipticCurveDLP
deriving DecidableEq, Repr

inductive Category where
  | oracle
  | estimation
  | communication
  | numberTheory
deriving DecidableEq, Repr

/-- Properties supplied by a canonical `Algorithm.Solves` endpoint. -/
structure VerificationProfile where
  correctness : Bool
  successProbability : Bool
  borrowedRestoration : Bool
  eventBound : Bool
  spaceBound : Bool
  depthBound : Bool
deriving DecidableEq, Repr

def VerificationProfile.complete : VerificationProfile where
  correctness := true
  successProbability := true
  borrowedRestoration := true
  eventBound := true
  spaceBound := true
  depthBound := true

structure Entry where
  family : CoreFamily
  name : String
  category : Category
  sourceModule : String
  profile : VerificationProfile
deriving DecidableEq, Repr

/-- Canonical algorithms that already expose a complete verified endpoint. -/
def verifiedCatalog : List Entry :=
  [ ⟨.bernsteinVazirani, "Bernstein–Vazirani", .oracle,
      "QuantumAlg.Algorithms.BernsteinVazirani", .complete⟩
  , ⟨.deutschJozsa, "Deutsch–Jozsa", .oracle,
      "QuantumAlg.Algorithms.DeutschJozsa", .complete⟩
  , ⟨.simon, "Simon", .oracle,
      "QuantumAlg.Algorithms.Simon", .complete⟩
  , ⟨.groverSearch, "Grover search", .oracle,
      "QuantumAlg.Algorithms.Grover", .complete⟩
  , ⟨.quantumPhaseEstimation, "Quantum phase estimation", .estimation,
      "QuantumAlg.Algorithms.QPE", .complete⟩
  , ⟨.amplitudeEstimation, "Amplitude estimation", .estimation,
      "QuantumAlg.Algorithms.AmplitudeEstimation", .complete⟩
  , ⟨.teleportation, "Quantum teleportation", .communication,
      "QuantumAlg.Algorithms.Teleportation", .complete⟩
  , ⟨.superdenseCoding, "Superdense coding", .communication,
      "QuantumAlg.Algorithms.SuperdenseCoding", .complete⟩
  , ⟨.orderFinding, "Order finding", .numberTheory,
      "QuantumAlg.Algorithms.OrderFinding", .complete⟩
  , ⟨.integerFactoring, "Integer factoring", .numberTheory,
      "QuantumAlg.Algorithms.Factoring", .complete⟩
  , ⟨.finiteCyclicDLP, "Finite cyclic discrete logarithm", .numberTheory,
      "QuantumAlg.Algorithms.FiniteCyclicDLP", .complete⟩
  , ⟨.ellipticCurveDLP, "Elliptic-curve discrete logarithm", .numberTheory,
      "QuantumAlg.Algorithms.EllipticCurve.DLP", .complete⟩ ]

def lookup (family : CoreFamily) : Option Entry :=
  verifiedCatalog.find? fun entry => entry.family = family

@[simp] theorem verifiedCatalog_length : verifiedCatalog.length = 12 := rfl

/-- Every family in the declared core scope is present. -/
theorem verifiedCatalog_covers_core (family : CoreFamily) :
    family ∈ verifiedCatalog.map Entry.family := by
  cases family <;> simp [verifiedCatalog]

/-- No family is counted twice. -/
theorem verifiedCatalog_families_nodup :
    (verifiedCatalog.map Entry.family).Nodup := by
  decide

/-- Public names are unique as well as family identifiers. -/
theorem verifiedCatalog_names_nodup :
    (verifiedCatalog.map Entry.name).Nodup := by
  decide

/-- Every admitted registry row carries the full endpoint profile. -/
theorem verifiedCatalog_profiles_complete (entry : Entry)
    (present : entry ∈ verifiedCatalog) :
    entry.profile = VerificationProfile.complete := by
  simp only [verifiedCatalog, List.mem_cons, List.not_mem_nil, or_false]
    at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Registry lookup succeeds for every family in the declared core scope. -/
theorem lookup_isSome (family : CoreFamily) : (lookup family).isSome := by
  cases family <;> decide

/-- Successful lookup returns the requested family and a complete profile. -/
theorem lookup_spec (family : CoreFamily) :
    ∃ entry, lookup family = some entry ∧ entry.family = family ∧
      entry.profile = VerificationProfile.complete := by
  cases family <;> decide

end QuantumLeanLeap.Algorithms
