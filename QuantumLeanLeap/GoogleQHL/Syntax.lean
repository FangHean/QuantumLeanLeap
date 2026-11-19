import QuantumLeanLeap.GoogleQHL.Basic

/-!
# Classical--quantum program syntax

The constructors follow the public grammar in the paper. Guards are represented
by Boolean-valued store functions; this packages decidability directly.
-/

namespace QuantumLeanLeap.GoogleQHL

variable {Var : Type} {d : Nat}

/-- A shallowly embedded classical--quantum while language. -/
inductive QProg (Var : Type) (d : Nat) where
  | skip
  | abort
  | assign (target : Var) (expression : Store Var → Int)
  | qset (zeroIndex : Fin d)
  | apply (unitary : Unitary d)
  | measure (target : Var) (outcomes : Nat) (measurement : Measurement d outcomes)
  | seq (first second : QProg Var d)
  | qif (guard : Store Var → Bool) (thenBranch elseBranch : QProg Var d)
  | qwhile (guard : Store Var → Bool) (body : QProg Var d)

namespace QProg

/-- Sequential-composition notation without claiming a parser extension. -/
def andThen (first second : QProg Var d) : QProg Var d := .seq first second

end QProg
end QuantumLeanLeap.GoogleQHL
