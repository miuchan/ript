/-!
# Typed process signatures

A stage-1 signature supplies object symbols, typed process generators, and the
resource cost of each generator. Capability labels are deferred until their
first concrete consumer.
-/

set_option autoImplicit false

namespace Ript.Syntax

universe u w

/-- A typed collection of primitive processes carrying generator costs. -/
structure Signature (R : Type w) where
  /-- Symbols for the input and output types of processes. -/
  Obj : Type u
  /-- Primitive process symbols indexed by their source and target. -/
  Gen : Obj → Obj → Type u
  /-- The declared resource cost of a primitive process. -/
  cost : {X Y : Obj} → Gen X Y → R

end Ript.Syntax
