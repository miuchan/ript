import Ript.Univalent.Model

/-!
# Soundness and internal univalence

This file proves the central Stage-11 result: in the interpreted deep
universe, the internal identity type between two codes is equivalent to the
type of internal structural equivalences between them.  Both sides are
semantic quotients of explicit syntax, so the theorem is proved without an
external univalence axiom.

The file also states the corresponding soundness/reflection theorem for the
quotient model, a generic indiscernibility theorem for invariant internal
predicates, and a concrete structure-identity result for deterministic process
spaces.
-/

set_option autoImplicit false

namespace Ript.Univalent

universe u w

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)
variable {A B C D : Code Atom}

/-- Map an internal identity to the structural equivalence it denotes. -/
def idToEquiv (path : M.Identity A B) : M.InternalEquiv A B :=
  Quotient.map PathExpr.toEquivExpr (by
    intro first second h
    exact h) path

/-- The internal univalence introduction rule on semantic quotients. -/
def equivToId (equiv : M.InternalEquiv A B) : M.Identity A B :=
  Quotient.map PathExpr.ua (by
    intro first second h
    exact h) equiv

@[simp]
theorem interpret_idToEquiv (path : M.Identity A B) :
    InternalEquiv.interpret M (idToEquiv M path) = Identity.interpret M path := by
  induction path using Quotient.inductionOn
  rfl

@[simp]
theorem interpret_equivToId (equiv : M.InternalEquiv A B) :
    Identity.interpret M (equivToId M equiv) = InternalEquiv.interpret M equiv := by
  induction equiv using Quotient.inductionOn
  rfl

/-- Converting an equivalence to identity and back is the identity operation. -/
@[simp]
theorem idToEquiv_equivToId (equiv : M.InternalEquiv A B) :
    idToEquiv M (equivToId M equiv) = equiv := by
  apply InternalEquiv.eq_of_interpret_eq M
  simp

/-- Converting an identity to equivalence and back is the identity operation. -/
@[simp]
theorem equivToId_idToEquiv (path : M.Identity A B) :
    equivToId M (idToEquiv M path) = path := by
  apply Identity.eq_of_interpret_eq M
  simp

/-- Internal univalence for the interpreted process-interface universe.

This equivalence lives entirely inside the deep embedding.  Its left-hand
side is `UniverseModel.Identity M A B`, not Lean equality `A = B`. -/
def internalUnivalence (A B : Code Atom) :
    M.Identity A B ≃ M.InternalEquiv A B where
  toFun := idToEquiv M
  invFun := equivToId M
  left_inv := equivToId_idToEquiv M
  right_inv := idToEquiv_equivToId M

@[simp]
theorem internalUnivalence_apply (path : M.Identity A B) :
    internalUnivalence M A B path = idToEquiv M path :=
  rfl

@[simp]
theorem internalUnivalence_symm_apply (equiv : M.InternalEquiv A B) :
    (internalUnivalence M A B).symm equiv = equivToId M equiv :=
  rfl

/-- Soundness and reflection of the internal identity quotient: two internal
paths are equal exactly when their interpreted type equivalences are equal. -/
theorem identity_eq_iff_interpret_eq (first second : M.Identity A B) :
    first = second ↔ Identity.interpret M first = Identity.interpret M second := by
  constructor
  · intro h
    exact congrArg (Identity.interpret M) h
  · exact Identity.eq_of_interpret_eq M

/-- Soundness and reflection of the internal equivalence quotient. -/
theorem internalEquiv_eq_iff_interpret_eq
    (first second : M.InternalEquiv A B) :
    first = second ↔
      InternalEquiv.interpret M first = InternalEquiv.interpret M second := by
  constructor
  · intro h
    exact congrArg (InternalEquiv.interpret M) h
  · exact InternalEquiv.eq_of_interpret_eq M

/-- Equality of raw paths in the quotient model implies equality of their
external interpretations. -/
theorem path_interpretation_sound {first second : PathExpr A B}
    (h : Identity.mk M first = Identity.mk M second) :
    first.denote M.atomSemantics = second.denote M.atomSemantics := by
  exact congrArg (Identity.interpret M) h

/-- An internal family is a structure whose fibers can be transported along
internal equivalences.  The operation is intentionally phrased over
`InternalEquiv`, not Lean code equality. -/
structure InternalFamily where
  /-- The type of structures over each interface code. -/
  fiber : Code Atom → Type w
  /-- Reindex structures along an internal equivalence. -/
  transport : ∀ {A B : Code Atom}, M.InternalEquiv A B → fiber A ≃ fiber B

namespace InternalFamily

/-- The structure-identity principle for an internal family: an internal
identity induces an equivalence between the corresponding structure fibers. -/
def transportAlongIdentity (family : M.InternalFamily)
    (path : M.Identity A B) : family.fiber A ≃ family.fiber B :=
  family.transport (idToEquiv M path)

end InternalFamily

/-- A proposition internal to the quotient universe must explicitly respect
internal equivalence.  This is the 1-truncated analogue of substitutivity. -/
structure InternalPredicate where
  /-- The proposition observed at each interface code. -/
  holds : Code Atom → Prop
  /-- Equivalent interfaces have logically equivalent observations. -/
  respects : ∀ {A B : Code Atom}, M.InternalEquiv A B → (holds A ↔ holds B)

namespace InternalPredicate

/-- Internally identical codes are indistinguishable by every well-formed
internal predicate. -/
theorem identity_indistinguishable (predicate : M.InternalPredicate)
    (path : M.Identity A B) : predicate.holds A ↔ predicate.holds B :=
  predicate.respects (idToEquiv M path)

/-- Internally equivalent codes are indistinguishable by every well-formed
internal predicate. -/
theorem equivalence_indistinguishable (predicate : M.InternalPredicate)
    (equiv : M.InternalEquiv A B) : predicate.holds A ↔ predicate.holds B :=
  predicate.respects equiv

end InternalPredicate

/-- Deterministic processes between interpreted interfaces. -/
abbrev FunctionProcess (A B : Code Atom) : Type :=
  Code.denote M.atomSemantics A → Code.denote M.atomSemantics B

/-- Reindex deterministic process spaces along identities of their source and
target interfaces.  This is a concrete structure-identity principle rather
than an assumed transport operation. -/
def functionProcessStructureIdentity
    (source : M.Identity A B) (target : M.Identity C D) :
    M.FunctionProcess A C ≃ M.FunctionProcess B D where
  toFun process input :=
    Identity.interpret M target
      (process ((Identity.interpret M source).symm input))
  invFun process input :=
    (Identity.interpret M target).symm
      (process (Identity.interpret M source input))
  left_inv process := by
    funext input
    simp
  right_inv process := by
    funext input
    simp

/-- Inhabitedness is an internal invariant: internally identical interfaces
are inhabited simultaneously. -/
theorem nonempty_iff_of_identity (path : M.Identity A B) :
    Nonempty (Code.denote M.atomSemantics A) ↔
      Nonempty (Code.denote M.atomSemantics B) := by
  constructor
  · rintro ⟨value⟩
    exact ⟨Identity.interpret M path value⟩
  · rintro ⟨value⟩
    exact ⟨(Identity.interpret M path).symm value⟩

end UniverseModel

end Ript.Univalent
