import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Skeletal
import Ript.Univalent.Soundness

/-!
# Truncated completion of the internal process-interface groupoid

This file makes the first Stage-12 completion step precise.  It supplies two
related constructions without claiming a full Rezk completion.

* `ObjectCompletion` is the choice-free quotient of interface codes by mere
  internal identity.  Internal equivalence and internal identity become
  exactly equality after propositional truncation.  Sum and tensor descend to
  the quotient and satisfy their structural laws as Lean equalities.
* `SkeletalCompletion` is Mathlib's categorical skeleton of the interpreted
  interface groupoid.  It retains every automorphism and is categorically
  equivalent to the original groupoid, while isomorphic objects are equal.
  Its construction of morphisms uses chosen representatives and is therefore
  intentionally noncomputable.

The quotient has a genuine universal property: functions out of it are
equivalent to functions on codes that respect internal identity.  Internal
predicates likewise correspond exactly to predicates on the quotient.
Functor categories out of the skeletal completion are equivalent to functor
categories out of the original groupoid.

These are the 0- and 1-truncated shadows required before a higher-dimensional
Rezk or presheaf completion.  They do not identify the type of all
isomorphisms with Lean equality, do not remove nontrivial automorphisms, and do
not introduce an external univalence principle.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory

universe u w v

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)
variable {A B C D : Code Atom}

/-- Codes are related when their internal identity type is merely inhabited.
This is the propositional truncation of the interpreted groupoid relation. -/
def objectIdentitySetoid : Setoid (Code Atom) where
  r A B := Nonempty (M.Identity A B)
  iseqv := {
    refl := fun A => ⟨Identity.refl M A⟩
    symm := fun h => h.map (Identity.symm M)
    trans := fun h₁ h₂ => Nonempty.map2 (Identity.trans M) h₁ h₂ }

/-- The choice-free 0-truncated completion of interface codes by internal
identity.  Its raw quotient representation remains separate from the
noncomputable categorical skeleton below. -/
abbrev ObjectCompletion : Type u :=
  Quotient M.objectIdentitySetoid

namespace ObjectCompletion

/-- Send an interface code to its class in the 0-truncated completion. -/
def ofCode (A : Code Atom) : M.ObjectCompletion :=
  Quotient.mk M.objectIdentitySetoid A

/-- Equality of completed codes is exactly mere internal identity. -/
theorem ofCode_eq_iff_identity (A B : Code Atom) :
    ofCode M A = ofCode M B ↔ Nonempty (M.Identity A B) :=
  Quotient.eq

/-- By internal univalence, equality of completed codes is also exactly mere
internal structural equivalence. -/
theorem ofCode_eq_iff_equiv (A B : Code Atom) :
    ofCode M A = ofCode M B ↔ Nonempty (M.InternalEquiv A B) := by
  rw [ofCode_eq_iff_identity]
  exact ⟨fun h => h.map (internalUnivalence M A B),
    fun h => h.map (internalUnivalence M A B).symm⟩

/-- Every internal identity induces equality in the completed object type. -/
theorem ofCode_eq_of_identity (path : M.Identity A B) :
    ofCode M A = ofCode M B :=
  (ofCode_eq_iff_identity M A B).2 ⟨path⟩

/-- Every internal structural equivalence induces equality in the completed
object type. -/
theorem ofCode_eq_of_equiv (equiv : M.InternalEquiv A B) :
    ofCode M A = ofCode M B :=
  (ofCode_eq_iff_equiv M A B).2 ⟨equiv⟩

/-- The completed empty interface. -/
def empty : M.ObjectCompletion :=
  ofCode M .empty

/-- The completed tensor-unit interface. -/
def unit : M.ObjectCompletion :=
  ofCode M .unit

/-- Disjoint sum descends through internal identity. -/
def sum : M.ObjectCompletion → M.ObjectCompletion → M.ObjectCompletion :=
  Quotient.map₂ Code.sum (by
    intro A B hAB C D hCD
    exact Nonempty.map2 (Identity.sumCongr M) hAB hCD)

/-- Parallel tensor descends through internal identity. -/
def tensor : M.ObjectCompletion → M.ObjectCompletion → M.ObjectCompletion :=
  Quotient.map₂ Code.tensor (by
    intro A B hAB C D hCD
    exact Nonempty.map2 (Identity.tensorCongr M) hAB hCD)

@[simp]
theorem sum_ofCode (A B : Code Atom) :
    sum M (ofCode M A) (ofCode M B) = ofCode M (.sum A B) :=
  rfl

@[simp]
theorem tensor_ofCode (A B : Code Atom) :
    tensor M (ofCode M A) (ofCode M B) = ofCode M (.tensor A B) :=
  rfl

/-- Sum symmetry becomes literal equality after object completion. -/
theorem sum_comm (X Y : M.ObjectCompletion) :
    sum M X Y = sum M Y X := by
  induction X using Quotient.inductionOn with
  | _ A =>
      induction Y using Quotient.inductionOn with
      | _ B =>
          exact ofCode_eq_of_equiv M
            (InternalEquiv.mk M (.sumSwap A B))

/-- Sum associativity becomes literal equality after object completion. -/
theorem sum_assoc (X Y Z : M.ObjectCompletion) :
    sum M (sum M X Y) Z = sum M X (sum M Y Z) := by
  induction X using Quotient.inductionOn with
  | _ A =>
      induction Y using Quotient.inductionOn with
      | _ B =>
          induction Z using Quotient.inductionOn with
          | _ C =>
              exact ofCode_eq_of_equiv M
                (InternalEquiv.mk M (.sumAssoc A B C))

/-- The empty interface is a left unit for completed sums. -/
theorem empty_sum (X : M.ObjectCompletion) :
    sum M (empty M) X = X := by
  induction X using Quotient.inductionOn with
  | _ A =>
      exact ofCode_eq_of_equiv M
        (InternalEquiv.mk M (.sumUnitLeft A))

/-- The empty interface is a right unit for completed sums. -/
theorem sum_empty (X : M.ObjectCompletion) :
    sum M X (empty M) = X := by
  induction X using Quotient.inductionOn with
  | _ A =>
      exact ofCode_eq_of_equiv M
        (InternalEquiv.mk M (.sumUnitRight A))

/-- Tensor symmetry becomes literal equality after object completion. -/
theorem tensor_comm (X Y : M.ObjectCompletion) :
    tensor M X Y = tensor M Y X := by
  induction X using Quotient.inductionOn with
  | _ A =>
      induction Y using Quotient.inductionOn with
      | _ B =>
          exact ofCode_eq_of_equiv M
            (InternalEquiv.mk M (.tensorSwap A B))

/-- Tensor associativity becomes literal equality after object completion. -/
theorem tensor_assoc (X Y Z : M.ObjectCompletion) :
    tensor M (tensor M X Y) Z = tensor M X (tensor M Y Z) := by
  induction X using Quotient.inductionOn with
  | _ A =>
      induction Y using Quotient.inductionOn with
      | _ B =>
          induction Z using Quotient.inductionOn with
          | _ C =>
              exact ofCode_eq_of_equiv M
                (InternalEquiv.mk M (.tensorAssoc A B C))

/-- The completed tensor unit is a left unit. -/
theorem unit_tensor (X : M.ObjectCompletion) :
    tensor M (unit M) X = X := by
  induction X using Quotient.inductionOn with
  | _ A =>
      exact ofCode_eq_of_equiv M
        (InternalEquiv.mk M (.tensorUnitLeft A))

/-- The completed tensor unit is a right unit. -/
theorem tensor_unit (X : M.ObjectCompletion) :
    tensor M X (unit M) = X := by
  induction X using Quotient.inductionOn with
  | _ A =>
      exact ofCode_eq_of_equiv M
        (InternalEquiv.mk M (.tensorUnitRight A))

end ObjectCompletion

/-- A value on interface codes together with proof that internal identity
cannot change the value.  These are exactly maps out of `ObjectCompletion`. -/
@[ext]
structure InvariantMap (β : Type w) where
  /-- The value assigned to every raw interface code. -/
  toFun : Code Atom → β
  /-- Internal identity preserves the assigned value. -/
  respects : ∀ {A B : Code Atom}, M.Identity A B → toFun A = toFun B

namespace InvariantMap

/-- Descend an identity-invariant map through the completed object quotient. -/
def descend {β : Type w} (f : M.InvariantMap β) : M.ObjectCompletion → β :=
  Quotient.lift f.toFun (by
    intro A B h
    exact h.elim f.respects)

@[simp]
theorem descend_ofCode {β : Type w} (f : M.InvariantMap β) (A : Code Atom) :
    descend (M := M) f (ObjectCompletion.ofCode M A) = f.toFun A :=
  rfl

end InvariantMap

/-- Pull a map on completed objects back to an identity-invariant map on raw
codes. -/
def invariantMapOfCompletion {β : Type w} (f : M.ObjectCompletion → β) :
    M.InvariantMap β where
  toFun A := f (ObjectCompletion.ofCode M A)
  respects path := congrArg f
    ((ObjectCompletion.ofCode_eq_iff_identity M _ _).2 ⟨path⟩)

/-- Universal property of the 0-truncated object completion: maps out of the
quotient are exactly maps on codes that respect internal identity. -/
def objectCompletionUniversal (β : Type w) :
    (M.ObjectCompletion → β) ≃ M.InvariantMap β where
  toFun := invariantMapOfCompletion M
  invFun := InvariantMap.descend (M := M)
  left_inv f := by
    funext X
    induction X using Quotient.inductionOn
    rfl
  right_inv f := by
    ext A
    rfl

namespace InternalPredicate

/-- Descend a well-formed internal predicate to the completed object type. -/
def descend (predicate : M.InternalPredicate) : M.ObjectCompletion → Prop :=
  Quotient.lift predicate.holds (by
    intro A B h
    apply propext
    exact h.elim (identity_indistinguishable M predicate))

@[simp]
theorem descend_ofCode (predicate : M.InternalPredicate) (A : Code Atom) :
    descend M predicate (ObjectCompletion.ofCode M A) = predicate.holds A :=
  rfl

/-- Every predicate on completed objects pulls back to an internal predicate
whose equivalence invariance is automatic. -/
def ofCompletion (predicate : M.ObjectCompletion → Prop) : M.InternalPredicate where
  holds A := predicate (ObjectCompletion.ofCode M A)
  respects equiv := by
    rw [(ObjectCompletion.ofCode_eq_iff_equiv M _ _).2 ⟨equiv⟩]

@[ext]
theorem ext {first second : M.InternalPredicate}
    (h : first.holds = second.holds) : first = second := by
  cases first
  cases second
  cases h
  rfl

end InternalPredicate

/-- Internal predicates are exactly predicates on the 0-truncated object
completion. -/
def internalPredicateCompletionEquiv :
    (M.ObjectCompletion → Prop) ≃ M.InternalPredicate where
  toFun := InternalPredicate.ofCompletion M
  invFun := InternalPredicate.descend M
  left_inv predicate := by
    funext X
    induction X using Quotient.inductionOn
    rfl
  right_inv predicate := by
    ext A
    rfl

/-- Mathlib's skeletal categorical completion of the interpreted internal
groupoid.  Unlike `ObjectCompletion`, it retains all automorphisms. -/
abbrev SkeletalCompletion : Type u :=
  CategoryTheory.Skeleton M.Object

/-- The skeleton of the interpreted interface groupoid is itself a groupoid. -/
noncomputable instance skeletalCompletionGroupoid : Groupoid M.SkeletalCompletion :=
  Groupoid.ofFullyFaithfulToGroupoid (CategoryTheory.fromSkeleton M.Object)
    (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful _)

/-- The noncomputable functor sending interpreted interface objects to their
chosen skeletal presentation. -/
noncomputable def toSkeletalCompletion : M.Object ⥤ M.SkeletalCompletion :=
  CategoryTheory.toSkeletonFunctor M.Object

/-- The fully faithful functor from the skeletal completion back to the
interpreted interface groupoid. -/
noncomputable def fromSkeletalCompletion : M.SkeletalCompletion ⥤ M.Object :=
  CategoryTheory.fromSkeleton M.Object

/-- The skeletal completion is categorically equivalent to the original
interpreted interface groupoid. -/
noncomputable def skeletalCompletionEquivalence : M.SkeletalCompletion ≌ M.Object :=
  CategoryTheory.skeletonEquivalence M.Object

/-- Isomorphic objects of the skeletal completion are equal. -/
theorem skeletalCompletion_skeletal : CategoryTheory.Skeletal M.SkeletalCompletion :=
  CategoryTheory.skeleton_skeletal M.Object

/-- Two raw interface codes have the same skeletal object exactly when their
internal identity type is merely inhabited. -/
theorem skeletalCode_eq_iff_identity (A B : Code Atom) :
    CategoryTheory.toSkeleton (C := M.Object) (⟨A⟩ : M.Object) =
      CategoryTheory.toSkeleton (C := M.Object) (⟨B⟩ : M.Object) ↔
        Nonempty (M.Identity A B) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.hom⟩
  · rintro ⟨path⟩
    exact ⟨asIso path⟩

/-- Internal univalence gives the equivalent characterization using mere
internal structural equivalence. -/
theorem skeletalCode_eq_iff_equiv (A B : Code Atom) :
    CategoryTheory.toSkeleton (C := M.Object) (⟨A⟩ : M.Object) =
      CategoryTheory.toSkeleton (C := M.Object) (⟨B⟩ : M.Object) ↔
        Nonempty (M.InternalEquiv A B) := by
  rw [skeletalCode_eq_iff_identity]
  exact ⟨fun h => h.map (internalUnivalence M A B),
    fun h => h.map (internalUnivalence M A B).symm⟩

/-- The choice-free completed object quotient maps canonically to the object
type of the skeletal categorical completion. -/
def objectCompletionToSkeletal : M.ObjectCompletion → M.SkeletalCompletion :=
  Quotient.lift
    (fun A => CategoryTheory.toSkeleton (C := M.Object) (⟨A⟩ : M.Object)) (by
      intro A B h
      exact h.elim fun path =>
        CategoryTheory.congr_toSkeleton_of_iso (asIso path))

@[simp]
theorem objectCompletionToSkeletal_ofCode (A : Code Atom) :
    objectCompletionToSkeletal M (ObjectCompletion.ofCode M A) =
      CategoryTheory.toSkeleton (C := M.Object) (⟨A⟩ : M.Object) :=
  rfl

/-- The canonical map from object completion to skeletal objects is injective. -/
theorem objectCompletionToSkeletal_injective :
    Function.Injective (objectCompletionToSkeletal M) := by
  intro X Y h
  induction X using Quotient.inductionOn with
  | _ A =>
      induction Y using Quotient.inductionOn with
      | _ B =>
          apply Quotient.sound
          exact (skeletalCode_eq_iff_identity M A B).1 h

/-- Every skeletal object comes from a completed raw interface code.  The proof
uses Mathlib's chosen representative of a skeleton object. -/
theorem objectCompletionToSkeletal_surjective :
    Function.Surjective (objectCompletionToSkeletal M) := by
  intro X
  refine ⟨ObjectCompletion.ofCode M
    ((CategoryTheory.fromSkeleton M.Object).obj X).code, ?_⟩
  exact CategoryTheory.toSkeleton_fromSkeleton_obj X

/-- The choice-free object completion and the objects of the categorical
skeleton have the same elements. -/
theorem objectCompletionToSkeletal_bijective :
    Function.Bijective (objectCompletionToSkeletal M) :=
  ⟨objectCompletionToSkeletal_injective M,
    objectCompletionToSkeletal_surjective M⟩

/-- Every morphism in the skeletal completion has equal endpoints.  Nontrivial
automorphisms may still remain at each endpoint. -/
theorem skeletalCompletion_totallyDisconnected :
    Groupoid.IsTotallyDisconnected M.SkeletalCompletion := by
  intro X Y f
  exact skeletalCompletion_skeletal M ⟨asIso f⟩

/-- Categorical universal property of the skeletal completion: restriction
along its equivalence with the original groupoid is an equivalence of functor
categories for every target category. -/
noncomputable def skeletalCompletionUniversal
    (E : Type v) [Category.{w} E] :
    (M.SkeletalCompletion ⥤ E) ≌ (M.Object ⥤ E) :=
  (skeletalCompletionEquivalence M).congrLeft

end UniverseModel

end Ript.Univalent
