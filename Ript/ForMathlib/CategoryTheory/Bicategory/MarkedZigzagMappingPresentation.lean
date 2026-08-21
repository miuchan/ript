import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzag

/-!
# Local presentation universal property for marked-zigzag mapping categories

For a marked bicategory and a fixed source-object pair, the presented
marked-zigzag mapping category has words as objects and quotient raw 2-cells
as morphisms. This file proves its target-independent local presentation
universal property.

A `LocalInterpretation` assigns target objects to words and target morphisms
to raw cells, respecting every presentation relation, identity, and vertical
composition. It descends to a functor out of the quotient mapping category.
The descended map computes exactly on every raw generator, and the compatible
lift is unique by quotient induction.

This is a presentation-level universal property. It does not assert that the
resulting nerve is already a model-independent hammock localization or a
standard simplicial weak equivalence.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory.MarkedZigzag.Presented

open CategoryTheory
open CategoryTheory.Bicategory

universe u₁ v₁ w₁ u₂ v₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable (W : Bicategory.MorphismProperty B)
variable {D : Type u₂} [Category.{v₂} D]
variable (X Y : B)

/-- Target-independent interpretation data for one marked-zigzag local
presentation. It assigns target objects to words and target morphisms to raw
cells, respects every quotient relation, and preserves the raw categorical
identity and vertical-composition generators. -/
structure LocalInterpretation (D : Type u₂) [Category.{v₂} D] where
  /-- Target object assigned to each typed marked-zigzag word. -/
  obj : Word W X Y → D
  /-- Target morphism assigned to each raw 2-cell expression. -/
  map : ∀ {first second : Word W X Y},
    Cell W first second → (obj first ⟶ obj second)
  /-- Related raw cells receive the same target morphism. -/
  map_rel : ∀ {first second : Word W X Y}
    {alpha beta : Cell W first second},
    Rel W alpha beta → map alpha = map beta
  /-- Raw identity cells map to target identities. -/
  map_id : ∀ word, map (Cell.id word) = 𝟙 (obj word)
  /-- Raw vertical composites map to target composites. -/
  map_vcomp : ∀ {first middle last : Word W X Y}
    (alpha : Cell W first middle) (beta : Cell W middle last),
    map (Cell.vcomp alpha beta) = map alpha ≫ map beta

namespace LocalInterpretation

variable (I : LocalInterpretation W X Y D)

/-- Descend a relation-respecting raw-cell interpretation to one quotient
2-cell hom-set. -/
def descendMap {first second : Word W X Y} :
    Hom W first second → (I.obj first ⟶ I.obj second) :=
  Quot.lift (fun alpha => I.map alpha)
    (fun _ _ h => I.map_rel h)

/-- The descended hom-set map computes exactly on a represented raw cell. -/
@[simp]
theorem descendMap_mk {first second : Word W X Y}
    (alpha : Cell W first second) :
    descendMap W X Y I (Presented.mk W alpha) = I.map alpha :=
  rfl

/-- Every local interpretation descends to a functor from the quotient
marked-zigzag mapping category. -/
def descend : Word W X Y ⥤ D where
  obj := I.obj
  map := descendMap W X Y I
  map_id word := by
    change descendMap W X Y I (Presented.mk W (Cell.id word)) = _
    rw [descendMap_mk W X Y I, I.map_id]
  map_comp := by
    intro first middle last alpha beta
    refine Quot.inductionOn alpha ?_
    intro rawAlpha
    refine Quot.inductionOn beta ?_
    intro rawBeta
    change I.map (Cell.vcomp rawAlpha rawBeta) = _
    rw [I.map_vcomp, descendMap_mk W X Y I,
      descendMap_mk W X Y I]

/-- The descended functor retains the chosen word-object interpretation
definitionally. -/
@[simp]
theorem descend_obj (word : Word W X Y) :
    (descend W X Y I).obj word = I.obj word :=
  rfl

/-- The descended functor computes exactly on every represented raw cell. -/
@[simp]
theorem descend_map_mk {first second : Word W X Y}
    (alpha : Cell W first second) :
    (descend W X Y I).map (Presented.mk W alpha) = I.map alpha :=
  rfl

/-- A compatible lift of a local interpretation to quotient hom-sets. The
object action is fixed by the interpretation; the fields record functor laws
and exact agreement on every raw-cell representative. -/
@[ext]
structure LocalLift where
  /-- Map on each quotient 2-cell hom-set. -/
  mapHom : ∀ {first second : Word W X Y},
    Hom W first second → (I.obj first ⟶ I.obj second)
  /-- Quotient identity preservation. -/
  map_id : ∀ word, mapHom (𝟙 word) = 𝟙 (I.obj word)
  /-- Quotient vertical-composition preservation. -/
  map_comp : ∀ {first middle last : Word W X Y}
    (alpha : Hom W first middle) (beta : Hom W middle last),
    mapHom (@CategoryStruct.comp (Word W X Y)
      (wordCategory W X Y).toCategoryStruct
      first middle last alpha beta) = mapHom alpha ≫ mapHom beta
  /-- Exact agreement with the raw interpretation on every representative. -/
  map_mk : ∀ {first second : Word W X Y}
    (alpha : Cell W first second),
    mapHom (Presented.mk W alpha) = I.map alpha

namespace LocalLift

/-- A compatible quotient lift determines a functor with the interpretation's
fixed object action. -/
def toFunctor (L : LocalLift W X Y I) : Word W X Y ⥤ D where
  obj := I.obj
  map := L.mapHom
  map_id := L.map_id
  map_comp := L.map_comp

/-- Compatible lifts are unique: quotient induction reduces equality to exact
agreement on represented raw cells. -/
instance : Subsingleton (LocalLift W X Y I) where
  allEq first second := by
    apply LocalLift.ext
    funext source target cell
    refine Quot.inductionOn cell ?_
    intro raw
    exact (first.map_mk raw).trans (second.map_mk raw).symm

end LocalLift

/-- Canonical compatible lift supplied by quotient descent. -/
def descendLift : LocalLift W X Y I where
  mapHom := descendMap W X Y I
  map_id := (descend W X Y I).map_id
  map_comp := (descend W X Y I).map_comp
  map_mk := descendMap_mk W X Y I

/-- Every compatible lift is the canonical quotient descent. -/
theorem lift_unique (L : LocalLift W X Y I) :
    L = descendLift W X Y I :=
  Subsingleton.elim _ _

/-- The canonical compatible lift yields exactly the descended functor. -/
@[simp]
theorem descendLift_toFunctor :
    (descendLift W X Y I).toFunctor = descend W X Y I :=
  rfl

/-- Functor-level uniqueness of the quotient descent among compatible
lifts. -/
theorem toFunctor_unique (L : LocalLift W X Y I) :
    L.toFunctor = descend W X Y I := by
  rw [lift_unique W X Y I L]
  rfl

end LocalInterpretation

end CategoryTheory.Bicategory.MarkedZigzag.Presented
