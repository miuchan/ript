import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagMappingPresentation
import Ript.ForMathlib.AlgebraicTopology.NerveHomotopy

/-!
# Simplicial universal property of marked-zigzag mapping presentations

This file lifts the target-independent local presentation theorem for
marked-zigzag mapping categories to categorical nerves in a common universe.

Every local interpretation induces an all-dimensional simplicial map. The
map computes exactly on word vertices, raw-cell edges, and arbitrary
simplices. Every compatible quotient lift induces exactly the same nerve map.
Natural transformations between descended interpretations induce genuine
`SSet.Homotopy` values, and natural isomorphisms supply homotopies in both
directions.

These results prove simplicial functoriality, uniqueness, and homotopy
invariance of the algebraic presentation. They do not by themselves identify
the nerve with a standard hammock localization or provide a model-category
weak-equivalence theorem.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory.MarkedZigzag.Presented.LocalInterpretation

open CategoryTheory
open Opposite Simplicial

universe u₁ v₁ w₁ u₂ v₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable (W : Bicategory.MorphismProperty B)
variable {D : Type u₂} [Category.{v₂} D]
variable (X Y : B)
variable (I : LocalInterpretation W X Y D)

/-- Common-universe replacement of the presented word/quotient-2-cell
mapping category, balanced against an arbitrary target category `D`. -/
@[nolint unusedArguments]
abbrev CommonWordCategory
    (W : Bicategory.MorphismProperty B) (X Y : B)
    (_D : Type u₂) [Category.{v₂} _D] :=
  AsSmall.{max u₂ v₂} (Word W X Y)

/-- Common-universe replacement of an arbitrary interpretation target,
balanced against the marked-zigzag mapping category. -/
abbrev CommonTargetCategory
    (_W : Bicategory.MorphismProperty B) (_X _Y : B)
    (D : Type u₂) [Category.{v₂} D] :=
  AsSmall.{max (max u₁ v₁) w₁} D

/-- Common-universe form of the quotient-descended interpretation functor. -/
def commonDescendFunctor :
    CommonWordCategory W X Y D ⥤ CommonTargetCategory W X Y D :=
  AsSmall.down ⋙ descend W X Y I ⋙ AsSmall.up

/-- Common-universe nerve of the marked-zigzag local presentation. -/
abbrev CommonWordNerve
    (W : Bicategory.MorphismProperty B) (X Y : B)
    (D : Type u₂) [Category.{v₂} D] :=
  CategoryTheory.nerve (CommonWordCategory W X Y D)

/-- Common-universe nerve of an arbitrary interpretation target. -/
abbrev CommonTargetNerve
    (W : Bicategory.MorphismProperty B) (X Y : B)
    (D : Type u₂) [Category.{v₂} D] :=
  CategoryTheory.nerve (CommonTargetCategory W X Y D)

/-- All-dimensional simplicial map induced by quotient descent of one local
interpretation. -/
def nerveMap :
    CommonWordNerve W X Y D ⟶ CommonTargetNerve W X Y D :=
  CategoryTheory.nerveMap (commonDescendFunctor W X Y I)

/-- Common-universe functor induced by any compatible quotient lift. -/
def commonLiftFunctor (L : LocalLift W X Y I) :
    CommonWordCategory W X Y D ⥤ CommonTargetCategory W X Y D :=
  AsSmall.down ⋙ L.toFunctor ⋙ AsSmall.up

/-- Simplicial map induced by any compatible quotient lift. -/
def liftNerveMap (L : LocalLift W X Y I) :
    CommonWordNerve W X Y D ⟶ CommonTargetNerve W X Y D :=
  CategoryTheory.nerveMap (commonLiftFunctor W X Y I L)

/-- Every compatible lift induces exactly the canonical common-universe
descended functor. -/
theorem commonLiftFunctor_unique (L : LocalLift W X Y I) :
    commonLiftFunctor W X Y I L = commonDescendFunctor W X Y I := by
  unfold commonLiftFunctor commonDescendFunctor
  rw [toFunctor_unique W X Y I L]

/-- Every compatible lift induces exactly the canonical all-dimensional
nerve map. -/
theorem liftNerveMap_unique (L : LocalLift W X Y I) :
    liftNerveMap W X Y I L = nerveMap W X Y I := by
  unfold liftNerveMap nerveMap
  rw [commonLiftFunctor_unique W X Y I L]

/-- The descended nerve map applies the common-universe descended functor to
an arbitrary simplex literally. -/
theorem nerveMap_simplex {n : ℕ}
    (simplex : (CommonWordNerve W X Y D).obj (op ⦋n⦌)) :
    (nerveMap W X Y I).app (op ⦋n⦌) simplex =
      simplex ⋙ commonDescendFunctor W X Y I := by
  rfl

/-- One marked-zigzag word as a vertex of the common presentation nerve. -/
def commonWordVertex (D : Type u₂) [Category.{v₂} D]
    (word : Word W X Y) :
    (CommonWordNerve W X Y D).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ ((AsSmall.up :
    Word W X Y ⥤ CommonWordCategory W X Y D).obj word)

/-- The target vertex assigned to one word by a local interpretation. -/
def commonTargetVertex (I : LocalInterpretation W X Y D)
    (word : Word W X Y) :
    (CommonTargetNerve W X Y D).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ ((AsSmall.up :
    D ⥤ CommonTargetCategory W X Y D).obj (I.obj word))

/-- The descended nerve map sends every word vertex to its exact interpreted
target vertex. -/
theorem nerveMap_wordVertex (word : Word W X Y) :
    (nerveMap W X Y I).app (op ⦋0⦌)
      (commonWordVertex W X Y D word) =
        commonTargetVertex W X Y I word := by
  unfold nerveMap commonWordVertex commonTargetVertex commonDescendFunctor
  rw [CategoryTheory.nerveMap_app_mk₀]
  rfl

/-- One raw 2-cell representative as an edge of the common presentation
nerve. -/
def commonRawCellEdge (D : Type u₂) [Category.{v₂} D]
    {first second : Word W X Y} (alpha : Cell W first second) :
    (CommonWordNerve W X Y D).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ ((AsSmall.up :
    Word W X Y ⥤ CommonWordCategory W X Y D).map
      (Presented.mk W alpha))

/-- The target edge assigned to one raw 2-cell by a local interpretation. -/
def commonTargetCellEdge (I : LocalInterpretation W X Y D)
    {first second : Word W X Y} (alpha : Cell W first second) :
    (CommonTargetNerve W X Y D).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ ((AsSmall.up :
    D ⥤ CommonTargetCategory W X Y D).map (I.map alpha))

/-- The descended nerve map computes exactly on every raw 2-cell edge. -/
theorem nerveMap_rawCellEdge {first second : Word W X Y}
    (alpha : Cell W first second) :
    (nerveMap W X Y I).app (op ⦋1⦌)
      (commonRawCellEdge W X Y D alpha) =
        commonTargetCellEdge W X Y I alpha := by
  unfold nerveMap commonRawCellEdge commonTargetCellEdge commonDescendFunctor
  rw [CategoryTheory.nerveMap_app_mk₁]
  rfl

variable {I J : LocalInterpretation W X Y D}

/-- Common-universe natural transformation induced by a natural
transformation between two descended local interpretations. -/
def commonNatTrans
    (alpha : descend W X Y I ⟶ descend W X Y J) :
    commonDescendFunctor W X Y I ⟶ commonDescendFunctor W X Y J :=
  Functor.whiskerRight (Functor.whiskerLeft AsSmall.down alpha) AsSmall.up

/-- Every natural transformation between descended local interpretations
induces a genuine simplicial homotopy between their all-dimensional nerve
maps. -/
noncomputable def nerveHomotopy
    (alpha : descend W X Y I ⟶ descend W X Y J) :
    SSet.Homotopy (nerveMap W X Y I) (nerveMap W X Y J) :=
  CategoryTheory.NerveHomotopy.ofNatTrans
    (commonNatTrans W X Y alpha)

/-- A natural isomorphism between descended interpretations supplies genuine
simplicial homotopies in both directions. -/
noncomputable def nerveIsoHomotopies
    (e : descend W X Y I ≅ descend W X Y J) :
    SSet.Homotopy (nerveMap W X Y I) (nerveMap W X Y J) ×
      SSet.Homotopy (nerveMap W X Y J) (nerveMap W X Y I) :=
  ⟨nerveHomotopy W X Y e.hom, nerveHomotopy W X Y e.inv⟩

end CategoryTheory.Bicategory.MarkedZigzag.Presented.LocalInterpretation
