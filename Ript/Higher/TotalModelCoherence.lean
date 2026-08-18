import Ript.Higher.TotalModelBicategory

/-!
# Explicit coherence for the total bicategory of resource models

This file exposes horizontal composition, interchange, and named coherence
laws for models whose resource algebras may differ.  The resource-map equality
carried by every two-cell is composed together with the underlying monoidal
natural transformations, so these operations live in the total bicategory
rather than in a single fixed-resource fibre.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory

universe u v w

variable {A B C D E : ResourceModel.{u, v, w}}

namespace ResourceModelTransformation

/-- Horizontal composition of total-model two-cells. -/
def horizontalComp {F G : A ⟶ B} {H I : B ⟶ C}
    (eta : F ⟶ G) (theta : H ⟶ I) : F ≫ H ⟶ G ≫ I :=
  (F ◁ theta) ≫ (eta ▷ I)

@[simp]
theorem horizontalComp_toNatTrans {F G : A ⟶ B} {H I : B ⟶ C}
    (eta : F ⟶ G) (theta : H ⟶ I) :
    (horizontalComp eta theta).toNatTrans =
      eta.toNatTrans ◫ theta.toNatTrans := by
  ext X
  rfl

/-- Interchange of vertical and horizontal composition in the total model
bicategory. -/
theorem horizontalComp_interchange
    {F₁ F₂ F₃ : A ⟶ B} {G₁ G₂ G₃ : B ⟶ C}
    (eta₁ : F₁ ⟶ F₂) (eta₂ : F₂ ⟶ F₃)
    (theta₁ : G₁ ⟶ G₂) (theta₂ : G₂ ⟶ G₃) :
    horizontalComp eta₁ theta₁ ≫ horizontalComp eta₂ theta₂ =
      horizontalComp (eta₁ ≫ eta₂) (theta₁ ≫ theta₂) := by
  simp only [horizontalComp, Category.assoc]
  rw [← Bicategory.whisker_exchange_assoc eta₁ theta₂,
    ← Bicategory.whiskerLeft_comp_assoc, ← Bicategory.comp_whiskerRight]

end ResourceModelTransformation

/-- Named pentagon coherence for composable changes of resource models. -/
theorem totalModel_pentagon
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E) :
    (Bicategory.associator f g h).hom ▷ i ≫
        (Bicategory.associator f (g ≫ h) i).hom ≫
          f ◁ (Bicategory.associator g h i).hom =
      (Bicategory.associator (f ≫ g) h i).hom ≫
        (Bicategory.associator f g (h ≫ i)).hom :=
  Bicategory.pentagon f g h i

/-- Named triangle coherence for composable changes of resource models. -/
theorem totalModel_triangle (f : A ⟶ B) (g : B ⟶ C) :
    (Bicategory.associator f (𝟙 B) g).hom ≫
        f ◁ (Bicategory.leftUnitor g).hom =
      (Bicategory.rightUnitor f).hom ▷ g :=
  Bicategory.triangle f g

end Ript.Higher
