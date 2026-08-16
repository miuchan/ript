import Ript.Higher.ModelBicategory

/-!
# Explicit 2-cell composition and coherence API

`ModelBicategory` supplies the bicategory instance.  This file exposes the
operations most often used by applications: horizontal composition of model
2-cells, interchange with vertical composition, and named access to the
pentagon and triangle coherence laws.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]
variable {A B C D E : ProcessModel.{u, v, w} R}

namespace ModelTransformation

/-- Horizontal composition of monoidal model 2-cells.  It is bundled directly
from horizontal composition of the underlying natural transformations, whose
monoidality is supplied by mathlib's `NatTrans.IsMonoidal.hcomp` instance. -/
def horizontalComp {F G : A ⟶ B} {H I : B ⟶ C}
    (eta : F ⟶ G) (theta : H ⟶ I) : F ≫ H ⟶ G ≫ I :=
  (F ◁ theta) ≫ (eta ▷ I)

@[simp]
theorem horizontalComp_toNatTrans {F G : A ⟶ B} {H I : B ⟶ C}
    (eta : F ⟶ G) (theta : H ⟶ I) :
    (horizontalComp eta theta).toNatTrans = eta.toNatTrans ◫ theta.toNatTrans := by
  ext X
  rfl

/-- The two definitions of horizontal composition—first whisker left then
whisker right, or use `NatTrans.hcomp`—agree. -/
theorem horizontalComp_eq_whisker {F G : A ⟶ B} {H I : B ⟶ C}
    (eta : F ⟶ G) (theta : H ⟶ I) :
    horizontalComp eta theta = (F ◁ theta) ≫ (eta ▷ I) :=
  rfl

/-- Interchange of vertical and horizontal composition of model 2-cells. -/
theorem horizontalComp_interchange
    {F₁ F₂ F₃ : A ⟶ B} {G₁ G₂ G₃ : B ⟶ C}
    (eta₁ : F₁ ⟶ F₂) (eta₂ : F₂ ⟶ F₃)
    (theta₁ : G₁ ⟶ G₂) (theta₂ : G₂ ⟶ G₃) :
    horizontalComp eta₁ theta₁ ≫ horizontalComp eta₂ theta₂ =
      horizontalComp (eta₁ ≫ eta₂) (theta₁ ≫ theta₂) := by
  simp only [horizontalComp, Category.assoc]
  rw [← Bicategory.whisker_exchange_assoc eta₁ theta₂,
    ← Bicategory.whiskerLeft_comp_assoc, ← Bicategory.comp_whiskerRight]

end ModelTransformation

/-- Named form of the model bicategory's pentagon coherence law. -/
theorem model_pentagon (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E) :
    (Bicategory.associator f g h).hom ▷ i ≫
        (Bicategory.associator f (g ≫ h) i).hom ≫
          f ◁ (Bicategory.associator g h i).hom =
      (Bicategory.associator (f ≫ g) h i).hom ≫
        (Bicategory.associator f g (h ≫ i)).hom :=
  Bicategory.pentagon f g h i

/-- Named form of the model bicategory's triangle coherence law. -/
theorem model_triangle (f : A ⟶ B) (g : B ⟶ C) :
    (Bicategory.associator f (𝟙 B) g).hom ≫
        f ◁ (Bicategory.leftUnitor g).hom =
      (Bicategory.rightUnitor f).hom ▷ g :=
  Bicategory.triangle f g

end Ript.Higher
