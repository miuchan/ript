import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagLocalization
import Ript.Higher.Localization

/-!
# Formal cost-exact zigzags of process models

This module specializes the generic marked-zigzag construction to the
saturated cost-exact marking on the full bicategory of resource-indexed
process models.  It supplies the executable 1-cell syntax of the intended
higher localization: every model morphism may be traversed forward, while a
cost-exact morphism may additionally be traversed backward.

For every candidate satisfying the full cost-exact bicategorical localization
predicate, the syntax has a canonical single-valued interpretation after the
proof-level choice of adjoint-equivalence witnesses.  Concatenation is
represented by target composition, and both marked cancellation orders are
represented by the chosen unit and counit.

The generic quotient now supplies an actual target bicategory and canonical
pseudofunctor, and this file proves that it inverts all saturated cost-exact
arrows. It also constructs the universal lift and its adjoint-equivalence
factorization for every cost-exact-inverting pseudofunctor. Recursive mate
extension of strong transformations and modifications proves the local
equivalence, so the canonical inclusion satisfies the complete
bicategorical-localization predicate.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher.CostExactZigzag

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u v w u' v' w'

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- One oriented step for the saturated cost-exact marking. -/
abbrev Step :=
  CategoryTheory.Bicategory.MarkedZigzag.Step
    (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R))

/-- A typed finite zigzag of model morphisms and formal reverses of
cost-exact model morphisms. -/
abbrev Word :=
  CategoryTheory.Bicategory.MarkedZigzag.Word
    (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R))

/-- Raw freely generated 2-cell expressions between parallel cost-exact
zigzags.  The eventual localization quotient will impose their equations. -/
abbrev Cell {M N : ProcessModel.{u, v, w} R}
    (first second : Word (R := R) M N) :=
  CategoryTheory.Bicategory.MarkedZigzag.Cell
    (costExactArrows R) first second

/-- The actual presented bicategory candidate for the full cost-exact
localization of process models. -/
abbrev Localization :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.Localization
    (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R))

/-- Canonical pseudofunctor from all process models into the presented
cost-exact zigzag bicategory. -/
def inclusion : ProcessModel.{u, v, w} R ⥤ᵖ Localization (R := R) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.inclusion
    (costExactArrows R)

/-- The presented cost-exact localization has exactly the source object set,
so its canonical inclusion is surjective on objects. -/
theorem inclusion_obj_surjective :
    Function.Surjective (inclusion (R := R)).obj :=
  CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.inclusion_obj_surjective
    (costExactArrows R)

/-- The presented inclusion sends every saturated cost-exact arrow to an
adjoint equivalence. -/
theorem inclusion_inverts :
    (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)).IsInvertedBy
        (inclusion (R := R)) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.inclusion_inverts
    (costExactArrows R)

/-- Chosen adjoint equivalence in the presented target associated with one
cost-exact source arrow. -/
noncomputable def markedEquivalence
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    (CategoryTheory.Bicategory.MarkedZigzag.Presented.Localization.mk M :
      Localization (R := R)) ≌
      CategoryTheory.Bicategory.MarkedZigzag.Presented.Localization.mk N :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.markedEquivalence
    (costExactArrows R) F hF

@[simp]
theorem markedEquivalence_hom
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    (markedEquivalence F hF).hom =
      CategoryTheory.Bicategory.MarkedZigzag.Word.forward
        (costExactArrows R) F :=
  rfl

@[simp]
theorem markedEquivalence_inv
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    (markedEquivalence F hF).inv =
      CategoryTheory.Bicategory.MarkedZigzag.Word.backward
        (costExactArrows R) F hF :=
  rfl

/-- Embed an arbitrary model morphism as a one-step forward word. -/
def forward {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N) :
    Word (R := R) M N :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.forward
    (costExactArrows R) F

/-- Embed a marked cost-exact model morphism as a one-step reverse word. -/
def backward {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) : Word (R := R) N M :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.backward
    (costExactArrows R) F hF

/-- A raw cost-reflecting model morphism has a formal reverse word because
the higher marking is its explicit invertible-2-cell saturation. -/
def backwardCostReflecting {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costReflectingArrows R F) : Word (R := R) N M :=
  backward F (costReflectingArrows_le_costExactArrows F hF)

/-- Raw unit 2-cell generator from the empty word to a cost-exact arrow
followed by its formal reverse. -/
def unitCell {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    Cell (R := R) (.nil M)
      (CategoryTheory.Bicategory.MarkedZigzag.Word.append
        (costExactArrows R) (forward F) (backward F hF)) :=
  CategoryTheory.Bicategory.MarkedZigzag.Cell.unit
    (costExactArrows R) F hF

/-- Raw counit 2-cell generator from a formal reverse followed by its
cost-exact arrow to the empty word. -/
def counitCell {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    Cell (R := R)
      (CategoryTheory.Bicategory.MarkedZigzag.Word.append
        (costExactArrows R) (backward F hF) (forward F))
      (.nil N) :=
  CategoryTheory.Bicategory.MarkedZigzag.Cell.counit
    (costExactArrows R) F hF

/-- Raw cost reflection is enough to construct the future unit generator. -/
def unitCellCostReflecting {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costReflectingArrows R F) :
    Cell (R := R) (.nil M)
      (CategoryTheory.Bicategory.MarkedZigzag.Word.append
        (costExactArrows R) (forward F) (backwardCostReflecting F hF)) :=
  unitCell F (costReflectingArrows_le_costExactArrows F hF)

/-- Raw cost reflection is enough to construct the future counit generator. -/
def counitCellCostReflecting {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costReflectingArrows R F) :
    Cell (R := R)
      (CategoryTheory.Bicategory.MarkedZigzag.Word.append
        (costExactArrows R) (backwardCostReflecting F hF) (forward F))
      (.nil N) :=
  counitCell F (costReflectingArrows_le_costExactArrows F hF)

/-- The source local hom-category maps functorially into the presented
cost-exact zigzag hom-category, retaining every original 2-cell as a quotient
generator. -/
def forwardHomFunctor (M N : ProcessModel.{u, v, w} R) :
    (M ⟶ N) ⥤ Word (R := R) M N :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.forwardHomFunctor
    (costExactArrows R) M N

/-- The forward source identity is isomorphic to the empty cost-exact word in
the presented local hom-category. -/
def sourceIdIso (M : ProcessModel.{u, v, w} R) :
    forward (𝟙 M) ≅
      (CategoryTheory.Bicategory.MarkedZigzag.Word.nil M :
        Word (R := R) M M) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.sourceIdIso
    (costExactArrows R) M

/-- The forward source composite is isomorphic to concatenation of the two
forward words. -/
def sourceCompIso {M N P : ProcessModel.{u, v, w} R}
    (F : M ⟶ N) (G : N ⟶ P) :
    forward (F ≫ G) ≅
      CategoryTheory.Bicategory.MarkedZigzag.Word.append
        (costExactArrows R) (forward F) (forward G) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.sourceCompIso
    (costExactArrows R) F G

/-- A marked arrow and its formal reverse have an invertible unit in the
presented local category. -/
def markedUnitIso {M N : ProcessModel.{u, v, w} R}
    (F : M ⟶ N) (hF : costExactArrows R F) :
    (CategoryTheory.Bicategory.MarkedZigzag.Word.nil M :
      Word (R := R) M M) ≅
        CategoryTheory.Bicategory.MarkedZigzag.Word.append
          (costExactArrows R) (forward F) (backward F hF) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.markedUnitIso
    (costExactArrows R) F hF

/-- A formal reverse followed by its marked arrow has an invertible counit in
the presented local category. -/
def markedCounitIso {M N : ProcessModel.{u, v, w} R}
    (F : M ⟶ N) (hF : costExactArrows R F) :
    CategoryTheory.Bicategory.MarkedZigzag.Word.append
        (costExactArrows R) (backward F hF) (forward F) ≅
      (CategoryTheory.Bicategory.MarkedZigzag.Word.nil N :
        Word (R := R) N N) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.markedCounitIso
    (costExactArrows R) F hF

/-- Executable concatenation of cost-exact formal zigzags. -/
def append {M N P : ProcessModel.{u, v, w} R} :
    Word (R := R) M N → Word (R := R) N P → Word (R := R) M P :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.append (costExactArrows R)

/-- Number of oriented steps in a cost-exact formal zigzag. -/
def length {M N : ProcessModel.{u, v, w} R} :
    Word (R := R) M N → ℕ :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.length (costExactArrows R)

/-- Weak associativity of cost-exact zigzag composition, represented by the
actual associator isomorphism of the presented local category. -/
def appendAssociatorIso {M N P Q : ProcessModel.{u, v, w} R}
    (first : Word (R := R) M N) (second : Word (R := R) N P)
    (third : Word (R := R) P Q) :
    append (append first second) third ≅
      append first (append second third) :=
  CategoryTheory.Bicategory.MarkedZigzag.Presented.wordAssociatorIso
    (costExactArrows R) first second third

@[simp]
theorem length_append {M N P : ProcessModel.{u, v, w} R}
    (first : Word (R := R) M N) (second : Word (R := R) N P) :
    length (append first second) = length first + length second :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.length_append
    (costExactArrows R) first second

@[simp]
theorem length_forward {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N) :
    length (forward F) = 1 :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.length_forward
    (costExactArrows R) F

@[simp]
theorem length_backward {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    length (backward F hF) = 1 :=
  CategoryTheory.Bicategory.MarkedZigzag.Word.length_backward
    (costExactArrows R) F hF

variable {L : Type u'} [Bicategory.{w', v'} L]
variable (Q : ProcessModel.{u, v, w} R ⥤ᵖ L)

/-- The universal single-valued interpreter out of the presented cost-exact
zigzag bicategory for any pseudofunctor that inverts every cost-exact arrow. -/
noncomputable def liftOfInverts
    (hQ : (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)).IsInvertedBy Q) :
    Localization (R := R) ⥤ᵖ L :=
  CategoryTheory.Bicategory.MarkedZigzag.InversionData.lift
    (costExactArrows R) Q
      (CategoryTheory.Bicategory.MarkedZigzag.InversionData.ofIsInvertedBy
        (costExactArrows R) Q hQ)

/-- Restricting the universal cost-exact word interpreter along the canonical
inclusion recovers the original pseudofunctor up to adjoint equivalence. -/
noncomputable def factorizationOfInverts
    (hQ : (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)).IsInvertedBy Q) :
    (inclusion (R := R)).comp (liftOfInverts Q hQ) ≌ Q :=
  CategoryTheory.Bicategory.MarkedZigzag.InversionData.factorization
    (costExactArrows R) Q
      (CategoryTheory.Bicategory.MarkedZigzag.InversionData.ofIsInvertedBy
        (costExactArrows R) Q hQ)

/-- Every cost-exact-inverting pseudofunctor factors through the presented
cost-exact zigzag inclusion. This proves the full object-level existence part
of its bicategorical localization universal property. -/
theorem factorsThrough
    (hQ : (costExactArrows (R := R) :
      Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)).IsInvertedBy Q) :
    (inclusion (R := R)).FactorsThrough Q :=
  CategoryTheory.Bicategory.MarkedZigzag.InversionData.factorsThrough
    (costExactArrows R) Q hQ

/-- **Existence theorem for the higher cost-exact localization.** The
presented cost-exact zigzag inclusion inverts precisely the marked arrows,
admits all marking-inverting pseudofunctor lifts up to adjoint equivalence,
and induces equivalences on every category of strong transformations and
modifications. -/
theorem inclusion_isBicategoricalLocalization :
    IsCostExactBicategoricalLocalization (inclusion (R := R)) :=
  CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.inclusion_isBicategoricalLocalization
    (costExactArrows R)

/-- Chosen adjoint-equivalence images of all cost-exact arrows, extracted from
a genuine cost-exact bicategorical localization witness. -/
noncomputable def inversionData
    (hQ : IsCostExactBicategoricalLocalization Q) :
    CategoryTheory.Bicategory.MarkedZigzag.InversionData
      (costExactArrows R) Q :=
  CategoryTheory.Bicategory.MarkedZigzag.InversionData.ofIsInvertedBy
    (costExactArrows R) Q hQ.inverts

/-- **Cost-exact zigzag representation theorem.** Every formal cost-exact
zigzag has one recursive interpretation in any genuine higher localization;
concatenation and both marked cancellation orders are represented by
bicategorical coherence, unit, and counit isomorphisms. -/
noncomputable def interpretationCore
    (hQ : IsCostExactBicategoricalLocalization Q) :
    CategoryTheory.Bicategory.MarkedZigzag.InversionData.InterpretationCore
      (costExactArrows R) Q (inversionData Q hQ) :=
  CategoryTheory.Bicategory.MarkedZigzag.InversionData.interpretationCore
    (costExactArrows R) Q (inversionData Q hQ)

/-- The forward/reverse word of every cost-exact arrow cancels after
interpretation in a genuine higher localization. -/
noncomputable def forwardBackwardCancellation
    (hQ : IsCostExactBicategoricalLocalization Q)
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    (interpretationCore Q hQ).eval
        (append (forward F) (backward F hF)) ≅ 𝟙 (Q.obj M) :=
  (interpretationCore Q hQ).forwardBackward F hF

/-- The reverse/forward word of every cost-exact arrow cancels after
interpretation in a genuine higher localization. -/
noncomputable def backwardForwardCancellation
    (hQ : IsCostExactBicategoricalLocalization Q)
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) :
    (interpretationCore Q hQ).eval
        (append (backward F hF) (forward F)) ≅ 𝟙 (Q.obj N) :=
  (interpretationCore Q hQ).backwardForward F hF

end Ript.Higher.CostExactZigzag
