import Mathlib.CategoryTheory.Equivalence
import Ript.Core.Monotone
import Ript.Semantics.ResourceChangingInterpretation

/-!
# Computable path normal forms for free sequential process theories

For every typed signature, raw expressions modulo category laws are represented
by lists of primitive generators with typed endpoints.  This module proves:

* normalization is executable;
* formal derivability is exactly equality of normalized paths;
* the semantic image of any heterogeneous interpretation is exactly its path
  image;
* every path-faithful interpretation is semantically complete.

No finiteness, acyclicity, or thinness assumption is required.
-/

set_option autoImplicit false

namespace Ript.Semantics.SequentialNormalForm

open CategoryTheory
open Ript.Core
open Ript.Semantics
open Ript.Syntax

universe u v w x

/-! ## Typed generator paths -/

/-- A typed list of primitive generators. -/
inductive ProcessPath {R : Type w} (signature : Signature.{u, w} R) :
    signature.Obj → signature.Obj → Type u where
  | nil (X : signature.Obj) : ProcessPath signature X X
  | cons {X Y Z : signature.Obj} (generator : signature.Gen X Y)
      (tail : ProcessPath signature Y Z) : ProcessPath signature X Z

namespace ProcessPath

variable {R : Type w} {signature : Signature.{u, w} R}

/-- Concatenate two typed generator paths. -/
def append {X Y Z : signature.Obj} :
    ProcessPath signature X Y → ProcessPath signature Y Z →
      ProcessPath signature X Z
  | .nil _, right => right
  | .cons generator tail, right => .cons generator (append tail right)

@[simp]
theorem nil_append {X Y : signature.Obj} (path : ProcessPath signature X Y) :
    append (.nil X) path = path :=
  rfl

@[simp]
theorem append_nil {X Y : signature.Obj} (path : ProcessPath signature X Y) :
    append path (.nil Y) = path := by
  induction path with
  | nil => rfl
  | cons generator tail ih => simp [append, ih]

theorem append_assoc {W X Y Z : signature.Obj}
    (first : ProcessPath signature W X)
    (second : ProcessPath signature X Y)
    (third : ProcessPath signature Y Z) :
    append (append first second) third =
      append first (append second third) := by
  induction first with
  | nil => rfl
  | cons generator tail ih => simp [append, ih]

/-- Reify a generator path as a right-associated expression.  The terminal
identity is removed by the category-law derivation below. -/
def toExpr {X Y : signature.Obj} :
    ProcessPath signature X Y → Expr signature X Y
  | .nil X => .id X
  | .cons generator tail => .comp (.gen generator) tail.toExpr

/-- Reified concatenation is derivably equal to syntactic composition. -/
theorem append_derives {X Y Z : signature.Obj}
    (left : ProcessPath signature X Y)
    (right : ProcessPath signature Y Z) :
    Derives (.comp left.toExpr right.toExpr) (append left right).toExpr := by
  induction left with
  | nil => exact .id_comp _
  | cons generator tail ih =>
      exact (Derives.assoc (.gen generator) tail.toExpr right.toExpr).trans
        (Derives.comp_congr (.refl _) (ih right))

end ProcessPath

/-! ## Normalization and proof-theoretic representation -/

variable {R : Type w} {signature : Signature.{u, w} R}

/-- Compute the generator path represented by an expression. -/
def normalize {X Y : signature.Obj} :
    Expr signature X Y → ProcessPath signature X Y
  | .gen generator => .cons generator (.nil _)
  | .id X => .nil X
  | .comp left right =>
      ProcessPath.append (normalize left) (normalize right)

/-- Reifying and renormalizing a generator path returns the same path. -/
@[simp]
theorem normalize_toExpr {X Y : signature.Obj}
    (path : ProcessPath signature X Y) :
    normalize path.toExpr = path := by
  induction path with
  | nil => rfl
  | cons generator tail ih => simp [ProcessPath.toExpr, normalize,
      ProcessPath.append, ih]

/-- Every expression derives to its computed generator path. -/
theorem normalize_derives {X Y : signature.Obj}
    (expression : Expr signature X Y) :
    Derives expression (normalize expression).toExpr :=
  match expression with
  | .gen generator => (Derives.comp_id (.gen generator)).symm
  | .id X => .refl _
  | .comp left right =>
      (Derives.comp_congr (normalize_derives left)
        (normalize_derives right)).trans
          (ProcessPath.append_derives (normalize left) (normalize right))

/-- Every formal derivation preserves the computed generator path. -/
theorem normalize_eq_of_derives {X Y : signature.Obj}
    {left right : Expr signature X Y} (derivation : Derives left right) :
    normalize left = normalize right := by
  induction derivation with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp_congr _ _ ih₁ ih₂ => exact congrArg₂ ProcessPath.append ih₁ ih₂
  | id_comp => rfl
  | comp_id expression => exact ProcessPath.append_nil (normalize expression)
  | assoc first second third =>
      exact ProcessPath.append_assoc (normalize first) (normalize second)
        (normalize third)

/-- **Free sequential representation theorem.** Formal derivability is exactly
equality of computable generator-path normal forms. -/
theorem derives_iff_normalize_eq {X Y : signature.Obj}
    (left right : Expr signature X Y) :
    Derives left right ↔ normalize left = normalize right := by
  constructor
  · exact normalize_eq_of_derives
  · intro equality
    have rightDerivation := normalize_derives right
    rw [← equality] at rightDerivation
    exact (normalize_derives left).trans rightDerivation.symm

/-! ## Quotient term-model representation -/

/-- Read a quotient term-model morphism as its unique typed generator path. -/
def termHomToPath {X Y : TermModel signature} :
    (X ⟶ Y) → ProcessPath signature X Y :=
  Quotient.lift normalize
    (fun _ _ derivation ↦ normalize_eq_of_derives derivation)

/-- Embed a typed generator path into the quotient term model. -/
def pathToTerm {X Y : TermModel signature}
    (path : ProcessPath signature X Y) : X ⟶ Y :=
  TermModel.quote signature path.toExpr

/-- Normalizing the quoted form of a term-model morphism returns that
morphism's original quotient class. -/
theorem pathToTerm_termHomToPath {X Y : TermModel signature}
    (morphism : X ⟶ Y) :
    pathToTerm (termHomToPath morphism) = morphism := by
  induction morphism using Quotient.inductionOn with
  | _ expression => exact Quotient.sound (normalize_derives expression).symm

/-- Quoting and rereading a typed path returns that path definitionally up to
the executable normalizer. -/
@[simp]
theorem termHomToPath_pathToTerm {X Y : TermModel signature}
    (path : ProcessPath signature X Y) :
    termHomToPath (pathToTerm path) = path :=
  normalize_toExpr path

/-- **Free-category path representation.** Every hom-set of the sequential
term model is computably equivalent to the corresponding type of generator
paths.  The quotient is used only to certify equality; normalization computes
the forward map. -/
def termHomEquivPath (X Y : TermModel signature) :
    (X ⟶ Y) ≃ ProcessPath signature X Y where
  toFun := termHomToPath
  invFun := pathToTerm
  left_inv := pathToTerm_termHomToPath
  right_inv := termHomToPath_pathToTerm

@[simp]
theorem termHomEquivPath_apply_quote {X Y : TermModel signature}
    (expression : Expr signature X Y) :
    termHomEquivPath X Y (TermModel.quote signature expression) =
      normalize expression :=
  rfl

/-! ## The free path category -/

/-- A wrapper around signature objects whose morphisms are typed generator
paths.  The wrapper keeps its category instance distinct from the quotient
term model's instance on the same underlying object symbols. -/
structure PathModel {R : Type w} (signature : Signature.{u, w} R) where
  /-- The represented signature object. -/
  object : signature.Obj

namespace PathModel

/-- Path-model objects are determined by their signature object. -/
@[ext]
theorem ext {R : Type w} {signature : Signature.{u, w} R}
    {X Y : PathModel signature} (object_eq : X.object = Y.object) : X = Y := by
  cases X
  cases Y
  cases object_eq
  rfl

variable {R : Type w} (signature : Signature.{u, w} R)

/-- Typed generator paths form a category by concatenation. -/
instance category : Category.{u} (PathModel signature) where
  Hom X Y := ProcessPath signature X.object Y.object
  id X := .nil X.object
  comp := ProcessPath.append
  id_comp := ProcessPath.nil_append
  comp_id := ProcessPath.append_nil
  assoc := ProcessPath.append_assoc

variable [AddCommMonoid R] [Preorder R]

/-- A path costs exactly the syntax cost of its canonical reification. -/
def cost {X Y : PathModel signature} (path : X ⟶ Y) : R :=
  path.toExpr.syntaxCost

/-- The path category carries the exact free sequential process cost. -/
instance hasProcessCost : HasProcessCost (PathModel signature) R where
  cost := cost signature
  cost_id _ := rfl
  cost_comp left right :=
    le_of_eq (ProcessPath.append_derives left right).syntaxCost_eq.symm

end PathModel

/-- Normalize quotient term-model morphisms into the explicit path category. -/
def termToPathFunctor :
    CategoryTheory.Functor (TermModel signature) (PathModel signature) where
  obj X := ⟨X⟩
  map := termHomToPath
  map_id _ := rfl
  map_comp {X Y Z} left right := by
    induction left using Quotient.inductionOn with
    | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => rfl

/-- Quote explicit paths back into the quotient term model. -/
def pathToTermFunctor :
    CategoryTheory.Functor (PathModel signature) (TermModel signature) where
  obj X := X.object
  map := pathToTerm
  map_id _ := rfl
  map_comp left right :=
    Quotient.sound (ProcessPath.append_derives left right).symm

/-- The quotient-to-path-to-quotient round trip is naturally the identity. -/
def termPathUnitIso :
    𝟭 (TermModel signature) ≅ termToPathFunctor (signature := signature) ⋙
      pathToTermFunctor (signature := signature) where
  hom :=
    { app := fun X ↦ 𝟙 X
      naturality := fun {X Y} morphism ↦ by
        change morphism ≫ 𝟙 _ = 𝟙 _ ≫ pathToTerm (termHomToPath morphism)
        simp only [Category.comp_id, Category.id_comp]
        exact (pathToTerm_termHomToPath morphism).symm }
  inv :=
    { app := fun X ↦ 𝟙 X
      naturality := fun {X Y} morphism ↦ by
        change pathToTerm (termHomToPath morphism) ≫ 𝟙 _ = 𝟙 _ ≫ morphism
        simp only [Category.comp_id, Category.id_comp]
        exact pathToTerm_termHomToPath morphism }
  hom_inv_id := by
    ext X
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    exact Category.id_comp _
  inv_hom_id := by
    ext X
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    exact Category.id_comp _

/-- The path-to-quotient-to-path round trip is naturally the identity. -/
def pathTermCounitIso :
    pathToTermFunctor (signature := signature) ⋙
        termToPathFunctor (signature := signature) ≅
      𝟭 (PathModel signature) where
  hom :=
    { app := fun X ↦ eqToHom (PathModel.ext rfl)
      naturality := fun {X Y} path ↦ by
        cases X
        cases Y
        change termHomToPath (pathToTerm path) ≫ 𝟙 _ = 𝟙 _ ≫ path
        simp only [Category.comp_id, Category.id_comp]
        exact termHomToPath_pathToTerm path }
  inv :=
    { app := fun X ↦ eqToHom (PathModel.ext rfl).symm
      naturality := fun {X Y} path ↦ by
        cases X
        cases Y
        change path ≫ 𝟙 _ = 𝟙 _ ≫ termHomToPath (pathToTerm path)
        simp only [Category.comp_id, Category.id_comp]
        exact (termHomToPath_pathToTerm path).symm }
  hom_inv_id := by
    ext X
    cases X
    rfl
  inv_hom_id := by
    ext X
    cases X
    rfl

/-- **Categorical free-path representation theorem.** The quotient sequential
term model is explicitly equivalent to the category of typed generator paths.
Both functors are constructive: normalization goes forward and quotation goes
backward. -/
def termPathEquivalence :
    TermModel signature ≌ PathModel signature where
  functor := termToPathFunctor
  inverse := pathToTermFunctor
  unitIso := termPathUnitIso
  counitIso := pathTermCounitIso
  functor_unitIso_comp X := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

section ResourceExactPathRepresentation

variable [AddCommMonoid R] [Preorder R]

/-- Normalization is resource-nonincreasing; in fact the theorem below proves
that it preserves the exact quotient cost. -/
def termToPathResourceFunctor :
    ResourceMonotoneFunctor (TermModel signature) (PathModel signature) R where
  toFunctor := termToPathFunctor
  map_cost_le morphism := by
    induction morphism using Quotient.inductionOn with
    | _ expression =>
      exact le_of_eq (normalize_derives expression).syntaxCost_eq.symm

/-- Path quotation is resource-nonincreasing and exact. -/
def pathToTermResourceFunctor :
    ResourceMonotoneFunctor (PathModel signature) (TermModel signature) R where
  toFunctor := pathToTermFunctor
  map_cost_le _ := le_rfl

/-- **Exact resource representation.** Normalization preserves the process
cost of every quotient morphism exactly. -/
theorem termToPath_cost_eq {X Y : TermModel signature} (morphism : X ⟶ Y) :
    processCost (R := R) (termToPathFunctor.map morphism) =
      processCost (R := R) morphism := by
  induction morphism using Quotient.inductionOn with
  | _ expression => exact (normalize_derives expression).syntaxCost_eq.symm

/-- Quoting a path preserves its exact free-process cost. -/
@[simp]
theorem pathToTerm_cost_eq {X Y : PathModel signature} (path : X ⟶ Y) :
    processCost (R := R) (pathToTermFunctor.map path) =
      processCost (R := R) path :=
  rfl

end ResourceExactPathRepresentation

/-! ## Semantic image and completeness -/

variable [AddCommMonoid R] [Preorder R]

/-- A semantic morphism represented by some expression. -/
def InImage {S : Type w} {C : Type x} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : R →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (morphism : interpretation.obj X ⟶ interpretation.obj Y) :
    Prop :=
  ∃ expression : Expr signature X Y,
    ResourceChangingInterpretation.eval interpretation expression = morphism

/-- **Exact semantic-image representation.** The image of an interpretation is
exactly the denotations of typed generator paths. -/
theorem inImage_iff_exists_path
    {S : Type w} {C : Type x} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : R →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (morphism : interpretation.obj X ⟶ interpretation.obj Y) :
    InImage interpretation morphism ↔
      ∃ path : ProcessPath signature X Y,
        morphism = ResourceChangingInterpretation.eval interpretation
          path.toExpr := by
  constructor
  · rintro ⟨expression, rfl⟩
    exact ⟨normalize expression,
      ResourceChangingInterpretation.soundness interpretation
        (normalize_derives expression)⟩
  · rintro ⟨path, equality⟩
    exact ⟨path.toExpr, equality.symm⟩

/-- A heterogeneous interpretation is path faithful when equal path
denotations imply equal typed generator paths. -/
def PathFaithful
    {S : Type w} {C : Type x} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : R →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) : Prop :=
  ∀ {X Y : signature.Obj} (left right : ProcessPath signature X Y),
    ResourceChangingInterpretation.eval interpretation left.toExpr =
      ResourceChangingInterpretation.eval interpretation right.toExpr →
    left = right

/-- Equality reflection for one interpretation. -/
def SemanticallyComplete
    {S : Type w} {C : Type x} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : R →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) : Prop :=
  ∀ {X Y : signature.Obj} (left right : Expr signature X Y),
    ResourceChangingInterpretation.eval interpretation left =
      ResourceChangingInterpretation.eval interpretation right →
    Derives left right

/-- **Generic semantic completeness theorem.** Every path-faithful
heterogeneous interpretation reflects formal equality. -/
theorem semanticallyComplete_of_pathFaithful
    {S : Type w} {C : Type x} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : R →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (faithful : PathFaithful interpretation) :
    SemanticallyComplete interpretation := by
  intro X Y left right equality
  have leftSound := ResourceChangingInterpretation.soundness interpretation
    (normalize_derives left)
  have rightSound := ResourceChangingInterpretation.soundness interpretation
    (normalize_derives right)
  have pathEquality := faithful (normalize left) (normalize right)
    (leftSound.symm.trans (equality.trans rightSound))
  exact (derives_iff_normalize_eq left right).2 pathEquality

end Ript.Semantics.SequentialNormalForm
