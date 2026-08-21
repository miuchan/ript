import Mathlib.CategoryTheory.CopyDiscardCategory.Cartesian
import Ript.Syntax.DependentBranching.Free

/-!
# Cartesian symmetric monoidal structure on branching algebras

Dependent branching algebras have pointwise products. The product carrier is
the ordinary product type, leaf is paired, and every generator operation is
evaluated componentwise.  Together with the one-point algebra this gives
chosen finite products, hence a cartesian symmetric monoidal category.

The central representation theorem says that folding one common protocol into
a product algebra is exactly the pair of its two model interpretations.  Thus
the tensor packages parallel cross-model observation without identifying the
models or their carriers.
-/

set_option autoImplicit false

namespace Ript.Syntax.DependentBranching.Free

open CategoryTheory Limits MonoidalCategory

open Ript.Syntax.DependentBranching

universe u

variable {signature : Signature.{u}}

/-- One-point terminal branching algebra. -/
abbrev unitAlgebra (signature : Signature.{u}) : Algebra signature where
  Carrier := PUnit.{u + 1}
  leaf := PUnit.unit
  node _ _ := PUnit.unit

/-- Pointwise product of two branching algebras. -/
abbrev tensorAlgebra (first second : Algebra signature) : Algebra signature where
  Carrier := first × second
  leaf := (first.leaf, second.leaf)
  node generator continuations :=
    (first.node generator fun outcome ↦ (continuations outcome).1,
      second.node generator fun outcome ↦ (continuations outcome).2)

/-- First projection from a product branching algebra. -/
def fstHom (first second : Algebra signature) :
    Hom (tensorAlgebra first second) first where
  toFun := Prod.fst
  map_leaf := rfl
  map_node _ _ := rfl

/-- Second projection from a product branching algebra. -/
def sndHom (first second : Algebra signature) :
    Hom (tensorAlgebra first second) second where
  toFun := Prod.snd
  map_leaf := rfl
  map_node _ _ := rfl

/-- Pair two algebra homomorphisms into the product algebra. -/
def pairHom {source first second : Algebra signature}
    (left : Hom source first) (right : Hom source second) :
    Hom source (tensorAlgebra first second) where
  toFun value := (left.toFun value, right.toFun value)
  map_leaf := by rw [left.map_leaf, right.map_leaf]
  map_node generator continuations := by
    rw [left.map_node, right.map_node]

/-- Componentwise tensor of two algebra homomorphisms. -/
def tensorHom {firstSource firstTarget secondSource secondTarget :
    Algebra signature}
    (first : Hom firstSource firstTarget)
    (second : Hom secondSource secondTarget) :
    Hom (tensorAlgebra firstSource secondSource)
      (tensorAlgebra firstTarget secondTarget) where
  toFun value := (first.toFun value.1, second.toFun value.2)
  map_leaf := by rw [first.map_leaf, second.map_leaf]
  map_node generator continuations := by
    rw [first.map_node, second.map_node]

/-! ## Chosen finite products -/

namespace Cartesian

/-- The one-point algebra is terminal. -/
def isTerminalUnit : IsTerminal (unitAlgebra signature) :=
  letI (algebra : Algebra signature) :
      Unique (algebra ⟶ unitAlgebra signature) :=
    { default :=
        { toFun := fun _ ↦ PUnit.unit
          map_leaf := rfl
          map_node := fun _ _ ↦ rfl }
      uniq := fun morphism ↦ by
        apply Hom.ext
        funext value
        exact Subsingleton.elim _ _ }
  .ofUnique _

/-- Chosen terminal limit cone. -/
def terminalLimitCone : LimitCone (Functor.empty (Algebra signature)) :=
  ⟨_, isTerminalUnit⟩

/-- Product cone with componentwise projections. -/
def binaryProductCone (first second : Algebra signature) :
    BinaryFan first second :=
  BinaryFan.mk (fstHom first second) (sndHom first second)

/-- Pointwise algebra products satisfy the binary-product universal property. -/
def binaryProductLimit (first second : Algebra signature) :
    IsLimit (binaryProductCone first second) where
  lift cone := pairHom (BinaryFan.fst cone) (BinaryFan.snd cone)
  fac cone index := Discrete.recOn index fun index ↦
    WalkingPair.casesOn index rfl rfl
  uniq cone morphism equations := by
    apply Hom.ext
    funext value
    apply Prod.ext
    · exact congrArg (fun hom ↦ hom.toFun value)
        (equations ⟨WalkingPair.left⟩)
    · exact congrArg (fun hom ↦ hom.toFun value)
        (equations ⟨WalkingPair.right⟩)

/-- Chosen binary-product limit cone. -/
def binaryProductLimitCone (first second : Algebra signature) :
    LimitCone (pair first second) :=
  ⟨_, binaryProductLimit first second⟩

end Cartesian

/-- Branching algebras form a cartesian monoidal category under pointwise
products. -/
instance cartesianMonoidalCategory :
    CartesianMonoidalCategory (Algebra signature) where
  tensorObj := tensorAlgebra
  tensorUnit := unitAlgebra signature
  __ := CartesianMonoidalCategory.ofChosenFiniteProducts
    Cartesian.terminalLimitCone Cartesian.binaryProductLimitCone

/-- Cartesian products supply the canonical braiding. -/
instance braidedCategory : BraidedCategory (Algebra signature) :=
  .ofCartesianMonoidalCategory

/-- Every algebra homomorphism preserves the canonical copy and discard maps. -/
@[instance_reducible]
instance copyDiscardCategory : CopyDiscardCategory (Algebra signature) :=
  CartesianCopyDiscard.ofCartesianMonoidalCategory

/-- Tensor is definitionally the pointwise product algebra. -/
theorem tensorObj_eq (first second : Algebra signature) :
    first ⊗ second = tensorAlgebra first second :=
  rfl

/-- Tensoring algebra homomorphisms acts componentwise. -/
@[simp]
theorem tensorHom_toFun
    {firstSource firstTarget secondSource secondTarget : Algebra signature}
    (first : firstSource ⟶ firstTarget)
    (second : secondSource ⟶ secondTarget)
    (value : firstSource × secondSource) :
    (first ⊗ₘ second).toFun value =
      (first.toFun value.1, second.toFun value.2) :=
  rfl

/-- The monoidal associator rebrackets product carriers. -/
@[simp]
theorem associator_hom_toFun (first second third : Algebra signature)
    (value : (first × second) × third) :
    (α_ first second third).hom.toFun value =
      (value.1.1, (value.1.2, value.2)) :=
  rfl

/-- The left unitor removes the one-point carrier. -/
@[simp]
theorem leftUnitor_hom_toFun (algebra : Algebra signature)
    (value : PUnit × algebra) :
    (λ_ algebra).hom.toFun value = value.2 :=
  rfl

/-- The right unitor removes the one-point carrier. -/
@[simp]
theorem rightUnitor_hom_toFun (algebra : Algebra signature)
    (value : algebra × PUnit) :
    (ρ_ algebra).hom.toFun value = value.1 :=
  rfl

/-- The cartesian braiding swaps model interpretations. -/
@[simp]
theorem braiding_hom_toFun (first second : Algebra signature)
    (value : first × second) :
    (β_ first second).hom.toFun value = (value.2, value.1) :=
  rfl

/-! ## Product interpretation theorems -/

/-- **Parallel model representation.**  Folding one common dependent tree
into the tensor product of two model algebras is exactly the pair of folds. -/
theorem fold_tensor (first second : Algebra signature)
    (tree : Tree signature) :
    fold (first ⊗ second) tree =
      (fold first tree, fold second tree) := by
  induction tree with
  | leaf => rfl
  | node generator next induction =>
      simp only [fold_node]
      change
        (first.node generator fun outcome ↦
            (fold (first ⊗ second) (next outcome)).1,
          second.node generator fun outcome ↦
            (fold (first ⊗ second) (next outcome)).2) = _
      have firstContinuations :
          (fun outcome ↦ (fold (first ⊗ second) (next outcome)).1) =
            (fun outcome ↦ fold first (next outcome)) := by
        funext outcome
        exact congrArg Prod.fst (induction outcome)
      have secondContinuations :
          (fun outcome ↦ (fold (first ⊗ second) (next outcome)).2) =
            (fun outcome ↦ fold second (next outcome)) := by
        funext outcome
        exact congrArg Prod.snd (induction outcome)
      rw [firstContinuations, secondContinuations]

/-- Equality in a product interpretation is exactly simultaneous equality in
its two component models. -/
theorem fold_tensor_eq_iff (first second : Algebra signature)
    (left right : Tree signature) :
    fold (first ⊗ second) left = fold (first ⊗ second) right ↔
      fold first left = fold first right ∧
        fold second left = fold second right := by
  rw [fold_tensor, fold_tensor]
  constructor
  · intro equal
    exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩
  · rintro ⟨firstEqual, secondEqual⟩
    rw [firstEqual, secondEqual]

/-- The unique free interpretation into a product algebra is the pairing of
the two unique component interpretations. -/
theorem foldHom_tensor (first second : Algebra signature) :
    foldHom (first ⊗ second) =
      pairHom (foldHom first) (foldHom second) := by
  exact hom_ext_from_tree _ _ _

/-- The term model can be paired with any model to obtain a jointly faithful
interpretation. -/
theorem tree_tensor_reflects_equality (algebra : Algebra signature)
    {left right : Tree signature}
    (equal : fold (treeAlgebra signature ⊗ algebra) left =
      fold (treeAlgebra signature ⊗ algebra) right) :
    left = right := by
  have component :=
    (fold_tensor_eq_iff (treeAlgebra signature) algebra left right).mp
      equal |>.1
  simpa using component

/-- **Joint-model completeness.**  Formal derivability is equivalent to
equality in the product of the term model with any second model. -/
theorem jointSemanticCompleteness (algebra : Algebra signature)
    {left right : Tree signature} :
    Derives left right ↔
      fold (treeAlgebra signature ⊗ algebra) left =
        fold (treeAlgebra signature ⊗ algebra) right := by
  constructor
  · intro derivation
    exact derivation.sound _
  · intro equal
    exact Derives.iff_eq.mpr (tree_tensor_reflects_equality algebra equal)

end Ript.Syntax.DependentBranching.Free
