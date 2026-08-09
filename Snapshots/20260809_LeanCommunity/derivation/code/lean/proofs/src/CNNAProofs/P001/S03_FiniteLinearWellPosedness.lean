import CNNAProofs.P001.S02_DirectedMaximumPrinciple

/-!
# P001 — finite linear well-posedness

This module closes the finite-dimensional existence and uniqueness layer for
one ordered directed cut without changing the original interior block.

The proof chain is:

1. bundle the original `K_II` block as a rational linear endomorphism;
2. derive injectivity from the kernel-triviality theorem;
3. derive surjectivity from finite dimensionality;
4. solve every boundary column of `K_IB`;
5. assemble the column solutions into one rectangular matrix;
6. prove that the assembled matrix satisfies `K_II X = K_IB`;
7. prove uniqueness by applying injectivity to each pair of columns.

No inverse matrix, determinant, pseudoinverse, regularization, symmetrization,
or grounding vertex is introduced.
-/

namespace CNNAProofs.P001

open scoped BigOperators

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- The unmodified interior block `K_II`, acting on rational interior vectors. -/
def interiorLinearMap {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior) :
    (Fin interior → ℚ) →ₗ[ℚ] (Fin interior → ℚ) :=
  (coreRatMatrixValue blocks.kII).mulVecLin

/-- Pointwise agreement between the bundled linear map and the explicit
    row-by-column `K_II` action used by `IsInteriorKernelVector`. -/
theorem interiorLinearMap_apply {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (vector : Fin interior → ℚ)
    (row : Fin interior) :
    interiorLinearMap blocks vector row =
      ∑ column, blocks.kII row column * vector column := by
  change
    (∑ column,
      (coreRatMatrixValue blocks.kII) row column * vector column) =
      ∑ column, blocks.kII row column * vector column
  rfl

/-- Triviality of the original homogeneous interior kernel implies injectivity
    of the explicitly bundled interior endomorphism. -/
theorem interiorLinearMap_injective {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    Function.Injective (interiorLinearMap blocks) := by
  intro left right hImage
  have hDifferenceImage :
      interiorLinearMap blocks (left - right) = 0 := by
    calc
      interiorLinearMap blocks (left - right) =
          interiorLinearMap blocks left - interiorLinearMap blocks right := by
        exact map_sub (interiorLinearMap blocks) left right
      _ = 0 := by
        rw [hImage, sub_self]
  have hDifferenceKernel :
      IsInteriorKernelVector blocks (left - right) := by
    intro row
    rw [← interiorLinearMap_apply blocks (left - right) row]
    exact congrFun hDifferenceImage row
  have hDifferenceZero : left - right = 0 :=
    hKernel (left - right) hDifferenceKernel
  exact sub_eq_zero.mp hDifferenceZero

/-- Finite-dimensional injectivity of the interior endomorphism implies
    surjectivity on the same rational vector space. -/
theorem interiorLinearMap_surjective {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    Function.Surjective (interiorLinearMap blocks) :=
  LinearMap.surjective_of_injective
    (interiorLinearMap_injective blocks hKernel)

/-- Every right-hand side has an interior solution. -/
theorem interiorRightHandSideSolveExists {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks)
    (rightHandSide : Fin interior → ℚ) :
    ∃ solution : Fin interior → ℚ,
      interiorLinearMap blocks solution = rightHandSide :=
  interiorLinearMap_surjective blocks hKernel rightHandSide

/-- Columnwise surjectivity assembles into an exact rectangular solution of
    the public equation `K_II X = K_IB`. -/
theorem interiorSolveExists {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    InteriorSolveExists blocks := by
  have hColumnExists :
      ∀ column : Fin boundary,
        ∃ solution : Fin interior → ℚ,
          interiorLinearMap blocks solution =
            fun row => blocks.kIB row column := by
    intro column
    exact interiorRightHandSideSolveExists blocks hKernel
      (fun row => blocks.kIB row column)
  choose solutionColumn hSolutionColumn using hColumnExists
  let solve : RationalMatrix interior boundary :=
    Matrix.of fun row column => solutionColumn column row
  refine ⟨solve, ?_⟩
  unfold IsMathlibInteriorSolve rationalMatrixMul
  apply Matrix.ext
  intro row column
  change
    (∑ middle, blocks.kII row middle * solutionColumn column middle) =
      blocks.kIB row column
  rw [← interiorLinearMap_apply blocks (solutionColumn column) row]
  exact congrFun (hSolutionColumn column) row

/-- Two exact rectangular interior solves agree column by column because the
    original interior endomorphism is injective. -/
theorem interiorSolveUnique {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    InteriorSolveUnique blocks := by
  intro left right hLeft hRight
  change
    rationalMatrixMul (coreRatMatrixValue blocks.kII) left =
      coreRatMatrixValue blocks.kIB at hLeft
  change
    rationalMatrixMul (coreRatMatrixValue blocks.kII) right =
      coreRatMatrixValue blocks.kIB at hRight
  apply Matrix.ext
  intro row column
  have hLeftColumn :
      interiorLinearMap blocks (fun middle => left middle column) =
        fun outputRow => blocks.kIB outputRow column := by
    apply funext
    intro outputRow
    rw [interiorLinearMap_apply]
    have hEntry := congrArg (fun matrix => matrix outputRow column) hLeft
    change
      (∑ middle, blocks.kII outputRow middle * left middle column) =
        blocks.kIB outputRow column at hEntry
    exact hEntry
  have hRightColumn :
      interiorLinearMap blocks (fun middle => right middle column) =
        fun outputRow => blocks.kIB outputRow column := by
    apply funext
    intro outputRow
    rw [interiorLinearMap_apply]
    have hEntry := congrArg (fun matrix => matrix outputRow column) hRight
    change
      (∑ middle, blocks.kII outputRow middle * right middle column) =
        blocks.kIB outputRow column at hEntry
    exact hEntry
  have hColumnEquality :
      (fun middle => left middle column) =
        fun middle => right middle column :=
    interiorLinearMap_injective blocks hKernel
      (hLeftColumn.trans hRightColumn.symm)
  exact congrFun hColumnEquality row

/-- The existing public existence and uniqueness contracts hold together. -/
theorem interiorWellPosed {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    InteriorSolveExists blocks ∧ InteriorSolveUnique blocks :=
  ⟨interiorSolveExists blocks hKernel,
    interiorSolveUnique blocks hKernel⟩

end CNNAProofs.P001
