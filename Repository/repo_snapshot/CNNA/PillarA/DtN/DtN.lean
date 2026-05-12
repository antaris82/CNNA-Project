import CNNA.PillarA.Finite.DirichletLaplacian

set_option autoImplicit false

namespace CNNA.PillarA.DtN

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite

universe u

structure TwoSidedInv {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : Prop where
  left_inv : A * B = 1
  right_inv : B * A = 1

private structure InternalInteriorInverse
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (D : DirichletLaplacianStrong Cell T) where
  inv : Matrix D.interiorVertex D.interiorVertex ℝ
  inv_ok : TwoSidedInv D.interiorBlock inv

namespace InternalInteriorInverse

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

def cast (h : T = U)
    {D : DirichletLaplacianStrong Cell T}
    (w : InternalInteriorInverse D) :
    InternalInteriorInverse (DirichletLaplacianStrong.cast (Cell := Cell) h D) := by
  cases h
  exact w

theorem cast_rfl
    {D : DirichletLaplacianStrong Cell T}
    (w : InternalInteriorInverse D) :
    cast (Cell := Cell) rfl w = w := by
  rfl

def boundaryOperator
    {D : DirichletLaplacianStrong Cell T}
    (w : InternalInteriorInverse D) :
    Matrix D.boundaryVertex D.boundaryVertex ℝ :=
  D.boundaryBlock - D.boundaryInteriorBlock * w.inv * D.interiorBoundaryBlock

def interiorSolve
    {D : DirichletLaplacianStrong Cell T}
    (w : InternalInteriorInverse D)
    (φ : D.boundaryVertex → ℝ) :
    D.interiorVertex → ℝ :=
  fun i => - (w.inv.mulVec (D.interiorBoundaryBlock.mulVec φ)) i

def boundaryFlux
    {D : DirichletLaplacianStrong Cell T}
    (φ : D.boundaryVertex → ℝ)
    (uI : D.interiorVertex → ℝ) :
    D.boundaryVertex → ℝ :=
  fun b => (D.boundaryBlock.mulVec φ) b + (D.boundaryInteriorBlock.mulVec uI) b

theorem boundaryFlux_eq_boundaryOperator_mulVec
    {D : DirichletLaplacianStrong Cell T}
    (w : InternalInteriorInverse D) (φ : D.boundaryVertex → ℝ) :
    boundaryFlux φ (interiorSolve w φ) =
      (boundaryOperator w).mulVec φ := by
  let rhsI : D.interiorVertex → ℝ := D.interiorBoundaryBlock.mulVec φ
  let wI : D.interiorVertex → ℝ := w.inv.mulVec rhsI
  let M : Matrix D.boundaryVertex D.boundaryVertex ℝ :=
    D.boundaryInteriorBlock * w.inv * D.interiorBoundaryBlock
  funext b
  have hNeg :
      D.boundaryInteriorBlock.mulVec (fun i => - wI i) b =
        - (D.boundaryInteriorBlock.mulVec wI) b := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib, mul_neg]
  have hComp :
      M.mulVec φ b = (D.boundaryInteriorBlock).mulVec wI b := by
    simp [M, wI, rhsI, Matrix.mul_assoc, Matrix.mulVec_mulVec]
  have hNegMat :
      (-M).mulVec φ b = - (M.mulVec φ b) := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib, neg_mul]
  have hInteriorTerm :
      D.boundaryInteriorBlock.mulVec (fun i => - wI i) b = (-M).mulVec φ b := by
    calc
      D.boundaryInteriorBlock.mulVec (fun i => - wI i) b
          = - (D.boundaryInteriorBlock.mulVec wI) b := hNeg
      _ = - (M.mulVec φ b) := by rw [hComp]
      _ = (-M).mulVec φ b := hNegMat.symm
  have hAdd :
      (D.boundaryBlock + (-M)).mulVec φ b =
        D.boundaryBlock.mulVec φ b + (-M).mulVec φ b := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]
  have hw : interiorSolve w φ = fun i => - wI i := by
    funext i
    simp [interiorSolve, wI, rhsI]
  calc
    boundaryFlux φ (interiorSolve w φ) b
        = D.boundaryBlock.mulVec φ b +
            D.boundaryInteriorBlock.mulVec (fun i => - wI i) b := by
              simp [boundaryFlux, hw]
    _ = D.boundaryBlock.mulVec φ b + (-M).mulVec φ b := by
          rw [hInteriorTerm]
    _ = (D.boundaryBlock + (-M)).mulVec φ b := by
          rw [hAdd]
    _ = (boundaryOperator w).mulVec φ b := by
          simp [boundaryOperator, M, sub_eq_add_neg]

theorem interiorBlock_mulVec_interiorSolve
    {D : DirichletLaplacianStrong Cell T}
    (w : InternalInteriorInverse D) (φ : D.boundaryVertex → ℝ) :
    D.interiorBlock.mulVec (interiorSolve w φ) =
      - (D.interiorBoundaryBlock.mulVec φ) := by
  let rhs : D.interiorVertex → ℝ := D.interiorBoundaryBlock.mulVec φ
  have hL : D.interiorBlock * w.inv = 1 :=
    w.inv_ok.left_inv
  have hNeg :
      D.interiorBlock.mulVec (interiorSolve w φ) =
        fun i => - (D.interiorBlock.mulVec (w.inv.mulVec rhs)) i := by
    funext i
    simp [interiorSolve, rhs, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib, mul_neg]
  calc
    D.interiorBlock.mulVec (interiorSolve w φ)
        = fun i => - (D.interiorBlock.mulVec (w.inv.mulVec rhs)) i := hNeg
    _ = fun i => - (((D.interiorBlock) * w.inv).mulVec rhs) i := by
          simp [Matrix.mulVec_mulVec]
    _ = fun i => - rhs i := by
          simp [hL]
    _ = - (D.interiorBoundaryBlock.mulVec φ) := by
          rfl

end InternalInteriorInverse

inductive InteriorEliminationMode where
  | explicitInverse
  | elimination
  | fallback
  deriving DecidableEq, Repr

class InteriorEliminationData
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (D : DirichletLaplacianStrong Cell T) where
  eliminationMode : InteriorEliminationMode
  boundaryOperator : Matrix D.boundaryVertex D.boundaryVertex ℝ
  interiorSolve : (D.boundaryVertex → ℝ) → D.interiorVertex → ℝ
  interiorSolve_spec : ∀ φ : D.boundaryVertex → ℝ,
    D.interiorBlock.mulVec (interiorSolve φ) =
      - (D.interiorBoundaryBlock.mulVec φ)
  boundaryOperator_spec : ∀ φ : D.boundaryVertex → ℝ,
    D.boundaryBlock.mulVec φ +
        D.boundaryInteriorBlock.mulVec (interiorSolve φ) =
      boundaryOperator.mulVec φ

namespace InteriorEliminationData

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

private def ofInternalInverse
    (D : DirichletLaplacianStrong Cell T)
    (w : InternalInteriorInverse D)
    (mode : InteriorEliminationMode := InteriorEliminationMode.explicitInverse) :
    InteriorEliminationData D where
  eliminationMode := mode
  boundaryOperator := InternalInteriorInverse.boundaryOperator w
  interiorSolve := InternalInteriorInverse.interiorSolve w
  interiorSolve_spec := by
    intro φ
    exact InternalInteriorInverse.interiorBlock_mulVec_interiorSolve w φ
  boundaryOperator_spec := by
    intro φ
    funext b
    exact congrArg (fun f => f b)
      (InternalInteriorInverse.boundaryFlux_eq_boundaryOperator_mulVec w φ)

end InteriorEliminationData

structure DtNStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : DirichletLaplacianStrong Cell T
  eliminationMode : InteriorEliminationMode
  boundaryOperator : Matrix source.boundaryVertex source.boundaryVertex ℝ
  interiorSolve : (source.boundaryVertex → ℝ) → source.interiorVertex → ℝ
  interiorSolve_spec : ∀ φ : source.boundaryVertex → ℝ,
    source.interiorBlock.mulVec (interiorSolve φ) =
      - (source.interiorBoundaryBlock.mulVec φ)
  boundaryOperator_spec : ∀ φ : source.boundaryVertex → ℝ,
    source.boundaryBlock.mulVec φ +
        source.boundaryInteriorBlock.mulVec (interiorSolve φ) =
      boundaryOperator.mulVec φ

abbrev DtNStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  DtNStrong (Cell := Cell) T

namespace DtNStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

def ofEliminationData
    (D : DirichletLaplacianStrong Cell T)
    [edata : InteriorEliminationData D] :
    DtNStrong Cell T where
  source := D
  eliminationMode := edata.eliminationMode
  boundaryOperator := edata.boundaryOperator
  interiorSolve := edata.interiorSolve
  interiorSolve_spec := by
    intro φ
    exact edata.interiorSolve_spec φ
  boundaryOperator_spec := by
    intro φ
    exact edata.boundaryOperator_spec φ

def cast (h : T = U) (K : DtNStrong Cell T) : DtNStrong Cell U := by
  cases h
  exact K

theorem cast_rfl (K : DtNStrong Cell T) :
    cast (Cell := Cell) rfl K = K := by
  rfl

abbrev boundaryVertex (K : DtNStrong Cell T) :=
  K.source.boundaryVertex

abbrev interiorVertex (K : DtNStrong Cell T) :=
  K.source.interiorVertex

abbrev boundaryPotential (K : DtNStrong Cell T) :=
  K.boundaryVertex → ℝ

abbrev interiorPotential (K : DtNStrong Cell T) :=
  K.interiorVertex → ℝ

def boundaryFlux (K : DtNStrong Cell T)
    (φ : K.boundaryPotential) (uI : K.interiorPotential) :
    K.boundaryPotential :=
  fun b => (K.source.boundaryBlock.mulVec φ) b + (K.source.boundaryInteriorBlock.mulVec uI) b

theorem boundaryFlux_eq_boundaryOperator_mulVec
    (K : DtNStrong Cell T) (φ : K.boundaryPotential) :
    K.boundaryFlux φ (K.interiorSolve φ) =
      (K.boundaryOperator).mulVec φ := by
  funext b
  have h := K.boundaryOperator_spec φ
  exact congrArg (fun f => f b) h

theorem interiorBlock_mulVec_interiorSolve
    (K : DtNStrong Cell T) (φ : K.boundaryPotential) :
    K.source.interiorBlock.mulVec (K.interiorSolve φ) =
      - (K.source.interiorBoundaryBlock.mulVec φ) := by
  exact K.interiorSolve_spec φ

end DtNStrong

namespace StrengtheningS5

open CNNA.PillarA.Finite.StrengtheningS4
open CNNA.PillarA.Finite.StrengtheningS5

abbrev ReferenceInteriorEliminationData (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :=
  InteriorEliminationData (referenceFullDirichletLaplacian b p wp)

abbrev VariationInteriorEliminationData (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :=
  InteriorEliminationData (variationFullDirichletLaplacian β p wp)

def referenceFullDtN (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    [ReferenceInteriorEliminationData b p wp]
    : DtNStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  DtNStrong.ofEliminationData (referenceFullDirichletLaplacian b p wp)

def variationFullDtN (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy)
    [VariationInteriorEliminationData β p wp]
    : DtNStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  DtNStrong.ofEliminationData (variationFullDirichletLaplacian β p wp)

end StrengtheningS5

end CNNA.PillarA.DtN
