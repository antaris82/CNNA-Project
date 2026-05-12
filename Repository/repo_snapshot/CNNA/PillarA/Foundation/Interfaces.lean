import CNNA.PillarA.Foundation.FiniteHilbert
import CNNA.PillarA.Foundation.MatrixAlgebra
import CNNA.PillarA.Foundation.MatrixNorms
import CNNA.PillarA.Foundation.SubstrateClass

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u v w

abbrev LayeredCell (Cell : Nat → Type u) : Type u :=
  Sigma Cell

structure LayerSlice (Cell : Nat → Type u) [SubstrateClass Cell] where
  level : Nat
  carrier : Finset (Cell level)

namespace LayerSlice

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def card (S : LayerSlice Cell) : Nat :=
  S.carrier.card

theorem mem_carrier_mk_iff {L : Nat} {s : Finset (Cell L)} {x : Cell L} :
    x ∈ (LayerSlice.mk L s).carrier ↔ x ∈ s := by
  rfl

def refine (S : LayerSlice Cell) : LayerSlice Cell :=
  { level := S.level + 1
    carrier := SubstrateClass.refineSet (Cell := Cell) S.carrier }

def coarsen (S : LayerSlice Cell) : LayerSlice Cell :=
  match S with
  | ⟨0, carrier⟩ =>
      { level := 0
        carrier := carrier }
  | ⟨L + 1, carrier⟩ =>
      { level := L
        carrier := SubstrateClass.coarsenSet (Cell := Cell) carrier }

theorem refine_level (S : LayerSlice Cell) :
    S.refine.level = S.level + 1 := by
  rfl

theorem refine_carrier (S : LayerSlice Cell) :
    S.refine.carrier = SubstrateClass.refineSet (Cell := Cell) S.carrier := by
  rfl

theorem coarsen_mk_zero_level (s : Finset (Cell 0)) :
    (LayerSlice.mk 0 s).coarsen.level = 0 := by
  rfl

theorem coarsen_mk_zero_carrier (s : Finset (Cell 0)) :
    (LayerSlice.mk 0 s).coarsen.carrier = s := by
  rfl

theorem coarsen_mk_succ_level {L : Nat} (s : Finset (Cell (L + 1))) :
    (LayerSlice.mk (L + 1) s).coarsen.level = L := by
  rfl

theorem coarsen_mk_succ_carrier {L : Nat} (s : Finset (Cell (L + 1))) :
    (LayerSlice.mk (L + 1) s).coarsen.carrier = SubstrateClass.coarsenSet (Cell := Cell) s := by
  rfl

end LayerSlice

structure BoundarySlice (Cell : Nat → Type u) [SubstrateClass Cell]
    extends LayerSlice Cell where
  boundary : Finset (Cell level)
  boundary_subset : boundary ⊆ carrier

namespace BoundarySlice

variable {Cell : Nat → Type u} [SubstrateClass Cell]

theorem mem_carrier_of_mem_boundary (B : BoundarySlice Cell) {x : Cell B.level}
    (hx : x ∈ B.boundary) :
    x ∈ B.carrier := by
  exact B.boundary_subset hx

def boundaryCard (B : BoundarySlice Cell) : Nat :=
  B.boundary.card

theorem boundaryCard_le_carrierCard (B : BoundarySlice Cell) :
    B.boundaryCard ≤ B.toLayerSlice.card := by
  exact Finset.card_le_card B.boundary_subset

end BoundarySlice

class HasLayerSlice (α : Type v) (Cell : Nat → Type u) [SubstrateClass Cell] where
  layerSlice : α → LayerSlice Cell

class HasBoundarySlice (α : Type v) (Cell : Nat → Type u) [SubstrateClass Cell] where
  boundarySlice : α → BoundarySlice Cell

class HasSourceMap (α : Type v) (β : Type w) where
  sourceMap : α → β

class HasRefinement (α : Type v) (β : Type w) where
  refine : α → β

class HasCoarsening (α : Type v) (β : Type w) where
  coarsen : α → β

section LayerSliceInstances

variable {Cell : Nat → Type u} [SubstrateClass Cell]

instance instHasRefinementLayerSlice : HasRefinement (LayerSlice Cell) (LayerSlice Cell) where
  refine := LayerSlice.refine

instance instHasCoarseningLayerSlice : HasCoarsening (LayerSlice Cell) (LayerSlice Cell) where
  coarsen := LayerSlice.coarsen

end LayerSliceInstances

namespace HasLayerSlice

variable {α : Type v} {Cell : Nat → Type u} [SubstrateClass Cell] [HasLayerSlice α Cell]

def slice (a : α) : LayerSlice Cell :=
  HasLayerSlice.layerSlice (α := α) (Cell := Cell) a

theorem slice_level (a : α) :
    (slice (α := α) (Cell := Cell) a).level =
      (HasLayerSlice.layerSlice (α := α) (Cell := Cell) a).level := by
  rfl

theorem slice_carrier (a : α) :
    (slice (α := α) (Cell := Cell) a).carrier =
      (HasLayerSlice.layerSlice (α := α) (Cell := Cell) a).carrier := by
  rfl

end HasLayerSlice

namespace HasBoundarySlice

variable {α : Type v} {Cell : Nat → Type u} [SubstrateClass Cell] [HasBoundarySlice α Cell]

def slice (a : α) : BoundarySlice Cell :=
  HasBoundarySlice.boundarySlice (α := α) (Cell := Cell) a

theorem boundary_subset_carrier (a : α) :
    (slice (α := α) (Cell := Cell) a).boundary ⊆
      (slice (α := α) (Cell := Cell) a).carrier := by
  exact (slice (α := α) (Cell := Cell) a).boundary_subset

theorem mem_carrier_of_mem_boundary (a : α)
    {x : Cell (slice (α := α) (Cell := Cell) a).level}
    (hx : x ∈ (slice (α := α) (Cell := Cell) a).boundary) :
    x ∈ (slice (α := α) (Cell := Cell) a).carrier := by
  exact boundary_subset_carrier (α := α) (Cell := Cell) a hx

end HasBoundarySlice


section AlgebraContracts

abbrev ExecState (ι : Type v) : Type v :=
  FiniteStateSpace ExecComplex ι

abbrev ExecObservable (ι : Type v) : Type v :=
  Observable ExecComplex ι

abbrev ExecMat (ι : Type v) : Type v :=
  MatrixNorm.Exec.ExecMat ι

abbrev ExecHermitian (ι : Type v) [Fintype ι] [DecidableEq ι] : Type v :=
  HermitianMatrix (𝕜 := ExecComplex) (ι := ι)

structure StateContract (𝕜 : Type u) (ι : Type v) where
  Carrier : Type (max u v)
  equivState : Carrier ≃ FiniteStateSpace 𝕜 ι

namespace StateContract

variable {𝕜 : Type u} {ι : Type v}

def toState (C : StateContract 𝕜 ι) : C.Carrier → FiniteStateSpace 𝕜 ι :=
  C.equivState

def ofState (C : StateContract 𝕜 ι) : FiniteStateSpace 𝕜 ι → C.Carrier :=
  C.equivState.symm

theorem left_inv (C : StateContract 𝕜 ι) :
    Function.LeftInverse C.ofState C.toState := by
  intro x
  exact C.equivState.left_inv x

theorem right_inv (C : StateContract 𝕜 ι) :
    Function.RightInverse C.ofState C.toState := by
  intro x
  exact C.equivState.right_inv x

def canonical : StateContract 𝕜 ι where
  Carrier := FiniteStateSpace 𝕜 ι
  equivState := Equiv.refl _

def exec : StateContract ExecComplex ι :=
  canonical

end StateContract

structure StarAlgebraContract (𝕜 : Type u) (ι : Type v) where
  Carrier : Type (max u v)
  equivObservable : Carrier ≃ Observable 𝕜 ι

namespace StarAlgebraContract

variable {𝕜 : Type u} {ι : Type v}

def toObservable (C : StarAlgebraContract 𝕜 ι) : C.Carrier → Observable 𝕜 ι :=
  C.equivObservable

def ofObservable (C : StarAlgebraContract 𝕜 ι) : Observable 𝕜 ι → C.Carrier :=
  C.equivObservable.symm

theorem left_inv (C : StarAlgebraContract 𝕜 ι) :
    Function.LeftInverse C.ofObservable C.toObservable := by
  intro A
  exact C.equivObservable.left_inv A

theorem right_inv (C : StarAlgebraContract 𝕜 ι) :
    Function.RightInverse C.ofObservable C.toObservable := by
  intro A
  exact C.equivObservable.right_inv A

def canonical : StarAlgebraContract 𝕜 ι where
  Carrier := Observable 𝕜 ι
  equivObservable := Equiv.refl _

def exec : StarAlgebraContract ExecComplex ι :=
  canonical

end StarAlgebraContract

structure ExecNormContract (ι : Type v) [Fintype ι] [DecidableEq ι] where
  Carrier : Type v
  equivMatrix : Carrier ≃ ExecMat ι

namespace ExecNormContract

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

def toMatrix (C : ExecNormContract ι) : C.Carrier → ExecMat ι :=
  C.equivMatrix

def ofMatrix (C : ExecNormContract ι) : ExecMat ι → C.Carrier :=
  C.equivMatrix.symm

def frobeniusSq (C : ExecNormContract ι) (A : C.Carrier) : ℚ :=
  MatrixNorm.Exec.frobeniusSq (C.toMatrix A)

def zeroTest (C : ExecNormContract ι) (A : C.Carrier) : Bool :=
  MatrixNorm.Exec.zeroTest (C.toMatrix A)

def shift (C : ExecNormContract ι) (ε : ℚ) (A : C.Carrier) : ℚ :=
  MatrixNorm.Exec.shift ε (C.toMatrix A)

theorem frobeniusSq_nonneg (C : ExecNormContract ι) (A : C.Carrier) :
    0 ≤ C.frobeniusSq A := by
  exact MatrixNorm.Exec.frobeniusSq_nonneg (C.toMatrix A)

theorem zeroTest_eq_true_iff (C : ExecNormContract ι) (A : C.Carrier) :
    C.zeroTest A = true ↔ C.toMatrix A = 0 := by
  exact MatrixNorm.Exec.zeroTest_eq_true_iff (C.toMatrix A)

def canonical : ExecNormContract ι where
  Carrier := ExecMat ι
  equivMatrix := Equiv.refl _

end ExecNormContract

structure PreNet (Region : Type u) (Obj : Type v) where
  fiber : Region → Obj

structure RegionNet (Region : Type u) (Obj : Type v) extends PreNet Region Obj

structure LocalAlgebraNet (Region : Type u) {𝕜 : Type v} {ι : Type w}
    (A : StarAlgebraContract 𝕜 ι) where
  fiber : Region → A.Carrier

structure StateNet (Region : Type u) {𝕜 : Type v} {ι : Type w}
    (S : StateContract 𝕜 ι) where
  fiber : Region → S.Carrier

structure ChannelContract {𝕜 : Type u} {ι : Type v}
    (A : StarAlgebraContract 𝕜 ι) where
  Carrier : Type (max u v)
  equivMap : Carrier ≃ (A.Carrier → A.Carrier)

namespace ChannelContract

variable {𝕜 : Type u} {ι : Type v} {A : StarAlgebraContract 𝕜 ι}

def toMap (C : ChannelContract A) : C.Carrier → (A.Carrier → A.Carrier) :=
  C.equivMap

def ofMap (C : ChannelContract A) : (A.Carrier → A.Carrier) → C.Carrier :=
  C.equivMap.symm

def canonical (A : StarAlgebraContract 𝕜 ι) : ChannelContract A where
  Carrier := A.Carrier → A.Carrier
  equivMap := Equiv.refl _

end ChannelContract

structure ChannelNet (Region : Type u) {𝕜 : Type v} {ι : Type w}
    {A : StarAlgebraContract 𝕜 ι} (C : ChannelContract A) where
  fiber : Region → C.Carrier

end AlgebraContracts

end CNNA.PillarA.Foundation
