import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction
import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

/--
Necessary bright-side block equations forced by multiplicativity of the fixed
canonical norm on the fixed canonical product.
-/
def CanonicalBrightBlockNormSqSystem
    (X : CayleyDicksonSource Cell T) : Prop :=
  (∀ a b : TriadicOuterBlock X .left .left,
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
        (CanonicalBlockTuple.compose_left_left_left X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b) ∧
  (∀ a : TriadicOuterBlock X .left .left,
      ∀ b : TriadicOuterBlock X .left .right,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex)
          (CanonicalBlockTuple.compose_left_left_right X a b) =
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) b) ∧
  (∀ a : TriadicOuterBlock X .left .right,
      ∀ b : TriadicOuterBlock X .right .left,
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
          (CanonicalBlockTuple.compose_left_right_left X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) b) ∧
  (∀ a : TriadicOuterBlock X .left .right,
      ∀ b : TriadicOuterBlock X .right .right,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex)
          (CanonicalBlockTuple.compose_left_right_right X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b)

/-- Necessary center block equation forced by canonical Slot-2 closure. -/
def CanonicalCenterBlockNormSqSystem
    (X : CayleyDicksonSource Cell T) : Prop :=
  ∀ a b : TriadicCenterBlock X,
    MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex)
      (CanonicalBlockTuple.compose_center X a b) =
    MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) a *
    MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) b

/--
Necessary dark-side block equations forced by multiplicativity of the fixed
canonical norm on the fixed canonical product.
-/
def CanonicalDarkBlockNormSqSystem
    (X : CayleyDicksonSource Cell T) : Prop :=
  (∀ a : TriadicOuterBlock X .right .left,
      ∀ b : TriadicOuterBlock X .left .left,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex)
          (CanonicalBlockTuple.compose_right_left_left X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b) ∧
  (∀ a : TriadicOuterBlock X .right .left,
      ∀ b : TriadicOuterBlock X .left .right,
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
          (CanonicalBlockTuple.compose_right_left_right X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) b) ∧
  (∀ a : TriadicOuterBlock X .right .right,
      ∀ b : TriadicOuterBlock X .right .left,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex)
          (CanonicalBlockTuple.compose_right_right_left X a b) =
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) b) ∧
  (∀ a b : TriadicOuterBlock X .right .right,
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
        (CanonicalBlockTuple.compose_right_right_right X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b)

/--
Bundled necessary block system for the fixed canonical Slot-2 norm/product pair.
Any genuine canonical Slot-2 closure must satisfy these three subsystems.
-/
structure CanonicalNormSqBlockSystem
    (X : CayleyDicksonSource Cell T) where
  bright : CanonicalBrightBlockNormSqSystem X
  center : CanonicalCenterBlockNormSqSystem X
  dark : CanonicalDarkBlockNormSqSystem X

/--
Canonical Slot-2 multiplicativity implies the full bright-side block system.
-/
theorem canonicalFixedNormSqCandidate_implies_brightBlockSystem
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    CanonicalBrightBlockNormSqSystem X := by
  constructor
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_left_left_left_left X h a b
  constructor
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_left_left_left_right X h a b
  constructor
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_left_right_right_left X h a b
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_left_right_right_right X h a b

/--
Canonical Slot-2 multiplicativity implies the center block equation.
-/
theorem canonicalFixedNormSqCandidate_implies_centerBlockSystem
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    CanonicalCenterBlockNormSqSystem X := by
  intro a b
  exact canonicalFixedNormSqCandidate_forces_center_center X h a b

/--
Canonical Slot-2 multiplicativity implies the full dark-side block system.
-/
theorem canonicalFixedNormSqCandidate_implies_darkBlockSystem
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    CanonicalDarkBlockNormSqSystem X := by
  constructor
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_right_left_left_left X h a b
  constructor
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_right_left_left_right X h a b
  constructor
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_right_right_right_left X h a b
  · intro a b
    exact canonicalFixedNormSqCandidate_forces_right_right_right_right X h a b

/--
Bundled consequence: a closed fixed canonical Slot-2 witness carries the whole block system.
-/
def canonicalNormSqBlockSystemOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    CanonicalNormSqBlockSystem X where
  bright := canonicalFixedNormSqCandidate_implies_brightBlockSystem X h
  center := canonicalFixedNormSqCandidate_implies_centerBlockSystem X h
  dark := canonicalFixedNormSqCandidate_implies_darkBlockSystem X h

/--
Frontier form: any canonical Slot-2 closure forces the bundled block system.
-/
def CanonicalNormSqBlockSystemFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (CanonicalNormSqBlockSystem X)

theorem canonicalFixedNormSqFrontier_implies_blockSystemFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqMultiplicativityFrontier (Cell := Cell) (T := T) X) :
    CanonicalNormSqBlockSystemFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqBlockSystemOf X witness⟩

theorem canonicalDivisionFromNormSqFrontier_implies_blockSystemFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    CanonicalNormSqBlockSystemFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqBlockSystemOf X witness.slot2⟩

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
