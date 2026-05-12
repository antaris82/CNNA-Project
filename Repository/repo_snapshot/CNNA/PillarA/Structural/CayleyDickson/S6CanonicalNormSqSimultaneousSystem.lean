import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem

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
A single simultaneous Slot-2 reduction object carrying all nine pure block equations
at once. This is the common proof surface for the bright, center, and dark packages.
-/
structure CanonicalNormSqSimultaneousSystem
    (X : CayleyDicksonSource Cell T) where
  left_left_left_left :
    ∀ a b : TriadicOuterBlock X .left .left,
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
        (CanonicalBlockTuple.compose_left_left_left X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b
  left_left_left_right :
    ∀ a : TriadicOuterBlock X .left .left,
      ∀ b : TriadicOuterBlock X .left .right,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex)
          (CanonicalBlockTuple.compose_left_left_right X a b) =
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) b
  left_right_right_left :
    ∀ a : TriadicOuterBlock X .left .right,
      ∀ b : TriadicOuterBlock X .right .left,
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex)
          (CanonicalBlockTuple.compose_left_right_left X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) b
  left_right_right_right :
    ∀ a : TriadicOuterBlock X .left .right,
      ∀ b : TriadicOuterBlock X .right .right,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex)
          (CanonicalBlockTuple.compose_left_right_right X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b
  center_center :
    ∀ a b : TriadicCenterBlock X,
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex)
        (CanonicalBlockTuple.compose_center X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.interfaceBoundaryVertex) b
  right_left_left_left :
    ∀ a : TriadicOuterBlock X .right .left,
      ∀ b : TriadicOuterBlock X .left .left,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex)
          (CanonicalBlockTuple.compose_right_left_left X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSq (ι := X.schur.brightBoundaryVertex) b
  right_left_left_right :
    ∀ a : TriadicOuterBlock X .right .left,
      ∀ b : TriadicOuterBlock X .left .right,
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
          (CanonicalBlockTuple.compose_right_left_right X a b) =
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.brightBoundaryVertex)
          (κ := X.schur.darkBoundaryVertex) b
  right_right_right_left :
    ∀ a : TriadicOuterBlock X .right .right,
      ∀ b : TriadicOuterBlock X .right .left,
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex)
          (CanonicalBlockTuple.compose_right_right_left X a b) =
        MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
        MatrixNorm.Analytic.frobSqRect
          (ι := X.schur.darkBoundaryVertex)
          (κ := X.schur.brightBoundaryVertex) b
  right_right_right_right :
    ∀ a b : TriadicOuterBlock X .right .right,
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex)
        (CanonicalBlockTuple.compose_right_right_right X a b) =
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) a *
      MatrixNorm.Analytic.frobSq (ι := X.schur.darkBoundaryVertex) b

/--
A closed fixed canonical Slot-2 witness forces the full simultaneous block system.
-/
def canonicalNormSqSimultaneousSystemOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqCandidate X) :
    CanonicalNormSqSimultaneousSystem X where
  left_left_left_left :=
    canonicalFixedNormSqCandidate_forces_left_left_left_left X h
  left_left_left_right :=
    canonicalFixedNormSqCandidate_forces_left_left_left_right X h
  left_right_right_left :=
    canonicalFixedNormSqCandidate_forces_left_right_right_left X h
  left_right_right_right :=
    canonicalFixedNormSqCandidate_forces_left_right_right_right X h
  center_center :=
    canonicalFixedNormSqCandidate_forces_center_center X h
  right_left_left_left :=
    canonicalFixedNormSqCandidate_forces_right_left_left_left X h
  right_left_left_right :=
    canonicalFixedNormSqCandidate_forces_right_left_left_right X h
  right_right_right_left :=
    canonicalFixedNormSqCandidate_forces_right_right_right_left X h
  right_right_right_right :=
    canonicalFixedNormSqCandidate_forces_right_right_right_right X h

/--
The simultaneous system projects to the bright-side subsystem.
-/
theorem canonicalNormSqSimultaneousSystem_implies_bright
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqSimultaneousSystem X) :
    CanonicalBrightBlockNormSqSystem X := by
  constructor
  · intro a b
    exact h.left_left_left_left a b
  constructor
  · intro a b
    exact h.left_left_left_right a b
  constructor
  · intro a b
    exact h.left_right_right_left a b
  · intro a b
    exact h.left_right_right_right a b

/--
The simultaneous system projects to the center subsystem.
-/
theorem canonicalNormSqSimultaneousSystem_implies_center
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqSimultaneousSystem X) :
    CanonicalCenterBlockNormSqSystem X := by
  intro a b
  exact h.center_center a b

/--
The simultaneous system projects to the dark-side subsystem.
-/
theorem canonicalNormSqSimultaneousSystem_implies_dark
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqSimultaneousSystem X) :
    CanonicalDarkBlockNormSqSystem X := by
  constructor
  · intro a b
    exact h.right_left_left_left a b
  constructor
  · intro a b
    exact h.right_left_left_right a b
  constructor
  · intro a b
    exact h.right_right_right_left a b
  · intro a b
    exact h.right_right_right_right a b

/--
The simultaneous system packages all three previously separated subsystems at once.
-/
def canonicalNormSqBlockSystemOfSimultaneous
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqSimultaneousSystem X) :
    CanonicalNormSqBlockSystem X where
  bright := canonicalNormSqSimultaneousSystem_implies_bright X h
  center := canonicalNormSqSimultaneousSystem_implies_center X h
  dark := canonicalNormSqSimultaneousSystem_implies_dark X h

/--
Conversely, the previously bundled bright/center/dark system is equivalent to the
single simultaneous nine-equation system.
-/
def canonicalNormSqSimultaneousSystemOfBlockSystem
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqBlockSystem X) :
    CanonicalNormSqSimultaneousSystem X where
  left_left_left_left := h.bright.1
  left_left_left_right := h.bright.2.1
  left_right_right_left := h.bright.2.2.1
  left_right_right_right := h.bright.2.2.2
  center_center := h.center
  right_left_left_left := h.dark.1
  right_left_left_right := h.dark.2.1
  right_right_right_left := h.dark.2.2.1
  right_right_right_right := h.dark.2.2.2

/--
Simultaneous frontier form for the canonical Slot-2 reduction: all nine pure block
consequences are available together on a single object.
-/
def CanonicalNormSqSimultaneousFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (CanonicalNormSqSimultaneousSystem X)

theorem canonicalFixedNormSqFrontier_implies_simultaneousFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalFixedNormSqMultiplicativityFrontier (Cell := Cell) (T := T) X) :
    CanonicalNormSqSimultaneousFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqSimultaneousSystemOf X witness⟩

theorem canonicalDivisionFromNormSqFrontier_implies_simultaneousFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalDivisionFromNormSqFrontier (Cell := Cell) (T := T) X) :
    CanonicalNormSqSimultaneousFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqSimultaneousSystemOf X witness.slot2⟩

theorem canonicalNormSqSimultaneousFrontier_implies_blockSystemFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqSimultaneousFrontier (Cell := Cell) (T := T) X) :
    CanonicalNormSqBlockSystemFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqBlockSystemOfSimultaneous X witness⟩

theorem canonicalNormSqBlockSystemFrontier_implies_simultaneousFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalNormSqBlockSystemFrontier (Cell := Cell) (T := T) X) :
    CanonicalNormSqSimultaneousFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalNormSqSimultaneousSystemOfBlockSystem X witness⟩

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
