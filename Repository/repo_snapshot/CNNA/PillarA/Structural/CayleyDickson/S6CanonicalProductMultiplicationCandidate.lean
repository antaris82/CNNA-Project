import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate

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

namespace CanonicalBlockTuple

variable (X : CayleyDicksonSource Cell T)

def compose_left_left_left
    (a : RoleBoundaryMatrix X .bright .bright)
    (b : RoleBoundaryMatrix X .bright .bright) :
    RoleBoundaryMatrix X .bright .bright :=
  a * b

def compose_left_left_right
    (a : RoleBoundaryMatrix X .bright .bright)
    (b : RoleBoundaryMatrix X .bright .dark) :
    RoleBoundaryMatrix X .bright .dark :=
  a * b

def compose_left_right_left
    (a : RoleBoundaryMatrix X .bright .dark)
    (b : RoleBoundaryMatrix X .dark .bright) :
    RoleBoundaryMatrix X .bright .bright :=
  a * b

def compose_left_right_right
    (a : RoleBoundaryMatrix X .bright .dark)
    (b : RoleBoundaryMatrix X .dark .dark) :
    RoleBoundaryMatrix X .bright .dark :=
  a * b

def compose_right_left_left
    (a : RoleBoundaryMatrix X .dark .bright)
    (b : RoleBoundaryMatrix X .bright .bright) :
    RoleBoundaryMatrix X .dark .bright :=
  a * b

def compose_right_left_right
    (a : RoleBoundaryMatrix X .dark .bright)
    (b : RoleBoundaryMatrix X .bright .dark) :
    RoleBoundaryMatrix X .dark .dark :=
  a * b

def compose_right_right_left
    (a : RoleBoundaryMatrix X .dark .dark)
    (b : RoleBoundaryMatrix X .dark .bright) :
    RoleBoundaryMatrix X .dark .bright :=
  a * b

def compose_right_right_right
    (a : RoleBoundaryMatrix X .dark .dark)
    (b : RoleBoundaryMatrix X .dark .dark) :
    RoleBoundaryMatrix X .dark .dark :=
  a * b

def compose_center
    (a b : TriadicCenterBlock X) :
    TriadicCenterBlock X :=
  a * b

def outerCompose
    (κ η μ : ReducedRoleIndex) :
    TriadicOuterBlock X κ η →
      TriadicOuterBlock X η μ →
      TriadicOuterBlock X κ μ := by
  cases κ <;> cases η <;> cases μ
  · exact compose_left_left_left X
  · exact compose_left_left_right X
  · exact compose_left_right_left X
  · exact compose_left_right_right X
  · exact compose_right_left_left X
  · exact compose_right_left_right X
  · exact compose_right_right_left X
  · exact compose_right_right_right X

def mul
    (a b : CanonicalBlockTuple X) : CanonicalBlockTuple X where
  leftLeft :=
    compose_left_left_left X a.leftLeft b.leftLeft +
      compose_left_right_left X a.leftRight b.rightLeft
  leftRight :=
    compose_left_left_right X a.leftLeft b.leftRight +
      compose_left_right_right X a.leftRight b.rightRight
  center :=
    compose_center X a.center b.center
  rightLeft :=
    compose_right_left_left X a.rightLeft b.leftLeft +
      compose_right_right_left X a.rightRight b.rightLeft
  rightRight :=
    compose_right_left_right X a.rightLeft b.leftRight +
      compose_right_right_right X a.rightRight b.rightRight

instance : Mul (CanonicalBlockTuple X) where
  mul := mul X

theorem mul_leftLeft
    (a b : CanonicalBlockTuple X) :
    (mul X a b).leftLeft =
      compose_left_left_left X a.leftLeft b.leftLeft +
        compose_left_right_left X a.leftRight b.rightLeft := by
  rfl

theorem mul_leftRight
    (a b : CanonicalBlockTuple X) :
    (mul X a b).leftRight =
      compose_left_left_right X a.leftLeft b.leftRight +
        compose_left_right_right X a.leftRight b.rightRight := by
  rfl

theorem mul_center
    (a b : CanonicalBlockTuple X) :
    (mul X a b).center =
      compose_center X a.center b.center := by
  rfl

theorem mul_rightLeft
    (a b : CanonicalBlockTuple X) :
    (mul X a b).rightLeft =
      compose_right_left_left X a.rightLeft b.leftLeft +
        compose_right_right_left X a.rightRight b.rightLeft := by
  rfl

theorem mul_rightRight
    (a b : CanonicalBlockTuple X) :
    (mul X a b).rightRight =
      compose_right_left_right X a.rightLeft b.leftRight +
        compose_right_right_right X a.rightRight b.rightRight := by
  rfl

theorem mul_assoc_leftLeft
    (a b c : CanonicalBlockTuple X) :
    (mul X (mul X a b) c).leftLeft =
      (mul X a (mul X b c)).leftLeft := by
  simp [mul, compose_left_left_left, compose_left_right_left,
    compose_left_left_right, compose_left_right_right,
    compose_right_left_left, compose_right_right_left,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel_nf

theorem mul_assoc_leftRight
    (a b c : CanonicalBlockTuple X) :
    (mul X (mul X a b) c).leftRight =
      (mul X a (mul X b c)).leftRight := by
  simp [mul, compose_left_left_right, compose_left_right_right,
    compose_left_left_left, compose_left_right_left,
    compose_right_left_right, compose_right_right_right,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel_nf

theorem mul_assoc_center
    (a b c : CanonicalBlockTuple X) :
    (mul X (mul X a b) c).center =
      (mul X a (mul X b c)).center := by
  simp [mul, compose_center, Matrix.mul_assoc]

theorem mul_assoc_rightLeft
    (a b c : CanonicalBlockTuple X) :
    (mul X (mul X a b) c).rightLeft =
      (mul X a (mul X b c)).rightLeft := by
  simp [mul, compose_right_left_left, compose_right_right_left,
    compose_left_left_left, compose_left_right_left,
    compose_right_left_right, compose_right_right_right,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel_nf

theorem mul_assoc_rightRight
    (a b c : CanonicalBlockTuple X) :
    (mul X (mul X a b) c).rightRight =
      (mul X a (mul X b c)).rightRight := by
  simp [mul, compose_right_left_right, compose_right_right_right,
    compose_left_left_right, compose_left_right_right,
    compose_right_left_left, compose_right_right_left,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel_nf

theorem mul_assoc
    (a b c : CanonicalBlockTuple X) :
    mul X (mul X a b) c = mul X a (mul X b c) := by
  refine CanonicalBlockTuple.ext (X := X)
    (mul_assoc_leftLeft X a b c)
    (mul_assoc_leftRight X a b c)
    (mul_assoc_center X a b c)
    (mul_assoc_rightLeft X a b c)
    (mul_assoc_rightRight X a b c)

end CanonicalBlockTuple

/-- Canonical single-carrier product surface obtained from the explicit block formula. -/
def canonicalAlternativeLawProductSurface
    (X : CayleyDicksonSource Cell T) :
    AlternativeLawProductSurface X where
  Carrier := CanonicalBlockTuple X
  mul := CanonicalBlockTuple.mul X

/--
Exact outer-embedding compatibility obligation for the canonical block multiplication.
This is now a sharply formulated proof duty rather than an informal requirement.
-/
def CanonicalOuterEmbeddingCompatibility
    (X : CayleyDicksonSource Cell T) : Prop :=
  ∀ κ η μ : ReducedRoleIndex,
    ∀ a : TriadicOuterBlock X κ η,
      ∀ b : TriadicOuterBlock X η μ,
        CanonicalBlockTuple.mul X
            (CanonicalBlockTuple.embedOuter X κ η a)
            (CanonicalBlockTuple.embedOuter X η μ b) =
          CanonicalBlockTuple.embedOuter X κ μ
            (CanonicalBlockTuple.outerCompose X κ η μ a b)

/--
Exact center-embedding compatibility obligation for the canonical block multiplication.
-/
def CanonicalCenterEmbeddingCompatibility
    (X : CayleyDicksonSource Cell T) : Prop :=
  ∀ a b : TriadicCenterBlock X,
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedCenter X a)
        (CanonicalBlockTuple.embedCenter X b) =
      CanonicalBlockTuple.embedCenter X
        (CanonicalBlockTuple.compose_center X a b)

/--
The remaining honest frontier after fixing the canonical carrier and the canonical
multiplication formula: prove embedding compatibility and the full alternative law.
-/
structure CanonicalProductLawCandidate
    (X : CayleyDicksonSource Cell T) where
  outerEmbeddingCompatibility : CanonicalOuterEmbeddingCompatibility X
  centerEmbeddingCompatibility : CanonicalCenterEmbeddingCompatibility X
  fullAlternativeLaw : FullAlternativeLaw (canonicalAlternativeLawProductSurface X)


private theorem canonicalOuterEmbeddingCompatibility_left_left_left
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .left .left)
    (b : TriadicOuterBlock X .left .left) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .left .left a)
        (CanonicalBlockTuple.embedOuter X .left .left b) =
      CanonicalBlockTuple.embedOuter X .left .left
        (CanonicalBlockTuple.outerCompose X .left .left .left a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_left_left_right
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .left .left)
    (b : TriadicOuterBlock X .left .right) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .left .left a)
        (CanonicalBlockTuple.embedOuter X .left .right b) =
      CanonicalBlockTuple.embedOuter X .left .right
        (CanonicalBlockTuple.outerCompose X .left .left .right a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_left_right_left
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .left .right)
    (b : TriadicOuterBlock X .right .left) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .left .right a)
        (CanonicalBlockTuple.embedOuter X .right .left b) =
      CanonicalBlockTuple.embedOuter X .left .left
        (CanonicalBlockTuple.outerCompose X .left .right .left a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_left_right_right
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .left .right)
    (b : TriadicOuterBlock X .right .right) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .left .right a)
        (CanonicalBlockTuple.embedOuter X .right .right b) =
      CanonicalBlockTuple.embedOuter X .left .right
        (CanonicalBlockTuple.outerCompose X .left .right .right a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_right_left_left
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .right .left)
    (b : TriadicOuterBlock X .left .left) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .right .left a)
        (CanonicalBlockTuple.embedOuter X .left .left b) =
      CanonicalBlockTuple.embedOuter X .right .left
        (CanonicalBlockTuple.outerCompose X .right .left .left a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_right_left_right
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .right .left)
    (b : TriadicOuterBlock X .left .right) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .right .left a)
        (CanonicalBlockTuple.embedOuter X .left .right b) =
      CanonicalBlockTuple.embedOuter X .right .right
        (CanonicalBlockTuple.outerCompose X .right .left .right a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_right_right_left
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .right .right)
    (b : TriadicOuterBlock X .right .left) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .right .right a)
        (CanonicalBlockTuple.embedOuter X .right .left b) =
      CanonicalBlockTuple.embedOuter X .right .left
        (CanonicalBlockTuple.outerCompose X .right .right .left a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

private theorem canonicalOuterEmbeddingCompatibility_right_right_right
    (X : CayleyDicksonSource Cell T)
    (a : TriadicOuterBlock X .right .right)
    (b : TriadicOuterBlock X .right .right) :
    CanonicalBlockTuple.mul X
        (CanonicalBlockTuple.embedOuter X .right .right a)
        (CanonicalBlockTuple.embedOuter X .right .right b) =
      CanonicalBlockTuple.embedOuter X .right .right
        (CanonicalBlockTuple.outerCompose X .right .right .right a b) := by
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.outerCompose,
      CanonicalBlockTuple.embedOuter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_center,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right]

theorem canonicalOuterEmbeddingCompatibility_closed
    (X : CayleyDicksonSource Cell T) :
    CanonicalOuterEmbeddingCompatibility X := by
  intro κ η μ a b
  cases κ <;> cases η <;> cases μ
  · exact canonicalOuterEmbeddingCompatibility_left_left_left X a b
  · exact canonicalOuterEmbeddingCompatibility_left_left_right X a b
  · exact canonicalOuterEmbeddingCompatibility_left_right_left X a b
  · exact canonicalOuterEmbeddingCompatibility_left_right_right X a b
  · exact canonicalOuterEmbeddingCompatibility_right_left_left X a b
  · exact canonicalOuterEmbeddingCompatibility_right_left_right X a b
  · exact canonicalOuterEmbeddingCompatibility_right_right_left X a b
  · exact canonicalOuterEmbeddingCompatibility_right_right_right X a b

theorem canonicalCenterEmbeddingCompatibility_closed
    (X : CayleyDicksonSource Cell T) :
    CanonicalCenterEmbeddingCompatibility X := by
  intro a b
  refine CanonicalBlockTuple.ext (X := X) ?_ ?_ ?_ ?_ ?_ <;>
    simp [CanonicalBlockTuple.mul, CanonicalBlockTuple.embedCenter,
      CanonicalBlockTuple.compose_left_left_left,
      CanonicalBlockTuple.compose_left_left_right,
      CanonicalBlockTuple.compose_left_right_left,
      CanonicalBlockTuple.compose_left_right_right,
      CanonicalBlockTuple.compose_right_left_left,
      CanonicalBlockTuple.compose_right_left_right,
      CanonicalBlockTuple.compose_right_right_left,
      CanonicalBlockTuple.compose_right_right_right,
      CanonicalBlockTuple.compose_center]

theorem canonicalAlternativeLaw_left
    (X : CayleyDicksonSource Cell T) :
    LeftAlternativeLaw (canonicalAlternativeLawProductSurface X) := by
  intro a b
  exact CanonicalBlockTuple.mul_assoc X a a b

theorem canonicalAlternativeLaw_right
    (X : CayleyDicksonSource Cell T) :
    RightAlternativeLaw (canonicalAlternativeLawProductSurface X) := by
  intro a b
  exact CanonicalBlockTuple.mul_assoc X a b b

theorem canonicalAlternativeLaw_full
    (X : CayleyDicksonSource Cell T) :
    FullAlternativeLaw (canonicalAlternativeLawProductSurface X) := by
  exact ⟨canonicalAlternativeLaw_left X, canonicalAlternativeLaw_right X⟩

def canonicalProductLawCandidateClosed
    (X : CayleyDicksonSource Cell T) :
    CanonicalProductLawCandidate X where
  outerEmbeddingCompatibility := canonicalOuterEmbeddingCompatibility_closed X
  centerEmbeddingCompatibility := canonicalCenterEmbeddingCompatibility_closed X
  fullAlternativeLaw := canonicalAlternativeLaw_full X

/--
Once the explicit canonical multiplication is fixed, the global S6 Slot-1 frontier can be
packaged over this specific surface.
-/
def canonicalProductLawBoundaryOf
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalProductLawCandidate X) :
    FullAlternativeLawBoundary X where
  scaffold := alternativeLawScaffoldSeedOf X
  surface := canonicalAlternativeLawProductSurface X
  embedOuter := CanonicalBlockTuple.embedOuter X
  embedCenter := CanonicalBlockTuple.embedCenter X
  outerFormulaCompatibility := CanonicalOuterEmbeddingCompatibility X
  centerInverseCompatibility := CanonicalCenterEmbeddingCompatibility X
  fullAlternativeLaw := h.fullAlternativeLaw

/--
The canonical-product frontier is now a proof-carrying refinement of the former abstract
closure frontier.
-/
def CanonicalProductAlternativeLawFrontier
    (X : CayleyDicksonSource Cell T) : Prop :=
  Nonempty (CanonicalProductLawCandidate X)


theorem canonicalProductAlternativeLawFrontier_closed
    (X : CayleyDicksonSource Cell T) :
    CanonicalProductAlternativeLawFrontier (Cell := Cell) (T := T) X := by
  exact ⟨canonicalProductLawCandidateClosed X⟩

theorem canonicalProductAlternativeLawFrontier_implies_fullAlternativeLawClosureFrontier
    (X : CayleyDicksonSource Cell T)
    (h : CanonicalProductAlternativeLawFrontier (Cell := Cell) (T := T) X) :
    FullAlternativeLawClosureFrontier (Cell := Cell) (T := T) X := by
  rcases h with ⟨witness⟩
  exact ⟨canonicalProductLawBoundaryOf X witness⟩

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
