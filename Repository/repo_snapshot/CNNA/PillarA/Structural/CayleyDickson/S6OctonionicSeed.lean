import CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed

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

inductive TriadicRoleIndex where
  | left
  | center
  | right
  deriving DecidableEq

namespace TriadicRoleIndex

def dual : TriadicRoleIndex → TriadicRoleIndex
  | .left => .right
  | .center => .center
  | .right => .left

def toRole : TriadicRoleIndex → PreNumericSectorRole
  | .left => .bright
  | .center => .interface
  | .right => .dark

def ofOuter : ReducedRoleIndex → TriadicRoleIndex
  | .left => .left
  | .right => .right

theorem dual_left : dual .left = .right := by
  rfl

theorem dual_center : dual .center = .center := by
  rfl

theorem dual_right : dual .right = .left := by
  rfl

theorem dual_involutive (τ : TriadicRoleIndex) : dual (dual τ) = τ := by
  cases τ <;> rfl

theorem toRole_left : toRole .left = .bright := by
  rfl

theorem toRole_center : toRole .center = .interface := by
  rfl

theorem toRole_right : toRole .right = .dark := by
  rfl

theorem toRole_dual (τ : TriadicRoleIndex) :
    PreNumericSectorRole.dual (toRole τ) = toRole (dual τ) := by
  cases τ <;> rfl

theorem toRole_ofOuter (κ : ReducedRoleIndex) :
    toRole (ofOuter κ) = ReducedRoleIndex.toRole κ := by
  cases κ <;> rfl

end TriadicRoleIndex

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev TriadicCenterBlock (X : CayleyDicksonSource Cell T) : Type _ :=
  RoleBoundaryMatrix X .interface .interface

def triadicCenterMatrix (X : CayleyDicksonSource Cell T) : TriadicCenterBlock X :=
  roleBlock X .interface .interface

def triadicCenterInverse (X : CayleyDicksonSource Cell T) : TriadicCenterBlock X :=
  X.schur.interfaceInverse

theorem triadicCenter_left_inverse
    (X : CayleyDicksonSource Cell T) :
    triadicCenterMatrix X * triadicCenterInverse X = (1 : TriadicCenterBlock X) := by
  simpa [triadicCenterMatrix, triadicCenterInverse] using interfaceBlock_left_inverse X

theorem triadicCenter_right_inverse
    (X : CayleyDicksonSource Cell T) :
    triadicCenterInverse X * triadicCenterMatrix X = (1 : TriadicCenterBlock X) := by
  simpa [triadicCenterMatrix, triadicCenterInverse] using interfaceBlock_right_inverse X

abbrev TriadicOuterBlock (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : Type _ :=
  ReducedRoleBlock X κ η

def triadicOuterRawBlock (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : TriadicOuterBlock X κ η :=
  reducedRawBlock X κ η

def triadicOuterMediated (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : TriadicOuterBlock X κ η :=
  reducedInterfaceMediated X κ η

def triadicOuterSchur (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : TriadicOuterBlock X κ η :=
  reducedSchurBlock X κ η

theorem triadicOuterRaw_eq_reducedRaw
    (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) :
    triadicOuterRawBlock X κ η = reducedRawBlock X κ η := by
  rfl

theorem triadicOuterMediated_eq_reduced
    (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) :
    triadicOuterMediated X κ η = reducedInterfaceMediated X κ η := by
  rfl

theorem triadicOuterSchur_eq_reduced
    (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) :
    triadicOuterSchur X κ η = reducedSchurBlock X κ η := by
  rfl

theorem triadicOuterSchur_formula
    (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) :
    triadicOuterSchur X κ η =
      triadicOuterRawBlock X κ η - triadicOuterMediated X κ η := by
  simpa [triadicOuterSchur, triadicOuterRawBlock, triadicOuterMediated] using
    reducedSchur_formula X κ η

structure OctonionicSeed
    (X : CayleyDicksonSource Cell T) where
  quaternionic : QuaternionicSeed X
  quaternionic_eq : quaternionic = quaternionicSeedOf X
  triadicDualInvolutive :
    ∀ τ : TriadicRoleIndex,
      TriadicRoleIndex.dual (TriadicRoleIndex.dual τ) = τ
  triadicRoleDualCompatibility :
    ∀ τ : TriadicRoleIndex,
      PreNumericSectorRole.dual (TriadicRoleIndex.toRole τ) =
        TriadicRoleIndex.toRole (TriadicRoleIndex.dual τ)
  outerRoleCompatibility :
    ∀ κ : ReducedRoleIndex,
      TriadicRoleIndex.toRole (TriadicRoleIndex.ofOuter κ) =
        ReducedRoleIndex.toRole κ
  centerFixed :
    TriadicRoleIndex.dual .center = .center
  centerLeftInverse :
    triadicCenterMatrix X * triadicCenterInverse X = (1 : TriadicCenterBlock X)
  centerRightInverse :
    triadicCenterInverse X * triadicCenterMatrix X = (1 : TriadicCenterBlock X)
  outerFormula :
    ∀ κ η : ReducedRoleIndex,
      triadicOuterSchur X κ η =
        triadicOuterRawBlock X κ η - triadicOuterMediated X κ η

def octonionicSeedOf
    (X : CayleyDicksonSource Cell T) : OctonionicSeed X where
  quaternionic := quaternionicSeedOf X
  quaternionic_eq := rfl
  triadicDualInvolutive := TriadicRoleIndex.dual_involutive
  triadicRoleDualCompatibility := TriadicRoleIndex.toRole_dual
  outerRoleCompatibility := TriadicRoleIndex.toRole_ofOuter
  centerFixed := TriadicRoleIndex.dual_center
  centerLeftInverse := triadicCenter_left_inverse X
  centerRightInverse := triadicCenter_right_inverse X
  outerFormula := triadicOuterSchur_formula X

theorem octonionic_status_open
    (X : CayleyDicksonSource Cell T) :
    (statusLedgerOf X).octonionicSeedStatus = SeedStatus.open := by
  rfl

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
