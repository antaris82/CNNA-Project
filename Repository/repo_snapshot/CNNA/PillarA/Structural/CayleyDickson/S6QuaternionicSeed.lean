import CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed

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

inductive ReducedRoleIndex where
  | left
  | right
  deriving DecidableEq

namespace ReducedRoleIndex

def dual : ReducedRoleIndex → ReducedRoleIndex
  | .left => .right
  | .right => .left

def toRole : ReducedRoleIndex → PreNumericSectorRole
  | .left => .bright
  | .right => .dark

theorem dual_left : dual .left = .right := by
  rfl

theorem dual_right : dual .right = .left := by
  rfl

theorem dual_involutive (κ : ReducedRoleIndex) : dual (dual κ) = κ := by
  cases κ <;> rfl

theorem toRole_left : toRole .left = .bright := by
  rfl

theorem toRole_right : toRole .right = .dark := by
  rfl

theorem toRole_dual (κ : ReducedRoleIndex) :
    PreNumericSectorRole.dual (toRole κ) = toRole (dual κ) := by
  cases κ <;> rfl

end ReducedRoleIndex

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev ReducedRoleBlock (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : Type _ :=
  RoleBoundaryMatrix X (ReducedRoleIndex.toRole κ) (ReducedRoleIndex.toRole η)

def reducedRawBlock (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : ReducedRoleBlock X κ η := by
  cases κ <;> cases η
  · exact roleBlock X .bright .bright
  · exact roleBlock X .bright .dark
  · exact roleBlock X .dark .bright
  · exact roleBlock X .dark .dark

def reducedSchurBlock (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : ReducedRoleBlock X κ η := by
  cases κ <;> cases η
  · exact X.schur.brightBrightSchur
  · exact X.schur.brightDarkSchur
  · exact X.schur.darkBrightSchur
  · exact X.schur.darkDarkSchur

def reducedInterfaceMediated (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) : ReducedRoleBlock X κ η := by
  cases κ <;> cases η
  · exact brightBrightInterfaceMediated X
  · exact brightDarkInterfaceMediated X
  · exact darkBrightInterfaceMediated X
  · exact darkDarkInterfaceMediated X

theorem reducedSchurBlock_left_left
    (X : CayleyDicksonSource Cell T) :
    reducedSchurBlock X .left .left = X.schur.brightBrightSchur := by
  rfl

theorem reducedSchurBlock_left_right
    (X : CayleyDicksonSource Cell T) :
    reducedSchurBlock X .left .right = X.schur.brightDarkSchur := by
  rfl

theorem reducedSchurBlock_right_left
    (X : CayleyDicksonSource Cell T) :
    reducedSchurBlock X .right .left = X.schur.darkBrightSchur := by
  rfl

theorem reducedSchurBlock_right_right
    (X : CayleyDicksonSource Cell T) :
    reducedSchurBlock X .right .right = X.schur.darkDarkSchur := by
  rfl

theorem reducedInterfaceMediated_left_left
    (X : CayleyDicksonSource Cell T) :
    reducedInterfaceMediated X .left .left = brightBrightInterfaceMediated X := by
  rfl

theorem reducedInterfaceMediated_left_right
    (X : CayleyDicksonSource Cell T) :
    reducedInterfaceMediated X .left .right = brightDarkInterfaceMediated X := by
  rfl

theorem reducedInterfaceMediated_right_left
    (X : CayleyDicksonSource Cell T) :
    reducedInterfaceMediated X .right .left = darkBrightInterfaceMediated X := by
  rfl

theorem reducedInterfaceMediated_right_right
    (X : CayleyDicksonSource Cell T) :
    reducedInterfaceMediated X .right .right = darkDarkInterfaceMediated X := by
  rfl

theorem reducedRawBlock_left_left
    (X : CayleyDicksonSource Cell T) :
    reducedRawBlock X .left .left = roleBlock X .bright .bright := by
  rfl

theorem reducedRawBlock_left_right
    (X : CayleyDicksonSource Cell T) :
    reducedRawBlock X .left .right = roleBlock X .bright .dark := by
  rfl

theorem reducedRawBlock_right_left
    (X : CayleyDicksonSource Cell T) :
    reducedRawBlock X .right .left = roleBlock X .dark .bright := by
  rfl

theorem reducedRawBlock_right_right
    (X : CayleyDicksonSource Cell T) :
    reducedRawBlock X .right .right = roleBlock X .dark .dark := by
  rfl

theorem reducedSchur_formula
    (X : CayleyDicksonSource Cell T)
    (κ η : ReducedRoleIndex) :
    reducedSchurBlock X κ η =
      reducedRawBlock X κ η - reducedInterfaceMediated X κ η := by
  cases κ <;> cases η
  · simpa [reducedSchurBlock, reducedRawBlock, reducedInterfaceMediated] using
      brightBrightSchur_role_formula X
  · simpa [reducedSchurBlock, reducedRawBlock, reducedInterfaceMediated] using
      brightDarkSchur_role_formula X
  · simpa [reducedSchurBlock, reducedRawBlock, reducedInterfaceMediated] using
      darkBrightSchur_role_formula X
  · simpa [reducedSchurBlock, reducedRawBlock, reducedInterfaceMediated] using
      darkDarkSchur_role_formula X

structure QuaternionicSeed
    (X : CayleyDicksonSource Cell T) where
  role : RoleCompositionSeed X
  role_eq : role = roleCompositionSeedOf X
  reducedDualInvolutive :
    ∀ κ : ReducedRoleIndex,
      ReducedRoleIndex.dual (ReducedRoleIndex.dual κ) = κ
  reducedRoleDualCompatibility :
    ∀ κ : ReducedRoleIndex,
      PreNumericSectorRole.dual (ReducedRoleIndex.toRole κ) =
        ReducedRoleIndex.toRole (ReducedRoleIndex.dual κ)
  leftLeftFormula :
    reducedSchurBlock X .left .left =
      reducedRawBlock X .left .left - reducedInterfaceMediated X .left .left
  leftRightFormula :
    reducedSchurBlock X .left .right =
      reducedRawBlock X .left .right - reducedInterfaceMediated X .left .right
  rightLeftFormula :
    reducedSchurBlock X .right .left =
      reducedRawBlock X .right .left - reducedInterfaceMediated X .right .left
  rightRightFormula :
    reducedSchurBlock X .right .right =
      reducedRawBlock X .right .right - reducedInterfaceMediated X .right .right

def quaternionicSeedOf
    (X : CayleyDicksonSource Cell T) : QuaternionicSeed X where
  role := roleCompositionSeedOf X
  role_eq := rfl
  reducedDualInvolutive := ReducedRoleIndex.dual_involutive
  reducedRoleDualCompatibility := ReducedRoleIndex.toRole_dual
  leftLeftFormula := by
    exact reducedSchur_formula X .left .left
  leftRightFormula := by
    exact reducedSchur_formula X .left .right
  rightLeftFormula := by
    exact reducedSchur_formula X .right .left
  rightRightFormula := by
    exact reducedSchur_formula X .right .right

theorem quaternionic_status_open
    (X : CayleyDicksonSource Cell T) :
    (statusLedgerOf X).quaternionicSeedStatus = SeedStatus.open := by
  rfl

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
