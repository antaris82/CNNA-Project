import CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds

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

namespace CoupledSectorKind

def dual : CoupledSectorKind → CoupledSectorKind
  | .bright => .dark
  | .interface => .interface
  | .dark => .bright

theorem dual_bright : dual .bright = .dark := by
  rfl

theorem dual_interface : dual .interface = .interface := by
  rfl

theorem dual_dark : dual .dark = .bright := by
  rfl

theorem dual_involutive (K : CoupledSectorKind) : dual (dual K) = K := by
  cases K <;> rfl

end CoupledSectorKind

namespace PreNumericSectorRole

def toCoupledSectorKind : PreNumericSectorRole → CoupledSectorKind
  | .bright => .bright
  | .interface => .interface
  | .dark => .dark

theorem toCoupledSectorKind_bright :
    toCoupledSectorKind .bright = CoupledSectorKind.bright := by
  rfl

theorem toCoupledSectorKind_interface :
    toCoupledSectorKind .interface = CoupledSectorKind.interface := by
  rfl

theorem toCoupledSectorKind_dark :
    toCoupledSectorKind .dark = CoupledSectorKind.dark := by
  rfl

theorem toCoupledSectorKind_dual (ρ : PreNumericSectorRole) :
    toCoupledSectorKind (dual ρ) =
      CoupledSectorKind.dual (toCoupledSectorKind ρ) := by
  cases ρ <;> rfl

end PreNumericSectorRole

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev RoleBoundaryVertex (X : CayleyDicksonSource Cell T)
    (ρ : PreNumericSectorRole) : Type _ :=
  match ρ with
  | .bright => X.schur.brightBoundaryVertex
  | .interface => X.schur.interfaceBoundaryVertex
  | .dark => X.schur.darkBoundaryVertex

abbrev RoleBoundaryMatrix (X : CayleyDicksonSource Cell T)
    (ρ σ : PreNumericSectorRole) : Type _ :=
  Matrix (RoleBoundaryVertex X ρ) (RoleBoundaryVertex X σ) ℝ

def roleBlock (X : CayleyDicksonSource Cell T)
    (ρ σ : PreNumericSectorRole) :
    RoleBoundaryMatrix X ρ σ := by
  cases ρ <;> cases σ
  · exact X.schur.brightBrightBlock
  · exact X.schur.brightInterfaceBlock
  · exact X.schur.brightDarkBlock
  · exact X.schur.interfaceBrightBlock
  · exact X.schur.interfaceBlock
  · exact X.schur.interfaceDarkBlock
  · exact X.schur.darkBrightBlock
  · exact X.schur.darkInterfaceBlock
  · exact X.schur.darkDarkBlock

theorem roleBlock_bright_bright
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .bright .bright = X.schur.brightBrightBlock := by
  rfl

theorem roleBlock_bright_interface
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .bright .interface = X.schur.brightInterfaceBlock := by
  rfl

theorem roleBlock_bright_dark
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .bright .dark = X.schur.brightDarkBlock := by
  rfl

theorem roleBlock_interface_bright
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .interface .bright = X.schur.interfaceBrightBlock := by
  rfl

theorem roleBlock_interface_interface
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .interface .interface = X.schur.interfaceBlock := by
  rfl

theorem roleBlock_interface_dark
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .interface .dark = X.schur.interfaceDarkBlock := by
  rfl

theorem roleBlock_dark_bright
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .dark .bright = X.schur.darkBrightBlock := by
  rfl

theorem roleBlock_dark_interface
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .dark .interface = X.schur.darkInterfaceBlock := by
  rfl

theorem roleBlock_dark_dark
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .dark .dark = X.schur.darkDarkBlock := by
  rfl

def brightBrightInterfaceMediated (X : CayleyDicksonSource Cell T) :
    Matrix X.schur.brightBoundaryVertex X.schur.brightBoundaryVertex ℝ :=
  X.schur.brightInterfaceBlock * X.schur.interfaceInverse * X.schur.interfaceBrightBlock

def brightDarkInterfaceMediated (X : CayleyDicksonSource Cell T) :
    Matrix X.schur.brightBoundaryVertex X.schur.darkBoundaryVertex ℝ :=
  X.schur.brightInterfaceBlock * X.schur.interfaceInverse * X.schur.interfaceDarkBlock

def darkBrightInterfaceMediated (X : CayleyDicksonSource Cell T) :
    Matrix X.schur.darkBoundaryVertex X.schur.brightBoundaryVertex ℝ :=
  X.schur.darkInterfaceBlock * X.schur.interfaceInverse * X.schur.interfaceBrightBlock

def darkDarkInterfaceMediated (X : CayleyDicksonSource Cell T) :
    Matrix X.schur.darkBoundaryVertex X.schur.darkBoundaryVertex ℝ :=
  X.schur.darkInterfaceBlock * X.schur.interfaceInverse * X.schur.interfaceDarkBlock

theorem interfaceBlock_left_inverse
    (X : CayleyDicksonSource Cell T) :
    roleBlock X .interface .interface * X.schur.interfaceInverse =
      (1 : RoleBoundaryMatrix X .interface .interface) := by
  simpa [roleBlock] using X.schur.interfaceInverse_left_inv

theorem interfaceBlock_right_inverse
    (X : CayleyDicksonSource Cell T) :
    X.schur.interfaceInverse * roleBlock X .interface .interface =
      (1 : RoleBoundaryMatrix X .interface .interface) := by
  simpa [roleBlock] using X.schur.interfaceInverse_right_inv

theorem brightBrightSchur_role_formula
    (X : CayleyDicksonSource Cell T) :
    X.schur.brightBrightSchur =
      roleBlock X .bright .bright - brightBrightInterfaceMediated X := by
  simpa [roleBlock, brightBrightInterfaceMediated] using X.schur.brightBrightSchur_def

theorem brightDarkSchur_role_formula
    (X : CayleyDicksonSource Cell T) :
    X.schur.brightDarkSchur =
      roleBlock X .bright .dark - brightDarkInterfaceMediated X := by
  simpa [roleBlock, brightDarkInterfaceMediated] using X.schur.brightDarkSchur_def

theorem darkBrightSchur_role_formula
    (X : CayleyDicksonSource Cell T) :
    X.schur.darkBrightSchur =
      roleBlock X .dark .bright - darkBrightInterfaceMediated X := by
  simpa [roleBlock, darkBrightInterfaceMediated] using X.schur.darkBrightSchur_def

theorem darkDarkSchur_role_formula
    (X : CayleyDicksonSource Cell T) :
    X.schur.darkDarkSchur =
      roleBlock X .dark .dark - darkDarkInterfaceMediated X := by
  simpa [roleBlock, darkDarkInterfaceMediated] using X.schur.darkDarkSchur_def

structure RoleCompositionSeed
    (X : CayleyDicksonSource Cell T) where
  complex : ComplexCouplingSeed X
  complex_eq : complex = complexCouplingSeedOf X
  interfaceLeftInverse :
    roleBlock X .interface .interface * X.schur.interfaceInverse =
      (1 : RoleBoundaryMatrix X .interface .interface)
  interfaceRightInverse :
    X.schur.interfaceInverse * roleBlock X .interface .interface =
      (1 : RoleBoundaryMatrix X .interface .interface)
  brightBrightFormula :
    X.schur.brightBrightSchur =
      roleBlock X .bright .bright - brightBrightInterfaceMediated X
  brightDarkFormula :
    X.schur.brightDarkSchur =
      roleBlock X .bright .dark - brightDarkInterfaceMediated X
  darkBrightFormula :
    X.schur.darkBrightSchur =
      roleBlock X .dark .bright - darkBrightInterfaceMediated X
  darkDarkFormula :
    X.schur.darkDarkSchur =
      roleBlock X .dark .dark - darkDarkInterfaceMediated X

def roleCompositionSeedOf
    (X : CayleyDicksonSource Cell T) : RoleCompositionSeed X where
  complex := complexCouplingSeedOf X
  complex_eq := rfl
  interfaceLeftInverse := interfaceBlock_left_inverse X
  interfaceRightInverse := interfaceBlock_right_inverse X
  brightBrightFormula := brightBrightSchur_role_formula X
  brightDarkFormula := brightDarkSchur_role_formula X
  darkBrightFormula := darkBrightSchur_role_formula X
  darkDarkFormula := darkDarkSchur_role_formula X

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
