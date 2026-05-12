import CNNA.PillarA.ToC.GeneratedBranchFamily

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

inductive SM0GeneratedSourceStatus where
  | scaffoldedFromAR12aBaseline
  deriving DecidableEq, Repr

inductive SM0CutSpecCoreStatus where
  | noCutSpecFullImportedInSmokeCore
  deriving DecidableEq, Repr

inductive SM0CarrierOriginStatus where
  | substrateClassLevelCarrier
  deriving DecidableEq, Repr

inductive SM0MatrixDataStatus where
  | noMatrixDataBeforeSM3EntryLemmas
  deriving DecidableEq, Repr

inductive SM0OldSmokeContinuityStatus where
  | noOldSM1ToSM3dPositiveImport
  deriving DecidableEq, Repr

def regularGeneratedSmokeCarrier (b L : Nat) :
    Finset (ConcreteSubstrate.RegularCell b L) :=
  (regularGeneratedFamily b).carrier L

def variableGeneratedSmokeCarrier (β : Nat → Nat) (L : Nat) :
    Finset (LevelVariableSubstrate.LevelVariableCell β L) :=
  (variableGeneratedFamily β).carrier L

theorem regularGeneratedSmokeCarrier_eq_univ (b L : Nat) :
    regularGeneratedSmokeCarrier b L = Finset.univ := by
  rfl

theorem variableGeneratedSmokeCarrier_eq_univ (β : Nat → Nat) (L : Nat) :
    variableGeneratedSmokeCarrier β L = Finset.univ := by
  rfl

def regularGeneratedSmokeCarrier_nonSingletonAtSucc
    {b L : Nat} (hb : 0 < b) :
    GeneratedBranchFamily.NonSingletonWitness
      (ConcreteSubstrate.RegularCell b) (L + 1) :=
  regularGeneratedFamily_nonSingletonAtSucc (b := b) (L := L) hb

def variableGeneratedSmokeCarrier_nonSingletonAtSucc
    {β : Nat → Nat} {L : Nat} (hβ : 0 < β L) :
    GeneratedBranchFamily.NonSingletonWitness
      (LevelVariableSubstrate.LevelVariableCell β) (L + 1) :=
  variableGeneratedFamily_nonSingletonAtSucc (β := β) (L := L) hβ

structure SM0GeneratedSourceLedger where
  status : SM0GeneratedSourceStatus
  cutSpecCoreStatus : SM0CutSpecCoreStatus
  carrierOriginStatus : SM0CarrierOriginStatus
  matrixDataStatus : SM0MatrixDataStatus
  oldSmokeContinuityStatus : SM0OldSmokeContinuityStatus
  regularCarrier_eq_univ : ∀ b L : Nat,
    regularGeneratedSmokeCarrier b L = Finset.univ
  variableCarrier_eq_univ : ∀ β : Nat → Nat, ∀ L : Nat,
    variableGeneratedSmokeCarrier β L = Finset.univ
  regularNonSingletonAtSucc : ∀ {b L : Nat}, 0 < b →
    GeneratedBranchFamily.NonSingletonWitness
      (ConcreteSubstrate.RegularCell b) (L + 1)
  variableNonSingletonAtSucc : ∀ {β : Nat → Nat} {L : Nat}, 0 < β L →
    GeneratedBranchFamily.NonSingletonWitness
      (LevelVariableSubstrate.LevelVariableCell β) (L + 1)

def sm0GeneratedSourceLedger : SM0GeneratedSourceLedger where
  status := SM0GeneratedSourceStatus.scaffoldedFromAR12aBaseline
  cutSpecCoreStatus := SM0CutSpecCoreStatus.noCutSpecFullImportedInSmokeCore
  carrierOriginStatus := SM0CarrierOriginStatus.substrateClassLevelCarrier
  matrixDataStatus := SM0MatrixDataStatus.noMatrixDataBeforeSM3EntryLemmas
  oldSmokeContinuityStatus := SM0OldSmokeContinuityStatus.noOldSM1ToSM3dPositiveImport
  regularCarrier_eq_univ := regularGeneratedSmokeCarrier_eq_univ
  variableCarrier_eq_univ := variableGeneratedSmokeCarrier_eq_univ
  regularNonSingletonAtSucc := by
    intro b L hb
    exact regularGeneratedSmokeCarrier_nonSingletonAtSucc (b := b) (L := L) hb
  variableNonSingletonAtSucc := by
    intro β L hβ
    exact variableGeneratedSmokeCarrier_nonSingletonAtSucc (β := β) (L := L) hβ

theorem sm0GeneratedSourceLedger_status :
    sm0GeneratedSourceLedger.status =
      SM0GeneratedSourceStatus.scaffoldedFromAR12aBaseline := by
  rfl

theorem sm0GeneratedSourceLedger_cutSpecCoreStatus :
    sm0GeneratedSourceLedger.cutSpecCoreStatus =
      SM0CutSpecCoreStatus.noCutSpecFullImportedInSmokeCore := by
  rfl

theorem sm0GeneratedSourceLedger_carrierOriginStatus :
    sm0GeneratedSourceLedger.carrierOriginStatus =
      SM0CarrierOriginStatus.substrateClassLevelCarrier := by
  rfl

theorem sm0GeneratedSourceLedger_matrixDataStatus :
    sm0GeneratedSourceLedger.matrixDataStatus =
      SM0MatrixDataStatus.noMatrixDataBeforeSM3EntryLemmas := by
  rfl

theorem sm0GeneratedSourceLedger_oldSmokeContinuityStatus :
    sm0GeneratedSourceLedger.oldSmokeContinuityStatus =
      SM0OldSmokeContinuityStatus.noOldSM1ToSM3dPositiveImport := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
