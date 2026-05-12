import CNNA.PillarA.Arithmetic.Schur.L3Gaussian

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T}

inductive L123IdentityLedgerStatus where
  | ar10L1ToL3IdentitiesClosed
  deriving DecidableEq, Repr

inductive L123MatrixTransportStatus where
  | allLevelsTransportedThroughRecursiveBoundarySource
  deriving DecidableEq, Repr

inductive L123CharpolyNumeratorLedgerStatus where
  | allCharpolyLedgersHaveSchurNumeratorAgreement
  deriving DecidableEq, Repr

inductive L123FactorizationLedgerStatus where
  | l1ScalarL2EisensteinL3GaussianCertified
  deriving DecidableEq, Repr

inductive L123NormDiscriminantLedgerStatus where
  | l1NormL2MinusThreeL3MinusFourCertified
  deriving DecidableEq, Repr

inductive L123TheoremOnlyLedgerStatus where
  | noNewArithmeticDataNoUncheckedProseValues
  deriving DecidableEq, Repr

inductive L123DownstreamDisciplineStatus where
  | laterPhasesMayConsumeOnlyTheoremFields
  deriving DecidableEq, Repr

structure L123IdentityLedger
    (B1 : BoundarySource.BoundarySourceSurface source L1Level)
    (B2 : BoundarySource.BoundarySourceSurface source L2Level)
    (B3 : BoundarySource.BoundarySourceSurface source L3Level)
    (b k2 k3 : Nat) where
  l1Ledger : L1BaselineLedger B1 b
  l1Ledger_eq : l1Ledger = L1BaselineLedger.fromBoundarySource B1 b
  l2Ledger : L2EisensteinLedger B2 k2
  l2Ledger_eq : l2Ledger = L2EisensteinLedger.fromBoundarySource B2 k2
  l3Ledger : L3GaussianLedger B3 k3
  l3Ledger_eq : l3Ledger = L3GaussianLedger.fromBoundarySource B3 k3
  identityStatus : L123IdentityLedgerStatus
  identityStatus_eq : identityStatus = L123IdentityLedgerStatus.ar10L1ToL3IdentitiesClosed
  matrixTransportStatus : L123MatrixTransportStatus
  matrixTransportStatus_eq :
    matrixTransportStatus =
      L123MatrixTransportStatus.allLevelsTransportedThroughRecursiveBoundarySource
  charpolyNumeratorStatus : L123CharpolyNumeratorLedgerStatus
  charpolyNumeratorStatus_eq :
    charpolyNumeratorStatus =
      L123CharpolyNumeratorLedgerStatus.allCharpolyLedgersHaveSchurNumeratorAgreement
  factorizationStatus : L123FactorizationLedgerStatus
  factorizationStatus_eq :
    factorizationStatus =
      L123FactorizationLedgerStatus.l1ScalarL2EisensteinL3GaussianCertified
  normDiscriminantStatus : L123NormDiscriminantLedgerStatus
  normDiscriminantStatus_eq :
    normDiscriminantStatus =
      L123NormDiscriminantLedgerStatus.l1NormL2MinusThreeL3MinusFourCertified
  theoremOnlyStatus : L123TheoremOnlyLedgerStatus
  theoremOnlyStatus_eq :
    theoremOnlyStatus =
      L123TheoremOnlyLedgerStatus.noNewArithmeticDataNoUncheckedProseValues
  downstreamDisciplineStatus : L123DownstreamDisciplineStatus
  downstreamDisciplineStatus_eq :
    downstreamDisciplineStatus =
      L123DownstreamDisciplineStatus.laterPhasesMayConsumeOnlyTheoremFields
  l1Route : B1.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  l2Route : B2.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  l3Route : B3.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  l1RecurrenceClosed :
    l1Ledger.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  l2RecurrenceClosed :
    l2Ledger.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  l3RecurrenceClosed :
    l3Ledger.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  l1CharpolyClosed :
    l1Ledger.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  l2CharpolyClosed :
    l2Ledger.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  l3CharpolyClosed :
    l3Ledger.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  l1CharpolyNumerator :
    l1Ledger.charpolyLedger.profile.numeratorStatus =
      CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator
  l2CharpolyNumerator :
    l2Ledger.charpolyLedger.profile.numeratorStatus =
      CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator
  l3CharpolyNumerator :
    l3Ledger.charpolyLedger.profile.numeratorStatus =
      CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator
  l1NoFreeAssumptions :
    l1Ledger.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  l2NoFreeAssumptions :
    l2Ledger.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  l3NoFreeAssumptions :
    l3Ledger.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  l1ScalarDeterminantEqNormform :
    operativeDeterminant l1Ledger.scalarControlMatrix = l1BranchingNorm b
  l1ScalarCharpolyRoot :
    operativeCharpolyEvaluation l1Ledger.scalarControlMatrix (l1BaselineSpectralRoot b) = 0
  l1NormformRe : l1Ledger.normform.re = l1BranchingRat b
  l1NormformIm : l1Ledger.normform.im = 0
  l1SignalDiscipline :
    l1Ledger.signalDisciplineStatus =
      L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1
  l2FactorizationClosed :
    l2Ledger.factorizationStatus =
      L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified
  l2NormformClosed :
    l2Ledger.normformStatus = L2EisensteinNormformStatus.eisensteinNormformCertified
  l2DiscriminantMinusThree :
    l2Ledger.discriminantStatus =
      L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree
  l2OrderSeedClosed :
    l2Ledger.orderStatus = L2EisensteinOrderStatus.eisensteinOrderSeedCertified
  l2CMSeedClosed :
    l2Ledger.cmSeedStatus = L2EisensteinCMSeedStatus.rhoSeedCertified
  l2NoShortcut :
    l2Ledger.noShortcutStatus =
      L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion
  l3FactorizationClosed :
    l3Ledger.factorizationStatus =
      L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified
  l3NormformClosed :
    l3Ledger.normformStatus = L3GaussianNormformStatus.gaussianNormformCertified
  l3DiscriminantMinusFour :
    l3Ledger.discriminantStatus =
      L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour
  l3OrderSeedClosed :
    l3Ledger.orderStatus = L3GaussianOrderStatus.gaussianOrderSeedCertified
  l3CMSeedClosed :
    l3Ledger.cmSeedStatus = L3GaussianCMSeedStatus.iSeedCertified
  l3NoShortcut :
    l3Ledger.noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion
  l1NoCutSpecCarrierClaim :
    BoundarySource.LevelHistoryIndex L1Level →
      source.toc.approximant source.concretePolicy = T
  l2NoCutSpecCarrierClaim :
    BoundarySource.LevelHistoryIndex L2Level →
      source.toc.approximant source.concretePolicy = T
  l3NoCutSpecCarrierClaim :
    BoundarySource.LevelHistoryIndex L3Level →
      source.toc.approximant source.concretePolicy = T

namespace L123IdentityLedger

variable {B1 : BoundarySource.BoundarySourceSurface source L1Level}
variable {B2 : BoundarySource.BoundarySourceSurface source L2Level}
variable {B3 : BoundarySource.BoundarySourceSurface source L3Level}
variable {b k2 k3 : Nat}

def fromBoundarySources
    (B1 : BoundarySource.BoundarySourceSurface source L1Level)
    (B2 : BoundarySource.BoundarySourceSurface source L2Level)
    (B3 : BoundarySource.BoundarySourceSurface source L3Level)
    (b k2 k3 : Nat) :
    L123IdentityLedger B1 B2 B3 b k2 k3 :=
  let l1 := L1BaselineLedger.fromBoundarySource B1 b
  let l2 := L2EisensteinLedger.fromBoundarySource B2 k2
  let l3 := L3GaussianLedger.fromBoundarySource B3 k3
  {
    l1Ledger := l1
    l1Ledger_eq := by
      rfl
    l2Ledger := l2
    l2Ledger_eq := by
      rfl
    l3Ledger := l3
    l3Ledger_eq := by
      rfl
    identityStatus := L123IdentityLedgerStatus.ar10L1ToL3IdentitiesClosed
    identityStatus_eq := by
      rfl
    matrixTransportStatus :=
      L123MatrixTransportStatus.allLevelsTransportedThroughRecursiveBoundarySource
    matrixTransportStatus_eq := by
      rfl
    charpolyNumeratorStatus :=
      L123CharpolyNumeratorLedgerStatus.allCharpolyLedgersHaveSchurNumeratorAgreement
    charpolyNumeratorStatus_eq := by
      rfl
    factorizationStatus :=
      L123FactorizationLedgerStatus.l1ScalarL2EisensteinL3GaussianCertified
    factorizationStatus_eq := by
      rfl
    normDiscriminantStatus :=
      L123NormDiscriminantLedgerStatus.l1NormL2MinusThreeL3MinusFourCertified
    normDiscriminantStatus_eq := by
      rfl
    theoremOnlyStatus :=
      L123TheoremOnlyLedgerStatus.noNewArithmeticDataNoUncheckedProseValues
    theoremOnlyStatus_eq := by
      rfl
    downstreamDisciplineStatus :=
      L123DownstreamDisciplineStatus.laterPhasesMayConsumeOnlyTheoremFields
    downstreamDisciplineStatus_eq := by
      rfl
    l1Route := l1.route
    l2Route := l2.route
    l3Route := l3.route
    l1RecurrenceClosed := l1.recurrenceClosed
    l2RecurrenceClosed := l2.recurrenceClosed
    l3RecurrenceClosed := l3.recurrenceClosed
    l1CharpolyClosed := l1.charpolyClosed
    l2CharpolyClosed := l2.charpolyClosed
    l3CharpolyClosed := l3.charpolyClosed
    l1CharpolyNumerator := l1.charpolyLedger.profile.numeratorStatus_eq
    l2CharpolyNumerator := l2.charpolyLedger.profile.numeratorStatus_eq
    l3CharpolyNumerator := l3.charpolyLedger.profile.numeratorStatus_eq
    l1NoFreeAssumptions := l1.charpolyNoFreeAssumptions
    l2NoFreeAssumptions := l2.charpolyNoFreeAssumptions
    l3NoFreeAssumptions := l3.charpolyNoFreeAssumptions
    l1ScalarDeterminantEqNormform := l1.scalarDeterminant_eq_normform
    l1ScalarCharpolyRoot := l1.scalarCharpolyRoot
    l1NormformRe := l1.normform_re
    l1NormformIm := l1.normform_im
    l1SignalDiscipline := l1.signalDisciplineStatus_eq
    l2FactorizationClosed := l2.factorizationStatus_eq
    l2NormformClosed := l2.normformStatus_eq
    l2DiscriminantMinusThree := l2.discriminantStatus_eq
    l2OrderSeedClosed := l2.orderStatus_eq
    l2CMSeedClosed := l2.cmSeedStatus_eq
    l2NoShortcut := l2.noShortcutStatus_eq
    l3FactorizationClosed := l3.factorizationStatus_eq
    l3NormformClosed := l3.normformStatus_eq
    l3DiscriminantMinusFour := l3.discriminantStatus_eq
    l3OrderSeedClosed := l3.orderStatus_eq
    l3CMSeedClosed := l3.cmSeedStatus_eq
    l3NoShortcut := l3.noShortcutStatus_eq
    l1NoCutSpecCarrierClaim := l1.noCutSpecCarrierClaim
    l2NoCutSpecCarrierClaim := l2.noCutSpecCarrierClaim
    l3NoCutSpecCarrierClaim := l3.noCutSpecCarrierClaim
  }

theorem identity_status_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.identityStatus = L123IdentityLedgerStatus.ar10L1ToL3IdentitiesClosed :=
  Ldg.identityStatus_eq

theorem theorem_only_status
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.theoremOnlyStatus =
      L123TheoremOnlyLedgerStatus.noNewArithmeticDataNoUncheckedProseValues :=
  Ldg.theoremOnlyStatus_eq

theorem downstream_discipline_status
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.downstreamDisciplineStatus =
      L123DownstreamDisciplineStatus.laterPhasesMayConsumeOnlyTheoremFields :=
  Ldg.downstreamDisciplineStatus_eq

theorem matrix_transport_status
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.matrixTransportStatus =
      L123MatrixTransportStatus.allLevelsTransportedThroughRecursiveBoundarySource :=
  Ldg.matrixTransportStatus_eq

theorem charpoly_numerator_status
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.charpolyNumeratorStatus =
      L123CharpolyNumeratorLedgerStatus.allCharpolyLedgersHaveSchurNumeratorAgreement :=
  Ldg.charpolyNumeratorStatus_eq

theorem factorization_status
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.factorizationStatus =
      L123FactorizationLedgerStatus.l1ScalarL2EisensteinL3GaussianCertified :=
  Ldg.factorizationStatus_eq

theorem norm_discriminant_status
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.normDiscriminantStatus =
      L123NormDiscriminantLedgerStatus.l1NormL2MinusThreeL3MinusFourCertified :=
  Ldg.normDiscriminantStatus_eq

theorem all_routes_recursiveHistory
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    B1.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory ∧
      B2.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory ∧
        B3.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory := by
  constructor
  · exact Ldg.l1Route
  · constructor
    · exact Ldg.l2Route
    · exact Ldg.l3Route

theorem all_recurrences_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.recurrenceLedger.recurrenceStatus =
        SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed ∧
      Ldg.l2Ledger.recurrenceLedger.recurrenceStatus =
        SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed ∧
        Ldg.l3Ledger.recurrenceLedger.recurrenceStatus =
          SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed := by
  constructor
  · exact Ldg.l1RecurrenceClosed
  · constructor
    · exact Ldg.l2RecurrenceClosed
    · exact Ldg.l3RecurrenceClosed

theorem all_charpolys_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.charpolyLedger.profile.computationStatus =
        OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed ∧
      Ldg.l2Ledger.charpolyLedger.profile.computationStatus =
        OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed ∧
        Ldg.l3Ledger.charpolyLedger.profile.computationStatus =
          OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed := by
  constructor
  · exact Ldg.l1CharpolyClosed
  · constructor
    · exact Ldg.l2CharpolyClosed
    · exact Ldg.l3CharpolyClosed

theorem all_charpoly_schur_numerators_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.charpolyLedger.profile.numeratorStatus =
        CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator ∧
      Ldg.l2Ledger.charpolyLedger.profile.numeratorStatus =
        CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator ∧
        Ldg.l3Ledger.charpolyLedger.profile.numeratorStatus =
          CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator := by
  constructor
  · exact Ldg.l1CharpolyNumerator
  · constructor
    · exact Ldg.l2CharpolyNumerator
    · exact Ldg.l3CharpolyNumerator

theorem all_no_free_charpoly_assumptions
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.charpolyLedger.profile.noFreeAssumptionStatus =
        AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption ∧
      Ldg.l2Ledger.charpolyLedger.profile.noFreeAssumptionStatus =
        AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption ∧
        Ldg.l3Ledger.charpolyLedger.profile.noFreeAssumptionStatus =
          AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption := by
  constructor
  · exact Ldg.l1NoFreeAssumptions
  · constructor
    · exact Ldg.l2NoFreeAssumptions
    · exact Ldg.l3NoFreeAssumptions

theorem l1_scalar_identity_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    operativeDeterminant Ldg.l1Ledger.scalarControlMatrix = l1BranchingNorm b ∧
      operativeCharpolyEvaluation Ldg.l1Ledger.scalarControlMatrix
          (l1BaselineSpectralRoot b) = 0 := by
  constructor
  · exact Ldg.l1ScalarDeterminantEqNormform
  · exact Ldg.l1ScalarCharpolyRoot

theorem l2_eisenstein_identities_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l2Ledger.factorizationStatus =
        L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified ∧
      Ldg.l2Ledger.normformStatus = L2EisensteinNormformStatus.eisensteinNormformCertified ∧
        Ldg.l2Ledger.discriminantStatus =
          L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree ∧
          Ldg.l2Ledger.cmSeedStatus = L2EisensteinCMSeedStatus.rhoSeedCertified := by
  constructor
  · exact Ldg.l2FactorizationClosed
  · constructor
    · exact Ldg.l2NormformClosed
    · constructor
      · exact Ldg.l2DiscriminantMinusThree
      · exact Ldg.l2CMSeedClosed

theorem l3_gaussian_identities_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l3Ledger.factorizationStatus =
        L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified ∧
      Ldg.l3Ledger.normformStatus = L3GaussianNormformStatus.gaussianNormformCertified ∧
        Ldg.l3Ledger.discriminantStatus =
          L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour ∧
          Ldg.l3Ledger.cmSeedStatus = L3GaussianCMSeedStatus.iSeedCertified := by
  constructor
  · exact Ldg.l3FactorizationClosed
  · constructor
    · exact Ldg.l3NormformClosed
    · constructor
      · exact Ldg.l3DiscriminantMinusFour
      · exact Ldg.l3CMSeedClosed

theorem no_shortcuts_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.signalDisciplineStatus =
        L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1 ∧
      Ldg.l2Ledger.noShortcutStatus =
        L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion ∧
        Ldg.l3Ledger.noShortcutStatus =
          L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion := by
  constructor
  · exact Ldg.l1SignalDiscipline
  · constructor
    · exact Ldg.l2NoShortcut
    · exact Ldg.l3NoShortcut

theorem noCutSpecCarrierClaims_closed
    (Ldg : L123IdentityLedger B1 B2 B3 b k2 k3) :
    (BoundarySource.LevelHistoryIndex L1Level →
        source.toc.approximant source.concretePolicy = T) ∧
      (BoundarySource.LevelHistoryIndex L2Level →
        source.toc.approximant source.concretePolicy = T) ∧
        (BoundarySource.LevelHistoryIndex L3Level →
          source.toc.approximant source.concretePolicy = T) := by
  constructor
  · intro j
    exact Ldg.l1NoCutSpecCarrierClaim j
  · constructor
    · intro j
      exact Ldg.l2NoCutSpecCarrierClaim j
    · intro j
      exact Ldg.l3NoCutSpecCarrierClaim j

end L123IdentityLedger

end Schur

namespace StrengtheningAR10

abbrev AR10L123IdentityLedgerStatus := Schur.L123IdentityLedgerStatus
abbrev AR10L123MatrixTransportStatus := Schur.L123MatrixTransportStatus
abbrev AR10L123CharpolyNumeratorLedgerStatus :=
  Schur.L123CharpolyNumeratorLedgerStatus
abbrev AR10L123FactorizationLedgerStatus := Schur.L123FactorizationLedgerStatus
abbrev AR10L123NormDiscriminantLedgerStatus := Schur.L123NormDiscriminantLedgerStatus
abbrev AR10L123TheoremOnlyLedgerStatus := Schur.L123TheoremOnlyLedgerStatus
abbrev AR10L123DownstreamDisciplineStatus := Schur.L123DownstreamDisciplineStatus

abbrev AR10L123IdentityLedger
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level)
    (B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level)
    (B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level)
    (b k2 k3 : Nat) :=
  Schur.L123IdentityLedger B1 B2 B3 b k2 k3

def AR10L123IdentityLedgerFromBoundarySources
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level)
    (B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level)
    (B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level)
    (b k2 k3 : Nat) :
    AR10L123IdentityLedger B1 B2 B3 b k2 k3 :=
  Schur.L123IdentityLedger.fromBoundarySources B1 B2 B3 b k2 k3

theorem AR10L123IdentityLedger_identity_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {b k2 k3 : Nat}
    (Ldg : AR10L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.identityStatus = Schur.L123IdentityLedgerStatus.ar10L1ToL3IdentitiesClosed :=
  Schur.L123IdentityLedger.identity_status_closed Ldg

theorem AR10L123IdentityLedger_theorem_only
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {b k2 k3 : Nat}
    (Ldg : AR10L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.theoremOnlyStatus =
      Schur.L123TheoremOnlyLedgerStatus.noNewArithmeticDataNoUncheckedProseValues :=
  Schur.L123IdentityLedger.theorem_only_status Ldg

theorem AR10L123IdentityLedger_all_charpolys_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {b k2 k3 : Nat}
    (Ldg : AR10L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.charpolyLedger.profile.computationStatus =
        Schur.OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed ∧
      Ldg.l2Ledger.charpolyLedger.profile.computationStatus =
        Schur.OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed ∧
        Ldg.l3Ledger.charpolyLedger.profile.computationStatus =
          Schur.OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  Schur.L123IdentityLedger.all_charpolys_closed Ldg

theorem AR10L123IdentityLedger_l2_l3_discriminants_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {b k2 k3 : Nat}
    (Ldg : AR10L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l2Ledger.discriminantStatus =
        Schur.L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree ∧
      Ldg.l3Ledger.discriminantStatus =
        Schur.L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour := by
  constructor
  · exact Ldg.l2DiscriminantMinusThree
  · exact Ldg.l3DiscriminantMinusFour

theorem AR10L123IdentityLedger_no_shortcuts_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B1 : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {B2 : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {B3 : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {b k2 k3 : Nat}
    (Ldg : AR10L123IdentityLedger B1 B2 B3 b k2 k3) :
    Ldg.l1Ledger.signalDisciplineStatus =
        Schur.L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1 ∧
      Ldg.l2Ledger.noShortcutStatus =
        Schur.L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion ∧
        Ldg.l3Ledger.noShortcutStatus =
          Schur.L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion :=
  Schur.L123IdentityLedger.no_shortcuts_closed Ldg

end StrengtheningAR10

end CNNA.PillarA.Arithmetic
