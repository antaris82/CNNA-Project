import CNNA.PillarA.Arithmetic.Schur.CharpolyC
import CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace CayleyDickson

abbrev StructuralCDSource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CNNA.PillarA.Structural.CayleyDickson.CayleyDicksonSource (Cell := Cell) T

inductive AR6aCarrierTransferStatus where
  | arithmeticBoundaryAndCDCarrierKeptSeparateWithSharedSchurProvenance
  deriving DecidableEq, Repr

inductive AR6aEmbeddingTransferStatus where
  | cdCanonicalCarrierEmbeddingsRecordedNoArithmeticEmbeddingClaim
  deriving DecidableEq, Repr

inductive AR6aConjugationTransferStatus where
  | execMirrorStarAndCDCanonicalStarCheckedSeparately
  deriving DecidableEq, Repr

inductive AR6aProductTransferStatus where
  | execMirrorProductAndCDCanonicalProductCheckedSeparately
  deriving DecidableEq, Repr

inductive AR6aNormTransferStatus where
  | execMirrorNormAndCDCanonicalNormCheckedNoScalarIdentity
  deriving DecidableEq, Repr

inductive AR6aNoIdentificationStatus where
  | noExecMirrorCDComplexIdentificationWithoutTransferLemma
  deriving DecidableEq, Repr

inductive AR6aBridgeLedgerStatus where
  | ar6aComplexCouplingTestClosed
  deriving DecidableEq, Repr

structure ExecMirrorScalarTransfer where
  toMirror : ExecComplex → ℂ
  toMirror_eq : toMirror = ExecComplexBridge.toComplex
  map_zero : toMirror 0 = 0
  map_one : toMirror 1 = 1
  map_add : ∀ a b : ExecComplex, toMirror (a + b) = toMirror a + toMirror b
  map_mul : ∀ a b : ExecComplex, toMirror (a * b) = toMirror a * toMirror b
  map_conj : ∀ a : ExecComplex, toMirror (star a) = star (toMirror a)
  map_normSq : ∀ a : ExecComplex,
    Complex.normSq (toMirror a) = (MatrixNorm.Exec.sqNorm a : ℝ)

namespace ExecMirrorScalarTransfer

def closed : ExecMirrorScalarTransfer where
  toMirror := ExecComplexBridge.toComplex
  toMirror_eq := by
    rfl
  map_zero := by
    exact ExecComplexBridge.toComplex_zero
  map_one := by
    exact ExecComplexBridge.toComplex_one
  map_add := by
    intro a b
    exact ExecComplexBridge.toComplex_add a b
  map_mul := by
    intro a b
    exact ExecComplexBridge.toComplex_mul a b
  map_conj := by
    intro a
    exact ExecComplexBridge.toComplex_star a
  map_normSq := by
    intro a
    exact ExecComplexBridge.Mirror.sqNorm_map a

end ExecMirrorScalarTransfer

structure CDCanonicalComplexSurface
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (X : StructuralCDSource Cell T) where
  productCandidate : CNNA.PillarA.Structural.CayleyDickson.CanonicalProductLawCandidate X
  productCandidate_eq :
    productCandidate =
      CNNA.PillarA.Structural.CayleyDickson.canonicalProductLawCandidateClosed X
  multiplication :
    CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X →
      CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X →
      CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X
  multiplication_eq :
    multiplication = CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.mul X
  starMap :
    CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X →
      CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X
  starMap_eq :
    starMap = CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.star X
  normSq :
    CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X → ℝ
  normSq_eq :
    normSq = CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.normSq X
  cd_regularization_split : X.regularization.split = X.carrier.split
  cd_schur_split : X.schur.split = X.carrier.split
  starInvolutive :
    ∀ a : CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X,
      starMap (starMap a) = a
  normSq_nonneg :
    ∀ a : CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X,
      0 ≤ normSq a

namespace CDCanonicalComplexSurface

def fromCDSource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (X : StructuralCDSource Cell T) :
    CDCanonicalComplexSurface X where
  productCandidate :=
    CNNA.PillarA.Structural.CayleyDickson.canonicalProductLawCandidateClosed X
  productCandidate_eq := by
    rfl
  multiplication := CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.mul X
  multiplication_eq := by
    rfl
  starMap := CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.star X
  starMap_eq := by
    rfl
  normSq := CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.normSq X
  normSq_eq := by
    rfl
  cd_regularization_split := X.regularization_split
  cd_schur_split := X.schur_split
  starInvolutive := by
    intro a
    exact CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.star_star X a
  normSq_nonneg := by
    intro a
    exact CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple.normSq_nonneg X a

end CDCanonicalComplexSurface

structure CDComplexArithmeticBridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T)
    (X : StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter) where
  mirrorLedger : Schur.CMirrorCharpolyLedger source L z
  cdSurface : CDCanonicalComplexSurface X
  execMirrorTransfer : ExecMirrorScalarTransfer
  sharedSchur : X.schur = source.multiSchur
  carrierTransferStatus : AR6aCarrierTransferStatus
  carrierTransferStatus_eq :
    carrierTransferStatus =
      AR6aCarrierTransferStatus.arithmeticBoundaryAndCDCarrierKeptSeparateWithSharedSchurProvenance
  embeddingTransferStatus : AR6aEmbeddingTransferStatus
  embeddingTransferStatus_eq :
    embeddingTransferStatus =
      AR6aEmbeddingTransferStatus.cdCanonicalCarrierEmbeddingsRecordedNoArithmeticEmbeddingClaim
  conjugationTransferStatus : AR6aConjugationTransferStatus
  conjugationTransferStatus_eq :
    conjugationTransferStatus =
      AR6aConjugationTransferStatus.execMirrorStarAndCDCanonicalStarCheckedSeparately
  productTransferStatus : AR6aProductTransferStatus
  productTransferStatus_eq :
    productTransferStatus =
      AR6aProductTransferStatus.execMirrorProductAndCDCanonicalProductCheckedSeparately
  normTransferStatus : AR6aNormTransferStatus
  normTransferStatus_eq :
    normTransferStatus =
      AR6aNormTransferStatus.execMirrorNormAndCDCanonicalNormCheckedNoScalarIdentity
  noIdentificationStatus : AR6aNoIdentificationStatus
  noIdentificationStatus_eq :
    noIdentificationStatus =
      AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma
  bridgeStatus : AR6aBridgeLedgerStatus
  bridgeStatus_eq : bridgeStatus = AR6aBridgeLedgerStatus.ar6aComplexCouplingTestClosed
  mirrorNoReverseConsumption :
    mirrorLedger.mirrorProfile.noReverseConsumptionStatus =
      Schur.CMirrorNoReverseConsumptionStatus.execPathDoesNotConsumeMirror
  mirrorParameterSeparation :
    mirrorLedger.mirrorProfile.parameterSeparationStatus =
      Schur.CMirrorParameterSeparationStatus.spectralRatSeparateFromModularQ
  mirrorRoute :
    mirrorLedger.operativeLedger.recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory
  cdRegularizationSplit : X.regularization.split = X.carrier.split
  cdSchurSplit : X.schur.split = X.carrier.split
  cdSchurMatchesArithmeticSource : source.multiSchur = X.schur
  execMulTransfer : ∀ a b : ExecComplex,
    execMirrorTransfer.toMirror (a * b) =
      execMirrorTransfer.toMirror a * execMirrorTransfer.toMirror b
  execConjugationTransfer : ∀ a : ExecComplex,
    execMirrorTransfer.toMirror (star a) = star (execMirrorTransfer.toMirror a)
  execNormTransfer : ∀ a : ExecComplex,
    Complex.normSq (execMirrorTransfer.toMirror a) =
      (MatrixNorm.Exec.sqNorm a : ℝ)
  cdStarTransfer :
    ∀ a : CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X,
      cdSurface.starMap (cdSurface.starMap a) = a
  cdNormNonnegative :
    ∀ a : CNNA.PillarA.Structural.CayleyDickson.CanonicalBlockTuple X,
      0 ≤ cdSurface.normSq a

namespace CDComplexArithmeticBridge

def fromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (X : StructuralCDSource Cell T)
    (z : Schur.SpectralParameter)
    (hSchur : X.schur = source.multiSchur) :
    CDComplexArithmeticBridge source X L z where
  mirrorLedger := Schur.CMirrorCharpolyLedger.fromBoundarySource B z
  cdSurface := CDCanonicalComplexSurface.fromCDSource X
  execMirrorTransfer := ExecMirrorScalarTransfer.closed
  sharedSchur := hSchur
  carrierTransferStatus :=
    AR6aCarrierTransferStatus.arithmeticBoundaryAndCDCarrierKeptSeparateWithSharedSchurProvenance
  carrierTransferStatus_eq := by
    rfl
  embeddingTransferStatus :=
    AR6aEmbeddingTransferStatus.cdCanonicalCarrierEmbeddingsRecordedNoArithmeticEmbeddingClaim
  embeddingTransferStatus_eq := by
    rfl
  conjugationTransferStatus :=
    AR6aConjugationTransferStatus.execMirrorStarAndCDCanonicalStarCheckedSeparately
  conjugationTransferStatus_eq := by
    rfl
  productTransferStatus :=
    AR6aProductTransferStatus.execMirrorProductAndCDCanonicalProductCheckedSeparately
  productTransferStatus_eq := by
    rfl
  normTransferStatus :=
    AR6aNormTransferStatus.execMirrorNormAndCDCanonicalNormCheckedNoScalarIdentity
  normTransferStatus_eq := by
    rfl
  noIdentificationStatus :=
    AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma
  noIdentificationStatus_eq := by
    rfl
  bridgeStatus := AR6aBridgeLedgerStatus.ar6aComplexCouplingTestClosed
  bridgeStatus_eq := by
    rfl
  mirrorNoReverseConsumption := by
    exact Schur.CMirrorCharpolyLedger.no_reverse_consumption
      (Schur.CMirrorCharpolyLedger.fromBoundarySource B z)
  mirrorParameterSeparation := by
    exact Schur.CMirrorCharpolyLedger.parameter_separation
      (Schur.CMirrorCharpolyLedger.fromBoundarySource B z)
  mirrorRoute := by
    exact Schur.CMirrorCharpolyLedger.route_recursiveHistory
      (Schur.CMirrorCharpolyLedger.fromBoundarySource B z)
  cdRegularizationSplit := X.regularization_split
  cdSchurSplit := X.schur_split
  cdSchurMatchesArithmeticSource := by
    exact hSchur.symm
  execMulTransfer := by
    intro a b
    exact ExecMirrorScalarTransfer.closed.map_mul a b
  execConjugationTransfer := by
    intro a
    exact ExecMirrorScalarTransfer.closed.map_conj a
  execNormTransfer := by
    intro a
    exact ExecMirrorScalarTransfer.closed.map_normSq a
  cdStarTransfer := by
    intro a
    exact (CDCanonicalComplexSurface.fromCDSource X).starInvolutive a
  cdNormNonnegative := by
    intro a
    exact (CDCanonicalComplexSurface.fromCDSource X).normSq_nonneg a

theorem status_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {X : StructuralCDSource Cell T}
    {L : Nat} {z : Schur.SpectralParameter}
    (Bdg : CDComplexArithmeticBridge source X L z) :
    Bdg.bridgeStatus = AR6aBridgeLedgerStatus.ar6aComplexCouplingTestClosed :=
  Bdg.bridgeStatus_eq

theorem no_exec_mirror_cd_identification
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {X : StructuralCDSource Cell T}
    {L : Nat} {z : Schur.SpectralParameter}
    (Bdg : CDComplexArithmeticBridge source X L z) :
    Bdg.noIdentificationStatus =
      AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma :=
  Bdg.noIdentificationStatus_eq

theorem shared_schur_provenance
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {X : StructuralCDSource Cell T}
    {L : Nat} {z : Schur.SpectralParameter}
    (Bdg : CDComplexArithmeticBridge source X L z) :
    X.schur = source.multiSchur :=
  Bdg.sharedSchur

end CDComplexArithmeticBridge

end CayleyDickson

namespace StrengtheningAR6a

abbrev AR6aStructuralCDSource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CayleyDickson.StructuralCDSource Cell T

abbrev AR6aCDCanonicalComplexSurface
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (X : AR6aStructuralCDSource Cell T) :=
  CayleyDickson.CDCanonicalComplexSurface X

abbrev AR6aCDComplexArithmeticBridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T)
    (X : AR6aStructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter) :=
  CayleyDickson.CDComplexArithmeticBridge source X L z

def AR6aCDComplexArithmeticBridgeFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (X : AR6aStructuralCDSource Cell T)
    (z : Schur.SpectralParameter)
    (hSchur : X.schur = source.multiSchur) :
    AR6aCDComplexArithmeticBridge source X L z :=
  CayleyDickson.CDComplexArithmeticBridge.fromBoundarySource B X z hSchur

theorem AR6aBridge_status_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {X : AR6aStructuralCDSource Cell T} {z : Schur.SpectralParameter}
    (Bdg : AR6aCDComplexArithmeticBridge source X L z) :
    Bdg.bridgeStatus =
      CayleyDickson.AR6aBridgeLedgerStatus.ar6aComplexCouplingTestClosed :=
  CayleyDickson.CDComplexArithmeticBridge.status_closed Bdg

end StrengtheningAR6a

end CNNA.PillarA.Arithmetic
