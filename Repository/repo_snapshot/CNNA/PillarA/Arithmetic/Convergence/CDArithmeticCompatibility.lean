import CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge
import CNNA.PillarA.Arithmetic.Orders.NormForms

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Convergence

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

inductive AR12aDiscriminantAlgebraClassification where
  | gaussianDMinusFourCompatibility
  | eisensteinDMinusThreeCompatibility
  | imaginaryQuadraticOrderCompatibility
  | higherDegreeOrIrreducibleCDCObstruction
  deriving DecidableEq, Repr

inductive AR12aQuadraticOrderCDEqualityStatus where
  | quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  deriving DecidableEq, Repr

inductive AR12aScalarComparisonStatus where
  | scalarDataComparedOnlyThroughExplicitTransfer
  deriving DecidableEq, Repr

inductive AR12aNormComparisonStatus where
  | normAndNormFormDataComparedOnlyThroughCertificates
  deriving DecidableEq, Repr

inductive AR12aConjugationComparisonStatus where
  | conjugationDataKeptSeparateUntilTransferLemma
  deriving DecidableEq, Repr

inductive AR12aFormComparisonStatus where
  | quadraticFormDataComparedNoAlgebraIdentification
  deriving DecidableEq, Repr

inductive AR12aPeriodLatticePreparationStatus where
  | ar13PeriodLatticePreparationOnly
  | blockedForNonQuadraticOutcome
  deriving DecidableEq, Repr

inductive AR12aDownstreamDisciplineStatus where
  | noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  deriving DecidableEq, Repr

inductive AR12aDerivedOnlyStatus where
  | ar12OrdersAndAR6aCDDataOnly
  deriving DecidableEq, Repr

inductive AR12aCDCObstructionStatus where
  | nonQuadraticOutcomeBlockedFromCDComplexIdentification
  deriving DecidableEq, Repr

structure ImaginaryQuadraticDiscriminantWitness
    (Q : Orders.QuadraticNormFormCertificate) where
  discriminant : ℤ
  discriminant_eq_normDiscriminant : discriminant = Q.normDiscriminant
  negative : discriminant < 0

namespace ImaginaryQuadraticDiscriminantWitness

def gaussian : ImaginaryQuadraticDiscriminantWitness Orders.QuadraticNormFormCertificate.gaussian where
  discriminant := -4
  discriminant_eq_normDiscriminant := by
    rfl
  negative := by
    decide

def eisenstein : ImaginaryQuadraticDiscriminantWitness Orders.QuadraticNormFormCertificate.eisenstein where
  discriminant := -3
  discriminant_eq_normDiscriminant := by
    rfl
  negative := by
    decide

theorem discriminant_matches_norm
    {Q : Orders.QuadraticNormFormCertificate}
    (W : ImaginaryQuadraticDiscriminantWitness Q) :
    W.discriminant = Q.normDiscriminant :=
  W.discriminant_eq_normDiscriminant

end ImaginaryQuadraticDiscriminantWitness

structure QuadraticOrderCDCompatibilitySurface
    (X : CayleyDickson.StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter)
    (Q : Orders.QuadraticNormFormCertificate) where
  bridge : CayleyDickson.CDComplexArithmeticBridge source X L z
  discriminantWitness : ImaginaryQuadraticDiscriminantWitness Q
  orderDiscriminant_eq_normDiscriminant :
    Q.orderCertificate.order.discriminant = Q.normDiscriminant
  classification : AR12aDiscriminantAlgebraClassification
  classification_eq :
    classification = AR12aDiscriminantAlgebraClassification.imaginaryQuadraticOrderCompatibility ∨
      classification = AR12aDiscriminantAlgebraClassification.gaussianDMinusFourCompatibility ∨
        classification = AR12aDiscriminantAlgebraClassification.eisensteinDMinusThreeCompatibility
  noOrderCDEqualityStatus : AR12aQuadraticOrderCDEqualityStatus
  noOrderCDEqualityStatus_eq :
    noOrderCDEqualityStatus =
      AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  scalarComparisonStatus : AR12aScalarComparisonStatus
  scalarComparisonStatus_eq :
    scalarComparisonStatus =
      AR12aScalarComparisonStatus.scalarDataComparedOnlyThroughExplicitTransfer
  normComparisonStatus : AR12aNormComparisonStatus
  normComparisonStatus_eq :
    normComparisonStatus =
      AR12aNormComparisonStatus.normAndNormFormDataComparedOnlyThroughCertificates
  conjugationComparisonStatus : AR12aConjugationComparisonStatus
  conjugationComparisonStatus_eq :
    conjugationComparisonStatus =
      AR12aConjugationComparisonStatus.conjugationDataKeptSeparateUntilTransferLemma
  formComparisonStatus : AR12aFormComparisonStatus
  formComparisonStatus_eq :
    formComparisonStatus =
      AR12aFormComparisonStatus.quadraticFormDataComparedNoAlgebraIdentification
  periodLatticePreparationStatus : AR12aPeriodLatticePreparationStatus
  periodLatticePreparationStatus_eq :
    periodLatticePreparationStatus =
      AR12aPeriodLatticePreparationStatus.ar13PeriodLatticePreparationOnly
  downstreamDisciplineStatus : AR12aDownstreamDisciplineStatus
  downstreamDisciplineStatus_eq :
    downstreamDisciplineStatus =
      AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  derivedOnlyStatus : AR12aDerivedOnlyStatus
  derivedOnlyStatus_eq :
    derivedOnlyStatus = AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  cdBridgeClosed :
    bridge.bridgeStatus = CayleyDickson.AR6aBridgeLedgerStatus.ar6aComplexCouplingTestClosed
  cdNoIdentification :
    bridge.noIdentificationStatus =
      CayleyDickson.AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma
  cdSharedSchur : X.schur = source.multiSchur
  schurDiscriminantBridge :
    Q.bridge.schurDiscriminant =
      ((Q.bridge.conductor * Q.bridge.conductor : Nat) : ℤ) * Q.bridge.fundamentalDiscriminant
  noIrreduciblePrimeShortcut :
    Q.irreduciblePrimeDisciplineStatus =
      Orders.IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD

namespace QuadraticOrderCDCompatibilitySurface

variable {X : CayleyDickson.StructuralCDSource Cell T}
variable {z : Schur.SpectralParameter}

def fromImaginaryQuadratic
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z)
    (Q : Orders.QuadraticNormFormCertificate)
    (W : ImaginaryQuadraticDiscriminantWitness Q)
    (hOrderNorm : Q.orderCertificate.order.discriminant = Q.normDiscriminant) :
    QuadraticOrderCDCompatibilitySurface (source := source) X L z Q where
  bridge := Bdg
  discriminantWitness := W
  orderDiscriminant_eq_normDiscriminant := hOrderNorm
  classification := AR12aDiscriminantAlgebraClassification.imaginaryQuadraticOrderCompatibility
  classification_eq := Or.inl rfl
  noOrderCDEqualityStatus :=
    AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  noOrderCDEqualityStatus_eq := by
    rfl
  scalarComparisonStatus := AR12aScalarComparisonStatus.scalarDataComparedOnlyThroughExplicitTransfer
  scalarComparisonStatus_eq := by
    rfl
  normComparisonStatus := AR12aNormComparisonStatus.normAndNormFormDataComparedOnlyThroughCertificates
  normComparisonStatus_eq := by
    rfl
  conjugationComparisonStatus :=
    AR12aConjugationComparisonStatus.conjugationDataKeptSeparateUntilTransferLemma
  conjugationComparisonStatus_eq := by
    rfl
  formComparisonStatus := AR12aFormComparisonStatus.quadraticFormDataComparedNoAlgebraIdentification
  formComparisonStatus_eq := by
    rfl
  periodLatticePreparationStatus := AR12aPeriodLatticePreparationStatus.ar13PeriodLatticePreparationOnly
  periodLatticePreparationStatus_eq := by
    rfl
  downstreamDisciplineStatus :=
    AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  downstreamDisciplineStatus_eq := by
    rfl
  derivedOnlyStatus := AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  derivedOnlyStatus_eq := by
    rfl
  cdBridgeClosed := CayleyDickson.CDComplexArithmeticBridge.status_closed Bdg
  cdNoIdentification := CayleyDickson.CDComplexArithmeticBridge.no_exec_mirror_cd_identification Bdg
  cdSharedSchur := CayleyDickson.CDComplexArithmeticBridge.shared_schur_provenance Bdg
  schurDiscriminantBridge := Orders.QuadraticNormFormCertificate.schur_to_fundamental_bridge Q
  noIrreduciblePrimeShortcut := Orders.QuadraticNormFormCertificate.no_irreducible_prime_shortcut Q

def gaussian
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    QuadraticOrderCDCompatibilitySurface (source := source) X L z Orders.QuadraticNormFormCertificate.gaussian where
  bridge := Bdg
  discriminantWitness := ImaginaryQuadraticDiscriminantWitness.gaussian
  orderDiscriminant_eq_normDiscriminant := by
    rfl
  classification := AR12aDiscriminantAlgebraClassification.gaussianDMinusFourCompatibility
  classification_eq := Or.inr (Or.inl rfl)
  noOrderCDEqualityStatus :=
    AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  noOrderCDEqualityStatus_eq := by
    rfl
  scalarComparisonStatus := AR12aScalarComparisonStatus.scalarDataComparedOnlyThroughExplicitTransfer
  scalarComparisonStatus_eq := by
    rfl
  normComparisonStatus := AR12aNormComparisonStatus.normAndNormFormDataComparedOnlyThroughCertificates
  normComparisonStatus_eq := by
    rfl
  conjugationComparisonStatus :=
    AR12aConjugationComparisonStatus.conjugationDataKeptSeparateUntilTransferLemma
  conjugationComparisonStatus_eq := by
    rfl
  formComparisonStatus := AR12aFormComparisonStatus.quadraticFormDataComparedNoAlgebraIdentification
  formComparisonStatus_eq := by
    rfl
  periodLatticePreparationStatus := AR12aPeriodLatticePreparationStatus.ar13PeriodLatticePreparationOnly
  periodLatticePreparationStatus_eq := by
    rfl
  downstreamDisciplineStatus :=
    AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  downstreamDisciplineStatus_eq := by
    rfl
  derivedOnlyStatus := AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  derivedOnlyStatus_eq := by
    rfl
  cdBridgeClosed := CayleyDickson.CDComplexArithmeticBridge.status_closed Bdg
  cdNoIdentification := CayleyDickson.CDComplexArithmeticBridge.no_exec_mirror_cd_identification Bdg
  cdSharedSchur := CayleyDickson.CDComplexArithmeticBridge.shared_schur_provenance Bdg
  schurDiscriminantBridge :=
    Orders.QuadraticNormFormCertificate.schur_to_fundamental_bridge
      Orders.QuadraticNormFormCertificate.gaussian
  noIrreduciblePrimeShortcut :=
    Orders.QuadraticNormFormCertificate.no_irreducible_prime_shortcut
      Orders.QuadraticNormFormCertificate.gaussian

def eisenstein
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    QuadraticOrderCDCompatibilitySurface (source := source) X L z Orders.QuadraticNormFormCertificate.eisenstein where
  bridge := Bdg
  discriminantWitness := ImaginaryQuadraticDiscriminantWitness.eisenstein
  orderDiscriminant_eq_normDiscriminant := by
    rfl
  classification := AR12aDiscriminantAlgebraClassification.eisensteinDMinusThreeCompatibility
  classification_eq := Or.inr (Or.inr rfl)
  noOrderCDEqualityStatus :=
    AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  noOrderCDEqualityStatus_eq := by
    rfl
  scalarComparisonStatus := AR12aScalarComparisonStatus.scalarDataComparedOnlyThroughExplicitTransfer
  scalarComparisonStatus_eq := by
    rfl
  normComparisonStatus := AR12aNormComparisonStatus.normAndNormFormDataComparedOnlyThroughCertificates
  normComparisonStatus_eq := by
    rfl
  conjugationComparisonStatus :=
    AR12aConjugationComparisonStatus.conjugationDataKeptSeparateUntilTransferLemma
  conjugationComparisonStatus_eq := by
    rfl
  formComparisonStatus := AR12aFormComparisonStatus.quadraticFormDataComparedNoAlgebraIdentification
  formComparisonStatus_eq := by
    rfl
  periodLatticePreparationStatus := AR12aPeriodLatticePreparationStatus.ar13PeriodLatticePreparationOnly
  periodLatticePreparationStatus_eq := by
    rfl
  downstreamDisciplineStatus :=
    AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  downstreamDisciplineStatus_eq := by
    rfl
  derivedOnlyStatus := AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  derivedOnlyStatus_eq := by
    rfl
  cdBridgeClosed := CayleyDickson.CDComplexArithmeticBridge.status_closed Bdg
  cdNoIdentification := CayleyDickson.CDComplexArithmeticBridge.no_exec_mirror_cd_identification Bdg
  cdSharedSchur := CayleyDickson.CDComplexArithmeticBridge.shared_schur_provenance Bdg
  schurDiscriminantBridge :=
    Orders.QuadraticNormFormCertificate.schur_to_fundamental_bridge
      Orders.QuadraticNormFormCertificate.eisenstein
  noIrreduciblePrimeShortcut :=
    Orders.QuadraticNormFormCertificate.no_irreducible_prime_shortcut
      Orders.QuadraticNormFormCertificate.eisenstein

def gaussianFromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (X : CayleyDickson.StructuralCDSource Cell T)
    (z : Schur.SpectralParameter)
    (hSchur : X.schur = source.multiSchur) :
    QuadraticOrderCDCompatibilitySurface (source := source) X L z Orders.QuadraticNormFormCertificate.gaussian :=
  gaussian (source := source) (CayleyDickson.CDComplexArithmeticBridge.fromBoundarySource (source := source) B X z hSchur)

def eisensteinFromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (X : CayleyDickson.StructuralCDSource Cell T)
    (z : Schur.SpectralParameter)
    (hSchur : X.schur = source.multiSchur) :
    QuadraticOrderCDCompatibilitySurface (source := source) X L z Orders.QuadraticNormFormCertificate.eisenstein :=
  eisenstein (source := source) (CayleyDickson.CDComplexArithmeticBridge.fromBoundarySource (source := source) B X z hSchur)

theorem no_order_cd_equality
    {Q : Orders.QuadraticNormFormCertificate}
    (S : QuadraticOrderCDCompatibilitySurface (source := source) X L z Q) :
    S.noOrderCDEqualityStatus =
      AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra :=
  S.noOrderCDEqualityStatus_eq

theorem period_lattice_preparation_only
    {Q : Orders.QuadraticNormFormCertificate}
    (S : QuadraticOrderCDCompatibilitySurface (source := source) X L z Q) :
    S.periodLatticePreparationStatus =
      AR12aPeriodLatticePreparationStatus.ar13PeriodLatticePreparationOnly :=
  S.periodLatticePreparationStatus_eq

theorem no_downstream_shortcut
    {Q : Orders.QuadraticNormFormCertificate}
    (S : QuadraticOrderCDCompatibilitySurface (source := source) X L z Q) :
    S.downstreamDisciplineStatus =
      AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15 :=
  S.downstreamDisciplineStatus_eq

theorem cd_no_identification
    {Q : Orders.QuadraticNormFormCertificate}
    (S : QuadraticOrderCDCompatibilitySurface (source := source) X L z Q) :
    S.bridge.noIdentificationStatus =
      CayleyDickson.AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma :=
  S.cdNoIdentification

theorem gaussian_classification
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    (gaussian (source := source) Bdg).classification =
      AR12aDiscriminantAlgebraClassification.gaussianDMinusFourCompatibility := by
  rfl

theorem eisenstein_classification
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    (eisenstein (source := source) Bdg).classification =
      AR12aDiscriminantAlgebraClassification.eisensteinDMinusThreeCompatibility := by
  rfl

theorem gaussian_discriminant_is_negative_four
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    (gaussian (source := source) Bdg).discriminantWitness.discriminant = -4 := by
  rfl

theorem eisenstein_discriminant_is_negative_three
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    (eisenstein (source := source) Bdg).discriminantWitness.discriminant = -3 := by
  rfl

end QuadraticOrderCDCompatibilitySurface

structure NonQuadraticCDComplexObstruction
    (X : CayleyDickson.StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter) where
  bridge : CayleyDickson.CDComplexArithmeticBridge source X L z
  block : Orders.NonQuadraticDiscriminantBlock
  classification : AR12aDiscriminantAlgebraClassification
  classification_eq :
    classification =
      AR12aDiscriminantAlgebraClassification.higherDegreeOrIrreducibleCDCObstruction
  obstructionStatus : AR12aCDCObstructionStatus
  obstructionStatus_eq :
    obstructionStatus =
      AR12aCDCObstructionStatus.nonQuadraticOutcomeBlockedFromCDComplexIdentification
  forwardingBlocked :
    block.forwardingStatus = Orders.NonQuadraticForwardingStatus.blockedFromQuadraticOrderPath
  periodLatticePreparationStatus : AR12aPeriodLatticePreparationStatus
  periodLatticePreparationStatus_eq :
    periodLatticePreparationStatus = AR12aPeriodLatticePreparationStatus.blockedForNonQuadraticOutcome
  downstreamDisciplineStatus : AR12aDownstreamDisciplineStatus
  downstreamDisciplineStatus_eq :
    downstreamDisciplineStatus =
      AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  derivedOnlyStatus : AR12aDerivedOnlyStatus
  derivedOnlyStatus_eq :
    derivedOnlyStatus = AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  cdBridgeClosed :
    bridge.bridgeStatus = CayleyDickson.AR6aBridgeLedgerStatus.ar6aComplexCouplingTestClosed
  cdNoIdentification :
    bridge.noIdentificationStatus =
      CayleyDickson.AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma
  cdSharedSchur : X.schur = source.multiSchur

namespace NonQuadraticCDComplexObstruction

variable {X : CayleyDickson.StructuralCDSource Cell T}
variable {z : Schur.SpectralParameter}

def fromBlock
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z)
    (N : Orders.NonQuadraticDiscriminantBlock) :
    NonQuadraticCDComplexObstruction (source := source) X L z where
  bridge := Bdg
  block := N
  classification :=
    AR12aDiscriminantAlgebraClassification.higherDegreeOrIrreducibleCDCObstruction
  classification_eq := by
    rfl
  obstructionStatus :=
    AR12aCDCObstructionStatus.nonQuadraticOutcomeBlockedFromCDComplexIdentification
  obstructionStatus_eq := by
    rfl
  forwardingBlocked := Orders.NonQuadraticDiscriminantBlock.blocked N
  periodLatticePreparationStatus := AR12aPeriodLatticePreparationStatus.blockedForNonQuadraticOutcome
  periodLatticePreparationStatus_eq := by
    rfl
  downstreamDisciplineStatus :=
    AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  downstreamDisciplineStatus_eq := by
    rfl
  derivedOnlyStatus := AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  derivedOnlyStatus_eq := by
    rfl
  cdBridgeClosed := CayleyDickson.CDComplexArithmeticBridge.status_closed Bdg
  cdNoIdentification := CayleyDickson.CDComplexArithmeticBridge.no_exec_mirror_cd_identification Bdg
  cdSharedSchur := CayleyDickson.CDComplexArithmeticBridge.shared_schur_provenance Bdg

def fromAR11Certificate
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z)
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L}
    (C : Schur.HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    NonQuadraticCDComplexObstruction (source := source) X L z :=
  fromBlock (source := source) Bdg (Orders.NonQuadraticDiscriminantBlock.fromAR11 C)

def fromBoundarySourceAndAR11Certificate
    (B : BoundarySource.BoundarySourceSurface source L)
    (X : CayleyDickson.StructuralCDSource Cell T)
    (z : Schur.SpectralParameter)
    (hSchur : X.schur = source.multiSchur)
    {b : Nat} {hL : 3 < L}
    (C : Schur.HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    NonQuadraticCDComplexObstruction (source := source) X L z :=
  fromAR11Certificate (source := source)
    (CayleyDickson.CDComplexArithmeticBridge.fromBoundarySource (source := source) B X z hSchur) C

theorem classification_obstruction
    (O : NonQuadraticCDComplexObstruction (source := source) X L z) :
    O.classification =
      AR12aDiscriminantAlgebraClassification.higherDegreeOrIrreducibleCDCObstruction :=
  O.classification_eq

theorem forwarding_blocked
    (O : NonQuadraticCDComplexObstruction (source := source) X L z) :
    O.block.forwardingStatus = Orders.NonQuadraticForwardingStatus.blockedFromQuadraticOrderPath :=
  O.forwardingBlocked

theorem period_lattice_blocked
    (O : NonQuadraticCDComplexObstruction (source := source) X L z) :
    O.periodLatticePreparationStatus = AR12aPeriodLatticePreparationStatus.blockedForNonQuadraticOutcome :=
  O.periodLatticePreparationStatus_eq

theorem no_downstream_shortcut
    (O : NonQuadraticCDComplexObstruction (source := source) X L z) :
    O.downstreamDisciplineStatus =
      AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15 :=
  O.downstreamDisciplineStatus_eq

end NonQuadraticCDComplexObstruction

structure CDArithmeticCompatibility
    (X : CayleyDickson.StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter) where
  bridge : CayleyDickson.CDComplexArithmeticBridge source X L z
  orderCertificate : Option Orders.QuadraticOrderConventionCertificate
  normFormCertificate : Option Orders.QuadraticNormFormCertificate
  nonQuadraticBlock : Option Orders.NonQuadraticDiscriminantBlock
  classification : AR12aDiscriminantAlgebraClassification
  noOrderCDEqualityStatus : AR12aQuadraticOrderCDEqualityStatus
  noOrderCDEqualityStatus_eq :
    noOrderCDEqualityStatus =
      AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  periodLatticePreparationStatus : AR12aPeriodLatticePreparationStatus
  downstreamDisciplineStatus : AR12aDownstreamDisciplineStatus
  downstreamDisciplineStatus_eq :
    downstreamDisciplineStatus =
      AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15
  derivedOnlyStatus : AR12aDerivedOnlyStatus
  derivedOnlyStatus_eq :
    derivedOnlyStatus = AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly
  cdNoIdentification :
    bridge.noIdentificationStatus =
      CayleyDickson.AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma
  cdSharedSchur : X.schur = source.multiSchur

namespace CDArithmeticCompatibility

variable {X : CayleyDickson.StructuralCDSource Cell T}
variable {z : Schur.SpectralParameter}

def fromQuadraticSurface
    {Q : Orders.QuadraticNormFormCertificate}
    (S : QuadraticOrderCDCompatibilitySurface (source := source) X L z Q) :
    CDArithmeticCompatibility (source := source) X L z where
  bridge := S.bridge
  orderCertificate := some Q.orderCertificate
  normFormCertificate := some Q
  nonQuadraticBlock := none
  classification := S.classification
  noOrderCDEqualityStatus := S.noOrderCDEqualityStatus
  noOrderCDEqualityStatus_eq := S.noOrderCDEqualityStatus_eq
  periodLatticePreparationStatus := S.periodLatticePreparationStatus
  downstreamDisciplineStatus := S.downstreamDisciplineStatus
  downstreamDisciplineStatus_eq := S.downstreamDisciplineStatus_eq
  derivedOnlyStatus := S.derivedOnlyStatus
  derivedOnlyStatus_eq := S.derivedOnlyStatus_eq
  cdNoIdentification := S.cdNoIdentification
  cdSharedSchur := S.cdSharedSchur

def fromNonQuadraticObstruction
    (O : NonQuadraticCDComplexObstruction (source := source) X L z) :
    CDArithmeticCompatibility (source := source) X L z where
  bridge := O.bridge
  orderCertificate := none
  normFormCertificate := none
  nonQuadraticBlock := some O.block
  classification := O.classification
  noOrderCDEqualityStatus :=
    AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra
  noOrderCDEqualityStatus_eq := by
    rfl
  periodLatticePreparationStatus := O.periodLatticePreparationStatus
  downstreamDisciplineStatus := O.downstreamDisciplineStatus
  downstreamDisciplineStatus_eq := O.downstreamDisciplineStatus_eq
  derivedOnlyStatus := O.derivedOnlyStatus
  derivedOnlyStatus_eq := O.derivedOnlyStatus_eq
  cdNoIdentification := O.cdNoIdentification
  cdSharedSchur := O.cdSharedSchur

def gaussian
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    CDArithmeticCompatibility (source := source) X L z :=
  fromQuadraticSurface (source := source) (QuadraticOrderCDCompatibilitySurface.gaussian (source := source) Bdg)

def eisenstein
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    CDArithmeticCompatibility (source := source) X L z :=
  fromQuadraticSurface (source := source) (QuadraticOrderCDCompatibilitySurface.eisenstein (source := source) Bdg)

def nonQuadratic
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z)
    (N : Orders.NonQuadraticDiscriminantBlock) :
    CDArithmeticCompatibility (source := source) X L z :=
  fromNonQuadraticObstruction (source := source) (NonQuadraticCDComplexObstruction.fromBlock (source := source) Bdg N)

theorem no_order_cd_equality
    (C : CDArithmeticCompatibility (source := source) X L z) :
    C.noOrderCDEqualityStatus =
      AR12aQuadraticOrderCDEqualityStatus.quadraticOrderNotIdentifiedWithCayleyDicksonAlgebra :=
  C.noOrderCDEqualityStatus_eq

theorem no_downstream_shortcut
    (C : CDArithmeticCompatibility (source := source) X L z) :
    C.downstreamDisciplineStatus =
      AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15 :=
  C.downstreamDisciplineStatus_eq

theorem derived_only
    (C : CDArithmeticCompatibility (source := source) X L z) :
    C.derivedOnlyStatus = AR12aDerivedOnlyStatus.ar12OrdersAndAR6aCDDataOnly :=
  C.derivedOnlyStatus_eq

theorem gaussian_classification
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    (gaussian (source := source) Bdg).classification =
      AR12aDiscriminantAlgebraClassification.gaussianDMinusFourCompatibility := by
  rfl

theorem eisenstein_classification
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    (eisenstein (source := source) Bdg).classification =
      AR12aDiscriminantAlgebraClassification.eisensteinDMinusThreeCompatibility := by
  rfl

theorem nonQuadratic_classification
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z)
    (N : Orders.NonQuadraticDiscriminantBlock) :
    (nonQuadratic (source := source) Bdg N).classification =
      AR12aDiscriminantAlgebraClassification.higherDegreeOrIrreducibleCDCObstruction := by
  rfl

end CDArithmeticCompatibility

end Convergence

namespace StrengtheningAR12a

abbrev AR12aDiscriminantAlgebraClassification :=
  Convergence.AR12aDiscriminantAlgebraClassification
abbrev AR12aQuadraticOrderCDEqualityStatus :=
  Convergence.AR12aQuadraticOrderCDEqualityStatus
abbrev AR12aPeriodLatticePreparationStatus :=
  Convergence.AR12aPeriodLatticePreparationStatus
abbrev AR12aDownstreamDisciplineStatus :=
  Convergence.AR12aDownstreamDisciplineStatus
abbrev AR12aImaginaryQuadraticDiscriminantWitness :=
  Convergence.ImaginaryQuadraticDiscriminantWitness
abbrev AR12aQuadraticOrderCDCompatibilitySurface
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (X : CayleyDickson.StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter)
    (Q : Orders.QuadraticNormFormCertificate) :=
  Convergence.QuadraticOrderCDCompatibilitySurface (source := source) X L z Q
abbrev AR12aNonQuadraticCDComplexObstruction
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (X : CayleyDickson.StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter) :=
  Convergence.NonQuadraticCDComplexObstruction (source := source) X L z
abbrev AR12aCDArithmeticCompatibility
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (X : CayleyDickson.StructuralCDSource Cell T)
    (L : Nat)
    (z : Schur.SpectralParameter) :=
  Convergence.CDArithmeticCompatibility (source := source) X L z

def AR12aGaussianCompatibilityFromBridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {X : CayleyDickson.StructuralCDSource Cell T} {z : Schur.SpectralParameter}
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    AR12aCDArithmeticCompatibility (source := source) X L z :=
  Convergence.CDArithmeticCompatibility.gaussian (source := source) Bdg

def AR12aEisensteinCompatibilityFromBridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {X : CayleyDickson.StructuralCDSource Cell T} {z : Schur.SpectralParameter}
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z) :
    AR12aCDArithmeticCompatibility (source := source) X L z :=
  Convergence.CDArithmeticCompatibility.eisenstein (source := source) Bdg

def AR12aNonQuadraticObstructionFromBridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {X : CayleyDickson.StructuralCDSource Cell T} {z : Schur.SpectralParameter}
    (Bdg : CayleyDickson.CDComplexArithmeticBridge source X L z)
    (N : Orders.NonQuadraticDiscriminantBlock) :
    AR12aCDArithmeticCompatibility (source := source) X L z :=
  Convergence.CDArithmeticCompatibility.nonQuadratic (source := source) Bdg N

theorem AR12aCompatibility_no_downstream_shortcut
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {X : CayleyDickson.StructuralCDSource Cell T} {z : Schur.SpectralParameter}
    (C : AR12aCDArithmeticCompatibility (source := source) X L z) :
    C.downstreamDisciplineStatus =
      Convergence.AR12aDownstreamDisciplineStatus.noJQFunctionLMoonshineConsumerBeforeAR13ToAR15 :=
  Convergence.CDArithmeticCompatibility.no_downstream_shortcut (source := source) C

theorem AR12aCompatibility_no_cd_identification
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {X : CayleyDickson.StructuralCDSource Cell T} {z : Schur.SpectralParameter}
    (C : AR12aCDArithmeticCompatibility (source := source) X L z) :
    C.bridge.noIdentificationStatus =
      CayleyDickson.AR6aNoIdentificationStatus.noExecMirrorCDComplexIdentificationWithoutTransferLemma :=
  C.cdNoIdentification

end StrengtheningAR12a

end CNNA.PillarA.Arithmetic
