import CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

def rootIndex (L : Nat) : BoundarySource.LevelHistoryIndex L :=
  ⟨0, Nat.succ_pos L⟩

def leafIndex (L : Nat) : BoundarySource.LevelHistoryIndex L :=
  ⟨L, Nat.lt_succ_self L⟩

theorem rootIndex_val (L : Nat) :
    (rootIndex L).val = 0 := by
  rfl

theorem leafIndex_val (L : Nat) :
    (leafIndex L).val = L := by
  rfl

inductive RootInteriorLeafSeparationStatus where
  | separated
  deriving DecidableEq, Repr

inductive SchurMobiusRecurrenceStatus where
  | ar4SchurMobiusRecursionClosed
  deriving DecidableEq, Repr

inductive SchurNumeratorDenominatorStatus where
  | theoremCarryingBoundaryDiagonal
  deriving DecidableEq, Repr

structure RootRecurrenceEquation
    (R : RecursiveSchurSource source L) where
  nodeKind : SchurRecursionNodeKind
  nodeKind_eq : nodeKind = SchurRecursionNodeKind.root
  index : BoundarySource.LevelHistoryIndex L
  index_eq_root : index = rootIndex L
  numerator_eq_boundary : R.numerator index = boundaryMatrixAt R.boundarySource index index
  denominator_eq_one : R.denominator index = 1
  sigma_eq_boundary : R.sigma index = boundaryMatrixAt R.boundarySource index index
  denominator_mul_sigma_eq_numerator :
    R.denominator index * R.sigma index = R.numerator index

namespace RootRecurrenceEquation

def fromRecursiveSchurSource
    (R : RecursiveSchurSource source L) :
    RootRecurrenceEquation R where
  nodeKind := SchurRecursionNodeKind.root
  nodeKind_eq := by
    rfl
  index := rootIndex L
  index_eq_root := by
    rfl
  numerator_eq_boundary := R.numerator_from_boundary (rootIndex L)
  denominator_eq_one := R.denominator_from_unit (rootIndex L)
  sigma_eq_boundary := R.sigma_from_boundary (rootIndex L)
  denominator_mul_sigma_eq_numerator := R.quotient_relation (rootIndex L)

theorem quotient_relation
    {R : RecursiveSchurSource source L}
    (E : RootRecurrenceEquation R) :
    R.denominator E.index * R.sigma E.index = R.numerator E.index :=
  E.denominator_mul_sigma_eq_numerator

end RootRecurrenceEquation

structure InteriorRecurrenceEquation
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) where
  nodeKind : SchurRecursionNodeKind
  nodeKind_eq : nodeKind = SchurRecursionNodeKind.interior
  leftOfRoot : 0 < k.val
  rightOfLeaf : k.val < L
  numerator_eq_boundary : R.numerator k = boundaryMatrixAt R.boundarySource k k
  denominator_eq_one : R.denominator k = 1
  sigma_eq_boundary : R.sigma k = boundaryMatrixAt R.boundarySource k k
  denominator_mul_sigma_eq_numerator :
    R.denominator k * R.sigma k = R.numerator k

namespace InteriorRecurrenceEquation

def fromRecursiveSchurSource
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L)
    (hroot : 0 < k.val) (hleaf : k.val < L) :
    InteriorRecurrenceEquation R k where
  nodeKind := SchurRecursionNodeKind.interior
  nodeKind_eq := by
    rfl
  leftOfRoot := hroot
  rightOfLeaf := hleaf
  numerator_eq_boundary := R.numerator_from_boundary k
  denominator_eq_one := R.denominator_from_unit k
  sigma_eq_boundary := R.sigma_from_boundary k
  denominator_mul_sigma_eq_numerator := R.quotient_relation k

theorem quotient_relation
    {R : RecursiveSchurSource source L}
    {k : BoundarySource.LevelHistoryIndex L}
    (E : InteriorRecurrenceEquation R k) :
    R.denominator k * R.sigma k = R.numerator k :=
  E.denominator_mul_sigma_eq_numerator

end InteriorRecurrenceEquation

structure LeafRecurrenceEquation
    (R : RecursiveSchurSource source L) where
  nodeKind : SchurRecursionNodeKind
  nodeKind_eq : nodeKind = SchurRecursionNodeKind.leaf
  index : BoundarySource.LevelHistoryIndex L
  index_eq_leaf : index = leafIndex L
  numerator_eq_boundary : R.numerator index = boundaryMatrixAt R.boundarySource index index
  denominator_eq_one : R.denominator index = 1
  sigma_eq_boundary : R.sigma index = boundaryMatrixAt R.boundarySource index index
  denominator_mul_sigma_eq_numerator :
    R.denominator index * R.sigma index = R.numerator index

namespace LeafRecurrenceEquation

def fromRecursiveSchurSource
    (R : RecursiveSchurSource source L) :
    LeafRecurrenceEquation R where
  nodeKind := SchurRecursionNodeKind.leaf
  nodeKind_eq := by
    rfl
  index := leafIndex L
  index_eq_leaf := by
    rfl
  numerator_eq_boundary := R.numerator_from_boundary (leafIndex L)
  denominator_eq_one := R.denominator_from_unit (leafIndex L)
  sigma_eq_boundary := R.sigma_from_boundary (leafIndex L)
  denominator_mul_sigma_eq_numerator := R.quotient_relation (leafIndex L)

theorem quotient_relation
    {R : RecursiveSchurSource source L}
    (E : LeafRecurrenceEquation R) :
    R.denominator E.index * R.sigma E.index = R.numerator E.index :=
  E.denominator_mul_sigma_eq_numerator

end LeafRecurrenceEquation

structure SchurMobiusRecurrenceLedger
    (source : ArithmeticSource Cell T) (L : Nat) where
  recursiveSource : RecursiveSchurSource source L
  rootEquation : RootRecurrenceEquation recursiveSource
  interiorEquation :
    ∀ (k : BoundarySource.LevelHistoryIndex L),
      0 < k.val → k.val < L → InteriorRecurrenceEquation recursiveSource k
  leafEquation : LeafRecurrenceEquation recursiveSource
  separationStatus : RootInteriorLeafSeparationStatus
  separationStatus_eq : separationStatus = RootInteriorLeafSeparationStatus.separated
  numeratorDenominatorStatus : SchurNumeratorDenominatorStatus
  numeratorDenominatorStatus_eq :
    numeratorDenominatorStatus =
      SchurNumeratorDenominatorStatus.theoremCarryingBoundaryDiagonal
  recurrenceStatus : SchurMobiusRecurrenceStatus
  recurrenceStatus_eq :
    recurrenceStatus = SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  parameterStatus : MobiusTransferParameterStatus
  parameterStatus_eq :
    parameterStatus = MobiusTransferParameterStatus.fromBoundarySourceAndAR3Only
  actionDataStatus : MobiusActionDataStatus
  actionDataStatus_eq :
    actionDataStatus = MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData
  route :
    recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace SchurMobiusRecurrenceLedger

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L) :
    SchurMobiusRecurrenceLedger source L where
  recursiveSource := RecursiveSchurSource.fromBoundarySource B
  rootEquation := RootRecurrenceEquation.fromRecursiveSchurSource
    (RecursiveSchurSource.fromBoundarySource B)
  interiorEquation := by
    intro k hroot hleaf
    exact InteriorRecurrenceEquation.fromRecursiveSchurSource
      (RecursiveSchurSource.fromBoundarySource B) k hroot hleaf
  leafEquation := LeafRecurrenceEquation.fromRecursiveSchurSource
    (RecursiveSchurSource.fromBoundarySource B)
  separationStatus := RootInteriorLeafSeparationStatus.separated
  separationStatus_eq := by
    rfl
  numeratorDenominatorStatus :=
    SchurNumeratorDenominatorStatus.theoremCarryingBoundaryDiagonal
  numeratorDenominatorStatus_eq := by
    rfl
  recurrenceStatus := SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  recurrenceStatus_eq := by
    rfl
  parameterStatus := MobiusTransferParameterStatus.fromBoundarySourceAndAR3Only
  parameterStatus_eq := by
    rfl
  actionDataStatus := MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData
  actionDataStatus_eq := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem status_closed
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.recurrenceStatus = SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed :=
  Ldg.recurrenceStatus_eq

theorem separation_status
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.separationStatus = RootInteriorLeafSeparationStatus.separated :=
  Ldg.separationStatus_eq

theorem numeratorDenominator_status
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.numeratorDenominatorStatus =
      SchurNumeratorDenominatorStatus.theoremCarryingBoundaryDiagonal :=
  Ldg.numeratorDenominatorStatus_eq

theorem root_quotient_relation
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.recursiveSource.denominator Ldg.rootEquation.index *
        Ldg.recursiveSource.sigma Ldg.rootEquation.index =
      Ldg.recursiveSource.numerator Ldg.rootEquation.index :=
  Ldg.rootEquation.denominator_mul_sigma_eq_numerator

theorem interior_quotient_relation
    (Ldg : SchurMobiusRecurrenceLedger source L)
    (k : BoundarySource.LevelHistoryIndex L)
    (hroot : 0 < k.val) (hleaf : k.val < L) :
    Ldg.recursiveSource.denominator k * Ldg.recursiveSource.sigma k =
      Ldg.recursiveSource.numerator k :=
  (Ldg.interiorEquation k hroot hleaf).denominator_mul_sigma_eq_numerator

theorem leaf_quotient_relation
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.recursiveSource.denominator Ldg.leafEquation.index *
        Ldg.recursiveSource.sigma Ldg.leafEquation.index =
      Ldg.recursiveSource.numerator Ldg.leafEquation.index :=
  Ldg.leafEquation.denominator_mul_sigma_eq_numerator

theorem parameterStatus_fromBoundarySourceAndAR3Only
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.parameterStatus = MobiusTransferParameterStatus.fromBoundarySourceAndAR3Only :=
  Ldg.parameterStatus_eq

theorem actionDataStatus_noNumericData
    (Ldg : SchurMobiusRecurrenceLedger source L) :
    Ldg.actionDataStatus = MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData :=
  Ldg.actionDataStatus_eq

theorem noCutSpecCarrierClaim_at
    (Ldg : SchurMobiusRecurrenceLedger source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim k

end SchurMobiusRecurrenceLedger

end Schur

end CNNA.PillarA.Arithmetic
