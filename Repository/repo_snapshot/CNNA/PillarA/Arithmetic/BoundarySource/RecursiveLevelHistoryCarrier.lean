import CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure RecursiveLevelHistoryCarrier
    (source : ArithmeticSource Cell T) (L : Nat) where
  witnessAt : (k : LevelHistoryIndex L) → LevelStepWitness source L k

namespace RecursiveLevelHistoryCarrier

variable (source : ArithmeticSource Cell T) (L : Nat)

def fromArithmeticSource : RecursiveLevelHistoryCarrier source L where
  witnessAt := by
    intro k
    exact LevelStepWitness.fromArithmeticSource source L k

theorem witnessAt_dtnProvenance
    (C : RecursiveLevelHistoryCarrier source L) (k : LevelHistoryIndex L) :
    source.dtn = source.multiSchur.binary :=
  (C.witnessAt k).hasDtnProvenance

theorem witnessAt_generalizedDtNProvenance
    (C : RecursiveLevelHistoryCarrier source L) (k : LevelHistoryIndex L) :
    source.generalizedDtN = source.multiSchur.generalized :=
  (C.witnessAt k).hasGeneralizedDtNProvenance

theorem witnessAt_schurProvenance
    (C : RecursiveLevelHistoryCarrier source L) (k : LevelHistoryIndex L) :
    source.coupling = source.multiSchur :=
  (C.witnessAt k).hasSchurProvenance

theorem witnessAt_noCutSpecCarrierClaim
    (C : RecursiveLevelHistoryCarrier source L) (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  (C.witnessAt k).noCutSpecCarrierClaim

end RecursiveLevelHistoryCarrier

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDRecursiveLevelHistoryCarrierOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.RecursiveLevelHistoryCarrier (Cell := Cell) (T := T) source L

def ar2bDRecursiveLevelHistoryCarrierFromSource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :
    AR2bDRecursiveLevelHistoryCarrierOf source L :=
  BoundarySource.RecursiveLevelHistoryCarrier.fromArithmeticSource source L

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
