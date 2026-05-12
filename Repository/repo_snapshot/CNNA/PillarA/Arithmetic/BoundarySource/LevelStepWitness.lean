import CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev LevelStepNoCutSpecCarrierClaim
    (source : ArithmeticSource Cell T) (L : Nat)
    (_k : LevelHistoryIndex L) : Prop :=
  source.toc.approximant source.concretePolicy = T

structure LevelStepWitness
    (source : ArithmeticSource Cell T) (L : Nat)
    (k : LevelHistoryIndex L) where
  hasDtnProvenance : source.dtn = source.multiSchur.binary
  hasGeneralizedDtNProvenance : source.generalizedDtN = source.multiSchur.generalized
  hasSchurProvenance : source.coupling = source.multiSchur
  noCutSpecCarrierClaim : LevelStepNoCutSpecCarrierClaim source L k

namespace LevelStepWitness

variable (source : ArithmeticSource Cell T) (L : Nat) (k : LevelHistoryIndex L)

def fromArithmeticSource : LevelStepWitness source L k where
  hasDtnProvenance := by
    rfl
  hasGeneralizedDtNProvenance := by
    rfl
  hasSchurProvenance := by
    rfl
  noCutSpecCarrierClaim := by
    exact source.truncation_eq_toc.symm

theorem dtnProvenance_eq
    (W : LevelStepWitness source L k) :
    source.dtn = source.multiSchur.binary :=
  W.hasDtnProvenance

theorem generalizedDtNProvenance_eq
    (W : LevelStepWitness source L k) :
    source.generalizedDtN = source.multiSchur.generalized :=
  W.hasGeneralizedDtNProvenance

theorem schurProvenance_eq
    (W : LevelStepWitness source L k) :
    source.coupling = source.multiSchur :=
  W.hasSchurProvenance

theorem noCutSpecCarrierClaim_eq_tocApproximant
    (W : LevelStepWitness source L k) :
    source.toc.approximant source.concretePolicy = T :=
  W.noCutSpecCarrierClaim

end LevelStepWitness

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDLevelStepWitnessOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat)
    (k : BoundarySource.LevelHistoryIndex L) :=
  BoundarySource.LevelStepWitness (Cell := Cell) (T := T) source L k

def ar2bDLevelStepWitnessFromSource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat)
    (k : BoundarySource.LevelHistoryIndex L) :
    AR2bDLevelStepWitnessOf source L k :=
  BoundarySource.LevelStepWitness.fromArithmeticSource source L k

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
