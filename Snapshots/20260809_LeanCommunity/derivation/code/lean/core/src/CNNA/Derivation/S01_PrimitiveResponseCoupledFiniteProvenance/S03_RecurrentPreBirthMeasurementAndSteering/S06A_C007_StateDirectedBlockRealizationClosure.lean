import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S03A_C006_ExactFractionRatRealizationClosure
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering.S06_C007_InterBirthDirectedResponseRnSnplus1

/-!
C007 realization closure — canonical rational realization of the exact
state-directed block matrix.

C007 already fixes every raw matrix entry from the C005 conductance state.  The
C006 `ExactFraction.toRat` bridge now supplies a canonical core-`Rat` entry for
each exact raw value, so existence of `StateDirectedBlockRealization` is a C007
fact rather than a free downstream assumption.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering

open NextOpenProvenanceSlot
open CanonicalBirthLocalMeasurementCut
open BirthLocalSchurDtnPrimitive
open BirthCutInteriorDomainTheorem

namespace InterBirthDirectedResponse

/-- Canonical C006 rational blocks obtained entrywise from C007's exact raw
state-directed matrix. -/
def canonicalStateDirectedBlocks {X : ResponseCapableState}
    (next : NextOpenSlot X) : BirthCutBlocks next :=
  mkBirthCutBlocks next
    (fun i j => ExactFraction.toRat (rawKBB next i j))
    (fun i j => ExactFraction.toRat (rawKBI next i j))
    (fun i j => ExactFraction.toRat (rawKIB next i j))
    (fun i j => ExactFraction.toRat (rawKII next i j))

/-- The canonical entrywise C006 realization represents exactly C007's four
raw state-directed blocks. -/
theorem canonicalStateDirectedBlocks_realizes {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    RealizesStateDirectedBlocks next (canonicalStateDirectedBlocks next) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact ExactFraction.toRat_represents (rawKBB next i j)
  · intro i j
    exact ExactFraction.toRat_represents (rawKBI next i j)
  · intro i j
    exact ExactFraction.toRat_represents (rawKIB next i j)
  · intro i j
    exact ExactFraction.toRat_represents (rawKII next i j)

/-- Canonical proof-bearing C007 realization. -/
def canonicalStateDirectedBlockRealization {X : ResponseCapableState}
    (next : NextOpenSlot X) : StateDirectedBlockRealization X next where
  blocks := canonicalStateDirectedBlocks next
  realizes := canonicalStateDirectedBlocks_realizes next

/-- C007 itself supplies a state-directed block realization for every admissible
C005 state and selected C004 slot; downstream nodes need not assume one. -/
theorem stateDirectedBlockRealization_exists {X : ResponseCapableState}
    (next : NextOpenSlot X) :
    ∃ realization : StateDirectedBlockRealization X next,
      realization = canonicalStateDirectedBlockRealization next := by
  exact ⟨canonicalStateDirectedBlockRealization next, rfl⟩

end InterBirthDirectedResponse

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
