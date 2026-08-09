import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S01_C004A_FirstProvenanceSlotS1
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S02_A001_GenesisSeedStar
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation.S03_N001_InitialConductanceNormalizationCStar1

/-!
Paper 1.2.4 / C013 — first non-root provenance birth `v₁`.

C013 is the exceptional first birth, before a nontrivial response network
exists.  It consumes C004A, A001 and N001.  The seed is accepted as an explicit
bootstrap argument but is not stored in the generated state; T001 owns the
separate theorem that this makes the first weighted state seed-neutral.

The construction requires the C004A address to lie within the finite cutoff.
Consequently `L = 0` has a structural `s₁` but no C013 birth.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- C013 output.  The A001 seed is deliberately not a stored field. -/
structure FirstNonRootBirth where
  slot : FirstProvenanceSlot
  normalization : InitialConductanceNormalization
  withinCutoff : FirstProvenanceSlot.WithinCutoff slot

namespace FirstNonRootBirth

/-- Exceptional first-birth constructor.  The singleton seed is consumed but not retained. -/
def build
    (slot : FirstProvenanceSlot)
    (_seed : GenesisSeed)
    (normalization : InitialConductanceNormalization)
    (h : FirstProvenanceSlot.WithinCutoff slot) : FirstNonRootBirth where
  slot := slot
  normalization := normalization
  withinCutoff := h

/-- Root endpoint inherited from the first provenance slot. -/
def rootAddress (B : FirstNonRootBirth) : ProvenanceAddress B.slot.grammar.branching :=
  FirstProvenanceSlot.parentAddress B.slot

/-- Newborn provenance address is exactly the C004A first-slot address. -/
def newbornAddress (B : FirstNonRootBirth) : ProvenanceAddress B.slot.grammar.branching :=
  FirstProvenanceSlot.address B.slot

/-- The two stored directed orientations of the first relation. -/
def directedRelations (B : FirstNonRootBirth) :
    (ProvenanceAddress B.slot.grammar.branching × ProvenanceAddress B.slot.grammar.branching) ×
    (ProvenanceAddress B.slot.grammar.branching × ProvenanceAddress B.slot.grammar.branching) :=
  ((rootAddress B, newbornAddress B), (newbornAddress B, rootAddress B))

/-- N001 supplies the symmetric unit conductances of the first relation. -/
def directedConductances (B : FirstNonRootBirth) : Nat × Nat :=
  InitialConductanceNormalization.directedValues B.normalization

/-- The newborn is the rank-zero one-step address selected by C004A. -/
theorem newborn_eq_first_slot (B : FirstNonRootBirth) :
    newbornAddress B = FirstProvenanceSlot.address B.slot :=
  rfl

/-- The newborn's provenance parent is the root address. -/
theorem newborn_parent_root (B : FirstNonRootBirth) :
    ProvenanceAddress.parent? (newbornAddress B) = some (rootAddress B) := by
  change ProvenanceAddress.parent? (FirstProvenanceSlot.address B.slot) =
    some (FirstProvenanceSlot.parentAddress B.slot)
  exact FirstProvenanceSlot.address_parent B.slot

/-- Both directed orientations are born with N001 unit conductance. -/
theorem directedConductances_eq_unit_pair (B : FirstNonRootBirth) :
    directedConductances B = (1, 1) := by
  change InitialConductanceNormalization.directedValues B.normalization = (1, 1)
  exact InitialConductanceNormalization.directedValues_eq_unit_pair B.normalization

end FirstNonRootBirth

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S02_BootstrapOfTheFirstRelation
