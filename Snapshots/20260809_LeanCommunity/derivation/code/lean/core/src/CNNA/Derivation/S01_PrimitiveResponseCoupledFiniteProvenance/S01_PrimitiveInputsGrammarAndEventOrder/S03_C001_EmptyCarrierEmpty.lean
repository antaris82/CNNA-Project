/-!
Paper 1.1.3 / C001 — empty carrier `∅`.

Scientific contract:
* the derivation has an actual pre-root carrier value;
* that carrier has no provenance nodes;
* that carrier has no relations;
* no root, address, geometry, weight, or event ordering is introduced here.

The carrier is deliberately inhabited.  A constructorless inductive type would
mean that no carrier value exists at all; that is not the C001 semantics.
The unique constructor below instead represents the one canonical empty
carrier from which C002 performs root genesis.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

universe u

/-- The inhabited singleton representing the primitive empty carrier. -/
inductive EmptyCarrier : Type where
  | empty

namespace EmptyCarrier

/-- Canonical value used at the C001 → C002 boundary. -/
def canonical : EmptyCarrier :=
  .empty

/-- Membership predicate for any prospective node type: always false. -/
def ContainsNode {α : Type u} (_carrier : EmptyCarrier) (_node : α) : Prop :=
  False

/-- Relation predicate for any prospective node type: always false. -/
def ContainsRelation {α : Type u}
    (_carrier : EmptyCarrier) (_source _target : α) : Prop :=
  False

/-- No value can be a node of the empty carrier. -/
theorem noNode {α : Type u} (carrier : EmptyCarrier) (node : α) :
    ¬ ContainsNode carrier node :=
  fun h => h

/-- No ordered pair can be a relation of the empty carrier. -/
theorem noRelation {α : Type u} (carrier : EmptyCarrier) (source target : α) :
    ¬ ContainsRelation carrier source target :=
  fun h => h

/-- There is no hidden choice in C001: every inhabitant is canonical. -/
theorem eqCanonical (carrier : EmptyCarrier) : carrier = canonical := by
  cases carrier
  rfl

end EmptyCarrier

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
