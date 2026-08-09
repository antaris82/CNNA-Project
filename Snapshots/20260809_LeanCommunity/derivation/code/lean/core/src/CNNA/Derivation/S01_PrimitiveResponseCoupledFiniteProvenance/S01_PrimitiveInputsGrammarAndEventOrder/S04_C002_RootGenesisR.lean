import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S03_C001_EmptyCarrierEmpty

/-!
Paper 1.1.4 / C002 — root genesis `r`.

Scientific contract:
* root genesis consumes the C001 empty carrier;
* the post-genesis carrier contains exactly one provenance node, the root;
* no relation exists yet;
* the root has no parent and no geometric position;
* no address, node index, sibling rank, event index, conductance, load, or
  response datum is introduced at this node.

Address grammar is owned by C003 and event ordering by C018.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

universe u

/-- The unique zero-payload provenance node born at genesis. -/
inductive Root : Type where
  | root

namespace Root

/-- Canonical root value. -/
def canonical : Root :=
  .root

/-- There is no hidden root choice. -/
theorem eqCanonical (r : Root) : r = canonical := by
  cases r
  rfl

end Root

/-- Canonical carrier immediately after root genesis. -/
inductive RootedCarrier : Type where
  | rooted

namespace RootedCarrier

/-- Canonical post-genesis carrier. -/
def canonical : RootedCarrier :=
  .rooted

/-- Node-membership at C002: precisely the canonical root. -/
def ContainsNode (_carrier : RootedCarrier) (node : Root) : Prop :=
  node = Root.canonical

/-- No relation exists immediately after root genesis. -/
def ContainsRelation {α : Type u}
    (_carrier : RootedCarrier) (_source _target : α) : Prop :=
  False

/-- The root has no parent at C002. -/
def HasParent {α : Type u}
    (_carrier : RootedCarrier) (_root : Root) (_parent : α) : Prop :=
  False

/-- C002 assigns no geometric position to the root. -/
def HasGeometricPosition {α : Type u}
    (_carrier : RootedCarrier) (_root : Root) (_position : α) : Prop :=
  False

/-- The canonical root is present in every rooted carrier. -/
theorem rootPresent (carrier : RootedCarrier) :
    ContainsNode carrier Root.canonical :=
  rfl

/-- Any node of the C002 carrier is the canonical root. -/
theorem nodeUnique (carrier : RootedCarrier) (node : Root)
    (h : ContainsNode carrier node) : node = Root.canonical :=
  h

/-- No ordered pair is a relation at root genesis. -/
theorem noRelation {α : Type u} (carrier : RootedCarrier) (source target : α) :
    ¬ ContainsRelation carrier source target :=
  fun h => h

/-- The root has no parent. -/
theorem rootHasNoParent {α : Type u}
    (carrier : RootedCarrier) (parent : α) :
    ¬ HasParent carrier Root.canonical parent :=
  fun h => h

/-- The root carries no geometric position at this derivation node. -/
theorem rootHasNoGeometricPosition {α : Type u}
    (carrier : RootedCarrier) (position : α) :
    ¬ HasGeometricPosition carrier Root.canonical position :=
  fun h => h

/-- There is no hidden choice in the post-genesis carrier. -/
theorem eqCanonical (carrier : RootedCarrier) : carrier = canonical := by
  cases carrier
  rfl

end RootedCarrier

/-- Unique C001 -> C002 root-genesis transition. -/
def rootGenesis (_carrier : EmptyCarrier) : RootedCarrier :=
  RootedCarrier.canonical

/-- The canonical empty carrier maps definitionally to the canonical rooted carrier. -/
theorem rootGenesis_canonical :
    rootGenesis EmptyCarrier.canonical = RootedCarrier.canonical :=
  rfl

/-- Since C001 is unique, the genesis result is source-independent. -/
theorem rootGenesis_eqCanonical (carrier : EmptyCarrier) :
    rootGenesis carrier = RootedCarrier.canonical :=
  rfl

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
