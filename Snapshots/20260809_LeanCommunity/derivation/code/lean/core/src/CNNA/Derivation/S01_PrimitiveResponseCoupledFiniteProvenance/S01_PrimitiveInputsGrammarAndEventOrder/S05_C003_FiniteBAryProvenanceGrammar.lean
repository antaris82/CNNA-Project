import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S01_I001_BranchingParameterB
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S02_I002_FiniteApproximantDepthL
import CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder.S04_C002_RootGenesisR

/-!
Paper 1.1.5 / C003 — finite b-ary provenance grammar.

The three direct predecessors join here:
* C002 supplies the already-born unique root;
* I001 supplies `b >= 2`;
* I002 supplies the finite cutoff `L >= 0`.

The local slot type is `Fin b.value`.  Addresses are finite words of slots,
the C002 root is anchored to the empty word, child formation appends one slot,
parent and sibling-rank labels are recovered from the word, and accepted finite
addresses satisfy `depth <= L`.

No event order, node id, geometry, conductance, response, or dynamics is owned
by this module.  In particular, `L` truncates accepted words but does not alter
the intrinsic local slot alphabet.  C018 owns event ordering.
-/

namespace CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder

/-- Intrinsic local child-slot alphabet `S_b = {0, ..., b-1}`. -/
abbrev ProvenanceSlot (b : BranchingParameter) := Fin b.value

/-- A provenance address is a finite word over the local child-slot alphabet. -/
abbrev ProvenanceAddress (b : BranchingParameter) := List (ProvenanceSlot b)

namespace ProvenanceAddress

/-- Empty provenance word `ε`. -/
def root (b : BranchingParameter) : ProvenanceAddress b :=
  []

/-- Append exactly one local slot.  This constructor is independent of `L`. -/
def snoc {b : BranchingParameter} : ProvenanceAddress b → ProvenanceSlot b → ProvenanceAddress b
  | [], r => [r]
  | x :: xs, r => x :: snoc xs r

/-- Intrinsic provenance depth is word length. -/
def depth {b : BranchingParameter} (a : ProvenanceAddress b) : Nat :=
  a.length

/-- The root word has depth zero. -/
theorem depth_root (b : BranchingParameter) : depth (root b) = 0 :=
  rfl

/-- Appending one slot raises provenance depth by exactly one. -/
theorem depth_snoc {b : BranchingParameter} (u : ProvenanceAddress b) (r : ProvenanceSlot b) :
    depth (snoc u r) = Nat.succ (depth u) := by
  induction u with
  | nil =>
      rfl
  | cons x xs ih =>
      change Nat.succ (depth (snoc xs r)) = Nat.succ (Nat.succ (depth xs))
      rw [ih]

/-- Decompose a nonempty word into prefix parent and final slot. -/
def unsnoc? {b : BranchingParameter} :
    ProvenanceAddress b → Option (ProvenanceAddress b × ProvenanceSlot b)
  | [] => none
  | x :: xs =>
      match unsnoc? xs with
      | none => some ([], x)
      | some (u, r) => some (x :: u, r)

/-- `unsnoc?` exactly reverses one application of `snoc`. -/
theorem unsnoc?_snoc {b : BranchingParameter} (u : ProvenanceAddress b) (r : ProvenanceSlot b) :
    unsnoc? (snoc u r) = some (u, r) := by
  induction u with
  | nil =>
      rfl
  | cons x xs ih =>
      change
        (match unsnoc? (snoc xs r) with
          | none => some ([], x)
          | some (v, s) => some (x :: v, s)) = some (x :: xs, r)
      rw [ih]

/-- Prefix parent, undefined exactly for the root word. -/
def parent? {b : BranchingParameter} (a : ProvenanceAddress b) : Option (ProvenanceAddress b) :=
  match unsnoc? a with
  | none => none
  | some (u, _) => some u

/-- Final child-slot/sibling-rank label, undefined exactly for the root word. -/
def finalSlot? {b : BranchingParameter} (a : ProvenanceAddress b) : Option (ProvenanceSlot b) :=
  match unsnoc? a with
  | none => none
  | some (_, r) => some r

/-- Immediate provenance-parent relation induced by word extension. -/
def Parent {b : BranchingParameter} (u a : ProvenanceAddress b) : Prop :=
  parent? a = some u

/-- The root word has no provenance parent. -/
theorem parent?_root (b : BranchingParameter) : parent? (root b) = none :=
  rfl

/-- The root word has no final child-slot/rank label. -/
theorem finalSlot?_root (b : BranchingParameter) : finalSlot? (root b) = none :=
  rfl

/-- The parent of `u⌢r` is exactly `u`. -/
theorem parent?_snoc {b : BranchingParameter} (u : ProvenanceAddress b) (r : ProvenanceSlot b) :
    parent? (snoc u r) = some u := by
  unfold parent?
  rw [unsnoc?_snoc]

/-- The final slot/rank of `u⌢r` is exactly `r`. -/
theorem finalSlot?_snoc {b : BranchingParameter} (u : ProvenanceAddress b) (r : ProvenanceSlot b) :
    finalSlot? (snoc u r) = some r := by
  unfold finalSlot?
  rw [unsnoc?_snoc]

/-- Child formation induces the immediate parent relation. -/
theorem parent_snoc {b : BranchingParameter} (u : ProvenanceAddress b) (r : ProvenanceSlot b) :
    Parent u (snoc u r) :=
  parent?_snoc u r

/-- Equality of child words forces equality of their parent words. -/
theorem snoc_parent_unique {b : BranchingParameter}
    {u v : ProvenanceAddress b} {r s : ProvenanceSlot b}
    (h : snoc u r = snoc v s) : u = v := by
  have hp := congrArg parent? h
  rw [parent?_snoc, parent?_snoc] at hp
  cases hp
  rfl

/-- Equality of child words forces equality of their final rank labels. -/
theorem snoc_slot_unique {b : BranchingParameter}
    {u v : ProvenanceAddress b} {r s : ProvenanceSlot b}
    (h : snoc u r = snoc v s) : r = s := by
  have hr := congrArg finalSlot? h
  rw [finalSlot?_snoc, finalSlot?_snoc] at hr
  cases hr
  rfl

end ProvenanceAddress

/-- A provenance word accepted by finite cutoff `L`. -/
structure BoundedProvenanceAddress
    (b : BranchingParameter) (L : FiniteApproximantDepth) where
  address : ProvenanceAddress b
  depth_le_cutoff : ProvenanceAddress.depth address ≤ L.value

namespace BoundedProvenanceAddress

/-- The empty word is accepted for every finite cutoff, including `L = 0`. -/
def root (b : BranchingParameter) (L : FiniteApproximantDepth) :
    BoundedProvenanceAddress b L where
  address := ProvenanceAddress.root b
  depth_le_cutoff := Nat.zero_le L.value

/-- Extend an accepted word when its successor depth remains at most `L`. -/
def child {b : BranchingParameter} {L : FiniteApproximantDepth}
    (u : BoundedProvenanceAddress b L)
    (r : ProvenanceSlot b)
    (h : Nat.succ (ProvenanceAddress.depth u.address) ≤ L.value) :
    BoundedProvenanceAddress b L where
  address := ProvenanceAddress.snoc u.address r
  depth_le_cutoff := by
    rw [ProvenanceAddress.depth_snoc]
    exact h

/-- Bounded root address equation. -/
theorem root_address (b : BranchingParameter) (L : FiniteApproximantDepth) :
    (root b L).address = ProvenanceAddress.root b :=
  rfl

/-- Bounded child address equation. -/
theorem child_address {b : BranchingParameter} {L : FiniteApproximantDepth}
    (u : BoundedProvenanceAddress b L)
    (r : ProvenanceSlot b)
    (h : Nat.succ (ProvenanceAddress.depth u.address) ≤ L.value) :
    (child u r h).address = ProvenanceAddress.snoc u.address r :=
  rfl

/-- Bounded child formation preserves the exact successor-depth equation. -/
theorem child_depth {b : BranchingParameter} {L : FiniteApproximantDepth}
    (u : BoundedProvenanceAddress b L)
    (r : ProvenanceSlot b)
    (h : Nat.succ (ProvenanceAddress.depth u.address) ≤ L.value) :
    ProvenanceAddress.depth (child u r h).address =
      Nat.succ (ProvenanceAddress.depth u.address) :=
  ProvenanceAddress.depth_snoc u.address r

end BoundedProvenanceAddress

/-- The C003 construction joining its three direct scientific predecessors. -/
structure FiniteBAryProvenanceGrammar where
  rootedCarrier : RootedCarrier
  branching : BranchingParameter
  cutoff : FiniteApproximantDepth

namespace FiniteBAryProvenanceGrammar

/-- Canonical constructor: C002 rooted carrier + I001 branching + I002 cutoff. -/
def build (rootedCarrier : RootedCarrier) (branching : BranchingParameter)
    (cutoff : FiniteApproximantDepth) : FiniteBAryProvenanceGrammar where
  rootedCarrier := rootedCarrier
  branching := branching
  cutoff := cutoff

/-- The C002 root is present in the predecessor carrier used by the grammar. -/
theorem rootPresent (G : FiniteBAryProvenanceGrammar) :
    RootedCarrier.ContainsNode G.rootedCarrier Root.canonical :=
  RootedCarrier.rootPresent G.rootedCarrier

/-- Anchor the unique C002 root token to the bounded empty provenance word. -/
def rootAddress (G : FiniteBAryProvenanceGrammar) (_root : Root) :
    BoundedProvenanceAddress G.branching G.cutoff :=
  BoundedProvenanceAddress.root G.branching G.cutoff

/-- The canonical C002 root is anchored to the empty provenance word. -/
theorem rootAddress_canonical (G : FiniteBAryProvenanceGrammar) :
    (rootAddress G Root.canonical).address = ProvenanceAddress.root G.branching :=
  rfl

/-- Root uniqueness makes the root-address anchor independent of token presentation. -/
theorem rootAddress_unique (G : FiniteBAryProvenanceGrammar) (r : Root) :
    rootAddress G r = rootAddress G Root.canonical :=
  rfl

/-- Explicit constructor equation for the rooted-carrier predecessor. -/
theorem build_rootedCarrier (carrier : RootedCarrier) (b : BranchingParameter)
    (L : FiniteApproximantDepth) : (build carrier b L).rootedCarrier = carrier :=
  rfl

/-- Explicit constructor equation for the branching predecessor. -/
theorem build_branching (carrier : RootedCarrier) (b : BranchingParameter)
    (L : FiniteApproximantDepth) : (build carrier b L).branching = b :=
  rfl

/-- Explicit constructor equation for the cutoff predecessor. -/
theorem build_cutoff (carrier : RootedCarrier) (b : BranchingParameter)
    (L : FiniteApproximantDepth) : (build carrier b L).cutoff = L :=
  rfl

end FiniteBAryProvenanceGrammar

end CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S01_PrimitiveInputsGrammarAndEventOrder
