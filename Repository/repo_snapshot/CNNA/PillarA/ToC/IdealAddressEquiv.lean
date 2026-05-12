import CNNA.PillarA.ToC.Addressing

set_option autoImplicit false

namespace CNNA.PillarA.ToC

open CNNA.PillarA.Foundation

universe u v

class IdealAddressEquiv
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] : Type (max u v + 1)
    extends AddressPresentation Cell Addr where
  child_mem_children_iff :
    ∀ {L : Nat} (p : Cell L) (c : Cell (L + 1)),
      c ∈ SubstrateClass.children p ↔
        addressOf c ∈ children (addressOf p)

namespace DirectedFamily

variable {Cell : Nat → Type u} [SubstrateClass Cell]

@[ext] theorem ext (F G : DirectedFamily (Cell := Cell))
    (hcarrier : ∀ L : Nat, F.carrier L = G.carrier L) : F = G := by
  cases F with
  | mk carrierF rootedF forwardF =>
    cases G with
    | mk carrierG rootedG forwardG =>
      have hcar : carrierF = carrierG := by
        funext L
        exact hcarrier L
      subst hcar
      have hroot : rootedF = rootedG := Subsingleton.elim _ _
      subst hroot
      have hforward : forwardF = forwardG := Subsingleton.elim _ _
      subst hforward
      rfl

end DirectedFamily

namespace IdealAddressEquiv

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]

def encode {L : Nat} (c : Cell L) : Addr L :=
  AddressPresentation.addressOf (Cell := Cell) (Addr := Addr) c

def decode {L : Nat} (a : Addr L) : Cell L :=
  AddressPresentation.cellOf (Cell := Cell) (Addr := Addr) a

theorem decode_encode {L : Nat} (c : Cell L) :
    decode (Cell := Cell) (Addr := Addr) (encode (Cell := Cell) (Addr := Addr) c) = c := by
  exact AddressPresentation.cellOf_addressOf (Cell := Cell) (Addr := Addr) c

theorem encode_decode {L : Nat} (a : Addr L) :
    encode (Cell := Cell) (Addr := Addr) (decode (Cell := Cell) (Addr := Addr) a) = a := by
  exact AddressPresentation.addressOf_cellOf (Cell := Cell) (Addr := Addr) a

theorem encode_root_eq_root :
    encode (Cell := Cell) (Addr := Addr) (SubstrateClass.root (Cell := Cell)) =
      AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
  exact AddressPresentation.addressOf_root_eq_root (Cell := Cell) (Addr := Addr)

theorem decode_root_eq_root :
    decode (Cell := Cell) (Addr := Addr)
      (AddressPresentation.root (Cell := Cell) (Addr := Addr)) =
        SubstrateClass.root (Cell := Cell) := by
  exact AddressPresentation.cellOf_root_eq_root (Cell := Cell) (Addr := Addr)

theorem decode_child_mem_children_iff {L : Nat} (a : Addr L) (b : Addr (L + 1)) :
    decode (Cell := Cell) (Addr := Addr) b ∈
        SubstrateClass.children (decode (Cell := Cell) (Addr := Addr) a) ↔
      b ∈ AddressPresentation.children (Cell := Cell) (Addr := Addr) a := by
  have h := IdealAddressEquiv.child_mem_children_iff
    (Cell := Cell) (Addr := Addr)
    (decode (Cell := Cell) (Addr := Addr) a)
    (decode (Cell := Cell) (Addr := Addr) b)
  constructor
  · intro hdec
    have haddr := h.mp hdec
    have hb_eq :
        AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) b) = b :=
      encode_decode (Cell := Cell) (Addr := Addr) b
    have ha_eq :
        AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) a) = a :=
      AddressPresentation.addressOf_cellOf (Cell := Cell) (Addr := Addr) a
    rw [hb_eq, ha_eq] at haddr
    exact haddr
  · intro hb
    have hb_eq :
        AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) b) = b :=
      encode_decode (Cell := Cell) (Addr := Addr) b
    have ha_eq :
        AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) a) = a :=
      AddressPresentation.addressOf_cellOf (Cell := Cell) (Addr := Addr) a
    have haddr :
        AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
            (decode (Cell := Cell) (Addr := Addr) b) ∈
          AddressPresentation.children (Cell := Cell) (Addr := Addr)
            (AddressPresentation.addressOf (Cell := Cell) (Addr := Addr)
              (decode (Cell := Cell) (Addr := Addr) a)) := by
      rw [hb_eq, ha_eq]
      exact hb
    exact h.mpr haddr

theorem encode_parent_eq_iff {L : Nat} (p : Cell L) (c : Cell (L + 1)) :
    p ∈ SubstrateClass.parents c ↔
      AddressPresentation.parent (Cell := Cell) (Addr := Addr)
        (encode (Cell := Cell) (Addr := Addr) c) =
          encode (Cell := Cell) (Addr := Addr) p := by
  constructor
  · intro hp
    have hc : c ∈ SubstrateClass.children p :=
      SubstrateClass.child_mem_of_parent_mem (Cell := Cell) hp
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr) p) := by
      exact (IdealAddressEquiv.child_mem_children_iff
        (Cell := Cell) (Addr := Addr) p c).mp hc
    exact AddressPresentation.parent_eq_of_child_mem
      (Cell := Cell) (Addr := Addr) henc
  · intro hp
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr) p) := by
      exact AddressPresentation.child_mem_of_parent_eq
        (Cell := Cell) (Addr := Addr) hp
    have hc : c ∈ SubstrateClass.children p := by
      exact (IdealAddressEquiv.child_mem_children_iff
        (Cell := Cell) (Addr := Addr) p c).mpr henc
    exact SubstrateClass.parent_mem_of_child_mem (Cell := Cell) hc

theorem decode_parent_mem_parents {L : Nat} (a : Addr (L + 1)) :
    decode (Cell := Cell) (Addr := Addr)
        (AddressPresentation.parent (Cell := Cell) (Addr := Addr) a) ∈
      SubstrateClass.parents (decode (Cell := Cell) (Addr := Addr) a) := by
  have hpar : AddressPresentation.parent (Cell := Cell) (Addr := Addr)
      (encode (Cell := Cell) (Addr := Addr)
        (decode (Cell := Cell) (Addr := Addr) a)) =
    encode (Cell := Cell) (Addr := Addr)
      (decode (Cell := Cell) (Addr := Addr)
        (AddressPresentation.parent (Cell := Cell) (Addr := Addr) a)) := by
    rw [encode_decode (Cell := Cell) (Addr := Addr) a,
      encode_decode (Cell := Cell) (Addr := Addr)
        (AddressPresentation.parent (Cell := Cell) (Addr := Addr) a)]
  exact (encode_parent_eq_iff
    (Cell := Cell) (Addr := Addr)
    (decode (Cell := Cell) (Addr := Addr)
      (AddressPresentation.parent (Cell := Cell) (Addr := Addr) a))
    (decode (Cell := Cell) (Addr := Addr) a)).mpr hpar

def decodedParent {L : Nat} (c : Cell (L + 1)) : Cell L :=
  decode (Cell := Cell) (Addr := Addr)
    (AddressPresentation.parent (Cell := Cell) (Addr := Addr)
      (encode (Cell := Cell) (Addr := Addr) c))

theorem parent_mem_decodedParent {L : Nat} (c : Cell (L + 1)) :
    decodedParent (Cell := Cell) (Addr := Addr) c ∈ SubstrateClass.parents c := by
  have hpar : AddressPresentation.parent (Cell := Cell) (Addr := Addr)
      (encode (Cell := Cell) (Addr := Addr) c) =
    encode (Cell := Cell) (Addr := Addr)
      (decodedParent (Cell := Cell) (Addr := Addr) c) := by
    unfold decodedParent
    rw [encode_decode (Cell := Cell) (Addr := Addr)
      (AddressPresentation.parent (Cell := Cell) (Addr := Addr)
        (encode (Cell := Cell) (Addr := Addr) c))]
  exact (encode_parent_eq_iff
    (Cell := Cell) (Addr := Addr)
    (decodedParent (Cell := Cell) (Addr := Addr) c) c).mpr hpar

theorem parents_eq_singleton_decodedParent {L : Nat} (c : Cell (L + 1)) :
    SubstrateClass.parents c =
      {decodedParent (Cell := Cell) (Addr := Addr) c} := by
  ext p
  constructor
  · intro hp
    have hpar : AddressPresentation.parent (Cell := Cell) (Addr := Addr)
        (encode (Cell := Cell) (Addr := Addr) c) =
      encode (Cell := Cell) (Addr := Addr) p := by
      exact (encode_parent_eq_iff (Cell := Cell) (Addr := Addr) p c).mp hp
    have henc : encode (Cell := Cell) (Addr := Addr) p =
        encode (Cell := Cell) (Addr := Addr)
          (decodedParent (Cell := Cell) (Addr := Addr) c) := by
      calc
        encode (Cell := Cell) (Addr := Addr) p =
            AddressPresentation.parent (Cell := Cell) (Addr := Addr)
              (encode (Cell := Cell) (Addr := Addr) c) := hpar.symm
        _ = encode (Cell := Cell) (Addr := Addr)
              (decodedParent (Cell := Cell) (Addr := Addr) c) := by
              unfold decodedParent
              rw [encode_decode (Cell := Cell) (Addr := Addr)
                (AddressPresentation.parent (Cell := Cell) (Addr := Addr)
                  (encode (Cell := Cell) (Addr := Addr) c))]
    have hpEq : p = decodedParent (Cell := Cell) (Addr := Addr) c :=
      AddressPresentation.addressOf_injective (Cell := Cell) (Addr := Addr) henc
    subst hpEq
    exact Finset.mem_singleton_self _
  · intro hp
    have hpEq : p = decodedParent (Cell := Cell) (Addr := Addr) c := by
      exact Finset.mem_singleton.mp hp
    subst hpEq
    exact parent_mem_decodedParent (Cell := Cell) (Addr := Addr) c

def encodeSet {L : Nat} (S : Finset (Cell L)) : Finset (Addr L) :=
  S.image (encode (Cell := Cell) (Addr := Addr))

def decodeSet {L : Nat} (S : Finset (Addr L)) : Finset (Cell L) :=
  S.image (decode (Cell := Cell) (Addr := Addr))

theorem mem_encodeSet {L : Nat} {S : Finset (Cell L)} {a : Addr L} :
    a ∈ encodeSet (Cell := Cell) (Addr := Addr) S ↔
      decode (Cell := Cell) (Addr := Addr) a ∈ S := by
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨c, hc, hca⟩
    subst hca
    rw [decode_encode (Cell := Cell) (Addr := Addr) c]
    exact hc
  · intro ha
    exact Finset.mem_image.mpr ⟨
      decode (Cell := Cell) (Addr := Addr) a,
      ha,
      by exact encode_decode (Cell := Cell) (Addr := Addr) a⟩

theorem mem_decodeSet {L : Nat} {S : Finset (Addr L)} {c : Cell L} :
    c ∈ decodeSet (Cell := Cell) (Addr := Addr) S ↔
      encode (Cell := Cell) (Addr := Addr) c ∈ S := by
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨a, ha, hac⟩
    subst hac
    rw [encode_decode (Cell := Cell) (Addr := Addr) a]
    exact ha
  · intro hc
    exact Finset.mem_image.mpr ⟨
      encode (Cell := Cell) (Addr := Addr) c,
      hc,
      by exact decode_encode (Cell := Cell) (Addr := Addr) c⟩

theorem decodeSet_encodeSet {L : Nat} (S : Finset (Cell L)) :
    decodeSet (Cell := Cell) (Addr := Addr)
      (encodeSet (Cell := Cell) (Addr := Addr) S) = S := by
  ext c
  constructor
  · intro hc
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        encodeSet (Cell := Cell) (Addr := Addr) S := by
      exact (mem_decodeSet (Cell := Cell) (Addr := Addr)
        (S := encodeSet (Cell := Cell) (Addr := Addr) S)
        (c := c)).mp hc
    have hc' := (mem_encodeSet (Cell := Cell) (Addr := Addr)
      (S := S)
      (a := encode (Cell := Cell) (Addr := Addr) c)).mp henc
    rw [decode_encode (Cell := Cell) (Addr := Addr) c] at hc'
    exact hc'
  · intro hc
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        encodeSet (Cell := Cell) (Addr := Addr) S := by
      exact (mem_encodeSet (Cell := Cell) (Addr := Addr)
        (S := S)
        (a := encode (Cell := Cell) (Addr := Addr) c)).mpr (by
          rw [decode_encode (Cell := Cell) (Addr := Addr) c]
          exact hc)
    exact (mem_decodeSet (Cell := Cell) (Addr := Addr)
      (S := encodeSet (Cell := Cell) (Addr := Addr) S)
      (c := c)).mpr henc

theorem encodeSet_decodeSet {L : Nat} (S : Finset (Addr L)) :
    encodeSet (Cell := Cell) (Addr := Addr)
      (decodeSet (Cell := Cell) (Addr := Addr) S) = S := by
  ext a
  constructor
  · intro ha
    have hdec : decode (Cell := Cell) (Addr := Addr) a ∈
        decodeSet (Cell := Cell) (Addr := Addr) S := by
      exact (mem_encodeSet (Cell := Cell) (Addr := Addr)
        (S := decodeSet (Cell := Cell) (Addr := Addr) S)
        (a := a)).mp ha
    have ha' := (mem_decodeSet (Cell := Cell) (Addr := Addr)
      (S := S)
      (c := decode (Cell := Cell) (Addr := Addr) a)).mp hdec
    rw [encode_decode (Cell := Cell) (Addr := Addr) a] at ha'
    exact ha'
  · intro ha
    have hdec : decode (Cell := Cell) (Addr := Addr) a ∈
        decodeSet (Cell := Cell) (Addr := Addr) S := by
      exact (mem_decodeSet (Cell := Cell) (Addr := Addr)
        (S := S)
        (c := decode (Cell := Cell) (Addr := Addr) a)).mpr (by
          rw [encode_decode (Cell := Cell) (Addr := Addr) a]
          exact ha)
    exact (mem_encodeSet (Cell := Cell) (Addr := Addr)
      (S := decodeSet (Cell := Cell) (Addr := Addr) S)
      (a := a)).mpr hdec

def addrRootLayer : Finset (Addr 0) :=
  {AddressPresentation.root (Cell := Cell) (Addr := Addr)}

theorem encodeSet_rootLayer :
    encodeSet (Cell := Cell) (Addr := Addr) (SubstrateClass.rootLayer (Cell := Cell)) =
      addrRootLayer (Cell := Cell) (Addr := Addr) := by
  ext a
  constructor
  · intro ha
    have hdec : decode (Cell := Cell) (Addr := Addr) a ∈ SubstrateClass.rootLayer (Cell := Cell) := by
      exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mp ha
    have hroot : decode (Cell := Cell) (Addr := Addr) a = SubstrateClass.root (Cell := Cell) :=
      (SubstrateClass.mem_rootLayer_iff (Cell := Cell)
        (decode (Cell := Cell) (Addr := Addr) a)).mp hdec
    have haEq : a = AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
      calc
        a = encode (Cell := Cell) (Addr := Addr)
              (decode (Cell := Cell) (Addr := Addr) a) := by
                exact (encode_decode (Cell := Cell) (Addr := Addr) a).symm
        _ = encode (Cell := Cell) (Addr := Addr) (SubstrateClass.root (Cell := Cell)) := by
              rw [hroot]
        _ = AddressPresentation.root (Cell := Cell) (Addr := Addr) :=
              encode_root_eq_root (Cell := Cell) (Addr := Addr)
    simpa [addrRootLayer] using Finset.mem_singleton.mpr haEq
  · intro ha
    have haEq : a = AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
      simpa [addrRootLayer] using ha
    have hdec : decode (Cell := Cell) (Addr := Addr) a ∈ SubstrateClass.rootLayer (Cell := Cell) := by
      have hroot : decode (Cell := Cell) (Addr := Addr) a = SubstrateClass.root (Cell := Cell) := by
        calc
          decode (Cell := Cell) (Addr := Addr) a =
              decode (Cell := Cell) (Addr := Addr)
                (AddressPresentation.root (Cell := Cell) (Addr := Addr)) := by rw [haEq]
          _ = SubstrateClass.root (Cell := Cell) :=
                decode_root_eq_root (Cell := Cell) (Addr := Addr)
      exact (SubstrateClass.mem_rootLayer_iff (Cell := Cell)
        (decode (Cell := Cell) (Addr := Addr) a)).mpr hroot
    exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mpr hdec

theorem decodeSet_rootLayer :
    decodeSet (Cell := Cell) (Addr := Addr)
      (addrRootLayer (Cell := Cell) (Addr := Addr)) =
        SubstrateClass.rootLayer (Cell := Cell) := by
  ext c
  constructor
  · intro hc
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        addrRootLayer (Cell := Cell) (Addr := Addr) := by
      rw [← (mem_decodeSet (Cell := Cell) (Addr := Addr)
        (S := addrRootLayer (Cell := Cell) (Addr := Addr))
        (c := c))]
      exact hc
    have hroot_addr : encode (Cell := Cell) (Addr := Addr) c =
        AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
      simpa [addrRootLayer] using henc
    have hroot_cell : c = SubstrateClass.root (Cell := Cell) := by
      calc
        c = decode (Cell := Cell) (Addr := Addr)
              (encode (Cell := Cell) (Addr := Addr) c) := by
                exact (decode_encode (Cell := Cell) (Addr := Addr) c).symm
        _ = decode (Cell := Cell) (Addr := Addr)
              (AddressPresentation.root (Cell := Cell) (Addr := Addr)) := by
                rw [hroot_addr]
        _ = SubstrateClass.root (Cell := Cell) := by
              exact decode_root_eq_root (Cell := Cell) (Addr := Addr)
    exact (SubstrateClass.mem_rootLayer_iff (Cell := Cell) c).mpr hroot_cell
  · intro hc
    have hroot_cell : c = SubstrateClass.root (Cell := Cell) := by
      exact (SubstrateClass.mem_rootLayer_iff (Cell := Cell) c).mp hc
    have hroot_addr : encode (Cell := Cell) (Addr := Addr) c =
        AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
      calc
        encode (Cell := Cell) (Addr := Addr) c =
            encode (Cell := Cell) (Addr := Addr)
              (SubstrateClass.root (Cell := Cell)) := by
                rw [hroot_cell]
        _ = AddressPresentation.root (Cell := Cell) (Addr := Addr) := by
              exact encode_root_eq_root (Cell := Cell) (Addr := Addr)
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        addrRootLayer (Cell := Cell) (Addr := Addr) := by
      simpa [addrRootLayer] using hroot_addr
    rw [(mem_decodeSet (Cell := Cell) (Addr := Addr)
      (S := addrRootLayer (Cell := Cell) (Addr := Addr))
      (c := c))]
    exact henc

theorem encodeSet_children {L : Nat} (p : Cell L) :
    encodeSet (Cell := Cell) (Addr := Addr) (SubstrateClass.children p) =
      AddressPresentation.children (Cell := Cell) (Addr := Addr)
        (encode (Cell := Cell) (Addr := Addr) p) := by
  ext b
  constructor
  · intro hb
    have hdec : decode (Cell := Cell) (Addr := Addr) b ∈ SubstrateClass.children p := by
      exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mp hb
    have haddr : encode (Cell := Cell) (Addr := Addr)
        (decode (Cell := Cell) (Addr := Addr) b) ∈
          AddressPresentation.children (Cell := Cell) (Addr := Addr)
            (encode (Cell := Cell) (Addr := Addr) p) := by
      exact (IdealAddressEquiv.child_mem_children_iff
        (Cell := Cell) (Addr := Addr) p
        (decode (Cell := Cell) (Addr := Addr) b)).mp hdec
    have hb_eq :
        encode (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) b) = b :=
      encode_decode (Cell := Cell) (Addr := Addr) b
    rw [hb_eq] at haddr
    exact haddr
  · intro hb
    have hb_eq :
        encode (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) b) = b :=
      encode_decode (Cell := Cell) (Addr := Addr) b
    have haddr : encode (Cell := Cell) (Addr := Addr)
        (decode (Cell := Cell) (Addr := Addr) b) ∈
          AddressPresentation.children (Cell := Cell) (Addr := Addr)
            (encode (Cell := Cell) (Addr := Addr) p) := by
      rw [hb_eq]
      exact hb
    have hdec : decode (Cell := Cell) (Addr := Addr) b ∈ SubstrateClass.children p := by
      exact (IdealAddressEquiv.child_mem_children_iff
        (Cell := Cell) (Addr := Addr) p
        (decode (Cell := Cell) (Addr := Addr) b)).mpr haddr
    exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mpr hdec

theorem decodeSet_children {L : Nat} (a : Addr L) :
    decodeSet (Cell := Cell) (Addr := Addr)
      (AddressPresentation.children (Cell := Cell) (Addr := Addr) a) =
        SubstrateClass.children (decode (Cell := Cell) (Addr := Addr) a) := by
  ext c
  constructor
  · intro hc
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr) a := by
      exact (mem_decodeSet (Cell := Cell) (Addr := Addr)).mp hc
    have ha_eq :
        encode (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) a) = a :=
      encode_decode (Cell := Cell) (Addr := Addr) a
    have henc' : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr)
            (decode (Cell := Cell) (Addr := Addr) a)) := by
      rw [ha_eq]
      exact henc
    exact (IdealAddressEquiv.child_mem_children_iff
      (Cell := Cell) (Addr := Addr)
      (decode (Cell := Cell) (Addr := Addr) a) c).mpr henc'
  · intro hc
    have henc' : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr)
            (decode (Cell := Cell) (Addr := Addr) a)) := by
      exact (IdealAddressEquiv.child_mem_children_iff
        (Cell := Cell) (Addr := Addr)
        (decode (Cell := Cell) (Addr := Addr) a) c).mp hc
    have ha_eq :
        encode (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) a) = a :=
      encode_decode (Cell := Cell) (Addr := Addr) a
    have henc : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr) a := by
      rw [ha_eq] at henc'
      exact henc'
    exact (mem_decodeSet (Cell := Cell) (Addr := Addr)).mpr henc

def addrRefineSet {L : Nat} (S : Finset (Addr L)) : Finset (Addr (L + 1)) :=
  S.biUnion (fun a => AddressPresentation.children (Cell := Cell) (Addr := Addr) a)

theorem encodeSet_refineSet {L : Nat} (S : Finset (Cell L)) :
    encodeSet (Cell := Cell) (Addr := Addr) (SubstrateClass.refineSet (Cell := Cell) S) =
      addrRefineSet (Cell := Cell) (Addr := Addr)
        (encodeSet (Cell := Cell) (Addr := Addr) S) := by
  ext b
  constructor
  · intro hb
    have hdec : decode (Cell := Cell) (Addr := Addr) b ∈
        SubstrateClass.refineSet (Cell := Cell) S := by
      exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mp hb
    rcases Finset.mem_biUnion.mp hdec with ⟨p, hpS, hchild⟩
    have haddrChild : b ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr) p) := by
      have htmp : encode (Cell := Cell) (Addr := Addr)
          (decode (Cell := Cell) (Addr := Addr) b) ∈
            AddressPresentation.children (Cell := Cell) (Addr := Addr)
              (encode (Cell := Cell) (Addr := Addr) p) := by
        exact (IdealAddressEquiv.child_mem_children_iff
          (Cell := Cell) (Addr := Addr) p
          (decode (Cell := Cell) (Addr := Addr) b)).mp hchild
      rw [encode_decode (Cell := Cell) (Addr := Addr) b] at htmp
      exact htmp
    exact Finset.mem_biUnion.mpr ⟨
      encode (Cell := Cell) (Addr := Addr) p,
      (mem_encodeSet (Cell := Cell) (Addr := Addr)).mpr (by
        rw [decode_encode (Cell := Cell) (Addr := Addr) p]
        exact hpS),
      haddrChild⟩
  · intro hb
    rcases Finset.mem_biUnion.mp hb with ⟨a, haS, hchild⟩
    have hdecA : decode (Cell := Cell) (Addr := Addr) a ∈ S := by
      exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mp haS
    have hdecChild : decode (Cell := Cell) (Addr := Addr) b ∈
        SubstrateClass.children (decode (Cell := Cell) (Addr := Addr) a) := by
      exact (decode_child_mem_children_iff (Cell := Cell) (Addr := Addr) a b).mpr hchild
    have href : decode (Cell := Cell) (Addr := Addr) b ∈
        SubstrateClass.refineSet (Cell := Cell) S := by
      exact Finset.mem_biUnion.mpr ⟨
        decode (Cell := Cell) (Addr := Addr) a,
        hdecA,
        hdecChild⟩
    exact (mem_encodeSet (Cell := Cell) (Addr := Addr)).mpr href

theorem decodeSet_refineSet {L : Nat} (S : Finset (Addr L)) :
    decodeSet (Cell := Cell) (Addr := Addr)
      (addrRefineSet (Cell := Cell) (Addr := Addr) S) =
        SubstrateClass.refineSet (Cell := Cell)
          (decodeSet (Cell := Cell) (Addr := Addr) S) := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨b, hb, hbc⟩
    subst hbc
    rcases Finset.mem_biUnion.mp hb with ⟨a, haS, hchild⟩
    exact Finset.mem_biUnion.mpr ⟨
      decode (Cell := Cell) (Addr := Addr) a,
      (mem_decodeSet (Cell := Cell) (Addr := Addr)).mpr (by
        rw [encode_decode (Cell := Cell) (Addr := Addr) a]
        exact haS),
      (decode_child_mem_children_iff (Cell := Cell) (Addr := Addr) a b).mpr hchild⟩
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨p, hpS, hchild⟩
    have haddrP : encode (Cell := Cell) (Addr := Addr) p ∈ S := by
      exact (mem_decodeSet (Cell := Cell) (Addr := Addr)).mp hpS
    have haddrChild : encode (Cell := Cell) (Addr := Addr) c ∈
        AddressPresentation.children (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr) p) := by
      exact (IdealAddressEquiv.child_mem_children_iff
        (Cell := Cell) (Addr := Addr) p c).mp hchild
    exact Finset.mem_image.mpr ⟨
      encode (Cell := Cell) (Addr := Addr) c,
      Finset.mem_biUnion.mpr ⟨
        encode (Cell := Cell) (Addr := Addr) p,
        haddrP,
        haddrChild⟩,
      by exact decode_encode (Cell := Cell) (Addr := Addr) c⟩

def addrCoarsenSet {L : Nat} (S : Finset (Addr (L + 1))) : Finset (Addr L) :=
  S.image (AddressPresentation.parent (Cell := Cell) (Addr := Addr))

theorem decodeSet_coarsenSet {L : Nat} (S : Finset (Addr (L + 1))) :
    decodeSet (Cell := Cell) (Addr := Addr)
      (addrCoarsenSet (Cell := Cell) (Addr := Addr) S) =
        SubstrateClass.coarsenSet (Cell := Cell)
          (decodeSet (Cell := Cell) (Addr := Addr) S) := by
  ext p
  constructor
  · intro hp
    have henc : encode (Cell := Cell) (Addr := Addr) p ∈
        addrCoarsenSet (Cell := Cell) (Addr := Addr) S := by
      exact (mem_decodeSet (Cell := Cell) (Addr := Addr)).mp hp
    rcases Finset.mem_image.mp henc with ⟨b, hbS, hbpar⟩
    have hpar : p ∈ SubstrateClass.parents (decode (Cell := Cell) (Addr := Addr) b) := by
      have hEq : AddressPresentation.parent (Cell := Cell) (Addr := Addr)
          (encode (Cell := Cell) (Addr := Addr)
            (decode (Cell := Cell) (Addr := Addr) b)) =
          encode (Cell := Cell) (Addr := Addr) p := by
        rw [encode_decode (Cell := Cell) (Addr := Addr) b]
        exact hbpar
      exact (encode_parent_eq_iff
        (Cell := Cell) (Addr := Addr) p
        (decode (Cell := Cell) (Addr := Addr) b)).mpr hEq
    exact Finset.mem_biUnion.mpr ⟨
      decode (Cell := Cell) (Addr := Addr) b,
      (mem_decodeSet (Cell := Cell) (Addr := Addr)).mpr (by
        rw [encode_decode (Cell := Cell) (Addr := Addr) b]
        exact hbS),
      hpar⟩
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨c, hcS, hpar⟩
    have hencS : encode (Cell := Cell) (Addr := Addr) c ∈ S := by
      exact (mem_decodeSet (Cell := Cell) (Addr := Addr)).mp hcS
    have hparent : AddressPresentation.parent (Cell := Cell) (Addr := Addr)
        (encode (Cell := Cell) (Addr := Addr) c) =
      encode (Cell := Cell) (Addr := Addr) p := by
      exact (encode_parent_eq_iff (Cell := Cell) (Addr := Addr) p c).mp hpar
    have henc : encode (Cell := Cell) (Addr := Addr) p ∈
        addrCoarsenSet (Cell := Cell) (Addr := Addr) S := by
      exact Finset.mem_image.mpr ⟨
        encode (Cell := Cell) (Addr := Addr) c,
        hencS,
        hparent⟩
    exact (mem_decodeSet (Cell := Cell) (Addr := Addr)).mpr henc

theorem encodeSet_coarsenSet {L : Nat} (S : Finset (Cell (L + 1))) :
    encodeSet (Cell := Cell) (Addr := Addr)
      (SubstrateClass.coarsenSet (Cell := Cell) S) =
        addrCoarsenSet (Cell := Cell) (Addr := Addr)
          (encodeSet (Cell := Cell) (Addr := Addr) S) := by
  calc
    encodeSet (Cell := Cell) (Addr := Addr)
        (SubstrateClass.coarsenSet (Cell := Cell) S)
        = encodeSet (Cell := Cell) (Addr := Addr)
            (decodeSet (Cell := Cell) (Addr := Addr)
              (addrCoarsenSet (Cell := Cell) (Addr := Addr)
                (encodeSet (Cell := Cell) (Addr := Addr) S))) := by
            rw [decodeSet_coarsenSet, decodeSet_encodeSet]
    _ = addrCoarsenSet (Cell := Cell) (Addr := Addr)
          (encodeSet (Cell := Cell) (Addr := Addr) S) := by
          rw [encodeSet_decodeSet]


end IdealAddressEquiv

end CNNA.PillarA.ToC
