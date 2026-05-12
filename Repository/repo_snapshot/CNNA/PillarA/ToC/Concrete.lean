import CNNA.PillarA.ToC.IdealAddressEquiv
import CNNA.PillarA.ToC.ConcreteIdeal
import CNNA.PillarA.Foundation.Determinism
import CNNA.PillarA.Foundation.LevelVariableSubstrate

set_option autoImplicit false

namespace CNNA.PillarA.ToC

open CNNA.PillarA.Foundation

universe u v

structure ConcretePolicy where
  L_max : Nat
  deriving DecidableEq, Repr

abbrev ConcretePolicyOf := ConcretePolicy

namespace ConcretePolicy

def key (p : ConcretePolicy) : Nat :=
  p.L_max

theorem key_eq_L_max (p : ConcretePolicyOf) :
    p.key = p.L_max := by
  rfl

end ConcretePolicy

structure TruncatedFamily (Cell : Nat → Type u) [SubstrateClass Cell] where
  cutoff : Nat
  carrier : ∀ L : Nat, Finset (Cell L)
  rooted : carrier 0 = Σ₀[Cell]
  forward : ∀ L : Nat, L < cutoff →
    carrier (L + 1) ⊆ RefineSetOf (Cell := Cell) (carrier L)

abbrev TruncatedFamilyOf
    (Cell : Nat → Type u) [SubstrateClass Cell] :=
  TruncatedFamily Cell

namespace TruncatedFamily

variable {Cell : Nat → Type u} [SubstrateClass Cell]

@[ext] theorem ext (S T : TruncatedFamily Cell)
    (hcutoff : S.cutoff = T.cutoff)
    (hcarrier : ∀ L : Nat, S.carrier L = T.carrier L) :
    S = T := by
  cases S with
  | mk cutoffS carrierS rootedS forwardS =>
    cases T with
    | mk cutoffT carrierT rootedT forwardT =>
      simp at hcutoff
      subst hcutoff
      have hcar : carrierS = carrierT := by
        funext L
        exact hcarrier L
      subst hcar
      have hrooted : rootedS = rootedT := by
        exact Subsingleton.elim _ _
      subst hrooted
      have hforward : forwardS = forwardT := by
        exact Subsingleton.elim _ _
      subst hforward
      rfl

def slice (T : TruncatedFamily Cell) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := T.carrier L }

theorem slice_level (T : TruncatedFamily Cell) (L : Nat) :
    (T.slice L).level = L := by
  rfl

theorem slice_carrier (T : TruncatedFamily Cell) (L : Nat) :
    (T.slice L).carrier = T.carrier L := by
  rfl

theorem root_mem (T : TruncatedFamily Cell) :
    SubstrateClass.root (Cell := Cell) ∈ T.carrier 0 := by
  rw [T.rooted]
  exact SubstrateClass.root_mem_rootLayer (Cell := Cell)

theorem zero_slice_nonempty (T : TruncatedFamily Cell) :
    (T.carrier 0).Nonempty := by
  exact ⟨SubstrateClass.root (Cell := Cell), T.root_mem⟩

def topSlice (T : TruncatedFamily Cell) : LayerSlice Cell :=
  T.slice T.cutoff

theorem topSlice_level (T : TruncatedFamily Cell) :
    T.topSlice.level = T.cutoff := by
  rfl

theorem topSlice_carrier (T : TruncatedFamily Cell) :
    T.topSlice.carrier = T.carrier T.cutoff := by
  rfl

end TruncatedFamily

namespace DirectedFamily

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def truncate (F : DirectedFamily (Cell := Cell)) (N : Nat) :
    TruncatedFamily Cell where
  cutoff := N
  carrier := fun L => if h : L ≤ N then F.carrier L else ∅
  rooted := by
    have h0 : 0 ≤ N := Nat.zero_le N
    simpa [h0] using F.rooted
  forward := by
    intro L hLt
    have hL : L ≤ N := Nat.le_of_lt hLt
    have hLs : L + 1 ≤ N := Nat.succ_le_of_lt hLt
    simpa [hL, hLs] using F.forward L

theorem truncate_cutoff (F : DirectedFamily (Cell := Cell)) (N : Nat) :
    (F.truncate N).cutoff = N := by
  rfl

theorem truncate_carrier_of_le (F : DirectedFamily (Cell := Cell))
    {L N : Nat} (h : L ≤ N) :
    (F.truncate N).carrier L = F.carrier L := by
  simp [truncate, h]

theorem truncate_carrier_of_gt (F : DirectedFamily (Cell := Cell))
    {L N : Nat} (h : N < L) :
    (F.truncate N).carrier L = ∅ := by
  simp [truncate, Nat.not_le.mpr h]

theorem truncate_topSlice_carrier (F : DirectedFamily (Cell := Cell)) (N : Nat) :
    (F.truncate N).topSlice.carrier = F.carrier N := by
  change (F.truncate N).carrier N = F.carrier N
  exact truncate_carrier_of_le (F := F) (L := N) (N := N) le_rfl

def approximantFamily (F : DirectedFamily (Cell := Cell)) :
    KeyedFamily ConcretePolicyOf Nat (TruncatedFamilyOf Cell) :=
  KeyedFamily.mkFromKey ConcretePolicy.key (fun N => F.truncate N)

theorem approximantFamily_key (F : DirectedFamily (Cell := Cell)) (p : ConcretePolicyOf) :
    (F.approximantFamily).keyOf p = p.L_max := by
  rfl

theorem approximantFamily_val (F : DirectedFamily (Cell := Cell)) (p : ConcretePolicy) :
    (F.approximantFamily).val p = F.truncate p.L_max := by
  rfl

end DirectedFamily

section EquivalenceTransport

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]

abbrev AddressTruncatedFamily
    (Cell : Nat → Type u) (Addr : Nat → Type v)
    [SubstrateClass Cell] [IdealAddressEquiv Cell Addr] :=
  @TruncatedFamily Addr (AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr))

namespace TruncatedFamily

def encode (T : TruncatedFamily Cell) :
    AddressTruncatedFamily Cell Addr := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine
    { cutoff := T.cutoff
      carrier := fun L => IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr) (T.carrier L)
      rooted := ?_
      forward := ?_ }
  · ext a
    rw [T.rooted, IdealAddressEquiv.encodeSet_rootLayer]
    constructor
    · intro ha
      have hroot : a = SubstrateClass.root (Cell := Addr) := by
        simpa [IdealAddressEquiv.addrRootLayer] using ha
      exact (SubstrateClass.mem_rootLayer_iff (Cell := Addr) a).mpr hroot
    · intro ha
      have hroot : a = SubstrateClass.root (Cell := Addr) := by
        exact (SubstrateClass.mem_rootLayer_iff (Cell := Addr) a).mp ha
      simpa [IdealAddressEquiv.addrRootLayer] using hroot
  · intro L hL a ha
    have hdec : IdealAddressEquiv.decode (Cell := Cell) (Addr := Addr) a ∈ T.carrier (L + 1) := by
      exact (IdealAddressEquiv.mem_encodeSet (Cell := Cell) (Addr := Addr)).mp ha
    have href : IdealAddressEquiv.decode (Cell := Cell) (Addr := Addr) a ∈
        SubstrateClass.refineSet (Cell := Cell) (T.carrier L) :=
      T.forward L hL hdec
    have henc : a ∈ IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr)
        (RefineSetOf (Cell := Cell) (T.carrier L)) := by
      exact (IdealAddressEquiv.mem_encodeSet (Cell := Cell) (Addr := Addr)).mpr href
    rw [IdealAddressEquiv.encodeSet_refineSet (Cell := Cell) (Addr := Addr) (S := T.carrier L)] at henc
    simpa [SubstrateClass.refineSet, AddressPresentation.addressSubstrate,
      IdealAddressEquiv.addrRefineSet] using henc

def decode (T : AddressTruncatedFamily Cell Addr) :
    TruncatedFamily Cell := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine
    { cutoff := T.cutoff
      carrier := fun L => IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr) (T.carrier L)
      rooted := ?_
      forward := ?_ }
  · have hroot : T.carrier 0 = IdealAddressEquiv.addrRootLayer (Cell := Cell) (Addr := Addr) := by
      simpa [SubstrateClass.rootLayer, IdealAddressEquiv.addrRootLayer] using T.rooted
    rw [hroot]
    exact IdealAddressEquiv.decodeSet_rootLayer (Cell := Cell) (Addr := Addr)
  · intro L hL c hc
    have henc : IdealAddressEquiv.encode (Cell := Cell) (Addr := Addr) c ∈ T.carrier (L + 1) := by
      exact (IdealAddressEquiv.mem_decodeSet (Cell := Cell) (Addr := Addr)).mp hc
    have href : IdealAddressEquiv.encode (Cell := Cell) (Addr := Addr) c ∈
        IdealAddressEquiv.addrRefineSet (Cell := Cell) (Addr := Addr) (T.carrier L) := by
      exact T.forward L hL henc
    have hdec : c ∈ IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr)
        (IdealAddressEquiv.addrRefineSet (Cell := Cell) (Addr := Addr) (T.carrier L)) := by
      exact (IdealAddressEquiv.mem_decodeSet (Cell := Cell) (Addr := Addr)).mpr href
    rw [IdealAddressEquiv.decodeSet_refineSet (Cell := Cell) (Addr := Addr) (S := T.carrier L)] at hdec
    simpa [SubstrateClass.refineSet, AddressPresentation.addressSubstrate,
      IdealAddressEquiv.addrRefineSet] using hdec

theorem decode_encode (T : TruncatedFamily Cell) :
    TruncatedFamily.decode (Cell := Cell) (Addr := Addr)
      (TruncatedFamily.encode (Cell := Cell) (Addr := Addr) T) = T := by
  refine TruncatedFamily.ext _ _ ?_ ?_
  · simp [TruncatedFamily.decode, TruncatedFamily.encode]
  · intro L
    change IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr)
      (IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr) (T.carrier L)) = T.carrier L
    exact
      (IdealAddressEquiv.decodeSet_encodeSet (Cell := Cell) (Addr := Addr) (S := T.carrier L))

theorem encode_decode (T : AddressTruncatedFamily Cell Addr) :
    TruncatedFamily.encode (Cell := Cell) (Addr := Addr)
      (TruncatedFamily.decode (Cell := Cell) (Addr := Addr) T) = T := by
  letI : SubstrateClass Addr :=
    AddressPresentation.addressSubstrate (Cell := Cell) (Addr := Addr)
  refine TruncatedFamily.ext _ _ ?_ ?_
  · simp [TruncatedFamily.decode, TruncatedFamily.encode]
  · intro L
    change IdealAddressEquiv.encodeSet (Cell := Cell) (Addr := Addr)
      (IdealAddressEquiv.decodeSet (Cell := Cell) (Addr := Addr) (T.carrier L)) = T.carrier L
    exact
      (IdealAddressEquiv.encodeSet_decodeSet (Cell := Cell) (Addr := Addr) (S := T.carrier L))

end TruncatedFamily

namespace DirectedFamily

def addressApproximantFamily (F : DirectedFamily (Cell := Cell)) :
    KeyedFamily ConcretePolicyOf Nat (AddressTruncatedFamily Cell Addr) :=
  KeyedFamily.mkFromKey ConcretePolicy.key
    (fun N => TruncatedFamily.encode (Cell := Cell) (Addr := Addr) (F.truncate N))

theorem addressApproximantFamily_val (F : DirectedFamily (Cell := Cell))
    (p : ConcretePolicy) :
    (DirectedFamily.addressApproximantFamily (Cell := Cell) (Addr := Addr) F).val p =
      TruncatedFamily.encode (Cell := Cell) (Addr := Addr) (F.truncate p.L_max) := by
  rfl

end DirectedFamily

end EquivalenceTransport

structure ToCStrong (Cell : Nat → Type u) [SubstrateClass Cell] where
  ideal : DirectedFamily (Cell := Cell)
  concrete : KeyedFamily ConcretePolicy Nat (TruncatedFamily Cell)
  concrete_isCanonical : concrete = ideal.approximantFamily

abbrev ToCStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell] :=
  ToCStrong Cell

namespace ToCStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def ofIdeal (F : DirectedFamily (Cell := Cell)) : ToCStrongOf Cell where
  ideal := F
  concrete := F.approximantFamily
  concrete_isCanonical := rfl

theorem ofIdeal_ideal (F : DirectedFamily (Cell := Cell)) :
    (ToCStrong.ofIdeal F).ideal = F := by
  rfl

theorem ofIdeal_concrete (F : DirectedFamily (Cell := Cell)) :
    (ToCStrong.ofIdeal F).concrete = F.approximantFamily := by
  rfl

def approximant (T : ToCStrongOf Cell) (p : ConcretePolicyOf) : TruncatedFamilyOf Cell :=
  T.concrete.val p

theorem approximant_eq_truncate (T : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    T.approximant p = T.ideal.truncate p.L_max := by
  rw [ToCStrong.approximant, T.concrete_isCanonical]
  rfl

end ToCStrong

section ToCStrongTransport

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [IdealAddressEquiv Cell Addr]

namespace ToCStrong

def addressedConcrete (T : ToCStrongOf Cell) :
    KeyedFamily ConcretePolicyOf Nat (AddressTruncatedFamily Cell Addr) :=
  DirectedFamily.addressApproximantFamily (Cell := Cell) (Addr := Addr) T.ideal

theorem addressedConcrete_val (T : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    (ToCStrong.addressedConcrete (Cell := Cell) (Addr := Addr) T).val p =
      TruncatedFamily.encode (Cell := Cell) (Addr := Addr) (T.ideal.truncate p.L_max) := by
  rfl

end ToCStrong

end ToCStrongTransport

section StrengtheningS4

abbrev VariationIdealCellOf (β : Nat → Nat) (L : Nat) : Type :=
  LevelVariableSubstrate.LevelVariableCell β L

def variationThread (β : Nat → Nat) : IdealThread (VariationIdealCellOf β) :=
  LevelVariableSubstrate.zeroThread β

def variationFamily (β : Nat → Nat) : DirectedFamily (Cell := VariationIdealCellOf β) :=
  (variationThread β).family

theorem variationFamily_rooted (β : Nat → Nat) :
    (variationFamily β).carrier 0 = SubstrateClass.rootLayer (Cell := VariationIdealCellOf β) := by
  exact (variationThread β).rooted_carrier

abbrev ReferenceToCStrongOf (b : Nat) :=
  ToCStrongOf (ConcreteIdeal.ReferenceCell b)

abbrev VariationToCStrongOf (β : Nat → Nat) :=
  ToCStrongOf (VariationIdealCellOf β)

def referenceToC (b : Nat) : ReferenceToCStrongOf b :=
  ToCStrong.ofIdeal (ConcreteIdeal.referenceFamily b)

def variationToC (β : Nat → Nat) : VariationToCStrongOf β :=
  ToCStrong.ofIdeal (variationFamily β)

theorem referenceToC_ideal (b : Nat) :
    (referenceToC b).ideal = ConcreteIdeal.referenceFamily b := by
  rfl

theorem variationToC_ideal (β : Nat → Nat) :
    (variationToC β).ideal = variationFamily β := by
  rfl

theorem referenceToC_approximant_eq_truncate (b : Nat) (p : ConcretePolicyOf) :
    (referenceToC b).approximant p =
      (ConcreteIdeal.referenceFamily b).truncate p.L_max := by
  exact ToCStrong.approximant_eq_truncate (T := referenceToC b) p

theorem variationToC_approximant_eq_truncate (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variationToC β).approximant p =
      (variationFamily β).truncate p.L_max := by
  exact ToCStrong.approximant_eq_truncate (T := variationToC β) p

def referenceAddressedConcrete (b : Nat) :
    KeyedFamily ConcretePolicyOf Nat
      (AddressTruncatedFamily (ConcreteIdeal.ReferenceCell b) (ConcreteIdeal.ReferenceAddr b)) :=
  ToCStrong.addressedConcrete
    (Cell := ConcreteIdeal.ReferenceCell b)
    (Addr := ConcreteIdeal.ReferenceAddr b)
    (referenceToC b)

theorem referenceAddressedConcrete_val (b : Nat) (p : ConcretePolicyOf) :
    (referenceAddressedConcrete b).val p =
      TruncatedFamily.encode
        (Cell := ConcreteIdeal.ReferenceCell b)
        (Addr := ConcreteIdeal.ReferenceAddr b)
        ((ConcreteIdeal.referenceFamily b).truncate p.L_max) := by
  rfl

end StrengtheningS4

end CNNA.PillarA.ToC
