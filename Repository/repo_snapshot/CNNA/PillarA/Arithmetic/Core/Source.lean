import CNNA.PillarA.ToC.BuildAll
import CNNA.PillarA.Finite.ChannelSeed
import CNNA.PillarA.Coupling.MultiSchur

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Coupling

universe u

inductive ArithmeticSourceKind where
  | reference
  | variation
  deriving DecidableEq, Repr

inductive ArithmeticStrandKind where
  | exec
  | complexMirror
  deriving DecidableEq, Repr

structure ArithmeticSource (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  kind : ArithmeticSourceKind
  toc : ToCStrongOf Cell
  concretePolicy : ConcretePolicyOf
  truncation_eq_toc : T = toc.approximant concretePolicy
  channel : ChannelSeedStrong Cell T
  multiSchur : MultiSchurStrong Cell T

abbrev ArithmeticSourceOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ArithmeticSource (Cell := Cell) T

namespace ArithmeticSource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev finiteApproximant (S : ArithmeticSource Cell T) : ApproximantStrong Cell T :=
  S.multiSchur.approximant

abbrev dtn (S : ArithmeticSource Cell T) : DtNStrong Cell T :=
  S.multiSchur.binary

abbrev generalizedDtN (S : ArithmeticSource Cell T) : GeneralizedDtNStrong Cell T :=
  S.multiSchur.generalized

abbrev coupling (S : ArithmeticSource Cell T) : MultiSchurStrong Cell T :=
  S.multiSchur

abbrev channelSeed (S : ArithmeticSource Cell T) : ChannelSeedStrong Cell T :=
  S.channel

abbrev spectralExec (S : ArithmeticSource Cell T) : SpectralDecompositionStrong Cell T :=
  S.channel.stateSpace.spectral

abbrev spectralBridge (S : ArithmeticSource Cell T) : SpectralBridgeStrong Cell T :=
  S.channel.stateSpace.spectralBridge

abbrev spectralMirror (S : ArithmeticSource Cell T) : SpectralDecompositionCStrong Cell T :=
  S.channel.stateSpace.mirror

abbrev execStrand (_ : ArithmeticSource Cell T) : ArithmeticStrandKind :=
  ArithmeticStrandKind.exec

abbrev complexMirrorStrand (_ : ArithmeticSource Cell T) : ArithmeticStrandKind :=
  ArithmeticStrandKind.complexMirror

theorem finiteApproximant_eq_multiSchur (S : ArithmeticSource Cell T) :
    S.finiteApproximant = S.multiSchur.approximant := by
  rfl

theorem dtn_eq_multiSchur_binary (S : ArithmeticSource Cell T) :
    S.dtn = S.multiSchur.binary := by
  rfl

theorem generalizedDtN_eq_multiSchur_generalized (S : ArithmeticSource Cell T) :
    S.generalizedDtN = S.multiSchur.generalized := by
  rfl

theorem coupling_eq_multiSchur (S : ArithmeticSource Cell T) :
    S.coupling = S.multiSchur := by
  rfl

theorem channelSeed_eq_channel (S : ArithmeticSource Cell T) :
    S.channelSeed = S.channel := by
  rfl

theorem spectralExec_eq_channel_spectral (S : ArithmeticSource Cell T) :
    S.spectralExec = S.channel.stateSpace.spectral := by
  rfl

theorem spectralBridge_eq_channel_bridge (S : ArithmeticSource Cell T) :
    S.spectralBridge = S.channel.stateSpace.spectralBridge := by
  rfl

theorem spectralMirror_eq_channel_mirror (S : ArithmeticSource Cell T) :
    S.spectralMirror = S.channel.stateSpace.mirror := by
  rfl

theorem execStrand_is_exec (S : ArithmeticSource Cell T) :
    S.execStrand = ArithmeticStrandKind.exec := by
  rfl

theorem complexMirrorStrand_is_complexMirror (S : ArithmeticSource Cell T) :
    S.complexMirrorStrand = ArithmeticStrandKind.complexMirror := by
  rfl

theorem truncation_eq_toc_approximant (S : ArithmeticSource Cell T) :
    T = S.toc.approximant S.concretePolicy :=
  S.truncation_eq_toc

end ArithmeticSource

namespace StrengtheningAR1

open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.Finite.StrengtheningS9
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6
open CNNA.PillarA.Coupling.StrengtheningS7

abbrev ReferenceArithmeticSourceOf (b : Nat) (p : ConcretePolicyOf) :=
  ArithmeticSourceOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p)

abbrev VariationArithmeticSourceOf (β : Nat → Nat) (p : ConcretePolicyOf) :=
  ArithmeticSourceOf (VariationIdealCellOf β) ((variationToC β).approximant p)

def referenceArithmeticSource (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp] :
    ReferenceArithmeticSourceOf b p where
  kind := ArithmeticSourceKind.reference
  toc := referenceToC b
  concretePolicy := p
  truncation_eq_toc := rfl
  channel := referenceFullChannelSeed b p wp
  multiSchur := referenceFullMultiSchur b p wp rp

def variationArithmeticSource (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    [VariationInterfaceEliminationData β p wp rp] :
    VariationArithmeticSourceOf β p where
  kind := ArithmeticSourceKind.variation
  toc := variationToC β
  concretePolicy := p
  truncation_eq_toc := rfl
  channel := variationFullChannelSeed β p wp
  multiSchur := variationFullMultiSchur β p wp rp

theorem referenceArithmeticSource_kind (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp] :
    (referenceArithmeticSource b p wp rp).kind = ArithmeticSourceKind.reference := by
  rfl

theorem variationArithmeticSource_kind (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    [VariationInterfaceEliminationData β p wp rp] :
    (variationArithmeticSource β p wp rp).kind = ArithmeticSourceKind.variation := by
  rfl

theorem referenceArithmeticSource_toc (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp] :
    (referenceArithmeticSource b p wp rp).toc = referenceToC b := by
  rfl

theorem variationArithmeticSource_toc (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    [VariationInterfaceEliminationData β p wp rp] :
    (variationArithmeticSource β p wp rp).toc = variationToC β := by
  rfl

theorem referenceArithmeticSource_channel (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp] :
    (referenceArithmeticSource b p wp rp).channel = referenceFullChannelSeed b p wp := by
  rfl

theorem variationArithmeticSource_channel (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    [VariationInterfaceEliminationData β p wp rp] :
    (variationArithmeticSource β p wp rp).channel = variationFullChannelSeed β p wp := by
  rfl

theorem referenceArithmeticSource_multiSchur (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp] :
    (referenceArithmeticSource b p wp rp).multiSchur =
      referenceFullMultiSchur b p wp rp := by
  rfl

theorem variationArithmeticSource_multiSchur (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    [VariationInterfaceEliminationData β p wp rp] :
    (variationArithmeticSource β p wp rp).multiSchur =
      variationFullMultiSchur β p wp rp := by
  rfl

end StrengtheningAR1

end CNNA.PillarA.Arithmetic
