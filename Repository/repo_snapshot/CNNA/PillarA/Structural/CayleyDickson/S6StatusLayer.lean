import CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

def OnticPrimacyTheorem
    (X : CayleyDicksonSource Cell T) : Prop :=
  T = X.ideal.truncate X.cutoff

def PrenumericSectorTheorem
    (X : CayleyDicksonSource Cell T) : Prop :=
  X.regularization.split = X.split ∧
    X.schur.split = X.split ∧
    2 ≤ X.regularization.selectedSectorCount ∧
    X.regularization.selectedBrightCarrier ∪
        X.regularization.selectedBoundaryCarrier ∪
        X.regularization.selectedDarkCarrier =
      T.carrier X.regularization.selectedLevel

def ScalarAxisStatusSeparationTheorem
    (X : CayleyDicksonSource Cell T) : Prop :=
  X.regularization.regularizationShift =
      X.regularization.regularizationPolicy.canonicalShift
        X.regularization.comparisonOperator ∧
    X.regularization.epsilon ≤ X.regularization.regularizationShift ∧
    X.regularization.stabilizedOperator =
      X.regularization.rawBoundaryOperator +
        X.regularization.regularizationShift •
          (1 :
            Matrix X.regularization.boundaryVertex
              X.regularization.boundaryVertex ℝ)

structure S6TheoremLayer
    (X : CayleyDicksonSource Cell T) : Prop where
  onticPrimacy : OnticPrimacyTheorem X
  prenumericSector : PrenumericSectorTheorem X
  scalarAxisStatusSeparation : ScalarAxisStatusSeparationTheorem X

theorem onticPrimacy_of_additionalFinding
    (X : CayleyDicksonSource Cell T)
    (h : S6AdditionalFinding X) :
    OnticPrimacyTheorem X := by
  exact h.idealPrimacy

theorem prenumericSector_of_additionalFinding
    (X : CayleyDicksonSource Cell T)
    (h : S6AdditionalFinding X) :
    PrenumericSectorTheorem X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.prenumericRegularizationReuse
  · exact h.prenumericCouplingReuse
  · exact h.selectedSectorCountGeTwo
  · exact h.selectedSectorCover

theorem scalarAxisStatusSeparation_of_additionalFinding
    (X : CayleyDicksonSource Cell T)
    (h : S6AdditionalFinding X) :
    ScalarAxisStatusSeparationTheorem X := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.shiftFromExecComparison
  · exact h.shiftDominatesEpsilon
  · exact h.stabilizedOperatorFormula

theorem s6_theorem_layer
    (X : CayleyDicksonSource Cell T) :
    S6TheoremLayer X := by
  let h := s6_additional_finding X
  refine ⟨?_, ?_, ?_⟩
  · exact onticPrimacy_of_additionalFinding X h
  · exact prenumericSector_of_additionalFinding X h
  · exact scalarAxisStatusSeparation_of_additionalFinding X h

def OctonionicIdealConjecture
    (idealHasCanonicalOctonionicAlgebra : DirectedFamily (Cell := Cell) → Prop)
    (X : CayleyDicksonSource Cell T) : Prop :=
  OnticPrimacyTheorem X ∧ idealHasCanonicalOctonionicAlgebra X.ideal

def ApproximantProjectionConjecture
    (approximantsExposeProjectiveSubregimes :
      CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T) : Prop :=
  OnticPrimacyTheorem X ∧
    PrenumericSectorTheorem X ∧
    approximantsExposeProjectiveSubregimes X

def CayleyDicksonLiftConjecture
    (realToIdealLimitRealizesAlgebraLift :
      CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T) : Prop :=
  OnticPrimacyTheorem X ∧
    PrenumericSectorTheorem X ∧
    ScalarAxisStatusSeparationTheorem X ∧
    realToIdealLimitRealizesAlgebraLift X

structure S6ConjectureLayer
    (X : CayleyDicksonSource Cell T) where
  octonionicIdeal : Prop
  approximantProjection : Prop
  cayleyDicksonLift : Prop

def s6_conjecture_layer
    (idealHasCanonicalOctonionicAlgebra : DirectedFamily (Cell := Cell) → Prop)
    (approximantsExposeProjectiveSubregimes :
      CayleyDicksonSource Cell T → Prop)
    (realToIdealLimitRealizesAlgebraLift :
      CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T) :
    S6ConjectureLayer X where
  octonionicIdeal :=
    OctonionicIdealConjecture
      idealHasCanonicalOctonionicAlgebra X
  approximantProjection :=
    ApproximantProjectionConjecture
      approximantsExposeProjectiveSubregimes X
  cayleyDicksonLift :=
    CayleyDicksonLiftConjecture
      realToIdealLimitRealizesAlgebraLift X

def CanonicalIdealAlgebraizationObligation
    (idealHasCanonicalOctonionicAlgebra : DirectedFamily (Cell := Cell) → Prop)
    (X : CayleyDicksonSource Cell T) : Prop :=
  idealHasCanonicalOctonionicAlgebra X.ideal

def FunctorialApproximantCompatibilityObligation
    (approximantsExposeProjectiveSubregimes :
      CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T) : Prop :=
  approximantsExposeProjectiveSubregimes X

def RegimeRecoveryObligation
    (realToIdealLimitRealizesAlgebraLift :
      CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T) : Prop :=
  realToIdealLimitRealizesAlgebraLift X

structure S6OpenProofObligations
    (X : CayleyDicksonSource Cell T) where
  canonicalIdealAlgebraization : Prop
  functorialApproximantCompatibility : Prop
  regimeRecovery : Prop

def s6_open_proof_obligations
    (idealHasCanonicalOctonionicAlgebra : DirectedFamily (Cell := Cell) → Prop)
    (approximantsExposeProjectiveSubregimes :
      CayleyDicksonSource Cell T → Prop)
    (realToIdealLimitRealizesAlgebraLift :
      CayleyDicksonSource Cell T → Prop)
    (X : CayleyDicksonSource Cell T) :
    S6OpenProofObligations X where
  canonicalIdealAlgebraization :=
    CanonicalIdealAlgebraizationObligation
      idealHasCanonicalOctonionicAlgebra X
  functorialApproximantCompatibility :=
    FunctorialApproximantCompatibilityObligation
      approximantsExposeProjectiveSubregimes X
  regimeRecovery :=
    RegimeRecoveryObligation
      realToIdealLimitRealizesAlgebraLift X

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
