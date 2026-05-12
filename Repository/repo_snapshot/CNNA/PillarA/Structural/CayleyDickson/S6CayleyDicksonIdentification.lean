import CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema
import CNNA.PillarA.Foundation.MatrixNorms

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

def CanonicalTriadicMultiplicationCandidate
    (X : CayleyDicksonSource Cell T) : Prop :=
  (∀ κ η : ReducedRoleIndex,
      triadicOuterSchur X κ η =
        triadicOuterRawBlock X κ η - triadicOuterMediated X κ η) ∧
    triadicCenterMatrix X * triadicCenterInverse X = (1 : TriadicCenterBlock X) ∧
    triadicCenterInverse X * triadicCenterMatrix X = (1 : TriadicCenterBlock X)

theorem canonicalTriadicMultiplicationCandidate_of_octonionic
    (X : CayleyDicksonSource Cell T) :
    CanonicalTriadicMultiplicationCandidate X := by
  refine ⟨?_, ?_, ?_⟩
  · exact (octonionicSeedOf X).outerFormula
  · exact (octonionicSeedOf X).centerLeftInverse
  · exact (octonionicSeedOf X).centerRightInverse

def DualCompatibleConjugationCandidate : Prop :=
  (∀ ρ : PreNumericSectorRole,
      PreNumericSectorRole.dual (PreNumericSectorRole.dual ρ) = ρ) ∧
    (∀ K : CoupledSectorKind,
      CoupledSectorKind.dual (CoupledSectorKind.dual K) = K) ∧
    (∀ κ : ReducedRoleIndex,
      ReducedRoleIndex.dual (ReducedRoleIndex.dual κ) = κ) ∧
    (∀ τ : TriadicRoleIndex,
      TriadicRoleIndex.dual (TriadicRoleIndex.dual τ) = τ) ∧
    (∀ ρ : PreNumericSectorRole,
      PreNumericSectorRole.toCoupledSectorKind (PreNumericSectorRole.dual ρ) =
        CoupledSectorKind.dual (PreNumericSectorRole.toCoupledSectorKind ρ)) ∧
    (∀ κ : ReducedRoleIndex,
      PreNumericSectorRole.dual (ReducedRoleIndex.toRole κ) =
        ReducedRoleIndex.toRole (ReducedRoleIndex.dual κ)) ∧
    (∀ τ : TriadicRoleIndex,
      PreNumericSectorRole.dual (TriadicRoleIndex.toRole τ) =
        TriadicRoleIndex.toRole (TriadicRoleIndex.dual τ))

theorem dualCompatibleConjugationCandidate_closed :
    DualCompatibleConjugationCandidate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PreNumericSectorRole.dual_involutive
  · exact CoupledSectorKind.dual_involutive
  · exact ReducedRoleIndex.dual_involutive
  · exact TriadicRoleIndex.dual_involutive
  · exact PreNumericSectorRole.toCoupledSectorKind_dual
  · exact ReducedRoleIndex.toRole_dual
  · exact TriadicRoleIndex.toRole_dual

def DiagonalNormSqNonnegCandidate
    (X : CayleyDicksonSource Cell T) : Prop :=
  0 ≤ MatrixNorm.Analytic.frobSq X.schur.brightBrightSchur ∧
    0 ≤ MatrixNorm.Analytic.frobSq (triadicCenterMatrix X) ∧
    0 ≤ MatrixNorm.Analytic.frobSq X.schur.darkDarkSchur

theorem diagonalNormSqNonnegCandidate_closed
    (X : CayleyDicksonSource Cell T) :
    DiagonalNormSqNonnegCandidate X := by
  refine ⟨?_, ?_, ?_⟩
  · exact MatrixNorm.Analytic.frobSq_nonneg X.schur.brightBrightSchur
  · exact MatrixNorm.Analytic.frobSq_nonneg (triadicCenterMatrix X)
  · exact MatrixNorm.Analytic.frobSq_nonneg X.schur.darkDarkSchur

structure CayleyDicksonIdentificationSeed
    (X : CayleyDicksonSource Cell T) where
  octonionic : OctonionicSeed X
  octonionic_eq : octonionic = octonionicSeedOf X
  canonicalTriadicMultiplication : CanonicalTriadicMultiplicationCandidate X
  dualCompatibleConjugation : DualCompatibleConjugationCandidate
  diagonalNormSqNonneg : DiagonalNormSqNonnegCandidate X

def cayleyDicksonIdentificationSeedOf
    (X : CayleyDicksonSource Cell T) :
    CayleyDicksonIdentificationSeed X where
  octonionic := octonionicSeedOf X
  octonionic_eq := rfl
  canonicalTriadicMultiplication :=
    canonicalTriadicMultiplicationCandidate_of_octonionic X
  dualCompatibleConjugation :=
    dualCompatibleConjugationCandidate_closed
  diagonalNormSqNonneg :=
    diagonalNormSqNonnegCandidate_closed X

structure CayleyDicksonRemainingResearch where
  idealHasCanonicalOctonionicAlgebra : DirectedFamily (Cell := Cell) → Prop
  positiveDefiniteNormSq : CayleyDicksonSource Cell T → Prop
  alternativeLaw : CayleyDicksonSource Cell T → Prop
  divisionFromNormSq : CayleyDicksonSource Cell T → Prop
  externalHurwitzCompatibility : CayleyDicksonSource Cell T → Prop

def CayleyDicksonRemainingResearch.toCanonicalIdealAlgebraizationResearchSlot
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T)) :
    CanonicalIdealAlgebraizationResearchSlot (Cell := Cell) (T := T) where
  idealHasCanonicalOctonionicAlgebra := remaining.idealHasCanonicalOctonionicAlgebra
  canonicalTriadicMultiplication :=
    fun X => CanonicalTriadicMultiplicationCandidate X
  dualCompatibleConjugation :=
    fun _ => DualCompatibleConjugationCandidate
  positiveDefiniteNormSq := remaining.positiveDefiniteNormSq
  alternativeLaw := remaining.alternativeLaw
  divisionFromNormSq := remaining.divisionFromNormSq
  externalHurwitzCompatibility := remaining.externalHurwitzCompatibility

def CayleyDicksonRemainingResearch.toResearchSchema
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (functorialSlot :
      FunctorialApproximantCompatibilityResearchSlot (Cell := Cell) (T := T))
    (regimeSlot : RegimeRecoveryResearchSlot (Cell := Cell) (T := T)) :
    S6ResearchSchema (Cell := Cell) (T := T) where
  canonicalIdealAlgebraization :=
    remaining.toCanonicalIdealAlgebraizationResearchSlot
  functorialApproximantCompatibility := functorialSlot
  regimeRecovery := regimeSlot

theorem cayleyDickson_seed_canonicalTriadicMultiplication
    (X : CayleyDicksonSource Cell T) :
    CanonicalTriadicMultiplicationCandidate X := by
  exact (cayleyDicksonIdentificationSeedOf X).canonicalTriadicMultiplication

theorem cayleyDickson_seed_dualCompatibleConjugation
    (X : CayleyDicksonSource Cell T) :
    DualCompatibleConjugationCandidate := by
  exact (cayleyDicksonIdentificationSeedOf X).dualCompatibleConjugation

theorem cayleyDickson_seed_diagonalNormSqNonneg
    (X : CayleyDicksonSource Cell T) :
    DiagonalNormSqNonnegCandidate X := by
  exact (cayleyDicksonIdentificationSeedOf X).diagonalNormSqNonneg

theorem toCanonicalIdealAlgebraizationResearchSlot_canonicalTriadicMultiplication
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlot).canonicalTriadicMultiplication X := by
  exact canonicalTriadicMultiplicationCandidate_of_octonionic X

theorem toCanonicalIdealAlgebraizationResearchSlot_dualCompatibleConjugation
    (remaining : CayleyDicksonRemainingResearch (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    (remaining.toCanonicalIdealAlgebraizationResearchSlot).dualCompatibleConjugation X := by
  exact dualCompatibleConjugationCandidate_closed

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
