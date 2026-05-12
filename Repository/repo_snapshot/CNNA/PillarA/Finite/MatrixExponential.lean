import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import CNNA.PillarA.Finite.StateSpace

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure MatrixExponentialStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : StateSpaceStrong Cell T

abbrev MatrixExponentialStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  MatrixExponentialStrong (Cell := Cell) T

namespace MatrixExponentialStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (E F : MatrixExponentialStrong Cell T)
    (hsource : E.source = F.source) :
    E = F := by
  cases E with
  | mk sourceE =>
      cases F with
      | mk sourceF =>
          cases hsource
          rfl

def ofStateSpace (S : StateSpaceStrong Cell T) : MatrixExponentialStrong Cell T where
  source := S

def cast (h : T = U) (E : MatrixExponentialStrong Cell T) :
    MatrixExponentialStrong Cell U := by
  cases h
  exact E

theorem cast_rfl (E : MatrixExponentialStrong Cell T) :
    cast (Cell := Cell) rfl E = E := by
  rfl

abbrev stateSpace (E : MatrixExponentialStrong Cell T) : StateSpaceStrong Cell T :=
  E.source

abbrev spectralBridge (E : MatrixExponentialStrong Cell T) : SpectralBridgeStrong Cell T :=
  E.stateSpace.source

abbrev boxVertex (E : MatrixExponentialStrong Cell T) :=
  E.stateSpace.boxVertex

abbrev execGenerator (E : MatrixExponentialStrong Cell T) :
    Matrix E.boxVertex E.boxVertex ExecComplex :=
  E.stateSpace.execGenerator

abbrev mirrorGenerator (E : MatrixExponentialStrong Cell T) :
    Matrix E.boxVertex E.boxVertex ℂ :=
  E.stateSpace.mirrorGenerator

abbrev weightPolicy (E : MatrixExponentialStrong Cell T) : WeightPolicy :=
  E.stateSpace.spectral.source.policy

abbrev thermalAxis (E : MatrixExponentialStrong Cell T) : ThermalAxis :=
  E.weightPolicy.thermal

abbrev thermalBetaQ (E : MatrixExponentialStrong Cell T) : ℚ :=
  E.weightPolicy.beta

def scaledGeneratorApprox (E : MatrixExponentialStrong Cell T) (τ : ℚ) :
    Matrix E.boxVertex E.boxVertex ExecComplex :=
  ExecComplex.ofRat τ • E.execGenerator

def expApproxTerm (E : MatrixExponentialStrong Cell T)
    (A : Matrix E.boxVertex E.boxVertex ExecComplex) (n : Nat) :
    Matrix E.boxVertex E.boxVertex ExecComplex :=
  ExecComplex.ofRat (((Nat.factorial n : ℚ))⁻¹) • A ^ n

def expApprox (E : MatrixExponentialStrong Cell T) (N : Nat)
    (A : Matrix E.boxVertex E.boxVertex ExecComplex) :
    Matrix E.boxVertex E.boxVertex ExecComplex :=
  Finset.sum (Finset.range (N + 1)) (fun n => E.expApproxTerm A n)

theorem expApprox_zero (E : MatrixExponentialStrong Cell T) (N : Nat) :
    E.expApprox N 0 = 1 := by
  induction N with
  | zero =>
      apply Matrix.ext
      intro i j
      apply ExecComplex.ext
      · by_cases h : i = j
        · subst h
          simp [expApprox, expApproxTerm, ExecComplex.ofRat]
          rw [ExecComplex.one_re]
        · simp [expApprox, expApproxTerm, h, ExecComplex.ofRat]
      · by_cases h : i = j
        · subst h
          simp [expApprox, expApproxTerm, ExecComplex.ofRat]
          rw [ExecComplex.one_im]
        · simp [expApprox, expApproxTerm, h, ExecComplex.ofRat]
  | succ N ih =>
      rw [expApprox, Finset.sum_range_succ]
      change E.expApprox N 0 + E.expApproxTerm 0 (N + 1) = 1
      rw [ih]
      have hterm : E.expApproxTerm 0 (N + 1) = 0 := by
        simp [expApproxTerm]
      rw [hterm]
      simp

def evolutionApproxAt (E : MatrixExponentialStrong Cell T) (N : Nat) (τ : ℚ) :
    Matrix E.boxVertex E.boxVertex ExecComplex :=
  E.expApprox N (E.scaledGeneratorApprox τ)

theorem scaledGeneratorApprox_zero (E : MatrixExponentialStrong Cell T) :
    E.scaledGeneratorApprox 0 = 0 := by
  apply Matrix.ext
  intro i j
  apply ExecComplex.ext
  · simp [scaledGeneratorApprox, ExecComplex.ofRat, ExecComplex.mul_re]
    rw [ExecComplex.zero_re]
  · simp [scaledGeneratorApprox, ExecComplex.ofRat, ExecComplex.mul_im]
    rw [ExecComplex.zero_im]

theorem evolutionApproxAt_zero (E : MatrixExponentialStrong Cell T) (N : Nat) :
    E.evolutionApproxAt N 0 = 1 := by
  unfold evolutionApproxAt
  rw [E.scaledGeneratorApprox_zero]
  exact E.expApprox_zero N

def thermalApproxAt (E : MatrixExponentialStrong Cell T) (N : Nat)
    (Θ : ThermalAxis) : Matrix E.boxVertex E.boxVertex ExecComplex :=
  E.evolutionApproxAt N (-Θ.beta)

def weightedThermalApproxAt (E : MatrixExponentialStrong Cell T) (N : Nat)
    (wp : WeightPolicy) : Matrix E.boxVertex E.boxVertex ExecComplex :=
  E.thermalApproxAt N wp.thermal

abbrev defaultThermalApproxAt (E : MatrixExponentialStrong Cell T) (N : Nat) :
    Matrix E.boxVertex E.boxVertex ExecComplex :=
  E.weightedThermalApproxAt N E.weightPolicy

theorem thermalBetaQ_eq_policy_beta (E : MatrixExponentialStrong Cell T) :
    E.thermalBetaQ = E.weightPolicy.beta := by
  rfl

theorem defaultThermalApproxAt_eq_weighted (E : MatrixExponentialStrong Cell T) (N : Nat) :
    E.defaultThermalApproxAt N = E.weightedThermalApproxAt N E.weightPolicy := by
  rfl

theorem weightedThermalApproxAt_eq_axis (E : MatrixExponentialStrong Cell T)
    (N : Nat) (wp : WeightPolicy) :
    E.weightedThermalApproxAt N wp = E.thermalApproxAt N wp.thermal := by
  rfl

noncomputable def mirrorExp (E : MatrixExponentialStrong Cell T)
    (A : Matrix E.boxVertex E.boxVertex ℂ) :
    Matrix E.boxVertex E.boxVertex ℂ :=
  NormedSpace.exp A

noncomputable def mirrorGeneratorExp (E : MatrixExponentialStrong Cell T) :
    Matrix E.boxVertex E.boxVertex ℂ :=
  E.mirrorExp E.mirrorGenerator

def mirrorScaledGenerator (E : MatrixExponentialStrong Cell T) (τ : ℂ) :
    Matrix E.boxVertex E.boxVertex ℂ :=
  τ • E.mirrorGenerator

noncomputable def mirrorEvolutionAt (E : MatrixExponentialStrong Cell T) (τ : ℂ) :
    Matrix E.boxVertex E.boxVertex ℂ :=
  E.mirrorExp (E.mirrorScaledGenerator τ)

noncomputable def mirrorThermalAt (E : MatrixExponentialStrong Cell T) (β : ℝ) :
    Matrix E.boxVertex E.boxVertex ℂ :=
  E.mirrorEvolutionAt (-(β : ℂ))

theorem mirrorGenerator_isHermitian (E : MatrixExponentialStrong Cell T) :
    IsHermitian E.mirrorGenerator := by
  exact E.stateSpace.mirrorGenerator_isHermitian

theorem mirrorExp_eq_normedSpace_exp (E : MatrixExponentialStrong Cell T)
    (A : Matrix E.boxVertex E.boxVertex ℂ) :
    E.mirrorExp A = NormedSpace.exp A := by
  rfl

theorem mirrorEvolutionAt_zero (E : MatrixExponentialStrong Cell T) :
    E.mirrorEvolutionAt 0 = 1 := by
  simp [mirrorEvolutionAt, mirrorScaledGenerator, mirrorExp]

theorem mirrorThermalAt_zero (E : MatrixExponentialStrong Cell T) :
    E.mirrorThermalAt 0 = 1 := by
  simp [mirrorThermalAt, mirrorEvolutionAt_zero]

end MatrixExponentialStrong

namespace StrengtheningS9

open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullMatrixExponential (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    MatrixExponentialStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  MatrixExponentialStrong.ofStateSpace (referenceFullStateSpace b p wp)

def variationFullMatrixExponential (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    MatrixExponentialStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  MatrixExponentialStrong.ofStateSpace (variationFullStateSpace β p wp)

end StrengtheningS9

end CNNA.PillarA.Finite
