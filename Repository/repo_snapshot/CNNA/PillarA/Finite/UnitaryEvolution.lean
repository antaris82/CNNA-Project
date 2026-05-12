import Mathlib.Analysis.Complex.Exponential
import CNNA.PillarA.Finite.MatrixExponential

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure EvolutionApproxAxis where
  order : Nat
  time : ℚ

namespace EvolutionApproxAxis

@[ext] theorem ext (Ξ Ψ : EvolutionApproxAxis)
    (horder : Ξ.order = Ψ.order) (htime : Ξ.time = Ψ.time) :
    Ξ = Ψ := by
  cases Ξ
  cases Ψ
  cases horder
  cases htime
  rfl

def zero (N : Nat) : EvolutionApproxAxis where
  order := N
  time := 0

def neg (Ξ : EvolutionApproxAxis) : EvolutionApproxAxis where
  order := Ξ.order
  time := -Ξ.time

theorem neg_order (Ξ : EvolutionApproxAxis) : Ξ.neg.order = Ξ.order := by
  rfl

theorem neg_time (Ξ : EvolutionApproxAxis) : Ξ.neg.time = -Ξ.time := by
  rfl

theorem neg_neg (Ξ : EvolutionApproxAxis) : Ξ.neg.neg = Ξ := by
  cases Ξ with
  | mk order time =>
      apply EvolutionApproxAxis.ext
      · rfl
      · change -(-time) = time
        exact _root_.neg_neg time

theorem zero_order (N : Nat) : (zero N).order = N := by
  rfl

theorem zero_time (N : Nat) : (zero N).time = 0 := by
  rfl

end EvolutionApproxAxis

structure UnitaryEvolutionStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : MatrixExponentialStrong Cell T

abbrev UnitaryEvolutionStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  UnitaryEvolutionStrong (Cell := Cell) T

namespace UnitaryEvolutionStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (U₁ U₂ : UnitaryEvolutionStrong Cell T)
    (hsource : U₁.source = U₂.source) :
    U₁ = U₂ := by
  cases U₁ with
  | mk source₁ =>
      cases U₂ with
      | mk source₂ =>
          cases hsource
          rfl

def ofMatrixExponential (E : MatrixExponentialStrong Cell T) :
    UnitaryEvolutionStrong Cell T where
  source := E

def cast (h : T = U) (U₁ : UnitaryEvolutionStrong Cell T) :
    UnitaryEvolutionStrong Cell U := by
  cases h
  exact U₁

theorem cast_rfl (U₁ : UnitaryEvolutionStrong Cell T) :
    cast (Cell := Cell) rfl U₁ = U₁ := by
  rfl

abbrev matrixExponential (U₁ : UnitaryEvolutionStrong Cell T) : MatrixExponentialStrong Cell T :=
  U₁.source

abbrev stateSpace (U₁ : UnitaryEvolutionStrong Cell T) : StateSpaceStrong Cell T :=
  U₁.matrixExponential.stateSpace

abbrev boxVertex (U₁ : UnitaryEvolutionStrong Cell T) :=
  U₁.stateSpace.boxVertex

abbrev execObservable (U₁ : UnitaryEvolutionStrong Cell T) : Type _ :=
  U₁.stateSpace.execObservable

abbrev execDensityOperator (U₁ : UnitaryEvolutionStrong Cell T) : Type _ :=
  U₁.stateSpace.execDensityOperator

abbrev mirrorGenerator (U₁ : UnitaryEvolutionStrong Cell T) : Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  U₁.matrixExponential.mirrorGenerator

def propagator (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) : Matrix U₁.boxVertex U₁.boxVertex ExecComplex :=
  U₁.matrixExponential.evolutionApproxAt Ξ.order Ξ.time

def inversePropagator (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) : Matrix U₁.boxVertex U₁.boxVertex ExecComplex :=
  U₁.matrixExponential.evolutionApproxAt Ξ.order (-Ξ.time)

def schrodingerConjugation (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) (ρ : U₁.execDensityOperator) :
    U₁.execDensityOperator :=
  U₁.propagator Ξ * ρ * U₁.inversePropagator Ξ

def heisenbergConjugation (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) (A : U₁.execObservable) :
    U₁.execObservable :=
  U₁.inversePropagator Ξ * A * U₁.propagator Ξ

theorem propagator_eq_evolutionApproxAt (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    U₁.propagator Ξ = U₁.matrixExponential.evolutionApproxAt Ξ.order Ξ.time := by
  rfl

theorem inversePropagator_eq_evolutionApproxAt_neg (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    U₁.inversePropagator Ξ = U₁.matrixExponential.evolutionApproxAt Ξ.order (-Ξ.time) := by
  rfl

theorem inversePropagator_eq_propagator_neg (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    U₁.inversePropagator Ξ = U₁.propagator Ξ.neg := by
  rfl

theorem propagator_neg_eq_inversePropagator (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    U₁.propagator Ξ.neg = U₁.inversePropagator Ξ := by
  rfl

theorem inversePropagator_neg_eq_propagator (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    U₁.inversePropagator Ξ.neg = U₁.propagator Ξ := by
  unfold inversePropagator propagator EvolutionApproxAxis.neg
  rw [_root_.neg_neg]

theorem propagator_zero (U₁ : UnitaryEvolutionStrong Cell T) (N : Nat) :
    U₁.propagator (EvolutionApproxAxis.zero N) = 1 := by
  unfold propagator
  change U₁.matrixExponential.evolutionApproxAt N ((EvolutionApproxAxis.zero N).time) = 1
  rw [EvolutionApproxAxis.zero_time]
  exact U₁.matrixExponential.evolutionApproxAt_zero N

theorem inversePropagator_zero (U₁ : UnitaryEvolutionStrong Cell T) (N : Nat) :
    U₁.inversePropagator (EvolutionApproxAxis.zero N) = 1 := by
  unfold inversePropagator
  change U₁.matrixExponential.evolutionApproxAt N (-((EvolutionApproxAxis.zero N).time)) = 1
  rw [EvolutionApproxAxis.zero_time]
  rw [_root_.neg_zero]
  exact U₁.matrixExponential.evolutionApproxAt_zero N

theorem schrodingerConjugation_zero (U₁ : UnitaryEvolutionStrong Cell T)
    (N : Nat) (ρ : U₁.execDensityOperator) :
    U₁.schrodingerConjugation (EvolutionApproxAxis.zero N) ρ = ρ := by
  unfold schrodingerConjugation
  rw [U₁.propagator_zero N]
  rw [one_mul]
  rw [U₁.inversePropagator_zero N]
  rw [Matrix.mul_one]

theorem heisenbergConjugation_zero (U₁ : UnitaryEvolutionStrong Cell T)
    (N : Nat) (A : U₁.execObservable) :
    U₁.heisenbergConjugation (EvolutionApproxAxis.zero N) A = A := by
  unfold heisenbergConjugation
  rw [U₁.inversePropagator_zero N]
  rw [one_mul]
  rw [U₁.propagator_zero N]
  rw [Matrix.mul_one]

theorem schrodingerConjugation_comp (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ₂ Ξ₁ : EvolutionApproxAxis) (ρ : U₁.execDensityOperator) :
    U₁.schrodingerConjugation Ξ₂ (U₁.schrodingerConjugation Ξ₁ ρ) =
      (U₁.propagator Ξ₂ * U₁.propagator Ξ₁) * ρ *
        (U₁.inversePropagator Ξ₁ * U₁.inversePropagator Ξ₂) := by
  unfold schrodingerConjugation
  simp only [Matrix.mul_assoc]

theorem heisenbergConjugation_comp (U₁ : UnitaryEvolutionStrong Cell T)
    (Ξ₂ Ξ₁ : EvolutionApproxAxis) (A : U₁.execObservable) :
    U₁.heisenbergConjugation Ξ₂ (U₁.heisenbergConjugation Ξ₁ A) =
      (U₁.inversePropagator Ξ₂ * U₁.inversePropagator Ξ₁) * A *
        (U₁.propagator Ξ₁ * U₁.propagator Ξ₂) := by
  unfold heisenbergConjugation
  simp only [Matrix.mul_assoc]

noncomputable def mirrorSkewGenerator (U₁ : UnitaryEvolutionStrong Cell T)
    (t : ℝ) : Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  ((-(t : ℂ) * Complex.I) : ℂ) • U₁.mirrorGenerator

noncomputable def mirrorBackwardSkewGenerator (U₁ : UnitaryEvolutionStrong Cell T)
    (t : ℝ) : Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  (((t : ℂ) * Complex.I) : ℂ) • U₁.mirrorGenerator

noncomputable def mirrorPropagator (U₁ : UnitaryEvolutionStrong Cell T)
    (t : ℝ) : Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  U₁.matrixExponential.mirrorExp (U₁.mirrorSkewGenerator t)

noncomputable def mirrorInversePropagator (U₁ : UnitaryEvolutionStrong Cell T)
    (t : ℝ) : Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  U₁.matrixExponential.mirrorExp (U₁.mirrorBackwardSkewGenerator t)

noncomputable def mirrorSchrodingerConjugation (U₁ : UnitaryEvolutionStrong Cell T)
    (t : ℝ) (ρ : Matrix U₁.boxVertex U₁.boxVertex ℂ) :
    Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  U₁.mirrorPropagator t * ρ * U₁.mirrorInversePropagator t

noncomputable def mirrorHeisenbergConjugation (U₁ : UnitaryEvolutionStrong Cell T)
    (t : ℝ) (A : Matrix U₁.boxVertex U₁.boxVertex ℂ) :
    Matrix U₁.boxVertex U₁.boxVertex ℂ :=
  U₁.mirrorInversePropagator t * A * U₁.mirrorPropagator t

theorem mirrorPropagator_zero (U₁ : UnitaryEvolutionStrong Cell T) :
    U₁.mirrorPropagator 0 = 1 := by
  simp [mirrorPropagator, mirrorSkewGenerator, MatrixExponentialStrong.mirrorExp]

theorem mirrorInversePropagator_zero (U₁ : UnitaryEvolutionStrong Cell T) :
    U₁.mirrorInversePropagator 0 = 1 := by
  simp [mirrorInversePropagator, mirrorBackwardSkewGenerator, MatrixExponentialStrong.mirrorExp]

theorem mirrorSchrodingerConjugation_zero (U₁ : UnitaryEvolutionStrong Cell T)
    (ρ : Matrix U₁.boxVertex U₁.boxVertex ℂ) :
    U₁.mirrorSchrodingerConjugation 0 ρ = ρ := by
  unfold mirrorSchrodingerConjugation
  rw [U₁.mirrorPropagator_zero, U₁.mirrorInversePropagator_zero]
  simp only [one_mul, Matrix.mul_one]

theorem mirrorHeisenbergConjugation_zero (U₁ : UnitaryEvolutionStrong Cell T)
    (A : Matrix U₁.boxVertex U₁.boxVertex ℂ) :
    U₁.mirrorHeisenbergConjugation 0 A = A := by
  unfold mirrorHeisenbergConjugation
  rw [U₁.mirrorInversePropagator_zero, U₁.mirrorPropagator_zero]
  simp only [one_mul, Matrix.mul_one]

theorem mirrorSchrodingerConjugation_comp (U₁ : UnitaryEvolutionStrong Cell T)
    (t₂ t₁ : ℝ) (ρ : Matrix U₁.boxVertex U₁.boxVertex ℂ) :
    U₁.mirrorSchrodingerConjugation t₂ (U₁.mirrorSchrodingerConjugation t₁ ρ) =
      (U₁.mirrorPropagator t₂ * U₁.mirrorPropagator t₁) * ρ *
        (U₁.mirrorInversePropagator t₁ * U₁.mirrorInversePropagator t₂) := by
  unfold mirrorSchrodingerConjugation
  simp only [Matrix.mul_assoc]

theorem mirrorHeisenbergConjugation_comp (U₁ : UnitaryEvolutionStrong Cell T)
    (t₂ t₁ : ℝ) (A : Matrix U₁.boxVertex U₁.boxVertex ℂ) :
    U₁.mirrorHeisenbergConjugation t₂ (U₁.mirrorHeisenbergConjugation t₁ A) =
      (U₁.mirrorInversePropagator t₂ * U₁.mirrorInversePropagator t₁) * A *
        (U₁.mirrorPropagator t₁ * U₁.mirrorPropagator t₂) := by
  unfold mirrorHeisenbergConjugation
  simp only [Matrix.mul_assoc]

end UnitaryEvolutionStrong

namespace StrengtheningS9

open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullUnitaryEvolution (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    UnitaryEvolutionStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  UnitaryEvolutionStrong.ofMatrixExponential (referenceFullMatrixExponential b p wp)

def variationFullUnitaryEvolution (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    UnitaryEvolutionStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  UnitaryEvolutionStrong.ofMatrixExponential (variationFullMatrixExponential β p wp)

end StrengtheningS9

end CNNA.PillarA.Finite
