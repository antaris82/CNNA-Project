import CNNA.PillarA.Finite.UnitaryEvolution

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure DynamicsAdapterStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : UnitaryEvolutionStrong Cell T

abbrev DynamicsAdapterStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  DynamicsAdapterStrong (Cell := Cell) T

namespace DynamicsAdapterStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (D₁ D₂ : DynamicsAdapterStrong Cell T)
    (hsource : D₁.source = D₂.source) :
    D₁ = D₂ := by
  cases D₁ with
  | mk source₁ =>
      cases D₂ with
      | mk source₂ =>
          cases hsource
          rfl

def ofUnitaryEvolution (U₁ : UnitaryEvolutionStrong Cell T) :
    DynamicsAdapterStrong Cell T where
  source := U₁

def cast (h : T = U) (D : DynamicsAdapterStrong Cell T) :
    DynamicsAdapterStrong Cell U := by
  cases h
  exact D

theorem cast_rfl (D : DynamicsAdapterStrong Cell T) :
    cast (Cell := Cell) rfl D = D := by
  rfl

abbrev unitaryEvolution (D : DynamicsAdapterStrong Cell T) : UnitaryEvolutionStrong Cell T :=
  D.source

abbrev stateSpace (D : DynamicsAdapterStrong Cell T) : StateSpaceStrong Cell T :=
  D.unitaryEvolution.stateSpace

abbrev boxVertex (D : DynamicsAdapterStrong Cell T) :=
  D.stateSpace.boxVertex

abbrev execState (D : DynamicsAdapterStrong Cell T) : Type _ :=
  D.stateSpace.execState

abbrev execObservable (D : DynamicsAdapterStrong Cell T) : Type _ :=
  D.stateSpace.execObservable

abbrev execDensityOperator (D : DynamicsAdapterStrong Cell T) : Type _ :=
  D.stateSpace.execDensityOperator

abbrev execStateContract (D : DynamicsAdapterStrong Cell T) :
    StateContract ExecComplex D.boxVertex :=
  D.stateSpace.execStateContract

abbrev execObservableContract (D : DynamicsAdapterStrong Cell T) :
    StarAlgebraContract ExecComplex D.boxVertex :=
  D.stateSpace.execObservableContract

abbrev mirrorState (D : DynamicsAdapterStrong Cell T) : Type _ :=
  D.stateSpace.mirrorState

abbrev mirrorObservable (D : DynamicsAdapterStrong Cell T) : Type _ :=
  D.stateSpace.mirrorObservable

abbrev mirrorDensityOperator (D : DynamicsAdapterStrong Cell T) : Type _ :=
  D.stateSpace.mirrorDensityOperator

def schrodingerState (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) (ψ : D.execState) : D.execState :=
  (D.unitaryEvolution.propagator Ξ).mulVec ψ

abbrev schrodingerDensity (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) (ρ : D.execDensityOperator) :
    D.execDensityOperator :=
  D.unitaryEvolution.schrodingerConjugation Ξ ρ

abbrev heisenbergObservable (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) (A : D.execObservable) :
    D.execObservable :=
  D.unitaryEvolution.heisenbergConjugation Ξ A

structure StarAlgDynamicsSeed (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) where
  stateContract : StateContract ExecComplex D.boxVertex
  observableContract : StarAlgebraContract ExecComplex D.boxVertex
  propagator : Matrix D.boxVertex D.boxVertex ExecComplex
  inversePropagator : Matrix D.boxVertex D.boxVertex ExecComplex
  stateMap : D.execState → D.execState
  densityMap : D.execDensityOperator → D.execDensityOperator
  observableMap : D.execObservable → D.execObservable

def starAlgDynamicsSeed (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) : StarAlgDynamicsSeed D Ξ where
  stateContract := D.execStateContract
  observableContract := D.execObservableContract
  propagator := D.unitaryEvolution.propagator Ξ
  inversePropagator := D.unitaryEvolution.inversePropagator Ξ
  stateMap := D.schrodingerState Ξ
  densityMap := D.schrodingerDensity Ξ
  observableMap := D.heisenbergObservable Ξ

theorem execDensityOperator_eq_execObservable (D : DynamicsAdapterStrong Cell T) :
    D.execDensityOperator = D.execObservable := by
  rfl

theorem schrodingerState_zero (D : DynamicsAdapterStrong Cell T)
    (N : Nat) (ψ : D.execState) :
    D.schrodingerState (EvolutionApproxAxis.zero N) ψ = ψ := by
  unfold schrodingerState
  rw [D.unitaryEvolution.propagator_zero N]
  exact Matrix.one_mulVec ψ

theorem schrodingerDensity_zero (D : DynamicsAdapterStrong Cell T)
    (N : Nat) (ρ : D.execDensityOperator) :
    D.schrodingerDensity (EvolutionApproxAxis.zero N) ρ = ρ := by
  exact D.unitaryEvolution.schrodingerConjugation_zero N ρ

theorem heisenbergObservable_zero (D : DynamicsAdapterStrong Cell T)
    (N : Nat) (A : D.execObservable) :
    D.heisenbergObservable (EvolutionApproxAxis.zero N) A = A := by
  exact D.unitaryEvolution.heisenbergConjugation_zero N A

theorem schrodingerState_comp (D : DynamicsAdapterStrong Cell T)
    (Ξ₂ Ξ₁ : EvolutionApproxAxis) (ψ : D.execState) :
    D.schrodingerState Ξ₂ (D.schrodingerState Ξ₁ ψ) =
      (D.unitaryEvolution.propagator Ξ₂ * D.unitaryEvolution.propagator Ξ₁).mulVec ψ := by
  unfold schrodingerState
  exact Matrix.mulVec_mulVec ψ (D.unitaryEvolution.propagator Ξ₂)
    (D.unitaryEvolution.propagator Ξ₁)

theorem schrodingerDensity_comp (D : DynamicsAdapterStrong Cell T)
    (Ξ₂ Ξ₁ : EvolutionApproxAxis) (ρ : D.execDensityOperator) :
    D.schrodingerDensity Ξ₂ (D.schrodingerDensity Ξ₁ ρ) =
      (D.unitaryEvolution.propagator Ξ₂ * D.unitaryEvolution.propagator Ξ₁) * ρ *
        (D.unitaryEvolution.inversePropagator Ξ₁ * D.unitaryEvolution.inversePropagator Ξ₂) := by
  exact D.unitaryEvolution.schrodingerConjugation_comp Ξ₂ Ξ₁ ρ

theorem heisenbergObservable_comp (D : DynamicsAdapterStrong Cell T)
    (Ξ₂ Ξ₁ : EvolutionApproxAxis) (A : D.execObservable) :
    D.heisenbergObservable Ξ₂ (D.heisenbergObservable Ξ₁ A) =
      (D.unitaryEvolution.inversePropagator Ξ₂ * D.unitaryEvolution.inversePropagator Ξ₁) * A *
        (D.unitaryEvolution.propagator Ξ₁ * D.unitaryEvolution.propagator Ξ₂) := by
  exact D.unitaryEvolution.heisenbergConjugation_comp Ξ₂ Ξ₁ A

theorem schrodingerDensity_star (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) (ρ : D.execDensityOperator) :
    star (D.schrodingerDensity Ξ ρ) =
      star (D.unitaryEvolution.inversePropagator Ξ) * star ρ *
        star (D.unitaryEvolution.propagator Ξ) := by
  unfold schrodingerDensity UnitaryEvolutionStrong.schrodingerConjugation
  rw [Matrix.star_mul]
  rw [Matrix.star_mul]
  rw [Matrix.mul_assoc]

theorem heisenbergObservable_star (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) (A : D.execObservable) :
    star (D.heisenbergObservable Ξ A) =
      star (D.unitaryEvolution.propagator Ξ) * star A *
        star (D.unitaryEvolution.inversePropagator Ξ) := by
  unfold heisenbergObservable UnitaryEvolutionStrong.heisenbergConjugation
  rw [Matrix.star_mul]
  rw [Matrix.star_mul]
  rw [Matrix.mul_assoc]

theorem starAlgDynamicsSeed_stateContract (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).stateContract = D.execStateContract := by
  rfl

theorem starAlgDynamicsSeed_observableContract (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).observableContract = D.execObservableContract := by
  rfl

theorem starAlgDynamicsSeed_propagator (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).propagator = D.unitaryEvolution.propagator Ξ := by
  rfl

theorem starAlgDynamicsSeed_inversePropagator (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).inversePropagator = D.unitaryEvolution.inversePropagator Ξ := by
  rfl

theorem starAlgDynamicsSeed_stateMap (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).stateMap = D.schrodingerState Ξ := by
  rfl

theorem starAlgDynamicsSeed_densityMap (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).densityMap = D.schrodingerDensity Ξ := by
  rfl

theorem starAlgDynamicsSeed_observableMap (D : DynamicsAdapterStrong Cell T)
    (Ξ : EvolutionApproxAxis) :
    (D.starAlgDynamicsSeed Ξ).observableMap = D.heisenbergObservable Ξ := by
  rfl

theorem starAlgDynamicsSeed_zero (D : DynamicsAdapterStrong Cell T)
    (N : Nat) :
    (D.starAlgDynamicsSeed (EvolutionApproxAxis.zero N)).stateMap = id ∧
      (D.starAlgDynamicsSeed (EvolutionApproxAxis.zero N)).densityMap = id ∧
      (D.starAlgDynamicsSeed (EvolutionApproxAxis.zero N)).observableMap = id := by
  constructor
  · funext ψ
    exact D.schrodingerState_zero N ψ
  · constructor
    · funext ρ
      exact D.schrodingerDensity_zero N ρ
    · funext A
      exact D.heisenbergObservable_zero N A

noncomputable def mirrorSchrodingerState (D : DynamicsAdapterStrong Cell T)
    (t : ℝ) (ψ : D.mirrorState) : D.mirrorState :=
  (D.unitaryEvolution.mirrorPropagator t).mulVec ψ

noncomputable def mirrorSchrodingerDensity (D : DynamicsAdapterStrong Cell T)
    (t : ℝ) (ρ : D.mirrorDensityOperator) : D.mirrorDensityOperator :=
  D.unitaryEvolution.mirrorSchrodingerConjugation t ρ

noncomputable def mirrorHeisenbergObservable (D : DynamicsAdapterStrong Cell T)
    (t : ℝ) (A : D.mirrorObservable) : D.mirrorObservable :=
  D.unitaryEvolution.mirrorHeisenbergConjugation t A

structure MirrorStarAlgDynamicsSeed (D : DynamicsAdapterStrong Cell T) (t : ℝ) where
  stateMap : D.mirrorState → D.mirrorState
  densityMap : D.mirrorDensityOperator → D.mirrorDensityOperator
  observableMap : D.mirrorObservable → D.mirrorObservable

noncomputable def mirrorStarAlgDynamicsSeed (D : DynamicsAdapterStrong Cell T) (t : ℝ) :
    MirrorStarAlgDynamicsSeed D t where
  stateMap := D.mirrorSchrodingerState t
  densityMap := D.mirrorSchrodingerDensity t
  observableMap := D.mirrorHeisenbergObservable t

theorem mirrorSchrodingerState_zero (D : DynamicsAdapterStrong Cell T)
    (ψ : D.mirrorState) :
    D.mirrorSchrodingerState 0 ψ = ψ := by
  simp [mirrorSchrodingerState, D.unitaryEvolution.mirrorPropagator_zero]

theorem mirrorSchrodingerDensity_zero (D : DynamicsAdapterStrong Cell T)
    (ρ : D.mirrorDensityOperator) :
    D.mirrorSchrodingerDensity 0 ρ = ρ := by
  simpa [mirrorSchrodingerDensity] using D.unitaryEvolution.mirrorSchrodingerConjugation_zero ρ

theorem mirrorHeisenbergObservable_zero (D : DynamicsAdapterStrong Cell T)
    (A : D.mirrorObservable) :
    D.mirrorHeisenbergObservable 0 A = A := by
  simpa [mirrorHeisenbergObservable] using D.unitaryEvolution.mirrorHeisenbergConjugation_zero A

theorem mirrorStarAlgDynamicsSeed_zero (D : DynamicsAdapterStrong Cell T) :
    (D.mirrorStarAlgDynamicsSeed 0).stateMap = D.mirrorSchrodingerState 0 ∧
      (D.mirrorStarAlgDynamicsSeed 0).densityMap = D.mirrorSchrodingerDensity 0 ∧
      (D.mirrorStarAlgDynamicsSeed 0).observableMap = D.mirrorHeisenbergObservable 0 := by
  exact ⟨rfl, ⟨rfl, rfl⟩⟩

end DynamicsAdapterStrong

namespace StrengtheningS9

open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullDynamicsAdapter (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    DynamicsAdapterStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  DynamicsAdapterStrong.ofUnitaryEvolution (referenceFullUnitaryEvolution b p wp)

def variationFullDynamicsAdapter (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    DynamicsAdapterStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  DynamicsAdapterStrong.ofUnitaryEvolution (variationFullUnitaryEvolution β p wp)

end StrengtheningS9

end CNNA.PillarA.Finite
