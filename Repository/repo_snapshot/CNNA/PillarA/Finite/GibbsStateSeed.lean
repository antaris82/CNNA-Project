import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace
import CNNA.PillarA.Finite.MatrixExponential

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure GibbsStateSeedStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : MatrixExponentialStrong Cell T

abbrev GibbsStateSeedStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  GibbsStateSeedStrong (Cell := Cell) T

namespace GibbsStateSeedStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (G H : GibbsStateSeedStrong Cell T)
    (hsource : G.source = H.source) :
    G = H := by
  cases G with
  | mk sourceG =>
      cases H with
      | mk sourceH =>
          cases hsource
          rfl

def ofMatrixExponential (E : MatrixExponentialStrong Cell T) :
    GibbsStateSeedStrong Cell T where
  source := E

def cast (h : T = U) (G : GibbsStateSeedStrong Cell T) :
    GibbsStateSeedStrong Cell U := by
  cases h
  exact G

theorem cast_rfl (G : GibbsStateSeedStrong Cell T) :
    cast (Cell := Cell) rfl G = G := by
  rfl

abbrev matrixExponential (G : GibbsStateSeedStrong Cell T) : MatrixExponentialStrong Cell T :=
  G.source

abbrev stateSpace (G : GibbsStateSeedStrong Cell T) : StateSpaceStrong Cell T :=
  G.matrixExponential.stateSpace

abbrev spectralBridge (G : GibbsStateSeedStrong Cell T) : SpectralBridgeStrong Cell T :=
  G.stateSpace.source

abbrev mirror (G : GibbsStateSeedStrong Cell T) : SpectralDecompositionCStrong Cell T :=
  G.spectralBridge.mirror

abbrev boxVertex (G : GibbsStateSeedStrong Cell T) :=
  G.stateSpace.boxVertex

abbrev execDensityOperator (G : GibbsStateSeedStrong Cell T) : Type _ :=
  G.stateSpace.execDensityOperator

abbrev weightPolicy (G : GibbsStateSeedStrong Cell T) : WeightPolicy :=
  G.matrixExponential.weightPolicy

abbrev thermalAxis (G : GibbsStateSeedStrong Cell T) : ThermalAxis :=
  G.weightPolicy.thermal

def gibbsApproxUnnormalizedAt (G : GibbsStateSeedStrong Cell T) (N : Nat)
    (Θ : ThermalAxis) : G.execDensityOperator :=
  G.matrixExponential.thermalApproxAt N Θ

def weightedGibbsApproxUnnormalized (G : GibbsStateSeedStrong Cell T) (N : Nat)
    (wp : WeightPolicy) : G.execDensityOperator :=
  G.matrixExponential.weightedThermalApproxAt N wp

abbrev gibbsApproxUnnormalized (G : GibbsStateSeedStrong Cell T) (N : Nat) :
    G.execDensityOperator :=
  G.weightedGibbsApproxUnnormalized N G.weightPolicy

def gibbsApproxPartitionFunctionAt (G : GibbsStateSeedStrong Cell T) (N : Nat)
    (Θ : ThermalAxis) : ExecComplex :=
  G.stateSpace.execTrace (G.gibbsApproxUnnormalizedAt N Θ)

def weightedGibbsApproxPartitionFunction (G : GibbsStateSeedStrong Cell T) (N : Nat)
    (wp : WeightPolicy) : ExecComplex :=
  G.stateSpace.execTrace (G.weightedGibbsApproxUnnormalized N wp)

abbrev gibbsApproxPartitionFunction (G : GibbsStateSeedStrong Cell T) (N : Nat) : ExecComplex :=
  G.weightedGibbsApproxPartitionFunction N G.weightPolicy

structure GibbsApproxPartitionWitness (G : GibbsStateSeedStrong Cell T) (N : Nat) where
  value : ℚ
  trace_eq : G.gibbsApproxPartitionFunction N = ExecComplex.ofRat value
  value_ne_zero : value ≠ 0

def gibbsApproxState (G : GibbsStateSeedStrong Cell T) (N : Nat)
    (w : GibbsApproxPartitionWitness (G := G) N) :
    G.execDensityOperator :=
  G.stateSpace.execTraceNormalize
    (G.gibbsApproxUnnormalized N) w.value w.trace_eq w.value_ne_zero

theorem weightedGibbsApproxUnnormalized_eq_axis (G : GibbsStateSeedStrong Cell T)
    (N : Nat) (wp : WeightPolicy) :
    G.weightedGibbsApproxUnnormalized N wp = G.gibbsApproxUnnormalizedAt N wp.thermal := by
  rfl

theorem gibbsApproxUnnormalized_eq_defaultThermalApproxAt
    (G : GibbsStateSeedStrong Cell T) (N : Nat) :
    G.gibbsApproxUnnormalized N = G.matrixExponential.defaultThermalApproxAt N := by
  rfl

theorem gibbsApproxPartitionFunction_eq_execTrace
    (G : GibbsStateSeedStrong Cell T) (N : Nat) :
    G.gibbsApproxPartitionFunction N =
      G.stateSpace.execTrace (G.gibbsApproxUnnormalized N) := by
  rfl

theorem gibbsApproxState_eq_execTraceNormalize
    (G : GibbsStateSeedStrong Cell T) (N : Nat)
    (w : GibbsApproxPartitionWitness (G := G) N) :
    G.gibbsApproxState N w =
      G.stateSpace.execTraceNormalize
        (G.gibbsApproxUnnormalized N) w.value w.trace_eq w.value_ne_zero := by
  rfl

noncomputable def mirrorGibbsWeight (G : GibbsStateSeedStrong Cell T)
    (β : ℝ) (i : G.boxVertex) : ℝ :=
  Real.exp (-β * G.mirror.eigenvalues i)

noncomputable def mirrorGibbsDiagonal (G : GibbsStateSeedStrong Cell T) (β : ℝ) :
    Matrix G.boxVertex G.boxVertex ℂ :=
  Matrix.diagonal (fun i => (G.mirrorGibbsWeight β i : ℂ))

noncomputable def mirrorDiagonalPartitionFunction (G : GibbsStateSeedStrong Cell T)
    (β : ℝ) : ℂ :=
  Matrix.trace (G.mirrorGibbsDiagonal β)

noncomputable def mirrorEigenvectorUnitaryMatrix (G : GibbsStateSeedStrong Cell T) :
    Matrix G.boxVertex G.boxVertex ℂ :=
  G.mirror.eigenvectorUnitaryMatrix

noncomputable def mirrorGibbsUnnormalized (G : GibbsStateSeedStrong Cell T) (β : ℝ) :
    Matrix G.boxVertex G.boxVertex ℂ :=
  G.mirrorEigenvectorUnitaryMatrix * G.mirrorGibbsDiagonal β * star G.mirrorEigenvectorUnitaryMatrix

noncomputable def mirrorPartitionFunction (G : GibbsStateSeedStrong Cell T)
    (β : ℝ) : ℂ :=
  G.stateSpace.mirrorTrace (G.mirrorGibbsUnnormalized β)

noncomputable def mirrorGibbsState (G : GibbsStateSeedStrong Cell T) (β : ℝ)
    (hZ : G.mirrorPartitionFunction β ≠ 0) :
    Matrix G.boxVertex G.boxVertex ℂ :=
  G.stateSpace.mirrorTraceNormalize
    (G.mirrorGibbsUnnormalized β) (G.mirrorPartitionFunction β) hZ

noncomputable def mirrorThermalCandidate (G : GibbsStateSeedStrong Cell T) (β : ℝ) :
    Matrix G.boxVertex G.boxVertex ℂ :=
  G.matrixExponential.mirrorThermalAt β

theorem mirrorDiagonalPartitionFunction_eq_trace (G : GibbsStateSeedStrong Cell T)
    (β : ℝ) :
    G.mirrorDiagonalPartitionFunction β = Matrix.trace (G.mirrorGibbsDiagonal β) := by
  rfl

theorem mirrorPartitionFunction_eq_trace (G : GibbsStateSeedStrong Cell T)
    (β : ℝ) :
    G.mirrorPartitionFunction β = Matrix.trace (G.mirrorGibbsUnnormalized β) := by
  rfl

theorem mirrorGibbsState_eq_traceNormalize (G : GibbsStateSeedStrong Cell T)
    (β : ℝ) (hZ : G.mirrorPartitionFunction β ≠ 0) :
    G.mirrorGibbsState β hZ =
      G.stateSpace.mirrorTraceNormalize
        (G.mirrorGibbsUnnormalized β) (G.mirrorPartitionFunction β) hZ := by
  rfl

theorem mirrorThermalCandidate_zero (G : GibbsStateSeedStrong Cell T) :
    G.mirrorThermalCandidate 0 = 1 := by
  simpa [mirrorThermalCandidate] using G.matrixExponential.mirrorThermalAt_zero

end GibbsStateSeedStrong

namespace StrengtheningS9

open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullGibbsStateSeed (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    GibbsStateSeedStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  GibbsStateSeedStrong.ofMatrixExponential (referenceFullMatrixExponential b p wp)

def variationFullGibbsStateSeed (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    GibbsStateSeedStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  GibbsStateSeedStrong.ofMatrixExponential (variationFullMatrixExponential β p wp)

end StrengtheningS9

end CNNA.PillarA.Finite
