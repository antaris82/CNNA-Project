import Mathlib.LinearAlgebra.Matrix.Trace
import CNNA.PillarA.Finite.SpectralBridge

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure StateSpaceStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SpectralBridgeStrong Cell T

abbrev StateSpaceStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  StateSpaceStrong (Cell := Cell) T

namespace StateSpaceStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (S R : StateSpaceStrong Cell T)
    (hsource : S.source = R.source) :
    S = R := by
  cases S with
  | mk sourceS =>
      cases R with
      | mk sourceR =>
          cases hsource
          rfl

def ofSpectralBridge (B : SpectralBridgeStrong Cell T) :
    StateSpaceStrong Cell T where
  source := B

def cast (h : T = U) (S : StateSpaceStrong Cell T) :
    StateSpaceStrong Cell U := by
  cases h
  exact S

theorem cast_rfl (S : StateSpaceStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

abbrev spectralBridge (S : StateSpaceStrong Cell T) : SpectralBridgeStrong Cell T :=
  S.source

abbrev spectral (S : StateSpaceStrong Cell T) : SpectralDecompositionStrong Cell T :=
  S.source.source

abbrev mirror (S : StateSpaceStrong Cell T) : SpectralDecompositionCStrong Cell T :=
  S.source.mirror

abbrev boxVertex (S : StateSpaceStrong Cell T) :=
  S.spectral.boxVertex

abbrev execState (S : StateSpaceStrong Cell T) : Type _ :=
  ExecState S.boxVertex

abbrev mirrorState (S : StateSpaceStrong Cell T) : Type _ :=
  FiniteStateSpace ℂ S.boxVertex

abbrev execObservable (S : StateSpaceStrong Cell T) : Type _ :=
  ExecObservable S.boxVertex

abbrev mirrorObservable (S : StateSpaceStrong Cell T) : Type _ :=
  Observable ℂ S.boxVertex

abbrev execDensityOperator (S : StateSpaceStrong Cell T) : Type _ :=
  Matrix S.boxVertex S.boxVertex ExecComplex

abbrev mirrorDensityOperator (S : StateSpaceStrong Cell T) : Type _ :=
  Matrix S.boxVertex S.boxVertex ℂ

abbrev execStateContract (S : StateSpaceStrong Cell T) : StateContract ExecComplex S.boxVertex :=
  StateContract.exec

abbrev mirrorStateContract (S : StateSpaceStrong Cell T) : StateContract ℂ S.boxVertex :=
  StateContract.canonical

abbrev execObservableContract (S : StateSpaceStrong Cell T) :
    StarAlgebraContract ExecComplex S.boxVertex :=
  StarAlgebraContract.exec

abbrev mirrorObservableContract (S : StateSpaceStrong Cell T) :
    StarAlgebraContract ℂ S.boxVertex :=
  StarAlgebraContract.canonical

abbrev execGenerator (S : StateSpaceStrong Cell T) : Matrix S.boxVertex S.boxVertex ExecComplex :=
  S.spectral.execMatrix

abbrev mirrorGenerator (S : StateSpaceStrong Cell T) : Matrix S.boxVertex S.boxVertex ℂ :=
  S.spectralBridge.complexMatrix

def execInner (S : StateSpaceStrong Cell T) (ψ φ : S.execState) : ExecComplex :=
  sesq (𝕜 := ExecComplex) ψ φ

def mirrorInner (S : StateSpaceStrong Cell T) (ψ φ : S.mirrorState) : ℂ :=
  sesq (𝕜 := ℂ) ψ φ

def mirrorStateNormSq (S : StateSpaceStrong Cell T) (ψ : S.mirrorState) : ℝ :=
  Complex.re (S.mirrorInner ψ ψ)

def execStateNormSq (S : StateSpaceStrong Cell T) (ψ : S.execState) : ℚ :=
  (S.execInner ψ ψ).re

def execTrace (S : StateSpaceStrong Cell T) (ρ : S.execDensityOperator) : ExecComplex :=
  Matrix.trace ρ

def execIsTraceOne (S : StateSpaceStrong Cell T) (ρ : S.execDensityOperator) : Prop :=
  S.execTrace ρ = 1

def execTraceNormalize (S : StateSpaceStrong Cell T)
    (ρ : S.execDensityOperator) (q : ℚ)
    (_htrace : S.execTrace ρ = ExecComplex.ofRat q) (_hq : q ≠ 0) :
    S.execDensityOperator :=
  ExecComplex.ofRat q⁻¹ • ρ

noncomputable def mirrorTrace (S : StateSpaceStrong Cell T) (ρ : S.mirrorDensityOperator) : ℂ :=
  Matrix.trace ρ

def mirrorIsTraceOne (S : StateSpaceStrong Cell T) (ρ : S.mirrorDensityOperator) : Prop :=
  S.mirrorTrace ρ = 1

noncomputable def mirrorTraceNormalize (S : StateSpaceStrong Cell T)
    (ρ : S.mirrorDensityOperator) (Z : ℂ) (_hZ : Z ≠ 0) : S.mirrorDensityOperator :=
  Z⁻¹ • ρ

def mirrorIsPositive (S : StateSpaceStrong Cell T) (ρ : S.mirrorDensityOperator) : Prop :=
  IsHermitian ρ ∧
    ∀ ψ : S.mirrorState, 0 ≤ Complex.re (sesq (𝕜 := ℂ) ψ (act (𝕜 := ℂ) ρ ψ))

def mirrorPositiveCone (S : StateSpaceStrong Cell T) : Set S.mirrorDensityOperator :=
  { ρ | S.mirrorIsPositive ρ }

def execPureStateVector (S : StateSpaceStrong Cell T) (i : S.boxVertex) : S.execState :=
  basisVector (𝕜 := ExecComplex) i

abbrev execBasisStateVector (S : StateSpaceStrong Cell T) (i : S.boxVertex) : S.execState :=
  S.execPureStateVector i

def execPureProjector (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execDensityOperator :=
  S.spectral.coordinateProjector i

abbrev execBasisProjector (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execDensityOperator :=
  S.execPureProjector i

def mirrorPureStateVector (S : StateSpaceStrong Cell T) (i : S.boxVertex) : S.mirrorState :=
  basisVector (𝕜 := ℂ) i

def mirrorPureProjector (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorDensityOperator :=
  S.spectralBridge.complexCoordinateProjector i

theorem execPureStateVector_apply_same (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execPureStateVector i i = 1 := by
  exact basisVector_apply_same (𝕜 := ExecComplex) i

theorem execPureStateVector_apply_ne (S : StateSpaceStrong Cell T)
    {i j : S.boxVertex} (hij : j ≠ i) :
    S.execPureStateVector i j = 0 := by
  exact basisVector_apply_ne (𝕜 := ExecComplex) hij

theorem execPureStateVector_ne_zero (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execPureStateVector i ≠ 0 := by
  intro hzero
  have hvalue : S.execPureStateVector i i = 0 := by
    simpa using congrFun hzero i
  rw [S.execPureStateVector_apply_same i] at hvalue
  have hre : (1 : ExecComplex).re = 0 := by
    simpa [ExecComplex.zero_re] using congrArg ExecComplex.re hvalue
  norm_num [ExecComplex.one_re] at hre

theorem execPureProjector_apply_same (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execPureProjector i i i = 1 := by
  unfold execPureProjector
  simp [SpectralDecompositionStrong.coordinateProjector]

theorem execPureProjector_ne_zero (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execPureProjector i ≠ 0 := by
  intro hzero
  have hvalue : S.execPureProjector i i i = 0 := by
    simpa using congrFun (congrFun hzero i) i
  rw [S.execPureProjector_apply_same i] at hvalue
  have hre : (1 : ExecComplex).re = 0 := by
    simpa [ExecComplex.zero_re] using congrArg ExecComplex.re hvalue
  norm_num [ExecComplex.one_re] at hre

theorem execPureProjector_isHermitian (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    IsHermitian (S.execPureProjector i) := by
  exact S.spectral.coordinateProjector_isHermitian i

theorem execPureProjector_trace (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execTrace (S.execPureProjector i) = 1 := by
  unfold execTrace execPureProjector
  rw [Matrix.trace]
  simp [SpectralDecompositionStrong.coordinateProjector]

theorem execPureProjector_trace_one (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execIsTraceOne (S.execPureProjector i) := by
  exact S.execPureProjector_trace i

theorem execPureProjector_trace_ne_zero (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execTrace (S.execPureProjector i) ≠ 0 := by
  rw [S.execPureProjector_trace i]
  intro hzero
  have hre : (1 : ExecComplex).re = 0 := by
    simpa [ExecComplex.zero_re] using congrArg ExecComplex.re hzero
  norm_num [ExecComplex.one_re] at hre

theorem execPureProjector_traceNormalize (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.execTraceNormalize (S.execPureProjector i) (1 : ℚ)
      (by simpa [ExecComplex.ofRat] using S.execPureProjector_trace i)
      (show (1 : ℚ) ≠ 0 by norm_num) =
      S.execPureProjector i := by
  unfold execTraceNormalize
  have hOneInv : ExecComplex.ofRat ((1 : ℚ)⁻¹) = (1 : ExecComplex) := by
    apply ExecComplex.ext
    · simp [ExecComplex.ofRat_re, ExecComplex.one_re]
    · simp [ExecComplex.ofRat_im, ExecComplex.one_im]
  rw [hOneInv]
  exact one_smul ExecComplex (S.execPureProjector i)

theorem mirrorPureStateVector_apply_same (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorPureStateVector i i = 1 := by
  exact basisVector_apply_same (𝕜 := ℂ) i

theorem mirrorPureStateVector_apply_ne (S : StateSpaceStrong Cell T)
    {i j : S.boxVertex} (hij : j ≠ i) :
    S.mirrorPureStateVector i j = 0 := by
  exact basisVector_apply_ne (𝕜 := ℂ) hij

theorem mirrorPureStateVector_ne_zero (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorPureStateVector i ≠ 0 := by
  intro hzero
  have hvalue : S.mirrorPureStateVector i i = 0 := by
    simpa using congrFun hzero i
  rw [S.mirrorPureStateVector_apply_same i] at hvalue
  exact one_ne_zero hvalue

theorem mirrorPureProjector_apply_same (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorPureProjector i i i = 1 := by
  unfold mirrorPureProjector
  simp [SpectralBridgeStrong.complexCoordinateProjector_apply]

theorem mirrorPureProjector_ne_zero (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorPureProjector i ≠ 0 := by
  intro hzero
  have hvalue : S.mirrorPureProjector i i i = 0 := by
    simpa using congrFun (congrFun hzero i) i
  rw [S.mirrorPureProjector_apply_same i] at hvalue
  exact one_ne_zero hvalue

theorem mirrorGenerator_isHermitian (S : StateSpaceStrong Cell T) :
    IsHermitian S.mirrorGenerator := by
  exact S.spectralBridge.complexMatrix_isHermitian

theorem mirrorPureProjector_isHermitian (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    IsHermitian (S.mirrorPureProjector i) := by
  exact S.spectralBridge.complexCoordinateProjector_isHermitian i

theorem mirrorPureProjector_trace (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorTrace (S.mirrorPureProjector i) = 1 := by
  unfold mirrorTrace mirrorPureProjector
  rw [Matrix.trace]
  simp [SpectralBridgeStrong.complexCoordinateProjector_apply]

theorem mirrorPureProjector_trace_one (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorIsTraceOne (S.mirrorPureProjector i) := by
  exact S.mirrorPureProjector_trace i

theorem mirrorPureProjector_trace_ne_zero (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorTrace (S.mirrorPureProjector i) ≠ 0 := by
  rw [S.mirrorPureProjector_trace i]
  exact one_ne_zero

theorem mirrorPureProjector_traceNormalize (S : StateSpaceStrong Cell T) (i : S.boxVertex) :
    S.mirrorTraceNormalize (S.mirrorPureProjector i) (1 : ℂ)
      (show (1 : ℂ) ≠ 0 by simp) =
      S.mirrorPureProjector i := by
  unfold mirrorTraceNormalize
  ext j k
  change ((1 : ℂ)⁻¹ * S.mirrorPureProjector i j k) = S.mirrorPureProjector i j k
  rw [inv_one, one_mul]

theorem mirrorTraceNormalize_eq (S : StateSpaceStrong Cell T)
    (ρ : S.mirrorDensityOperator) {Z : ℂ} (hZ : Z ≠ 0) :
    S.mirrorTraceNormalize ρ Z hZ = Z⁻¹ • ρ := by
  rfl

end StateSpaceStrong

namespace StrengtheningS9

open CNNA.PillarA.Finite.StrengtheningS8d
open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullStateSpace (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    StateSpaceStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  StateSpaceStrong.ofSpectralBridge (referenceFullSpectralBridge b p wp)

def variationFullStateSpace (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    StateSpaceStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  StateSpaceStrong.ofSpectralBridge (variationFullSpectralBridge β p wp)

end StrengtheningS9

end CNNA.PillarA.Finite
