import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CNNA.PillarA.Finite.DirichletLaplacian

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

/--
S8a operative spectral root surface.
This file deliberately stays on the public `ExecComplex` strand.
The analytic `ℂ`-mirror is split into `Finite/SpectralDecompositionC.lean`,
and all comparison / transfer statements are funneled through
`Finite/SpectralBridge.lean`.
-/
structure SpectralDecompositionStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : DirichletLaplacianStrong Cell T

abbrev SpectralDecompositionStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SpectralDecompositionStrong (Cell := Cell) T

abbrev SpectralDecompositionOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SpectralDecompositionStrong (Cell := Cell) T

namespace SpectralDecompositionStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (S R : SpectralDecompositionStrong Cell T)
    (hsource : S.source = R.source) :
    S = R := by
  cases S with
  | mk sourceS =>
    cases R with
    | mk sourceR =>
      cases hsource
      rfl

def ofDirichlet (D : DirichletLaplacianStrong Cell T) :
    SpectralDecompositionStrong Cell T where
  source := D

def cast (h : T = U) (S : SpectralDecompositionStrong Cell T) :
    SpectralDecompositionStrong Cell U := by
  cases h
  exact S

theorem cast_rfl (S : SpectralDecompositionStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

abbrev boxVertex (S : SpectralDecompositionStrong Cell T) :=
  S.source.boxVertex

abbrev boundaryVertex (S : SpectralDecompositionStrong Cell T) :=
  S.source.boundaryVertex

abbrev interiorVertex (S : SpectralDecompositionStrong Cell T) :=
  S.source.interiorVertex

abbrev sourceMatrix (S : SpectralDecompositionStrong Cell T) :
    Matrix S.boxVertex S.boxVertex ℝ :=
  S.source.matrix

abbrev sourceFrobeniusSq (S : SpectralDecompositionStrong Cell T) : ℝ :=
  S.source.frobSq

abbrev weightQ (S : SpectralDecompositionStrong Cell T) : ℚ :=
  S.source.policy.constantWeightQ

theorem weightQ_pos (S : SpectralDecompositionStrong Cell T) :
    0 < S.weightQ := by
  exact S.source.policy.beta_pos

theorem weightQ_nonneg (S : SpectralDecompositionStrong Cell T) :
    0 ≤ S.weightQ := by
  exact le_of_lt S.weightQ_pos

def offDiagQ (S : SpectralDecompositionStrong Cell T)
    (i j : S.boxVertex) : ℚ :=
  if j = i then 0 else S.weightQ

def degreeQ (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : ℚ :=
  ∑ j : S.boxVertex, S.offDiagQ i j

theorem offDiagQ_self (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) :
    S.offDiagQ i i = 0 := by
  simp [offDiagQ]

theorem offDiagQ_of_ne (S : SpectralDecompositionStrong Cell T)
    {i j : S.boxVertex} (hij : i ≠ j) :
    S.offDiagQ i j = S.weightQ := by
  have hji : j ≠ i := by
    exact fun h => hij h.symm
  simp [offDiagQ, hji]

theorem offDiagQ_symm (S : SpectralDecompositionStrong Cell T)
    (i j : S.boxVertex) :
    S.offDiagQ i j = S.offDiagQ j i := by
  by_cases hij : i = j
  · subst hij
    simp [offDiagQ]
  · have hji : j ≠ i := by
      exact fun h => hij h.symm
    simp [offDiagQ, hij, hji]

def execMatrix (S : SpectralDecompositionStrong Cell T) :
    Matrix S.boxVertex S.boxVertex ExecComplex :=
  fun i j =>
    if i = j then
      ExecComplex.ofRat (S.degreeQ i)
    else
      -ExecComplex.ofRat (S.offDiagQ i j)

def execFrobeniusSq (S : SpectralDecompositionStrong Cell T) : ℚ :=
  MatrixNorm.Exec.frobeniusSq S.execMatrix

def execZeroTest (S : SpectralDecompositionStrong Cell T) : Bool :=
  MatrixNorm.Exec.zeroTest S.execMatrix

def execShift (S : SpectralDecompositionStrong Cell T) (ε : ℚ) : ℚ :=
  MatrixNorm.Exec.shift ε S.execMatrix

theorem execMatrix_apply_diag (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) :
    S.execMatrix i i = ExecComplex.ofRat (S.degreeQ i) := by
  unfold execMatrix
  split_ifs with h
  · rfl
  · exact False.elim (h rfl)

theorem execMatrix_apply_of_ne (S : SpectralDecompositionStrong Cell T)
    {i j : S.boxVertex} (hij : i ≠ j) :
    S.execMatrix i j = -ExecComplex.ofRat (S.offDiagQ i j) := by
  unfold execMatrix
  split_ifs with h
  · exact False.elim (hij h)
  · rfl

theorem execMatrix_isHermitian (S : SpectralDecompositionStrong Cell T) :
    IsHermitian S.execMatrix := by
  rw [isHermitian_iff]
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    apply ExecComplex.ext
    · simp [Matrix.conjTranspose, execMatrix, ExecComplex.star_ofRat,
        ExecComplex.ofRat_re]
    · simp [Matrix.conjTranspose, execMatrix, ExecComplex.star_ofRat,
        ExecComplex.ofRat_im]
  · have hji : j ≠ i := by
      exact fun h => hij h.symm
    apply ExecComplex.ext
    · simp [Matrix.conjTranspose, execMatrix, hij, hji, offDiagQ,
        ExecComplex.star_ofRat, ExecComplex.neg_re,
        ExecComplex.ofRat_re]
    · simp [Matrix.conjTranspose, execMatrix, hij, hji, offDiagQ,
        ExecComplex.star_ofRat, ExecComplex.neg_im,
        ExecComplex.ofRat_im]

def execHermitianMatrix (S : SpectralDecompositionStrong Cell T) :
    HermitianMatrix (𝕜 := ExecComplex) (ι := S.boxVertex) where
  matrix := S.execMatrix
  hermitian := S.execMatrix_isHermitian

def spectralTrace (S : SpectralDecompositionStrong Cell T) : ExecComplex :=
  Matrix.trace S.execMatrix

def spectralDeterminant (S : SpectralDecompositionStrong Cell T) : ExecComplex :=
  Matrix.det S.execMatrix

def spectralCharDetMatrix (S : SpectralDecompositionStrong Cell T) (q : ℚ) :
    Matrix S.boxVertex S.boxVertex ExecComplex :=
  fun i j =>
    if i = j then
      ExecComplex.ofRat q - S.execMatrix i j
    else
      -S.execMatrix i j

def spectralCharDetEval (S : SpectralDecompositionStrong Cell T) (q : ℚ) : ExecComplex :=
  Matrix.det (S.spectralCharDetMatrix q)

structure SpectralShadow (S : SpectralDecompositionStrong Cell T) where
  trace : ExecComplex
  determinant : ExecComplex
  charDetEval : ℚ → ExecComplex

def spectralShadow (S : SpectralDecompositionStrong Cell T) : SpectralShadow S where
  trace := S.spectralTrace
  determinant := S.spectralDeterminant
  charDetEval := S.spectralCharDetEval

def coordinateSpectralValue (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : ExecComplex :=
  S.execMatrix i i

def coordinateSpectralResidual (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : S.boxVertex → ExecComplex :=
  fun j => if j = i then 0 else S.execMatrix j i

structure CoordinateSpectralCandidate (S : SpectralDecompositionStrong Cell T) where
  index : S.boxVertex
  value : ExecComplex
  residual : S.boxVertex → ExecComplex

def coordinateSpectralCandidate (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : CoordinateSpectralCandidate S where
  index := i
  value := S.coordinateSpectralValue i
  residual := S.coordinateSpectralResidual i

def coordinateProjector (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : Matrix S.boxVertex S.boxVertex ExecComplex :=
  fun j k => if j = i then if k = i then 1 else 0 else 0

theorem coordinateProjector_isHermitian (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) :
    IsHermitian (S.coordinateProjector i) := by
  rw [isHermitian_iff]
  apply Matrix.ext
  intro j k
  by_cases hj : j = i <;> by_cases hk : k = i
  · subst j
    subst k
    simp [Matrix.conjTranspose, coordinateProjector]
  · subst j
    simp [Matrix.conjTranspose, coordinateProjector, hk]
  · subst k
    simp [Matrix.conjTranspose, coordinateProjector, hj]
  · simp [Matrix.conjTranspose, coordinateProjector, hj, hk]

def coordinateProjectorSelfCommutator (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : Matrix S.boxVertex S.boxVertex ExecComplex :=
  (S.coordinateProjector i * S.coordinateProjector i) -
    (S.coordinateProjector i * S.coordinateProjector i)

theorem coordinateProjector_selfCommutator_zero (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) :
    S.coordinateProjectorSelfCommutator i = 0 := by
  simp [coordinateProjectorSelfCommutator]

structure CoordinateProjectorCertificate (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) where
  hermitian : IsHermitian (S.coordinateProjector i)
  selfCommutator_zero : S.coordinateProjectorSelfCommutator i = 0

def coordinateProjectorCertificate (S : SpectralDecompositionStrong Cell T)
    (i : S.boxVertex) : CoordinateProjectorCertificate S i where
  hermitian := S.coordinateProjector_isHermitian i
  selfCommutator_zero := S.coordinateProjector_selfCommutator_zero i

theorem execFrobeniusSq_nonneg (S : SpectralDecompositionStrong Cell T) :
    0 ≤ S.execFrobeniusSq := by
  exact MatrixNorm.Exec.frobeniusSq_nonneg S.execMatrix

theorem execZeroTest_eq_true_iff (S : SpectralDecompositionStrong Cell T) :
    S.execZeroTest = true ↔ S.execMatrix = 0 := by
  exact MatrixNorm.Exec.zeroTest_eq_true_iff S.execMatrix

theorem execFrobeniusSq_eq_zero_iff (S : SpectralDecompositionStrong Cell T) :
    S.execFrobeniusSq = 0 ↔ S.execMatrix = 0 := by
  exact MatrixNorm.Exec.frobeniusSq_eq_zero_iff S.execMatrix

theorem execShift_eq_deltaRegularization (S : SpectralDecompositionStrong Cell T) (ε : ℚ) :
    S.execShift ε = MatrixNorm.Exec.deltaRegularization ε S.execMatrix := by
  exact MatrixNorm.Exec.shift_eq_deltaRegularization ε S.execMatrix

structure SpectralCertificate (S : SpectralDecompositionStrong Cell T) where
  hermitian : IsHermitian S.execMatrix
  frobeniusSq_nonneg : 0 ≤ S.execFrobeniusSq
  zeroTest_spec : S.execZeroTest = true ↔ S.execMatrix = 0

def spectralCertificate (S : SpectralDecompositionStrong Cell T) : S.SpectralCertificate where
  hermitian := S.execMatrix_isHermitian
  frobeniusSq_nonneg := S.execFrobeniusSq_nonneg
  zeroTest_spec := S.execZeroTest_eq_true_iff

end SpectralDecompositionStrong

namespace StrengtheningS8a

open CNNA.PillarA.Finite.StrengtheningS4
open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullSpectralDecomposition (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    SpectralDecompositionStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  SpectralDecompositionStrong.ofDirichlet (referenceFullDirichletLaplacian b p wp)

def variationFullSpectralDecomposition (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    SpectralDecompositionStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  SpectralDecompositionStrong.ofDirichlet (variationFullDirichletLaplacian β p wp)

end StrengtheningS8a

end CNNA.PillarA.Finite
