import CNNA.PillarA.Finite.SpectralDecompositionC

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

/--
S8d bridge between the operative ExecComplex spectral root and its analytic `ℂ`-mirror.
The bridge is intentionally one-way in the sense of the plan:
`SpectralDecomposition` remains the public operative surface,
while the `ℂ`-mirror is audited and consumed only through explicit transfer lemmas.
-/
structure SpectralBridgeStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SpectralDecompositionStrong Cell T

abbrev SpectralBridgeStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SpectralBridgeStrong (Cell := Cell) T

namespace SpectralBridgeStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (B C : SpectralBridgeStrong Cell T)
    (hsource : B.source = C.source) :
    B = C := by
  cases B with
  | mk sourceB =>
    cases C with
    | mk sourceC =>
      cases hsource
      rfl

def ofSpectral (S : SpectralDecompositionStrong Cell T) :
    SpectralBridgeStrong Cell T where
  source := S

def cast (h : T = U) (B : SpectralBridgeStrong Cell T) :
    SpectralBridgeStrong Cell U := by
  cases h
  exact B

theorem cast_rfl (B : SpectralBridgeStrong Cell T) :
    cast (Cell := Cell) rfl B = B := by
  rfl

abbrev mirror (B : SpectralBridgeStrong Cell T) :
    SpectralDecompositionCStrong Cell T :=
  SpectralDecompositionCStrong.ofSpectral B.source

abbrev boxVertex (B : SpectralBridgeStrong Cell T) :=
  B.source.boxVertex

abbrev execMatrix (B : SpectralBridgeStrong Cell T) :
    Matrix B.boxVertex B.boxVertex ExecComplex :=
  B.source.execMatrix

abbrev complexMatrix (B : SpectralBridgeStrong Cell T) :
    Matrix B.boxVertex B.boxVertex ℂ :=
  B.mirror.complexMatrix

abbrev execFrobeniusSq (B : SpectralBridgeStrong Cell T) : ℚ :=
  B.source.execFrobeniusSq

abbrev execShift (B : SpectralBridgeStrong Cell T) (ε : ℚ) : ℚ :=
  B.source.execShift ε

abbrev complexFrobeniusSq (B : SpectralBridgeStrong Cell T) : ℝ :=
  ExecComplexBridge.Mirror.frobSq B.complexMatrix

abbrev complexShift (B : SpectralBridgeStrong Cell T) (ε : ℚ) : ℝ :=
  ExecComplexBridge.Mirror.deltaRegularization ε B.complexMatrix

abbrev execTrace (B : SpectralBridgeStrong Cell T) : ExecComplex :=
  B.source.spectralTrace

abbrev complexTrace (B : SpectralBridgeStrong Cell T) : ℂ :=
  ExecComplexBridge.toComplex B.execTrace

abbrev execDeterminant (B : SpectralBridgeStrong Cell T) : ExecComplex :=
  B.source.spectralDeterminant

abbrev complexDeterminant (B : SpectralBridgeStrong Cell T) : ℂ :=
  ExecComplexBridge.toComplex B.execDeterminant

abbrev complexCharDetMatrix (B : SpectralBridgeStrong Cell T) (q : ℚ) :
    Matrix B.boxVertex B.boxVertex ℂ :=
  ExecComplexBridge.mapMatrix (B.source.spectralCharDetMatrix q)

abbrev execCharDetEval (B : SpectralBridgeStrong Cell T) (q : ℚ) : ExecComplex :=
  B.source.spectralCharDetEval q

abbrev complexCharDetEval (B : SpectralBridgeStrong Cell T) (q : ℚ) : ℂ :=
  ExecComplexBridge.toComplex (B.execCharDetEval q)

abbrev complexCoordinateSpectralValue (B : SpectralBridgeStrong Cell T)
    (i : B.boxVertex) : ℂ :=
  ExecComplexBridge.toComplex (B.source.coordinateSpectralValue i)

abbrev complexCoordinateProjector (B : SpectralBridgeStrong Cell T)
    (i : B.boxVertex) : Matrix B.boxVertex B.boxVertex ℂ :=
  ExecComplexBridge.mapMatrix (B.source.coordinateProjector i)

abbrev complexCoordinateProjectorSelfCommutator (B : SpectralBridgeStrong Cell T)
    (i : B.boxVertex) : Matrix B.boxVertex B.boxVertex ℂ :=
  ExecComplexBridge.mapMatrix (B.source.coordinateProjectorSelfCommutator i)

theorem mirror_source (B : SpectralBridgeStrong Cell T) :
    B.mirror.source = B.source := by
  rfl

theorem complexMatrix_eq_mapExecMatrix (B : SpectralBridgeStrong Cell T) :
    B.complexMatrix = ExecComplexBridge.mapMatrix B.execMatrix := by
  rfl

theorem complexMatrix_isHermitian (B : SpectralBridgeStrong Cell T) :
    IsHermitian B.complexMatrix := by
  exact B.mirror.complexMatrix_isHermitian

theorem complexFrobeniusSq_eq_execFrobeniusSq (B : SpectralBridgeStrong Cell T) :
    B.complexFrobeniusSq = (B.execFrobeniusSq : ℝ) := by
  simpa [complexFrobeniusSq, complexMatrix, execMatrix, execFrobeniusSq] using
    ExecComplexBridge.Mirror.frobeniusSq_mapExecMat (A := B.execMatrix)

theorem complexShift_eq_execShift (B : SpectralBridgeStrong Cell T) (ε : ℚ) :
    B.complexShift ε = (B.execShift ε : ℝ) := by
  simpa [complexShift, complexMatrix, execMatrix, execShift] using
    ExecComplexBridge.Mirror.shift_mapExecMat (ε := ε) (A := B.execMatrix)

theorem complexTrace_eq_map_execTrace (B : SpectralBridgeStrong Cell T) :
    B.complexTrace = ExecComplexBridge.toComplex B.execTrace := by
  rfl

theorem matrix_trace_eq_complexTrace (B : SpectralBridgeStrong Cell T) :
    Matrix.trace B.complexMatrix = B.complexTrace := by
  simpa [complexTrace, execTrace, complexMatrix, execMatrix,
    SpectralDecompositionStrong.spectralTrace] using
    (ExecComplexBridge.toComplex_sum (s := Finset.univ)
      (f := fun i : B.boxVertex => B.execMatrix i i)).symm

theorem complexDeterminant_eq_map_execDeterminant (B : SpectralBridgeStrong Cell T) :
    B.complexDeterminant = ExecComplexBridge.toComplex B.execDeterminant := by
  rfl

theorem matrix_det_eq_complexDeterminant (B : SpectralBridgeStrong Cell T) :
    Matrix.det B.complexMatrix = B.complexDeterminant := by
  simpa [complexDeterminant, execDeterminant, complexMatrix, execMatrix,
    SpectralDecompositionStrong.spectralDeterminant,
    ExecComplexBridge.toComplexHom_apply,
    ExecComplexBridge.mapSquareMatrix_apply] using
    (RingHom.map_det ExecComplexBridge.toComplexHom B.execMatrix).symm

theorem complexCharDetMatrix_apply (B : SpectralBridgeStrong Cell T) (q : ℚ)
    (i j : B.boxVertex) :
    B.complexCharDetMatrix q i j =
      if i = j then (q : ℂ) - B.complexMatrix i j else -B.complexMatrix i j := by
  by_cases hij : i = j
  · simp [complexCharDetMatrix, SpectralDecompositionStrong.spectralCharDetMatrix,
      B.complexMatrix_eq_mapExecMatrix, hij,
      ExecComplexBridge.mapMatrix, ExecComplexBridge.toComplex_ofRat,
      ExecComplexBridge.toComplex_sub]
  · simp [complexCharDetMatrix, SpectralDecompositionStrong.spectralCharDetMatrix,
      B.complexMatrix_eq_mapExecMatrix, hij,
      ExecComplexBridge.mapMatrix, ExecComplexBridge.toComplex_neg]

theorem complexCharDetEval_eq_map_execCharDetEval
    (B : SpectralBridgeStrong Cell T) (q : ℚ) :
    B.complexCharDetEval q = ExecComplexBridge.toComplex (B.execCharDetEval q) := by
  rfl

theorem matrix_det_charDet_eq_complexCharDetEval
    (B : SpectralBridgeStrong Cell T) (q : ℚ) :
    Matrix.det (B.complexCharDetMatrix q) = B.complexCharDetEval q := by
  simpa [complexCharDetEval, execCharDetEval, complexCharDetMatrix,
    SpectralDecompositionStrong.spectralCharDetEval,
    ExecComplexBridge.toComplexHom_apply,
    ExecComplexBridge.mapSquareMatrix_apply] using
    (RingHom.map_det ExecComplexBridge.toComplexHom
      (B.source.spectralCharDetMatrix q)).symm

theorem complexCoordinateSpectralValue_eq_map
    (B : SpectralBridgeStrong Cell T) (i : B.boxVertex) :
    B.complexCoordinateSpectralValue i =
      ExecComplexBridge.toComplex (B.source.coordinateSpectralValue i) := by
  rfl

theorem complexMatrix_diag_eq_complexCoordinateSpectralValue
    (B : SpectralBridgeStrong Cell T) (i : B.boxVertex) :
    B.complexMatrix i i = B.complexCoordinateSpectralValue i := by
  rfl

theorem complexCoordinateProjector_apply
    (B : SpectralBridgeStrong Cell T) (i j k : B.boxVertex) :
    B.complexCoordinateProjector i j k =
      if j = i then if k = i then 1 else 0 else 0 := by
  unfold complexCoordinateProjector
  rw [ExecComplexBridge.mapMatrix_apply]
  by_cases hji : j = i
  · by_cases hki : k = i
    · simp [SpectralDecompositionStrong.coordinateProjector, hji, hki,
        ExecComplexBridge.toComplex_one]
    · simp [SpectralDecompositionStrong.coordinateProjector, hji, hki,
        ExecComplexBridge.toComplex_zero]
  · simp [SpectralDecompositionStrong.coordinateProjector, hji,
      ExecComplexBridge.toComplex_zero]

theorem complexCoordinateProjector_isHermitian
    (B : SpectralBridgeStrong Cell T) (i : B.boxVertex) :
    IsHermitian (B.complexCoordinateProjector i) := by
  exact ExecComplexBridge.map_isHermitian
    (A := B.source.coordinateProjector i)
    (B.source.coordinateProjector_isHermitian i)

theorem complexCoordinateProjectorSelfCommutator_eq_map
    (B : SpectralBridgeStrong Cell T) (i : B.boxVertex) :
    B.complexCoordinateProjectorSelfCommutator i =
      ExecComplexBridge.mapMatrix (B.source.coordinateProjectorSelfCommutator i) := by
  rfl

theorem complexCoordinateProjectorSelfCommutator_eq_difference
    (B : SpectralBridgeStrong Cell T) (i : B.boxVertex) :
    B.complexCoordinateProjectorSelfCommutator i =
      (B.complexCoordinateProjector i * B.complexCoordinateProjector i) -
        (B.complexCoordinateProjector i * B.complexCoordinateProjector i) := by
  rw [complexCoordinateProjectorSelfCommutator_eq_map]
  rw [SpectralDecompositionStrong.coordinateProjectorSelfCommutator]
  rw [ExecComplexBridge.mapMatrix_sub]
  rw [ExecComplexBridge.mapMatrix_mul]

theorem complexCoordinateProjector_selfCommutator_zero
    (B : SpectralBridgeStrong Cell T) (i : B.boxVertex) :
    B.complexCoordinateProjectorSelfCommutator i = 0 := by
  rw [complexCoordinateProjectorSelfCommutator_eq_map]
  rw [B.source.coordinateProjector_selfCommutator_zero i]
  ext j k
  simp [ExecComplexBridge.mapMatrix, ExecComplexBridge.toComplex_zero]

structure SpectralShadowBridgeCertificate (B : SpectralBridgeStrong Cell T) where
  matrix_identification :
    B.complexMatrix = ExecComplexBridge.mapMatrix B.execMatrix
  hermitian_transfer : IsHermitian B.complexMatrix
  trace_transfer : B.complexTrace = ExecComplexBridge.toComplex B.execTrace
  determinant_transfer :
    B.complexDeterminant = ExecComplexBridge.toComplex B.execDeterminant
  charDet_transfer : ∀ q : ℚ,
    B.complexCharDetEval q = ExecComplexBridge.toComplex (B.execCharDetEval q)

def spectralShadowBridgeCertificate (B : SpectralBridgeStrong Cell T) :
    SpectralShadowBridgeCertificate B where
  matrix_identification := B.complexMatrix_eq_mapExecMatrix
  hermitian_transfer := B.complexMatrix_isHermitian
  trace_transfer := B.complexTrace_eq_map_execTrace
  determinant_transfer := B.complexDeterminant_eq_map_execDeterminant
  charDet_transfer := B.complexCharDetEval_eq_map_execCharDetEval

structure CoordinateProjectorBridgeCertificate (B : SpectralBridgeStrong Cell T)
    (i : B.boxVertex) where
  value_transfer :
    B.complexCoordinateSpectralValue i =
      ExecComplexBridge.toComplex (B.source.coordinateSpectralValue i)
  projector_hermitian : IsHermitian (B.complexCoordinateProjector i)
  projector_selfCommutator_zero :
    B.complexCoordinateProjectorSelfCommutator i = 0

def coordinateProjectorBridgeCertificate (B : SpectralBridgeStrong Cell T)
    (i : B.boxVertex) : CoordinateProjectorBridgeCertificate B i where
  value_transfer := B.complexCoordinateSpectralValue_eq_map i
  projector_hermitian := B.complexCoordinateProjector_isHermitian i
  projector_selfCommutator_zero := B.complexCoordinateProjector_selfCommutator_zero i

end SpectralBridgeStrong

namespace StrengtheningS8d

open CNNA.PillarA.Finite.StrengtheningS8a
open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullSpectralBridge (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    SpectralBridgeStrongOf (ReferenceIdealCellOf b)
      ((referenceToC b).approximant p) :=
  SpectralBridgeStrong.ofSpectral (referenceFullSpectralDecomposition b p wp)

def variationFullSpectralBridge (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    SpectralBridgeStrongOf (VariationIdealCellOf β)
      ((variationToC β).approximant p) :=
  SpectralBridgeStrong.ofSpectral (variationFullSpectralDecomposition β p wp)

end StrengtheningS8d

end CNNA.PillarA.Finite
