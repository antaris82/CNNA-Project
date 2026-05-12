import CNNA.PillarA.DtN.DtN
import CNNA.PillarA.Foundation.RegularizationPolicy
import CNNA.PillarA.Foundation.MatrixNorms

set_option autoImplicit false

namespace CNNA.PillarA.DtN

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite

universe u

structure DtNStabilizedStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : DtNStrong Cell T
  policy : RegularizationPolicy

abbrev DtNStabilizedStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  DtNStabilizedStrong (Cell := Cell) T

namespace DtNStabilizedStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (K R : DtNStabilizedStrong Cell T)
    (hsource : K.source = R.source)
    (hpolicy : K.policy = R.policy) :
    K = R := by
  cases K with
  | mk sourceK policyK =>
    cases R with
    | mk sourceR policyR =>
      cases hsource
      cases hpolicy
      rfl

def ofDtN (K : DtNStrong Cell T) (P : RegularizationPolicy) :
    DtNStabilizedStrong Cell T where
  source := K
  policy := P

def cast (h : T = U) (K : DtNStabilizedStrong Cell T) : DtNStabilizedStrong Cell U := by
  cases h
  exact K

theorem cast_rfl (K : DtNStabilizedStrong Cell T) :
    cast (Cell := Cell) rfl K = K := by
  rfl

abbrev boundaryVertex (K : DtNStabilizedStrong Cell T) :=
  K.source.boundaryVertex

abbrev boundaryPotential (K : DtNStabilizedStrong Cell T) :=
  K.boundaryVertex → ℝ

abbrev rawBoundaryOperator (K : DtNStabilizedStrong Cell T) :
    Matrix K.boundaryVertex K.boundaryVertex ℝ :=
  K.source.boundaryOperator

def symmetrizedBoundaryOperator (K : DtNStabilizedStrong Cell T) :
    Matrix K.boundaryVertex K.boundaryVertex ℝ :=
  K.rawBoundaryOperator + Matrix.transpose K.rawBoundaryOperator

abbrev symmetrizedOperator (K : DtNStabilizedStrong Cell T) :
    Matrix K.boundaryVertex K.boundaryVertex ℝ :=
  K.symmetrizedBoundaryOperator

def regularizationPolicy (K : DtNStabilizedStrong Cell T) : RegularizationPolicy :=
  K.policy

def epsilon (K : DtNStabilizedStrong Cell T) : ℝ :=
  K.regularizationPolicy.epsilonReal

theorem epsilon_pos (K : DtNStabilizedStrong Cell T) :
    0 < K.epsilon := by
  exact K.regularizationPolicy.epsilonReal_pos

theorem epsilon_nonneg (K : DtNStabilizedStrong Cell T) :
    0 ≤ K.epsilon := by
  exact K.regularizationPolicy.epsilonReal_nonneg

def comparisonWeightQ (K : DtNStabilizedStrong Cell T) : ℚ :=
  K.source.source.policy.constantWeightQ

theorem comparisonWeightQ_pos (K : DtNStabilizedStrong Cell T) :
    0 < K.comparisonWeightQ := by
  exact K.source.source.policy.beta_pos

def comparisonDegreeQ (K : DtNStabilizedStrong Cell T) : ℚ :=
  ((Fintype.card K.boundaryVertex - 1 : Nat) : ℚ) * K.comparisonWeightQ

def comparisonOperator (K : DtNStabilizedStrong Cell T) :
    Matrix K.boundaryVertex K.boundaryVertex ExecComplex :=
  fun i j =>
    if i = j then
      ExecComplex.ofRat K.comparisonDegreeQ
    else
      -ExecComplex.ofRat K.comparisonWeightQ

def comparisonFrobeniusSq (K : DtNStabilizedStrong Cell T) : ℚ :=
  MatrixNorm.Exec.frobeniusSq K.comparisonOperator

def regularizationShiftQ (K : DtNStabilizedStrong Cell T) : ℚ :=
  K.regularizationPolicy.canonicalShift K.comparisonOperator

def regularizationShift (K : DtNStabilizedStrong Cell T) : ℝ :=
  K.regularizationShiftQ

theorem regularizationShiftQ_pos (K : DtNStabilizedStrong Cell T) :
    0 < K.regularizationShiftQ := by
  exact K.regularizationPolicy.canonicalShift_pos K.comparisonOperator

theorem regularizationShift_pos (K : DtNStabilizedStrong Cell T) :
    0 < K.regularizationShift := by
  change (0 : ℝ) < ((K.regularizationShiftQ : ℚ) : ℝ)
  exact_mod_cast K.regularizationShiftQ_pos

theorem regularizationShift_nonneg (K : DtNStabilizedStrong Cell T) :
    0 ≤ K.regularizationShift := by
  exact le_of_lt K.regularizationShift_pos

theorem regularizationShiftQ_ge_epsilonQ (K : DtNStabilizedStrong Cell T) :
    K.regularizationPolicy.epsilon ≤ K.regularizationShiftQ := by
  exact K.regularizationPolicy.canonicalShift_ge_epsilon K.comparisonOperator

theorem regularizationShift_ge_epsilon (K : DtNStabilizedStrong Cell T) :
    K.epsilon ≤ K.regularizationShift := by
  change ((K.regularizationPolicy.epsilon : ℚ) : ℝ) ≤ ((K.regularizationShiftQ : ℚ) : ℝ)
  exact_mod_cast K.regularizationShiftQ_ge_epsilonQ

theorem comparisonOperator_apply_diag
    (K : DtNStabilizedStrong Cell T) (i : K.boundaryVertex) :
    K.comparisonOperator i i = ExecComplex.ofRat K.comparisonDegreeQ := by
  unfold comparisonOperator
  split_ifs with h
  · rfl
  · exact False.elim (h rfl)

theorem comparisonOperator_apply_of_ne
    (K : DtNStabilizedStrong Cell T) {i j : K.boundaryVertex} (hij : i ≠ j) :
    K.comparisonOperator i j = -ExecComplex.ofRat K.comparisonWeightQ := by
  unfold comparisonOperator
  split_ifs with h
  · exact False.elim (hij h)
  · rfl

theorem comparisonDegreeQ_nonneg (K : DtNStabilizedStrong Cell T) :
    0 ≤ K.comparisonDegreeQ := by
  refine mul_nonneg ?_ ?_
  · exact_mod_cast Nat.zero_le (Fintype.card K.boundaryVertex - 1)
  · exact le_of_lt K.comparisonWeightQ_pos

theorem regularizationShift_eq_policy_canonicalShift (K : DtNStabilizedStrong Cell T) :
    K.regularizationShift = K.regularizationPolicy.canonicalShift K.comparisonOperator := by
  rfl

def stabilizedOperator (K : DtNStabilizedStrong Cell T) :
    Matrix K.boundaryVertex K.boundaryVertex ℝ :=
  K.rawBoundaryOperator +
    K.regularizationShift • (1 : Matrix K.boundaryVertex K.boundaryVertex ℝ)

def stabilizedSymmetricOperator (K : DtNStabilizedStrong Cell T) :
    Matrix K.boundaryVertex K.boundaryVertex ℝ :=
  K.symmetrizedBoundaryOperator +
    K.regularizationShift • (1 : Matrix K.boundaryVertex K.boundaryVertex ℝ)

def stabilizedFlux (K : DtNStabilizedStrong Cell T)
    (φ : K.boundaryPotential) :
    K.boundaryPotential :=
  (K.stabilizedOperator).mulVec φ

theorem symmetrizedBoundaryOperator_transpose (K : DtNStabilizedStrong Cell T) :
    Matrix.transpose K.symmetrizedBoundaryOperator = K.symmetrizedBoundaryOperator := by
  ext i j
  simp [symmetrizedBoundaryOperator, rawBoundaryOperator, add_comm]

theorem symmetrizedOperator_transpose (K : DtNStabilizedStrong Cell T) :
    Matrix.transpose K.symmetrizedOperator = K.symmetrizedOperator := by
  exact K.symmetrizedBoundaryOperator_transpose

theorem stabilizedOperator_eq_raw_plus_shift (K : DtNStabilizedStrong Cell T) :
    K.stabilizedOperator =
      K.rawBoundaryOperator +
        K.regularizationShift • (1 : Matrix K.boundaryVertex K.boundaryVertex ℝ) := by
  rfl

theorem stabilizedSymmetricOperator_transpose (K : DtNStabilizedStrong Cell T) :
    Matrix.transpose K.stabilizedSymmetricOperator = K.stabilizedSymmetricOperator := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [stabilizedSymmetricOperator, symmetrizedBoundaryOperator, rawBoundaryOperator]
  · have hji : j ≠ i := by
      exact fun h => hij h.symm
    simp [stabilizedSymmetricOperator, symmetrizedBoundaryOperator, rawBoundaryOperator,
      hij, hji, add_comm]

theorem stabilizedFlux_eq_mulVec
    (K : DtNStabilizedStrong Cell T) (φ : K.boundaryPotential) :
    K.stabilizedFlux φ = (K.stabilizedOperator).mulVec φ := by
  rfl

end DtNStabilizedStrong

namespace StrengtheningS6

open CNNA.PillarA.Finite.StrengtheningS4
open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5

def referenceDefaultRegularizationPolicy : RegularizationPolicy :=
  RegularizationPolicy.reference 1 (show (0 : ℚ) < 1 by exact zero_lt_one)

def referenceFullDtNStabilized (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    : DtNStabilizedStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  DtNStabilizedStrong.ofDtN (referenceFullDtN b p wp) rp

def variationFullDtNStabilized (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    : DtNStabilizedStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  DtNStabilizedStrong.ofDtN (variationFullDtN β p wp) rp

end StrengtheningS6

end CNNA.PillarA.DtN
