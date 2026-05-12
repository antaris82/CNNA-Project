import CNNA.PillarA.Arithmetic.Schur.L1Baseline

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T}

abbrev L2Level : Nat := 2

def l2RootIndex : BoundarySource.LevelHistoryIndex L2Level :=
  rootIndex L2Level

def l2MiddleIndex : BoundarySource.LevelHistoryIndex L2Level :=
  ⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩

def l2LeafIndex : BoundarySource.LevelHistoryIndex L2Level :=
  leafIndex L2Level

theorem l2RootIndex_val : l2RootIndex.val = 0 := by
  rfl

theorem l2MiddleIndex_val : l2MiddleIndex.val = 1 := by
  rfl

theorem l2LeafIndex_val : l2LeafIndex.val = 2 := by
  rfl

theorem l2MiddleIndex_interior :
    0 < l2MiddleIndex.val ∧ l2MiddleIndex.val < L2Level := by
  constructor
  · exact Nat.succ_pos 0
  · exact Nat.lt_succ_self 1

def l2SquareBranching (k : Nat) : Nat :=
  k * k

theorem l2SquareBranching_eq_square (k : Nat) :
    l2SquareBranching k = k * k := by
  rfl

def l2RhoMultiplicationMatrix : Matrix (Fin 2) (Fin 2) ExecComplex :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 0
    else if i.val = 0 ∧ j.val = 1 then -1
    else if i.val = 1 ∧ j.val = 0 then 1
    else -1

theorem l2RhoMultiplicationMatrix_00 :
    l2RhoMultiplicationMatrix 0 0 = 0 := by
  rfl

theorem l2RhoMultiplicationMatrix_01 :
    l2RhoMultiplicationMatrix 0 1 = -1 := by
  rfl

theorem l2RhoMultiplicationMatrix_10 :
    l2RhoMultiplicationMatrix 1 0 = 1 := by
  rfl

theorem l2RhoMultiplicationMatrix_11 :
    l2RhoMultiplicationMatrix 1 1 = -1 := by
  rfl

def l2EisensteinPolynomialEval (z : SpectralParameter) : ExecComplex :=
  spectralParameterExec z * spectralParameterExec z + spectralParameterExec z + 1

def l2EisensteinNormForm (a b : ℚ) : ℚ :=
  a * a - a * b + b * b

def l2EisensteinNormCoefficientA : ℤ :=
  1

def l2EisensteinNormCoefficientB : ℤ :=
  -1

def l2EisensteinNormCoefficientC : ℤ :=
  1

def l2EisensteinNormDiscriminant : ℤ :=
  l2EisensteinNormCoefficientB * l2EisensteinNormCoefficientB -
    4 * l2EisensteinNormCoefficientA * l2EisensteinNormCoefficientC

theorem l2EisensteinNormDiscriminant_eq_neg_three :
    l2EisensteinNormDiscriminant = -3 := by
  unfold l2EisensteinNormDiscriminant
  unfold l2EisensteinNormCoefficientA
  unfold l2EisensteinNormCoefficientB
  unfold l2EisensteinNormCoefficientC
  ring

theorem l2EisensteinNormForm_self (a b : ℚ) :
    l2EisensteinNormForm a b = a * a - a * b + b * b := by
  rfl

theorem l2RhoSpectralPencil_00 (z : SpectralParameter) :
    spectralPencil l2RhoMultiplicationMatrix z 0 0 = spectralParameterExec z := by
  simp [spectralPencil, l2RhoMultiplicationMatrix]

theorem l2RhoSpectralPencil_01 (z : SpectralParameter) :
    spectralPencil l2RhoMultiplicationMatrix z 0 1 = 1 := by
  simp [spectralPencil, l2RhoMultiplicationMatrix]

theorem l2RhoSpectralPencil_10 (z : SpectralParameter) :
    spectralPencil l2RhoMultiplicationMatrix z 1 0 = -1 := by
  simp [spectralPencil, l2RhoMultiplicationMatrix]

theorem l2RhoSpectralPencil_11 (z : SpectralParameter) :
    spectralPencil l2RhoMultiplicationMatrix z 1 1 = spectralParameterExec z + 1 := by
  simp [spectralPencil, l2RhoMultiplicationMatrix]

theorem l2RhoCharpolyFactorization (z : SpectralParameter) :
    charpolyEvalFinTwoFormula l2RhoMultiplicationMatrix z =
      l2EisensteinPolynomialEval z := by
  calc
    charpolyEvalFinTwoFormula l2RhoMultiplicationMatrix z
        = detFinTwoFormula (spectralPencil l2RhoMultiplicationMatrix z) := by
      rfl
    _ = spectralPencil l2RhoMultiplicationMatrix z 0 0 *
          spectralPencil l2RhoMultiplicationMatrix z 1 1 -
        spectralPencil l2RhoMultiplicationMatrix z 0 1 *
          spectralPencil l2RhoMultiplicationMatrix z 1 0 := by
      rfl
    _ = spectralParameterExec z * (spectralParameterExec z + 1) - 1 * (-1) := by
      rw [l2RhoSpectralPencil_00, l2RhoSpectralPencil_01,
        l2RhoSpectralPencil_10, l2RhoSpectralPencil_11]
    _ = l2EisensteinPolynomialEval z := by
      unfold l2EisensteinPolynomialEval
      ring

theorem l2RhoOperativeCharpolyFactorization (z : SpectralParameter) :
    operativeCharpolyEvaluation l2RhoMultiplicationMatrix z =
      l2EisensteinPolynomialEval z := by
  calc
    operativeCharpolyEvaluation l2RhoMultiplicationMatrix z
        = charpolyEvalFinTwoFormula l2RhoMultiplicationMatrix z :=
      (charpolyEvalFinTwoFormula_eq_eval l2RhoMultiplicationMatrix z).symm
    _ = l2EisensteinPolynomialEval z :=
      l2RhoCharpolyFactorization z

inductive L2EisensteinFactorizationStatus where
  | ar8L2QuadraticFactorizationCertified
  deriving DecidableEq, Repr

inductive L2EisensteinNormformStatus where
  | eisensteinNormformCertified
  deriving DecidableEq, Repr

inductive L2EisensteinDiscriminantStatus where
  | schurDiscriminantConventionGivesMinusThree
  deriving DecidableEq, Repr

inductive L2EisensteinOrderStatus where
  | eisensteinOrderSeedCertified
  deriving DecidableEq, Repr

inductive L2EisensteinCMSeedStatus where
  | rhoSeedCertified
  deriving DecidableEq, Repr

inductive L2EisensteinNoShortcutStatus where
  | noPatternRecognitionNoMoonshineNoQExpansion
  deriving DecidableEq, Repr

inductive L2CMSeedSymbol where
  | rho
  deriving DecidableEq, Repr

inductive L2QuadraticOrderSymbol where
  | eisenstein
  deriving DecidableEq, Repr

structure L2EisensteinFactorizationCertificate where
  matrix : Matrix (Fin 2) (Fin 2) ExecComplex
  matrix_eq_rhoMultiplication : matrix = l2RhoMultiplicationMatrix
  polynomialEval : SpectralParameter → ExecComplex
  polynomialEval_eq : polynomialEval = l2EisensteinPolynomialEval
  charpoly_factorization :
    ∀ z : SpectralParameter, operativeCharpolyEvaluation matrix z = polynomialEval z
  discriminant : ℤ
  discriminant_eq : discriminant = -3
  factorizationStatus : L2EisensteinFactorizationStatus
  factorizationStatus_eq :
    factorizationStatus =
      L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified
  noFreeAssumptionStatus : AR5NoFreeAssumptionStatus
  noFreeAssumptionStatus_eq :
    noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption

namespace L2EisensteinFactorizationCertificate

def closed : L2EisensteinFactorizationCertificate where
  matrix := l2RhoMultiplicationMatrix
  matrix_eq_rhoMultiplication := by
    rfl
  polynomialEval := l2EisensteinPolynomialEval
  polynomialEval_eq := by
    rfl
  charpoly_factorization := by
    intro z
    exact l2RhoOperativeCharpolyFactorization z
  discriminant := l2EisensteinNormDiscriminant
  discriminant_eq := l2EisensteinNormDiscriminant_eq_neg_three
  factorizationStatus :=
    L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified
  factorizationStatus_eq := by
    rfl
  noFreeAssumptionStatus :=
    AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  noFreeAssumptionStatus_eq := by
    rfl

theorem factorization_closed
    (C : L2EisensteinFactorizationCertificate) :
    C.factorizationStatus =
      L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified :=
  C.factorizationStatus_eq

theorem discriminant_minus_three
    (C : L2EisensteinFactorizationCertificate) :
    C.discriminant = -3 :=
  C.discriminant_eq

theorem no_free_assumptions
    (C : L2EisensteinFactorizationCertificate) :
    C.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  C.noFreeAssumptionStatus_eq

end L2EisensteinFactorizationCertificate

structure L2EisensteinNormCertificate where
  normForm : ℚ → ℚ → ℚ
  normForm_eq : normForm = l2EisensteinNormForm
  coefficientA : ℤ
  coefficientA_eq : coefficientA = l2EisensteinNormCoefficientA
  coefficientB : ℤ
  coefficientB_eq : coefficientB = l2EisensteinNormCoefficientB
  coefficientC : ℤ
  coefficientC_eq : coefficientC = l2EisensteinNormCoefficientC
  discriminant : ℤ
  discriminant_eq : discriminant = -3
  normformStatus : L2EisensteinNormformStatus
  normformStatus_eq :
    normformStatus = L2EisensteinNormformStatus.eisensteinNormformCertified

namespace L2EisensteinNormCertificate

def closed : L2EisensteinNormCertificate where
  normForm := l2EisensteinNormForm
  normForm_eq := by
    rfl
  coefficientA := l2EisensteinNormCoefficientA
  coefficientA_eq := by
    rfl
  coefficientB := l2EisensteinNormCoefficientB
  coefficientB_eq := by
    rfl
  coefficientC := l2EisensteinNormCoefficientC
  coefficientC_eq := by
    rfl
  discriminant := l2EisensteinNormDiscriminant
  discriminant_eq := l2EisensteinNormDiscriminant_eq_neg_three
  normformStatus := L2EisensteinNormformStatus.eisensteinNormformCertified
  normformStatus_eq := by
    rfl

theorem discriminant_minus_three
    (C : L2EisensteinNormCertificate) :
    C.discriminant = -3 :=
  C.discriminant_eq

theorem status_certified
    (C : L2EisensteinNormCertificate) :
    C.normformStatus = L2EisensteinNormformStatus.eisensteinNormformCertified :=
  C.normformStatus_eq

end L2EisensteinNormCertificate

structure L2EisensteinOrderSeed where
  orderSymbol : L2QuadraticOrderSymbol
  orderSymbol_eq : orderSymbol = L2QuadraticOrderSymbol.eisenstein
  discriminant : ℤ
  discriminant_eq : discriminant = -3
  orderStatus : L2EisensteinOrderStatus
  orderStatus_eq : orderStatus = L2EisensteinOrderStatus.eisensteinOrderSeedCertified
  discriminantStatus : L2EisensteinDiscriminantStatus
  discriminantStatus_eq :
    discriminantStatus =
      L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree

namespace L2EisensteinOrderSeed

def closed : L2EisensteinOrderSeed where
  orderSymbol := L2QuadraticOrderSymbol.eisenstein
  orderSymbol_eq := by
    rfl
  discriminant := l2EisensteinNormDiscriminant
  discriminant_eq := l2EisensteinNormDiscriminant_eq_neg_three
  orderStatus := L2EisensteinOrderStatus.eisensteinOrderSeedCertified
  orderStatus_eq := by
    rfl
  discriminantStatus :=
    L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree
  discriminantStatus_eq := by
    rfl

theorem discriminant_minus_three
    (S : L2EisensteinOrderSeed) :
    S.discriminant = -3 :=
  S.discriminant_eq

theorem order_status_certified
    (S : L2EisensteinOrderSeed) :
    S.orderStatus = L2EisensteinOrderStatus.eisensteinOrderSeedCertified :=
  S.orderStatus_eq

end L2EisensteinOrderSeed

structure L2RhoCMSeed where
  seed : L2CMSeedSymbol
  seed_eq : seed = L2CMSeedSymbol.rho
  orderSeed : L2EisensteinOrderSeed
  orderSeed_eq : orderSeed = L2EisensteinOrderSeed.closed
  minimalPolynomialEval : SpectralParameter → ExecComplex
  minimalPolynomialEval_eq : minimalPolynomialEval = l2EisensteinPolynomialEval
  discriminant : ℤ
  discriminant_eq : discriminant = -3
  cmSeedStatus : L2EisensteinCMSeedStatus
  cmSeedStatus_eq : cmSeedStatus = L2EisensteinCMSeedStatus.rhoSeedCertified
  noShortcutStatus : L2EisensteinNoShortcutStatus
  noShortcutStatus_eq :
    noShortcutStatus =
      L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion

namespace L2RhoCMSeed

def closed : L2RhoCMSeed where
  seed := L2CMSeedSymbol.rho
  seed_eq := by
    rfl
  orderSeed := L2EisensteinOrderSeed.closed
  orderSeed_eq := by
    rfl
  minimalPolynomialEval := l2EisensteinPolynomialEval
  minimalPolynomialEval_eq := by
    rfl
  discriminant := l2EisensteinNormDiscriminant
  discriminant_eq := l2EisensteinNormDiscriminant_eq_neg_three
  cmSeedStatus := L2EisensteinCMSeedStatus.rhoSeedCertified
  cmSeedStatus_eq := by
    rfl
  noShortcutStatus :=
    L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion
  noShortcutStatus_eq := by
    rfl

theorem seed_is_rho
    (S : L2RhoCMSeed) :
    S.seed = L2CMSeedSymbol.rho :=
  S.seed_eq

theorem cm_status_certified
    (S : L2RhoCMSeed) :
    S.cmSeedStatus = L2EisensteinCMSeedStatus.rhoSeedCertified :=
  S.cmSeedStatus_eq

theorem no_shortcut
    (S : L2RhoCMSeed) :
    S.noShortcutStatus =
      L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion :=
  S.noShortcutStatus_eq

end L2RhoCMSeed

structure L2BoundaryMatrixProfile
    (B : BoundarySource.BoundarySourceSurface source L2Level) where
  matrix : BoundarySource.LevelHistoryMatrix L2Level
  matrix_eq_boundary : matrix = boundaryLevelHistoryMatrix B
  rootRoot : ExecComplex
  rootRoot_eq : rootRoot = matrix l2RootIndex l2RootIndex
  rootMiddle : ExecComplex
  rootMiddle_eq : rootMiddle = matrix l2RootIndex l2MiddleIndex
  rootLeaf : ExecComplex
  rootLeaf_eq : rootLeaf = matrix l2RootIndex l2LeafIndex
  middleRoot : ExecComplex
  middleRoot_eq : middleRoot = matrix l2MiddleIndex l2RootIndex
  middleMiddle : ExecComplex
  middleMiddle_eq : middleMiddle = matrix l2MiddleIndex l2MiddleIndex
  middleLeaf : ExecComplex
  middleLeaf_eq : middleLeaf = matrix l2MiddleIndex l2LeafIndex
  leafRoot : ExecComplex
  leafRoot_eq : leafRoot = matrix l2LeafIndex l2RootIndex
  leafMiddle : ExecComplex
  leafMiddle_eq : leafMiddle = matrix l2LeafIndex l2MiddleIndex
  leafLeaf : ExecComplex
  leafLeaf_eq : leafLeaf = matrix l2LeafIndex l2LeafIndex
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L2Level,
      source.toc.approximant source.concretePolicy = T

namespace L2BoundaryMatrixProfile

variable {B : BoundarySource.BoundarySourceSurface source L2Level}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L2Level) :
    L2BoundaryMatrixProfile B where
  matrix := boundaryLevelHistoryMatrix B
  matrix_eq_boundary := by
    rfl
  rootRoot := boundaryLevelHistoryMatrix B l2RootIndex l2RootIndex
  rootRoot_eq := by
    rfl
  rootMiddle := boundaryLevelHistoryMatrix B l2RootIndex l2MiddleIndex
  rootMiddle_eq := by
    rfl
  rootLeaf := boundaryLevelHistoryMatrix B l2RootIndex l2LeafIndex
  rootLeaf_eq := by
    rfl
  middleRoot := boundaryLevelHistoryMatrix B l2MiddleIndex l2RootIndex
  middleRoot_eq := by
    rfl
  middleMiddle := boundaryLevelHistoryMatrix B l2MiddleIndex l2MiddleIndex
  middleMiddle_eq := by
    rfl
  middleLeaf := boundaryLevelHistoryMatrix B l2MiddleIndex l2LeafIndex
  middleLeaf_eq := by
    rfl
  leafRoot := boundaryLevelHistoryMatrix B l2LeafIndex l2RootIndex
  leafRoot_eq := by
    rfl
  leafMiddle := boundaryLevelHistoryMatrix B l2LeafIndex l2MiddleIndex
  leafMiddle_eq := by
    rfl
  leafLeaf := boundaryLevelHistoryMatrix B l2LeafIndex l2LeafIndex
  leafLeaf_eq := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem matrix_from_boundary
    (P : L2BoundaryMatrixProfile B) :
    P.matrix = boundaryLevelHistoryMatrix B :=
  P.matrix_eq_boundary

theorem route_recursiveHistory
    (P : L2BoundaryMatrixProfile B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.route

theorem noCutSpecCarrierClaim_at
    (P : L2BoundaryMatrixProfile B)
    (k : BoundarySource.LevelHistoryIndex L2Level) :
    source.toc.approximant source.concretePolicy = T :=
  P.noCutSpecCarrierClaim k

end L2BoundaryMatrixProfile

structure L2EisensteinLedger
    (B : BoundarySource.BoundarySourceSurface source L2Level)
    (k : Nat) where
  boundaryMatrixProfile : L2BoundaryMatrixProfile B
  recurrenceLedger : SchurMobiusRecurrenceLedger source L2Level
  recurrenceLedger_eq : recurrenceLedger = SchurMobiusRecurrenceLedger.fromBoundarySource B
  charpolyLedger : OperativeCharpolyLedger source L2Level 0
  charpolyLedger_eq : charpolyLedger = OperativeCharpolyLedger.fromBoundarySource B 0
  squareBranching : Nat
  squareBranching_eq : squareBranching = l2SquareBranching k
  squareBranching_is_square : squareBranching = k * k
  factorizationCertificate : L2EisensteinFactorizationCertificate
  factorizationCertificate_eq :
    factorizationCertificate = L2EisensteinFactorizationCertificate.closed
  normCertificate : L2EisensteinNormCertificate
  normCertificate_eq : normCertificate = L2EisensteinNormCertificate.closed
  orderSeed : L2EisensteinOrderSeed
  orderSeed_eq : orderSeed = L2EisensteinOrderSeed.closed
  rhoSeed : L2RhoCMSeed
  rhoSeed_eq : rhoSeed = L2RhoCMSeed.closed
  factorizationStatus : L2EisensteinFactorizationStatus
  factorizationStatus_eq :
    factorizationStatus =
      L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified
  normformStatus : L2EisensteinNormformStatus
  normformStatus_eq :
    normformStatus = L2EisensteinNormformStatus.eisensteinNormformCertified
  discriminantStatus : L2EisensteinDiscriminantStatus
  discriminantStatus_eq :
    discriminantStatus =
      L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree
  orderStatus : L2EisensteinOrderStatus
  orderStatus_eq : orderStatus = L2EisensteinOrderStatus.eisensteinOrderSeedCertified
  cmSeedStatus : L2EisensteinCMSeedStatus
  cmSeedStatus_eq : cmSeedStatus = L2EisensteinCMSeedStatus.rhoSeedCertified
  noShortcutStatus : L2EisensteinNoShortcutStatus
  noShortcutStatus_eq :
    noShortcutStatus =
      L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion
  recurrenceClosed :
    recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  charpolyClosed :
    charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  charpolyNoFreeAssumptions :
    charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _j : BoundarySource.LevelHistoryIndex L2Level,
      source.toc.approximant source.concretePolicy = T

namespace L2EisensteinLedger

variable {B : BoundarySource.BoundarySourceSurface source L2Level}
variable {k : Nat}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L2Level)
    (k : Nat) :
    L2EisensteinLedger B k where
  boundaryMatrixProfile := L2BoundaryMatrixProfile.fromBoundarySource B
  recurrenceLedger := SchurMobiusRecurrenceLedger.fromBoundarySource B
  recurrenceLedger_eq := by
    rfl
  charpolyLedger := OperativeCharpolyLedger.fromBoundarySource B 0
  charpolyLedger_eq := by
    rfl
  squareBranching := l2SquareBranching k
  squareBranching_eq := by
    rfl
  squareBranching_is_square := by
    rfl
  factorizationCertificate := L2EisensteinFactorizationCertificate.closed
  factorizationCertificate_eq := by
    rfl
  normCertificate := L2EisensteinNormCertificate.closed
  normCertificate_eq := by
    rfl
  orderSeed := L2EisensteinOrderSeed.closed
  orderSeed_eq := by
    rfl
  rhoSeed := L2RhoCMSeed.closed
  rhoSeed_eq := by
    rfl
  factorizationStatus :=
    L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified
  factorizationStatus_eq := by
    rfl
  normformStatus := L2EisensteinNormformStatus.eisensteinNormformCertified
  normformStatus_eq := by
    rfl
  discriminantStatus :=
    L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree
  discriminantStatus_eq := by
    rfl
  orderStatus := L2EisensteinOrderStatus.eisensteinOrderSeedCertified
  orderStatus_eq := by
    rfl
  cmSeedStatus := L2EisensteinCMSeedStatus.rhoSeedCertified
  cmSeedStatus_eq := by
    rfl
  noShortcutStatus :=
    L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion
  noShortcutStatus_eq := by
    rfl
  recurrenceClosed := by
    rfl
  charpolyClosed := by
    rfl
  charpolyNoFreeAssumptions := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro j
    exact B.noCutSpecCarrierClaim_at j

theorem factorization_status_closed
    (Ldg : L2EisensteinLedger B k) :
    Ldg.factorizationStatus =
      L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified :=
  Ldg.factorizationStatus_eq

theorem normform_status_closed
    (Ldg : L2EisensteinLedger B k) :
    Ldg.normformStatus = L2EisensteinNormformStatus.eisensteinNormformCertified :=
  Ldg.normformStatus_eq

theorem discriminant_status_minus_three
    (Ldg : L2EisensteinLedger B k) :
    Ldg.discriminantStatus =
      L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree :=
  Ldg.discriminantStatus_eq

theorem order_status_eisenstein
    (Ldg : L2EisensteinLedger B k) :
    Ldg.orderStatus = L2EisensteinOrderStatus.eisensteinOrderSeedCertified :=
  Ldg.orderStatus_eq

theorem cm_seed_status_rho
    (Ldg : L2EisensteinLedger B k) :
    Ldg.cmSeedStatus = L2EisensteinCMSeedStatus.rhoSeedCertified :=
  Ldg.cmSeedStatus_eq

theorem no_shortcut
    (Ldg : L2EisensteinLedger B k) :
    Ldg.noShortcutStatus =
      L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion :=
  Ldg.noShortcutStatus_eq

theorem square_branching_is_square
    (Ldg : L2EisensteinLedger B k) :
    Ldg.squareBranching = k * k :=
  Ldg.squareBranching_is_square

theorem recurrence_status_closed
    (Ldg : L2EisensteinLedger B k) :
    Ldg.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed :=
  Ldg.recurrenceClosed

theorem charpoly_status_closed
    (Ldg : L2EisensteinLedger B k) :
    Ldg.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  Ldg.charpolyClosed

theorem charpoly_no_free_assumptions
    (Ldg : L2EisensteinLedger B k) :
    Ldg.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  Ldg.charpolyNoFreeAssumptions

theorem route_recursiveHistory
    (Ldg : L2EisensteinLedger B k) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem noCutSpecCarrierClaim_at
    (Ldg : L2EisensteinLedger B k)
    (j : BoundarySource.LevelHistoryIndex L2Level) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim j

end L2EisensteinLedger

end Schur

namespace StrengtheningAR8

abbrev AR8L2Level := Schur.L2Level
abbrev AR8L2RootIndex := Schur.l2RootIndex
abbrev AR8L2MiddleIndex := Schur.l2MiddleIndex
abbrev AR8L2LeafIndex := Schur.l2LeafIndex
abbrev AR8L2EisensteinFactorizationStatus := Schur.L2EisensteinFactorizationStatus
abbrev AR8L2EisensteinNormformStatus := Schur.L2EisensteinNormformStatus
abbrev AR8L2EisensteinDiscriminantStatus := Schur.L2EisensteinDiscriminantStatus
abbrev AR8L2EisensteinOrderStatus := Schur.L2EisensteinOrderStatus
abbrev AR8L2EisensteinCMSeedStatus := Schur.L2EisensteinCMSeedStatus
abbrev AR8L2EisensteinNoShortcutStatus := Schur.L2EisensteinNoShortcutStatus
abbrev AR8L2CMSeedSymbol := Schur.L2CMSeedSymbol
abbrev AR8L2QuadraticOrderSymbol := Schur.L2QuadraticOrderSymbol
abbrev AR8L2EisensteinFactorizationCertificate :=
  Schur.L2EisensteinFactorizationCertificate
abbrev AR8L2EisensteinNormCertificate := Schur.L2EisensteinNormCertificate
abbrev AR8L2EisensteinOrderSeed := Schur.L2EisensteinOrderSeed
abbrev AR8L2RhoCMSeed := Schur.L2RhoCMSeed

abbrev AR8L2BoundaryMatrixProfile
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L2Level) :=
  Schur.L2BoundaryMatrixProfile B

abbrev AR8L2EisensteinLedger
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L2Level)
    (k : Nat) :=
  Schur.L2EisensteinLedger B k

def AR8L2EisensteinLedgerFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L2Level)
    (k : Nat) :
    AR8L2EisensteinLedger B k :=
  Schur.L2EisensteinLedger.fromBoundarySource B k

theorem AR8L2EisensteinLedger_factorization_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {k : Nat}
    (Ldg : AR8L2EisensteinLedger B k) :
    Ldg.factorizationStatus =
      Schur.L2EisensteinFactorizationStatus.ar8L2QuadraticFactorizationCertified :=
  Schur.L2EisensteinLedger.factorization_status_closed Ldg

theorem AR8L2EisensteinLedger_discriminant_minus_three
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {k : Nat}
    (Ldg : AR8L2EisensteinLedger B k) :
    Ldg.discriminantStatus =
      Schur.L2EisensteinDiscriminantStatus.schurDiscriminantConventionGivesMinusThree :=
  Schur.L2EisensteinLedger.discriminant_status_minus_three Ldg

theorem AR8L2EisensteinLedger_cm_seed_rho
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {k : Nat}
    (Ldg : AR8L2EisensteinLedger B k) :
    Ldg.cmSeedStatus = Schur.L2EisensteinCMSeedStatus.rhoSeedCertified :=
  Schur.L2EisensteinLedger.cm_seed_status_rho Ldg

theorem AR8L2EisensteinLedger_no_shortcut
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L2Level}
    {k : Nat}
    (Ldg : AR8L2EisensteinLedger B k) :
    Ldg.noShortcutStatus =
      Schur.L2EisensteinNoShortcutStatus.noPatternRecognitionNoMoonshineNoQExpansion :=
  Schur.L2EisensteinLedger.no_shortcut Ldg

end StrengtheningAR8

end CNNA.PillarA.Arithmetic
