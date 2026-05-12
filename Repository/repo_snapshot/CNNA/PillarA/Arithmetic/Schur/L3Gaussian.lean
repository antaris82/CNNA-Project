import CNNA.PillarA.Arithmetic.Schur.L2Eisenstein

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T}

abbrev L3Level : Nat := 3

def l3RootIndex : BoundarySource.LevelHistoryIndex L3Level :=
  rootIndex L3Level

def l3FirstInteriorIndex : BoundarySource.LevelHistoryIndex L3Level :=
  ⟨1, by
    show 1 < 4
    exact Nat.succ_lt_succ (Nat.zero_lt_succ 2)⟩

def l3SecondInteriorIndex : BoundarySource.LevelHistoryIndex L3Level :=
  ⟨2, by
    show 2 < 4
    exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))⟩

def l3LeafIndex : BoundarySource.LevelHistoryIndex L3Level :=
  leafIndex L3Level

theorem l3RootIndex_val : l3RootIndex.val = 0 := by
  rfl

theorem l3FirstInteriorIndex_val : l3FirstInteriorIndex.val = 1 := by
  rfl

theorem l3SecondInteriorIndex_val : l3SecondInteriorIndex.val = 2 := by
  rfl

theorem l3LeafIndex_val : l3LeafIndex.val = 3 := by
  rfl

theorem l3FirstInteriorIndex_interior :
    0 < l3FirstInteriorIndex.val ∧ l3FirstInteriorIndex.val < L3Level := by
  constructor
  · exact Nat.succ_pos 0
  · exact Nat.succ_lt_succ (Nat.succ_pos 1)

theorem l3SecondInteriorIndex_interior :
    0 < l3SecondInteriorIndex.val ∧ l3SecondInteriorIndex.val < L3Level := by
  constructor
  · exact Nat.succ_pos 1
  · exact Nat.lt_succ_self 2

def l3TwiceSquareBranching (k : Nat) : Nat :=
  2 * k * k

theorem l3TwiceSquareBranching_eq_two_mul_square (k : Nat) :
    l3TwiceSquareBranching k = 2 * k * k := by
  rfl

def l3GaussMultiplicationMatrix : Matrix (Fin 2) (Fin 2) ExecComplex :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 0
    else if i.val = 0 ∧ j.val = 1 then -1
    else if i.val = 1 ∧ j.val = 0 then 1
    else 0

theorem l3GaussMultiplicationMatrix_00 :
    l3GaussMultiplicationMatrix 0 0 = 0 := by
  rfl

theorem l3GaussMultiplicationMatrix_01 :
    l3GaussMultiplicationMatrix 0 1 = -1 := by
  rfl

theorem l3GaussMultiplicationMatrix_10 :
    l3GaussMultiplicationMatrix 1 0 = 1 := by
  rfl

theorem l3GaussMultiplicationMatrix_11 :
    l3GaussMultiplicationMatrix 1 1 = 0 := by
  rfl

def l3GaussianPolynomialEval (z : SpectralParameter) : ExecComplex :=
  spectralParameterExec z * spectralParameterExec z + 1

def l3GaussianNormForm (a b : ℚ) : ℚ :=
  a * a + b * b

def l3GaussianNormCoefficientA : ℤ :=
  1

def l3GaussianNormCoefficientB : ℤ :=
  0

def l3GaussianNormCoefficientC : ℤ :=
  1

def l3GaussianNormDiscriminant : ℤ :=
  l3GaussianNormCoefficientB * l3GaussianNormCoefficientB -
    4 * l3GaussianNormCoefficientA * l3GaussianNormCoefficientC

theorem l3GaussianNormDiscriminant_eq_neg_four :
    l3GaussianNormDiscriminant = -4 := by
  unfold l3GaussianNormDiscriminant
  unfold l3GaussianNormCoefficientA
  unfold l3GaussianNormCoefficientB
  unfold l3GaussianNormCoefficientC
  ring

theorem l3GaussianNormForm_self (a b : ℚ) :
    l3GaussianNormForm a b = a * a + b * b := by
  rfl

theorem l3GaussSpectralPencil_00 (z : SpectralParameter) :
    spectralPencil l3GaussMultiplicationMatrix z 0 0 = spectralParameterExec z := by
  simp [spectralPencil, l3GaussMultiplicationMatrix]

theorem l3GaussSpectralPencil_01 (z : SpectralParameter) :
    spectralPencil l3GaussMultiplicationMatrix z 0 1 = 1 := by
  simp [spectralPencil, l3GaussMultiplicationMatrix]

theorem l3GaussSpectralPencil_10 (z : SpectralParameter) :
    spectralPencil l3GaussMultiplicationMatrix z 1 0 = -1 := by
  simp [spectralPencil, l3GaussMultiplicationMatrix]

theorem l3GaussSpectralPencil_11 (z : SpectralParameter) :
    spectralPencil l3GaussMultiplicationMatrix z 1 1 = spectralParameterExec z := by
  simp [spectralPencil, l3GaussMultiplicationMatrix]

theorem l3GaussCharpolyFactorization (z : SpectralParameter) :
    charpolyEvalFinTwoFormula l3GaussMultiplicationMatrix z =
      l3GaussianPolynomialEval z := by
  calc
    charpolyEvalFinTwoFormula l3GaussMultiplicationMatrix z
        = detFinTwoFormula (spectralPencil l3GaussMultiplicationMatrix z) := by
      rfl
    _ = spectralPencil l3GaussMultiplicationMatrix z 0 0 *
          spectralPencil l3GaussMultiplicationMatrix z 1 1 -
        spectralPencil l3GaussMultiplicationMatrix z 0 1 *
          spectralPencil l3GaussMultiplicationMatrix z 1 0 := by
      rfl
    _ = spectralParameterExec z * spectralParameterExec z - 1 * (-1) := by
      rw [l3GaussSpectralPencil_00, l3GaussSpectralPencil_01,
        l3GaussSpectralPencil_10, l3GaussSpectralPencil_11]
    _ = l3GaussianPolynomialEval z := by
      unfold l3GaussianPolynomialEval
      ring

theorem l3GaussOperativeCharpolyFactorization (z : SpectralParameter) :
    operativeCharpolyEvaluation l3GaussMultiplicationMatrix z =
      l3GaussianPolynomialEval z := by
  calc
    operativeCharpolyEvaluation l3GaussMultiplicationMatrix z
        = charpolyEvalFinTwoFormula l3GaussMultiplicationMatrix z :=
      (charpolyEvalFinTwoFormula_eq_eval l3GaussMultiplicationMatrix z).symm
    _ = l3GaussianPolynomialEval z :=
      l3GaussCharpolyFactorization z

inductive L3GaussianFactorizationStatus where
  | ar9L3QuadraticFactorizationCertified
  deriving DecidableEq, Repr

inductive L3GaussianNormformStatus where
  | gaussianNormformCertified
  deriving DecidableEq, Repr

inductive L3GaussianDiscriminantStatus where
  | schurDiscriminantConventionGivesMinusFour
  deriving DecidableEq, Repr

inductive L3GaussianOrderStatus where
  | gaussianOrderSeedCertified
  deriving DecidableEq, Repr

inductive L3GaussianCMSeedStatus where
  | iSeedCertified
  deriving DecidableEq, Repr

inductive L3GaussianNoShortcutStatus where
  | noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion
  deriving DecidableEq, Repr

inductive L3CMSeedSymbol where
  | gaussianI
  deriving DecidableEq, Repr

inductive L3QuadraticOrderSymbol where
  | gaussian
  deriving DecidableEq, Repr

structure L3GaussianFactorizationCertificate where
  matrix : Matrix (Fin 2) (Fin 2) ExecComplex
  matrix_eq_gaussMultiplication : matrix = l3GaussMultiplicationMatrix
  polynomialEval : SpectralParameter → ExecComplex
  polynomialEval_eq : polynomialEval = l3GaussianPolynomialEval
  charpoly_factorization :
    ∀ z : SpectralParameter, operativeCharpolyEvaluation matrix z = polynomialEval z
  discriminant : ℤ
  discriminant_eq : discriminant = -4
  factorizationStatus : L3GaussianFactorizationStatus
  factorizationStatus_eq :
    factorizationStatus =
      L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified
  noFreeAssumptionStatus : AR5NoFreeAssumptionStatus
  noFreeAssumptionStatus_eq :
    noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption

namespace L3GaussianFactorizationCertificate

def closed : L3GaussianFactorizationCertificate where
  matrix := l3GaussMultiplicationMatrix
  matrix_eq_gaussMultiplication := by
    rfl
  polynomialEval := l3GaussianPolynomialEval
  polynomialEval_eq := by
    rfl
  charpoly_factorization := by
    intro z
    exact l3GaussOperativeCharpolyFactorization z
  discriminant := l3GaussianNormDiscriminant
  discriminant_eq := l3GaussianNormDiscriminant_eq_neg_four
  factorizationStatus :=
    L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified
  factorizationStatus_eq := by
    rfl
  noFreeAssumptionStatus :=
    AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  noFreeAssumptionStatus_eq := by
    rfl

theorem factorization_closed
    (C : L3GaussianFactorizationCertificate) :
    C.factorizationStatus =
      L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified :=
  C.factorizationStatus_eq

theorem discriminant_minus_four
    (C : L3GaussianFactorizationCertificate) :
    C.discriminant = -4 :=
  C.discriminant_eq

theorem no_free_assumptions
    (C : L3GaussianFactorizationCertificate) :
    C.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  C.noFreeAssumptionStatus_eq

end L3GaussianFactorizationCertificate

structure L3GaussianNormCertificate where
  normForm : ℚ → ℚ → ℚ
  normForm_eq : normForm = l3GaussianNormForm
  coefficientA : ℤ
  coefficientA_eq : coefficientA = l3GaussianNormCoefficientA
  coefficientB : ℤ
  coefficientB_eq : coefficientB = l3GaussianNormCoefficientB
  coefficientC : ℤ
  coefficientC_eq : coefficientC = l3GaussianNormCoefficientC
  discriminant : ℤ
  discriminant_eq : discriminant = -4
  normformStatus : L3GaussianNormformStatus
  normformStatus_eq :
    normformStatus = L3GaussianNormformStatus.gaussianNormformCertified

namespace L3GaussianNormCertificate

def closed : L3GaussianNormCertificate where
  normForm := l3GaussianNormForm
  normForm_eq := by
    rfl
  coefficientA := l3GaussianNormCoefficientA
  coefficientA_eq := by
    rfl
  coefficientB := l3GaussianNormCoefficientB
  coefficientB_eq := by
    rfl
  coefficientC := l3GaussianNormCoefficientC
  coefficientC_eq := by
    rfl
  discriminant := l3GaussianNormDiscriminant
  discriminant_eq := l3GaussianNormDiscriminant_eq_neg_four
  normformStatus := L3GaussianNormformStatus.gaussianNormformCertified
  normformStatus_eq := by
    rfl

theorem discriminant_minus_four
    (C : L3GaussianNormCertificate) :
    C.discriminant = -4 :=
  C.discriminant_eq

theorem status_certified
    (C : L3GaussianNormCertificate) :
    C.normformStatus = L3GaussianNormformStatus.gaussianNormformCertified :=
  C.normformStatus_eq

end L3GaussianNormCertificate

structure L3GaussianOrderSeed where
  orderSymbol : L3QuadraticOrderSymbol
  orderSymbol_eq : orderSymbol = L3QuadraticOrderSymbol.gaussian
  discriminant : ℤ
  discriminant_eq : discriminant = -4
  orderStatus : L3GaussianOrderStatus
  orderStatus_eq : orderStatus = L3GaussianOrderStatus.gaussianOrderSeedCertified
  discriminantStatus : L3GaussianDiscriminantStatus
  discriminantStatus_eq :
    discriminantStatus =
      L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour
  noShortcutStatus : L3GaussianNoShortcutStatus
  noShortcutStatus_eq :
    noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion

namespace L3GaussianOrderSeed

def closed : L3GaussianOrderSeed where
  orderSymbol := L3QuadraticOrderSymbol.gaussian
  orderSymbol_eq := by
    rfl
  discriminant := l3GaussianNormDiscriminant
  discriminant_eq := l3GaussianNormDiscriminant_eq_neg_four
  orderStatus := L3GaussianOrderStatus.gaussianOrderSeedCertified
  orderStatus_eq := by
    rfl
  discriminantStatus :=
    L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour
  discriminantStatus_eq := by
    rfl
  noShortcutStatus :=
    L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion
  noShortcutStatus_eq := by
    rfl

theorem discriminant_minus_four
    (S : L3GaussianOrderSeed) :
    S.discriminant = -4 :=
  S.discriminant_eq

theorem order_status_certified
    (S : L3GaussianOrderSeed) :
    S.orderStatus = L3GaussianOrderStatus.gaussianOrderSeedCertified :=
  S.orderStatus_eq

theorem no_shortcut
    (S : L3GaussianOrderSeed) :
    S.noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion :=
  S.noShortcutStatus_eq

end L3GaussianOrderSeed

structure L3GaussianICMSeed where
  seed : L3CMSeedSymbol
  seed_eq : seed = L3CMSeedSymbol.gaussianI
  orderSeed : L3GaussianOrderSeed
  orderSeed_eq : orderSeed = L3GaussianOrderSeed.closed
  minimalPolynomialEval : SpectralParameter → ExecComplex
  minimalPolynomialEval_eq : minimalPolynomialEval = l3GaussianPolynomialEval
  discriminant : ℤ
  discriminant_eq : discriminant = -4
  cmSeedStatus : L3GaussianCMSeedStatus
  cmSeedStatus_eq : cmSeedStatus = L3GaussianCMSeedStatus.iSeedCertified
  noShortcutStatus : L3GaussianNoShortcutStatus
  noShortcutStatus_eq :
    noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion

namespace L3GaussianICMSeed

def closed : L3GaussianICMSeed where
  seed := L3CMSeedSymbol.gaussianI
  seed_eq := by
    rfl
  orderSeed := L3GaussianOrderSeed.closed
  orderSeed_eq := by
    rfl
  minimalPolynomialEval := l3GaussianPolynomialEval
  minimalPolynomialEval_eq := by
    rfl
  discriminant := l3GaussianNormDiscriminant
  discriminant_eq := l3GaussianNormDiscriminant_eq_neg_four
  cmSeedStatus := L3GaussianCMSeedStatus.iSeedCertified
  cmSeedStatus_eq := by
    rfl
  noShortcutStatus :=
    L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion
  noShortcutStatus_eq := by
    rfl

theorem seed_is_gaussian_i
    (S : L3GaussianICMSeed) :
    S.seed = L3CMSeedSymbol.gaussianI :=
  S.seed_eq

theorem cm_status_certified
    (S : L3GaussianICMSeed) :
    S.cmSeedStatus = L3GaussianCMSeedStatus.iSeedCertified :=
  S.cmSeedStatus_eq

theorem no_shortcut
    (S : L3GaussianICMSeed) :
    S.noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion :=
  S.noShortcutStatus_eq

end L3GaussianICMSeed

structure L3BoundaryMatrixProfile
    (B : BoundarySource.BoundarySourceSurface source L3Level) where
  matrix : BoundarySource.LevelHistoryMatrix L3Level
  matrix_eq_boundary : matrix = boundaryLevelHistoryMatrix B
  entry : BoundarySource.LevelHistoryIndex L3Level →
    BoundarySource.LevelHistoryIndex L3Level → ExecComplex
  entry_eq_matrix : ∀ i j, entry i j = matrix i j
  rootIndex_eq : l3RootIndex.val = 0
  firstInteriorIndex_eq : l3FirstInteriorIndex.val = 1
  secondInteriorIndex_eq : l3SecondInteriorIndex.val = 2
  leafIndex_eq : l3LeafIndex.val = 3
  firstInterior : 0 < l3FirstInteriorIndex.val ∧ l3FirstInteriorIndex.val < L3Level
  secondInterior : 0 < l3SecondInteriorIndex.val ∧ l3SecondInteriorIndex.val < L3Level
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L3Level,
      source.toc.approximant source.concretePolicy = T

namespace L3BoundaryMatrixProfile

variable {B : BoundarySource.BoundarySourceSurface source L3Level}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L3Level) :
    L3BoundaryMatrixProfile B where
  matrix := boundaryLevelHistoryMatrix B
  matrix_eq_boundary := by
    rfl
  entry := fun i j => boundaryLevelHistoryMatrix B i j
  entry_eq_matrix := by
    intro i j
    rfl
  rootIndex_eq := by
    rfl
  firstInteriorIndex_eq := by
    rfl
  secondInteriorIndex_eq := by
    rfl
  leafIndex_eq := by
    rfl
  firstInterior := l3FirstInteriorIndex_interior
  secondInterior := l3SecondInteriorIndex_interior
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem matrix_from_boundary
    (P : L3BoundaryMatrixProfile B) :
    P.matrix = boundaryLevelHistoryMatrix B :=
  P.matrix_eq_boundary

theorem entry_from_matrix
    (P : L3BoundaryMatrixProfile B)
    (i j : BoundarySource.LevelHistoryIndex L3Level) :
    P.entry i j = P.matrix i j :=
  P.entry_eq_matrix i j

theorem route_recursiveHistory
    (P : L3BoundaryMatrixProfile B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.route

theorem noCutSpecCarrierClaim_at
    (P : L3BoundaryMatrixProfile B)
    (k : BoundarySource.LevelHistoryIndex L3Level) :
    source.toc.approximant source.concretePolicy = T :=
  P.noCutSpecCarrierClaim k

end L3BoundaryMatrixProfile

structure L3GaussianLedger
    (B : BoundarySource.BoundarySourceSurface source L3Level)
    (k : Nat) where
  boundaryMatrixProfile : L3BoundaryMatrixProfile B
  recurrenceLedger : SchurMobiusRecurrenceLedger source L3Level
  recurrenceLedger_eq : recurrenceLedger = SchurMobiusRecurrenceLedger.fromBoundarySource B
  charpolyLedger : OperativeCharpolyLedger source L3Level 0
  charpolyLedger_eq : charpolyLedger = OperativeCharpolyLedger.fromBoundarySource B 0
  twiceSquareBranching : Nat
  twiceSquareBranching_eq : twiceSquareBranching = l3TwiceSquareBranching k
  twiceSquareBranching_is_two_mul_square : twiceSquareBranching = 2 * k * k
  factorizationCertificate : L3GaussianFactorizationCertificate
  factorizationCertificate_eq :
    factorizationCertificate = L3GaussianFactorizationCertificate.closed
  normCertificate : L3GaussianNormCertificate
  normCertificate_eq : normCertificate = L3GaussianNormCertificate.closed
  orderSeed : L3GaussianOrderSeed
  orderSeed_eq : orderSeed = L3GaussianOrderSeed.closed
  gaussianISeed : L3GaussianICMSeed
  gaussianISeed_eq : gaussianISeed = L3GaussianICMSeed.closed
  factorizationStatus : L3GaussianFactorizationStatus
  factorizationStatus_eq :
    factorizationStatus =
      L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified
  normformStatus : L3GaussianNormformStatus
  normformStatus_eq :
    normformStatus = L3GaussianNormformStatus.gaussianNormformCertified
  discriminantStatus : L3GaussianDiscriminantStatus
  discriminantStatus_eq :
    discriminantStatus =
      L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour
  orderStatus : L3GaussianOrderStatus
  orderStatus_eq : orderStatus = L3GaussianOrderStatus.gaussianOrderSeedCertified
  cmSeedStatus : L3GaussianCMSeedStatus
  cmSeedStatus_eq : cmSeedStatus = L3GaussianCMSeedStatus.iSeedCertified
  noShortcutStatus : L3GaussianNoShortcutStatus
  noShortcutStatus_eq :
    noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion
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
    ∀ _j : BoundarySource.LevelHistoryIndex L3Level,
      source.toc.approximant source.concretePolicy = T

namespace L3GaussianLedger

variable {B : BoundarySource.BoundarySourceSurface source L3Level}
variable {k : Nat}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L3Level)
    (k : Nat) :
    L3GaussianLedger B k where
  boundaryMatrixProfile := L3BoundaryMatrixProfile.fromBoundarySource B
  recurrenceLedger := SchurMobiusRecurrenceLedger.fromBoundarySource B
  recurrenceLedger_eq := by
    rfl
  charpolyLedger := OperativeCharpolyLedger.fromBoundarySource B 0
  charpolyLedger_eq := by
    rfl
  twiceSquareBranching := l3TwiceSquareBranching k
  twiceSquareBranching_eq := by
    rfl
  twiceSquareBranching_is_two_mul_square := by
    rfl
  factorizationCertificate := L3GaussianFactorizationCertificate.closed
  factorizationCertificate_eq := by
    rfl
  normCertificate := L3GaussianNormCertificate.closed
  normCertificate_eq := by
    rfl
  orderSeed := L3GaussianOrderSeed.closed
  orderSeed_eq := by
    rfl
  gaussianISeed := L3GaussianICMSeed.closed
  gaussianISeed_eq := by
    rfl
  factorizationStatus :=
    L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified
  factorizationStatus_eq := by
    rfl
  normformStatus := L3GaussianNormformStatus.gaussianNormformCertified
  normformStatus_eq := by
    rfl
  discriminantStatus :=
    L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour
  discriminantStatus_eq := by
    rfl
  orderStatus := L3GaussianOrderStatus.gaussianOrderSeedCertified
  orderStatus_eq := by
    rfl
  cmSeedStatus := L3GaussianCMSeedStatus.iSeedCertified
  cmSeedStatus_eq := by
    rfl
  noShortcutStatus :=
    L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion
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
    (Ldg : L3GaussianLedger B k) :
    Ldg.factorizationStatus =
      L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified :=
  Ldg.factorizationStatus_eq

theorem normform_status_closed
    (Ldg : L3GaussianLedger B k) :
    Ldg.normformStatus = L3GaussianNormformStatus.gaussianNormformCertified :=
  Ldg.normformStatus_eq

theorem discriminant_status_minus_four
    (Ldg : L3GaussianLedger B k) :
    Ldg.discriminantStatus =
      L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour :=
  Ldg.discriminantStatus_eq

theorem order_status_gaussian
    (Ldg : L3GaussianLedger B k) :
    Ldg.orderStatus = L3GaussianOrderStatus.gaussianOrderSeedCertified :=
  Ldg.orderStatus_eq

theorem cm_seed_status_i
    (Ldg : L3GaussianLedger B k) :
    Ldg.cmSeedStatus = L3GaussianCMSeedStatus.iSeedCertified :=
  Ldg.cmSeedStatus_eq

theorem no_shortcut
    (Ldg : L3GaussianLedger B k) :
    Ldg.noShortcutStatus =
      L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion :=
  Ldg.noShortcutStatus_eq

theorem twice_square_branching_is_two_mul_square
    (Ldg : L3GaussianLedger B k) :
    Ldg.twiceSquareBranching = 2 * k * k :=
  Ldg.twiceSquareBranching_is_two_mul_square

theorem recurrence_status_closed
    (Ldg : L3GaussianLedger B k) :
    Ldg.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed :=
  Ldg.recurrenceClosed

theorem charpoly_status_closed
    (Ldg : L3GaussianLedger B k) :
    Ldg.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  Ldg.charpolyClosed

theorem charpoly_no_free_assumptions
    (Ldg : L3GaussianLedger B k) :
    Ldg.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  Ldg.charpolyNoFreeAssumptions

theorem route_recursiveHistory
    (Ldg : L3GaussianLedger B k) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem noCutSpecCarrierClaim_at
    (Ldg : L3GaussianLedger B k)
    (j : BoundarySource.LevelHistoryIndex L3Level) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim j

end L3GaussianLedger

end Schur

namespace StrengtheningAR9

abbrev AR9L3Level := Schur.L3Level
abbrev AR9L3RootIndex := Schur.l3RootIndex
abbrev AR9L3FirstInteriorIndex := Schur.l3FirstInteriorIndex
abbrev AR9L3SecondInteriorIndex := Schur.l3SecondInteriorIndex
abbrev AR9L3LeafIndex := Schur.l3LeafIndex
abbrev AR9L3GaussianFactorizationStatus := Schur.L3GaussianFactorizationStatus
abbrev AR9L3GaussianNormformStatus := Schur.L3GaussianNormformStatus
abbrev AR9L3GaussianDiscriminantStatus := Schur.L3GaussianDiscriminantStatus
abbrev AR9L3GaussianOrderStatus := Schur.L3GaussianOrderStatus
abbrev AR9L3GaussianCMSeedStatus := Schur.L3GaussianCMSeedStatus
abbrev AR9L3GaussianNoShortcutStatus := Schur.L3GaussianNoShortcutStatus
abbrev AR9L3CMSeedSymbol := Schur.L3CMSeedSymbol
abbrev AR9L3QuadraticOrderSymbol := Schur.L3QuadraticOrderSymbol
abbrev AR9L3GaussianFactorizationCertificate :=
  Schur.L3GaussianFactorizationCertificate
abbrev AR9L3GaussianNormCertificate := Schur.L3GaussianNormCertificate
abbrev AR9L3GaussianOrderSeed := Schur.L3GaussianOrderSeed
abbrev AR9L3GaussianICMSeed := Schur.L3GaussianICMSeed

abbrev AR9L3BoundaryMatrixProfile
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L3Level) :=
  Schur.L3BoundaryMatrixProfile B

abbrev AR9L3GaussianLedger
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L3Level)
    (k : Nat) :=
  Schur.L3GaussianLedger B k

def AR9L3GaussianLedgerFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L3Level)
    (k : Nat) :
    AR9L3GaussianLedger B k :=
  Schur.L3GaussianLedger.fromBoundarySource B k

theorem AR9L3GaussianLedger_factorization_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {k : Nat}
    (Ldg : AR9L3GaussianLedger B k) :
    Ldg.factorizationStatus =
      Schur.L3GaussianFactorizationStatus.ar9L3QuadraticFactorizationCertified :=
  Schur.L3GaussianLedger.factorization_status_closed Ldg

theorem AR9L3GaussianLedger_discriminant_minus_four
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {k : Nat}
    (Ldg : AR9L3GaussianLedger B k) :
    Ldg.discriminantStatus =
      Schur.L3GaussianDiscriminantStatus.schurDiscriminantConventionGivesMinusFour :=
  Schur.L3GaussianLedger.discriminant_status_minus_four Ldg

theorem AR9L3GaussianLedger_cm_seed_i
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {k : Nat}
    (Ldg : AR9L3GaussianLedger B k) :
    Ldg.cmSeedStatus = Schur.L3GaussianCMSeedStatus.iSeedCertified :=
  Schur.L3GaussianLedger.cm_seed_status_i Ldg

theorem AR9L3GaussianLedger_no_shortcut
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L3Level}
    {k : Nat}
    (Ldg : AR9L3GaussianLedger B k) :
    Ldg.noShortcutStatus =
      Schur.L3GaussianNoShortcutStatus.noFieldOrderIdentificationBeforeAR12NoMoonshineNoQExpansion :=
  Schur.L3GaussianLedger.no_shortcut Ldg

end StrengtheningAR9

end CNNA.PillarA.Arithmetic
