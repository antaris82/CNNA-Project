import CNNA.PillarA.Arithmetic.Orders.QuadraticOrder

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Orders

inductive FundamentalDiscriminantConventionStatus where
  | fundamentalDiscriminantConventionCertified
  deriving DecidableEq, Repr

inductive SchurDiscriminantNormalizationStatus where
  | conductorSquareNormalizationCertified
  deriving DecidableEq, Repr

inductive PositiveDConventionStatus where
  | heegnerDConventionCertified
  | nonHeegnerDConventionCertificateProvided
  deriving DecidableEq, Repr

inductive NonQuadraticForwardingStatus where
  | blockedFromQuadraticOrderPath
  deriving DecidableEq, Repr

def heegnerFundamentalDiscriminant : Schur.HigherLevelHeegnerD → ℤ
  | Schur.HigherLevelHeegnerD.d1 => -4
  | Schur.HigherLevelHeegnerD.d2 => -8
  | Schur.HigherLevelHeegnerD.d3 => -3
  | Schur.HigherLevelHeegnerD.d7 => -7
  | Schur.HigherLevelHeegnerD.d11 => -11
  | Schur.HigherLevelHeegnerD.d19 => -19
  | Schur.HigherLevelHeegnerD.d43 => -43
  | Schur.HigherLevelHeegnerD.d67 => -67
  | Schur.HigherLevelHeegnerD.d163 => -163

theorem heegnerFundamentalDiscriminant_d1 :
    heegnerFundamentalDiscriminant Schur.HigherLevelHeegnerD.d1 = -4 := by
  rfl

theorem heegnerFundamentalDiscriminant_d3 :
    heegnerFundamentalDiscriminant Schur.HigherLevelHeegnerD.d3 = -3 := by
  rfl

structure SchurToFundamentalDiscriminantBridge where
  schurDiscriminant : ℤ
  fundamentalDiscriminant : ℤ
  conductor : Nat
  positiveD : Nat
  conductorPositive : 0 < conductor
  normalizationStatus : SchurDiscriminantNormalizationStatus
  normalizationStatus_eq :
    normalizationStatus =
      SchurDiscriminantNormalizationStatus.conductorSquareNormalizationCertified
  conventionStatus : FundamentalDiscriminantConventionStatus
  conventionStatus_eq :
    conventionStatus =
      FundamentalDiscriminantConventionStatus.fundamentalDiscriminantConventionCertified
  positiveDConventionStatus : PositiveDConventionStatus
  schur_eq_conductor_square_mul_fundamental :
    schurDiscriminant = ((conductor * conductor : Nat) : ℤ) * fundamentalDiscriminant
  irreduciblePrimeDisciplineStatus : IrreduciblePrimeDisciplineStatus
  irreduciblePrimeDisciplineStatus_eq :
    irreduciblePrimeDisciplineStatus =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD

theorem schur_discrim_to_fundamental_discrim
    (B : SchurToFundamentalDiscriminantBridge) :
    B.schurDiscriminant =
      ((B.conductor * B.conductor : Nat) : ℤ) * B.fundamentalDiscriminant :=
  B.schur_eq_conductor_square_mul_fundamental

namespace SchurToFundamentalDiscriminantBridge

def gaussian : SchurToFundamentalDiscriminantBridge where
  schurDiscriminant := Schur.l3GaussianNormDiscriminant
  fundamentalDiscriminant := -4
  conductor := 1
  positiveD := 1
  conductorPositive := Nat.succ_pos 0
  normalizationStatus :=
    SchurDiscriminantNormalizationStatus.conductorSquareNormalizationCertified
  normalizationStatus_eq := by
    rfl
  conventionStatus :=
    FundamentalDiscriminantConventionStatus.fundamentalDiscriminantConventionCertified
  conventionStatus_eq := by
    rfl
  positiveDConventionStatus := PositiveDConventionStatus.heegnerDConventionCertified
  schur_eq_conductor_square_mul_fundamental := by
    calc
      Schur.l3GaussianNormDiscriminant = -4 := Schur.l3GaussianNormDiscriminant_eq_neg_four
      _ = (((1 * 1 : Nat) : ℤ) * (-4 : ℤ)) := by
        ring
  irreduciblePrimeDisciplineStatus :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  irreduciblePrimeDisciplineStatus_eq := by
    rfl

def eisenstein : SchurToFundamentalDiscriminantBridge where
  schurDiscriminant := Schur.l2EisensteinNormDiscriminant
  fundamentalDiscriminant := -3
  conductor := 1
  positiveD := 3
  conductorPositive := Nat.succ_pos 0
  normalizationStatus :=
    SchurDiscriminantNormalizationStatus.conductorSquareNormalizationCertified
  normalizationStatus_eq := by
    rfl
  conventionStatus :=
    FundamentalDiscriminantConventionStatus.fundamentalDiscriminantConventionCertified
  conventionStatus_eq := by
    rfl
  positiveDConventionStatus := PositiveDConventionStatus.heegnerDConventionCertified
  schur_eq_conductor_square_mul_fundamental := by
    calc
      Schur.l2EisensteinNormDiscriminant = -3 := Schur.l2EisensteinNormDiscriminant_eq_neg_three
      _ = (((1 * 1 : Nat) : ℤ) * (-3 : ℤ)) := by
        ring
  irreduciblePrimeDisciplineStatus :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  irreduciblePrimeDisciplineStatus_eq := by
    rfl

theorem normalization_certified (B : SchurToFundamentalDiscriminantBridge) :
    B.normalizationStatus =
      SchurDiscriminantNormalizationStatus.conductorSquareNormalizationCertified :=
  B.normalizationStatus_eq

theorem convention_certified (B : SchurToFundamentalDiscriminantBridge) :
    B.conventionStatus =
      FundamentalDiscriminantConventionStatus.fundamentalDiscriminantConventionCertified :=
  B.conventionStatus_eq

theorem no_irreducible_prime_shortcut (B : SchurToFundamentalDiscriminantBridge) :
    B.irreduciblePrimeDisciplineStatus =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD :=
  B.irreduciblePrimeDisciplineStatus_eq

theorem gaussian_bridge_formula :
    gaussian.schurDiscriminant =
      ((gaussian.conductor * gaussian.conductor : Nat) : ℤ) * gaussian.fundamentalDiscriminant :=
  schur_discrim_to_fundamental_discrim gaussian

theorem eisenstein_bridge_formula :
    eisenstein.schurDiscriminant =
      ((eisenstein.conductor * eisenstein.conductor : Nat) : ℤ) * eisenstein.fundamentalDiscriminant :=
  schur_discrim_to_fundamental_discrim eisenstein

end SchurToFundamentalDiscriminantBridge

structure HeegnerDiscriminantBridge extends SchurToFundamentalDiscriminantBridge where
  heegnerD : Schur.HigherLevelHeegnerD
  positiveD_eq_heegnerD : positiveD = heegnerD.toNat
  fundamentalDiscriminant_eq_heegnerConvention :
    fundamentalDiscriminant = heegnerFundamentalDiscriminant heegnerD

namespace HeegnerDiscriminantBridge

def gaussian : HeegnerDiscriminantBridge where
  toSchurToFundamentalDiscriminantBridge := SchurToFundamentalDiscriminantBridge.gaussian
  heegnerD := Schur.HigherLevelHeegnerD.d1
  positiveD_eq_heegnerD := by
    rfl
  fundamentalDiscriminant_eq_heegnerConvention := by
    rfl

def eisenstein : HeegnerDiscriminantBridge where
  toSchurToFundamentalDiscriminantBridge := SchurToFundamentalDiscriminantBridge.eisenstein
  heegnerD := Schur.HigherLevelHeegnerD.d3
  positiveD_eq_heegnerD := by
    rfl
  fundamentalDiscriminant_eq_heegnerConvention := by
    rfl

theorem positiveD_matches_heegnerD (B : HeegnerDiscriminantBridge) :
    B.positiveD = B.heegnerD.toNat :=
  B.positiveD_eq_heegnerD

theorem fundamental_matches_heegnerConvention (B : HeegnerDiscriminantBridge) :
    B.fundamentalDiscriminant = heegnerFundamentalDiscriminant B.heegnerD :=
  B.fundamentalDiscriminant_eq_heegnerConvention

end HeegnerDiscriminantBridge

structure NonQuadraticDiscriminantBlock where
  schurDiscriminant : Option ℤ
  forwardingStatus : NonQuadraticForwardingStatus
  forwardingStatus_eq :
    forwardingStatus = NonQuadraticForwardingStatus.blockedFromQuadraticOrderPath

namespace NonQuadraticDiscriminantBlock

def fromAR11
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    {B : BoundarySource.BoundarySourceSurface source L}
    {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}
    (C : Schur.HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    NonQuadraticDiscriminantBlock where
  schurDiscriminant := C.schurDiscriminant
  forwardingStatus := NonQuadraticForwardingStatus.blockedFromQuadraticOrderPath
  forwardingStatus_eq := by
    rfl

theorem blocked (N : NonQuadraticDiscriminantBlock) :
    N.forwardingStatus = NonQuadraticForwardingStatus.blockedFromQuadraticOrderPath :=
  N.forwardingStatus_eq

end NonQuadraticDiscriminantBlock

end Orders

end CNNA.PillarA.Arithmetic
