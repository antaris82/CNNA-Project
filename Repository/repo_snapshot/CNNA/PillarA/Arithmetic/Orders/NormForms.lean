import CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Orders

structure BinaryQuadraticNormForm where
  coefficientA : ℤ
  coefficientB : ℤ
  coefficientC : ℤ
  deriving DecidableEq, Repr

namespace BinaryQuadraticNormForm

def eval (F : BinaryQuadraticNormForm) (x y : ℤ) : ℤ :=
  F.coefficientA * x * x + F.coefficientB * x * y + F.coefficientC * y * y

def discriminant (F : BinaryQuadraticNormForm) : ℤ :=
  F.coefficientB * F.coefficientB - 4 * F.coefficientA * F.coefficientC

def gaussian : BinaryQuadraticNormForm where
  coefficientA := 1
  coefficientB := 0
  coefficientC := 1

def eisenstein : BinaryQuadraticNormForm where
  coefficientA := 1
  coefficientB := -1
  coefficientC := 1

theorem gaussian_eval (x y : ℤ) :
    gaussian.eval x y = x * x + y * y := by
  unfold eval gaussian
  ring

theorem eisenstein_eval (x y : ℤ) :
    eisenstein.eval x y = x * x - x * y + y * y := by
  unfold eval eisenstein
  ring

theorem gaussian_discriminant :
    gaussian.discriminant = -4 := by
  unfold discriminant gaussian
  ring

theorem eisenstein_discriminant :
    eisenstein.discriminant = -3 := by
  unfold discriminant eisenstein
  ring

end BinaryQuadraticNormForm

inductive QuadraticNormFormStatus where
  | normFormCertified
  deriving DecidableEq, Repr

inductive UnitConventionStatus where
  | unitClaimsRestrictedToNormWitnesses
  deriving DecidableEq, Repr

structure QuadraticNormFormCertificate where
  orderCertificate : QuadraticOrderConventionCertificate
  normForm : BinaryQuadraticNormForm
  normDiscriminant : ℤ
  normDiscriminant_eq : normDiscriminant = normForm.discriminant
  bridge : SchurToFundamentalDiscriminantBridge
  schur_discrim_bridge :
    bridge.schurDiscriminant =
      ((bridge.conductor * bridge.conductor : Nat) : ℤ) * bridge.fundamentalDiscriminant
  normFormStatus : QuadraticNormFormStatus
  normFormStatus_eq : normFormStatus = QuadraticNormFormStatus.normFormCertified
  unitConventionStatus : UnitConventionStatus
  unitConventionStatus_eq :
    unitConventionStatus = UnitConventionStatus.unitClaimsRestrictedToNormWitnesses
  irreduciblePrimeDisciplineStatus : IrreduciblePrimeDisciplineStatus
  irreduciblePrimeDisciplineStatus_eq :
    irreduciblePrimeDisciplineStatus =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD

namespace QuadraticNormFormCertificate

def gaussian : QuadraticNormFormCertificate where
  orderCertificate := QuadraticOrderConventionCertificate.gaussian
  normForm := BinaryQuadraticNormForm.gaussian
  normDiscriminant := -4
  normDiscriminant_eq := by
    exact BinaryQuadraticNormForm.gaussian_discriminant.symm
  bridge := SchurToFundamentalDiscriminantBridge.gaussian
  schur_discrim_bridge :=
    SchurToFundamentalDiscriminantBridge.gaussian_bridge_formula
  normFormStatus := QuadraticNormFormStatus.normFormCertified
  normFormStatus_eq := by
    rfl
  unitConventionStatus := UnitConventionStatus.unitClaimsRestrictedToNormWitnesses
  unitConventionStatus_eq := by
    rfl
  irreduciblePrimeDisciplineStatus :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  irreduciblePrimeDisciplineStatus_eq := by
    rfl

def eisenstein : QuadraticNormFormCertificate where
  orderCertificate := QuadraticOrderConventionCertificate.eisenstein
  normForm := BinaryQuadraticNormForm.eisenstein
  normDiscriminant := -3
  normDiscriminant_eq := by
    exact BinaryQuadraticNormForm.eisenstein_discriminant.symm
  bridge := SchurToFundamentalDiscriminantBridge.eisenstein
  schur_discrim_bridge :=
    SchurToFundamentalDiscriminantBridge.eisenstein_bridge_formula
  normFormStatus := QuadraticNormFormStatus.normFormCertified
  normFormStatus_eq := by
    rfl
  unitConventionStatus := UnitConventionStatus.unitClaimsRestrictedToNormWitnesses
  unitConventionStatus_eq := by
    rfl
  irreduciblePrimeDisciplineStatus :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  irreduciblePrimeDisciplineStatus_eq := by
    rfl

theorem norm_form_certified (C : QuadraticNormFormCertificate) :
    C.normFormStatus = QuadraticNormFormStatus.normFormCertified :=
  C.normFormStatus_eq

theorem unit_claims_restricted (C : QuadraticNormFormCertificate) :
    C.unitConventionStatus = UnitConventionStatus.unitClaimsRestrictedToNormWitnesses :=
  C.unitConventionStatus_eq

theorem no_irreducible_prime_shortcut (C : QuadraticNormFormCertificate) :
    C.irreduciblePrimeDisciplineStatus =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD :=
  C.irreduciblePrimeDisciplineStatus_eq

theorem schur_to_fundamental_bridge (C : QuadraticNormFormCertificate) :
    C.bridge.schurDiscriminant =
      ((C.bridge.conductor * C.bridge.conductor : Nat) : ℤ) * C.bridge.fundamentalDiscriminant :=
  C.schur_discrim_bridge

theorem gaussian_norm_discriminant :
    gaussian.normDiscriminant = -4 := by
  rfl

theorem eisenstein_norm_discriminant :
    eisenstein.normDiscriminant = -3 := by
  rfl

end QuadraticNormFormCertificate

structure UnitNormWitness (C : QuadraticNormFormCertificate) where
  element : QuadraticOrderElement C.orderCertificate.order
  normValue : ℤ
  normValue_eq : normValue = C.normForm.eval element.coeffOne element.coeffGenerator
  unitNorm : normValue = 1 ∨ normValue = -1
  unitConventionStatus : UnitConventionStatus
  unitConventionStatus_eq :
    unitConventionStatus = UnitConventionStatus.unitClaimsRestrictedToNormWitnesses

namespace UnitNormWitness

theorem unit_norm_condition {C : QuadraticNormFormCertificate} (U : UnitNormWitness C) :
    U.normValue = 1 ∨ U.normValue = -1 :=
  U.unitNorm

theorem convention_restricted {C : QuadraticNormFormCertificate} (U : UnitNormWitness C) :
    U.unitConventionStatus = UnitConventionStatus.unitClaimsRestrictedToNormWitnesses :=
  U.unitConventionStatus_eq

end UnitNormWitness

inductive AR12ForwardingStatus where
  | quadraticCertificateForwardedToOrderConvention
  | nonQuadraticCertificateBlockedBeforeOrderConvention
  deriving DecidableEq, Repr

structure AR12QuadraticOrderOutput
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) where
  ar11Certificate : Schur.HigherLevelAR11Certificate B b hL z
  ar11Outcome : Schur.HigherLevelAR11Outcome
  ar11Outcome_eq : ar11Outcome = ar11Certificate.outcome
  forwardingStatus : AR12ForwardingStatus
  orderCertificate : Option QuadraticOrderConventionCertificate
  normFormCertificate : Option QuadraticNormFormCertificate
  nonQuadraticBlock : Option NonQuadraticDiscriminantBlock
  noIrreduciblePrimeShortcut : IrreduciblePrimeDisciplineStatus
  noIrreduciblePrimeShortcut_eq :
    noIrreduciblePrimeShortcut =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD

namespace AR12QuadraticOrderOutput

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}
variable {B : BoundarySource.BoundarySourceSurface source L}
variable {b : Nat} {hL : 3 < L} {z : Schur.SpectralParameter}

def fromQuadraticHeegner
    (C : Schur.HigherLevelQuadraticHeegnerCertificate B b hL z)
    (Q : QuadraticNormFormCertificate) :
    AR12QuadraticOrderOutput B b hL z where
  ar11Certificate := Schur.HigherLevelAR11Certificate.quadraticHeegner C
  ar11Outcome := Schur.HigherLevelAR11Outcome.quadraticHeegnerHit
  ar11Outcome_eq := by
    rfl
  forwardingStatus := AR12ForwardingStatus.quadraticCertificateForwardedToOrderConvention
  orderCertificate := some Q.orderCertificate
  normFormCertificate := some Q
  nonQuadraticBlock := none
  noIrreduciblePrimeShortcut :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  noIrreduciblePrimeShortcut_eq := by
    rfl

def fromQuadraticNonHeegner
    (C : Schur.HigherLevelQuadraticNonHeegnerCertificate B b hL z)
    (Q : QuadraticNormFormCertificate) :
    AR12QuadraticOrderOutput B b hL z where
  ar11Certificate := Schur.HigherLevelAR11Certificate.quadraticNonHeegner C
  ar11Outcome := Schur.HigherLevelAR11Outcome.quadraticNonHeegner
  ar11Outcome_eq := by
    rfl
  forwardingStatus := AR12ForwardingStatus.quadraticCertificateForwardedToOrderConvention
  orderCertificate := some Q.orderCertificate
  normFormCertificate := some Q
  nonQuadraticBlock := none
  noIrreduciblePrimeShortcut :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  noIrreduciblePrimeShortcut_eq := by
    rfl

def fromIrreducibleOrHigherDegree
    (C : Schur.HigherLevelIrreducibleOrHigherDegreeCertificate B b hL z) :
    AR12QuadraticOrderOutput B b hL z where
  ar11Certificate := Schur.HigherLevelAR11Certificate.irreducibleOrHigherDegree C
  ar11Outcome := Schur.HigherLevelAR11Outcome.irreducibleOrHigherDegree
  ar11Outcome_eq := by
    rfl
  forwardingStatus := AR12ForwardingStatus.nonQuadraticCertificateBlockedBeforeOrderConvention
  orderCertificate := none
  normFormCertificate := none
  nonQuadraticBlock := some (NonQuadraticDiscriminantBlock.fromAR11 C)
  noIrreduciblePrimeShortcut :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  noIrreduciblePrimeShortcut_eq := by
    rfl

theorem outcome_eq_certificate
    (O : AR12QuadraticOrderOutput B b hL z) :
    O.ar11Outcome = O.ar11Certificate.outcome :=
  O.ar11Outcome_eq

theorem no_irreducible_prime_shortcut
    (O : AR12QuadraticOrderOutput B b hL z) :
    O.noIrreduciblePrimeShortcut =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD :=
  O.noIrreduciblePrimeShortcut_eq

end AR12QuadraticOrderOutput

end Orders

namespace StrengtheningAR12

abbrev AR12QuadraticOrderShape := Orders.QuadraticOrderShape
abbrev AR12QuadraticOrder := Orders.QuadraticOrder
abbrev AR12QuadraticOrderElement := Orders.QuadraticOrderElement
abbrev AR12BinaryQuadraticNormForm := Orders.BinaryQuadraticNormForm
abbrev AR12SchurToFundamentalDiscriminantBridge :=
  Orders.SchurToFundamentalDiscriminantBridge
abbrev AR12HeegnerDiscriminantBridge := Orders.HeegnerDiscriminantBridge
abbrev AR12QuadraticNormFormCertificate := Orders.QuadraticNormFormCertificate
abbrev AR12QuadraticOrderOutput
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L)
    (b : Nat) (hL : 3 < L)
    (z : Schur.SpectralParameter) :=
  Orders.AR12QuadraticOrderOutput B b hL z
abbrev AR12ForwardingStatus := Orders.AR12ForwardingStatus
abbrev AR12IrreduciblePrimeDisciplineStatus := Orders.IrreduciblePrimeDisciplineStatus

end StrengtheningAR12

end CNNA.PillarA.Arithmetic
