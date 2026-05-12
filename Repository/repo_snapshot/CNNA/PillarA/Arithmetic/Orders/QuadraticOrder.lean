import CNNA.PillarA.Arithmetic.Schur.L3Gaussian
import CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Orders

inductive QuadraticOrderShape where
  | squareRootOrder
  | halfIntegralOrder
  deriving DecidableEq, Repr

namespace QuadraticOrderShape

def discriminant (shape : QuadraticOrderShape) (radicand : ℤ) : ℤ :=
  match shape with
  | squareRootOrder => 4 * radicand
  | halfIntegralOrder => radicand

theorem squareRoot_discriminant (d : ℤ) :
    QuadraticOrderShape.discriminant QuadraticOrderShape.squareRootOrder d = 4 * d := by
  rfl

theorem halfIntegral_discriminant (d : ℤ) :
    QuadraticOrderShape.discriminant QuadraticOrderShape.halfIntegralOrder d = d := by
  rfl

end QuadraticOrderShape

structure QuadraticOrder where
  radicand : ℤ
  shape : QuadraticOrderShape
  discriminant : ℤ
  discriminant_eq : discriminant = shape.discriminant radicand

namespace QuadraticOrder

def gaussian : QuadraticOrder where
  radicand := -1
  shape := QuadraticOrderShape.squareRootOrder
  discriminant := -4
  discriminant_eq := by
    unfold QuadraticOrderShape.discriminant
    ring

def eisenstein : QuadraticOrder where
  radicand := -3
  shape := QuadraticOrderShape.halfIntegralOrder
  discriminant := -3
  discriminant_eq := by
    rfl

theorem gaussian_radicand : gaussian.radicand = -1 := by
  rfl

theorem gaussian_shape : gaussian.shape = QuadraticOrderShape.squareRootOrder := by
  rfl

theorem gaussian_discriminant : gaussian.discriminant = -4 := by
  rfl

theorem eisenstein_radicand : eisenstein.radicand = -3 := by
  rfl

theorem eisenstein_shape : eisenstein.shape = QuadraticOrderShape.halfIntegralOrder := by
  rfl

theorem eisenstein_discriminant : eisenstein.discriminant = -3 := by
  rfl

end QuadraticOrder

structure QuadraticOrderElement (O : QuadraticOrder) where
  coeffOne : ℤ
  coeffGenerator : ℤ
  deriving DecidableEq, Repr

namespace QuadraticOrderElement

variable {O : QuadraticOrder}

def zero (O : QuadraticOrder) : QuadraticOrderElement O where
  coeffOne := 0
  coeffGenerator := 0

def one (O : QuadraticOrder) : QuadraticOrderElement O where
  coeffOne := 1
  coeffGenerator := 0

theorem zero_coeffOne : (zero O).coeffOne = 0 := by
  rfl

theorem zero_coeffGenerator : (zero O).coeffGenerator = 0 := by
  rfl

theorem one_coeffOne : (one O).coeffOne = 1 := by
  rfl

theorem one_coeffGenerator : (one O).coeffGenerator = 0 := by
  rfl

end QuadraticOrderElement

def squareRootOrderNorm (d a b : ℤ) : ℤ :=
  a * a - d * b * b

def halfIntegralOrderNorm (m a b : ℤ) : ℤ :=
  a * a + a * b + m * b * b

theorem squareRootOrderNorm_def (d a b : ℤ) :
    squareRootOrderNorm d a b = a * a - d * b * b := by
  rfl

theorem halfIntegralOrderNorm_def (m a b : ℤ) :
    halfIntegralOrderNorm m a b = a * a + a * b + m * b * b := by
  rfl

structure HalfIntegralCoefficientCertificate where
  radicand : ℤ
  coefficient : ℤ
  coefficient_eq : 4 * coefficient = 1 - radicand

namespace HalfIntegralCoefficientCertificate

def eisenstein : HalfIntegralCoefficientCertificate where
  radicand := -3
  coefficient := 1
  coefficient_eq := by
    ring

theorem eisenstein_coefficient : eisenstein.coefficient = 1 := by
  rfl

theorem eisenstein_radicand : eisenstein.radicand = -3 := by
  rfl

theorem coefficient_relation (C : HalfIntegralCoefficientCertificate) :
    4 * C.coefficient = 1 - C.radicand :=
  C.coefficient_eq

end HalfIntegralCoefficientCertificate

inductive QuadraticOrderProvenance where
  | ar8Eisenstein
  | ar9Gaussian
  | ar11QuadraticHeegner
  | ar11QuadraticNonHeegner
  deriving DecidableEq, Repr

inductive IrreduciblePrimeDisciplineStatus where
  | noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  deriving DecidableEq, Repr

inductive QuadraticOrderClosureStatus where
  | ar12QuadraticOrderConventionClosed
  deriving DecidableEq, Repr

structure QuadraticOrderConventionCertificate where
  order : QuadraticOrder
  provenance : QuadraticOrderProvenance
  closureStatus : QuadraticOrderClosureStatus
  closureStatus_eq :
    closureStatus = QuadraticOrderClosureStatus.ar12QuadraticOrderConventionClosed
  irreduciblePrimeDisciplineStatus : IrreduciblePrimeDisciplineStatus
  irreduciblePrimeDisciplineStatus_eq :
    irreduciblePrimeDisciplineStatus =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD

namespace QuadraticOrderConventionCertificate

def gaussian : QuadraticOrderConventionCertificate where
  order := QuadraticOrder.gaussian
  provenance := QuadraticOrderProvenance.ar9Gaussian
  closureStatus := QuadraticOrderClosureStatus.ar12QuadraticOrderConventionClosed
  closureStatus_eq := by
    rfl
  irreduciblePrimeDisciplineStatus :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  irreduciblePrimeDisciplineStatus_eq := by
    rfl

def eisenstein : QuadraticOrderConventionCertificate where
  order := QuadraticOrder.eisenstein
  provenance := QuadraticOrderProvenance.ar8Eisenstein
  closureStatus := QuadraticOrderClosureStatus.ar12QuadraticOrderConventionClosed
  closureStatus_eq := by
    rfl
  irreduciblePrimeDisciplineStatus :=
    IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD
  irreduciblePrimeDisciplineStatus_eq := by
    rfl

theorem closure_closed (C : QuadraticOrderConventionCertificate) :
    C.closureStatus = QuadraticOrderClosureStatus.ar12QuadraticOrderConventionClosed :=
  C.closureStatus_eq

theorem no_irreducible_prime_shortcut (C : QuadraticOrderConventionCertificate) :
    C.irreduciblePrimeDisciplineStatus =
      IrreduciblePrimeDisciplineStatus.noIrreduciblePrimeEquivalenceWithoutClassNumberOrUFD :=
  C.irreduciblePrimeDisciplineStatus_eq

theorem gaussian_order_discriminant :
    gaussian.order.discriminant = -4 := by
  rfl

theorem eisenstein_order_discriminant :
    eisenstein.order.discriminant = -3 := by
  rfl

end QuadraticOrderConventionCertificate

end Orders

end CNNA.PillarA.Arithmetic
