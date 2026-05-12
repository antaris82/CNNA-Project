import Mathlib.Data.Rat.Cast.Order
import CNNA.PillarA.Foundation.MatrixNorms
import CNNA.PillarA.Foundation.Determinism

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u

open MatrixNorm

structure RegularizationPolicy where
  epsilon : ℚ
  epsilon_pos : 0 < epsilon

namespace RegularizationPolicy

@[ext] theorem ext (P Q : RegularizationPolicy) (hepsilon : P.epsilon = Q.epsilon) : P = Q := by
  cases P with
  | mk epsilonP epsilon_posP =>
    cases Q with
    | mk epsilonQ epsilon_posQ =>
      cases hepsilon
      have hproof : epsilon_posP = epsilon_posQ := by
        apply Subsingleton.elim
      cases hproof
      rfl

def epsilonReal (P : RegularizationPolicy) : ℝ :=
  P.epsilon

theorem epsilonReal_pos (P : RegularizationPolicy) : 0 < P.epsilonReal := by
  change (0 : ℝ) < (P.epsilon : ℝ)
  exact_mod_cast P.epsilon_pos

theorem epsilonReal_nonneg (P : RegularizationPolicy) : 0 ≤ P.epsilonReal := by
  exact le_of_lt P.epsilonReal_pos

def canonicalDelta {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : RegularizationPolicy) (A : Exec.ExecMat ι) : ℚ :=
  Exec.deltaRegularization P.epsilon A

def canonicalShift {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : RegularizationPolicy) (A : Exec.ExecMat ι) : ℚ :=
  Exec.shift P.epsilon A

theorem canonicalDelta_pos {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : RegularizationPolicy) (A : Exec.ExecMat ι) :
    0 < P.canonicalDelta A := by
  exact Exec.deltaRegularization_pos P.epsilon P.epsilon_pos A

theorem canonicalDelta_ge_epsilon {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : RegularizationPolicy) (A : Exec.ExecMat ι) :
    P.epsilon ≤ P.canonicalDelta A := by
  exact Exec.deltaRegularization_ge_epsilon P.epsilon (le_of_lt P.epsilon_pos) A

theorem canonicalShift_pos {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : RegularizationPolicy) (A : Exec.ExecMat ι) :
    0 < P.canonicalShift A := by
  exact Exec.shift_pos P.epsilon P.epsilon_pos A

theorem canonicalShift_ge_epsilon {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : RegularizationPolicy) (A : Exec.ExecMat ι) :
    P.epsilon ≤ P.canonicalShift A := by
  exact Exec.shift_ge_epsilon P.epsilon (le_of_lt P.epsilon_pos) A

def key : PolicyKey RegularizationPolicy ℚ where
  key := epsilon

instance instKeyFaithful : KeyFaithful key where
  key_injective := by
    intro P Q h
    exact ext P Q h

def reference (epsilon : ℚ) (hepsilon : 0 < epsilon) : RegularizationPolicy where
  epsilon := epsilon
  epsilon_pos := hepsilon

end RegularizationPolicy

end CNNA.PillarA.Foundation
