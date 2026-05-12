import CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

universe u v w

namespace MatrixTransport

variable {R : Type w}
variable {ι : Type u} {κ : Type v}

def pullback (e : ι ≃ κ) (A : Matrix κ κ R) : Matrix ι ι R :=
  fun i j => A (e i) (e j)

def pushforward (e : ι ≃ κ) (A : Matrix ι ι R) : Matrix κ κ R :=
  fun i j => A (e.symm i) (e.symm j)

theorem pullback_apply
    (e : ι ≃ κ) (A : Matrix κ κ R) (i j : ι) :
    pullback e A i j = A (e i) (e j) := by
  rfl

theorem pushforward_apply
    (e : ι ≃ κ) (A : Matrix ι ι R) (i j : κ) :
    pushforward e A i j = A (e.symm i) (e.symm j) := by
  rfl

theorem pushforward_pullback_apply
    (e : ι ≃ κ) (A : Matrix κ κ R) (i j : κ) :
    pushforward e (pullback e A) i j = A i j := by
  change A (e (e.symm i)) (e (e.symm j)) = A i j
  rw [e.apply_symm_apply i, e.apply_symm_apply j]

theorem pullback_pushforward_apply
    (e : ι ≃ κ) (A : Matrix ι ι R) (i j : ι) :
    pullback e (pushforward e A) i j = A i j := by
  change A (e.symm (e i)) (e.symm (e j)) = A i j
  rw [e.symm_apply_apply i, e.symm_apply_apply j]

structure PullbackMatrix (e : ι ≃ κ) where
  sourceMatrix : Matrix κ κ R
  transported : Matrix ι ι R
  transported_eq_pullback : transported = pullback e sourceMatrix

namespace PullbackMatrix

variable {e : ι ≃ κ}

def fromSource (e : ι ≃ κ) (A : Matrix κ κ R) : PullbackMatrix (R := R) e where
  sourceMatrix := A
  transported := pullback e A
  transported_eq_pullback := by
    rfl

theorem component_identity
    (P : PullbackMatrix (R := R) e) (i j : ι) :
    P.transported i j = P.sourceMatrix (e i) (e j) := by
  rw [P.transported_eq_pullback]
  rfl

end PullbackMatrix

structure PushforwardMatrix (e : ι ≃ κ) where
  sourceMatrix : Matrix ι ι R
  transported : Matrix κ κ R
  transported_eq_pushforward : transported = pushforward e sourceMatrix

namespace PushforwardMatrix

variable {e : ι ≃ κ}

def fromSource (e : ι ≃ κ) (A : Matrix ι ι R) : PushforwardMatrix (R := R) e where
  sourceMatrix := A
  transported := pushforward e A
  transported_eq_pushforward := by
    rfl

theorem component_identity
    (P : PushforwardMatrix (R := R) e) (i j : κ) :
    P.transported i j = P.sourceMatrix (e.symm i) (e.symm j) := by
  rw [P.transported_eq_pushforward]
  rfl

end PushforwardMatrix

end MatrixTransport

end CNNA.PillarA.Arithmetic
