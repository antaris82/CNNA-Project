import Mathlib
import CNNA.PillarA.Foundation.Interfaces

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u v w z

structure PolicyKey (Policy : Type u) (Key : Type v) where
  key : Policy → Key

namespace PolicyKey

variable {Policy : Type u} {Key : Type v}

def SameKey (K : PolicyKey Policy Key) (p q : Policy) : Prop :=
  K.key p = K.key q

@[refl] theorem sameKey_refl (K : PolicyKey Policy Key) (p : Policy) :
    K.SameKey p p := by
  rfl

@[symm] theorem sameKey_symm (K : PolicyKey Policy Key) {p q : Policy} :
    K.SameKey p q → K.SameKey q p := by
  intro h
  exact h.symm

@[trans] theorem sameKey_trans (K : PolicyKey Policy Key) {p q r : Policy} :
    K.SameKey p q → K.SameKey q r → K.SameKey p r := by
  intro hpq hqr
  exact hpq.trans hqr

end PolicyKey

class KeyFaithful {Policy : Type u} {Key : Type v} (K : PolicyKey Policy Key) : Prop where
  key_injective : Function.Injective K.key

namespace KeyFaithful

variable {Policy : Type u} {Key : Type v} {K : PolicyKey Policy Key} [KeyFaithful K]

 theorem eq_of_sameKey {p q : Policy} (h : K.SameKey p q) : p = q := by
  exact KeyFaithful.key_injective (K := K) h

end KeyFaithful

structure KeyedFamily (Policy : Type u) (Key : Type v) (α : Type w) where
  keyOf : Policy → Key
  val : Policy → α

class KeyInvariant {Policy : Type u} {Key : Type v} {α : Type w}
    (F : KeyedFamily Policy Key α) : Prop where
  val_eq_of_key_eq : ∀ {p q : Policy}, F.keyOf p = F.keyOf q → F.val p = F.val q

namespace KeyedFamily

variable {Policy : Type u} {Key : Type v} {α : Type w}

def mkFromKey (keyOf : Policy → Key) (build : Key → α) :
    KeyedFamily Policy Key α :=
  { keyOf := keyOf
    val := fun p => build (keyOf p) }

theorem mkFromKey_keyOf (keyOf : Policy → Key) (build : Key → α) (p : Policy) :
    (mkFromKey keyOf build).keyOf p = keyOf p := by
  rfl

theorem mkFromKey_val (keyOf : Policy → Key) (build : Key → α) (p : Policy) :
    (mkFromKey keyOf build).val p = build (keyOf p) := by
  rfl

instance instKeyInvariant_mkFromKey (keyOf : Policy → Key) (build : Key → α) :
    KeyInvariant (mkFromKey keyOf build) where
  val_eq_of_key_eq := by
    intro p q hpq
    change build (keyOf p) = build (keyOf q)
    exact congrArg build hpq

 theorem val_eq_of_key_eq (F : KeyedFamily Policy Key α) [KeyInvariant F]
    {p q : Policy} (h : F.keyOf p = F.keyOf q) :
    F.val p = F.val q :=
  by
  exact KeyInvariant.val_eq_of_key_eq (F := F) h

end KeyedFamily

structure KeyedMap (Policy : Type u) (Key : Type v) (α : Type w) (β : Type z) where
  keyOf : Policy → Key
  map : Policy → α → β

class KeyedMapInvariant {Policy : Type u} {Key : Type v} {α : Type w} {β : Type z}
    (F : KeyedMap Policy Key α β) : Prop where
  map_eq_of_key_eq : ∀ {p q : Policy} (a : α), F.keyOf p = F.keyOf q → F.map p a = F.map q a

namespace KeyedMap

variable {Policy : Type u} {Key : Type v} {α : Type w} {β : Type z}

def mkFromKey (keyOf : Policy → Key) (build : Key → α → β) :
    KeyedMap Policy Key α β :=
  { keyOf := keyOf
    map := fun p a => build (keyOf p) a }

theorem mkFromKey_map (keyOf : Policy → Key) (build : Key → α → β)
    (p : Policy) (a : α) :
    (mkFromKey keyOf build).map p a = build (keyOf p) a := by
  rfl

instance instKeyedMapInvariant_mkFromKey (keyOf : Policy → Key) (build : Key → α → β) :
    KeyedMapInvariant (mkFromKey keyOf build) where
  map_eq_of_key_eq := by
    intro p q a hpq
    change build (keyOf p) a = build (keyOf q) a
    exact congrArg (fun k => build k a) hpq

 theorem map_eq_of_key_eq (F : KeyedMap Policy Key α β) [KeyedMapInvariant F]
    {p q : Policy} (a : α) (h : F.keyOf p = F.keyOf q) :
    F.map p a = F.map q a :=
  by
  exact KeyedMapInvariant.map_eq_of_key_eq (F := F) a h

end KeyedMap

end CNNA.PillarA.Foundation
