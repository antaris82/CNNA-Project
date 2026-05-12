import CNNA.PillarA.ToC.Concrete
import CNNA.PillarA.Foundation.ConcreteSubstrate
import CNNA.PillarA.Foundation.LevelVariableSubstrate

set_option autoImplicit false

namespace CNNA.PillarA.ToC

open CNNA.PillarA.Foundation

universe u

namespace GeneratedBranchFamily

structure NonSingletonWitness (Cell : Nat → Type u) [SubstrateClass Cell] (L : Nat) where
  left : Cell L
  right : Cell L
  left_mem : left ∈ Finset.univ
  right_mem : right ∈ Finset.univ
  distinct : left ≠ right

end GeneratedBranchFamily

def generatedBranchFamily (Cell : Nat → Type u) [SubstrateClass Cell] :
    DirectedFamily (Cell := Cell) where
  carrier := fun _ => Finset.univ
  rooted := by
    ext x
    constructor
    · intro _
      exact (SubstrateClass.mem_rootLayer_iff (Cell := Cell) x).mpr (SubstrateClass.root_eq x)
    · intro _
      exact Finset.mem_univ x
  forward := by
    intro _ x _
    rcases SubstrateClass.parent_exists (Cell := Cell) x with ⟨p, hp⟩
    exact Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ p, SubstrateClass.child_mem_of_parent_mem (Cell := Cell) hp⟩

theorem generatedBranchFamily_carrier
    (Cell : Nat → Type u) [SubstrateClass Cell] (L : Nat) :
    (generatedBranchFamily Cell).carrier L = Finset.univ := by
  rfl

theorem generatedBranchFamily_rooted
    (Cell : Nat → Type u) [SubstrateClass Cell] :
    (generatedBranchFamily Cell).carrier 0 = SubstrateClass.rootLayer (Cell := Cell) := by
  ext x
  constructor
  · intro _
    exact (SubstrateClass.mem_rootLayer_iff (Cell := Cell) x).mpr (SubstrateClass.root_eq x)
  · intro _
    exact Finset.mem_univ x

def generatedBranchToC (Cell : Nat → Type u) [SubstrateClass Cell] :
    ToCStrongOf Cell :=
  ToCStrong.ofIdeal (generatedBranchFamily Cell)

theorem generatedBranchToC_ideal
    (Cell : Nat → Type u) [SubstrateClass Cell] :
    (generatedBranchToC Cell).ideal = generatedBranchFamily Cell := by
  rfl

theorem generatedBranchToC_approximant_carrier_of_le
    (Cell : Nat → Type u) [SubstrateClass Cell]
    {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    ((generatedBranchToC Cell).approximant p).carrier L = Finset.univ := by
  rw [ToCStrong.approximant_eq_truncate]
  exact DirectedFamily.truncate_carrier_of_le
    (F := generatedBranchFamily Cell) (L := L) (N := p.L_max) hL

abbrev regularGeneratedFamily (b : Nat) :
    DirectedFamily (Cell := ConcreteSubstrate.RegularCell b) :=
  generatedBranchFamily (ConcreteSubstrate.RegularCell b)

abbrev regularGeneratedToC (b : Nat) :
    ToCStrongOf (ConcreteSubstrate.RegularCell b) :=
  generatedBranchToC (ConcreteSubstrate.RegularCell b)

theorem regularGeneratedFamily_carrier (b L : Nat) :
    (regularGeneratedFamily b).carrier L = Finset.univ := by
  rfl

theorem regularGeneratedToC_approximant_carrier_of_le
    (b : Nat) {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    ((regularGeneratedToC b).approximant p).carrier L = Finset.univ := by
  exact generatedBranchToC_approximant_carrier_of_le
    (Cell := ConcreteSubstrate.RegularCell b) hL

def regularGeneratedFamily_nonSingletonAtSucc
    {b L : Nat} (hb : 0 < b) :
    GeneratedBranchFamily.NonSingletonWitness
      (ConcreteSubstrate.RegularCell b) (L + 1) := by
  let p : ConcreteSubstrate.RegularCell b L := ConcreteSubstrate.zeroCell b L
  let a : Fin (b + 1) := ⟨1, Nat.succ_lt_succ hb⟩
  let left : ConcreteSubstrate.RegularCell b (L + 1) := ConcreteSubstrate.extend p 0
  let right : ConcreteSubstrate.RegularCell b (L + 1) := ConcreteSubstrate.extend p a
  refine
    { left := left
      right := right
      left_mem := Finset.mem_univ left
      right_mem := Finset.mem_univ right
      distinct := ?_ }
  intro hsame
  have hfin : (0 : Fin (b + 1)) = a :=
    ConcreteSubstrate.extend_injective (p := p) hsame
  have hnat : (0 : Nat) = 1 := congrArg Fin.val hfin
  exact Nat.succ_ne_zero 0 hnat.symm

abbrev variableGeneratedFamily (β : Nat → Nat) :
    DirectedFamily (Cell := LevelVariableSubstrate.LevelVariableCell β) :=
  generatedBranchFamily (LevelVariableSubstrate.LevelVariableCell β)

abbrev variableGeneratedToC (β : Nat → Nat) :
    ToCStrongOf (LevelVariableSubstrate.LevelVariableCell β) :=
  generatedBranchToC (LevelVariableSubstrate.LevelVariableCell β)

theorem variableGeneratedFamily_carrier (β : Nat → Nat) (L : Nat) :
    (variableGeneratedFamily β).carrier L = Finset.univ := by
  rfl

theorem variableGeneratedToC_approximant_carrier_of_le
    (β : Nat → Nat) {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    ((variableGeneratedToC β).approximant p).carrier L = Finset.univ := by
  exact generatedBranchToC_approximant_carrier_of_le
    (Cell := LevelVariableSubstrate.LevelVariableCell β) hL

def variableGeneratedFamily_nonSingletonAtSucc
    {β : Nat → Nat} {L : Nat} (hβ : 0 < β L) :
    GeneratedBranchFamily.NonSingletonWitness
      (LevelVariableSubstrate.LevelVariableCell β) (L + 1) := by
  let p : LevelVariableSubstrate.LevelVariableCell β L := LevelVariableSubstrate.zeroCell β L
  let a : Fin (β L + 1) := ⟨1, Nat.succ_lt_succ hβ⟩
  let left : LevelVariableSubstrate.LevelVariableCell β (L + 1) :=
    LevelVariableSubstrate.extend p 0
  let right : LevelVariableSubstrate.LevelVariableCell β (L + 1) :=
    LevelVariableSubstrate.extend p a
  refine
    { left := left
      right := right
      left_mem := Finset.mem_univ left
      right_mem := Finset.mem_univ right
      distinct := ?_ }
  intro hsame
  have hfin : (0 : Fin (β L + 1)) = a :=
    LevelVariableSubstrate.extend_injective (p := p) hsame
  have hnat : (0 : Nat) = 1 := congrArg Fin.val hfin
  exact Nat.succ_ne_zero 0 hnat.symm

end CNNA.PillarA.ToC
