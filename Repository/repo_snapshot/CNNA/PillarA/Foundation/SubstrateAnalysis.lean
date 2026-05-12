import CNNA.PillarA.Foundation.ConcreteSubstrate
import CNNA.PillarA.Foundation.LevelVariableSubstrate

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u

class LevelUniformBranchingSubstrateClass (Cell : Nat → Type u)
    [SubstrateClass Cell] : Type (u + 1) where
  branchingAt : Nat → Nat
  branching_eq : ∀ {L : Nat} (c : Cell L), SubstrateClass.branching c = branchingAt L

class UniformBranchingSubstrateClass (Cell : Nat → Type u)
    [SubstrateClass Cell] : Type (u + 1) where
  branchingConst : Nat
  branching_eq : ∀ {L : Nat} (c : Cell L), SubstrateClass.branching c = branchingConst

instance instLevelUniformBranchingRegularCell (b : Nat) :
    LevelUniformBranchingSubstrateClass (ConcreteSubstrate.RegularCell b) where
  branchingAt := fun _ => b + 1
  branching_eq := by
    intro L c
    rfl

instance instUniformBranchingRegularCell (b : Nat) :
    UniformBranchingSubstrateClass (ConcreteSubstrate.RegularCell b) where
  branchingConst := b + 1
  branching_eq := by
    intro L c
    rfl

instance instLevelUniformBranchingLevelVariableCell (branching : Nat → Nat) :
    LevelUniformBranchingSubstrateClass (LevelVariableSubstrate.LevelVariableCell branching) where
  branchingAt := fun L => branching L + 1
  branching_eq := by
    intro L c
    rfl

namespace SubstrateAnalysis

inductive AssumptionTier where
  | substrate
  | deterministic
  | levelUniform
  | uniform
  deriving DecidableEq, Repr

structure ClassifiedFact where
  name : String
  tier : AssumptionTier
  deriving Repr

def assumptionLedger : List ClassifiedFact :=
  [⟨"rootCard_eq_one", AssumptionTier.substrate⟩,
   ⟨"branchingSetAt_nonempty", AssumptionTier.substrate⟩,
   ⟨"parentCard_eq_one", AssumptionTier.deterministic⟩,
   ⟨"branchingSetAt_eq_singleton_level", AssumptionTier.levelUniform⟩,
   ⟨"branchingSetAt_eq_singleton_uniform", AssumptionTier.uniform⟩]

variable {Cell : Nat → Type u} [SubstrateClass Cell]

def rootCard : Nat :=
  Fintype.card (Cell 0)

theorem rootCard_eq_one : rootCard (Cell := Cell) = 1 := by
  rcases SubstrateClass.root_nonempty (Cell := Cell) with ⟨a⟩
  letI : Unique (Cell 0) :=
    { default := a
      uniq := fun x => (SubstrateClass.root_eq x).trans (SubstrateClass.root_eq a).symm }
  unfold rootCard
  exact Fintype.card_unique (α := Cell 0)

def branchingSetAt (L : Nat) : Finset Nat :=
  Finset.univ.image (fun c : Cell L => SubstrateClass.branching c)

theorem level_nonempty : ∀ L : Nat, Nonempty (Cell L)
  | 0 => SubstrateClass.root_nonempty (Cell := Cell)
  | L + 1 => by
      rcases level_nonempty L with ⟨c⟩
      rcases SubstrateClass.child_exists (Cell := Cell) c with ⟨d, hd⟩
      exact ⟨d⟩

theorem branchingSetAt_nonempty (L : Nat) :
    (branchingSetAt (Cell := Cell) L).Nonempty := by
  rcases level_nonempty (Cell := Cell) L with ⟨c⟩
  refine ⟨SubstrateClass.branching c, ?_⟩
  exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩

theorem branching_mem_pos {L : Nat} {n : Nat}
    (hn : n ∈ branchingSetAt (Cell := Cell) L) :
    0 < n := by
  rcases Finset.mem_image.mp hn with ⟨c, -, hc⟩
  rw [← hc]
  exact SubstrateClass.branching_pos (Cell := Cell) c

section Deterministic

variable [DeterministicSubstrateClass Cell]

def parentCard {L : Nat} (c : Cell (L + 1)) : Nat :=
  (SubstrateClass.parents c).card

theorem parentCard_eq_one {L : Nat} (c : Cell (L + 1)) :
    parentCard (Cell := Cell) c = 1 := by
  unfold parentCard
  rw [DeterministicSubstrateClass.parents_eq_singleton_parent (Cell := Cell) c]
  simp

end Deterministic

section LevelUniform

variable [LevelUniformBranchingSubstrateClass Cell]

def branchingAt (L : Nat) : Nat :=
  LevelUniformBranchingSubstrateClass.branchingAt (Cell := Cell) L

theorem branching_eq_level {L : Nat} (c : Cell L) :
    SubstrateClass.branching c = branchingAt (Cell := Cell) L := by
  exact LevelUniformBranchingSubstrateClass.branching_eq (Cell := Cell) c

theorem branchingSetAt_eq_singleton_level (L : Nat) :
    branchingSetAt (Cell := Cell) L = {branchingAt (Cell := Cell) L} := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨c, -, hc⟩
    have hbranch : SubstrateClass.branching c = branchingAt (Cell := Cell) L :=
      branching_eq_level (Cell := Cell) c
    rw [hbranch] at hc
    simpa using hc.symm
  · intro hn
    simp at hn
    rcases level_nonempty (Cell := Cell) L with ⟨c⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨c, Finset.mem_univ _, (branching_eq_level (Cell := Cell) c).trans hn.symm⟩

end LevelUniform

section Uniform

variable [UniformBranchingSubstrateClass Cell]

def branchingConst : Nat :=
  UniformBranchingSubstrateClass.branchingConst (Cell := Cell)

theorem branching_eq_uniform {L : Nat} (c : Cell L) :
    SubstrateClass.branching c = branchingConst (Cell := Cell) := by
  exact UniformBranchingSubstrateClass.branching_eq (Cell := Cell) c

theorem branchingSetAt_eq_singleton_uniform (L : Nat) :
    branchingSetAt (Cell := Cell) L = {branchingConst (Cell := Cell)} := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨c, -, hc⟩
    have hbranch : SubstrateClass.branching c = branchingConst (Cell := Cell) :=
      branching_eq_uniform (Cell := Cell) c
    rw [hbranch] at hc
    simpa using hc.symm
  · intro hn
    simp at hn
    rcases level_nonempty (Cell := Cell) L with ⟨c⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨c, Finset.mem_univ _, (branching_eq_uniform (Cell := Cell) c).trans hn.symm⟩

end Uniform

end SubstrateAnalysis

end CNNA.PillarA.Foundation
