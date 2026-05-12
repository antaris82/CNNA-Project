import CNNA.PillarA.Foundation.ExecComplex
import CNNA.PillarA.Foundation.ConcreteSubstrate
import CNNA.PillarA.Foundation.LevelVariableSubstrate
import CNNA.PillarA.Foundation.WeightPolicy
import CNNA.PillarA.Foundation.RegularizationPolicy
import CNNA.PillarA.Foundation.SubstrateAnalysis
import CNNA.PillarA.Foundation.Interfaces
import CNNA.PillarA.Foundation.MatrixAlgebra
import CNNA.PillarA.Foundation.MatrixNorms
import CNNA.PillarA.Foundation.SubstrateClass

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

abbrev RootLayerOf (Cell : Nat → Type _) [SubstrateClass Cell] : Finset (Cell 0) :=
  SubstrateClass.rootLayer (Cell := Cell)

abbrev ParentRelOf
    (Cell : Nat → Type _) [SubstrateClass Cell] {L : Nat}
    (c : Cell (L + 1)) (p : Cell L) : Prop :=
  SubstrateClass.ParentRel (Cell := Cell) c p

abbrev ChildRelOf
    (Cell : Nat → Type _) [SubstrateClass Cell] {L : Nat}
    (p : Cell L) (c : Cell (L + 1)) : Prop :=
  SubstrateClass.ChildRel (Cell := Cell) p c

abbrev RefineSetOf
    (Cell : Nat → Type _) [SubstrateClass Cell] {L : Nat}
    (S : Finset (Cell L)) : Finset (Cell (L + 1)) :=
  SubstrateClass.refineSet (Cell := Cell) S

abbrev CoarsenSetOf
    (Cell : Nat → Type _) [SubstrateClass Cell] {L : Nat}
    (S : Finset (Cell (L + 1))) : Finset (Cell L) :=
  SubstrateClass.coarsenSet (Cell := Cell) S

abbrev SeedScalarOf (𝕜 : Type _) :=
  SeedScalar 𝕜

abbrev ExecComplexOf :=
  ExecComplex

abbrev RegularConcreteCellOf (b : Nat) (L : Nat) :=
  ConcreteSubstrate.RegularCell b L

abbrev ReferenceThreadOf (b : Nat) :=
  ConcreteSubstrate.zeroThread b

abbrev LevelVariableCellOf (branching : Nat → Nat) (L : Nat) :=
  LevelVariableSubstrate.LevelVariableCell branching L

abbrev VariationThreadOf (branching : Nat → Nat) :=
  LevelVariableSubstrate.zeroThread branching

abbrev ThermalAxisOf :=
  ThermalAxis

abbrev WeightPolicyOf :=
  WeightPolicy

abbrev RegularizationPolicyOf :=
  RegularizationPolicy

abbrev LevelUniformBranchingSubstrateOf
    (Cell : Nat → Type _) [SubstrateClass Cell] :=
  LevelUniformBranchingSubstrateClass Cell

abbrev UniformBranchingSubstrateOf
    (Cell : Nat → Type _) [SubstrateClass Cell] :=
  UniformBranchingSubstrateClass Cell

abbrev HermitianMatrixOf
    (𝕜 : Type _) (ι : Type _)
    [SeedScalar 𝕜] [Fintype ι] [DecidableEq ι] :=
  HermitianMatrix (𝕜 := 𝕜) (ι := ι)

abbrev StateVectorOf (𝕜 : Type _) (ι : Type _) :=
  StateVector 𝕜 ι

abbrev FiniteStateSpaceOf (𝕜 : Type _) (ι : Type _) :=
  FiniteStateSpace 𝕜 ι

abbrev ExecStateOf (ι : Type _) :=
  ExecState ι

abbrev ExecObservableOf (ι : Type _) :=
  ExecObservable ι

abbrev ExecMatOf (ι : Type _) :=
  MatrixNorm.Exec.ExecMat ι

abbrev ExecNormContractOf (ι : Type _) [Fintype ι] [DecidableEq ι] :=
  ExecNormContract ι

abbrev StateContractOf (𝕜 : Type _) (ι : Type _) :=
  StateContract 𝕜 ι

abbrev StarAlgebraContractOf (𝕜 : Type _) (ι : Type _) :=
  StarAlgebraContract 𝕜 ι

abbrev ObservableOf (𝕜 : Type _) (ι : Type _) :=
  Observable 𝕜 ι

scoped notation "Execℂ" =>
  CNNA.PillarA.Foundation.ExecComplex

scoped notation "RefCell[" b "," L "]" =>
  CNNA.PillarA.Foundation.ConcreteSubstrate.RegularCell b L

scoped notation "VarCell[" β "," L "]" =>
  CNNA.PillarA.Foundation.LevelVariableSubstrate.LevelVariableCell β L

scoped notation "ThermAxis" =>
  CNNA.PillarA.Foundation.ThermalAxis

scoped notation "WPolicy" =>
  CNNA.PillarA.Foundation.WeightPolicy

scoped notation "RPolicy" =>
  CNNA.PillarA.Foundation.RegularizationPolicy

scoped notation "Σ₀[" Cell "]" =>
  CNNA.PillarA.Foundation.SubstrateClass.rootLayer (Cell := Cell)

scoped notation "𝕍[" 𝕜 "," ι "]" =>
  CNNA.PillarA.Foundation.StateVector 𝕜 ι

scoped notation "𝓗fin[" 𝕜 "," ι "]" =>
  CNNA.PillarA.Foundation.FiniteStateSpace 𝕜 ι

scoped notation "ExecState[" ι "]" =>
  CNNA.PillarA.Foundation.ExecState ι

scoped notation "ExecMat[" ι "]" =>
  CNNA.PillarA.Foundation.MatrixNorm.Exec.ExecMat ι

scoped notation "ExecObs[" ι "]" =>
  CNNA.PillarA.Foundation.ExecObservable ι

scoped notation "Herm[" 𝕜 "," ι "]" =>
  CNNA.PillarA.Foundation.HermitianMatrix (𝕜 := 𝕜) (ι := ι)

scoped notation "ExecHerm[" ι "]" =>
  CNNA.PillarA.Foundation.ExecHermitian ι

scoped notation "Obs[" 𝕜 "," ι "]" =>
  CNNA.PillarA.Foundation.Observable 𝕜 ι

end CNNA.PillarA.Foundation
