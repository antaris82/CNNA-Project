import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Trace
import CNNA.PillarA.Finite.DynamicsAdapter

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure ChannelSeedStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : DynamicsAdapterStrong Cell T

abbrev ChannelSeedStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ChannelSeedStrong (Cell := Cell) T

namespace ChannelSeedStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (C₁ C₂ : ChannelSeedStrong Cell T)
    (hsource : C₁.source = C₂.source) :
    C₁ = C₂ := by
  cases C₁ with
  | mk source₁ =>
      cases C₂ with
      | mk source₂ =>
          cases hsource
          rfl

def ofDynamicsAdapter (D : DynamicsAdapterStrong Cell T) :
    ChannelSeedStrong Cell T where
  source := D

def cast (h : T = U) (C : ChannelSeedStrong Cell T) :
    ChannelSeedStrong Cell U := by
  cases h
  exact C

theorem cast_rfl (C : ChannelSeedStrong Cell T) :
    cast (Cell := Cell) rfl C = C := by
  rfl

abbrev dynamicsAdapter (C : ChannelSeedStrong Cell T) : DynamicsAdapterStrong Cell T :=
  C.source

abbrev stateSpace (C : ChannelSeedStrong Cell T) : StateSpaceStrong Cell T :=
  C.dynamicsAdapter.stateSpace

abbrev boxVertex (C : ChannelSeedStrong Cell T) :=
  C.stateSpace.boxVertex

abbrev execObservable (C : ChannelSeedStrong Cell T) : Type _ :=
  C.stateSpace.execObservable

abbrev execDensityOperator (C : ChannelSeedStrong Cell T) : Type _ :=
  C.stateSpace.execDensityOperator

abbrev execState (C : ChannelSeedStrong Cell T) : Type _ :=
  C.stateSpace.execState

abbrev mirrorObservable (C : ChannelSeedStrong Cell T) : Type _ :=
  C.stateSpace.mirrorObservable

abbrev mirrorDensityOperator (C : ChannelSeedStrong Cell T) : Type _ :=
  C.stateSpace.mirrorDensityOperator

abbrev schrodingerChannel (C : ChannelSeedStrong Cell T)
    (Ξ : EvolutionApproxAxis) : C.execDensityOperator → C.execDensityOperator :=
  C.dynamicsAdapter.schrodingerDensity Ξ

abbrev heisenbergChannel (C : ChannelSeedStrong Cell T)
    (Ξ : EvolutionApproxAxis) : C.execObservable → C.execObservable :=
  C.dynamicsAdapter.heisenbergObservable Ξ

def execMatrixQuadraticForm {ι : Type _} [Fintype ι]
    (A : Matrix ι ι ExecComplex) (ψ : StateVector ExecComplex ι) : ExecComplex :=
  sesq (𝕜 := ExecComplex) ψ (act (𝕜 := ExecComplex) A ψ)

def execMatrixIsPositive {ι : Type _} [Fintype ι]
    (A : Matrix ι ι ExecComplex) : Prop :=
  IsHermitian A ∧
    ∀ ψ : StateVector ExecComplex ι, 0 ≤ (execMatrixQuadraticForm A ψ).re

structure KrausFamily (C : ChannelSeedStrong Cell T) where
  Index : Type _
  instFintypeIndex : Fintype Index
  op : Index → C.execObservable

attribute [instance] KrausFamily.instFintypeIndex

namespace KrausFamily

variable {C : ChannelSeedStrong Cell T}

def schrodingerAction (K : KrausFamily C)
    (ρ : C.execDensityOperator) : C.execDensityOperator :=
  ∑ a : K.Index, K.op a * ρ * star (K.op a)

def heisenbergAction (K : KrausFamily C)
    (A : C.execObservable) : C.execObservable :=
  ∑ a : K.Index, star (K.op a) * A * K.op a

def single (C : ChannelSeedStrong Cell T) (K : C.execObservable) : KrausFamily C where
  Index := Fin 1
  instFintypeIndex := inferInstance
  op := fun _ => K

def identity (C : ChannelSeedStrong Cell T) : KrausFamily C :=
  single C 1

def comp (K₂ K₁ : KrausFamily C) : KrausFamily C where
  Index := K₂.Index × K₁.Index
  instFintypeIndex := inferInstance
  op := fun ab => K₂.op ab.1 * K₁.op ab.2

end KrausFamily

structure UnitarySingleKrausSeed (C : ChannelSeedStrong Cell T) where
  operator : C.execObservable
  star_mul_operator : star operator * operator = 1
  operator_mul_star : operator * star operator = 1

namespace UnitarySingleKrausSeed

variable {C : ChannelSeedStrong Cell T}

def krausFamily (U : UnitarySingleKrausSeed C) : KrausFamily C :=
  KrausFamily.single C U.operator

def schrodinger (U : UnitarySingleKrausSeed C)
    (ρ : C.execDensityOperator) : C.execDensityOperator :=
  U.operator * ρ * star U.operator

def heisenberg (U : UnitarySingleKrausSeed C)
    (A : C.execObservable) : C.execObservable :=
  star U.operator * A * U.operator

theorem schrodinger_eq_krausAction (U : UnitarySingleKrausSeed C)
    (ρ : C.execDensityOperator) :
    U.schrodinger ρ = (U.krausFamily).schrodingerAction ρ := by
  unfold schrodinger KrausFamily.schrodingerAction krausFamily KrausFamily.single
  simp

theorem heisenberg_eq_krausAction (U : UnitarySingleKrausSeed C)
    (A : C.execObservable) :
    U.heisenberg A = (U.krausFamily).heisenbergAction A := by
  unfold heisenberg KrausFamily.heisenbergAction krausFamily KrausFamily.single
  simp

theorem schrodinger_tracePreserving (U : UnitarySingleKrausSeed C)
    (ρ : C.execDensityOperator) :
    C.stateSpace.execTrace (U.schrodinger ρ) = C.stateSpace.execTrace ρ := by
  unfold StateSpaceStrong.execTrace schrodinger
  calc
    Matrix.trace (U.operator * ρ * star U.operator)
        = Matrix.trace ((star U.operator * U.operator) * ρ) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle U.operator ρ (star U.operator))
    _ = Matrix.trace (1 * ρ) := by
          rw [U.star_mul_operator]
    _ = Matrix.trace ρ := by
          simp

end UnitarySingleKrausSeed

structure AlgebraicChannelPackage (C : ChannelSeedStrong Cell T) where
  schrodinger : C.execDensityOperator → C.execDensityOperator
  heisenberg : C.execObservable → C.execObservable
  krausFamily : KrausFamily C
  schrodinger_eq_kraus : ∀ ρ : C.execDensityOperator,
    schrodinger ρ = krausFamily.schrodingerAction ρ
  heisenberg_eq_kraus : ∀ A : C.execObservable,
    heisenberg A = krausFamily.heisenbergAction A

namespace AlgebraicChannelPackage

variable {C : ChannelSeedStrong Cell T}

def ofKrausFamily (K : KrausFamily C) : AlgebraicChannelPackage C where
  schrodinger := K.schrodingerAction
  heisenberg := K.heisenbergAction
  krausFamily := K
  schrodinger_eq_kraus := by
    intro ρ
    rfl
  heisenberg_eq_kraus := by
    intro A
    rfl

def ofUnitarySingleKraus (U : UnitarySingleKrausSeed C) : AlgebraicChannelPackage C where
  schrodinger := U.schrodinger
  heisenberg := U.heisenberg
  krausFamily := U.krausFamily
  schrodinger_eq_kraus := U.schrodinger_eq_krausAction
  heisenberg_eq_kraus := U.heisenberg_eq_krausAction

def matrixUnit (C : ChannelSeedStrong Cell T) (i j : C.boxVertex) : C.execDensityOperator :=
  Matrix.single i j (1 : ExecComplex)

def choiMatrix (P : AlgebraicChannelPackage C) :
    Matrix (C.boxVertex × C.boxVertex) (C.boxVertex × C.boxVertex) ExecComplex :=
  fun ik jl =>
    P.schrodinger (matrixUnit C ik.1 jl.1) ik.2 jl.2

def isTracePreserving (P : AlgebraicChannelPackage C) : Prop :=
  ∀ ρ : C.execDensityOperator,
    C.stateSpace.execTrace (P.schrodinger ρ) = C.stateSpace.execTrace ρ

def isPositive (P : AlgebraicChannelPackage C) : Prop :=
  ∀ ρ : C.execDensityOperator,
    execMatrixIsPositive ρ → execMatrixIsPositive (P.schrodinger ρ)

def isCompletelyPositive (P : AlgebraicChannelPackage C) : Prop :=
  execMatrixIsPositive P.choiMatrix

def isCPTP (P : AlgebraicChannelPackage C) : Prop :=
  P.isTracePreserving ∧ P.isCompletelyPositive

def identity (C : ChannelSeedStrong Cell T) : AlgebraicChannelPackage C :=
  ofKrausFamily (KrausFamily.identity C)

def zeroTime (C : ChannelSeedStrong Cell T) (N : Nat) : AlgebraicChannelPackage C where
  schrodinger := C.schrodingerChannel (EvolutionApproxAxis.zero N)
  heisenberg := C.heisenbergChannel (EvolutionApproxAxis.zero N)
  krausFamily := KrausFamily.identity C
  schrodinger_eq_kraus := by
    intro ρ
    have hzero := C.dynamicsAdapter.schrodingerDensity_zero N ρ
    calc
      C.schrodingerChannel (EvolutionApproxAxis.zero N) ρ = ρ := hzero
      _ = (KrausFamily.identity C).schrodingerAction ρ := by
            unfold KrausFamily.identity KrausFamily.single KrausFamily.schrodingerAction
            simp
  heisenberg_eq_kraus := by
    intro A
    have hzero := C.dynamicsAdapter.heisenbergObservable_zero N A
    calc
      C.heisenbergChannel (EvolutionApproxAxis.zero N) A = A := hzero
      _ = (KrausFamily.identity C).heisenbergAction A := by
            unfold KrausFamily.identity KrausFamily.single KrausFamily.heisenbergAction
            simp

def comp (P₂ P₁ : AlgebraicChannelPackage C) : AlgebraicChannelPackage C :=
  ofKrausFamily ((P₂.krausFamily).comp P₁.krausFamily)

theorem identity_schrodinger (C : ChannelSeedStrong Cell T)
    (ρ : C.execDensityOperator) :
    (identity C).schrodinger ρ = ρ := by
  unfold identity ofKrausFamily KrausFamily.identity KrausFamily.single KrausFamily.schrodingerAction
  simp

theorem identity_heisenberg (C : ChannelSeedStrong Cell T)
    (A : C.execObservable) :
    (identity C).heisenberg A = A := by
  unfold identity ofKrausFamily KrausFamily.identity KrausFamily.single KrausFamily.heisenbergAction
  simp

theorem identity_isTracePreserving (C : ChannelSeedStrong Cell T) :
    (identity C).isTracePreserving := by
  intro ρ
  rw [identity_schrodinger]

theorem zeroTime_schrodinger (C : ChannelSeedStrong Cell T) (N : Nat)
    (ρ : C.execDensityOperator) :
    (zeroTime C N).schrodinger ρ = ρ := by
  exact C.dynamicsAdapter.schrodingerDensity_zero N ρ

theorem zeroTime_heisenberg (C : ChannelSeedStrong Cell T) (N : Nat)
    (A : C.execObservable) :
    (zeroTime C N).heisenberg A = A := by
  exact C.dynamicsAdapter.heisenbergObservable_zero N A

theorem zeroTime_isTracePreserving (C : ChannelSeedStrong Cell T) (N : Nat) :
    (zeroTime C N).isTracePreserving := by
  intro ρ
  rw [zeroTime_schrodinger]

theorem unitarySingleKraus_isTracePreserving (U : UnitarySingleKrausSeed C) :
    (ofUnitarySingleKraus U).isTracePreserving := by
  intro ρ
  exact U.schrodinger_tracePreserving ρ

theorem comp_schrodinger (P₂ P₁ : AlgebraicChannelPackage C)
    (ρ : C.execDensityOperator) :
    (comp P₂ P₁).schrodinger ρ = P₂.schrodinger (P₁.schrodinger ρ) := by
  rw [P₂.schrodinger_eq_kraus (P₁.schrodinger ρ)]
  rw [P₁.schrodinger_eq_kraus ρ]
  unfold comp ofKrausFamily KrausFamily.comp KrausFamily.schrodingerAction
  calc
    ∑ x : P₂.krausFamily.Index × P₁.krausFamily.Index,
        (P₂.krausFamily.op x.1 * P₁.krausFamily.op x.2) * ρ *
          star (P₂.krausFamily.op x.1 * P₁.krausFamily.op x.2)
      = ∑ a : P₂.krausFamily.Index, ∑ b : P₁.krausFamily.Index,
          (P₂.krausFamily.op a * P₁.krausFamily.op b) * ρ *
            star (P₂.krausFamily.op a * P₁.krausFamily.op b) := by
          rw [← Finset.univ_product_univ]
          exact
            (Finset.sum_product'
              (s := (Finset.univ : Finset P₂.krausFamily.Index))
              (t := (Finset.univ : Finset P₁.krausFamily.Index))
              (f := fun a b =>
                (P₂.krausFamily.op a * P₁.krausFamily.op b) * ρ *
                  star (P₂.krausFamily.op a * P₁.krausFamily.op b)))
    _ = ∑ a : P₂.krausFamily.Index, ∑ b : P₁.krausFamily.Index,
          ((P₂.krausFamily.op a * (P₁.krausFamily.op b * ρ * star (P₁.krausFamily.op b))) *
            star (P₂.krausFamily.op a)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          refine Finset.sum_congr rfl ?_
          intro b hb
          simp [Matrix.mul_assoc, Matrix.star_mul]
    _ = ∑ a : P₂.krausFamily.Index,
          ((P₂.krausFamily.op a *
              ∑ b : P₁.krausFamily.Index,
                P₁.krausFamily.op b * ρ * star (P₁.krausFamily.op b)) *
            star (P₂.krausFamily.op a)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [← Finset.sum_mul]
          rw [← Finset.mul_sum]
    _ = ∑ a : P₂.krausFamily.Index,
          P₂.krausFamily.op a * (P₁.krausFamily.schrodingerAction ρ) *
            star (P₂.krausFamily.op a) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          unfold KrausFamily.schrodingerAction
          simp [Matrix.mul_assoc]
    _ = P₂.krausFamily.schrodingerAction (P₁.krausFamily.schrodingerAction ρ) := by
          rfl

theorem comp_heisenberg (P₂ P₁ : AlgebraicChannelPackage C)
    (A : C.execObservable) :
    (comp P₂ P₁).heisenberg A = P₁.heisenberg (P₂.heisenberg A) := by
  rw [P₁.heisenberg_eq_kraus (P₂.heisenberg A)]
  rw [P₂.heisenberg_eq_kraus A]
  unfold comp ofKrausFamily KrausFamily.comp KrausFamily.heisenbergAction
  calc
    ∑ x : P₂.krausFamily.Index × P₁.krausFamily.Index,
        star (P₂.krausFamily.op x.1 * P₁.krausFamily.op x.2) * A *
          (P₂.krausFamily.op x.1 * P₁.krausFamily.op x.2)
      = ∑ b : P₁.krausFamily.Index, ∑ a : P₂.krausFamily.Index,
          star (P₂.krausFamily.op a * P₁.krausFamily.op b) * A *
            (P₂.krausFamily.op a * P₁.krausFamily.op b) := by
          rw [← Finset.univ_product_univ]
          exact
            (Finset.sum_product_right'
              (s := (Finset.univ : Finset P₂.krausFamily.Index))
              (t := (Finset.univ : Finset P₁.krausFamily.Index))
              (f := fun a b =>
                star (P₂.krausFamily.op a * P₁.krausFamily.op b) * A *
                  (P₂.krausFamily.op a * P₁.krausFamily.op b)))
    _ = ∑ b : P₁.krausFamily.Index, ∑ a : P₂.krausFamily.Index,
          (star (P₁.krausFamily.op b) *
            (star (P₂.krausFamily.op a) * A * P₂.krausFamily.op a)) *
            P₁.krausFamily.op b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [Matrix.mul_assoc, Matrix.star_mul]
    _ = ∑ b : P₁.krausFamily.Index,
          (star (P₁.krausFamily.op b) *
            ∑ a : P₂.krausFamily.Index,
              star (P₂.krausFamily.op a) * A * P₂.krausFamily.op a) *
            P₁.krausFamily.op b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [← Finset.sum_mul]
          rw [← Finset.mul_sum]
    _ = ∑ b : P₁.krausFamily.Index,
          star (P₁.krausFamily.op b) * (P₂.krausFamily.heisenbergAction A) *
            P₁.krausFamily.op b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          unfold KrausFamily.heisenbergAction
          simp [Matrix.mul_assoc]
    _ = P₁.krausFamily.heisenbergAction (P₂.krausFamily.heisenbergAction A) := by
          rfl

theorem comp_zeroTime_left_schrodinger (P : AlgebraicChannelPackage C) (N : Nat)
    (ρ : C.execDensityOperator) :
    (comp P (zeroTime C N)).schrodinger ρ = P.schrodinger ρ := by
  rw [comp_schrodinger]
  rw [zeroTime_schrodinger]

theorem comp_zeroTime_right_schrodinger (P : AlgebraicChannelPackage C) (N : Nat)
    (ρ : C.execDensityOperator) :
    (comp (zeroTime C N) P).schrodinger ρ = P.schrodinger ρ := by
  rw [comp_schrodinger]
  rw [zeroTime_schrodinger]

theorem comp_zeroTime_left_heisenberg (P : AlgebraicChannelPackage C) (N : Nat)
    (A : C.execObservable) :
    (comp P (zeroTime C N)).heisenberg A = P.heisenberg A := by
  rw [comp_heisenberg]
  rw [zeroTime_heisenberg]

theorem comp_zeroTime_right_heisenberg (P : AlgebraicChannelPackage C) (N : Nat)
    (A : C.execObservable) :
    (comp (zeroTime C N) P).heisenberg A = P.heisenberg A := by
  rw [comp_heisenberg]
  rw [zeroTime_heisenberg]

end AlgebraicChannelPackage

structure MirrorAlgebraicChannelPackage (C : ChannelSeedStrong Cell T) (t : ℝ) where
  schrodinger : C.mirrorDensityOperator → C.mirrorDensityOperator
  heisenberg : C.mirrorObservable → C.mirrorObservable

noncomputable def mirrorSchrodingerChannel (C : ChannelSeedStrong Cell T)
    (t : ℝ) : C.mirrorDensityOperator → C.mirrorDensityOperator :=
  C.dynamicsAdapter.mirrorSchrodingerDensity t

noncomputable def mirrorHeisenbergChannel (C : ChannelSeedStrong Cell T)
    (t : ℝ) : C.mirrorObservable → C.mirrorObservable :=
  C.dynamicsAdapter.mirrorHeisenbergObservable t

noncomputable def mirrorChannelPackage (C : ChannelSeedStrong Cell T) (t : ℝ) :
    MirrorAlgebraicChannelPackage C t where
  schrodinger := C.mirrorSchrodingerChannel t
  heisenberg := C.mirrorHeisenbergChannel t

noncomputable def mirrorChannelCompose (C : ChannelSeedStrong Cell T)
    (t s : ℝ) (ρ : C.mirrorDensityOperator) :
    C.mirrorDensityOperator :=
  C.mirrorSchrodingerChannel t (C.mirrorSchrodingerChannel s ρ)

theorem mirrorSchrodingerChannel_zero (C : ChannelSeedStrong Cell T)
    (ρ : C.mirrorDensityOperator) :
    C.mirrorSchrodingerChannel 0 ρ = ρ := by
  exact C.dynamicsAdapter.mirrorSchrodingerDensity_zero ρ

theorem mirrorHeisenbergChannel_zero (C : ChannelSeedStrong Cell T)
    (A : C.mirrorObservable) :
    C.mirrorHeisenbergChannel 0 A = A := by
  exact C.dynamicsAdapter.mirrorHeisenbergObservable_zero A

theorem mirrorChannelCompose_zero_left (C : ChannelSeedStrong Cell T)
    (t : ℝ) (ρ : C.mirrorDensityOperator) :
    C.mirrorChannelCompose 0 t ρ = C.mirrorSchrodingerChannel t ρ := by
  unfold mirrorChannelCompose
  rw [C.mirrorSchrodingerChannel_zero]

theorem mirrorChannelPackage_zero (C : ChannelSeedStrong Cell T) :
    (C.mirrorChannelPackage 0).schrodinger = C.mirrorSchrodingerChannel 0 ∧
      (C.mirrorChannelPackage 0).heisenberg = C.mirrorHeisenbergChannel 0 := by
  constructor
  · rfl
  · rfl

end ChannelSeedStrong

namespace StrengtheningS9

open CNNA.PillarA.Finite.StrengtheningS5

def referenceFullChannelSeed (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b) :
    ChannelSeedStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ChannelSeedStrong.ofDynamicsAdapter (referenceFullDynamicsAdapter b p wp)

def variationFullChannelSeed (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) :
    ChannelSeedStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ChannelSeedStrong.ofDynamicsAdapter (variationFullDynamicsAdapter β p wp)

end StrengtheningS9

end CNNA.PillarA.Finite
