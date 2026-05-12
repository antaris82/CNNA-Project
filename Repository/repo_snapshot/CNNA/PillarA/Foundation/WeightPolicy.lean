import Mathlib.Data.Rat.Cast.Order
import CNNA.PillarA.Foundation.Determinism

set_option autoImplicit false

namespace CNNA.PillarA.Foundation

universe u v

structure ThermalAxis where
  beta : ℚ
  beta_pos : 0 < beta

namespace ThermalAxis

@[ext] theorem ext (Θ Ψ : ThermalAxis) (hbeta : Θ.beta = Ψ.beta) : Θ = Ψ := by
  cases Θ with
  | mk betaΘ beta_posΘ =>
    cases Ψ with
    | mk betaΨ beta_posΨ =>
      cases hbeta
      have hproof : beta_posΘ = beta_posΨ := by
        apply Subsingleton.elim
      cases hproof
      rfl

def betaReal (Θ : ThermalAxis) : ℝ :=
  Θ.beta

theorem betaReal_pos (Θ : ThermalAxis) : 0 < Θ.betaReal := by
  change (0 : ℝ) < (Θ.beta : ℝ)
  exact_mod_cast Θ.beta_pos

theorem betaReal_nonneg (Θ : ThermalAxis) : 0 ≤ Θ.betaReal := by
  exact le_of_lt Θ.betaReal_pos

def key : PolicyKey ThermalAxis ℚ where
  key := beta

instance instKeyFaithful : KeyFaithful key where
  key_injective := by
    intro Θ Ψ h
    exact ext Θ Ψ h

def reference (beta : ℚ) (hbeta : 0 < beta) : ThermalAxis where
  beta := beta
  beta_pos := hbeta

end ThermalAxis

structure WeightPolicy where
  thermal : ThermalAxis

namespace WeightPolicy

@[ext] theorem ext (P Q : WeightPolicy) (hthermal : P.thermal = Q.thermal) : P = Q := by
  cases P with
  | mk thermalP =>
    cases Q with
    | mk thermalQ =>
      cases hthermal
      rfl

def beta (P : WeightPolicy) : ℚ :=
  P.thermal.beta

def betaReal (P : WeightPolicy) : ℝ :=
  P.thermal.betaReal

theorem beta_pos (P : WeightPolicy) : 0 < P.beta :=
  P.thermal.beta_pos

theorem betaReal_pos (P : WeightPolicy) : 0 < P.betaReal :=
  P.thermal.betaReal_pos

theorem betaReal_nonneg (P : WeightPolicy) : 0 ≤ P.betaReal :=
  P.thermal.betaReal_nonneg

def constantWeightQ (P : WeightPolicy) : ℚ :=
  P.beta

def constantWeight {V : Type u} [DecidableEq V] (P : WeightPolicy) : V → V → ℝ :=
  fun i j => if i = j then 0 else P.betaReal

theorem constantWeight_self {V : Type u} [DecidableEq V]
    (P : WeightPolicy) (i : V) :
    P.constantWeight i i = 0 := by
  simp [constantWeight]

theorem constantWeight_of_ne {V : Type u} [DecidableEq V]
    (P : WeightPolicy) {i j : V} (hij : i ≠ j) :
    P.constantWeight i j = P.betaReal := by
  simp [constantWeight, hij]

theorem constantWeight_symm {V : Type u} [DecidableEq V]
    (P : WeightPolicy) (i j : V) :
    P.constantWeight i j = P.constantWeight j i := by
  by_cases hij : i = j
  · subst hij
    simp [constantWeight]
  · have hji : j ≠ i := by
      exact fun hji => hij hji.symm
    simp [constantWeight, hij, hji]

theorem constantWeight_nonneg {V : Type u} [DecidableEq V]
    (P : WeightPolicy) (i j : V) :
    0 ≤ P.constantWeight i j := by
  by_cases hij : i = j
  · subst hij
    simp [constantWeight]
  · simp [constantWeight, hij, P.betaReal_nonneg]

def key : PolicyKey WeightPolicy ℚ where
  key := beta

instance instKeyFaithful : KeyFaithful key where
  key_injective := by
    intro P Q h
    apply ext
    exact ThermalAxis.ext P.thermal Q.thermal h

def fromThermal (Θ : ThermalAxis) : WeightPolicy where
  thermal := Θ

def reference (beta : ℚ) (hbeta : 0 < beta) : WeightPolicy :=
  fromThermal (ThermalAxis.reference beta hbeta)

end WeightPolicy

end CNNA.PillarA.Foundation
