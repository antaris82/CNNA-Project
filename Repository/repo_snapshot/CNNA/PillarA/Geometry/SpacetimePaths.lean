import CNNA.PillarA.Geometry.Foliation

set_option autoImplicit false

namespace CNNA.PillarA.Geometry

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

section SpacetimePaths

variable {Cell : Nat → Type u} {Addr : Nat → Type v}
variable [SubstrateClass Cell] [AddressPresentation Cell Addr]

local notation "τ[" Cell "," Addr "]" =>
  foliationTime (Cell := Cell) (Addr := Addr)

local notation "Σ[" Cell "," Addr ";" n "]" =>
  foliationLayer (Cell := Cell) (Addr := Addr) n

abbrev Worldline := Nat → BundledAddress (Cell := Cell) (Addr := Addr)
abbrev WorldTube := Nat → Set (BundledAddress (Cell := Cell) (Addr := Addr))

def IsFoliationAdapted (γ : Worldline (Cell := Cell) (Addr := Addr)) : Prop :=
  ∀ n : Nat, γ n ∈ Σ[Cell, Addr; n]

def IsCausalChain (γ : Worldline (Cell := Cell) (Addr := Addr)) : Prop :=
  ∀ n : Nat, bundledPrefix (Cell := Cell) (Addr := Addr) (γ n) (γ (n + 1))

def IsOneStep
    (x y : BundledAddress (Cell := Cell) (Addr := Addr)) : Prop :=
  bundledPrefix (Cell := Cell) (Addr := Addr) x y ∧
    τ[Cell, Addr] y = τ[Cell, Addr] x + 1

def IsFoliationAdaptedTube (W : WorldTube (Cell := Cell) (Addr := Addr)) : Prop :=
  ∀ n : Nat, ∀ x : BundledAddress (Cell := Cell) (Addr := Addr),
    x ∈ W n → x ∈ Σ[Cell, Addr; n]

def IsCausalTube (W : WorldTube (Cell := Cell) (Addr := Addr)) : Prop :=
  ∀ n : Nat, ∀ x : BundledAddress (Cell := Cell) (Addr := Addr),
    x ∈ W n → ∃ y : BundledAddress (Cell := Cell) (Addr := Addr),
      y ∈ W (n + 1) ∧ bundledPrefix (Cell := Cell) (Addr := Addr) x y

theorem adapted_mem_layer
    (γ : Worldline (Cell := Cell) (Addr := Addr))
    (hγ : IsFoliationAdapted (Cell := Cell) (Addr := Addr) γ)
    (n : Nat) :
    γ n ∈ Σ[Cell, Addr; n] := by
  exact hγ n

theorem adapted_time
    (γ : Worldline (Cell := Cell) (Addr := Addr))
    (hγ : IsFoliationAdapted (Cell := Cell) (Addr := Addr) γ)
    (n : Nat) :
    τ[Cell, Addr] (γ n) = n := by
  exact foliationTime_eq_of_mem_layer (Cell := Cell) (Addr := Addr) (γ n) (hγ n)

theorem causal_time_mono
    (γ : Worldline (Cell := Cell) (Addr := Addr))
    (hγ : IsCausalChain (Cell := Cell) (Addr := Addr) γ)
    (n : Nat) :
    τ[Cell, Addr] (γ n) ≤ τ[Cell, Addr] (γ (n + 1)) := by
  exact bundledPrefix_time_mono (Cell := Cell) (Addr := Addr) (hγ n)

theorem adapted_and_causal_oneStep
    (γ : Worldline (Cell := Cell) (Addr := Addr))
    (hadapt : IsFoliationAdapted (Cell := Cell) (Addr := Addr) γ)
    (hcausal : IsCausalChain (Cell := Cell) (Addr := Addr) γ)
    (n : Nat) :
    IsOneStep (Cell := Cell) (Addr := Addr) (γ n) (γ (n + 1)) := by
  refine ⟨hcausal n, ?_⟩
  calc
    τ[Cell, Addr] (γ (n + 1)) = n + 1 := adapted_time (Cell := Cell) (Addr := Addr) γ hadapt (n + 1)
    _ = τ[Cell, Addr] (γ n) + 1 := by
      rw [adapted_time (Cell := Cell) (Addr := Addr) γ hadapt n]

theorem adaptedTube_mem_layer
    (W : WorldTube (Cell := Cell) (Addr := Addr))
    (hW : IsFoliationAdaptedTube (Cell := Cell) (Addr := Addr) W)
    (n : Nat) (x : BundledAddress (Cell := Cell) (Addr := Addr))
    (hx : x ∈ W n) :
    x ∈ Σ[Cell, Addr; n] := by
  exact hW n x hx

theorem adaptedTube_time
    (W : WorldTube (Cell := Cell) (Addr := Addr))
    (hW : IsFoliationAdaptedTube (Cell := Cell) (Addr := Addr) W)
    (n : Nat) (x : BundledAddress (Cell := Cell) (Addr := Addr))
    (hx : x ∈ W n) :
    τ[Cell, Addr] x = n := by
  exact foliationTime_eq_of_mem_layer (Cell := Cell) (Addr := Addr) x (hW n x hx)

theorem causalTube_time_mono
    (W : WorldTube (Cell := Cell) (Addr := Addr))
    (hW : IsCausalTube (Cell := Cell) (Addr := Addr) W)
    (n : Nat) (x : BundledAddress (Cell := Cell) (Addr := Addr))
    (hx : x ∈ W n) :
    ∃ y : BundledAddress (Cell := Cell) (Addr := Addr),
      y ∈ W (n + 1) ∧
      τ[Cell, Addr] x ≤ τ[Cell, Addr] y := by
  rcases hW n x hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, bundledPrefix_time_mono (Cell := Cell) (Addr := Addr) hxy⟩

end SpacetimePaths

end CNNA.PillarA.Geometry
