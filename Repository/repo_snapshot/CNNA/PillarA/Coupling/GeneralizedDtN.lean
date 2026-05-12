import CNNA.PillarA.Sectors.SectorSplit
import CNNA.PillarA.DtN.DtN

set_option autoImplicit false

namespace CNNA.PillarA.Coupling

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors

universe u

inductive CoupledSectorKind where
  | bright
  | interface
  | dark
  deriving DecidableEq, Repr

structure GeneralizedDtNStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  binary : DtNStrong Cell T
  split : SectorSplitStrong Cell T
  binary_eq_split_dtn : binary = split.dtn

abbrev GeneralizedDtNStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  GeneralizedDtNStrong (Cell := Cell) T

namespace GeneralizedDtNStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (G H : GeneralizedDtNStrong Cell T)
    (hbinary : G.binary = H.binary)
    (hsplit : G.split = H.split) :
    G = H := by
  cases G with
  | mk binaryG splitG proofG =>
    cases H with
    | mk binaryH splitH proofH =>
      cases hbinary
      cases hsplit
      have hproof : proofG = proofH := Subsingleton.elim _ _
      cases hproof
      rfl

def cast (h : T = U) (G : GeneralizedDtNStrong Cell T) :
    GeneralizedDtNStrong Cell U := by
  cases h
  exact G

theorem cast_rfl (G : GeneralizedDtNStrong Cell T) :
    cast (Cell := Cell) rfl G = G := by
  rfl

def castSquareMatrix {α β : Type _} (h : α = β)
    (A : Matrix α α ℝ) : Matrix β β ℝ := by
  cases h
  exact A

def ofBinaryAndSplit
    (K : DtNStrong Cell T)
    (S : SectorSplitStrong Cell T)
    (hK : K = S.dtn) :
    GeneralizedDtNStrong Cell T where
  binary := K
  split := S
  binary_eq_split_dtn := hK

def ofSectorSplit (S : SectorSplitStrong Cell T) :
    GeneralizedDtNStrong Cell T :=
  ofBinaryAndSplit S.dtn S rfl

theorem ofSectorSplit_binary (S : SectorSplitStrong Cell T) :
    (ofSectorSplit S).binary = S.dtn := by
  rfl

theorem ofSectorSplit_split (S : SectorSplitStrong Cell T) :
    (ofSectorSplit S).split = S := by
  rfl

def rawBinary (G : GeneralizedDtNStrong Cell T) : DtNStrong Cell T :=
  G.binary

def stabilizedBinary (G : GeneralizedDtNStrong Cell T) : DtNStabilizedStrong Cell T :=
  G.split.stabilized

abbrev boundaryVertex (G : GeneralizedDtNStrong Cell T) :=
  G.rawBinary.boundaryVertex

abbrev rawBoundaryVertex (G : GeneralizedDtNStrong Cell T) :=
  G.rawBinary.boundaryVertex

abbrev stabilizedBoundaryVertex (G : GeneralizedDtNStrong Cell T) :=
  G.stabilizedBinary.boundaryVertex

abbrev boundaryPotential (G : GeneralizedDtNStrong Cell T) :=
  G.boundaryVertex → ℝ

abbrev rawBoundaryPotential (G : GeneralizedDtNStrong Cell T) :=
  G.rawBoundaryVertex → ℝ

abbrev stabilizedBoundaryPotential (G : GeneralizedDtNStrong Cell T) :=
  G.stabilizedBoundaryVertex → ℝ

def dirichlet (G : GeneralizedDtNStrong Cell T) : DirichletLaplacianStrong Cell T :=
  G.rawBinary.source

def approximant (G : GeneralizedDtNStrong Cell T) : ApproximantStrong Cell T :=
  G.dirichlet.source

def cutoff (_ : GeneralizedDtNStrong Cell T) : Nat :=
  T.cutoff

def rawBoundaryOperator (G : GeneralizedDtNStrong Cell T) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawBinary.boundaryOperator

def symmetrizedBoundaryOperator (G : GeneralizedDtNStrong Cell T) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawBoundaryOperator + Matrix.transpose G.rawBoundaryOperator

def stabilizedBoundaryOperator (G : GeneralizedDtNStrong Cell T) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawBoundaryOperator +
    G.stabilizedBinary.regularizationShift •
      (1 : Matrix G.boundaryVertex G.boundaryVertex ℝ)

def boundaryOperator (G : GeneralizedDtNStrong Cell T) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawBoundaryOperator

def sectorRegion (G : GeneralizedDtNStrong Cell T) : CoupledSectorKind → RegionCore Cell T
  | .bright => G.split.brightRegion
  | .interface => G.split.interfaceRegion
  | .dark => G.split.darkRegion

def sectorBoundaryPorts (G : GeneralizedDtNStrong Cell T) :
    CoupledSectorKind → BoundaryPorts Cell T
  | .bright => G.split.brightBoundaryPorts
  | .interface => G.split.interfaceBoundaryPorts
  | .dark => G.split.darkBoundaryPorts

def regionCarrier (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : Finset (Cell L) :=
  (G.sectorRegion K).carrier L

def boundaryCarrier (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : Finset (Cell L) :=
  (G.sectorBoundaryPorts K).ports L

def interiorCarrier (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : Finset (Cell L) :=
  (G.sectorBoundaryPorts K).interiorCarrier L

def sectorCarrier (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : Finset (Cell L) :=
  match K with
  | .bright => G.split.brightSectorCarrier L
  | .interface => G.split.interfaceCarrier L
  | .dark => G.split.darkSectorCarrier L

def regionSlice (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : LayerSlice Cell :=
  (G.sectorRegion K).slice L

def boundarySlice (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : BoundarySlice Cell :=
  (G.sectorBoundaryPorts K).slice L

def interiorSlice (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := G.interiorCarrier K L }

def noOuterEnvironment (G : GeneralizedDtNStrong Cell T) : Prop :=
  G.split.noOuterEnvironment

def hasOuterEnvironment (G : GeneralizedDtNStrong Cell T) : Prop :=
  G.split.hasOuterEnvironment

theorem binary_eq_split_dtn' (G : GeneralizedDtNStrong Cell T) :
    G.binary = G.split.dtn := by
  exact G.binary_eq_split_dtn

theorem rawBinary_eq_binary (G : GeneralizedDtNStrong Cell T) :
    G.rawBinary = G.binary := by
  rfl

theorem rawBinary_eq_split_dtn (G : GeneralizedDtNStrong Cell T) :
    G.rawBinary = G.split.dtn := by
  exact G.binary_eq_split_dtn

theorem stabilizedBinary_eq_split_stabilized (G : GeneralizedDtNStrong Cell T) :
    G.stabilizedBinary = G.split.stabilized := by
  rfl

theorem stabilizedBinary_source_eq_rawBinary (G : GeneralizedDtNStrong Cell T) :
    G.stabilizedBinary.source = G.rawBinary := by
  change G.split.dtn = G.rawBinary
  rw [G.rawBinary_eq_split_dtn]

theorem boundaryOperator_eq_rawBoundaryOperator (G : GeneralizedDtNStrong Cell T) :
    G.boundaryOperator = G.rawBoundaryOperator := by
  rfl

theorem rawBoundaryOperator_eq_binary_boundaryOperator (G : GeneralizedDtNStrong Cell T) :
    G.rawBoundaryOperator = G.binary.boundaryOperator := by
  rfl

theorem symmetrizedBoundaryOperator_eq_formula (G : GeneralizedDtNStrong Cell T) :
    G.symmetrizedBoundaryOperator =
      G.rawBoundaryOperator + Matrix.transpose G.rawBoundaryOperator := by
  rfl

theorem stabilizedBoundaryOperator_eq_formula (G : GeneralizedDtNStrong Cell T) :
    G.stabilizedBoundaryOperator =
      G.rawBoundaryOperator +
        G.stabilizedBinary.regularizationShift •
          (1 : Matrix G.boundaryVertex G.boundaryVertex ℝ) := by
  rfl

theorem dirichlet_eq_split_dirichlet (G : GeneralizedDtNStrong Cell T) :
    G.dirichlet = G.split.dirichlet := by
  show G.rawBinary.source = G.split.dtn.source
  rw [rawBinary_eq_split_dtn]

theorem approximant_eq_split_approximant (G : GeneralizedDtNStrong Cell T) :
    G.approximant = G.split.approximant := by
  show G.rawBinary.source.source = G.split.dtn.source.source
  rw [rawBinary_eq_split_dtn]

theorem sectorRegion_bright (G : GeneralizedDtNStrong Cell T) :
    G.sectorRegion .bright = G.split.brightRegion := by
  rfl

theorem sectorRegion_interface (G : GeneralizedDtNStrong Cell T) :
    G.sectorRegion .interface = G.split.interfaceRegion := by
  rfl

theorem sectorRegion_dark (G : GeneralizedDtNStrong Cell T) :
    G.sectorRegion .dark = G.split.darkRegion := by
  rfl

theorem sectorBoundaryPorts_bright (G : GeneralizedDtNStrong Cell T) :
    G.sectorBoundaryPorts .bright = G.split.brightBoundaryPorts := by
  rfl

theorem sectorBoundaryPorts_interface (G : GeneralizedDtNStrong Cell T) :
    G.sectorBoundaryPorts .interface = G.split.interfaceBoundaryPorts := by
  rfl

theorem sectorBoundaryPorts_dark (G : GeneralizedDtNStrong Cell T) :
    G.sectorBoundaryPorts .dark = G.split.darkBoundaryPorts := by
  rfl

def boundaryVertexInSector (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (v : G.boundaryVertex) : Prop :=
  v.cell ∈ G.boundaryCarrier K v.level

instance decidableBoundaryVertexInSector
    (G : GeneralizedDtNStrong Cell T) (K : CoupledSectorKind) :
    DecidablePred (G.boundaryVertexInSector K) := by
  intro v
  unfold GeneralizedDtNStrong.boundaryVertexInSector
  infer_instance

abbrev SectorBoundaryVertex (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) :=
  {v : G.boundaryVertex // G.boundaryVertexInSector K v}

abbrev SectorBoundaryPotential (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) :=
  G.SectorBoundaryVertex K → ℝ

def boundaryTrace (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) : Finset G.boundaryVertex :=
  Finset.univ.filter (G.boundaryVertexInSector K)

theorem mem_boundaryTrace_iff (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (v : G.boundaryVertex) :
    v ∈ G.boundaryTrace K ↔ G.boundaryVertexInSector K v := by
  constructor
  · intro hv
    exact (Finset.mem_filter.mp hv).2
  · intro hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩

def rawRestrictedBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (G.SectorBoundaryVertex src) (G.SectorBoundaryVertex dst) ℝ :=
  fun i j => G.rawBoundaryOperator i.1 j.1

def stabilizedRestrictedBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (G.SectorBoundaryVertex src) (G.SectorBoundaryVertex dst) ℝ :=
  fun i j => G.stabilizedBoundaryOperator i.1 j.1

def restrictedBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (G.SectorBoundaryVertex src) (G.SectorBoundaryVertex dst) ℝ :=
  G.rawRestrictedBlock src dst

def restrictToSector (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (φ : G.boundaryPotential) :
    G.SectorBoundaryPotential K :=
  fun v => φ v.1

def glueFromSector (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (φ : G.SectorBoundaryPotential K) :
    G.boundaryPotential :=
  fun v =>
    if hv : G.boundaryVertexInSector K v then
      φ ⟨v, hv⟩
    else
      0

theorem rawRestrictedBlock_apply (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : G.SectorBoundaryVertex src)
    (j : G.SectorBoundaryVertex dst) :
    G.rawRestrictedBlock src dst i j = G.rawBoundaryOperator i.1 j.1 := by
  rfl

theorem stabilizedRestrictedBlock_apply (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : G.SectorBoundaryVertex src)
    (j : G.SectorBoundaryVertex dst) :
    G.stabilizedRestrictedBlock src dst i j = G.stabilizedBoundaryOperator i.1 j.1 := by
  rfl

theorem restrictedBlock_apply (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : G.SectorBoundaryVertex src)
    (j : G.SectorBoundaryVertex dst) :
    G.restrictedBlock src dst i j = G.boundaryOperator i.1 j.1 := by
  rfl

theorem restrictToSector_glueFromSector (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (φ : G.SectorBoundaryPotential K) :
    G.restrictToSector K (G.glueFromSector K φ) = φ := by
  funext v
  cases v with
  | mk v hv =>
      simp [restrictToSector, glueFromSector, hv]

theorem glueFromSector_apply_of_mem (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (φ : G.SectorBoundaryPotential K)
    {v : G.boundaryVertex} (hv : G.boundaryVertexInSector K v) :
    G.glueFromSector K φ v = φ ⟨v, hv⟩ := by
  simp [glueFromSector, hv]

theorem glueFromSector_apply_of_not_mem (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (φ : G.SectorBoundaryPotential K)
    {v : G.boundaryVertex} (hv : ¬ G.boundaryVertexInSector K v) :
    G.glueFromSector K φ v = 0 := by
  simp [glueFromSector, hv]

theorem regionCarrier_subset (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) :
    G.regionCarrier K L ⊆ T.carrier L := by
  cases K with
  | bright =>
      exact G.split.brightPatch.carrier_subset L
  | interface =>
      exact G.split.interface_subset_ambient L
  | dark =>
      exact G.split.darkFamily.carrier_subset L

theorem sectorBoundaryPorts_region_eq_sectorRegion (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) :
    (G.sectorBoundaryPorts K).region = G.sectorRegion K := by
  cases K with
  | bright =>
      change G.split.brightBoundaryPorts.region = G.split.brightRegion
      rw [G.split.brightBoundaryPorts_eq_patch_boundaryPorts,
        G.split.brightRegion_eq_patch_region]
      exact Eq.symm (ApproximantStrong.region_eq G.split.brightPatch.approximant)
  | interface =>
      exact G.split.interfaceBoundaryPorts_region
  | dark =>
      change G.split.darkBoundaryPorts.region = G.split.darkRegion
      rw [G.split.darkBoundaryPorts_eq_source_boundaryPorts,
        G.split.darkRegion_eq_source_region]
      exact G.split.darkFamily.boundaryPorts_region

theorem boundaryCarrier_subset_regionCarrier (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) :
    G.boundaryCarrier K L ⊆ G.regionCarrier K L := by
  rw [regionCarrier, ← G.sectorBoundaryPorts_region_eq_sectorRegion K]
  exact BoundaryPorts.ports_subset_carrier (G.sectorBoundaryPorts K) L

theorem interiorCarrier_subset_regionCarrier (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) (L : Nat) :
    G.interiorCarrier K L ⊆ G.regionCarrier K L := by
  rw [regionCarrier, ← G.sectorBoundaryPorts_region_eq_sectorRegion K]
  exact BoundaryPorts.interiorCarrier_subset_carrier (G.sectorBoundaryPorts K) L

theorem mem_brightBoundaryCarrier (G : GeneralizedDtNStrong Cell T)
    (v : G.boundaryVertex) :
    v.cell ∈ G.boundaryCarrier .bright v.level := by
  have hv : v.cell ∈ G.approximant.ports v.level :=
    v.mem_ports
  rw [G.approximant_eq_split_approximant] at hv
  change v.cell ∈ G.split.brightPatch.boundaryCarrier v.level
  rw [G.split.brightPatch.boundaryCarrier_eq_approximant_ports]
  exact hv

theorem bright_boundaryVertexInSector (G : GeneralizedDtNStrong Cell T)
    (v : G.boundaryVertex) :
    G.boundaryVertexInSector .bright v := by
  exact G.mem_brightBoundaryCarrier v

theorem brightBoundaryTrace_eq_univ (G : GeneralizedDtNStrong Cell T) :
    G.boundaryTrace .bright = Finset.univ := by
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    have hv : G.boundaryVertexInSector .bright v :=
      G.bright_boundaryVertexInSector v
    exact (G.mem_boundaryTrace_iff .bright v).2 hv

def rawKernelBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  fun i j =>
    if G.boundaryVertexInSector src i then
      if G.boundaryVertexInSector dst j then G.rawBoundaryOperator i j else 0
    else 0

def stabilizedKernelBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  fun i j =>
    if G.boundaryVertexInSector src i then
      if G.boundaryVertexInSector dst j then G.stabilizedBoundaryOperator i j else 0
    else 0

def kernelBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawKernelBlock src dst

def rawDiagonalBlock (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawKernelBlock K K

def stabilizedDiagonalBlock (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.stabilizedKernelBlock K K

def diagonalBlock (G : GeneralizedDtNStrong Cell T)
    (K : CoupledSectorKind) :
    Matrix G.boundaryVertex G.boundaryVertex ℝ :=
  G.rawDiagonalBlock K

def rawCoupledFlux (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (φ : G.boundaryPotential) :
    G.boundaryPotential :=
  (G.rawKernelBlock src dst).mulVec φ

def stabilizedCoupledFlux (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (φ : G.boundaryPotential) :
    G.boundaryPotential :=
  (G.stabilizedKernelBlock src dst).mulVec φ

def coupledFlux (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (φ : G.boundaryPotential) :
    G.boundaryPotential :=
  G.rawCoupledFlux src dst φ

theorem rawKernelBlock_eq_zero_of_not_mem_src
    (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    {i j : G.boundaryVertex}
    (hi : ¬ G.boundaryVertexInSector src i) :
    G.rawKernelBlock src dst i j = 0 := by
  simp [rawKernelBlock, hi]

theorem rawKernelBlock_eq_zero_of_not_mem_dst
    (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    {i j : G.boundaryVertex}
    (hi : G.boundaryVertexInSector src i)
    (hj : ¬ G.boundaryVertexInSector dst j) :
    G.rawKernelBlock src dst i j = 0 := by
  simp [rawKernelBlock, hi, hj]

theorem stabilizedKernelBlock_eq_zero_of_not_mem_src
    (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    {i j : G.boundaryVertex}
    (hi : ¬ G.boundaryVertexInSector src i) :
    G.stabilizedKernelBlock src dst i j = 0 := by
  simp [stabilizedKernelBlock, hi]

theorem stabilizedKernelBlock_eq_zero_of_not_mem_dst
    (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    {i j : G.boundaryVertex}
    (hi : G.boundaryVertexInSector src i)
    (hj : ¬ G.boundaryVertexInSector dst j) :
    G.stabilizedKernelBlock src dst i j = 0 := by
  simp [stabilizedKernelBlock, hi, hj]

theorem kernelBlock_eq_zero_of_not_mem_src
    (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    {i j : G.boundaryVertex}
    (hi : ¬ G.boundaryVertexInSector src i) :
    G.kernelBlock src dst i j = 0 := by
  simp [kernelBlock, rawKernelBlock, hi]

theorem kernelBlock_eq_zero_of_not_mem_dst
    (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    {i j : G.boundaryVertex}
    (hi : G.boundaryVertexInSector src i)
    (hj : ¬ G.boundaryVertexInSector dst j) :
    G.kernelBlock src dst i j = 0 := by
  simp [kernelBlock, rawKernelBlock, hi, hj]

theorem rawBrightBrightBlock_eq_rawBoundaryOperator (G : GeneralizedDtNStrong Cell T) :
    G.rawKernelBlock .bright .bright = G.rawBoundaryOperator := by
  ext i j
  have hi : G.boundaryVertexInSector .bright i :=
    G.bright_boundaryVertexInSector i
  have hj : G.boundaryVertexInSector .bright j :=
    G.bright_boundaryVertexInSector j
  simp [rawKernelBlock, hi, hj]

theorem stabilizedBrightBrightBlock_eq_stabilizedBoundaryOperator
    (G : GeneralizedDtNStrong Cell T) :
    G.stabilizedKernelBlock .bright .bright = G.stabilizedBoundaryOperator := by
  ext i j
  have hi : G.boundaryVertexInSector .bright i :=
    G.bright_boundaryVertexInSector i
  have hj : G.boundaryVertexInSector .bright j :=
    G.bright_boundaryVertexInSector j
  simp [stabilizedKernelBlock, hi, hj]

theorem brightBrightBlock_eq_boundaryOperator (G : GeneralizedDtNStrong Cell T) :
    G.kernelBlock .bright .bright = G.boundaryOperator := by
  calc
    G.kernelBlock .bright .bright = G.rawBoundaryOperator := G.rawBrightBrightBlock_eq_rawBoundaryOperator
    _ = G.boundaryOperator := by rw [G.boundaryOperator_eq_rawBoundaryOperator]

theorem rawRestrictedBlock_eq_rawKernelBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : G.SectorBoundaryVertex src)
    (j : G.SectorBoundaryVertex dst) :
    G.rawRestrictedBlock src dst i j = G.rawKernelBlock src dst i.1 j.1 := by
  have hi : G.boundaryVertexInSector src i.1 := i.2
  have hj : G.boundaryVertexInSector dst j.1 := j.2
  simp [rawRestrictedBlock, rawKernelBlock, hi, hj]

theorem stabilizedRestrictedBlock_eq_stabilizedKernelBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : G.SectorBoundaryVertex src)
    (j : G.SectorBoundaryVertex dst) :
    G.stabilizedRestrictedBlock src dst i j =
      G.stabilizedKernelBlock src dst i.1 j.1 := by
  have hi : G.boundaryVertexInSector src i.1 := i.2
  have hj : G.boundaryVertexInSector dst j.1 := j.2
  simp [stabilizedRestrictedBlock, stabilizedKernelBlock, hi, hj]

theorem restrictedBlock_eq_kernelBlock (G : GeneralizedDtNStrong Cell T)
    (src dst : CoupledSectorKind)
    (i : G.SectorBoundaryVertex src)
    (j : G.SectorBoundaryVertex dst) :
    G.restrictedBlock src dst i j = G.kernelBlock src dst i.1 j.1 := by
  have hi : G.boundaryVertexInSector src i.1 := i.2
  have hj : G.boundaryVertexInSector dst j.1 := j.2
  simp [restrictedBlock, kernelBlock, rawRestrictedBlock, rawKernelBlock, hi, hj]

end GeneralizedDtNStrong

namespace StrengtheningS7

open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6

private def generalizedFromStabilized
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (K : DtNStabilizedStrong Cell T) : GeneralizedDtNStrong Cell T :=
  GeneralizedDtNStrong.ofSectorSplit <|
    SectorSplitStrong.ofComplementSectorFamily <|
      ComplementSectorFamilyStrong.ofBranchPatch <|
        BranchPatchStrong.ofDtNStabilized K

def referenceFullGeneralizedDtN (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    : GeneralizedDtNStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  generalizedFromStabilized (referenceFullDtNStabilized b p wp rp)

def variationFullGeneralizedDtN (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    : GeneralizedDtNStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  generalizedFromStabilized (variationFullDtNStabilized β p wp rp)

end StrengtheningS7

end CNNA.PillarA.Coupling
