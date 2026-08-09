import CNNAProofs.P001.S03_FiniteLinearWellPosedness

/-!
# P001 — S07 response well-definedness

This module closes the response-existence and response-witness-independence
layer after finite interior well-posedness.

The proof chain is deliberately short:

1. transport the unique proof-layer rational solve through the already verified
   C006 semantic bridge;
2. inhabit the existing Core predicate `IsInteriorAdmissible`;
3. invoke the Core response-existence theorem;
4. invoke the Core value-uniqueness theorem for arbitrary raw exact-fraction
   response representatives;
5. expose the proof-layer rational value represented by every C006 response.

No inverse, determinant, Schur-complement API, new response operator,
regularization, symmetrization, pseudoinverse, or selected solver is introduced.
The directed Laplacian sign structure and strict distinguished-port positivity
remain separate later obligations.
-/

namespace CNNAProofs.P001

open CNNA.Derivation.S01_PrimitiveResponseCoupledFiniteProvenance.S03_RecurrentPreBirthMeasurementAndSteering
open BirthLocalSchurDtnPrimitive

/-- Entrywise exact-fraction value equality induces equality of the associated
    proof-layer rational matrices. -/
theorem exactMatrixValue_eq_of_matrixSameValue {rows cols : Nat}
    {left right : ExactFractionMatrix rows cols}
    (hValue : MatrixSameValue left right) :
    exactMatrixValue left = exactMatrixValue right := by
  apply Matrix.ext
  intro row column
  exact sameValue_iff_exactFractionValue_eq.mp (hValue row column)

/-- Finite rational well-posedness, transported through the exact semantic
    bridge, directly inhabits C006's existing admissibility predicate. -/
theorem c006InteriorAdmissible {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    IsInteriorAdmissible blocks := by
  obtain ⟨solve, hMathlibSolve⟩ := interiorSolveExists blocks hKernel
  have hCoreSolve : IsInteriorSolve blocks solve :=
    (interiorSolveAgreement blocks solve).mpr hMathlibSolve
  refine ⟨solve, hCoreSolve, ?_⟩
  intro other hOtherCoreSolve
  have hOtherMathlibSolve : IsMathlibInteriorSolve blocks other :=
    (interiorSolveAgreement blocks other).mp hOtherCoreSolve
  exact interiorSolveUnique blocks hKernel other solve
    hOtherMathlibSolve hMathlibSolve

/-- C006 therefore has at least one exact Schur/DtN response representative. -/
theorem responseExists {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    ∃ response : ExactFractionMatrix boundary boundary,
      IsSchurDtnResponse blocks response :=
  response_exists_of_admissible blocks
    (c006InteriorAdmissible blocks hKernel)

/-- Every C006 response representative denotes the proof-layer rational response
    of one exact interior solve. -/
theorem responseRepresentativeAgreement {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (response : ExactFractionMatrix boundary boundary)
    (hResponse : IsSchurDtnResponse blocks response) :
    ∃ solve : RationalMatrix interior boundary,
      IsMathlibInteriorSolve blocks solve ∧
        exactMatrixValue response = mathlibResponseFromSolve blocks solve := by
  obtain ⟨solve, hCoreSolve, hResponseValue⟩ := hResponse
  refine ⟨solve, (interiorSolveAgreement blocks solve).mp hCoreSolve, ?_⟩
  calc
    exactMatrixValue response =
        exactMatrixValue (responseFromSolve blocks solve) :=
      exactMatrixValue_eq_of_matrixSameValue hResponseValue
    _ = mathlibResponseFromSolve blocks solve :=
      responseValueAgreement blocks solve

/-- The exact C006 response value is independent of both the interior solve
    witness and the chosen positive-denominator raw representative. -/
theorem responseWitnessIndependent {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    ResponseWitnessIndependent blocks := by
  intro left right hLeft hRight
  exact response_unique_of_admissible blocks
    (c006InteriorAdmissible blocks hKernel)
    left right hLeft hRight

/-- S07 packages exactly the three existing response-well-definedness contracts;
    sign closure and strict port positivity are intentionally absent. -/
theorem responseWellDefined {boundary interior : Nat}
    (blocks : OrderedSchurBlocks boundary interior)
    (hKernel : InteriorKernelTrivial blocks) :
    IsInteriorAdmissible blocks ∧
      (∃ response : ExactFractionMatrix boundary boundary,
        IsSchurDtnResponse blocks response) ∧
      ResponseWitnessIndependent blocks :=
  ⟨c006InteriorAdmissible blocks hKernel,
    ⟨responseExists blocks hKernel,
      responseWitnessIndependent blocks hKernel⟩⟩

end CNNAProofs.P001
