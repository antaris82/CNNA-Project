# Semantic signal plan export

This directory filters the dependency DAG through detected cross-module symbol references. It now combines exact qualified hits with conservative imported-alias and open-namespace heuristics.

- Nodes: **287**
- Signal edges: **394**
- Acyclic: **True**
- Sources: **55**
- Sinks: **60**
- Reduced edges: **303**

## Mainline

- Source: `CNNA.PillarA.Foundation.HermitianStructure`
- Sink: `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`
- Length: **65**
- Path: `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Foundation.ExecComplex` → `CNNA.PillarA.Foundation.MatrixNorms` → `CNNA.PillarA.Foundation.Interfaces` → `CNNA.PillarA.Foundation.Notation` → `CNNA.PillarA.ToC.Contract` → `CNNA.PillarA.ToC.Addressing` → `CNNA.PillarA.ToC.IdealAddressEquiv` → `CNNA.PillarA.ToC.ConcreteIdeal` → `CNNA.PillarA.ToC.Notation` → `CNNA.PillarA.Finite.CutSpec` → `CNNA.PillarA.Finite.RegionCore` → `CNNA.PillarA.Finite.BoundaryPorts` → `CNNA.PillarA.Finite.Approximant` → `CNNA.PillarA.Finite.DirichletLaplacian` → `CNNA.PillarA.DtN.DtN` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e` → `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus` → `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`

## Critical source→sink paths

- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window` (65 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Arithmetic.Notation` (51 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqSimultaneousSystem` (48 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Structural.CayleyDickson.S6Slot1AlternativeLaw` (41 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Outputs.A_to_CayleyDickson` (37 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.ProofObligationI.Completion` (37 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.ProofObligationII.Preparation` (37 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.ProofObligationIII.Preparation` (37 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge` (36 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Inputs.B_to_A` (33 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Inputs.C_to_A` (33 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Inputs.D_to_A` (33 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Inputs.E_to_A` (33 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Outputs.A_to_C` (29 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Outputs.A_to_D` (29 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Handoff.Outputs.A_to_E` (29 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Network.Notation` (25 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Sectors.Notation` (25 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Finite.Notation` (24 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Coupling.Notation` (23 nodes)

## Files

- `summary.json`: aggregated signal-plan export
- `signal_graph.dot`: forward signal graph
- `signal_graph_reduced.dot`: transitive reduction of the forward signal graph
- `dominators.json`: dominator sets and immediate dominators
- `source_sink_paths.json`: representative critical source→sink paths
- `mainline.json`: selected longest mainline path
- `layers.json`: topological signal layers
- `weighted_source_sink_paths.json`: confidence-weighted source→sink paths
- `weighted_mainline.json`: confidence-weighted mainline

## Scope note

This is still heuristic: it detects declarations, open namespaces and alias-like references syntactically. It is sharper than import-only analysis, but not a proof of semantic usage in Lean elaboration.
