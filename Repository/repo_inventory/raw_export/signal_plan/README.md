# Signal plan export

This directory interprets the import DAG as a forward signal graph: dependency modules feed the modules that import them.

- Nodes: **287**
- Signal edges: **724**
- Acyclic: **True**
- Sources: **7**
- Sinks: **7**
- Reduced edges: **375**

## Mainline

- Source: `CNNA.PillarA.Foundation.HermitianStructure`
- Sink: `CNNA.BuildAll`
- Length: **74**
- Path: `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA.Foundation.ExecComplex` → `CNNA.PillarA.Foundation.MatrixNorms` → `CNNA.PillarA.Foundation.Interfaces` → `CNNA.PillarA.Foundation.Determinism` → `CNNA.PillarA.Foundation.ConcreteSubstrate` → `CNNA.PillarA.Foundation.SubstrateAnalysis` → `CNNA.PillarA.Foundation.Notation` → `CNNA.PillarA.ToC.Contract` → `CNNA.PillarA.ToC.Addressing` → `CNNA.PillarA.ToC.IdealAddressEquiv` → `CNNA.PillarA.ToC.ConcreteIdeal` → `CNNA.PillarA.ToC.Concrete` → `CNNA.PillarA.ToC.GeneratedBranchFamily` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e` → `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus` → `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e` → `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window` → `CNNA.PillarA.Arithmetic.BuildAll` → `CNNA.PillarA.BuildAll` → `CNNA.BuildAll`

## Critical source→sink paths

- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.BuildAll` (74 nodes)
- `CNNA.PillarA.Foundation.HermitianStructure` → `CNNA.PillarA` (74 nodes)
- `CNNA.PillarB.BuildAll` → `CNNA.PillarB` (2 nodes)
- `CNNA.PillarC.BuildAll` → `CNNA.PillarC` (2 nodes)
- `CNNA.PillarD.BuildAll` → `CNNA.PillarD` (2 nodes)
- `CNNA.PillarE.BuildAll` → `CNNA.PillarE` (2 nodes)
- `CNNA.Basic` → `CNNA.Basic` (1 nodes)

## Files

- `summary.json`: aggregated signal-plan export
- `signal_graph.dot`: forward signal graph
- `signal_graph_reduced.dot`: transitive reduction of the forward signal graph
- `dominators.json`: dominator sets and immediate dominators
- `source_sink_paths.json`: representative critical source→sink paths
- `mainline.json`: selected longest mainline path
- `layers.json`: topological signal layers
- weighted source→sink paths: not computed
- confidence-weighted mainline: not computed

## Scope note

This is a syntactic signal plan derived from imports. It does not prove semantic handoff usage at symbol level.
