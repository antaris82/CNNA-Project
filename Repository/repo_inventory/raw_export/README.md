# Lean module and import export

- Repo root: `/mnt/data/toolchain_work/CNNA_Planning_Doc_Tool/Repository/repo_snapshot`
- Source root: `/mnt/data/toolchain_work/CNNA_Planning_Doc_Tool/Repository/repo_snapshot/CNNA`
- Internal prefixes: `CNNA`
- Modules: **287**
- Internal import edges: **724**
- External import edges: **43**
- Missing internal imports: **0**

## Signal-plan export

- Signal sources: **7**
- Signal sinks: **7**
- Signal edges: **724**
- Reduced signal edges: **375**
- Mainline length: **74**
- Files: `signal_plan/summary.json`, `signal_plan/signal_graph.dot`, `signal_plan/signal_graph_reduced.dot`

## Symbol-reference export

- Declarations detected: **8860**
- Symbol-reference edges: **394**
- Referenced symbols: **1686**
- Semantic signal edges: **394**
- Semantic mainline length: **65**
- Files: `symbol_references/summary.json`, `symbol_references/references.json`, `symbol_references/semantic_signal_plan/summary.json`

## Architectural core export

- Artifact modules filtered: **46**
- Core modules retained: **241**
- Clean signal edges: **307**
- Clean mainline length: **68**
- Clean semantic mainline length: **56**
- Clean discipline bridges: **4**
- Files: `architectural_core/summary.json`, `architectural_core/artifact_modules.json`, `architectural_core/syntactic_signal_plan/summary.json`

## Dependency-respecting topological order

1. `CNNA.Basic`
2. `CNNA.PillarA.Foundation.HermitianStructure`
3. `CNNA.PillarA.Foundation.SubstrateClass`
4. `CNNA.PillarB.BuildAll`
5. `CNNA.PillarC.BuildAll`
6. `CNNA.PillarD.BuildAll`
7. `CNNA.PillarE.BuildAll`
8. `CNNA.PillarA.Foundation.ExecComplex`
9. `CNNA.PillarA.Foundation.FiniteHilbert`
10. `CNNA.PillarB`
11. `CNNA.PillarC`
12. `CNNA.PillarD`
13. `CNNA.PillarE`
14. `CNNA.PillarA.Foundation.ExecComplexLemmas`
15. `CNNA.PillarA.Foundation.MatrixNorms`
16. `CNNA.PillarA.Foundation.MatrixAlgebra`
17. `CNNA.PillarA.Foundation.ExecComplexBridge`
18. `CNNA.PillarA.Foundation.Interfaces`
19. `CNNA.PillarA.Foundation.Determinism`
20. `CNNA.PillarA.Foundation.ConcreteSubstrate`
21. `CNNA.PillarA.Foundation.LevelVariableSubstrate`
22. `CNNA.PillarA.Foundation.RegularizationPolicy`
23. `CNNA.PillarA.Foundation.WeightPolicy`
24. `CNNA.PillarA.Foundation.SubstrateAnalysis`
25. `CNNA.PillarA.Foundation.Notation`
26. `CNNA.PillarA.Foundation.BuildAll`
27. `CNNA.PillarA.ToC.Contract`
28. `CNNA.PillarA.ToC.Addressing`
29. `CNNA.PillarA.Geometry.LCPMeasure`
30. `CNNA.PillarA.ToC.IdealAddressEquiv`
31. `CNNA.PillarA.Geometry.Foliation`
32. `CNNA.PillarA.ToC.ConcreteIdeal`
33. `CNNA.PillarA.Geometry.SpacetimePaths`
34. `CNNA.PillarA.ToC.Concrete`
35. `CNNA.PillarA.Geometry.Notation`
36. `CNNA.PillarA.ToC.GeneratedBranchFamily`
37. `CNNA.PillarA.ToC.Notation`
38. `CNNA.PillarA.Geometry.BuildAll`
39. `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`
40. `CNNA.PillarA.Finite.CutSpec`
41. `CNNA.PillarA.ToC.BuildAll`
42. `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`
43. `CNNA.PillarA.Finite.RegionCore`
44. `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`
45. `CNNA.PillarA.Finite.BoundaryPorts`
46. `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`
47. `CNNA.PillarA.Finite.Approximant`
48. `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`
49. `CNNA.PillarA.Finite.DirichletLaplacian`
50. `CNNA.PillarA.Finite.Selection`
51. `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`
52. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`
53. `CNNA.PillarA.DtN.DtN`
54. `CNNA.PillarA.Finite.SpectralDecompositionCore`
55. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`
56. `CNNA.PillarA.DtN.DtNStabilized`
57. `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`
58. `CNNA.PillarA.Finite.SpectralDecompositionC`
59. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`
60. `CNNA.PillarA.DtN.Notation`
61. `CNNA.PillarA.Sectors.BranchPatch`
62. `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`
63. `CNNA.PillarA.Finite.SpectralBridge`
64. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`
65. `CNNA.PillarA.DtN.BuildAll`
66. `CNNA.PillarA.Sectors.ComplementSectorFamily`
67. `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`
68. `CNNA.PillarA.Finite.StateSpace`
69. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`
70. `CNNA.PillarA.Sectors.SectorSplit`
71. `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`
72. `CNNA.PillarA.Finite.MatrixExponential`
73. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`
74. `CNNA.PillarA.Coupling.GeneralizedDtN`
75. `CNNA.PillarA.Network.RegionNet`
76. `CNNA.PillarA.Sectors.BranchingWitness`
77. `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`
78. `CNNA.PillarA.Finite.GibbsStateSeed`
79. `CNNA.PillarA.Finite.UnitaryEvolution`
80. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`
81. `CNNA.PillarA.Coupling.MultiSchur`
82. `CNNA.PillarA.Network.SectorChannels`
83. `CNNA.PillarA.Network.InfiniteCarrier`
84. `CNNA.PillarA.Sectors.SelectedBranching`
85. `CNNA.PillarA.Finite.ExecSpectral.Certificates`
86. `CNNA.PillarA.Finite.DynamicsAdapter`
87. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`
88. `CNNA.PillarA.Coupling.Notation`
89. `CNNA.PillarA.Network.SectorSysEnv`
90. `CNNA.PillarA.Sectors.UVSpectralSelector`
91. `CNNA.PillarA.Finite.ExecSpectral.BuildAll`
92. `CNNA.PillarA.Finite.SpectralDecomposition`
93. `CNNA.PillarA.Finite.ChannelSeed`
94. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`
95. `CNNA.PillarA.Coupling.BuildAll`
96. `CNNA.PillarA.Network.RelativeEntropyFlow`
97. `CNNA.PillarA.Sectors.BranchingSelector`
98. `CNNA.PillarA.Finite.ExecSpectral.Notation`
99. `CNNA.PillarA.Arithmetic.Core.Source`
100. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`
101. `CNNA.PillarA.Network.Notation`
102. `CNNA.PillarA.Closure.ParameterClosure`
103. `CNNA.PillarA.Sectors.Notation`
104. `CNNA.PillarA.Finite.Notation`
105. `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`
106. `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`
107. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`
108. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`
109. `CNNA.PillarA.Network.BuildAll`
110. `CNNA.PillarA.Closure.RegularizationClosure`
111. `CNNA.PillarA.Sectors.BuildAll`
112. `CNNA.PillarA.Finite.BuildAll`
113. `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`
114. `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`
115. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`
116. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`
117. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`
118. `CNNA.PillarA.Closure.Notation`
119. `CNNA.PillarA.Structural.CayleyDickson.Source`
120. `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`
121. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`
122. `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
123. `CNNA.PillarA.Closure.BuildAll`
124. `CNNA.PillarA.Handoff.Core.SectorExport`
125. `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`
126. `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`
127. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`
128. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`
129. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`
130. `CNNA.PillarA.Handoff.Core.Step1StrongCore`
131. `CNNA.PillarA.Handoff.Outputs.A_to_C`
132. `CNNA.PillarA.Handoff.Outputs.A_to_D`
133. `CNNA.PillarA.Handoff.Outputs.A_to_E`
134. `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`
135. `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`
136. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`
137. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`
138. `CNNA.PillarA.Handoff.Core.Step1MathData`
139. `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`
140. `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`
141. `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`
142. `CNNA.PillarA.Handoff.Core.BuildAll`
143. `CNNA.PillarA.Handoff.Outputs.A_to_B`
144. `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`
145. `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`
146. `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`
147. `CNNA.PillarA.Handoff.Outputs.Closed`
148. `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`
149. `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`
150. `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`
151. `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`
152. `CNNA.PillarA.Handoff.Inputs.B_to_A`
153. `CNNA.PillarA.Handoff.Inputs.C_to_A`
154. `CNNA.PillarA.Handoff.Inputs.D_to_A`
155. `CNNA.PillarA.Handoff.Inputs.E_to_A`
156. `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`
157. `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
158. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`
159. `CNNA.PillarA.Handoff.Inputs.BuildAll`
160. `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`
161. `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`
162. `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`
163. `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`
164. `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`
165. `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`
166. `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`
167. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`
168. `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`
169. `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`
170. `CNNA.PillarA.Arithmetic.Core.MatrixTransport`
171. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`
172. `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
173. `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`
174. `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge`
175. `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`
176. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`
177. `CNNA.PillarA.Handoff.Outputs.A_to_CayleyDickson`
178. `CNNA.PillarA.Handoff.ProofObligationI.Completion`
179. `CNNA.PillarA.Handoff.ProofObligationII.Preparation`
180. `CNNA.PillarA.Handoff.ProofObligationIII.Preparation`
181. `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`
182. `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`
183. `CNNA.PillarA.Arithmetic.Actions.ActionPackage`
184. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`
185. `CNNA.PillarA.Handoff.Outputs.BuildAll`
186. `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`
187. `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`
188. `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`
189. `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`
190. `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`
191. `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`
192. `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`
193. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`
194. `CNNA.PillarA.Handoff.Notation`
195. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`
196. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`
197. `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`
198. `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`
199. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`
200. `CNNA.PillarA.Handoff.BuildAll`
201. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`
202. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`
203. `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`
204. `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`
205. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`
206. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`
207. `CNNA.PillarA.Structural.CayleyDickson.S6Slot1AlternativeLaw`
208. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`
209. `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`
210. `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`
211. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`
212. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`
213. `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`
214. `CNNA.PillarA.Arithmetic.Schur.Recurrence`
215. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`
216. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`
217. `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`
218. `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`
219. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`
220. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`
221. `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`
222. `CNNA.PillarA.Arithmetic.Schur.CharpolyC`
223. `CNNA.PillarA.Arithmetic.Schur.L1Baseline`
224. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`
225. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`
226. `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`
227. `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`
228. `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`
229. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`
230. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`
231. `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`
232. `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`
233. `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`
234. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`
235. `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`
236. `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`
237. `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`
238. `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqSimultaneousSystem`
239. `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`
240. `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`
241. `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`
242. `CNNA.PillarA.Structural.CayleyDickson.BuildAll`
243. `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`
244. `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`
245. `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`
246. `CNNA.PillarA.Structural.BuildAll`
247. `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`
248. `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`
249. `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`
250. `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`
251. `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`
252. `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`
253. `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`
254. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`
255. `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`
256. `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`
257. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`
258. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`
259. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`
260. `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`
261. `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`
262. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`
263. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`
264. `CNNA.PillarA.Arithmetic.Orders.NormForms`
265. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`
266. `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`
267. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`
268. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`
269. `CNNA.PillarA.Arithmetic.Notation`
270. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`
271. `CNNA.PillarA.Notation`
272. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`
273. `CNNA.Notation`
274. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`
275. `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`
276. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`
277. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`
278. `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`
279. `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`
280. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`
281. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`
282. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`
283. `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`
284. `CNNA.PillarA.Arithmetic.BuildAll`
285. `CNNA.PillarA.BuildAll`
286. `CNNA.BuildAll`
287. `CNNA.PillarA`

## Modules

### `CNNA.Basic`

- Group: `Basic`
- Path: `CNNA/Basic.lean`
- Imports (0): none
- Internal imports (0): none
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.BuildAll`

- Group: `BuildAll`
- Path: `CNNA/BuildAll.lean`
- Imports (2): `CNNA.Notation`, `CNNA.PillarA.BuildAll`
- Internal imports (2): `CNNA.Notation`, `CNNA.PillarA.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.Notation`

- Group: `Notation`
- Path: `CNNA/Notation.lean`
- Imports (1): `CNNA.PillarA.Notation`
- Internal imports (1): `CNNA.PillarA.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.BuildAll`

### `CNNA.PillarA`

- Group: `PillarA`
- Path: `CNNA/PillarA.lean`
- Imports (1): `CNNA.PillarA.BuildAll`
- Internal imports (1): `CNNA.PillarA.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Actions/ActionFormatDecision.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`

### `CNNA.PillarA.Arithmetic.Actions.ActionPackage`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Actions/ActionPackage.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`, `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Actions/GeneratorActionInventory.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Actions.ActionPackage`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Actions.ActionPackage`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`, `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/BoundarySourceConvergence.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`
- Internal imports (2): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Core.MatrixTransport`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/BoundarySourceDecisionLedger.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/BoundarySourceInterface.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/BoundarySourceTypeDecision.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/BoundaryStateSubstrate.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/BranchAddressSubstrate.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/ExistingIdealThreadNoGo.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/GeneratedSubstrateRoute.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (7): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/HistoryExpandedSubstrate.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/InterfaceExposureSubstrate.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/LevelHistoryIndex.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Core.Source`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Core.Source`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/LevelHistoryMatrix.lean`
- Imports (3): `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`, `CNNA.PillarA.Foundation.ExecComplex`, `Mathlib.Data.Matrix.Basic`
- Internal imports (2): `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`, `CNNA.PillarA.Foundation.ExecComplex`
- External imports (1): `Mathlib.Data.Matrix.Basic`
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/LevelStepWitness.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/MultiSchurToLevelHistoryAdapter.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/RecursiveLevelHistoryCarrier.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/RecursiveLevelHistoryRoute.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`, `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BoundarySource/RecursiveLevelHistoryTypeDecision.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`, `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.BuildAll`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/BuildAll.lean`
- Imports (126): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`, `CNNA.PillarA.Arithmetic.Actions.ActionPackage`, `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`, `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`, `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`, `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`, `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`, `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`, `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`, `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`, `CNNA.PillarA.Arithmetic.Core.MatrixTransport`, `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`, `CNNA.PillarA.Arithmetic.Orders.NormForms`, `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`, `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`, `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`, `CNNA.PillarA.Arithmetic.Schur.L1Baseline`, `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`, `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`, `CNNA.PillarA.Arithmetic.Schur.Recurrence`, `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- Internal imports (126): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`, `CNNA.PillarA.Arithmetic.Actions.ActionPackage`, `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceInterface`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`, `CNNA.PillarA.Arithmetic.BoundarySource.GeneratedSubstrateRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`, `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`, `CNNA.PillarA.Arithmetic.BoundarySource.LevelStepWitness`, `CNNA.PillarA.Arithmetic.BoundarySource.MultiSchurToLevelHistoryAdapter`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryTypeDecision`, `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`, `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`, `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`, `CNNA.PillarA.Arithmetic.Core.MatrixTransport`, `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`, `CNNA.PillarA.Arithmetic.Orders.NormForms`, `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`, `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`, `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`, `CNNA.PillarA.Arithmetic.Schur.L1Baseline`, `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`, `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`, `CNNA.PillarA.Arithmetic.Schur.Recurrence`, `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/CayleyDickson/ArithmeticCDBridge.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`, `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Convergence/CDArithmeticCompatibility.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Orders.NormForms`
- Internal imports (2): `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Orders.NormForms`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Convergence/QuaternionRamanujanInterface.lean`
- Imports (3): `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`
- Internal imports (3): `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Core/BrightDtNSource.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Core.MatrixTransport`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Core.MatrixTransport`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.Actions.ActionPackage`, `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Core/FullBoundaryAudit.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Core.Source`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Core.Source`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`, `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Core.MatrixTransport`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Core/MatrixTransport.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`
- Internal imports (1): `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Core.Source`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Core/Source.lean`
- Imports (3): `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.ToC.BuildAll`
- Internal imports (3): `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.ToC.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryIndex`, `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Graph/CheegerSeed.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Graph/RamanujanTest.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Graph/SpectralGapSeed.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Notation`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Notation.lean`
- Imports (80): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`, `CNNA.PillarA.Arithmetic.Actions.ActionPackage`, `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`, `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`, `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`, `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`, `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`, `CNNA.PillarA.Arithmetic.Core.MatrixTransport`, `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`, `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`, `CNNA.PillarA.Arithmetic.Orders.NormForms`, `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`, `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`, `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`, `CNNA.PillarA.Arithmetic.Schur.L1Baseline`, `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`, `CNNA.PillarA.Arithmetic.Schur.Recurrence`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- Internal imports (80): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`, `CNNA.PillarA.Arithmetic.Actions.ActionPackage`, `CNNA.PillarA.Arithmetic.Actions.GeneratorActionInventory`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceConvergence`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceDecisionLedger`, `CNNA.PillarA.Arithmetic.BoundarySource.BoundaryStateSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.BranchAddressSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.ExistingIdealThreadNoGo`, `CNNA.PillarA.Arithmetic.BoundarySource.HistoryExpandedSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.InterfaceExposureSubstrate`, `CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryRoute`, `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`, `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Arithmetic.Core.BrightDtNSource`, `CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit`, `CNNA.PillarA.Arithmetic.Core.MatrixTransport`, `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.Arithmetic.Graph.CheegerSeed`, `CNNA.PillarA.Arithmetic.Graph.RamanujanTest`, `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`, `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`, `CNNA.PillarA.Arithmetic.Orders.NormForms`, `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`, `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`, `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`, `CNNA.PillarA.Arithmetic.Schur.L1Baseline`, `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`, `CNNA.PillarA.Arithmetic.Schur.Recurrence`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Orders/DiscriminantConvention.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Orders.NormForms`

### `CNNA.PillarA.Arithmetic.Orders.NormForms`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Orders/NormForms.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Convergence.CDArithmeticCompatibility`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Orders/QuadraticOrder.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Orders.DiscriminantConvention`

### `CNNA.PillarA.Arithmetic.Schur.CharpolyC`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/CharpolyC.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/CharpolyExec.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Schur.Recurrence`, `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.Recurrence`
- External imports (1): `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Arithmetic.Schur.L1Baseline`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`

### `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/HigherLevelCertificates.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`

### `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/HigherLevelDiscriminants.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`

### `CNNA.PillarA.Arithmetic.Schur.HigherLevelOutcomeRouter`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/HigherLevelOutcomeRouter.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelDiscriminants`

### `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/HigherLevelPredictionLedger.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelCertificates`

### `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/IdentityLedger.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Graph.SpectralGapSeed`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.HigherLevelPredictionLedger`

### `CNNA.PillarA.Arithmetic.Schur.L1Baseline`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/L1Baseline.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`

### `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/L2Eisenstein.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.L1Baseline`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.L1Baseline`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`

### `CNNA.PillarA.Arithmetic.Schur.L3Gaussian`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/L3Gaussian.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.L2Eisenstein`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Orders.QuadraticOrder`, `CNNA.PillarA.Arithmetic.Schur.IdentityLedger`

### `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/MobiusTransfer.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Actions.ActionFormatDecision`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`

### `CNNA.PillarA.Arithmetic.Schur.Recurrence`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/Recurrence.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`

### `CNNA.PillarA.Arithmetic.Schur.RecursiveSchurSource`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Schur/RecursiveSchurSource.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Schur.MobiusTransfer`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Schur.Recurrence`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedApproximantCore.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedArithmeticSourceExecBoundaryOperatorSM5q.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedArithmeticSourceSM5.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedBoundaryInteriorPartition.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedDegreeFormulaAuditSM3db2eR0.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedDegreePivotScaleSourceSM3db2dR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedDirichletEntry.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`, `CNNA.PillarA.Foundation.WeightPolicy`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition`, `CNNA.PillarA.Foundation.WeightPolicy`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedDirichletExecEntrySourceSM3bq.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedGeneralizedTopBoundaryDtNSM3hR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorAccumulatedEntryCancellationR3c1.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorAccumulatedTraceEvaluation.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlock.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldInvarianceR3c1c.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldNormalFormR3c1a.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldTerminalIdentityR3c1d.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationCandidate.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationCandidateEntry.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationCarrier.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationCertificateSM3fR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationStep.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationTrace.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationStep`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateEntry`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorInverseCandidateEntry.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationTrace`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorInverseCandidateMatrix.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorInverseCandidateShapeSeparation.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateMatrix`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorInverseCandidateStart.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCarrier`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepCancellationR3c1bFull`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorLocalStepCancellationR3c1bFull.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorLocalStepSchurCancellationInvariantSM3db2aR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorProductIdentityProofR4a.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorProvenTwoSidedInvR5.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTerminalFoldResidualIdentityFieldsSM3db4aU.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityFromSM3db4aWR3c1dFull`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTraceCancellationDerivation.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTraceCancellationR3c2.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTracePivotScaleWitnessFromGeneratedDegreeSM3db2cR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorPerPivotRegularityFromTraceSM3db2bR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTracePivotTerminalCoverageSourceSM3db3aR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldInvarianceR3c1c`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualCoverageSM3db4aT`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTwoSidedInv.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`, `CNNA.PillarA.DtN.DtN`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry`, `CNNA.PillarA.DtN.DtN`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateStart`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTwoSidedInvFromSM3db7R.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`, `CNNA.PillarA.DtN.DtN`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`, `CNNA.PillarA.DtN.DtN`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedInverseCandidateExecEntrySourceSM3eRq.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`, `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryBoundaryPortSourceSM6a.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryCharpolyExecFromMirrorSM9b.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Schur.CharpolyExec`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryExecMirrorSourceSM9a.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceFromSM8RecheckSM9a`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryMatrixFromBridgeSM8.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistorySchurIndexBridgeRecheckSM7a.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryMatrixFromBridgeSM8`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelHistoryToSchurIndexSM7.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistorySchurIndexBridgeRecheckSM7a`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMatrixFromSM6bRecheckSM8`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelStepExecMirrorSourceSM6b.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceFromSM5qRecheckSM6b`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepWitnessSM6`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedLevelStepWitnessSM6.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryBoundaryPortSourceSM6a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryToSchurIndexSM7`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedMainPath.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorFromSM4qRecheckSM5q`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedMultiSchurExecBoundaryOperatorSM4q.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedMultiSchurSM4.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceSM5`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDegreeReciprocalSourceSM3db2fR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalDegreeReciprocalSourceSM3db2fR.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldKernelLocalSchurResidualBridgeR3c1b1`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalDeterminantCoefficientRecurrenceSM9e.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalDeterminantEvaluationBridgeFromSM9e.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantEvaluationBridgeFromSM9e`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalDiscriminantFactorGateFromSM9fFull.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedOperationalQuadraticDiscriminantSourceFromSM9g1Window.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Arithmetic.BuildAll`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedResetSM3LedgerSM3iR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedResetSM3LedgerSM3iR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurSM4`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedSM3fSchurExecCompletionSM3fqPlus.lean`
- Imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`
- Internal imports (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorFromSM3fqPlusSM4q`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedSM3fSchurExecEntrySourceSM3fq.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecCompletionSM3fqPlus`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedSource.lean`
- Imports (1): `CNNA.PillarA.ToC.GeneratedBranchFamily`
- Internal imports (1): `CNNA.PillarA.ToC.GeneratedBranchFamily`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath`

### `CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/GeneratedTopBoundaryDtNSM3gR.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedGeneralizedTopBoundaryDtNSM3hR`

### `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantCoefficientRecurrenceSM9e`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`

### `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/OperationalBoundedPolynomialForwardEvaluationSourceSM9ePlus.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.OperationalBoundedPolynomialEvaluationNormalFormSM9ePlus`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus`

### `CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff`

- Group: `PillarA/Arithmetic`
- Path: `CNNA/PillarA/Arithmetic/Smoke/SM3dbRToSM3eRHandoff.lean`
- Imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`
- Internal imports (1): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorInverseCandidateShapeSeparation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq`

### `CNNA.PillarA.BuildAll`

- Group: `PillarA`
- Path: `CNNA/PillarA/BuildAll.lean`
- Imports (13): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Closure.BuildAll`, `CNNA.PillarA.Coupling.BuildAll`, `CNNA.PillarA.DtN.BuildAll`, `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Geometry.BuildAll`, `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Notation`, `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Structural.BuildAll`, `CNNA.PillarA.ToC.BuildAll`
- Internal imports (13): `CNNA.PillarA.Arithmetic.BuildAll`, `CNNA.PillarA.Closure.BuildAll`, `CNNA.PillarA.Coupling.BuildAll`, `CNNA.PillarA.DtN.BuildAll`, `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Geometry.BuildAll`, `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Notation`, `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Structural.BuildAll`, `CNNA.PillarA.ToC.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.BuildAll`, `CNNA.PillarA`

### `CNNA.PillarA.Closure.BuildAll`

- Group: `PillarA/Closure`
- Path: `CNNA/PillarA/Closure/BuildAll.lean`
- Imports (3): `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Closure.ParameterClosure`, `CNNA.PillarA.Closure.RegularizationClosure`
- Internal imports (3): `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Closure.ParameterClosure`, `CNNA.PillarA.Closure.RegularizationClosure`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Closure.Notation`

- Group: `PillarA/Closure`
- Path: `CNNA/PillarA/Closure/Notation.lean`
- Imports (1): `CNNA.PillarA.Closure.RegularizationClosure`
- Internal imports (1): `CNNA.PillarA.Closure.RegularizationClosure`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Closure.BuildAll`, `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Closure.ParameterClosure`

- Group: `PillarA/Closure`
- Path: `CNNA/PillarA/Closure/ParameterClosure.lean`
- Imports (2): `CNNA.PillarA.DtN.DtNStabilized`, `CNNA.PillarA.Sectors.BranchingSelector`
- Internal imports (2): `CNNA.PillarA.DtN.DtNStabilized`, `CNNA.PillarA.Sectors.BranchingSelector`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Closure.BuildAll`, `CNNA.PillarA.Closure.RegularizationClosure`

### `CNNA.PillarA.Closure.RegularizationClosure`

- Group: `PillarA/Closure`
- Path: `CNNA/PillarA/Closure/RegularizationClosure.lean`
- Imports (1): `CNNA.PillarA.Closure.ParameterClosure`
- Internal imports (1): `CNNA.PillarA.Closure.ParameterClosure`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Closure.BuildAll`, `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Structural.CayleyDickson.Source`

### `CNNA.PillarA.Coupling.BuildAll`

- Group: `PillarA/Coupling`
- Path: `CNNA/PillarA/Coupling/BuildAll.lean`
- Imports (3): `CNNA.PillarA.Coupling.GeneralizedDtN`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Coupling.Notation`
- Internal imports (3): `CNNA.PillarA.Coupling.GeneralizedDtN`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Coupling.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Coupling.GeneralizedDtN`

- Group: `PillarA/Coupling`
- Path: `CNNA/PillarA/Coupling/GeneralizedDtN.lean`
- Imports (2): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.Sectors.SectorSplit`
- Internal imports (2): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.Sectors.SectorSplit`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Coupling.BuildAll`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Network.SectorChannels`

### `CNNA.PillarA.Coupling.MultiSchur`

- Group: `PillarA/Coupling`
- Path: `CNNA/PillarA/Coupling/MultiSchur.lean`
- Imports (1): `CNNA.PillarA.Coupling.GeneralizedDtN`
- Internal imports (1): `CNNA.PillarA.Coupling.GeneralizedDtN`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.Coupling.BuildAll`, `CNNA.PillarA.Coupling.Notation`, `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Structural.CayleyDickson.Source`

### `CNNA.PillarA.Coupling.Notation`

- Group: `PillarA/Coupling`
- Path: `CNNA/PillarA/Coupling/Notation.lean`
- Imports (1): `CNNA.PillarA.Coupling.MultiSchur`
- Internal imports (1): `CNNA.PillarA.Coupling.MultiSchur`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Coupling.BuildAll`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.DtN.BuildAll`

- Group: `PillarA/DtN`
- Path: `CNNA/PillarA/DtN/BuildAll.lean`
- Imports (3): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.DtN.DtNStabilized`, `CNNA.PillarA.DtN.Notation`
- Internal imports (3): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.DtN.DtNStabilized`, `CNNA.PillarA.DtN.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.DtN.DtN`

- Group: `PillarA/DtN`
- Path: `CNNA/PillarA/DtN/DtN.lean`
- Imports (1): `CNNA.PillarA.Finite.DirichletLaplacian`
- Internal imports (1): `CNNA.PillarA.Finite.DirichletLaplacian`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInv`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R`, `CNNA.PillarA.Coupling.GeneralizedDtN`, `CNNA.PillarA.DtN.BuildAll`, `CNNA.PillarA.DtN.DtNStabilized`

### `CNNA.PillarA.DtN.DtNStabilized`

- Group: `PillarA/DtN`
- Path: `CNNA/PillarA/DtN/DtNStabilized.lean`
- Imports (3): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.RegularizationPolicy`
- Internal imports (3): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.RegularizationPolicy`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Closure.ParameterClosure`, `CNNA.PillarA.DtN.BuildAll`, `CNNA.PillarA.DtN.Notation`, `CNNA.PillarA.Sectors.BranchPatch`

### `CNNA.PillarA.DtN.Notation`

- Group: `PillarA/DtN`
- Path: `CNNA/PillarA/DtN/Notation.lean`
- Imports (1): `CNNA.PillarA.DtN.DtNStabilized`
- Internal imports (1): `CNNA.PillarA.DtN.DtNStabilized`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.DtN.BuildAll`, `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Finite.Approximant`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/Approximant.lean`
- Imports (1): `CNNA.PillarA.Finite.BoundaryPorts`
- Internal imports (1): `CNNA.PillarA.Finite.BoundaryPorts`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Finite.Selection`

### `CNNA.PillarA.Finite.BoundaryPorts`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/BoundaryPorts.lean`
- Imports (1): `CNNA.PillarA.Finite.RegionCore`
- Internal imports (1): `CNNA.PillarA.Finite.RegionCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.Approximant`, `CNNA.PillarA.Finite.BuildAll`

### `CNNA.PillarA.Finite.BuildAll`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/BuildAll.lean`
- Imports (17): `CNNA.PillarA.Finite.Approximant`, `CNNA.PillarA.Finite.BoundaryPorts`, `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.Finite.CutSpec`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Finite.DynamicsAdapter`, `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.GibbsStateSeed`, `CNNA.PillarA.Finite.MatrixExponential`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Finite.RegionCore`, `CNNA.PillarA.Finite.Selection`, `CNNA.PillarA.Finite.SpectralBridge`, `CNNA.PillarA.Finite.SpectralDecomposition`, `CNNA.PillarA.Finite.SpectralDecompositionC`, `CNNA.PillarA.Finite.StateSpace`, `CNNA.PillarA.Finite.UnitaryEvolution`
- Internal imports (17): `CNNA.PillarA.Finite.Approximant`, `CNNA.PillarA.Finite.BoundaryPorts`, `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.Finite.CutSpec`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Finite.DynamicsAdapter`, `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.GibbsStateSeed`, `CNNA.PillarA.Finite.MatrixExponential`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Finite.RegionCore`, `CNNA.PillarA.Finite.Selection`, `CNNA.PillarA.Finite.SpectralBridge`, `CNNA.PillarA.Finite.SpectralDecomposition`, `CNNA.PillarA.Finite.SpectralDecompositionC`, `CNNA.PillarA.Finite.StateSpace`, `CNNA.PillarA.Finite.UnitaryEvolution`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Finite.ChannelSeed`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ChannelSeed.lean`
- Imports (4): `CNNA.PillarA.Finite.DynamicsAdapter`, `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Fintype.Prod`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Internal imports (1): `CNNA.PillarA.Finite.DynamicsAdapter`
- External imports (3): `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Fintype.Prod`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.CutSpec`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/CutSpec.lean`
- Imports (1): `CNNA.PillarA.ToC.Notation`
- Internal imports (1): `CNNA.PillarA.ToC.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.RegionCore`

### `CNNA.PillarA.Finite.DirichletLaplacian`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/DirichletLaplacian.lean`
- Imports (3): `CNNA.PillarA.Finite.Approximant`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.WeightPolicy`
- Internal imports (3): `CNNA.PillarA.Finite.Approximant`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.WeightPolicy`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.DtN.DtN`, `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Finite.SpectralDecompositionCore`

### `CNNA.PillarA.Finite.DynamicsAdapter`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/DynamicsAdapter.lean`
- Imports (1): `CNNA.PillarA.Finite.UnitaryEvolution`
- Internal imports (1): `CNNA.PillarA.Finite.UnitaryEvolution`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.ExecSpectral.BuildAll`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/BuildAll.lean`
- Imports (6): `CNNA.PillarA.Finite.ExecSpectral.Certificates`, `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`, `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`, `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`, `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`, `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`
- Internal imports (6): `CNNA.PillarA.Finite.ExecSpectral.Certificates`, `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`, `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`, `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`, `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`, `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.ExecSpectral.Notation`

### `CNNA.PillarA.Finite.ExecSpectral.Certificates`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/Certificates.lean`
- Imports (1): `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`
- Internal imports (1): `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.SpectralDecomposition`

### `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/CharpolyCore.lean`
- Imports (1): `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`
- Internal imports (1): `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`

### `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/EigenvectorKernel.lean`
- Imports (1): `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`
- Internal imports (1): `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`

### `CNNA.PillarA.Finite.ExecSpectral.Notation`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/Notation.lean`
- Imports (1): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`
- Internal imports (1): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/PolynomialCore.lean`
- Imports (1): `CNNA.PillarA.Finite.SpectralDecompositionCore`
- Internal imports (1): `CNNA.PillarA.Finite.SpectralDecompositionCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`

### `CNNA.PillarA.Finite.ExecSpectral.ProjectorCore`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/ProjectorCore.lean`
- Imports (1): `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`
- Internal imports (1): `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.ExecSpectral.Certificates`

### `CNNA.PillarA.Finite.ExecSpectral.RootIsolation`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/ExecSpectral/RootIsolation.lean`
- Imports (1): `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`
- Internal imports (1): `CNNA.PillarA.Finite.ExecSpectral.CharpolyCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.ExecSpectral.BuildAll`, `CNNA.PillarA.Finite.ExecSpectral.EigenvectorKernel`

### `CNNA.PillarA.Finite.GibbsStateSeed`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/GibbsStateSeed.lean`
- Imports (3): `CNNA.PillarA.Finite.MatrixExponential`, `Mathlib.Analysis.SpecialFunctions.Exponential`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Internal imports (1): `CNNA.PillarA.Finite.MatrixExponential`
- External imports (2): `Mathlib.Analysis.SpecialFunctions.Exponential`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.MatrixExponential`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/MatrixExponential.lean`
- Imports (3): `CNNA.PillarA.Finite.StateSpace`, `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Analysis.Normed.Algebra.MatrixExponential`
- Internal imports (1): `CNNA.PillarA.Finite.StateSpace`
- External imports (2): `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Analysis.Normed.Algebra.MatrixExponential`
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.GibbsStateSeed`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Finite.UnitaryEvolution`

### `CNNA.PillarA.Finite.Notation`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/Notation.lean`
- Imports (12): `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Finite.DynamicsAdapter`, `CNNA.PillarA.Finite.ExecSpectral.Notation`, `CNNA.PillarA.Finite.GibbsStateSeed`, `CNNA.PillarA.Finite.MatrixExponential`, `CNNA.PillarA.Finite.Selection`, `CNNA.PillarA.Finite.SpectralBridge`, `CNNA.PillarA.Finite.SpectralDecomposition`, `CNNA.PillarA.Finite.SpectralDecompositionC`, `CNNA.PillarA.Finite.StateSpace`, `CNNA.PillarA.Finite.UnitaryEvolution`
- Internal imports (12): `CNNA.PillarA.Finite.ChannelSeed`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Finite.DynamicsAdapter`, `CNNA.PillarA.Finite.ExecSpectral.Notation`, `CNNA.PillarA.Finite.GibbsStateSeed`, `CNNA.PillarA.Finite.MatrixExponential`, `CNNA.PillarA.Finite.Selection`, `CNNA.PillarA.Finite.SpectralBridge`, `CNNA.PillarA.Finite.SpectralDecomposition`, `CNNA.PillarA.Finite.SpectralDecompositionC`, `CNNA.PillarA.Finite.StateSpace`, `CNNA.PillarA.Finite.UnitaryEvolution`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Finite.RegionCore`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/RegionCore.lean`
- Imports (1): `CNNA.PillarA.Finite.CutSpec`
- Internal imports (1): `CNNA.PillarA.Finite.CutSpec`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BoundaryPorts`, `CNNA.PillarA.Finite.BuildAll`

### `CNNA.PillarA.Finite.Selection`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/Selection.lean`
- Imports (1): `CNNA.PillarA.Finite.Approximant`
- Internal imports (1): `CNNA.PillarA.Finite.Approximant`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.SpectralBridge`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/SpectralBridge.lean`
- Imports (1): `CNNA.PillarA.Finite.SpectralDecompositionC`
- Internal imports (1): `CNNA.PillarA.Finite.SpectralDecompositionC`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Finite.StateSpace`

### `CNNA.PillarA.Finite.SpectralDecomposition`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/SpectralDecomposition.lean`
- Imports (2): `CNNA.PillarA.Finite.ExecSpectral.Certificates`, `CNNA.PillarA.Finite.SpectralDecompositionCore`
- Internal imports (2): `CNNA.PillarA.Finite.ExecSpectral.Certificates`, `CNNA.PillarA.Finite.SpectralDecompositionCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.SpectralDecompositionC`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/SpectralDecompositionC.lean`
- Imports (3): `CNNA.PillarA.Finite.SpectralDecompositionCore`, `CNNA.PillarA.Foundation.ExecComplexBridge`, `Mathlib.Analysis.Matrix.Spectrum`
- Internal imports (2): `CNNA.PillarA.Finite.SpectralDecompositionCore`, `CNNA.PillarA.Foundation.ExecComplexBridge`
- External imports (1): `Mathlib.Analysis.Matrix.Spectrum`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Finite.SpectralBridge`

### `CNNA.PillarA.Finite.SpectralDecompositionCore`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/SpectralDecompositionCore.lean`
- Imports (3): `CNNA.PillarA.Finite.DirichletLaplacian`, `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Internal imports (1): `CNNA.PillarA.Finite.DirichletLaplacian`
- External imports (2): `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.ExecSpectral.PolynomialCore`, `CNNA.PillarA.Finite.SpectralDecomposition`, `CNNA.PillarA.Finite.SpectralDecompositionC`

### `CNNA.PillarA.Finite.StateSpace`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/StateSpace.lean`
- Imports (2): `CNNA.PillarA.Finite.SpectralBridge`, `Mathlib.LinearAlgebra.Matrix.Trace`
- Internal imports (1): `CNNA.PillarA.Finite.SpectralBridge`
- External imports (1): `Mathlib.LinearAlgebra.Matrix.Trace`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.MatrixExponential`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Finite.UnitaryEvolution`

- Group: `PillarA/Finite`
- Path: `CNNA/PillarA/Finite/UnitaryEvolution.lean`
- Imports (2): `CNNA.PillarA.Finite.MatrixExponential`, `Mathlib.Analysis.Complex.Exponential`
- Internal imports (1): `CNNA.PillarA.Finite.MatrixExponential`
- External imports (1): `Mathlib.Analysis.Complex.Exponential`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.BuildAll`, `CNNA.PillarA.Finite.DynamicsAdapter`, `CNNA.PillarA.Finite.Notation`

### `CNNA.PillarA.Foundation.BuildAll`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/BuildAll.lean`
- Imports (16): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.ExecComplex`, `CNNA.PillarA.Foundation.ExecComplexBridge`, `CNNA.PillarA.Foundation.ExecComplexLemmas`, `CNNA.PillarA.Foundation.FiniteHilbert`, `CNNA.PillarA.Foundation.HermitianStructure`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Foundation.RegularizationPolicy`, `CNNA.PillarA.Foundation.SubstrateAnalysis`, `CNNA.PillarA.Foundation.SubstrateClass`, `CNNA.PillarA.Foundation.WeightPolicy`
- Internal imports (16): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.ExecComplex`, `CNNA.PillarA.Foundation.ExecComplexBridge`, `CNNA.PillarA.Foundation.ExecComplexLemmas`, `CNNA.PillarA.Foundation.FiniteHilbert`, `CNNA.PillarA.Foundation.HermitianStructure`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Foundation.RegularizationPolicy`, `CNNA.PillarA.Foundation.SubstrateAnalysis`, `CNNA.PillarA.Foundation.SubstrateClass`, `CNNA.PillarA.Foundation.WeightPolicy`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Foundation.ConcreteSubstrate`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/ConcreteSubstrate.lean`
- Imports (4): `CNNA.PillarA.Foundation.Determinism`, `Mathlib.Data.Fin.Basic`, `Mathlib.Data.Finset.Image`, `Mathlib.Data.Fintype.Pi`
- Internal imports (1): `CNNA.PillarA.Foundation.Determinism`
- External imports (3): `Mathlib.Data.Fin.Basic`, `Mathlib.Data.Finset.Image`, `Mathlib.Data.Fintype.Pi`
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Foundation.SubstrateAnalysis`, `CNNA.PillarA.ToC.ConcreteIdeal`, `CNNA.PillarA.ToC.GeneratedBranchFamily`

### `CNNA.PillarA.Foundation.Determinism`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/Determinism.lean`
- Imports (2): `CNNA.PillarA.Foundation.Interfaces`, `Mathlib`
- Internal imports (1): `CNNA.PillarA.Foundation.Interfaces`
- External imports (1): `Mathlib`
- Missing internal imports (0): none
- Imported by (7): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.Foundation.RegularizationPolicy`, `CNNA.PillarA.Foundation.WeightPolicy`, `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.Contract`

### `CNNA.PillarA.Foundation.ExecComplex`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/ExecComplex.lean`
- Imports (6): `CNNA.PillarA.Foundation.HermitianStructure`, `Mathlib.Algebra.Ring.MinimalAxioms`, `Mathlib.Algebra.Ring.Rat`, `Mathlib.Algebra.Star.Basic`, `Mathlib.Tactic.Ext`, `Mathlib.Tactic.Ring`
- Internal imports (1): `CNNA.PillarA.Foundation.HermitianStructure`
- External imports (5): `Mathlib.Algebra.Ring.MinimalAxioms`, `Mathlib.Algebra.Ring.Rat`, `Mathlib.Algebra.Star.Basic`, `Mathlib.Tactic.Ext`, `Mathlib.Tactic.Ring`
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix`, `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.ExecComplexLemmas`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Foundation.ExecComplexBridge`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/ExecComplexBridge.lean`
- Imports (6): `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Complex.Basic`, `Mathlib.Data.Rat.BigOperators`, `Mathlib.Data.Rat.Cast.Order`
- Internal imports (2): `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`
- External imports (4): `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Complex.Basic`, `Mathlib.Data.Rat.BigOperators`, `Mathlib.Data.Rat.Cast.Order`
- Missing internal imports (0): none
- Imported by (8): `CNNA.PillarA.Arithmetic.Schur.CharpolyC`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedArithmeticSourceExecBoundaryOperatorSM5q`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryExecMirrorSourceSM9a`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelStepExecMirrorSourceSM6b`, `CNNA.PillarA.Arithmetic.Smoke.GeneratedMultiSchurExecBoundaryOperatorSM4q`, `CNNA.PillarA.Finite.SpectralDecompositionC`, `CNNA.PillarA.Foundation.BuildAll`

### `CNNA.PillarA.Foundation.ExecComplexLemmas`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/ExecComplexLemmas.lean`
- Imports (1): `CNNA.PillarA.Foundation.ExecComplex`
- Internal imports (1): `CNNA.PillarA.Foundation.ExecComplex`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Foundation.BuildAll`

### `CNNA.PillarA.Foundation.FiniteHilbert`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/FiniteHilbert.lean`
- Imports (2): `CNNA.PillarA.Foundation.HermitianStructure`, `Mathlib.Algebra.BigOperators.Ring.Finset`
- Internal imports (1): `CNNA.PillarA.Foundation.HermitianStructure`
- External imports (1): `Mathlib.Algebra.BigOperators.Ring.Finset`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.MatrixAlgebra`

### `CNNA.PillarA.Foundation.HermitianStructure`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/HermitianStructure.lean`
- Imports (2): `Mathlib.Algebra.Star.Basic`, `Mathlib.LinearAlgebra.Matrix.Hermitian`
- Internal imports (0): none
- External imports (2): `Mathlib.Algebra.Star.Basic`, `Mathlib.LinearAlgebra.Matrix.Hermitian`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.ExecComplex`, `CNNA.PillarA.Foundation.FiniteHilbert`

### `CNNA.PillarA.Foundation.Interfaces`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/Interfaces.lean`
- Imports (4): `CNNA.PillarA.Foundation.FiniteHilbert`, `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.SubstrateClass`
- Internal imports (4): `CNNA.PillarA.Foundation.FiniteHilbert`, `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.SubstrateClass`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Foundation.LevelVariableSubstrate`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/LevelVariableSubstrate.lean`
- Imports (4): `CNNA.PillarA.Foundation.Determinism`, `Mathlib.Data.Fin.Basic`, `Mathlib.Data.Finset.Image`, `Mathlib.Data.Fintype.Pi`
- Internal imports (1): `CNNA.PillarA.Foundation.Determinism`
- External imports (3): `Mathlib.Data.Fin.Basic`, `Mathlib.Data.Finset.Image`, `Mathlib.Data.Fintype.Pi`
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Foundation.SubstrateAnalysis`, `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.GeneratedBranchFamily`

### `CNNA.PillarA.Foundation.MatrixAlgebra`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/MatrixAlgebra.lean`
- Imports (4): `CNNA.PillarA.Foundation.FiniteHilbert`, `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Matrix.Basic`, `Mathlib.LinearAlgebra.Matrix.ConjTranspose`
- Internal imports (1): `CNNA.PillarA.Foundation.FiniteHilbert`
- External imports (3): `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Matrix.Basic`, `Mathlib.LinearAlgebra.Matrix.ConjTranspose`
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.ExecComplexBridge`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Foundation.MatrixNorms`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/MatrixNorms.lean`
- Imports (4): `CNNA.PillarA.Foundation.ExecComplex`, `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Matrix.Basic`, `Mathlib.Data.Real.Basic`
- Internal imports (1): `CNNA.PillarA.Foundation.ExecComplex`
- External imports (3): `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Data.Matrix.Basic`, `Mathlib.Data.Real.Basic`
- Missing internal imports (0): none
- Imported by (9): `CNNA.PillarA.DtN.DtNStabilized`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.ExecComplexBridge`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Foundation.RegularizationPolicy`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`, `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`

### `CNNA.PillarA.Foundation.Notation`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/Notation.lean`
- Imports (10): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.ExecComplex`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.RegularizationPolicy`, `CNNA.PillarA.Foundation.SubstrateAnalysis`, `CNNA.PillarA.Foundation.SubstrateClass`, `CNNA.PillarA.Foundation.WeightPolicy`
- Internal imports (10): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.ExecComplex`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.Foundation.MatrixAlgebra`, `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Foundation.RegularizationPolicy`, `CNNA.PillarA.Foundation.SubstrateAnalysis`, `CNNA.PillarA.Foundation.SubstrateClass`, `CNNA.PillarA.Foundation.WeightPolicy`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Notation`, `CNNA.PillarA.ToC.Addressing`, `CNNA.PillarA.ToC.Contract`

### `CNNA.PillarA.Foundation.RegularizationPolicy`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/RegularizationPolicy.lean`
- Imports (3): `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.MatrixNorms`, `Mathlib.Data.Rat.Cast.Order`
- Internal imports (2): `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.MatrixNorms`
- External imports (1): `Mathlib.Data.Rat.Cast.Order`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.DtN.DtNStabilized`, `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Foundation.SubstrateAnalysis`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/SubstrateAnalysis.lean`
- Imports (2): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`
- Internal imports (2): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Foundation.SubstrateClass`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/SubstrateClass.lean`
- Imports (1): `Mathlib`
- Internal imports (0): none
- External imports (1): `Mathlib`
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Interfaces`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Foundation.WeightPolicy`

- Group: `PillarA/Foundation`
- Path: `CNNA/PillarA/Foundation/WeightPolicy.lean`
- Imports (2): `CNNA.PillarA.Foundation.Determinism`, `Mathlib.Data.Rat.Cast.Order`
- Internal imports (1): `CNNA.PillarA.Foundation.Determinism`
- External imports (1): `Mathlib.Data.Rat.Cast.Order`
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry`, `CNNA.PillarA.Finite.DirichletLaplacian`, `CNNA.PillarA.Foundation.BuildAll`, `CNNA.PillarA.Foundation.Notation`

### `CNNA.PillarA.Geometry.BuildAll`

- Group: `PillarA/Geometry`
- Path: `CNNA/PillarA/Geometry/BuildAll.lean`
- Imports (4): `CNNA.PillarA.Geometry.Foliation`, `CNNA.PillarA.Geometry.LCPMeasure`, `CNNA.PillarA.Geometry.Notation`, `CNNA.PillarA.Geometry.SpacetimePaths`
- Internal imports (4): `CNNA.PillarA.Geometry.Foliation`, `CNNA.PillarA.Geometry.LCPMeasure`, `CNNA.PillarA.Geometry.Notation`, `CNNA.PillarA.Geometry.SpacetimePaths`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Geometry.Foliation`

- Group: `PillarA/Geometry`
- Path: `CNNA/PillarA/Geometry/Foliation.lean`
- Imports (1): `CNNA.PillarA.Geometry.LCPMeasure`
- Internal imports (1): `CNNA.PillarA.Geometry.LCPMeasure`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Geometry.BuildAll`, `CNNA.PillarA.Geometry.SpacetimePaths`

### `CNNA.PillarA.Geometry.LCPMeasure`

- Group: `PillarA/Geometry`
- Path: `CNNA/PillarA/Geometry/LCPMeasure.lean`
- Imports (2): `CNNA.PillarA.ToC.Addressing`, `Mathlib.Data.Nat.Find`
- Internal imports (1): `CNNA.PillarA.ToC.Addressing`
- External imports (1): `Mathlib.Data.Nat.Find`
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Geometry.BuildAll`, `CNNA.PillarA.Geometry.Foliation`

### `CNNA.PillarA.Geometry.Notation`

- Group: `PillarA/Geometry`
- Path: `CNNA/PillarA/Geometry/Notation.lean`
- Imports (1): `CNNA.PillarA.Geometry.SpacetimePaths`
- Internal imports (1): `CNNA.PillarA.Geometry.SpacetimePaths`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Geometry.BuildAll`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Geometry.SpacetimePaths`

- Group: `PillarA/Geometry`
- Path: `CNNA/PillarA/Geometry/SpacetimePaths.lean`
- Imports (1): `CNNA.PillarA.Geometry.Foliation`
- Internal imports (1): `CNNA.PillarA.Geometry.Foliation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Geometry.BuildAll`, `CNNA.PillarA.Geometry.Notation`

### `CNNA.PillarA.Handoff.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/BuildAll.lean`
- Imports (8): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`, `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Inputs.BuildAll`, `CNNA.PillarA.Handoff.Notation`, `CNNA.PillarA.Handoff.Outputs.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`
- Internal imports (8): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`, `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Inputs.BuildAll`, `CNNA.PillarA.Handoff.Notation`, `CNNA.PillarA.Handoff.Outputs.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Handoff.CayleyDicksonAdapter`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/CayleyDicksonAdapter.lean`
- Imports (3): `CNNA.PillarA.Handoff.Outputs.Closed`, `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`
- Internal imports (3): `CNNA.PillarA.Handoff.Outputs.Closed`, `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Outputs.A_to_CayleyDickson`, `CNNA.PillarA.Handoff.ProofObligationI.Completion`, `CNNA.PillarA.Handoff.ProofObligationII.Preparation`, `CNNA.PillarA.Handoff.ProofObligationIII.Preparation`

### `CNNA.PillarA.Handoff.Core.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Core/BuildAll.lean`
- Imports (3): `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Handoff.Core.Step1MathData`, `CNNA.PillarA.Handoff.Core.Step1StrongCore`
- Internal imports (3): `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Handoff.Core.Step1MathData`, `CNNA.PillarA.Handoff.Core.Step1StrongCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Notation`

### `CNNA.PillarA.Handoff.Core.SectorExport`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Core/SectorExport.lean`
- Imports (5): `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Closure.RegularizationClosure`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.DtN.Notation`, `CNNA.PillarA.Network.InfiniteCarrier`
- Internal imports (5): `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Closure.RegularizationClosure`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.DtN.Notation`, `CNNA.PillarA.Network.InfiniteCarrier`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (5): `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Core.Step1StrongCore`, `CNNA.PillarA.Handoff.Outputs.A_to_C`, `CNNA.PillarA.Handoff.Outputs.A_to_D`, `CNNA.PillarA.Handoff.Outputs.A_to_E`

### `CNNA.PillarA.Handoff.Core.Step1MathData`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Core/Step1MathData.lean`
- Imports (1): `CNNA.PillarA.Handoff.Core.Step1StrongCore`
- Internal imports (1): `CNNA.PillarA.Handoff.Core.Step1StrongCore`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Outputs.A_to_B`

### `CNNA.PillarA.Handoff.Core.Step1StrongCore`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Core/Step1StrongCore.lean`
- Imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- Internal imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Core.Step1MathData`

### `CNNA.PillarA.Handoff.Inputs.B_to_A`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Inputs/B_to_A.lean`
- Imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- Internal imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Inputs.BuildAll`

### `CNNA.PillarA.Handoff.Inputs.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Inputs/BuildAll.lean`
- Imports (4): `CNNA.PillarA.Handoff.Inputs.B_to_A`, `CNNA.PillarA.Handoff.Inputs.C_to_A`, `CNNA.PillarA.Handoff.Inputs.D_to_A`, `CNNA.PillarA.Handoff.Inputs.E_to_A`
- Internal imports (4): `CNNA.PillarA.Handoff.Inputs.B_to_A`, `CNNA.PillarA.Handoff.Inputs.C_to_A`, `CNNA.PillarA.Handoff.Inputs.D_to_A`, `CNNA.PillarA.Handoff.Inputs.E_to_A`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Notation`

### `CNNA.PillarA.Handoff.Inputs.C_to_A`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Inputs/C_to_A.lean`
- Imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- Internal imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Inputs.BuildAll`

### `CNNA.PillarA.Handoff.Inputs.D_to_A`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Inputs/D_to_A.lean`
- Imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- Internal imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Inputs.BuildAll`

### `CNNA.PillarA.Handoff.Inputs.E_to_A`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Inputs/E_to_A.lean`
- Imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- Internal imports (1): `CNNA.PillarA.Handoff.Outputs.Closed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Inputs.BuildAll`

### `CNNA.PillarA.Handoff.Notation`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Notation.lean`
- Imports (6): `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Inputs.BuildAll`, `CNNA.PillarA.Handoff.Outputs.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`
- Internal imports (6): `CNNA.PillarA.Handoff.Core.BuildAll`, `CNNA.PillarA.Handoff.Inputs.BuildAll`, `CNNA.PillarA.Handoff.Outputs.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`, `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Handoff.Outputs.A_to_B`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/A_to_B.lean`
- Imports (1): `CNNA.PillarA.Handoff.Core.Step1MathData`
- Internal imports (1): `CNNA.PillarA.Handoff.Core.Step1MathData`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.Outputs.BuildAll`, `CNNA.PillarA.Handoff.Outputs.Closed`

### `CNNA.PillarA.Handoff.Outputs.A_to_C`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/A_to_C.lean`
- Imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- Internal imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Outputs.BuildAll`

### `CNNA.PillarA.Handoff.Outputs.A_to_CayleyDickson`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/A_to_CayleyDickson.lean`
- Imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- Internal imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Outputs.BuildAll`

### `CNNA.PillarA.Handoff.Outputs.A_to_D`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/A_to_D.lean`
- Imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- Internal imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Outputs.BuildAll`

### `CNNA.PillarA.Handoff.Outputs.A_to_E`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/A_to_E.lean`
- Imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- Internal imports (1): `CNNA.PillarA.Handoff.Core.SectorExport`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.Outputs.BuildAll`

### `CNNA.PillarA.Handoff.Outputs.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/BuildAll.lean`
- Imports (6): `CNNA.PillarA.Handoff.Outputs.A_to_B`, `CNNA.PillarA.Handoff.Outputs.A_to_C`, `CNNA.PillarA.Handoff.Outputs.A_to_CayleyDickson`, `CNNA.PillarA.Handoff.Outputs.A_to_D`, `CNNA.PillarA.Handoff.Outputs.A_to_E`, `CNNA.PillarA.Handoff.Outputs.Closed`
- Internal imports (6): `CNNA.PillarA.Handoff.Outputs.A_to_B`, `CNNA.PillarA.Handoff.Outputs.A_to_C`, `CNNA.PillarA.Handoff.Outputs.A_to_CayleyDickson`, `CNNA.PillarA.Handoff.Outputs.A_to_D`, `CNNA.PillarA.Handoff.Outputs.A_to_E`, `CNNA.PillarA.Handoff.Outputs.Closed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Notation`

### `CNNA.PillarA.Handoff.Outputs.Closed`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/Outputs/Closed.lean`
- Imports (1): `CNNA.PillarA.Handoff.Outputs.A_to_B`
- Internal imports (1): `CNNA.PillarA.Handoff.Outputs.A_to_B`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (6): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`, `CNNA.PillarA.Handoff.Inputs.B_to_A`, `CNNA.PillarA.Handoff.Inputs.C_to_A`, `CNNA.PillarA.Handoff.Inputs.D_to_A`, `CNNA.PillarA.Handoff.Inputs.E_to_A`, `CNNA.PillarA.Handoff.Outputs.BuildAll`

### `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/ProofObligationI/BuildAll.lean`
- Imports (1): `CNNA.PillarA.Handoff.ProofObligationI.Completion`
- Internal imports (1): `CNNA.PillarA.Handoff.ProofObligationI.Completion`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Notation`

### `CNNA.PillarA.Handoff.ProofObligationI.Completion`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/ProofObligationI/Completion.lean`
- Imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- Internal imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.ProofObligationI.BuildAll`

### `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/ProofObligationII/BuildAll.lean`
- Imports (1): `CNNA.PillarA.Handoff.ProofObligationII.Preparation`
- Internal imports (1): `CNNA.PillarA.Handoff.ProofObligationII.Preparation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Notation`

### `CNNA.PillarA.Handoff.ProofObligationII.Preparation`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/ProofObligationII/Preparation.lean`
- Imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- Internal imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.ProofObligationII.BuildAll`

### `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/ProofObligationIII/BuildAll.lean`
- Imports (1): `CNNA.PillarA.Handoff.ProofObligationIII.Preparation`
- Internal imports (1): `CNNA.PillarA.Handoff.ProofObligationIII.Preparation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Handoff.BuildAll`, `CNNA.PillarA.Handoff.Notation`

### `CNNA.PillarA.Handoff.ProofObligationIII.Preparation`

- Group: `PillarA/Handoff`
- Path: `CNNA/PillarA/Handoff/ProofObligationIII/Preparation.lean`
- Imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- Internal imports (1): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Handoff.ProofObligationIII.BuildAll`

### `CNNA.PillarA.Network.BuildAll`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/BuildAll.lean`
- Imports (6): `CNNA.PillarA.Network.InfiniteCarrier`, `CNNA.PillarA.Network.Notation`, `CNNA.PillarA.Network.RegionNet`, `CNNA.PillarA.Network.RelativeEntropyFlow`, `CNNA.PillarA.Network.SectorChannels`, `CNNA.PillarA.Network.SectorSysEnv`
- Internal imports (6): `CNNA.PillarA.Network.InfiniteCarrier`, `CNNA.PillarA.Network.Notation`, `CNNA.PillarA.Network.RegionNet`, `CNNA.PillarA.Network.RelativeEntropyFlow`, `CNNA.PillarA.Network.SectorChannels`, `CNNA.PillarA.Network.SectorSysEnv`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Network.InfiniteCarrier`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/InfiniteCarrier.lean`
- Imports (1): `CNNA.PillarA.Network.RegionNet`
- Internal imports (1): `CNNA.PillarA.Network.RegionNet`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Handoff.Core.SectorExport`, `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Network.Notation`, `CNNA.PillarA.Structural.CayleyDickson.Source`

### `CNNA.PillarA.Network.Notation`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/Notation.lean`
- Imports (4): `CNNA.PillarA.Network.InfiniteCarrier`, `CNNA.PillarA.Network.RegionNet`, `CNNA.PillarA.Network.RelativeEntropyFlow`, `CNNA.PillarA.Network.SectorChannels`
- Internal imports (4): `CNNA.PillarA.Network.InfiniteCarrier`, `CNNA.PillarA.Network.RegionNet`, `CNNA.PillarA.Network.RelativeEntropyFlow`, `CNNA.PillarA.Network.SectorChannels`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Notation`

### `CNNA.PillarA.Network.RegionNet`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/RegionNet.lean`
- Imports (1): `CNNA.PillarA.Sectors.SectorSplit`
- Internal imports (1): `CNNA.PillarA.Sectors.SectorSplit`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Network.InfiniteCarrier`, `CNNA.PillarA.Network.Notation`

### `CNNA.PillarA.Network.RelativeEntropyFlow`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/RelativeEntropyFlow.lean`
- Imports (1): `CNNA.PillarA.Network.SectorSysEnv`
- Internal imports (1): `CNNA.PillarA.Network.SectorSysEnv`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Network.Notation`

### `CNNA.PillarA.Network.SectorChannels`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/SectorChannels.lean`
- Imports (1): `CNNA.PillarA.Coupling.GeneralizedDtN`
- Internal imports (1): `CNNA.PillarA.Coupling.GeneralizedDtN`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Network.Notation`, `CNNA.PillarA.Network.SectorSysEnv`

### `CNNA.PillarA.Network.SectorSysEnv`

- Group: `PillarA/Network`
- Path: `CNNA/PillarA/Network/SectorSysEnv.lean`
- Imports (1): `CNNA.PillarA.Network.SectorChannels`
- Internal imports (1): `CNNA.PillarA.Network.SectorChannels`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Network.BuildAll`, `CNNA.PillarA.Network.RelativeEntropyFlow`

### `CNNA.PillarA.Notation`

- Group: `PillarA`
- Path: `CNNA/PillarA/Notation.lean`
- Imports (11): `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Coupling.Notation`, `CNNA.PillarA.DtN.Notation`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Geometry.Notation`, `CNNA.PillarA.Handoff.Notation`, `CNNA.PillarA.Network.Notation`, `CNNA.PillarA.Sectors.Notation`, `CNNA.PillarA.ToC.Notation`
- Internal imports (11): `CNNA.PillarA.Arithmetic.Notation`, `CNNA.PillarA.Closure.Notation`, `CNNA.PillarA.Coupling.Notation`, `CNNA.PillarA.DtN.Notation`, `CNNA.PillarA.Finite.Notation`, `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.Geometry.Notation`, `CNNA.PillarA.Handoff.Notation`, `CNNA.PillarA.Network.Notation`, `CNNA.PillarA.Sectors.Notation`, `CNNA.PillarA.ToC.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.Notation`, `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Sectors.BranchPatch`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/BranchPatch.lean`
- Imports (1): `CNNA.PillarA.DtN.DtNStabilized`
- Internal imports (1): `CNNA.PillarA.DtN.DtNStabilized`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Sectors.ComplementSectorFamily`

### `CNNA.PillarA.Sectors.BranchingSelector`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/BranchingSelector.lean`
- Imports (1): `CNNA.PillarA.Sectors.UVSpectralSelector`
- Internal imports (1): `CNNA.PillarA.Sectors.UVSpectralSelector`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Closure.ParameterClosure`, `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Sectors.Notation`

### `CNNA.PillarA.Sectors.BranchingWitness`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/BranchingWitness.lean`
- Imports (1): `CNNA.PillarA.Sectors.SectorSplit`
- Internal imports (1): `CNNA.PillarA.Sectors.SectorSplit`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Sectors.SelectedBranching`

### `CNNA.PillarA.Sectors.BuildAll`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/BuildAll.lean`
- Imports (8): `CNNA.PillarA.Sectors.BranchPatch`, `CNNA.PillarA.Sectors.BranchingSelector`, `CNNA.PillarA.Sectors.BranchingWitness`, `CNNA.PillarA.Sectors.ComplementSectorFamily`, `CNNA.PillarA.Sectors.Notation`, `CNNA.PillarA.Sectors.SectorSplit`, `CNNA.PillarA.Sectors.SelectedBranching`, `CNNA.PillarA.Sectors.UVSpectralSelector`
- Internal imports (8): `CNNA.PillarA.Sectors.BranchPatch`, `CNNA.PillarA.Sectors.BranchingSelector`, `CNNA.PillarA.Sectors.BranchingWitness`, `CNNA.PillarA.Sectors.ComplementSectorFamily`, `CNNA.PillarA.Sectors.Notation`, `CNNA.PillarA.Sectors.SectorSplit`, `CNNA.PillarA.Sectors.SelectedBranching`, `CNNA.PillarA.Sectors.UVSpectralSelector`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Sectors.ComplementSectorFamily`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/ComplementSectorFamily.lean`
- Imports (1): `CNNA.PillarA.Sectors.BranchPatch`
- Internal imports (1): `CNNA.PillarA.Sectors.BranchPatch`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Sectors.SectorSplit`

### `CNNA.PillarA.Sectors.Notation`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/Notation.lean`
- Imports (1): `CNNA.PillarA.Sectors.BranchingSelector`
- Internal imports (1): `CNNA.PillarA.Sectors.BranchingSelector`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Notation`, `CNNA.PillarA.Sectors.BuildAll`

### `CNNA.PillarA.Sectors.SectorSplit`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/SectorSplit.lean`
- Imports (1): `CNNA.PillarA.Sectors.ComplementSectorFamily`
- Internal imports (1): `CNNA.PillarA.Sectors.ComplementSectorFamily`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Coupling.GeneralizedDtN`, `CNNA.PillarA.Network.RegionNet`, `CNNA.PillarA.Sectors.BranchingWitness`, `CNNA.PillarA.Sectors.BuildAll`

### `CNNA.PillarA.Sectors.SelectedBranching`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/SelectedBranching.lean`
- Imports (1): `CNNA.PillarA.Sectors.BranchingWitness`
- Internal imports (1): `CNNA.PillarA.Sectors.BranchingWitness`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Sectors.BuildAll`, `CNNA.PillarA.Sectors.UVSpectralSelector`

### `CNNA.PillarA.Sectors.UVSpectralSelector`

- Group: `PillarA/Sectors`
- Path: `CNNA/PillarA/Sectors/UVSpectralSelector.lean`
- Imports (1): `CNNA.PillarA.Sectors.SelectedBranching`
- Internal imports (1): `CNNA.PillarA.Sectors.SelectedBranching`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Sectors.BranchingSelector`, `CNNA.PillarA.Sectors.BuildAll`

### `CNNA.PillarA.Structural.BuildAll`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/BuildAll.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.Structural.CayleyDickson.BuildAll`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/BuildAll.lean`
- Imports (35): `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`, `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqSimultaneousSystem`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`, `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`, `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`, `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`, `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`, `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot1AlternativeLaw`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`, `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`, `CNNA.PillarA.Structural.CayleyDickson.Source`
- Internal imports (35): `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`, `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqSimultaneousSystem`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`, `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`, `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`, `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`, `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`, `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot1AlternativeLaw`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`, `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`, `CNNA.PillarA.Structural.CayleyDickson.Source`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Structural.BuildAll`

### `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6AdditionalFinding.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.Source`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.Source`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`

### `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6AlternativeLawScaffold.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalDivisionFromNormSq.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalIdealAlgebraizationPath.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalNormSqBlockSystem.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqSimultaneousSystem`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalNormSqCandidate.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalNormSqDefined.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (4): `CNNA.PillarA.Arithmetic.CayleyDickson.ArithmeticCDBridge`, `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqReduction`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalNormSqReduction.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqSimultaneousSystem`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalNormSqSimultaneousSystem.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqBlockSystem`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalProductMultiplicationCandidate.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot1AlternativeLaw`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalProductSurfaceCandidate.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalScalarPart.lean`
- Imports (2): `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`
- Internal imports (2): `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqDefined`

### `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalStar`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CanonicalStar.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalScalarPart`

### `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6CayleyDicksonIdentification.lean`
- Imports (2): `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`
- Internal imports (2): `CNNA.PillarA.Foundation.MatrixNorms`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`

### `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6ConcreteSeeds.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`

### `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6DivisionConclusionDecomposition.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`

### `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6DivisionConclusionScaffold.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`, `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`, `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`

### `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6DivisionUpgrade.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`, `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalIdealAlgebraizationPath`, `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`

### `CNNA.PillarA.Structural.CayleyDickson.S6FullAlternativeLawBoundary`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6FullAlternativeLawBoundary.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6AlternativeLawScaffold`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductSurfaceCandidate`

### `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6HurwitzStopSeed.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`

### `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6NormDefinitenessScaffold.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`

### `CNNA.PillarA.Structural.CayleyDickson.S6NormMultiplicativityScaffold`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6NormMultiplicativityScaffold.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`

### `CNNA.PillarA.Structural.CayleyDickson.S6NormUpgrade`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6NormUpgrade.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionUpgrade`, `CNNA.PillarA.Structural.CayleyDickson.S6NormDefinitenessScaffold`

### `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6OctonionicSeed.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`

### `CNNA.PillarA.Structural.CayleyDickson.S6PhaseICompactClosure`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6PhaseICompactClosure.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionScaffold`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`

### `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6ProofDutyGroups.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`, `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge`

### `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6QuaternionicSeed.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Arithmetic.Convergence.QuaternionRamanujanInterface`, `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed`

### `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6ResearchReadinessBridge.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`

### `CNNA.PillarA.Structural.CayleyDickson.S6ResearchSchema`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6ResearchSchema.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CayleyDicksonIdentification`, `CNNA.PillarA.Structural.CayleyDickson.S6ResearchReadinessBridge`

### `CNNA.PillarA.Structural.CayleyDickson.S6RoleCompositionSeed`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6RoleCompositionSeed.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6QuaternionicSeed`

### `CNNA.PillarA.Structural.CayleyDickson.S6Slot1AlternativeLaw`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6Slot1AlternativeLaw.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalProductMultiplicationCandidate`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`

### `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6Slot2NormSqMultiplicativity.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalNormSqCandidate`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`

### `CNNA.PillarA.Structural.CayleyDickson.S6Slot3DivisionFromNormSqLogic`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6Slot3DivisionFromNormSqLogic.lean`
- Imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`
- Internal imports (2): `CNNA.PillarA.Structural.CayleyDickson.S6DivisionConclusionDecomposition`, `CNNA.PillarA.Structural.CayleyDickson.S6Slot2NormSqMultiplicativity`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6CanonicalDivisionFromNormSq`

### `CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/S6StatusLayer.lean`
- Imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`
- Internal imports (1): `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Handoff.CayleyDicksonAdapter`, `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6ConcreteSeeds`

### `CNNA.PillarA.Structural.CayleyDickson.Source`

- Group: `PillarA/Structural`
- Path: `CNNA/PillarA/Structural/CayleyDickson/Source.lean`
- Imports (3): `CNNA.PillarA.Closure.RegularizationClosure`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Network.InfiniteCarrier`
- Internal imports (3): `CNNA.PillarA.Closure.RegularizationClosure`, `CNNA.PillarA.Coupling.MultiSchur`, `CNNA.PillarA.Network.InfiniteCarrier`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Structural.CayleyDickson.BuildAll`, `CNNA.PillarA.Structural.CayleyDickson.S6AdditionalFinding`

### `CNNA.PillarA.ToC.Addressing`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/Addressing.lean`
- Imports (2): `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.ToC.Contract`
- Internal imports (2): `CNNA.PillarA.Foundation.Notation`, `CNNA.PillarA.ToC.Contract`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Geometry.LCPMeasure`, `CNNA.PillarA.ToC.BuildAll`, `CNNA.PillarA.ToC.IdealAddressEquiv`

### `CNNA.PillarA.ToC.BuildAll`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/BuildAll.lean`
- Imports (7): `CNNA.PillarA.ToC.Addressing`, `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.ConcreteIdeal`, `CNNA.PillarA.ToC.Contract`, `CNNA.PillarA.ToC.GeneratedBranchFamily`, `CNNA.PillarA.ToC.IdealAddressEquiv`, `CNNA.PillarA.ToC.Notation`
- Internal imports (7): `CNNA.PillarA.ToC.Addressing`, `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.ConcreteIdeal`, `CNNA.PillarA.ToC.Contract`, `CNNA.PillarA.ToC.GeneratedBranchFamily`, `CNNA.PillarA.ToC.IdealAddressEquiv`, `CNNA.PillarA.ToC.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.Core.Source`, `CNNA.PillarA.BuildAll`

### `CNNA.PillarA.ToC.Concrete`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/Concrete.lean`
- Imports (4): `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.ToC.ConcreteIdeal`, `CNNA.PillarA.ToC.IdealAddressEquiv`
- Internal imports (4): `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.ToC.ConcreteIdeal`, `CNNA.PillarA.ToC.IdealAddressEquiv`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.ToC.BuildAll`, `CNNA.PillarA.ToC.GeneratedBranchFamily`, `CNNA.PillarA.ToC.Notation`

### `CNNA.PillarA.ToC.ConcreteIdeal`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/ConcreteIdeal.lean`
- Imports (2): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.ToC.IdealAddressEquiv`
- Internal imports (2): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.ToC.IdealAddressEquiv`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.ToC.BuildAll`, `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.Notation`

### `CNNA.PillarA.ToC.Contract`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/Contract.lean`
- Imports (2): `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.Notation`
- Internal imports (2): `CNNA.PillarA.Foundation.Determinism`, `CNNA.PillarA.Foundation.Notation`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.ToC.Addressing`, `CNNA.PillarA.ToC.BuildAll`

### `CNNA.PillarA.ToC.GeneratedBranchFamily`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/GeneratedBranchFamily.lean`
- Imports (3): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.ToC.Concrete`
- Internal imports (3): `CNNA.PillarA.Foundation.ConcreteSubstrate`, `CNNA.PillarA.Foundation.LevelVariableSubstrate`, `CNNA.PillarA.ToC.Concrete`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (2): `CNNA.PillarA.Arithmetic.Smoke.GeneratedSource`, `CNNA.PillarA.ToC.BuildAll`

### `CNNA.PillarA.ToC.IdealAddressEquiv`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/IdealAddressEquiv.lean`
- Imports (1): `CNNA.PillarA.ToC.Addressing`
- Internal imports (1): `CNNA.PillarA.ToC.Addressing`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.ToC.BuildAll`, `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.ConcreteIdeal`

### `CNNA.PillarA.ToC.Notation`

- Group: `PillarA/ToC`
- Path: `CNNA/PillarA/ToC/Notation.lean`
- Imports (2): `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.ConcreteIdeal`
- Internal imports (2): `CNNA.PillarA.ToC.Concrete`, `CNNA.PillarA.ToC.ConcreteIdeal`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (3): `CNNA.PillarA.Finite.CutSpec`, `CNNA.PillarA.Notation`, `CNNA.PillarA.ToC.BuildAll`

### `CNNA.PillarB`

- Group: `PillarB`
- Path: `CNNA/PillarB.lean`
- Imports (1): `CNNA.PillarB.BuildAll`
- Internal imports (1): `CNNA.PillarB.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.PillarB.BuildAll`

- Group: `PillarB`
- Path: `CNNA/PillarB/BuildAll.lean`
- Imports (0): none
- Internal imports (0): none
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarB`

### `CNNA.PillarC`

- Group: `PillarC`
- Path: `CNNA/PillarC.lean`
- Imports (1): `CNNA.PillarC.BuildAll`
- Internal imports (1): `CNNA.PillarC.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.PillarC.BuildAll`

- Group: `PillarC`
- Path: `CNNA/PillarC/BuildAll.lean`
- Imports (0): none
- Internal imports (0): none
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarC`

### `CNNA.PillarD`

- Group: `PillarD`
- Path: `CNNA/PillarD.lean`
- Imports (1): `CNNA.PillarD.BuildAll`
- Internal imports (1): `CNNA.PillarD.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.PillarD.BuildAll`

- Group: `PillarD`
- Path: `CNNA/PillarD/BuildAll.lean`
- Imports (0): none
- Internal imports (0): none
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarD`

### `CNNA.PillarE`

- Group: `PillarE`
- Path: `CNNA/PillarE.lean`
- Imports (1): `CNNA.PillarE.BuildAll`
- Internal imports (1): `CNNA.PillarE.BuildAll`
- External imports (0): none
- Missing internal imports (0): none
- Imported by (0): none

### `CNNA.PillarE.BuildAll`

- Group: `PillarE`
- Path: `CNNA/PillarE/BuildAll.lean`
- Imports (0): none
- Internal imports (0): none
- External imports (0): none
- Missing internal imports (0): none
- Imported by (1): `CNNA.PillarE`
