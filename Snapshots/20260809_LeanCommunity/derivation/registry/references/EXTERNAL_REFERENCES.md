# External references and exact use contexts

Generated from the TSV registries; the TSV files are authoritative.

## EXT-REF-DKP-001 — `SugiyamaSato2023DirectedKron`

Tomohiro Sugiyama and Kazuhiro Sato, *Kron Reduction and Effective Resistance of Directed Graphs*, SIAM Journal on Matrix Analysis and Applications 44(1) (2023), 270--292. DOI: `10.1137/22M1480823`. arXiv: `2202.12560v2`; arXiv DOI: `10.48550/arXiv.2202.12560`.

Canonical URL: https://doi.org/10.1137/22M1480823.
Alternate/direct source: https://arxiv.org/abs/2202.12560v2.
Verification: `VERIFIED_PRIMARY_PUBLISHER_AND_ARXIV` against SIAM publisher record; arXiv v2 record; arXiv v2 PDF pages 4, 5, 7.
Snapshot SHA-256: `e05901199cba236bdd615a7cbee677ca0ef8ab0309511e0a8d65d6c0a0aa0264`.

Uses:
- `EXT-USE-P001-DKP-MAIN` — P001 1.3.9.1 / MAIN_TEX: Directed Kron well-posedness, Laplacian closure, path-edge equivalence, and strong-connectivity preservation. Locator: Definition~3.2; Lemmas~3.3--3.4; Theorem~3.9.
- `EXT-USE-P001-DKP-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Exact source provenance and theorem-to-CNNA assumption map for the analytical positivity closure. Locator: Definition 3.2; Lemmas 3.3--3.4; Theorem 3.9; arXiv v2 PDF pp. 4, 5, 7.
- `EXT-USE-O001-NOVELTY-DIRECTED-INFOBOX` — O001 1.3.7 / MAIN_TEX: Directed Kron reduction is established recent work. Locator: Definition~3.2; Lemmas~3.3--3.4; Theorem~3.9.

## EXT-REF-LEAN-001 — `LeanReference431InductiveTypes`

The Lean 4 Development Team, *The Lean Language Reference: Inductive Types*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_OFFICIAL_DOCUMENTATION`. Stable source: `https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/`; accessed 2026-07-31.

Canonical URL: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/.
Alternate/direct source: https://lean-lang.org/doc/reference/latest/releases/v4.31.0/.
Verification: `VERIFIED_OFFICIAL_DOCUMENTATION` against Official Lean Language Reference; official Lean 4.31.0 release notes.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-M004-LEAN-INDUCTIVE` — M004 1.3.10 / SUPPLEMENT_MD: Documents the official source consulted when replacing unavailable List.Forall₂ with a module-local inductive relation. Locator: Section 4.4, constructors and generated recursors.

## EXT-REF-LEAN-003 — `Lean431ReleaseNotes`

The Lean 4 Development Team, *Lean 4.31.0 Release Notes*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_RELEASE`. Stable source: `https://lean-lang.org/doc/reference/latest/releases/v4.31.0/`; accessed 2026-07-31.

Canonical URL: https://lean-lang.org/doc/reference/latest/releases/v4.31.0/.
Alternate/direct source: https://github.com/leanprover/lean4.
Verification: `VERIFIED_OFFICIAL_RELEASE_DOCUMENTATION` against Official Lean 4.31.0 release notes.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-TOOLCHAIN-LEAN431` — PROJECT  / REGISTRY_ONLY: Binds consulted official Lean documentation to the exact project toolchain generation. Locator: Lean 4.31.0 release notes, released 2026-06-13.

## EXT-REF-MATHLIB-001 — `MathlibSchurComplementFabf563a`

Alexander Bentkamp, Eric Wieser, Jeremy Avigad, and Johan Commelin, *Mathlib module: Matrix.SchurComplement*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/SchurComplement.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/SchurComplement.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean.
Verification: `VERIFIED_OFFICIAL_SOURCE_COMMIT` against Pinned GitHub source commit; generated mathlib documentation.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Records the exact mathlib Schur-complement API boundary used by the declared contract. Locator: module header and main results; pinned source commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `EXT-USE-P001-MATHLIB-SCHUR-MAIN` — P001 1.3.9.1 / MAIN_TEX: Records the Schur-complement API boundary after the directed maximum-principle proof kernel triviality. Locator: module header and main results.

## EXT-REF-FOUND-001 — `vonNeumann1923TransfiniteNumbers`

John von Neumann, *Zur Einführung der transfiniten Zahlen*, Acta Litterarum ac Scientiarum Regiae Universitatis Hungaricae Francisco-Josephinae, Sectio Scientiarum Mathematicarum 1 (1923), 199--208. DOI status: `NOT_ASSIGNED_HISTORICAL_ARTICLE`.

Canonical URL: https://acta.bibl.u-szeged.hu/13294/.
Alternate/direct source: https://acta.bibl.u-szeged.hu/13294/1/math_001_199-208.pdf.
Verification: `VERIFIED_PRIMARY_REPOSITORY_AND_SOURCE_PDF` against Official University of Szeged repository record; primary-source PDF printed pp. 199--200.
Snapshot SHA-256: `e2b9b4fbfdaa1ba7eef1c9c5cca13aff7f1ae8a195122691b501dc1f2a50e6c5`.

Uses:
- `EXT-USE-C003-VONNEUMANN-INFOBOX` — C003 1.1.5 / MAIN_TEX: Primary-source basis for comparing the finite von-Neumann successor chain with the externally adjoined unary address grammar. Locator: Introduction and displayed finite ordinals, pp.~199--200.

## EXT-REF-GRAPH-001 — `Diestel2025GraphTheory`

Reinhard Diestel, *Graph Theory*, 6 ed., Graduate Texts in Mathematics 173, Springer Berlin, Heidelberg (2025). ISBN `978-3-662-70107-2`. DOI: `10.1007/978-3-662-70107-2`.

Canonical URL: https://doi.org/10.1007/978-3-662-70107-2.
Alternate/direct source: https://diestel-graph-theory.com/basic.html.
Verification: `VERIFIED_OFFICIAL_PUBLISHER_AND_AUTHOR_SITE` against Springer Nature book record; author-hosted sixth-edition preview.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C003-TREE-DIRECT` — C003 1.1.5 / MAIN_TEX: The bounded word grammar is a finite rooted ordered tree. Locator: Ch.~1, The Basics.
- `EXT-USE-O001-NOVELTY-GRAPH-INFOBOX` — O001 1.3.7 / MAIN_TEX: Rooted finite graph structure is standard. Locator: Ch.~1.

## EXT-REF-CAT-001 — `MacLane1998Categories`

Saunders Mac Lane, *Categories for the Working Mathematician*, 2 ed., Graduate Texts in Mathematics 5, Springer New York (1998). DOI: `10.1007/978-1-4757-4721-8`.

Canonical URL: https://doi.org/10.1007/978-1-4757-4721-8.
Alternate/direct source: not recorded.
Verification: `VERIFIED_OFFICIAL_PUBLISHER` against Springer Nature book record and table of contents.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C001-CATEGORY-INFOBOX` — C001 1.1.3 / MAIN_TEX: Empty and singleton objects have opposite universal roles in Set. Locator: Chs.~I and III, categories and universal constructions.

## EXT-REF-WORDS-001 — `Lothaire1997CombinatoricsWords`

M. Lothaire, *Combinatorics on Words*, 2 ed., Cambridge Mathematical Library, Cambridge University Press (1997). ISBN `9780521599245`. DOI: `10.1017/CBO9780511566097`.

Canonical URL: https://doi.org/10.1017/CBO9780511566097.
Alternate/direct source: https://www.cambridge.org/core/books/combinatorics-on-words/6FEBB4FCCB43895CCEFA8D69A0983374.
Verification: `VERIFIED_OFFICIAL_PUBLISHER` against Cambridge Core book record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C003-WORDS-DIRECT` — C003 1.1.5 / MAIN_TEX: Finite provenance addresses are words over a finite alphabet. Locator: Ch.~1 and free-monoid background.
- `EXT-USE-C018-SHORTLEX-DIRECT` — C018 1.1.6 / MAIN_TEX: C018 is length-first lexicographic order on finite words. Locator: Ch.~1, finite words and lexicographic order.
- `EXT-USE-C018-WORDS-INFOBOX` — C018 1.1.6 / MAIN_TEX: Address words admit shortlex ordering and fixed-depth base-b ranking. Locator: Ch.~1.
- `EXT-USE-O001-NOVELTY-WORDS-INFOBOX` — O001 1.3.7 / MAIN_TEX: Finite word grammars and lexicographic orders are standard. Locator: Ch.~1.
- `EXT-USE-P002-WORDS-MAIN` — P002 1.1.6.1 / MAIN_TEX: Lexicographic order of finite provenance words is standard; P002 proves the CNNA strict-total closure internally. Locator: Ch.~1, finite words and lexicographic order.
- `EXT-USE-P002-WORDS-SUPP` — P002 1.1.6.1 / SUPPLEMENT_MD: Standard finite-word lexicographic context for the P002 static order theorem. Locator: Ch. 1, finite words and lexicographic order.

## EXT-REF-DIGRAPH-001 — `BangJensenGutin2009Digraphs`

Jørgen Bang-Jensen and Gregory Z. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2 ed., Springer Monographs in Mathematics, Springer London (2009). DOI: `10.1007/978-1-84800-998-1`.

Canonical URL: https://doi.org/10.1007/978-1-84800-998-1.
Alternate/direct source: https://www.cs.rhul.ac.uk/books/dbook/.
Verification: `VERIFIED_OFFICIAL_PUBLISHER_AND_AUTHOR_SITE` against Springer Nature book record; author-hosted book page.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C005-DIGRAPH-DIRECT` — C005 1.3.1 / MAIN_TEX: C005 is a finite positively weighted digraph with a distinguished provenance backbone. Locator: Ch.~1, pp.~1--30.

## EXT-REF-SCHUR-001 — `Zhang2005SchurComplement`

Fuzhen Zhang (ed.), *The Schur Complement and Its Applications*, 1 ed., Numerical Methods and Algorithms 4, Springer New York (2005). ISBN `978-0-387-24271-2`. DOI: `10.1007/b105056`.

Canonical URL: https://doi.org/10.1007/b105056.
Alternate/direct source: not recorded.
Verification: `VERIFIED_OFFICIAL_PUBLISHER` against Springer Nature book record and chapter table of contents.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C006-SCHUR-DIRECT` — C006 1.3.3 / MAIN_TEX: The block formula used by C006 is the standard Schur complement. Locator: Horn--Zhang, Basic Properties, pp.~17--46.
- `EXT-USE-M002-PARTIAL-DIRECT` — M002 1.3.5 / MAIN_TEX: A classical Schur complement requires an admissible/invertible eliminated block. Locator: Basic Properties, pp.~17--46.
- `EXT-USE-O001-NOVELTY-SCHUR-INFOBOX` — O001 1.3.7 / MAIN_TEX: Schur elimination is standard linear algebra. Locator: Basic Properties, pp.~17--46.

## EXT-REF-EXACT-001 — `Bareiss1968ExactElimination`

Erwin H. Bareiss, *Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination*, Mathematics of Computation 22(103) (1968), 565--578. DOI: `10.1090/S0025-5718-1968-0226829-0`.

Canonical URL: https://doi.org/10.1090/S0025-5718-1968-0226829-0.
Alternate/direct source: https://www.ams.org/mcom/1968-22-103/S0025-5718-1968-0226829-0/.
Verification: `VERIFIED_OFFICIAL_PUBLISHER` against American Mathematical Society article record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C006-EXACT-INFOBOX` — C006 1.3.3 / MAIN_TEX: Exact elimination has a classical fraction-preserving/fraction-free lineage. Locator: pp.~565--578.

## EXT-REF-KRON-001 — `DoerflerBullo2013KronReduction`

Florian Dörfler and Francesco Bullo, *Kron Reduction of Graphs with Applications to Electrical Networks*, IEEE Transactions on Circuits and Systems I: Regular Papers 60(1) (2013), 150--163. DOI: `10.1109/TCSI.2012.2215780`. arXiv: `1102.2950v1`; arXiv DOI: `10.48550/arXiv.1102.2950`.

Canonical URL: https://doi.org/10.1109/TCSI.2012.2215780.
Alternate/direct source: https://arxiv.org/abs/1102.2950v1.
Verification: `VERIFIED_IEEE_AND_ARXIV` against IEEE Circuits and Systems Society record; arXiv record and manuscript.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C006-KRON-DIRECT` — C006 1.3.3 / MAIN_TEX: Network elimination by the same Schur formula is called Kron reduction and is identified with a DtN map. Locator: Sec.~I, Eqs.~(1)--(2), pp.~150--151.
- `EXT-USE-M005-SCALE-INFOBOX` — M005 1.2.6 / MAIN_TEX: Network Laplacians and their Kron-reduced responses are linear in conductances. Locator: Sec.~I, current-balance and reduced conductance equations.
- `EXT-USE-C006-FOURNAMES-INFOBOX` — C006 1.3.3 / MAIN_TEX: The same block elimination appears as Gaussian elimination, Schur complement, DtN map, and Kron reduction. Locator: Sec.~I, pp.~150--151.

## EXT-REF-LAPLACIAN-001 — `AgaevChebotarev2005NonsymmetricLaplacian`

Rafig Agaev and Pavel Chebotarev, *On the Spectra of Nonsymmetric Laplacian Matrices*, Linear Algebra and its Applications 399 (2005), 157--168. DOI: `10.1016/j.laa.2004.09.003`. arXiv: `math/0508176v1`; arXiv DOI: `10.48550/arXiv.math/0508176`.

Canonical URL: https://doi.org/10.1016/j.laa.2004.09.003.
Alternate/direct source: https://arxiv.org/abs/math/0508176v1.
Verification: `VERIFIED_ELSEVIER_AND_ARXIV` against Elsevier record; arXiv metadata and abstract.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C007-LAPLACIAN-DIRECT` — C007 1.3.6 / MAIN_TEX: C007 uses the standard row-sum-zero nonsymmetric Laplacian convention. Locator: Abstract and Sec.~1.

## EXT-REF-MARKOV-001 — `Norris1997MarkovChains`

J. R. Norris, *Markov Chains*, 1 ed., Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press (1997). ISBN `9780511810633`. DOI: `10.1017/CBO9780511810633`.

Canonical URL: https://doi.org/10.1017/CBO9780511810633.
Alternate/direct source: https://www.cambridge.org/core/books/markov-chains/A3F966B10633A32C8F06F37158031739.
Verification: `VERIFIED_OFFICIAL_PUBLISHER` against Cambridge Core book and chapter records.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C007-MARKOV-INFOBOX` — C007 1.3.6 / MAIN_TEX: The negative C007 Laplacian has the sign pattern of a continuous-time Markov generator. Locator: Ch.~2, continuous-time Markov chains.

## EXT-REF-NETWORK-001 — `DoyleSnell1984ElectricNetworks`

Peter G. Doyle and J. Laurie Snell, *Random Walks and Electric Networks*, 1 ed., Carus Mathematical Monographs 22, Mathematical Association of America (1984). ISBN `9780883850244`. DOI: `10.5948/UPO9781614440222`. arXiv: `math/0001057v1`; arXiv DOI: `10.48550/arXiv.math/0001057`.

Canonical URL: https://doi.org/10.5948/UPO9781614440222.
Alternate/direct source: https://arxiv.org/abs/math/0001057v1.
Verification: `VERIFIED_MAA_CAMBRIDGE_AND_ARXIV` against Cambridge Core/MAA book record; arXiv record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-M005-SCALING-DIRECT` — M005 1.2.6 / MAIN_TEX: Conductance-network equations are homogeneous under a common positive conductance rescaling. Locator: Electrical network preliminaries.

## EXT-REF-RESPONSE-001 — `CurtisIngermanMorrow1998Response`

Edward B. Curtis, David Ingerman, and James A. Morrow, *Circular Planar Graphs and Resistor Networks*, Linear Algebra and its Applications 283(1--3) (1998), 115--150. DOI: `10.1016/S0024-3795(98)10087-3`.

Canonical URL: https://doi.org/10.1016/S0024-3795(98)10087-3.
Alternate/direct source: https://sites.math.washington.edu/~curtis/cim.pdf.
Verification: `VERIFIED_ELSEVIER_AND_AUTHOR_MANUSCRIPT` against Elsevier record; author-hosted primary-source PDF.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-C006-RESPONSE-DIRECT` — C006 1.3.3 / MAIN_TEX: Electrical-network response is the linear map from boundary voltages to boundary currents. Locator: Abstract and Sec.~1, p.~115.

## EXT-REF-MATHLIB-002 — `MathlibFiniteDimensionalFabf563a`

Chris Hughes, *Mathlib module: FiniteDimensional.Basic*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional/Basic.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional/Basic.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean.
Verification: `VERIFIED_OFFICIAL_SOURCE_COMMIT` against Pinned GitHub source commit; generated mathlib documentation.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-FD-MAIN` — P001 1.3.9.1 / MAIN_TEX: Finite-dimensional bridge used to turn the internally proved injectivity of the exact interior operator into kernel-verified surjectivity. Locator: finite-dimensional injectivity--surjectivity equivalence.
- `EXT-USE-P001-MATHLIB-FD-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the finite-dimensional injectivity-to-surjectivity bridge used by the kernel-verified P001 finite-linear proof. Locator: `LinearMap.surjective_of_injective`; `LinearMap.injective_iff_surjective`; pinned source commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## EXT-REF-MATHLIB-003 — `MathlibMatrixPosDefFabf563a`

Alexander Bentkamp and Mohanad Ahmed, *Mathlib module: Matrix.PosDef*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/LinearAlgebra/Matrix/PosDef.lean.
Verification: `VERIFIED_OFFICIAL_SOURCE_COMMIT` against Pinned GitHub source commit; generated mathlib documentation.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-POSDEF-MAIN` — P001 1.3.9.1 / MAIN_TEX: Explains why Hermitian positive definiteness is not the directed P001 target. Locator: module header; Matrix.PosSemidef and Matrix.PosDef definitions.
- `EXT-USE-P001-MATHLIB-POSDEF-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the deliberate exclusion of Hermitian positive definiteness from the directed P001 contract. Locator: module header; Matrix.PosSemidef and Matrix.PosDef definitions; pinned source commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## EXT-REF-MATHLIB-004 — `MathlibMatrixMulFabf563a`

Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, and Lu-Ming Zhang, *Mathlib module: Data.Matrix.Mul*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Mul.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Mul.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Data/Matrix/Mul.lean.
Verification: `VERIFIED_OFFICIAL_SOURCE_COMMIT` against Pinned GitHub source commit; generated mathlib documentation.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-MATRIX-MUL-MAIN` — P001 1.3.9.1 / MAIN_TEX: Documents the exact rectangular product mirrored by P001. Locator: rectangular row-by-column multiplication definition.
- `EXT-USE-P001-MATHLIB-MATRIX-MUL-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the transparent rectangular product at the Core-to-proof boundary. Locator: implementation notes and rectangular multiplication definition; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## EXT-REF-LEAN-004 — `LeanRatLemmas431`

The Lean 4 Development Team, *Lean core module: Init.Data.Rat.Lemmas*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Init/Data/Rat/Lemmas.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Init/Data/Rat/Lemmas.html.
Alternate/direct source: https://github.com/leanprover/lean4/blob/v4.31.0/src/Init/Data/Rat/Lemmas.lean.
Verification: `VERIFIED_OFFICIAL_GENERATED_DOCUMENTATION` against Generated Lean API documentation; official Lean source tag.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-RAT-MAIN` — P001 1.3.9.1 / MAIN_TEX: Exact constructor lemmas used by the proved C006 fraction-value bridge. Locator: rational constructor and arithmetic lemmas.
- `EXT-USE-P001-MATHLIB-RAT-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Supplies the exact constructor lemmas used to identify C006 fraction arithmetic with ℚ. Locator: Rat.mkRat_self; Rat.mkRat_eq_iff; Rat.mkRat_add_mkRat; Rat.mkRat_mul_mkRat; Rat.neg_mkRat; Lean toolchain v4.31.0.

## EXT-REF-LEAN-005 — `LeanFinFold431`

The Lean 4 Development Team, *Lean core module: Init.Data.Fin.Fold*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Init/Data/Fin/Fold.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Init/Data/Fin/Fold.html.
Alternate/direct source: https://github.com/leanprover/lean4/blob/v4.31.0/src/Init/Data/Fin/Fold.lean.
Verification: `VERIFIED_OFFICIAL_GENERATED_DOCUMENTATION` against Generated Lean API documentation; official Lean source tag.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-FINFOLD-MAIN` — P001 1.3.9.1 / MAIN_TEX: Recursion equations for the explicit native fold-to-sum proof. Locator: finite-fold recursion equations.
- `EXT-USE-P001-MATHLIB-FINFOLD-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Supplies the recursion equations used by the fold-to-sum induction. Locator: Fin.foldl_zero; Fin.foldl_succ; Lean toolchain v4.31.0.

## EXT-REF-MATHLIB-005 — `MathlibBigOperatorsFinFabf563a`

Leanprover Community, *Mathlib module: Algebra.BigOperators.Fin*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Algebra/BigOperators/Fin.lean.
Verification: `VERIFIED_OFFICIAL_SOURCE_COMMIT` against Pinned GitHub source commit; generated mathlib documentation.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-FINSUM-MAIN` — P001 1.3.9.1 / MAIN_TEX: Finite-sum induction formulas paired with the native fold equations. Locator: finite-sum recursion equations.
- `EXT-USE-P001-MATHLIB-FINSUM-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Supplies the finite-sum recursion paired with Fin.foldl. Locator: Fin.sum_univ_zero; Fin.sum_univ_succ; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## EXT-REF-MATHLIB-006 — `MathlibFinsetMaxFabf563a`

Leanprover Community, *Mathlib module: Data.Finset.Max*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Data/Finset/Max.lean.
Verification: `VERIFIED_PRIMARY_SOURCE` against OFFICIAL_MATHLIB_DOCS_AND_PINNED_GITHUB_SOURCE.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-FINSET-MAX-MAIN` — P001 1.3.9.1 / MAIN_TEX: Finite maximum selection for the the directed maximum-principle proof potential argument. Locator: \texttt{Finset.exists\_max\_image}.
- `EXT-USE-P001-MATHLIB-FINSET-MAX-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the finite maximum-selection theorem used in the directed maximum-principle proof. Locator: Finset.exists_max_image; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## EXT-REF-MATHLIB-007 — `MathlibOrderedFinsetSumsFabf563a`

Leanprover Community, *Mathlib module: Algebra.Order.BigOperators.Group.Finset*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/BigOperators/Group/Finset.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/BigOperators/Group/Finset.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean.
Verification: `VERIFIED_PRIMARY_SOURCE` against OFFICIAL_MATHLIB_DOCS_AND_PINNED_GITHUB_SOURCE.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-ORDERED-SUM-MAIN` — P001 1.3.9.1 / MAIN_TEX: Finite nonnegative-sum zero criterion in the the directed maximum-principle proof defect argument. Locator: \texttt{Finset.sum\_eq\_zero\_iff\_of\_nonneg}.
- `EXT-USE-P001-MATHLIB-ORDERED-SUM-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the exact finite ordered-sum implication used by the directed maximum-principle proof. Locator: Finset.sum_eq_zero_iff_of_nonneg; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## EXT-REF-MATHLIB-008 — `MathlibFintypeBigOperatorsFabf563a`

Leanprover Community, *Mathlib module: Data.Fintype.BigOperators*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/BigOperators.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/BigOperators.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Data/Fintype/BigOperators.lean.
Verification: `VERIFIED_PRIMARY_SOURCE` against OFFICIAL_MATHLIB_DOCS_AND_PINNED_GITHUB_SOURCE.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-SUM-TYPE-MAIN` — P001 1.3.9.1 / MAIN_TEX: Boundary/interior decomposition and selected/zero sums over the complete finite cut type. Locator: \texttt{Fintype.sum\_sum\_type}; \texttt{Fintype.sum\_eq\_single}; \texttt{Fintype.sum\_eq\_zero}.
- `EXT-USE-P001-MATHLIB-SUM-TYPE-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the sum-type decomposition and whole-Fintype selected/zero sum APIs used by P001. Locator: Fintype.sum_sum_type; Fintype.sum_eq_single; Fintype.sum_eq_zero; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## EXT-REF-MATHLIB-009 — `MathlibMatrixToLinFabf563a`

Johannes Hölzl, Patrick Massot, Casper Putz, and Anne Baanen, *Mathlib module: LinearAlgebra.Matrix.ToLin*, Leanprover Community (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html`; accessed 2026-08-03.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html.
Alternate/direct source: https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/LinearAlgebra/Matrix/ToLin.lean.
Verification: `VERIFIED_PRIMARY_SOURCE` against OFFICIAL_MATHLIB_DOCS_AND_PINNED_GITHUB_SOURCE.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-MATHLIB-MULVECLIN-MAIN` — P001 1.3.9.1 / MAIN_TEX: Records the exact bundled matrix action used by the kernel-verified finite-linear proof. Locator: \texttt{Matrix.mulVecLin}; \texttt{Matrix.mulVecLin\_apply}.
- `EXT-USE-P001-MATHLIB-MULVECLIN-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Documents the exact bundled matrix action used by the kernel-verified finite-linear proof. Locator: Matrix.mulVecLin; Matrix.mulVecLin_apply; pinned source commit fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.

## EXT-REF-LEAN-006 — `LeanInitCore431`

The Lean 4 Development Team, *Lean 4 source module: Init.Core*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://leanprover-community.github.io/mathlib4_docs/Init/Core.html`; accessed 2026-08-05.

Canonical URL: https://leanprover-community.github.io/mathlib4_docs/Init/Core.html.
Alternate/direct source: https://github.com/leanprover/lean4/blob/v4.31.0/src/lean/Init/Core.lean.
Verification: `VERIFIED_OFFICIAL_SOURCE_TAG_AND_GENERATED_DOCUMENTATION` against Official Lean v4.31.0 source tag; generated Init.Core documentation.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P001-LEAN-SUBSINGLETON-MAIN` — P001 1.3.9.1 / MAIN_TEX: Proof-witness irrelevance used in the supporting M004 uniqueness theorem. Locator: Subsingleton.elim declaration; Lean 4.31.0 Init.Core.
- `EXT-USE-P001-LEAN-SUBSINGLETON-SUPP` — P001 1.3.9.1 / SUPPLEMENT_MD: Official Core API used to align proposition-valued positivity witnesses. Locator: Subsingleton.elim declaration; Lean 4.31.0 Init.Core.

## EXT-REF-OPS-PECHUKAS-001 — `Pechukas1994ReducedDynamics`

Philip Pechukas, *Reduced Dynamics Need Not Be Completely Positive*, Physical Review Letters 73(8) (1994), 1060--1062. DOI: `10.1103/PhysRevLett.73.1060`.

Canonical URL: https://doi.org/10.1103/PhysRevLett.73.1060.
Alternate/direct source: not recorded.
Verification: `VERIFIED_PRIMARY_PUBLISHER` against APS publisher record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-OPS-PECHUKAS-MAIN` — OPS Conceptual scope / MAIN_TEX: Initial correlations and assignment-map qualification of reduced dynamics. Locator: principal result.
- `EXT-USE-OPS-PECHUKAS-SUPP` — OPS Conceptual scope / SUPPLEMENT_MD: Initial correlations and assignment-map qualification of reduced dynamics. Locator: principal result.

## EXT-REF-OPS-POLLOCK-001 — `Pollock2018NonMarkovianProcesses`

Felix A. Pollock, César Rodríguez-Rosario, Thomas Frauenheim, Mauro Paternostro, and Kavan Modi, *Non-Markovian quantum processes: Complete framework and efficient characterization*, Physical Review A 97(1) (2018), 012127. DOI: `10.1103/PhysRevA.97.012127`.

Canonical URL: https://doi.org/10.1103/PhysRevA.97.012127.
Alternate/direct source: not recorded.
Verification: `VERIFIED_PRIMARY_PUBLISHER` against APS publisher record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-OPS-POLLOCK-MAIN` — OPS Conceptual scope / MAIN_TEX: Operational multi-time memory and process statistics. Locator: Abstract and process-tensor construction.
- `EXT-USE-OPS-POLLOCK-SUPP` — OPS Conceptual scope / SUPPLEMENT_MD: Operational multi-time memory and process statistics. Locator: Abstract and process-tensor construction.

## EXT-REF-OPS-DAVIESLEWIS-001 — `DaviesLewis1970OperationalQuantumProbability`

E. B. Davies and J. T. Lewis, *An operational approach to quantum probability*, Communications in Mathematical Physics 17(3) (1970), 239--260. DOI: `10.1007/BF01647093`.

Canonical URL: https://doi.org/10.1007/BF01647093.
Alternate/direct source: not recorded.
Verification: `VERIFIED_PRIMARY_PUBLISHER` against Springer/CMP bibliographic record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-OPS-DAVIESLEWIS-MAIN` — OPS Conceptual scope / MAIN_TEX: Outcome probabilities and outcome-conditioned state updates. Locator: operational instrument framework.
- `EXT-USE-OPS-DAVIESLEWIS-SUPP` — OPS Conceptual scope / SUPPLEMENT_MD: Outcome probabilities and outcome-conditioned state updates. Locator: operational instrument framework.

## EXT-REF-OPS-CHIRIBELLA-001 — `Chiribella2009QuantumNetworks`

Giulio Chiribella, Giacomo Mauro D’Ariano, and Paolo Perinotti, *Theoretical framework for quantum networks*, Physical Review A 80(2) (2009), 022339. DOI: `10.1103/PhysRevA.80.022339`.

Canonical URL: https://doi.org/10.1103/PhysRevA.80.022339.
Alternate/direct source: not recorded.
Verification: `VERIFIED_PRIMARY_PUBLISHER` against APS publisher record.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-OPS-CHIRIBELLA-MAIN` — OPS Conceptual scope / MAIN_TEX: Compositional multi-step quantum specialization. Locator: quantum-network and comb framework.
- `EXT-USE-OPS-CHIRIBELLA-SUPP` — OPS Conceptual scope / SUPPLEMENT_MD: Compositional multi-step quantum specialization. Locator: quantum-network and comb framework.

## EXT-REF-LEAN-007 — `LeanListLex431`

The Lean 4 Development Team, *Lean core module: Init.Data.List.Basic (List.Lex)*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_SOURCE`. Stable source: `https://github.com/leanprover/lean4/blob/v4.31.0/src/Init/Data/List/Basic.lean`; accessed 2026-08-08.

Canonical URL: https://github.com/leanprover/lean4/blob/v4.31.0/src/Init/Data/List/Basic.lean.
Alternate/direct source: https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html.
Verification: `VERIFIED_OFFICIAL_SOURCE_TAG` against Official leanprover/lean4 v4.31.0 source tag, lines defining List.Lex and decidableLex.
Snapshot SHA-256: `not retained`.

Uses:
- `EXT-USE-P002-LEAN-LISTLEX-MAIN` — P002 1.1.6.1 / MAIN_TEX: C018 uses Lean Core List.Lex; no mathlib import is required in CNNA Core. Locator: List.Lex and decidableLex in Init/Data/List/Basic.lean, Lean v4.31.0.
- `EXT-USE-P002-LEAN-LISTLEX-SUPP` — P002 1.1.6.1 / SUPPLEMENT_MD: Pins the exact Lean Core API underlying C018 address lexicography. Locator: List.Lex and decidableLex, Init/Data/List/Basic.lean at v4.31.0.

