# CNNA architectural identity: ComplemeNt Net Architecture

<!-- CNNA-ARCHITECTURE-BEGIN SUPPLEMENT -->
CNNA means **ComplemeNt Net Architecture**. The name identifies the invariant construction principle, not a late physical interpretation: one growing provenance net is repeatedly resolved into a realized or retained part, a relative complement, and an interface or handoff. The role of the complement is stage-, cut-, scale-, and projection-relative.

The architecture begins before any Schur/DtN or quantum specialization. `C001` supplies the empty baseline; `C002` creates the first realized node; `C003` and `C018` expose not-yet-realized continuation slots; `C004A` selects the first such slot; and `C013`/`C014` produce the first nontrivial response-capable directed net. Later complement elimination, record/live splitting, nested refinements, and reduced observations preserve this throughline in different mathematical forms.

This architectural statement is interpretive and organizational. It does not add a theorem beyond the registered node contracts.

<!-- CNNA-ARCHITECTURE-END SUPPLEMENT -->

# Conceptual scope: generalized open provenance systems

The general research object is an **open provenance system**: an observed present is treated as a reduced view of a real, historically grown provenance state.  The current CNNA DAG is one finite deterministic specialization, not a proof that every empirical open system has this form.

A generic state is organized schematically as

\[
\mathfrak P_n=(\Gamma_n,\mathsf{Rec}_n,\mathsf{Live}_n,\mathcal K_n,\mathcal C_n,\mathcal O_n).
\]

The intended roles are: event provenance, immutable birth record, mutable live response, response kernel, cut-relative complement, and observation/coarse-graining channel.  The weak hypothesis allows intrinsic stochasticity after provenance completion.  The strong CNNA hypothesis seeks deterministic completion.  **The strong universal claim is not currently proved.**

## Specialization map

| Layer | DAG locus | Current status |
|---|---|---|
| Event-provenance carrier and order | C003, C018, C005, C004 | finite CNNA definitions/results |
| Cut-relative complement and exact response | M001, C006, P001, C007, C020--C025 | finite directed Schur/DtN specialization; nodewise status applies |
| Response-coupled event generation | M003, M004, C008 | M003/M004 and C008 kernel-verified; C016 is the next record-channel construction |
| Record/live and backreaction | C008, C016, C017, C024, C043 | C008 update boundary verified; C016/C017 and later backreaction structure remain downstream |
| Nested cuts, refinement and cocycle | C044, C045, C047, C046, C043 | planned/partially migrated according to node status |
| Finite provenance-derived POVM | C025, M030, C032, C033, C053, C044, C047 | Legacy migration target; not yet a current DAG theorem |
| Open quantum process/instrument specialization | C043, C053, C057, C060 and later dedicated nodes | conceptual target; no universal OQS theorem claimed |
| Weyl/GNS/Araki--Woods and modular/AQFT | Sections 5--8 | late mathematical specialization; nodewise proof gates remain authoritative |

## Non-identifications

- Schur/DtN elimination is an effective response reduction, not a partial trace.
- A POVM supplies outcome probabilities; an instrument additionally supplies outcome-conditioned state updates.
- A process tensor or quantum comb is a quantum multi-time specialization, not the definition of provenance itself.
- Event provenance may remain acyclic even when the live state has recurrent or cyclic dynamics.

The reduced-dynamics ambiguity under initial correlations motivates a provenance-dependent reconstruction map.
<!-- CNNA-EXTREF-BEGIN EXT-USE-OPS-PECHUKAS-SUPP -->
**EXT-REF-OPS-PECHUKAS-001 — specialization context.** Philip Pechukas, *Reduced Dynamics Need Not Be Completely Positive*, Physical Review Letters 73(8) (1994), 1060--1062. DOI: `10.1103/PhysRevLett.73.1060`. Exact location: principal result. Context: Initial correlations and assignment-map qualification of reduced dynamics. Formal status: `INTERPRETIVE_SPECIALIZATION_CONTEXT_NOT_IMPORTED_AS_AXIOM`
<!-- CNNA-EXTREF-END EXT-USE-OPS-PECHUKAS-SUPP -->

The process-tensor framework is the primary quantum reference for operational multi-time memory.
<!-- CNNA-EXTREF-BEGIN EXT-USE-OPS-POLLOCK-SUPP -->
**EXT-REF-OPS-POLLOCK-001 — specialization context.** Felix A. Pollock, César Rodríguez-Rosario, Thomas Frauenheim, Mauro Paternostro, and Kavan Modi, *Non-Markovian quantum processes: Complete framework and efficient characterization*, Physical Review A 97(1) (2018), 012127. DOI: `10.1103/PhysRevA.97.012127`. Exact location: Abstract and process-tensor construction. Context: Operational multi-time memory and process statistics. Formal status: `INTERPRETIVE_SPECIALIZATION_CONTEXT_NOT_IMPORTED_AS_AXIOM`
<!-- CNNA-EXTREF-END EXT-USE-OPS-POLLOCK-SUPP -->

The Davies--Lewis instrument framework is the target distinction between probabilities and post-measurement states.
<!-- CNNA-EXTREF-BEGIN EXT-USE-OPS-DAVIESLEWIS-SUPP -->
**EXT-REF-OPS-DAVIESLEWIS-001 — specialization context.** E. B. Davies and J. T. Lewis, *An operational approach to quantum probability*, Communications in Mathematical Physics 17(3) (1970), 239--260. DOI: `10.1007/BF01647093`. Exact location: operational instrument framework. Context: Outcome probabilities and outcome-conditioned state updates. Formal status: `INTERPRETIVE_SPECIALIZATION_CONTEXT_NOT_IMPORTED_AS_AXIOM`
<!-- CNNA-EXTREF-END EXT-USE-OPS-DAVIESLEWIS-SUPP -->

The quantum-network/comb formalism is retained as context for later compositional specialization.
<!-- CNNA-EXTREF-BEGIN EXT-USE-OPS-CHIRIBELLA-SUPP -->
**EXT-REF-OPS-CHIRIBELLA-001 — specialization context.** Giulio Chiribella, Giacomo Mauro D’Ariano, and Paolo Perinotti, *Theoretical framework for quantum networks*, Physical Review A 80(2) (2009), 022339. DOI: `10.1103/PhysRevA.80.022339`. Exact location: quantum-network and comb framework. Context: Compositional multi-step quantum specialization. Formal status: `INTERPRETIVE_SPECIALIZATION_CONTEXT_NOT_IMPORTED_AS_AXIOM`
<!-- CNNA-EXTREF-END EXT-USE-OPS-CHIRIBELLA-SUPP -->

## Legacy POVM migration guard

The retained Legacy calculation constructed a finite Parseval-frame POVM from a compressed response state,
\[
E_v=z_vz_v^{\mathsf T},\qquad \sum_vE_v=I,\qquad p_v=\operatorname{tr}(D_NE_v).
\]
It is evidence and a migration specification.  It did **not** establish exact projective compatibility of independently reconstructed depths, an infinite state limit, a lift to the raw Weyl net, or a full outcome-conditioned instrument.  Any new DAG nodes for this chain must be derived from current predecessors rather than importing Legacy coefficients or numerical fallback rules.

## General completion hypothesis

For an empirically accessible open system $S$, the research program asks whether there exist a provenance-complete extension $\widehat S$, a retained region $B$, a complement-elimination operation $\operatorname{Eff}_{I_B}$, and an observation channel $Q_B$ such that the complete family of observable process statistics satisfies

\[
\mathbb P_S
=
\mathbb P_{Q_B\circ\operatorname{Eff}_{I_B}(\widehat S)}.
\]

The nontrivial content is not merely that the system has a past.  It is that the dynamically sufficient part of that past remains a real component of the present state and can alter future responses even when two reduced present descriptions coincide.

Let $X_n$ denote a reduced present and $\Pi_n$ its dynamically relevant provenance.  The target sufficient state is

\[
Z_n=(X_n,\Pi_n),
\qquad
\mathbb P(X_{n+1}\mid X_{\le n},a_{\le n})
=
\mathbb P(X_{n+1}\mid Z_n,a_n).
\]

This equation defines a target property.  The present DAG establishes it only for those finite deterministic update components that are explicitly formalized; it does not establish the quantifier over all empirical systems.

### Weak and strong forms

The **weak completion hypothesis** allows an intrinsically stochastic update kernel

\[
Z_{n+1}\sim\mathcal U_n(\,\cdot\mid Z_n,a_n).
\]

It claims only that omitted history is no longer an additional source of non-Markovianity once the sufficient provenance state is included.

The **strong deterministic CNNA hypothesis** instead seeks

\[
Z_{n+1}=\mathcal U_n(Z_n,a_n),
\]

or $Z_{n+1}=\mathcal U_n(Z_n)$ in the absence of an external intervention.  This strong form is an ontological hypothesis over and above the current finite proofs.

## Cut-relative environment and coherent refinement

For one complete finite carrier $V_n$ and retained region $B_n\subseteq V_n$, define

\[
I_{B_n}=V_n\setminus B_n.
\]

The environment is therefore a role relative to a cut.  If $B_1\subseteq B_2$, then $I_{B_2}\subseteq I_{B_1}$: a coordinate treated as environment at one resolution may be retained at a finer resolution.

A generalized open-provenance theory must consequently prove more than the existence of an effective response at each isolated cut.  For nested retained regions $B_1\subseteq B_2\subseteq B_3$, the corresponding reductions should satisfy a compositional law whenever all domains are admissible,

\[
\operatorname{Eff}_{B_3\setminus B_1}
=
\operatorname{Eff}_{B_2\setminus B_1}
\circ
\operatorname{Eff}_{B_3\setminus B_2},
\]

or else expose the controlled defect as a refinement cocycle.  C044, C045, C047, C046, and C043 are the designated DAG locus for this requirement.

## Record/live divergence and backreaction

The immutable record and mutable live state have different mathematical roles:

\[
\mathsf{Rec}_{n+1}=\mathsf{Rec}_n\cup\{r_{n+1}\},
\qquad
\mathsf{Live}_{n+1}=\mathcal U_n(\mathsf{Live}_n,r_{n+1},\Lambda_n).
\]

A record stores the conditions under which a relation was born.  The live channel stores how that relation currently acts after later growth.  Their difference is not treated as bookkeeping noise; it is the prospective carrier of backreaction and effective memory.  C008 owns the update, C016 the immutable record, C017 the live channel, C024 the backreaction stream, and C043 its multiscale reconstruction.

## Non-Markovianity and identifiability

In this framework Markovianity is relative to the chosen state description.  A reduced state can be non-Markovian because two provenance states $\Pi_n^{(1)}\ne\Pi_n^{(2)}$ yield the same $X_n$ but different future response laws.  This motivates, but does not prove, the interpretation

\[
\text{effective memory}
=
\text{dynamically visible unresolved provenance}.
\]

The corresponding inverse problem is identifiability.  Provenances $\Pi_1$ and $\Pi_2$ are observationally equivalent at a chosen intervention class if they induce the same complete family of process statistics.  The scientifically meaningful reconstruction target may therefore be a provenance-equivalence class rather than a unique microscopic history.

## Specialization ladder

The intended order is one-way and derived-only:

\[
\begin{aligned}
&\text{event provenance and response-coupled growth}\\
&\quad\longrightarrow\text{cut-relative effective response}\\
&\quad\longrightarrow\text{record/live and nested-channel coherence}\\
&\quad\longrightarrow\text{response algebra and positive state structures}\\
&\quad\longrightarrow\text{finite POVM and quantum-process specializations}\\
&\quad\longrightarrow\text{Weyl/GNS/Araki--Woods and modular/AQFT structures}.
\end{aligned}
\]

The reverse interpretation is not licensed: provenance is not defined retrospectively from a quantum state, and a quantum reduction is not assumed in order to derive the earlier response structure.

## Falsification and obstruction gates

The generalized program must be weakened or rejected for a proposed system class if any of the following persists after all admissible extensions are considered:

1. no finite or controlled provenance-sufficient state reproduces the observable multi-time statistics;
2. effective reductions for nested cuts cannot be made coherent and no controlled cocycle accounts for their defect;
3. record/live separation fails to define invariant birth data and a well-defined current state;
4. two supposedly equivalent provenance representatives yield different physical outputs after the registered quotient;
5. the finite POVM migration cannot derive positivity and completeness from current predecessors without importing Legacy fallback choices;
6. the OQS/AQFT specialization requires independent physical assumptions that are falsely presented as consequences of primitive provenance.

These are scientific obstruction criteria, not merely software tests.
