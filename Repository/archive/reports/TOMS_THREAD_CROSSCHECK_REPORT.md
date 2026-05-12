# TomS thread cross-check report for CNNA planning v21

## Method

The five Astronews thread pages were treated as an external reference and warning source, not as CNNA-generative input. The roadmap was updated only by adding proof obligations, comparison-only phases, object-register entries, and guardrails inside `masters/cnna_roadmap_master.yaml`.

## Main corrections against the prior plan

1. **Irreducible is not automatically prime.** The plan must keep the class-number/UFD/PID gate before any prime-generation claim derived from quadratic norm forms.
2. **Quadratic orders and arbitrary elliptic lattices are not interchangeable.** The CM/order/tau pipeline remains upstream of modular and j work.
3. **L-functions are not a Riemann-zeta shortcut.** The roadmap keeps character/splitting and modular/automorphic comparison after derived number-theory data.
4. **Monster is not the endpoint.** Monster/Monstrous-Moonshine is represented as a late comparison fingerprint; the actual question becomes the common-indicator/Hauptmodul bridge test.
5. **Finite simple groups, Leech lattice, theta/shell data, and VOA/moonshine-module material are added as comparison-only stages.** They do not feed Pillar A as assumptions.
6. **Physics-from-math shortcuts remain blocked.** String-theory/VOA/chiral-CFT material is allowed only as late comparison/consumer structure unless CNNA derives the relevant carrier.

## Files changed or added

- `masters/cnna_roadmap_master.yaml`: metadata v21, TomS cross-check section, phases 12.4-12.8, objects MOON3-MOON8, updated phase 12 scratchpad.
- `scripts/generate_tables.py`: generation of the TomS-thread cross-check table and TSV export.
- `tables/toms_thread_crosscheck.tex`, `tables/toms_thread_crosscheck_table.tex`: generated PDF tables.
- `generated_exports/external_source_crosscheck.generated.tsv`: generated inspection export.
- `CNNA_Planning_and_Documentation_Tool_v20_A3_English.tex`: v21 title and TomS cross-check section in the PDF body.
- `README.md`: v21 generation notes.

## Verification performed

- `python3 scripts/generate_tables.py` succeeded.
- `pdflatex` was run twice and produced a 62-page A3 PDF.
- The generated PDF was rendered to PNGs with the PDF workflow renderer; page 2 contains the TomS cross-check table and rendered without visible clipping in the inspected page.

## Not verified

No Lean build was run. This package changes planning/documentation data and generated LaTeX/PDF views only; it does not modify the Lean repository snapshot.
