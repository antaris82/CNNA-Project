# SM3eR-r3c1a Audit

Basis: green `CNNA_AR12a_SM3eR_r3c1_r3c2_patch_v1.zip`.

## Implementierte Phase

Neue Phase: `SM3eR-r3c1a`.

Neue Datei:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorBlockFoldNormalFormR3c1a.lean`

Geänderte Dateien:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorAccumulatedEntryCancellationR3c1.lean`
- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`

## Inhalt

r3c1a definiert die BlockFold-Normalform der links/rechts akkumulierten Produktfaltung:

- `generatedInteriorAccumulatedLeftConvolution`
- `generatedInteriorAccumulatedRightConvolution`
- `generatedInteriorLeftBlockFoldKernel`
- `generatedInteriorRightBlockFoldKernel`
- `generatedInteriorLeftBlockFold`
- `generatedInteriorRightBlockFold`
- `GeneratedInteriorBlockFoldNormalFormR3c1a`
- regular/variable Konstruktoren
- `SM3eRr3c1aBlockFoldNormalFormLedger`

Die bisherigen Convolution-Definitionen wurden aus `GeneratedInteriorAccumulatedEntryCancellationR3c1.lean`
entfernt und in die r3c1a-Datei vorgezogen. Dadurch konsumiert r3c1 die r3c1a-Oberfläche.

## Bewiesene r3c1a-Aussagen

Die definitorische Normalform wird entrywise geschlossen:

- `leftAccumulatedConvolution_eq_blockFold`
- `rightAccumulatedConvolution_eq_blockFold`
- `leftBlockFold_eq_kernelSum`
- `rightBlockFold_eq_kernelSum`
- `leftKernel_eq_components`
- `rightKernel_eq_components`
- Source-/No-Identity-/No-TwoSidedInv-/No-ProductIdentityProof-Gates

Damit ist r3c1a eine echte Normalform-/Expose-Phase. Sie beweist absichtlich noch nicht
`blockFold = identity`.

## Grenzen

r3c1a erzeugt keinen:

- `blockFold_eq_identity`
- `GeneratedInteriorAccumulatedEntryCancellationInvariant`
- `GeneratedInteriorSM3db7RProductIdentityProof`
- `TwoSidedInv`
- `InteriorEliminationData`
- DtN-/GeneralizedDtN-/MultiSchur-Datum
- Charpoly-/Faktor-/Diskriminantendatum

Nächster aktiver Schritt bleibt `SM3eR-r3c1b`: lokale Schur-Step-Kancellation auf BlockFold-Ebene.
