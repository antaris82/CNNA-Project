# SM3eR-r3c1 / SM3eR-r3c2 Audit

## Ausgangspunkt

Basis ist der r3c0-Stand `CNNA_AR12a_SM3eR_r3c_TraceCancellationDerivation_patch_v1(1).zip`.
Der bisherige r3c0-Code stellt `GeneratedInteriorSM3db7RTraceCancellationSource`,
`GeneratedInteriorSM3db7RTraceCancellationDerivation` und den Export in
`GeneratedInteriorSM3db7RProductCancellationLedger` bereit. Die sechs eigentlichen
Kancellationsfelder werden in dieser Schnittstelle weiterhin explizit getragen.

## Neue Phasenaufteilung

- `SM3eR-r3c1` ist jetzt die AccumulatedEntry-Cancellation-Schicht an der
  SM3db4aR/Fold-nahen Stelle.
- Die bisherige r3c1-Verbrauchsschicht wird als `SM3eR-r3c2` ausgearbeitet.

## Neue Datei r3c1

`CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorAccumulatedEntryCancellationR3c1.lean`

Diese Datei definiert:

- `generatedInteriorAccumulatedLeftConvolution`
- `generatedInteriorAccumulatedRightConvolution`
- `GeneratedInteriorAccumulatedEntryCancellationInvariant`
- Projektionstheoreme für links/rechts, diagonal/offdiag
- Regular-/Variable-Abbreviations
- `SM3eRr3c1AccumulatedEntryCancellationLedger`

Die r3c1-Struktur hält genau die sechs Kancellationsaussagen auf der
`generatedInteriorAccumulatedEntryValue T`-Ebene, also vor dem r3c2-Verbrauch über
SM3db7R-Handoff und r3a-Normalformen.

## Neue Datei r3c2

`CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorTraceCancellationR3c2.lean`

Diese Datei definiert:

- `GeneratedInteriorSM3db7RTraceCancellationDerivation.fromAccumulatedEntryCancellationInvariant`
- `traceCancellationDerivation_from_accumulatedEntryCancellationInvariant`
- `traceCancellationInvariant_from_accumulatedEntryCancellationInvariant`
- `productCancellationLedger_from_accumulatedEntryCancellationInvariant`
- `SM3eRr3c2TraceCancellationLedger`
- Regular-/Variable-Hilfskonstruktoren für die Derivation

Damit erhält r3c2 seine sechs Felder nicht mehr als freie Einzelargumente, sondern aus einem
r3c1-Objekt, das auf der akkumulierten Trace-/Fold-Ebene formuliert ist.

## Geänderte Importstellen

- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`

## Grenzen

Diese Implementierung erzeugt weiterhin keinen `GeneratedInteriorSM3db7RProductIdentityProof`,
keinen `TwoSidedInv`, keine `InteriorEliminationData`, keine DtN-/MultiSchur-Daten und keine
Charpoly-/Diskriminantendaten.

Der unbedingte mathematische Abschluss von r3c1 hängt weiterhin daran, dass ein konkretes
`GeneratedInteriorAccumulatedEntryCancellationInvariant` aus der bestehenden SM3db4aR/Fold-Kette
konstruiert wird. r3c2 ist danach vollständig vorbereitet und benötigt keine sechs freien
Kancellationsargumente mehr.
