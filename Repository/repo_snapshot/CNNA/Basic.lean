namespace CNNA

def projectName : String := "CNNA"

def migrationPhase : String :=
  "IV. Schritt 1 — P27 Archiv-Cutover: nur noch der derived-only Pillar-A-Pfad bleibt aktiv"

def buildPathPolicy : String :=
  "active path: CNNA/PillarA only; archived inactive paths: legacy_sources/REALOQS_v0.0605_stable and legacy_sources/CNNA_v0.100_unstable; CNNA/PillarB-E remain dormant BuildAll stubs"

end CNNA
