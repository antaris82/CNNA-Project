# CNNA v24 - Module manifest and reuse governance

## What changed

The next active planning gate is now **Phase 1.1.1.1.1 - Implementation module manifest and semantic placement gate**. Phase 1.1.1.1 became an umbrella and was split into three child gates:

1. **1.1.1.1.1** - module manifest and semantic placement gate
2. **1.1.1.1.2** - reuse / duplicate-implementation audit and canonical generator policy
3. **1.1.1.1.3** - declaration consumption classification map finalization

## Hard rule added

Before implementation starts, every active Lean phase must declare:

- exact count and names of proposed added modules;
- exact count and names of proposed modified modules;
- semantic placement rationale for each module;
- existing modules considered for reuse or extension;
- why any new module is necessary;
- public / legacy / API / proof-bridge role;
- expected import direction and consumer rights;
- duplicate-risk symbols or operations.

Granular phases do **not** imply granular code files. A new module is allowed only for a reusable semantic layer, API/firewall seam, legacy quarantine boundary, or unavoidable import-direction split.

## Canonical generator rule

The Smoke-Test Generator is planned as the canonical generator seam wherever its semantics apply. Generator-like request/output, smoke-test, extraction, ledger, or reusable theory-generation code must consume or extend that seam. Parallel generators are blocked unless the plan records a genuine semantic split.

## Relation to blue objects

Blue objects remain derived-only/proof-carrying but semantically/API unfinished. Their correction phases must use the module manifest so corrections are placed in natural reusable modules rather than scattered into phase-local files.

## Build status

This package changes planning artifacts and generated views only. No Lean build was run or claimed.
