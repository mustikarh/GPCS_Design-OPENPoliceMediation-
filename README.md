# GPCS_Design-OPENPoliceMediation-
Traceable formal models and proof artefacts for OPEN Policy-Mediation in GlobalPlatform Card Specification 2.4, verified with Atelier B and ProB.
# Formal Verification of OPEN Policy-Mediation in GlobalPlatform Card Specification 2.4

This repository contains the formal models, proof artefacts, and traceability
tables accompanying the paper "[judul]" ([venue/tahun, atau "under review"]).

The work formalises the OPEN Policy-Mediation enforcement layer of GPCS v2.4
using the B method, verified with Atelier B (proof obligations) and ProB
(reachability and animation).

## Contents
- `models/re_OPEN_L4.mch` — the B machine of record. State properties are
  discharged as proof obligations in Atelier B.
- `models/re_OPEN_L4_prob.mch` — a variant used for ProB model checking, with a
  single-privilege `open_install` parameter to keep the state space tractable.
  Equivalent to the machine of record for the temporal and reachability
  properties checked here.
- `proofs/` — proof-obligation files from Atelier B.
- `prob/` — the LTL/CTL formulas checked in ProB and their results.
- `register/` — the full requirement register (27 OPEN + 4 implementation-derived
  requirements), the requirement-to-proof traceability table, and the nine
  future-work requirements.

## Requirements register
The register covers 27 OPEN enforcement requirements extracted from GPCS v2.4,
plus 4 implementation-derived requirements. Of these, 18 are in-scope and
formalised in the machine; 9 are future work (see `register/future_work.md`).

## Reproducing the results
Atelier B: open `models/re_OPEN_L4.mch`, generate proof obligations, and run the
automatic prover. [Sebut versi Atelier B yang kamu pakai.]

ProB: open `models/re_OPEN_L4_prob.mch` and check the formulas in
`prob/formulas.txt` via the LTL/CTL panel. [Sebut versi ProB.]

## Verification summary
- 18 in-scope requirements verified: 15 in Atelier B (unbounded), 3 in ProB (bounded).
- Breakdown: 4 invariants, 3 assertions, 8 guards, 2 reachability, 1 animation.

## Citation
[Citation details will be added upon publication.]
