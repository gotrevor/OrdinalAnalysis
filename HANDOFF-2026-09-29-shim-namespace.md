# HANDOFF 2026-09-29 — SHIM-NAMESPACE done, coexistence green

Branch: `v4.34-port`
HEAD: `2b04ad2` ("SHIM-COEXIST-GREEN: record the three green acceptance runs")
Parent: `14d3911` ("SHIM-NAMESPACE: move compat shims out of Foundation's FFL.* namespaces")

## Status: the operator objective in SHIM-NAMESPACE.md is met

All three gates pass on a clean tree at `14d3911` (re-verified, not remembered):

| gate | result |
| --- | --- |
| `lake build` | `Build completed successfully (1599 jobs).` |
| `scripts/coexist-check.sh` | `coexist-check: OK` |
| `lake env lean scripts/AxiomCheck.lean` | silent, exit 0, every guard unchanged |
| `grep -rn '^namespace FFL' OrdinalAnalysis` | 0 hits |

`scripts/` is byte-identical to before this lap (`git status --short scripts/` clean across both
commits), so the frozen files and the audit surface AxiomCheck guards are untouched.
No `axiom` was added; no lakefile/manifest edit; no network; nothing pushed.

## What changed

The three compat shims used to declare into Foundation's own namespaces and install their
hierarchy-symbol notations globally, so no other project carrying its own Foundation shim could be
imported alongside `OrdinalAnalysis`.  They now declare into namespaces this repo owns, mirroring
the upstream shape one-for-one:

| was | is |
| --- | --- |
| `FFL.FirstOrder` | `OrdinalAnalysis.Compat.FirstOrder` |
| `FFL.FirstOrder.Arithmetic` | `OrdinalAnalysis.Compat.FirstOrder.Arithmetic` |
| `FFL.FirstOrder.LawfulSyntacticRewriting` | `OrdinalAnalysis.Compat.FirstOrder.LawfulSyntacticRewriting` |
| `FFL.SecondOrder` | `OrdinalAnalysis.Compat.SecondOrder` |

and `𝚺₀ 𝚷₀ 𝚫₀ 𝚺₁ 𝚷₁ 𝚫₁ ˡ⁺ ⊢ᴸᴷˡ` are all `scoped` in their namespace rather than global.

Outside the three shim files the only edit is to `open` lines: each existing `open FFL …` line now
also names the mirror namespace.  306 files touched, 484 insertions / 474 deletions — no proof text
changed.

## Two facts a future edit will trip over

1. **Not every file got a mirror `open`.**  ~75 files (`Gentzen/Setup.lean`, `ID1/Theory.lean`,
   `IDn/Theory.lean`, `Ramified/Ground.lean`, `ID1/Sound.lean`, …) do **not** transitively import the
   shim module whose namespace would be named, and `open <unimported namespace>` is a hard
   `unknown namespace` error that poisons every subsequent identifier in the file.  I computed the
   transitive import graph and stripped the mirror tokens exactly where unavailable.  If a future
   edit makes one of those files use a shim name, add the `import` **and** the mirror `open`
   together.
2. **`CompatSO.lean` opens `FFL.FirstOrder` selectively** — `open FFL.FirstOrder (Language)`, not the
   whole namespace.  Once the shim is no longer physically inside `namespace FFL.SecondOrder`, a full
   `open FFL.FirstOrder` makes `Proposition` ambiguous between `FFL.FirstOrder.Proposition` and
   `FFL.SecondOrder.Proposition` (≈30 `Ambiguous term` errors).  Keep it selective.

## Build-environment gotcha on this box

`lake build` intermittently fails with `failed to open file '…': Too many open files` on random
mathlib oleans — a file-descriptor limit under lake's parallelism, not a real error.  `ulimit -n
1048576` before the build plus a re-run clears it (each run makes real progress, so re-running
converges).  `lake` here accepts neither `-j` nor `--jobs`, so throttling parallelism is not an
option.

## Next steps

Nothing is open on this objective.  `box done` was accepted and the host stops the run without
relaunch.  If work resumes on this branch, the natural follow-ups are:

- The host strips the process notes (`SHIM-NAMESPACE.md`, `SHIM-COEXIST-GREEN.md`, this handoff)
  before any PR — do not fold them into the port commit.
- Sanity-check the coexistence property stays true as the port evolves by keeping
  `scripts/coexist-check.sh` in whatever CI the fork runs; it is the only thing that catches a
  regression, since a stray `namespace FFL…` still builds fine in isolation.
