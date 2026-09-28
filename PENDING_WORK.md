# PORT-V434 — open items after lap 3

**Nothing blocking.**  Both gates are green (`PORT-V434-GREEN.md`), `src/` is sorry-free and
axiom-free, and `PORT-REF-gi-Compat.lean.txt` has been deleted as the brief required.

## Upstream-facing (needs a host session; the box never pushes)

1. Push branch `v4.34` of `gotrevor/OrdinalAnalysis` and open the PR against
   `MaxWellApexLab/OrdinalAnalysis`.  `PORT-V434.md` is the migration log the PR body should
   summarise (W1–W9b plus goodstein-independence's list for the same Foundation jump).
2. Point goodstein-independence's `require` at this branch so it can use
   `Gentzen.UpperBound.gentzen_upper_bound`.

## Optional tidy-ups (none are correctness issues)

* The W9 splits introduce `private theorem`s named after the `have` they replaced
  (`goodAllTI_branchA`, `epsProg_hyp`, `epsJump_plus_J1`, …).  They are deliberately
  mechanical; Wu may prefer different names or a `section`/`namespace` grouping.
* `set_option linter.unusedSimpArgs false` at the top of `Ramified/UpperBound.lean` predates
  this port and could now be removed and the redundant `simp` arguments cleaned.
* Deprecation warnings left alone on purpose (`Ordinal.opow_succ`, `dif_pos`/`dif_neg`,
  the `haveI` style linter) — see PORT-V434.md item 24.

## What a future porter should read first

`PORT-V434.md`, section **W9 / W9b**.  On v4.34 the *kernel* runs out of memory whenever it
is asked to reduce a structural recursion on syntax at a **concrete coded formula**, and the
failure carries no message (`exit 137`).  Probe with
`lake env lean -M <MB> -j 2 --profile <file>`, add `-D maxHeartbeats=<n>` when the exception
escapes the message system, and fix by stating the step at a *variable* subformula.
