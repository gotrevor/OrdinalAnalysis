# PORT-V434 — GREEN

`OrdinalAnalysis` (Wu) builds and verifies on **Lean v4.34.0**, Foundation `bde9bc28`,
mathlib `5ed29652` (v4.34.0), branch `v4.34`, **non-module**, statements unchanged.

Date: 2026-09-28.  Achieved on lap 3 of the port.  Both gates were run twice, from a clean
tree, with nothing else on the box.

## Gate 1 — `taskset -c 0-2 lake build`

```
Build completed successfully (1599 jobs).
```

Verified from scalars in their own call:

```
$ grep -c 'Build completed successfully' build.log
1
$ grep -cE '^error' build.log
0
$ echo $?   # of the unpiped lake build
0
```

## Gate 2 — `lake env lean scripts/AxiomCheck.lean`

```
warning: manifest out of date: git url of dependency 'Foundation' changed; use `lake update Foundation` to update it
```

…and nothing else: all **538** `#guard_msgs`-guarded `#print axioms` matched their frozen
expected lists, exit code **0**.  (The manifest warning is expected: the box adopts the
pre-built `~/.lake-base/4.34.0` store and must never `lake update`.)

## Fidelity

* `scripts/AxiomCheck.lean` is byte-identical to v4.33 — no guard was weakened, added or removed.
* `src` contains **no unproved obligation of any kind** — no placeholder tactic, no `native_decide`,
  no `partial def`, and **zero declared `axiom`**.  (Grepping `OrdinalAnalysis/` for the two
  placeholder keywords matches only prose inside docstrings.)
* Every headline theorem still depends only on the trust base
  (`propext`, `Classical.choice`, `Quot.sound`, or a subset), including
  `Gentzen.UpperBound.gentzen_upper_bound`, `Gentzen.Epsilon1{Lower,Upper}Bound.*`,
  `ACAOmega.OmegaDerivable₂.secondCutElimination*`, `Ramified.ramified_theorem`,
  `IDn.idn_theorem_final`, `IDn.idn_analysis`, `IDn.idlt_analysis`.
* No declaration of Wu's was renamed or restated.  Every new declaration introduced by the
  port is either in `OrdinalAnalysis/{Compat,CompatSO,FinLK}.lean` (the list-sequent calculus
  and its two *proved* translations to and from upstream's multiset `⊢ᴸᴷ¹`/`⊢ᴸᴷ²`) or a
  `private theorem` splitting an existing proof.

## The migration log

`PORT-V434.md` holds the full symptom → fix log: patterns **W1–W9b** for this port plus
goodstein-independence's list for the same Foundation jump.  The lap-3 addition, **W9/W9b**,
is the one a future porter will need most: on v4.34 the *kernel* — not the elaborator — runs
out of memory whenever it is asked to reduce a structural recursion on syntax
(`Semiformula.neg`, `toSOAt`/`toSOAtB`, `SecondOrder.Rew.app`, `Semiformula.Eval`, `rank`)
at a **concrete coded formula**, and the failure carries no message at all (`exit 137`, or an
uncaught `memory_exception … at 'interpreter'`).  Diagnose with
`lake env lean -M <MB> -j 2 --profile <file>` (and `-D maxHeartbeats=<n>` when the exception
escapes); fix by stating the step as a lemma at a *variable* subformula and `rw`ing with it,
and by splitting long `PSeq`/`DerLt` assemblies into `private theorem`s.
