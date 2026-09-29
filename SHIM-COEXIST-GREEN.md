# SHIM-COEXIST-GREEN — OrdinalAnalysis no longer declares into Foundation's namespaces

Branch `v4.34-port`, at commit `14d3911` ("SHIM-NAMESPACE: move compat shims out of Foundation's
`FFL.*` namespaces").  All three acceptance runs below were made on a clean tree at that commit.

## What changed

The three compat shims (`OrdinalAnalysis/Compat.lean`, `CompatArith.lean`, `CompatSO.lean`) declared
into Foundation's own namespaces and installed their notations globally.  They now declare into
namespaces this repo owns, mirroring the upstream shape one-for-one:

| was | is |
| --- | --- |
| `FFL.FirstOrder` | `OrdinalAnalysis.Compat.FirstOrder` |
| `FFL.FirstOrder.Arithmetic` | `OrdinalAnalysis.Compat.FirstOrder.Arithmetic` |
| `FFL.FirstOrder.LawfulSyntacticRewriting` | `OrdinalAnalysis.Compat.FirstOrder.LawfulSyntacticRewriting` |
| `FFL.SecondOrder` | `OrdinalAnalysis.Compat.SecondOrder` |

and every shim notation (`𝚺₀`, `𝚷₀`, `𝚫₀`, `𝚺₁`, `𝚷₁`, `𝚫₁`, `ˡ⁺`, `⊢ᴸᴷˡ`) is now `scoped` in its
namespace instead of global.  Importing `OrdinalAnalysis` therefore adds **no** declaration and no
unscoped notation under `FFL.*`:

```
$ grep -rn '^namespace FFL' OrdinalAnalysis | wc -l
0
```

Call sites are otherwise untouched: the only edit outside the three shim files is that each existing
`open FFL …` line now also names the mirror namespace, and only in the files that actually
(transitively) import the shim module in question.  `scripts/` is byte-identical to before.

## The three runs

`lake build` (whole repo):

```
Build completed successfully (1599 jobs).
```

`scripts/coexist-check.sh` — compiles goodstein-independence's verbatim Foundation shim to an olean,
then elaborates a file importing both it and `OrdinalAnalysis`:

```
coexist-check: OK
```

`lake env lean scripts/AxiomCheck.lean` — every `#guard_msgs`-wrapped headline still prints exactly
`[propext, Classical.choice, Quot.sound]`, so the run is silent and exits 0:

```
AxiomCheck exit=0
```

## Note for the next lap

`OrdinalAnalysis/Gentzen/Setup.lean`, `ID1/Theory.lean`, `IDn/Theory.lean`, `Ramified/Ground.lean`
and ~70 others deliberately got *no* mirror `open`: they do not import the shim module whose
namespace would be named, so the `open` would be an `unknown namespace` error.  If a future edit
makes one of those files use a shim name, add the `import` and the mirror `open` together.
