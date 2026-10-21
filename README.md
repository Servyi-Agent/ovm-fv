# ovm-fv

Verification subprojects for the [ovm](https://github.com/anomalyco/ovm)
JavaScript engine.

| subproject | toolchain | what it is |
|---|---|---|
| [`specs/`](specs/) | Lean 4 | ECMA-262 transcribed into a verifiable, executable metalanguage; one file per spec clause |
| [`verus/lookup-walk/`](verus/lookup-walk/) | Verus | the ovm property walk proved a correct/incorrect simulation of ES [[Get]] (16 verified; the proved divergences of docs/findings.md) |
| [`harness/`](harness/) | Rust (cargo) | differential testers vs the ovm binary (to come) |
| [`docs/`](docs/) | — | findings, divergence reports |

## Organization

One self-contained project per directory, grouped by toolchain — lake
packages, verus projects, and cargo workspaces do not compose, so they
never nest. Each project has its own pinned toolchain file and an
executable check script (`specs/tools/check.sh`,
`verus/lookup-walk/check.sh`) with a uniform contract: exit 0 = green.
The root orchestrator runs them all:

    ./tools/check-all.sh

CI mirrors this per-project (`.github/workflows/ci.yml`).
