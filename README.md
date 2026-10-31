# Sharp Sample Complexity for the Prophet-Secretary Problem

[![Lean](https://github.com/GO-EPFL/prophet-secretary-sample-complexity/actions/workflows/lean.yml/badge.svg)](https://github.com/GO-EPFL/prophet-secretary-sample-complexity/actions/workflows/lean.yml)

This repository is a Lean formalization of **Sharp Sample Complexity for the Prophet-Secretary Problem**. It proves explicit matching $\Theta(1/\varepsilon)$ sample-complexity bounds per distribution for approaching the optimal global competitive ratio within additive $\varepsilon$, with constants independent of the number of random variables $n$. The [formalization guide](docs/Formalization.md) maps paper labels to declarations and explains the representations and proof methods.

## Build and verification

Install [elan](https://github.com/leanprover/elan) and Git, then run these commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean --run scripts/CheckAxioms.lean
```

The first command downloads official mathlib build caches; the project sources are built by the second.
The axiom checker also verifies that the public import reaches every mathematical source module.

Dependencies are pinned:

- Lean: `leanprover/lean4:v4.32.2` in `lean-toolchain`.
- mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c` in `lakefile.toml`.
- Transitive dependency revisions: `lake-manifest.json`.

## Public imports

```lean
import ProphetSecretary
```

Subject imports are available separately:

| Import | Contents |
|---|---|
| [`ProphetSecretary.Model`](ProphetSecretary/Model.lean) | Instances, observable policies, training, scalar values and Bellman analysis |
| [`ProphetSecretary.Reach`](ProphetSecretary/Reach.lean) | Reach-duration comparisons, rare jackpots, zeros and clipping |
| [`ProphetSecretary.Statistics`](ProphetSecretary/Statistics.lean) | Empirical optimization, upper bounds and the sharp complexity theorem |
| [`ProphetSecretary.LowerBound`](ProphetSecretary/LowerBound.lean) | Constructed finite experiments and the universal lower bound |
| [`ProphetSecretary.Limiting`](ProphetSecretary/Limiting.lean) | Poisson limits, compactness, closure and score transfer |
| [`ProphetSecretary.Stability`](ProphetSecretary/Stability.lean) | Outcome stability, curvature and score continuity |
| [`ProphetSecretary.Probability`](ProphetSecretary/Probability.lean) | Independent laws, likelihoods, couplings and information estimates |
| [`ProphetSecretary.Analysis`](ProphetSecretary/Analysis.lean) | Analytic estimates, derivative limits and finite minimax |

## Proof foundations

[`scripts/CheckAxioms.lean`](scripts/CheckAxioms.lean) checks the transitive axiom dependencies of every declaration originating in a project module, including private and generated declarations. It fails on anything outside `propext`, `Classical.choice` and `Quot.sound`, including unfinished proofs. The [guide](docs/Formalization.md) explains the statements and assumptions beyond this foundational check.
