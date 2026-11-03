# Sharp Sample Complexity and Polynomial-Time Learning for Prophet Secretary

[![Lean 4.32.2](https://img.shields.io/badge/Lean-4.32.2-4F46E5?style=for-the-badge&labelColor=172554)](lean-toolchain)
[![Build and axiom audit](https://img.shields.io/github/actions/workflow/status/GO-EPFL/prophet-secretary-sample-complexity/lean.yml?branch=main&event=push&style=for-the-badge&logo=githubactions&logoColor=white&label=Build%20%2B%20Axiom%20Audit&labelColor=172554)](https://github.com/GO-EPFL/prophet-secretary-sample-complexity/actions/workflows/lean.yml?query=branch%3Amain+event%3Apush)

This repository is a Lean formalization of **Sharp Sample Complexity and Polynomial-Time Learning for Prophet Secretary**.

The [main theorem](ProphetSecretary/Statistics/SharpConstructiveComplexity.lean#L149) gives a learner that runs in time polynomial in $n$ and $1/\varepsilon$ and achieves competitive ratio at least $C_{\mathrm{PS}}-\varepsilon$ with a hard budget of $O(1/\varepsilon)$ samples per distribution, with a matching lower bound even for adaptive sampling.

The [formalization guide](docs/Formalization.md) maps the paper’s results to Lean declarations.

## Build and verification

Install [elan](https://github.com/leanprover/elan) and Git, then run these commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean --run scripts/CheckAxioms.lean
```

The [Lean workflow](.github/workflows/lean.yml) runs the build and [axiom check](scripts/CheckAxioms.lean) on pushes and pull requests. The checker verifies public import coverage and allows only `propext`, `Classical.choice` and `Quot.sound`.

Dependencies are pinned:

- Lean: `leanprover/lean4:v4.32.2` in `lean-toolchain`.
- mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c` in `lakefile.toml`.
- Transitive dependency revisions: `lake-manifest.json`.

## Repository layout

```lean
import ProphetSecretary
```

The Lean sources are grouped by subject under `ProphetSecretary/`. Each subject has its own import:

| Import | Contents |
|---|---|
| [`ProphetSecretary.Model`](ProphetSecretary/Model.lean) | Instances, observable policies, training, scalar values and Bellman analysis |
| [`ProphetSecretary.Reach`](ProphetSecretary/Reach.lean) | Reach-duration comparisons, rare jackpots, zeros and clipping |
| [`ProphetSecretary.Statistics`](ProphetSecretary/Statistics.lean) | Empirical optimization, upper bounds and the sharp complexity theorem |
| [`ProphetSecretary.Statistics.ConstructiveLearning`](ProphetSecretary/Statistics/ConstructiveLearning.lean) | Calibrated learner, scalar planner and polynomial-time guarantees |
| [`ProphetSecretary.LowerBound`](ProphetSecretary/LowerBound.lean) | Constructed finite experiments and the universal lower bound |
| [`ProphetSecretary.Limiting`](ProphetSecretary/Limiting.lean) | Poisson limits, compactness, closure and score transfer |
| [`ProphetSecretary.Stability`](ProphetSecretary/Stability.lean) | Outcome stability, curvature and score continuity |
| [`ProphetSecretary.Probability`](ProphetSecretary/Probability.lean) | Independent laws, likelihoods, couplings and information estimates |
| [`ProphetSecretary.Analysis`](ProphetSecretary/Analysis.lean) | Analytic estimates, derivative limits and finite minimax |
