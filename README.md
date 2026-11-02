# Lean-QECert

<p align="center">
  <a href="https://github.com/leanprover/lean4/releases/tag/v4.33.1"><img src="https://img.shields.io/badge/Lean-v4.33.1-6C5CE7" alt="Lean v4.33.1"></a>
  <a href="https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.1"><img src="https://img.shields.io/badge/mathlib-v4.33.1-0087BD" alt="mathlib v4.33.1"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-Apache%202.0-blue.svg" alt="Apache License 2.0"></a>
</p>

Lean-QECert is a Lean 4 library for quantum error correction, built on Mathlib.
It formalizes quantum-code semantics, code constructions, locality bounds,
magic-state distillation, and quantum memory theory.

## Library overview

| Library import | Content |
| --- | --- |
| [`QEC.Semantics`](QEC/Semantics.lean) | States, channels, instruments, error correction, entropy, and dynamics. |
| [`QEC.Coding`](QEC/Coding.lean) | Stabilizer/CSS codes and algebraic code constructions. |
| [`QEC.Locality`](QEC/Locality.lean) | Interaction graphs, correctable regions, and separators. |
| [`QEC.Bounds`](QEC/Bounds.lean) | Commuting-projector and geometric-bound proof methods. |
| [`QEC.Distillation`](QEC/Distillation.lean) | Magic-state protocols, transversal gates, and distillation overhead. |
| [`QEC.Results`](QEC/Results.lean) | Final theorem assemblies; currently the locality-bound results. |

Import `QEC.Results.LocalityBounds` for the final geometric and connectivity
tradeoffs. Reusable constructions and proof methods remain in the domain imports.

For agent-oriented navigation with exact theorem names, focused imports, source
paths and documentation routes, see [MAIN_RESULTS.json](MAIN_RESULTS.json).
Read the complete Lean declaration type and all hypotheses before using a result;
the index titles are not theorem statements.

Highlights include selected results from the following papers:

- **Foundations**
  - [A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034v1)
    ([Lean](QEC/Semantics/ErrorCorrection/KLRecovery.lean)).
  - [Stabilizer Codes and Quantum Error Correction](https://arxiv.org/abs/quant-ph/9705052)
    ([Lean](QEC/Coding/Stabilizer/Distance.lean)).
- **Code constructions**
  - [Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength](https://arxiv.org/abs/0903.0566)
    ([Lean](QEC/Results/QLDPC/HypergraphProductParameters.lean)).
  - [Quantum expander codes](https://arxiv.org/abs/1504.00822)
    ([Lean](QEC/Results/QLDPC/QuantumExpanderParameters.lean)).
  - [Fiber bundle codes: breaking the N to the one-half polylog N barrier for quantum LDPC codes](https://arxiv.org/abs/2009.03921)
    ([Lean](QEC/Results/QLDPC/FiberBundleFamily.lean)).
- **Conditional good qLDPC families**
  - [Asymptotically good quantum and locally testable classical LDPC codes](https://arxiv.org/abs/2111.03654)
    ([Lean](QEC/Results/QLDPC/ConditionalLiftedProductFamily.lean)).
  - [Quantum Tanner codes](https://arxiv.org/abs/2202.13641)
    ([Lean](QEC/Results/QLDPC/ConditionalQuantumTannerFamily.lean)).
- **Locality bounds**
  - [Tradeoffs for reliable quantum information storage in 2D systems](https://arxiv.org/abs/0909.5200)
    ([Lean](QEC/Results/LocalityBounds/GeometricTradeoff.lean)).
  - [Connectivity constrains quantum codes](https://arxiv.org/abs/2106.00765)
    ([Lean](QEC/Results/LocalityBounds/ConnectivitySeparator.lean)).
  - [Improved rate-distance trade-offs for quantum codes with restricted connectivity](https://arxiv.org/abs/2307.03283)
    ([Lean](QEC/Results/LocalityBounds/RestrictedConnectivity.lean)).
  - [Locality vs Quantum Codes](https://arxiv.org/abs/2409.15203)
    ([Lean](QEC/Results/LocalityBounds/OptimalTradeoff.lean)).
- **Magic-state distillation**
  - [Universal Quantum Computation with ideal Clifford gates and noisy ancillas](https://arxiv.org/abs/quant-ph/0403025)
    ([Lean](QEC/Results/Distillation/MagicStateThreshold.lean)).
  - [Distillation with sublogarithmic overhead](https://arxiv.org/abs/1709.03543)
    ([Lean](QEC/Results/Distillation/SublogarithmicOverhead.lean)).
  - [Constant-Overhead Magic State Distillation](https://arxiv.org/abs/2408.07764)
    ([Lean](QEC/Results/Distillation/ConstantOverhead.lean)).
- **Quantum memory**
  - [A no-go theorem for a two-dimensional self-correcting quantum memory based on stabilizer codes](https://arxiv.org/abs/0810.1983v2)
    ([Lean](QEC/Results/QuantumMemory/TwoDimensionalEnergyBarrier.lean)).
  - [Thermodynamic stability criteria for a quantum memory based on stabilizer and subsystem codes](https://arxiv.org/abs/0907.2807v2)
    ([Lean](QEC/Results/QuantumMemory/StableSyndromeStorage.lean)).

Each result retains its stated hypotheses. The good qLDPC family results
assume external spectral bounds. Completed energy-barrier and storage results
do not yet constitute an end-to-end passive quantum memory theorem.

## Getting started

The example below targets Lean-QECert 0.1.0. Use Lean/Mathlib v4.33.1:

```text
leanprover/lean4:v4.33.1
```

Add to your `lakefile.toml`:

```toml
[[require]]
name = "QEC"
git = "https://github.com/QudeLeap/Lean-QECert.git"
rev = "0.1.0"
```

For example, in `Example.lean`:

```lean
import QEC.Semantics.ErrorCorrection.KLRecovery

#check QEC.Semantics.FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
```

Build the import and check the example using your host's resource limits:

```sh
lake update
lake build "+QEC.Semantics.ErrorCorrection.KLRecovery:olean"
lake env lean Example.lean
```

## Online catalog

The result catalog, search, citations and proof dependencies are planned at
<https://qudeleap.github.io/Lean-QECert/>. The website is not yet deployed.
The catalog retains complete reviewed mathematical statements and their
hypotheses; the JSON index in this repository provides
navigation rather than a duplicate statement representation.

## Related work

[VerifiedQC/Lean-QEC](https://github.com/VerifiedQC/Lean-QEC/tree/8d115519b471b71a21fbdddf5341d8203b841cc9)
develops stabilizer/CSS semantics and SAT-assisted distance verification;
[LeanQEC/QStab](https://github.com/yezhuoyang/LeanQEC/tree/142259eacfbe59ad8472004c639b2c943a85e34f/QStab)
studies operational syndrome-extraction fault tolerance. Lean-QECert shares
foundational topics with these projects, with an emphasis on mathematical
results and their prerequisite chains.

## Citation

Please cite the original mathematical sources for the results you use, as well
as Lean-QECert. Citation keys in the Lean source refer to [REFERENCES.json](REFERENCES.json).
For version 0.1.0:

```text
The Lean-QECert contributors. Lean-QECert, version 0.1.0. 2026.
https://github.com/QudeLeap/Lean-QECert
```

## License

[Apache-2.0](LICENSE).
