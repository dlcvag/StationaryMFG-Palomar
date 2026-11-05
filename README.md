# Stationary mean-field games: Palomar source repository

This repository contains the three main existence statements from **Solving
Mean-Field Games with Monotonicity Methods in Banach Spaces**, by Rita Ferreira,
Diogo Gomes, and Melih Üçer, and the Lean source needed to prove them.
The public paper is [arXiv:2506.21212v3](https://arxiv.org/abs/2506.21212v3).

The statements are independently specified in [Challenge.lean](Challenge.lean).
[Solution.lean](Solution.lean) connects them to the included proof development;
[comparator.json](comparator.json) selects all three comparisons. The Challenge
imports only Mathlib and has three deliberate proof holes. These are the
statement specification, not unfinished proofs in Solution.

**Verification status:** the full build passes on Lean 4.35.0, including
`Solution` and the integrability audits. All three Solution theorems and the
audited integrability results use only `propext`, `Classical.choice`, and
`Quot.sound`. On 2026-11-05, a fresh `lake comparator` accepted all three
comparisons and Lean's kernel accepted the solution. That local macOS run used
`--inadvisably-no-sandbox`; the official Linux preflight is a separate check.
No Palomar review or registration is claimed.

## Mathematical content

For positive spatial dimension, the discounted stationary first-order MFG
system is

$$
-u-H(x,Du,m)+V(x)=0,\qquad
m-\operatorname{div}(mD_pH(x,Du,m))-1=0.
$$

The results assume the paper's positive-mass regularity and monotonicity,
the appropriate growth condition, and the stated dual integrability of the
potential. They address three cases:

| Source label | Claim | Proof entry point |
|---|---|---|
| `thm:main-simple.power.growth` | Existence of strong solutions under standard power growth | [SimplePower/Paper.lean](StationaryMFG/Theorems/SimplePower/Paper.lean) |
| `thm:main-congestion.growth` | Existence of strong solutions under singular congestion growth | [Congestion/PaperMain.lean](StationaryMFG/Theorems/Congestion/PaperMain.lean) |
| `thm:main-weak.power.growth` | Existence of weak solutions under weak growth | [InfimalConvolution/PaperMain.lean](StationaryMFG/Theorems/InfimalConvolution/PaperMain.lean) |

Each conclusion includes the solution predicate, density integrability,
Sobolev membership, nonnegativity almost everywhere, identification of the
returned `Du` as the weak derivative of `u`, and the claimed integrability of
each component of `Du`. The exponents are
$\bar\beta=\beta+1$ and
$\bar\gamma=\alpha(\beta+1)/\beta$, with $\alpha>1$, $\beta>0$.

A strong solution satisfies the Hamilton–Jacobi inequality almost everywhere,
equality on positive density, and the transport equation against every smooth
periodic test function. Its flux is integrable. In the congestion theorem,
the Hamiltonian's boundary value can be infinite, and the continuous limiting
flux at zero mass need not be zero.

A weak solution satisfies the paper's variational inequality for bounded test
densities bounded away from zero and test potentials with bounded weak
derivatives. The weak-growth theorem assumes no boundary condition on the
original Hamiltonian. Internal regularization and boundary-continuity results
are proved in the development, not additional inputs to the three claims.

These are the paper's strong and monotone-operator weak solution concepts;
“strong” does not mean a classical smooth solution. Existence is the subject
of the comparison, not uniqueness, classical regularity, or numerical
convergence.

## Representation conventions and scope

Read the full Challenge statements and their definitions when assessing
correspondence with the paper.

- The spatial dimension satisfies `0 < d`. Integrals use the half-open unit
  cube in `Fin d → ℝ`. Periodic weak tests encode the torus formulation;
  the public interface uses bare functions rather than quotient spaces.
- Momentum uses the finite-dimensional sup norm. Equivalence with the
  Euclidean norm changes the constants in growth estimates. Positive-mass
  measurability is expressed using the Borel measurable structure.
- `H` and `DpH` are total Lean functions, but their input conditions concern
  positive mass. `DpH` is certified to be the actual momentum derivative.
  Strong solutions evaluate the Hamiltonian at vacuum by its extended-real
  right limit, rather than by an arbitrary supplied value of `H` at zero.
- The congestion theorem takes an extended flux `J` agreeing with `m DpH`
  at positive mass and satisfying the paper's continuity condition. It also
  uses the explicit periodicity of the representative `V` in its proof.
  All three Challenge statements require a periodic representative of `V`.
- Weak test densities use an everywhere-positive lower bound on a chosen
  representative. An essentially positive density has such a representative
  after a null-set modification. The relevant integrals are unchanged.
- The separate weak-gradient and gradient-integrability conclusions matter:
  `MemSobolevPer` alone does not supply the complete claimed gradient
  regularity.

Mathlib's Bochner integral is totalized: a nonintegrable integrand evaluates
to zero. Consequently, an isolated integral equality is not a sufficient
solution definition. Here the complete theorem hypotheses and conclusions
supply the missing integrability. For the transport identity, `m` and `J`
are integrable, and the smooth periodic test and its gradient are bounded
on the cube. For the weak variational inequality, the growth and regularity
hypotheses and the returned function-space bounds supply Hölder estimates
for every admissible test pair. Read the solution predicates together with
these ambient conditions, not as claims about arbitrary bare functions.
The supporting derivations are retained in [Integrability.lean](Integrability.lean).

The public reference is the versioned
[arXiv v3 paper](https://arxiv.org/abs/2506.21212v3), whose
[TeX source](https://arxiv.org/src/2506.21212v3) contains the labels in the table.
The development originally used a revised local manuscript. We compared its
three theorem statements, two solution definitions, four monotonicity/growth
assumptions, three standing Hamiltonian hypotheses, and exponent equation with
arXiv v3: all 13 blocks have identical TeX after removing comments and
normalizing whitespace. [The correspondence record](reference/source-correspondence.json)
contains exact source and block hashes. The complete manuscripts differ, and
this scoped textual comparison does not replace review of the Lean statements.
No manuscript copy or typesetting dependencies are needed in this repository.

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
lake env lean Integrability.lean
lake comparator --config comparator.json
```

The comparator command uses Linux `bubblewrap` for isolation. On a trusted
local checkout on macOS, `lake comparator --inadvisably-no-sandbox` runs the
comparison without that isolation; the official Linux preflight is a separate
check.

`lean-toolchain` selects Lean, and `lake-manifest.json` fixes the exact dependency
revisions. The compared Solution declarations must use only `propext`,
`Classical.choice`, and `Quot.sound`. The three intentional Challenge holes
must not occur in their proof dependencies.

For any later change, rerun Comparator against the actual source snapshot.
A historical comparison from the predecessor repository is not a substitute. A successful comparison establishes that the proved Solution
matches the independently specified Challenge; mathematical review must also
check that the Challenge expresses the cited paper results. Palomar applies
its own verification and review before any registration.

For its current mechanical checks, dispatch the **Palomar mechanical
preflight** workflow from GitHub Actions after pushing the exact source
commit. It calls the official verifier at an immutable revision and checks
the Challenge/Solution pair in the verifier's Linux environment. The workflow
produces a report artifact; it does not submit to or register with Palomar.
It is restricted to the maintained repository because its authorization
statement must not automatically be inherited by a fork.

## Provenance and contents

Diogo Gomes maintains this repository. The original development used Claude
agents with human guidance. ChatGPT, working through Codex, subsequently
supplied the boundary-continuity proofs and their Lean formalization, repaired
the paper-facing theorem interfaces and proofs, checked the challenge,
audited integral integrability, and prepared this source distribution and
toolchain port. [formalization.yaml](formalization.yaml) records source
authorship, automation, scope, and review status. This account does not claim
independent human peer review or endorsement by every paper author.

The original project is [StationaryMFG](https://github.com/dlcvag/StationaryMFG),
with source checkpoint `9cdc7dad5e84da878959fc382b2a0c852a93b874`. This distribution
includes the proof source itself; access to that development repository is
not required. The bare-function infrastructure was informed by
[DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi) and
[LpSpaces](https://github.com/dlcvag/LpSpaces), neither of which is imported
as a Lean dependency. Attributions to adapted material remain in the source.
Internal task labels and source line numbers are retained from the development
history; use Challenge and Solution for the current theorem interfaces.

The repository retains the independent specification, its solution bridge,
the proof dependency closure, build configuration, metadata, and concise
checking instructions. It omits task archives, agent configuration, historical
reports, generated appendices, development caches, and compiled artifacts.

The Lean code is licensed under [Apache-2.0](LICENSE). The cited manuscript
retains its authors' rights and is not relicensed by the code licence.
Mathlib and other dependencies retain their respective licences.
