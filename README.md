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
`Quot.sound`. On 2026-11-11, a fresh `lake comparator` accepted all three
comparisons after making integrability explicit in the weak-solution
predicate, and Lean's kernel accepted the solution. The contextual
equivalence with the former inequality-only condition also compiles using
only the standard axioms. That local macOS run used
`--inadvisably-no-sandbox`; a local manifest records 156 unchanged proof/build
input hashes before and after comparison. The [official Linux preflight](https://github.com/dlcvag/StationaryMFG-Palomar/actions/runs/42484842541)
passed on 2026-11-08 for commit `47150df`, including Comparator and the challenge
provenance audit. That preflight predates the later source refactors; each
submission must use a snapshot with its own passing preflight.
No Palomar editorial review or registration of this revised snapshot is claimed.

## Mathematical content

For positive spatial dimension, the discounted stationary first-order MFG
system is

$$
-u-H(x,Du,m)+V(x)=0,\qquad
m-\mathrm{div}(mD_pH(x,Du,m))-1=0.
$$

The results assume the paper's positive-mass regularity and monotonicity,
the appropriate growth condition, and the stated dual integrability of the
potential. They address three cases:

| Source label | Claim | Proof entry point |
|---|---|---|
| `thm:main-simple.power.growth` | Existence of strong solutions under standard power growth | [SimplePower/Paper.lean](StationaryMFG/Theorems/SimplePower/Paper.lean) |
| `thm:main-congestion.growth` | Existence of strong solutions under singular congestion growth | [Congestion/PaperMain.lean](StationaryMFG/Theorems/Congestion/PaperMain.lean) |
| `thm:main-weak.power.growth` | Existence of weak solutions under weak growth | [InfimalConvolution/PaperMain.lean](StationaryMFG/Theorems/InfimalConvolution/PaperMain.lean) |

Each conclusion includes the solution predicate and the named conditions in
`SolutionRegularity α β m u Du`: density integrability, nonnegativity of `m`
almost everywhere, and `HasSobolevGradient` for `u` and the returned `Du`.
The latter explicitly requires integrability of `u`, integration by parts
identifying `Du` as its weak gradient, and integrability of each gradient
component. The explicit `Du` supplies the Sobolev derivative witness; there is
no additional existential witness. The exponents are
$\bar\beta=\beta+1$ and
$\bar\gamma=\alpha(\beta+1)/\beta$, with $\alpha>1$, $\beta>0$.

A strong solution satisfies the Hamilton–Jacobi inequality almost everywhere,
equality on positive density, and the transport equation against every smooth
periodic test function. Its flux is integrable. In the congestion theorem,
the Hamiltonian's boundary value can be infinite, and the continuous limiting
flux at zero mass need not be zero.

A weak solution requires an integrable variational integrand with nonnegative
integral for every bounded test density bounded away from zero and every test
potential with bounded weak derivatives. The weak-growth theorem assumes no
boundary condition on the original Hamiltonian. Internal regularization and boundary-continuity results
are proved in the development, not additional inputs to the three claims.

These are the paper's strong and monotone-operator weak solution concepts;
“strong” does not mean a classical smooth solution. Existence is the subject
of the comparison, not uniqueness, classical regularity, or numerical
convergence.

## Representation conventions and scope

Read the full Challenge statements and their definitions when assessing
correspondence with the paper.

The file has five sections: periodic calculus and function spaces; standing
assumptions and the three growth alternatives; boundary conventions; solution
regularity and solution concepts; and the three existence theorems. Each
theorem's comment gives its paper label. `HypothesisMonotone` contains the
shared regularity (H1) and monotonicity (A1), while the growth structures state
the respective bounds (A2), (A3), and (A4), including the congestion flux
extension. Regularity appears once in each theorem's assumptions: removing
its duplicate copy from the growth structures changes only the packaging,
not the mathematical hypotheses. The bridge reconstructs the proof library's
growth bundles using the shared regularity.

- The spatial dimension satisfies `0 < d`. Integrals use the half-open unit
  cube in `Fin d → ℝ`. Periodic weak tests encode the torus formulation;
  the public interface uses bare functions rather than quotient spaces.
  Restricting the returned functions to this cube and periodizing them gives
  torus functions. `MemLpPer` abbreviates Mathlib's `MemLp` on the cube; it
  supplies almost-everywhere strong measurability and the finite Lp norm, but
  does not itself assert periodicity.
- Momentum uses the finite-dimensional sup norm. Equivalence with the
  Euclidean norm changes the available growth constants, preserving the
  exponents and the class of Hamiltonians. Positive-mass measurability is
  expressed using the Borel measurable structure.
- `H` and `DpH` are total Lean functions, but their input conditions concern
  positive mass. `DpH` is certified to be the actual momentum derivative.
  No independent convexity, fundamental-theorem-of-calculus,
  `DpH`-measurability, or derived-estimate premise is imposed. The supplied
  values of `H` at nonpositive mass need not be measurable or periodic.
  Strong solutions evaluate the Hamiltonian at vacuum by its extended-real
  right limit `Hext`, which may be positive infinity. Monotonicity gives this
  limit for almost every `x` and every `p`; proving this is part of the
  challenge. Equality to the supplied real value `H x p 0` is never assumed.
- The congestion theorem takes an extended flux `J` agreeing with `m DpH`
  at positive mass and satisfying the paper's continuity condition, without
  a separate measurability premise. Its limiting value at zero need not
  vanish. Simple growth uses the canonical zero flux at zero; weak growth
  needs no boundary-flux assumption because its test densities are positive.
  The congestion proof also uses the periodicity of the representative `V`.
  All three Challenge statements require a periodic representative of `V`.
- Smooth periodic tests are `C∞`, not analytic. Their classical gradient
  `φ.gradient x` is explicitly defined using `fderiv` in the standard basis;
  `φ.gradient x i` is the partial derivative in coordinate `i`. The challenge
  only needs these derivative values; the proof development establishes that
  the partial derivatives are themselves smooth periodic functions when that
  property is used.
- Weak derivatives are specified by integration by parts against every smooth
  periodic test. `HasSobolevGradient` collects these identities and the Lp
  bounds on the function and its specified gradient. It is used both in
  `SolutionRegularity` and, at exponent `∞`, in the admissible weak-test
  predicate. There is no additional existential Sobolev witness in the
  challenge.
- Gradients have type `Point d → Point d`: `Du x` is the gradient vector at
  `x`, and `Du x i` is its `i`th component. Coordinatewise weak-derivative
  and integrability conditions use `fun x => Du x i`. `Solution.lean`
  transposes the arguments to connect this convention to the proof library's
  coordinate-first derivative families.
- Weak test densities use an everywhere-positive lower bound on a chosen
  representative. An essentially positive density has such a representative
  after a null-set modification. The relevant integrals are unchanged.

The challenge keeps the derivative formulas, growth inequalities, boundary
extension, and solution conditions explicit. Its `⬝` notation denotes Mathlib's
`dotProduct`, the sum of coordinatewise products; there is no separate project
definition of that operation. This leaves the coordinate space's sup norm
unchanged. Mathlib also supplies the elementary continuous linear map used for
the momentum derivative. Only the three main existence
theorems have proof holes; the simplifications introduce no additional
unproved definitions or assumptions. `Solution.lean` proves equivalence of the
compact function-space, solution, and regularity conditions with their
counterparts in the included proof development.

Mathlib's Bochner integral is totalized: a nonintegrable integrand evaluates
to zero. `IsWeakSolution` therefore explicitly requires `Integrable` for
every admissible test, as well as the variational inequality. The existing
growth and regularity assumptions and witness bounds prove integrability
of each summand using Hölder estimates; no hypothesis is added to the main
theorem. The challenge names the integrand with a local `let`, so the formula
appears only once. For the transport identity, density regularity and the
explicit flux-integrability clause make both terms integrable, since smooth
periodic tests and their gradients are bounded on the cube. The same bounded
multiplier argument makes both sides of the weak-derivative identities
integrable at the stated Sobolev exponents. The supporting independent
derivations and `WeakIntegrabilityAudit.paper_iff_variational_inequality` are
retained in [Integrability.lean](Integrability.lean). The latter proves
equivalence with the former inequality-only condition under the unchanged
theorem assumptions and witness regularity.

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
not required.

We acknowledge **Scott Armstrong and Julia Kempe's
[DeGiorgi project](https://github.com/scottnarmstrong/DeGiorgi)**, a Lean
formalization of elliptic De Giorgi–Nash–Moser theory, described in their
[companion paper](https://arxiv.org/abs/2604.05984). It contributed to the
auxiliary periodic analysis in this development in the following ways:

- Its organization of Lp and Sobolev spaces using ordinary functions, together
  with the strategy of proving smooth estimates and extending them by density,
  informed our periodic function-space design.
- We adapted its weighted power-mean/Hölder estimate as
  [weighted_power_mean_setIntegral](StationaryMFG/Periodic/Poincare.lean#L1474),
  from [DeGiorgi/Poincare.lean](https://github.com/scottnarmstrong/DeGiorgi/blob/4c1b3077d3782b24065184df4ba59501b2e56fc7/DeGiorgi/Poincare.lean#L1224).
- We adapted its Jensen estimate for the Lp norm of an average as
  [eLpNorm_const_average_le](StationaryMFG/Periodic/SobolevPoincare.lean#L73),
  from [DeGiorgi/SobolevPoincare.lean](https://github.com/scottnarmstrong/DeGiorgi/blob/4c1b3077d3782b24065184df4ba59501b2e56fc7/DeGiorgi/SobolevPoincare.lean#L123).
  These estimates are used in the periodic Poincaré/Sobolev infrastructure.

DeGiorgi is not imported as a Lean dependency; the adapted proofs are included
here and retain their source attributions. The stationary MFG existence
arguments are developed in this repository.

Internal task labels and source line numbers are retained from the development
history; use Challenge and Solution for the current theorem interfaces.

The repository retains the independent specification, its solution bridge,
the proof dependency closure, build configuration, metadata, and concise
checking instructions. It omits task archives, agent configuration, historical
reports, generated appendices, development caches, and compiled artifacts.

The Lean code is licensed under [Apache-2.0](LICENSE). The cited manuscript
retains its authors' rights and is not relicensed by the code licence.
Mathlib and other dependencies retain their respective licences.
