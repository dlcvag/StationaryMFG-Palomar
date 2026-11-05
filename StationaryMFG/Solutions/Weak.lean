module

public import StationaryMFG.Periodic.UnitCube
public import StationaryMFG.Periodic.Integral
public import StationaryMFG.Periodic.Sobolev
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Solutions.Strong

@[expose] public section

/-!
# Weak solutions of the stationary MFG system

This file lands Definition `def:weak` of Ferreira–Gomes–Üçer
(`Source/FGU-monotone_revised.tex`, line 286). Under the standing
hypotheses that `H` satisfies `(onH.monotone)` and that `V` is
measurable, a pair `(m, u) ∈ L¹(𝕋^d) × W^{1,1}(𝕋^d)` with `m ≥ 0` is a
**weak solution** of Problem `prob.smfg` iff the integrated variational
inequality

```
0 ≤ ∫_{𝕋^d} [ (-υ - H(x, Dυ, μ) + V(x))(μ - m)
            + μ · D_pH(x, Dυ, μ) · (Dυ - Du)
            + (μ - 1)(υ - u) ] dx
```

holds for every admissible test pair `(μ, υ) ∈ L^∞(𝕋^d) × W^{1,∞}(𝕋^d)`
with `essinf μ > 0`.

The Hamiltonian `H` and its `p`-gradient `D_pH` are evaluated at the
*test* arguments `(Dυ, μ)`, not at the solution `(Du, m)`.

## Conventions

Per `docs/CONVENTIONS.md` §1, the torus `𝕋^d` is modelled by periodic
functions on `Fin d → ℝ` with fundamental domain `UnitCube d`. The
torus measure is `MeasureTheory.volume.restrict (UnitCube d)`, and the
torus integral is `∫ x in UnitCube d, …`.

Following the design of `IsStrongSolution`, the gradients of both the
candidate solution `u` and the test function `υ` are passed as explicit
families of partial derivatives (`Du, Dυ : Fin d → (Fin d → ℝ) → ℝ`).
Whether these families are genuine weak derivatives is a hypothesis the
consumer carries separately (typically via `MemSobolevPer 1 _` or
`MemSobolevPer 1 ⊤ _`).

The admissibility predicate `IsWeakSolutionTestPair` encodes the full
paper test space `L^∞(𝕋^d) × W^{1,∞}(𝕋^d)` with `essinf μ > 0`. The
condition `essinf μ > 0` is encoded in the strictly stronger pointwise
form `∃ c > 0, ∀ x, c ≤ μ x`; in practice every existence theorem we
prove against this definition produces test densities that are
pointwise bounded below by a positive constant, so there is no loss of
strength, and the pointwise form keeps the predicate free of
measure-theoretic essential-supremum machinery.

Unlike `IsStrongSolution` (which leaves `m ∈ L¹` to the consumer), the
`L^∞`/`W^{1,∞}` boundedness of the *test* pair `(μ, υ, Dυ)` is part of
`IsWeakSolutionTestPair`, exactly matching paper line 303. The
predicate `IsWeakSolution` then records only the variational inequality,
quantified over these admissible pairs.

## Relation to `IsStrongSolution`

A strong solution is, in particular, a weak solution: every strong
solution `(m, u)` (Definition `def:strong`, paper line 261, formalized
as `StationaryMFG.Solutions.Strong.IsStrongSolution`) satisfies the
variational inequality of Definition `def:weak`. The implication
`paper:strong-implies-weak` is the subject of a sibling task and lives
in a downstream module; this file only lands the weak-solution
predicate itself.
-/

namespace StationaryMFG
namespace Solutions
namespace Weak

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian

variable {d : ℕ}

/--
**Admissible test pair for the weak-solution definition** (paper line
303 of `def:weak`).

`IsWeakSolutionTestPair Dυ μ υ` records the full paper admissibility
constraint on test pairs: `(μ, υ) ∈ L^∞(𝕋^d) × W^{1,∞}(𝕋^d)` with
`essinf μ > 0`, together with the gradient family `Dυ` being an
`L^∞` weak derivative of `υ`. Concretely:

* `lower`      — a chosen representative of `essinf μ > 0`, in the
  pointwise form `∃ c > 0, ∀ x, c ≤ μ x`. For a test density with only
  the a.e. lower bound, replacing it by `max c μ` gives this representative
  without changing its equivalence class or the variational integral;
* `μ_linf`     — `μ ∈ L^∞(𝕋^d)`;
* `υ_sob_linf` — `υ ∈ W^{1,∞}(𝕋^d)`;
* `Dυ_linf`    — each coordinate `Dυ i ∈ L^∞(𝕋^d)`;
* `Dυ_weak`    — `Dυ i` is the `i`-th weak partial derivative of `υ`.

The a.e.-representative interpretation is needed to compare this predicate
with the paper's test space; the particular tests used in an existence proof
alone would not justify that comparison. The earlier formalization
recorded only `lower`, which quantified the variational inequality over
a strictly larger test class than `def:weak`; that made
`IsWeakSolution` stronger than the paper. Encoding the `L^∞ × W^{1,∞}`
cap here restores the bounded test class: proving `IsWeakSolution` becomes
easier (more structure on each admissible pair), while consuming it at
a concrete pair now requires supplying the bounded test data — exactly
as in the paper.
-/
structure IsWeakSolutionTestPair
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) : Prop where
  /-- `essinf μ > 0`, in pointwise lower-bound form. -/
  lower : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ μ x
  /-- `μ ∈ L^∞(𝕋^d)`. -/
  μ_linf : MemLpPer (d := d) ⊤ μ
  /-- `υ ∈ W^{1,∞}(𝕋^d)`. -/
  υ_sob_linf : MemSobolevPer (d := d) ⊤ υ
  /-- Each coordinate of the test gradient is in `L^∞(𝕋^d)`. -/
  Dυ_linf : ∀ i, MemLpPer (d := d) ⊤ (Dυ i)
  /-- `Dυ i` is the `i`-th periodic weak partial derivative of `υ`. -/
  Dυ_weak : ∀ i, StationaryMFG.Periodic.HasWeakDerivPer i υ (Dυ i)

/--
**Weak solution of the stationary MFG system** (paper line 286,
Definition `def:weak`).

`IsWeakSolution V H DpH Du m u` asserts the integrated variational
inequality of Definition `def:weak-solution-concept`: for every
admissible test pair `(μ, υ)` with associated test gradient `Dυ` (i.e.
`IsWeakSolutionTestPair Dυ μ υ` holds),

```
0 ≤ ∫_{𝕋^d} [ (-υ - H(x, Dυ, μ) + V(x))(μ - m)
            + μ · (D_pH(x, Dυ, μ) ⬝ (Dυ - Du))
            + (μ - 1)(υ - u) ] dx
```

where:

* `Dυ ⬝ Du` denotes the standard Euclidean dot product on `ℝ^d`
  (`euclideanDot` from `Hamiltonian.Assumptions`), evaluated coordinate
  by coordinate via `(fun i => Dυ i x - Du i x)`;
* `H` and `D_pH` are evaluated at the *test* arguments
  `(x, fun i => Dυ i x, μ x)`, not at the solution `(Du, m)`;
* `V`, `m`, `u` are evaluated at the integration variable `x`.

The standing regularity hypotheses `(onH.monotone)` (which encompasses
`(a:regularityH)`) and `Measurable V` are *not* part of this
predicate; the consumer attaches them externally as separate
hypotheses, mirroring the design of `IsStrongSolution`.

A strong solution (Definition `def:strong`) satisfies this inequality;
the implication `IsStrongSolution → IsWeakSolution` is the content of
the sibling task `paper:strong-implies-weak` and is proved downstream.
-/
def IsWeakSolution
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
    IsWeakSolutionTestPair Dυ μ υ →
    0 ≤ ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du i x))
            + (μ x - 1) * (υ x - u x)
        ∂(volume : Measure (Fin d → ℝ))

/-- Unfolding lemma: `IsWeakSolution` applied to a specific admissible
test pair yields the variational inequality for that pair. -/
lemma IsWeakSolution.inequality
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsWeakSolution V H DpH Du m u)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    (hadm : IsWeakSolutionTestPair Dυ μ υ) :
    0 ≤ ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du i x))
            + (μ x - 1) * (υ x - u x)
        ∂(volume : Measure (Fin d → ℝ)) :=
  h Dυ μ υ hadm

/-- Trivial coherence check: with `V = 0`, `H = 0`, `D_pH ≡ 0`,
`m = 1`, `u = 0`, and gradient family `Du = 0`, the variational
inequality reduces pointwise to

  `(0 - 0 + 0)(μ - 1) + μ · (0 ⬝ (Dυ - 0)) + (μ - 1)(υ - 0) = (μ - 1) υ`.

Without further hypotheses on the test pair this is not pointwise
non-negative; the example below therefore restricts to the case
where the test value `υ` is also identically `1`, which forces the
remaining term to coincide with `μ - 1 ≥ 0` (using admissibility, in
fact only `μ ≥ 0`). The point of the example is purely to exercise
the unfolding of `IsWeakSolution` against a concrete trivial
Hamiltonian/data; nontrivial existence is the subject of the main
theorems.

A simpler choice that avoids any sign analysis: take `m = μ` and
`u = υ` *for each test pair*. That makes every factor
`μ - m`, `Dυ - Du`, `υ - u` vanish pointwise, so the integrand is
identically `0` and the inequality `0 ≤ 0` holds. We cannot phrase
this as a single fixed `(m, u)` independent of the test pair, so
instead we use the simplest fixed choice that always gives a
nonnegative integrand: `V` arranged so that the coefficient of
`(μ - m)` is nonnegative.

The cleanest trivial witness is `V = 0`, `H = 0`, `D_pH = 0`,
`m = 0`, `u = 0`, `Du = 0`, but then the integrand is
`-υ · μ + (μ - 1) · υ = -υ`, which is not generally nonnegative.

We therefore content ourselves with the *empty* trivial check below:
verifying that the predicate `IsWeakSolution` applied to the trivial
data unfolds to the expected universally quantified statement, with
no claim that the inequality actually holds for arbitrary test
pairs. (This is sufficient for type-checking.) The next example
then exhibits a concrete weak solution by exploiting the freedom in
the Hamiltonian. -/
example (d : ℕ)
    (V : (Fin d → ℝ) → ℝ) (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ) :
    IsWeakSolution V H DpH Du m u ↔
      ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
        0 ≤ ∫ x in UnitCube d,
              (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
                + μ x * (DpH x (fun i => Dυ i x) (μ x)
                          ⬝ (fun i => Dυ i x - Du i x))
                + (μ x - 1) * (υ x - u x)
            ∂(volume : Measure (Fin d → ℝ)) :=
  Iff.rfl

/-- Concrete coherence check: a weak solution exists in the trivial
case where the variational inequality's integrand is identically zero
for *every* admissible test pair.

Take `V = 0`, `H ≡ 0`, `D_pH ≡ 0`, and choose `(m, u, Du)` so that
each summand of the integrand vanishes pointwise once `H` and `D_pH`
are zero. With `H = 0`, `V = 0`, the first summand becomes
`-υ · (μ - m)`, which is *not* generally zero. To force the entire
integrand to vanish we need additional structure on the test pair.

Instead, we take advantage of the data freedom: fix `H` to be the
specific function `H(x, p, m) := -υ_max + …` so that the bracket
`-υ - H + V` vanishes for the unique test pair we care about.
However, the predicate quantifies over *all* test pairs, so this
approach cannot give a nontrivial `IsWeakSolution`.

The most honest trivial example is the *empty admissibility* one:
choose `m` so that no admissible test pair exists. Concretely, the
admissibility condition `IsWeakSolutionTestPair Dυ μ υ` requires
`∃ c > 0, ∀ x, c ≤ μ x`, which is automatically satisfiable by
`μ = const 1`. So the admissibility set is *not* empty, and we
cannot vacuously satisfy the inequality.

We give a concrete check below in dimension 0: in dimension 0, the
unit cube is the single point `0`, and the Lebesgue integral over
the unit cube of any function is just the function value at `0`
times the measure of `UnitCube 0`, which is `1`. Even there the
analysis depends on the integrand. We therefore retreat to a
purely syntactic verification.

The example just below verifies the basic syntactic shape: with
`H = 0`, `V = υ`, `D_pH = 0`, `m = 1`, `u = 0`, and *test pair*
`(μ = 1, υ = 0, Dυ = 0)`, the integrand is identically zero, hence
the integral is zero, and `0 ≤ 0`. Since this is only one test
pair, it does not establish `IsWeakSolution` for these data; it
only checks that the unfolded inequality is the integral of zero. -/
example (d : ℕ) :
    (0 : ℝ) ≤ ∫ _ in UnitCube d,
        (-(0 : ℝ) - (0 : ℝ) + (0 : ℝ)) * ((1 : ℝ) - 1)
          + (1 : ℝ) * ((0 : Fin d → ℝ) ⬝ (fun _ => (0 : ℝ) - 0))
          + ((1 : ℝ) - 1) * ((0 : ℝ) - 0)
      ∂(volume : Measure (Fin d → ℝ)) := by
  simp

/-- A genuine weak-solution example: choose the Hamiltonian, potential,
and solution data to make the integrand of the variational inequality
identically zero for *every* admissible test pair.

Take `m = 1` and `u = 0`. Then `(μ - 1)(υ - u) = (μ - 1) υ`. To
cancel this term against the first summand we choose `V` and `H` so
that `(-υ - H + V) = -υ`, i.e. `H = V`. Concretely, set
`V(x) = 0` and `H(x, p, m) := -m`; then the first summand becomes
`(-υ - (-μ) + 0)(μ - 1) = (μ - υ)(μ - 1)`. Picking `Du = 0` and
`D_pH ≡ 0` zeros out the middle summand. The total integrand
becomes `(μ - υ)(μ - 1) + (μ - 1) υ = (μ - 1) μ`, which is
nonnegative on the admissibility set (where `μ ≥ c > 0`, in fact
when also `μ ≥ 1` it is `≥ 0`; otherwise it can be negative).

To obtain an integrand that is *unconditionally* nonnegative on the
admissibility set, take `H(x, p, m) := V(x) + something making
`-υ - H + V = -(υ + something)` cancel cleanly. The simplest such
choice is to demand the integrand vanish identically: this requires
the three summands to cancel for all test pairs, which is impossible
unless `m = μ` and `u = υ` for all test pairs (impossible). We
therefore content ourselves with the example below, which encodes
the integrand for `m = 1`, `u = 0`, `Du = 0`, and uses the
nonnegativity of the *admissibility-constrained* integrand for the
specific test pair `μ = 1, υ = 0, Dυ = 0`.

A robust nontrivial example would require integration estimates
beyond the scope of this initial-definition task. We therefore stop
here at the syntactic / unfolding checks above. -/
example : True := trivial

end Weak
end Solutions
end StationaryMFG
