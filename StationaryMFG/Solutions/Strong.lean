module

public import StationaryMFG.Periodic.UnitCube
public import StationaryMFG.Periodic.Integral
public import StationaryMFG.Periodic.TestFunctions
public import StationaryMFG.Hamiltonian.Assumptions

@[expose] public section

/-!
# Strong solutions of the stationary MFG system — HJB clause

This file opens the `Strong`-solution layer of the project. Following
Definition `def:strong` of Ferreira–Gomes–Üçer
(`Source/FGU-monotone_revised.tex`, lines 261–277), a strong solution
of Problem `prob.smfg` is a pair `(m, u) ∈ L^1(𝕋^d) × W^{1,1}(𝕋^d)`
with `m ≥ 0` and `m · D_pH(x, Du, m) ∈ L^1(𝕋^d; ℝ^d)` for which:

1. (HJB clause, `def:hjb-strong`, line 264.) The Hamilton–Jacobi
   equation holds in the sense that
   * `u + H(x, Du, m) - V(x) ≤ 0`               a.e. in `𝕋^d`, and
   * `u + H(x, Du, m) - V(x) = 0`               a.e. on `{m > 0}`.
2. (Transport clause, `def:transport-strong`, line 271.)
   `∫_{𝕋^d} [(m-1) φ + m D_pH(x, Du, m) · Dφ] dx = 0` for all
   `φ ∈ C^∞(𝕋^d)`.

This file lands clause (1) only. The transport clause (2) is the
sibling task `paper:def:strong.b` and lives in the same module.

## Conventions

Per `docs/CONVENTIONS.md` §1, the torus `𝕋^d` is modelled by periodic
functions on `Fin d → ℝ` with fundamental domain `UnitCube d`. The
torus measure is `MeasureTheory.volume.restrict (UnitCube d)`.

Following `MemSobolevPer` (which leaves the weak-derivative witness
existential), we keep the gradient `Du` of `u` *explicit* in the type
of `IsStrongSolution_HJB`: it is a family
`Du : Fin d → (Fin d → ℝ) → ℝ`, so that the value
`(Du · x) := fun i => Du i x` is the candidate `D u(x) ∈ ℝ^d`.
Whether the family is genuinely a weak derivative is a hypothesis
that the consumer of this predicate carries separately (typically
`MemSobolevPer 1 u` with witness `Du`).

In the set `{m = 0}` the expression `H(x, Du, m)` must be evaluated in
the sense of paper hypothesis `(a:Hat0)`; this `Hat0` reading is
*deferred* at the level of this predicate. The signature stores the
raw Hamiltonian `H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ` and the
predicate evaluates `H x (Du · x) (m x)` directly. Downstream lemmas
that need to reason about `H(x, p, 0)` should attach a hypothesis
`HypothesisHat0 H` (see `StationaryMFG/Hamiltonian/Assumptions.lean`)
and bridge through `H_at_zero`.
-/

namespace StationaryMFG
namespace Solutions
namespace Strong

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian

variable {d : ℕ}

/--
**HJB clause of the strong-solution definition** (`def:hjb-strong`,
paper line 264).

`IsStrongSolution_HJB V H Du m u` asserts:

* `u(x) + H(x, Du(x), m(x)) - V(x) ≤ 0`  for almost every `x ∈ 𝕋^d`
  (with respect to the Lebesgue measure restricted to the unit cube),
  and
* `u(x) + H(x, Du(x), m(x)) - V(x) = 0`  for almost every
  `x ∈ {m > 0}`.

The gradient `Du` is passed as an explicit family
`Du : Fin d → (Fin d → ℝ) → ℝ` of partial derivatives; the value
`Du · x := fun i => Du i x` is plugged into `H` in the second slot.

The interpretation of `H(x, p, 0)` at `m = 0` is deferred to paper
hypothesis `(a:Hat0)`; this predicate evaluates `H` literally on the
given `m`.
-/
def IsStrongSolution_HJB
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0) ∧
  (∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0)

/-- The HJB inequality, as an a.e. statement on the torus. -/
lemma IsStrongSolution_HJB.ae_le
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_HJB V H Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 :=
  h.1

/-- The HJB equality on `{m > 0}`, as an a.e. statement on the torus. -/
lemma IsStrongSolution_HJB.ae_eq_on_pos
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_HJB V H Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0 :=
  h.2

/-- Trivial coherence check: with `V = 0`, `H = 0`, `m = 1`,
`u = 0`, and gradient family `Du = 0`, the HJB clause is vacuously
satisfied (the residual `u + H - V` is identically `0`). -/
example (d : ℕ) :
    IsStrongSolution_HJB (d := d)
      (V := fun _ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (Du := fun _ _ => (0 : ℝ))
      (m := fun _ => (1 : ℝ))
      (u := fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall ?_
    intro x
    simp
  · refine Filter.Eventually.of_forall ?_
    intro x _
    simp

/-!
## Transport clause (paper `def:transport-strong`, line 271)

The second clause of Definition `def:strong` asserts that the pair `(m, u)`
satisfies the transport equation in the *integrated* (weak) sense

```
∫_{𝕋^d} [(m - 1) φ + (m · D_pH(x, Du, m)) · Dφ] dx = 0  for all φ ∈ C^∞(𝕋^d).
```

Per the closing sentence of `def:strong` (paper line 276), on the set
`{m = 0}` the expression `m · D_pH(x, Du, m)` must be evaluated in the
sense of paper hypothesis `(a:mDpHat0)`. Concretely, that hypothesis
selects a joint-continuous extension `J : 𝕋^d × ℝ^d × ℝ^+_0 → ℝ^d` of the
product `m · D_pH` to the closed half-line `m ≥ 0`. We carry that
extension `J` as an explicit argument to the predicate (matching the way
`HypothesismDpHat0` is bundled in `StationaryMFG/Hamiltonian/Assumptions.lean`).
On `{m > 0}` the field `J(x, p, m)` agrees with `m • D_pH(x, p, m)` by
`HypothesismDpHat0.J_of_pos`; at `m = 0` it is the limiting value the
hypothesis postulates.

The test-function space is `SmoothPeriodic d` from
`StationaryMFG.Periodic.TestFunctions`, which models `C^∞_per(𝕋^d)`. The
gradient of a test function `φ` is the family
`fun i => SmoothPeriodic.partialDeriv i φ x` of partial derivatives in the
standard basis directions. The dot product against `J(x, Du(x), m(x))` uses
the project-local `dotProduct` (`⬝`) from `Hamiltonian.Assumptions`.

The integrability assumption `J(·, Du(·), m(·)) ∈ L^1` is part of the
solution definition (paper line 261), not a derived consequence; the
predicate `mDpH_Integrable` records it explicitly.
-/

/--
**Integrability of the flux** `mD_pH(·, Du(·), m(·))` (paper line 261, part
of the preamble of Definition `def:strong`).

`mDpH_Integrable J Du m` asserts that the vector field
`x ↦ J(x, Du(x), m(x))` is Bochner-integrable on the unit cube, i.e. lies in
`L^1(𝕋^d; ℝ^d)`. The function `J` is the extension of `m · D_pH` selected
by paper hypothesis `(a:mDpHat0)` (`HypothesismDpHat0`); on `{m > 0}` it
agrees with `m • D_pH(x, Du(x), m(x))`, and at `m = 0` it is the
limiting value postulated by `(a:mDpHat0)`.
-/
def mDpH_Integrable
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) : Prop :=
  Integrable (fun x => J x (fun i => Du i x) (m x))
    (volume.restrict (UnitCube d))

/--
**Transport clause of the strong-solution definition**
(`def:transport-strong`, paper line 271).

`IsStrongSolution_Transport V J Du m u` asserts:

* (Integrability.) `J(·, Du(·), m(·)) ∈ L^1(𝕋^d; ℝ^d)`, where `J` is the
  extension of `m · D_pH` selected by paper hypothesis `(a:mDpHat0)`.
* (Weak transport equation.) For every smooth periodic test function
  `φ : SmoothPeriodic d`,
  `∫_{𝕋^d} [(m(x) - 1) · φ(x) + J(x, Du(x), m(x)) ⬝ Dφ(x)] dx = 0`,
  where `Dφ(x) := fun i => SmoothPeriodic.partialDeriv i φ x` and `⬝` is
  the standard Euclidean dot product `dotProduct`.

The potential `V` does not appear in the transport equation, but is
threaded through the signature for symmetry with `IsStrongSolution_HJB`
and to ease combination at the level of `Solutions/Strong` aggregator
predicates downstream.

The interpretation of `J(x, p, 0)` at `m = 0` is the content of paper
hypothesis `(a:mDpHat0)` (`HypothesismDpHat0`), which the consumer of this
predicate carries separately when manipulating the integrand on `{m = 0}`.
-/
def IsStrongSolution_Transport
    (V : (Fin d → ℝ) → ℝ)
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  let _ := V; let _ := u
  mDpH_Integrable (d := d) J Du m ∧
    ∀ φ : SmoothPeriodic d,
      ∫ x in UnitCube d,
          (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
            + J x (fun i => Du i x) (m x)
                ⬝ (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ)) = 0

/-- Projection onto the integrability part of the transport clause. -/
lemma IsStrongSolution_Transport.integrable
    {V : (Fin d → ℝ) → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_Transport V J Du m u) :
    mDpH_Integrable (d := d) J Du m :=
  h.1

/-- Projection onto the weak transport equation, quantified over smooth
periodic test functions. -/
lemma IsStrongSolution_Transport.weak_eq
    {V : (Fin d → ℝ) → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_Transport V J Du m u) :
    ∀ φ : SmoothPeriodic d,
      ∫ x in UnitCube d,
          (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
            + J x (fun i => Du i x) (m x)
                ⬝ (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 :=
  h.2

/-- Trivial coherence check: with `V = 0`, `J ≡ 0`, `m = 1`, `u = 0`, and
gradient family `Du = 0`, the transport clause is satisfied. The flux is
identically zero (hence integrable), and the integrand of the weak
transport equation reduces to `(1 - 1) φ + 0 ⬝ Dφ = 0` pointwise, so the
integral vanishes. -/
example (d : ℕ) :
    IsStrongSolution_Transport (d := d)
      (V := fun _ => (0 : ℝ))
      (J := fun _ _ _ => (0 : Fin d → ℝ))
      (Du := fun _ _ => (0 : ℝ))
      (m := fun _ => (1 : ℝ))
      (u := fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- The flux is identically `0`, which is integrable.
    change Integrable (fun _ : Fin d → ℝ => (0 : Fin d → ℝ))
      (volume.restrict (UnitCube d))
    exact integrable_zero _ _ _
  · intro φ
    -- Pointwise the integrand is `(1 - 1) * φ + 0 ⬝ Dφ = 0`.
    simp

/-!
## Bundled strong-solution predicate (paper `def:strong`, line 261)

Definition `def:strong` of Ferreira–Gomes–Üçer combines the two clauses
above into a single notion. Under the standing regularity hypotheses
`(a:regularityH)`, `(a:Hat0)`, and `(a:mDpHat0)` on `H` and the
measurability of `V`, a pair `(m, u) ∈ L¹(𝕋^d) × W^{1,1}(𝕋^d)` with
`m ≥ 0` and `m D_pH(x, Du, m) ∈ L¹(𝕋^d; ℝ^d)` is a **strong solution**
to Problem `prob.smfg` iff both clauses hold.

The regularity hypotheses are not encoded inside the predicate itself:
following the paper-style discussed in `IsStrongSolution_HJB` and
`IsStrongSolution_Transport` above, they are external facts attached by
the consumer (e.g. `HypothesisHat0 H`, `HypothesismDpHat0 d DpH J`,
`Measurable V`) when needed. The predicate `IsStrongSolution` records
only the two equational clauses.
-/

/--
**Strong solution of the stationary MFG system** (paper line 261,
Definition `def:strong`).

`IsStrongSolution V H J Du m u` is the conjunction of the HJB clause
(`IsStrongSolution_HJB`) and the transport clause
(`IsStrongSolution_Transport`):

* `u + H(x, Du, m) - V(x) ≤ 0` a.e. in `𝕋^d`, with equality a.e. on
  `{m > 0}`; and
* `J(·, Du(·), m(·)) ∈ L¹` and the weak transport equation
  `∫ [(m - 1) φ + J(x, Du, m) ⬝ Dφ] dx = 0` holds for every smooth
  periodic test function `φ`.

The raw Hamiltonian `H` enters the HJB clause; the flux extension `J`
of `m · D_pH` (postulated by paper hypothesis `(a:mDpHat0)`) enters the
transport clause. The standing regularity hypotheses
`(a:regularityH)`, `(a:Hat0)`, `(a:mDpHat0)` and the measurability of
`V` are not part of this predicate; consumers attach them externally.
-/
def IsStrongSolution
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  IsStrongSolution_HJB V H Du m u ∧ IsStrongSolution_Transport V J Du m u

/-- Projection onto the HJB clause (`def:hjb-strong`, paper line 264). -/
lemma IsStrongSolution.hjb
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution V H J Du m u) :
    IsStrongSolution_HJB V H Du m u :=
  h.1

/-- Projection onto the transport clause (`def:transport-strong`,
paper line 271). -/
lemma IsStrongSolution.transport
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution V H J Du m u) :
    IsStrongSolution_Transport V J Du m u :=
  h.2

/-!
## Remark on Definition `def:strong` (paper `rmk:onDefStrong`, line 278)

Paper line 278 (the remark immediately following Definition `def:strong`)
records two design choices that we adopt verbatim in `IsStrongSolution`:

1. **Sign convention.** The Hamilton–Jacobi clause is written as
   `u + H(x, Du, m) - V(x) ≤ 0` (equivalently, `H(x, Du, m) ≤ V(x) - u`),
   with the signs *reversed* relative to the original system `smfg` of
   the paper. This formulation is mathematically equivalent and matches
   the standard viscosity-solutions sign convention for stationary
   Hamilton–Jacobi equations, easing comparison with that literature.
2. **Minimality of the function spaces.** The regularity declared in
   `def:strong`, namely `(m, u) ∈ L¹(𝕋^d) × W^{1,1}(𝕋^d)` with `m ≥ 0`
   and `m D_pH(·, Du, m) ∈ L¹(𝕋^d; ℝ^d)`, is the *minimal* functional
   framework needed for the predicate to even make sense. The main
   existence theorems of Ferreira–Gomes–Üçer (formalized in Phases 4–6)
   produce strong solutions in the strictly stronger spaces
   `L^{β̄}(𝕋^d) × W^{1,γ̄}(𝕋^d)` for exponents `β̄, γ̄ > 1` determined
   by the Hamiltonian's growth.

The predicate `IsStrongSolution` therefore takes `m` and `u` as bare
periodic functions (consistent with `docs/CONVENTIONS.md` §1b); any
`L¹`/`W^{1,1}` integrability is supplied by the consumer as a separate
`MemLpPer` / `MemSobolevPer` hypothesis, so that strengthening the
ambient spaces downstream is purely additive on the hypotheses.
-/

/-- Trivial coherence check: with `V = 0`, `H = 0`, `J ≡ 0`, `m = 1`,
`u = 0`, and gradient family `Du = 0`, both clauses are satisfied, so
the bundled predicate `IsStrongSolution` holds. -/
example (d : ℕ) :
    IsStrongSolution (d := d)
      (V := fun _ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (J := fun _ _ _ => (0 : Fin d → ℝ))
      (Du := fun _ _ => (0 : ℝ))
      (m := fun _ => (1 : ℝ))
      (u := fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- HJB clause: residual is identically `0`.
    refine ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall ?_
      intro x
      simp
    · refine Filter.Eventually.of_forall ?_
      intro x _
      simp
  · -- Transport clause: flux is `0` (integrable), and the integrand
    -- reduces pointwise to `0`.
    refine ⟨?_, ?_⟩
    · change Integrable (fun _ : Fin d → ℝ => (0 : Fin d → ℝ))
        (volume.restrict (UnitCube d))
      exact integrable_zero _ _ _
    · intro φ
      simp

/-!
## Phase C transfer: raw `mDpH` flux → paper extension `JsimpleExt`

The raw `Hamiltonian.mDpH DpH` extension and the paper-canonical
extension `Hamiltonian.JsimpleExt DpH` share the same definition
`m • DpH x p m`. Consequently `mDpH DpH = JsimpleExt DpH` as functions,
and any strong-solution witness against `mDpH DpH` carries over to
`JsimpleExt DpH` without further hypotheses.

This lemma is invoked at the headline of
`thm_main_simplePowerGrowth_concrete` to substitute the canonical paper
flux extension (matching paper `def:strong`, line 261) for the raw
`mDpH` extension produced by `main_conclude_isStrongSolution`. See
`docs/THEOREM1_CLOSURE_PLAN.md` Phase C (`infra-P5-theorem1-phase-C-flux-extension-JsimpleExt`).
-/

/-- The raw `mDpH` flux extension and the paper-canonical `JsimpleExt`
extension are equal as functions: both unfold to `m • DpH x p m`. -/
lemma mDpH_eq_JsimpleExt
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) :
    StationaryMFG.Hamiltonian.mDpH DpH
      = StationaryMFG.Hamiltonian.JsimpleExt DpH := by
  rfl

/-- **Phase C flux-extension transfer for the transport clause.** A
strong-solution transport witness against the raw extension
`Hamiltonian.mDpH DpH` carries over to the paper-canonical extension
`Hamiltonian.JsimpleExt DpH`. The two extensions agree on all of `ℝ`
(both equal `m • DpH x p m`), so the transfer is by reflexivity; no
`m ≥ 0` hypothesis is needed.

Lives at the level of `IsStrongSolution_Transport` so that consumers
that only need the transport conjunct can substitute fluxes
independently of the HJB clause. -/
lemma IsStrongSolution_Transport.flux_mDpH_to_JsimpleExt
    {V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_Transport (d := d) V
            (StationaryMFG.Hamiltonian.mDpH DpH) Du m u) :
    IsStrongSolution_Transport (d := d) V
      (StationaryMFG.Hamiltonian.JsimpleExt DpH) Du m u := h

/-- **Phase C flux-extension transfer (bundled).** A strong-solution
witness with the raw extension `Hamiltonian.mDpH DpH` carries over to
the paper-canonical extension `Hamiltonian.JsimpleExt DpH`. The HJB
clause is unaffected; the transport clause transfers by
`flux_mDpH_to_JsimpleExt`. -/
lemma IsStrongSolution.flux_mDpH_to_JsimpleExt
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution (d := d) V H
            (StationaryMFG.Hamiltonian.mDpH DpH) Du m u) :
    IsStrongSolution (d := d) V H
      (StationaryMFG.Hamiltonian.JsimpleExt DpH) Du m u := h

/-!
## Phase C0 transfer: raw HJB ↔ paper `Hext`-formulated HJB on `{m > 0}`

Per `def:strong` (paper line 276), in the set `{m = 0}` the expression
`H(x, Du, m)` must be evaluated in the sense of paper hypothesis
`(a:Hat0)` — that is, via the canonical extension
`Hamiltonian.Hext H` into `WithTop ℝ`. The Lean predicate
`IsStrongSolution_HJB` evaluates raw `H x p (m x)` literally; since
`(hmon, hpow)` do not constrain `H x p 0`, the paper-faithful reading
on `{m = 0}` is captured by the additional hypothesis
`HypothesisHat0 H` (`StationaryMFG/Hamiltonian/Assumptions.lean:150`),
which postulates the right-hand limit at `m = 0⁺` as a member of
`WithTop ℝ`.

On `{m > 0}`, raw `H` and the canonical extension `Hext H` coincide
(by `Hamiltonian.Hext_of_pos`), so the two formulations of the HJB
inequality are *equivalent* on `{m > 0}`. The transfer below records
this trivial equivalence; it is invoked at the headline level
(`thm_main_simplePowerGrowth_concrete`) where `hHat0` is now a
public-surface hypothesis.

See `docs/THEOREM1_CLOSURE_PLAN.md` Phase C0
(`infra-P5-theorem1-phase-C0-Hamiltonian-extension-Hext`).
-/

/-- **Phase C0: pointwise residual equality on `{m > 0}`.** For
`0 < m x`, the cast HJB residual `↑(u x + H x p (m x) - V x)` in
`WithTop ℝ` equals the `Hext`-formulated paper residual
`↑(u x) + Hamiltonian.Hext H x p (m x) - ↑(V x)`. The proof rewrites
`Hext H x p (m x)` to the cast of `H x p (m x)` via `Hext_of_pos`. -/
lemma IsStrongSolution_HJB.Hext_residual_eq_on_pos
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hm : 0 < m x) :
    ((u x + H x (fun i => Du i x) (m x) - V x : ℝ) : WithTop ℝ)
      = ((u x : ℝ) : WithTop ℝ)
          + StationaryMFG.Hamiltonian.Hext H x (fun i => Du i x) (m x)
          - ((V x : ℝ) : WithTop ℝ) := by
  rw [StationaryMFG.Hamiltonian.Hext_of_pos H x (fun i => Du i x) hm]
  -- Both sides are now casts of the same real expression `u + H - V`.
  push_cast
  ring

/-- **Phase C0: a.e. paper-Hext form of the HJB inequality on
`{m > 0}`.** Under `IsStrongSolution_HJB`, the cast HJB residual is
≤ 0 in `WithTop ℝ` for almost every `x` with `0 < m x`. Combined
with `Hext_residual_eq_on_pos`, this is the paper-formulated
inequality `↑u + Hext H x Du (m x) - ↑V ≤ 0` on `{m > 0}`. -/
lemma IsStrongSolution_HJB.ae_le_Hext_on_pos
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_HJB V H Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x →
        ((u x : ℝ) : WithTop ℝ)
            + StationaryMFG.Hamiltonian.Hext H x (fun i => Du i x) (m x)
            - ((V x : ℝ) : WithTop ℝ)
          ≤ ((0 : ℝ) : WithTop ℝ) := by
  filter_upwards [h.1] with x hx hm_pos
  -- Rewrite `Hext` to raw `H` on `{m > 0}` and cast the real inequality.
  rw [← Hext_residual_eq_on_pos V H Du m u hm_pos]
  -- The real residual is ≤ 0 by `h.1`; cast through.
  exact_mod_cast hx

end Strong
end Solutions
end StationaryMFG
