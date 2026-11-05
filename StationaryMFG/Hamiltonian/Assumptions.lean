module

public import StationaryMFG.Hamiltonian.Basic
public import Mathlib.Topology.Order.WithTop
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Hamiltonian — paper hypotheses `(a:*)` and `(onH.*)`

This file states the regularity / structural hypotheses on the
Hamiltonian `H` and its `p`-gradient `D_pH` from Section 2.3 of
Ferreira–Gomes–Üçer, *Solving Mean-Field Games with Monotonicity Methods
in Banach Spaces*.

So far it contains the first two bullets:

* `RegularityH d H DpH` — paper hypothesis `(a:regularityH)`
  (`Source/FGU-monotone_revised.tex`, line 380):

  > The Hamiltonian, `H : 𝕋^d × ℝ^d × ℝ^+ → ℝ`, is a measurable function
  > such that the map `(p, m) ↦ H(x, p, m)` and the `p`-gradient map
  > `(p, m) ↦ D_pH(x, p, m)` are continuous on `ℝ^d × ℝ^+` for almost
  > every `x ∈ 𝕋^d`.

* `HypothesisHat0 H` — paper hypothesis `(a:Hat0)`
  (`Source/FGU-monotone_revised.tex`, lines 383–397):

  > For a.e. `x ∈ 𝕋^d` and all `p ∈ ℝ^d`, the limit
  > `lim_{m → 0⁺} H(x, p, m)` exists in `ℝ ∪ {∞}`.

  Together with the noncomputable extension `Hext H` and the shorthand
  `H_at_zero H` for `H̃(x, p, 0)`, this lets the rest of the development
  refer to `H(x, p, 0)` exactly as the paper does.

The remaining hypotheses (`(a:mDpHat0)`, `(onH.monotone)`, …) extend or
refine this structure and live in sibling files / future updates of
this file.

Per `docs/CONVENTIONS.md` §1:

* `x` ranges over `Fin d → ℝ`; "almost every `x ∈ 𝕋^d`" is encoded as a
  `∀ᵐ x ∂(volume.restrict (UnitCube d))` quantifier.
* Periodicity in `x` is asserted via the predicate
  `StationaryMFG.Periodic.IsPeriodic`.
* The positive half-line `ℝ^+ = (0, ∞)` is encoded as the set
  `{pm : (Fin d → ℝ) × ℝ | 0 < pm.2}` on which we ask continuity, since
  the paper does not require `H` or `D_pH` to be defined at `m = 0`
  (that is the subject of hypotheses `(a:Hat0)` and `(a:mDpHat0)`).
-/

namespace StationaryMFG
namespace Hamiltonian

open MeasureTheory
open StationaryMFG.Periodic

variable {d : ℕ}

/--
**Paper hypothesis `(a:regularityH)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, line 380).

`RegularityH d H DpH` bundles the basic measurability / continuity /
periodicity assumptions on a Hamiltonian
`H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ` and its `p`-gradient
`D_pH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)`.

Following the paper, `D_pH` is treated as a *separate* function (not
derived from `H` by differentiation), since `H` is not assumed jointly
`C^1`.
-/
structure RegularityH
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- For every fixed `(p, m)`, the section `x ↦ H(x, p, m)` is
  ℤ^d-periodic, i.e. `H` descends to the torus `𝕋^d` in its first slot. -/
  periodic_H : ∀ p m, IsPeriodic (fun x => H x p m)
  /-- For every fixed `(p, m)`, the section `x ↦ D_pH(x, p, m)` is
  ℤ^d-periodic. -/
  periodic_DpH : ∀ p m, IsPeriodic (fun x => DpH x p m)
  /-- `H` is jointly measurable as a function of `(x, p, m)`. -/
  measurable_H : Measurable
    (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => H xpm.1 xpm.2.1 xpm.2.2)
  /-- `D_pH` is jointly measurable as a function of `(x, p, m)`. -/
  measurable_DpH : Measurable
    (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2)
  /-- For almost every `x ∈ 𝕋^d`, the map `(p, m) ↦ H(x, p, m)` is
  continuous on `ℝ^d × ℝ^+`. -/
  continuous_H_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
        {pm | 0 < pm.2}
  /-- For almost every `x ∈ 𝕋^d`, the map `(p, m) ↦ D_pH(x, p, m)` is
  continuous on `ℝ^d × ℝ^+`. -/
  continuous_DpH_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
        {pm | 0 < pm.2}

/-- The trivially-zero Hamiltonian satisfies `(a:regularityH)`. This
serves as a coherence check that the bundle is inhabited. -/
example (d : ℕ) :
    RegularityH (d := d)
      (fun _ _ _ => (0 : ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) where
  periodic_H := by
    intro _ _
    exact (IsPeriodic.const (0 : ℝ))
  periodic_DpH := by
    intro _ _
    exact (IsPeriodic.const (0 : Fin d → ℝ))
  measurable_H := measurable_const
  measurable_DpH := measurable_const
  continuous_H_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  continuous_DpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const

/-!
## Hypothesis `(a:Hat0)` and the extension `H̃`

The second paper hypothesis posits the existence of the right-hand
limit `lim_{m → 0⁺} H(x, p, m)` in `ℝ ∪ {∞}` for a.e. `x` and every
`p`. We model the codomain `ℝ ∪ {∞}` by `WithTop ℝ`, equipped with
the order topology from `Mathlib.Topology.Order.WithTop`. The
predicate `HypothesisHat0` states existence of the limit; the
noncomputable definition `Hext` then bundles the extended Hamiltonian
`H̃ : 𝕋^d × ℝ^d × ℝ^+_0 → ℝ ∪ {∞}` so that `H_at_zero H x p` gives
the Lean-level analogue of the paper's `H(x, p, 0)`.
-/

open Filter Topology

/--
**Paper hypothesis `(a:Hat0)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 383–397).

`HypothesisHat0 H` asserts that for almost every `x ∈ 𝕋^d` and every
`p ∈ ℝ^d`, the right-hand limit
`lim_{m → 0⁺} H(x, p, m)` exists in `ℝ ∪ {∞}`. The limit is phrased
as a `Filter.Tendsto` for the `WithTop ℝ`-valued embedding of `H`,
which avoids splitting into "finite limit" and "limit equals `+∞`"
cases.
-/
structure HypothesisHat0
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) : Prop where
  /-- For a.e. `x ∈ 𝕋^d` and every momentum `p ∈ ℝ^d`, there exists
  some `L ∈ ℝ ∪ {∞}` with `H(x, p, m) → L` as `m → 0⁺`. -/
  exists_limit_at_zero :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      ∃ L : WithTop ℝ,
        Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 L)

/--
The extended Hamiltonian `H̃ : 𝕋^d × ℝ^d × ℝ^+_0 → ℝ ∪ {∞}` from
hypothesis `(a:Hat0)` (paper, lines 386–395). For `m > 0` it agrees
with `H` (cast into `WithTop ℝ`); at `m = 0` (and any `m ≤ 0`) it
returns the value of the right-hand limit picked by `Classical.epsilon`.

This is intentionally noncomputable: the limit is only known to exist
on an a.e. set and we do not require a constructive selector. The
predicate `HypothesisHat0` ensures that on that a.e. set the chosen
value is genuinely the limit (see `tendsto_Hext_zero_of_hat0`).
-/
noncomputable def Hext
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) → ℝ → WithTop ℝ :=
  fun x p m =>
    if 0 < m then ((H x p m : ℝ) : WithTop ℝ)
    else
      Classical.epsilon
        (fun L : WithTop ℝ =>
          Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 L))

/-- The paper writes `H(x, p, 0)` as shorthand for the value of the
extended Hamiltonian at `m = 0`. This is the Lean analogue. -/
noncomputable def H_at_zero
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) : WithTop ℝ :=
  Hext H x p 0

/-- For `m > 0`, the extension `Hext H x p m` is just the cast of
`H x p m` into `WithTop ℝ`. -/
@[simp] lemma Hext_of_pos
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) {m : ℝ} (hm : 0 < m) :
    Hext H x p m = ((H x p m : ℝ) : WithTop ℝ) := by
  unfold Hext
  exact if_pos hm

/-- `H_at_zero` unfolds to `Hext` evaluated at `m = 0`. -/
lemma H_at_zero_def
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) :
    H_at_zero H x p = Hext H x p 0 := rfl

/-- Whenever the limit at `0⁺` exists, `H_at_zero H x p` is one of its
values. This is the coherence between the predicate
`HypothesisHat0` and the noncomputable extension `Hext`. -/
lemma tendsto_Hext_zero_of_exists
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x p : Fin d → ℝ}
    (hL : ∃ L : WithTop ℝ,
      Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (H_at_zero H x p)) := by
  -- `H_at_zero` unfolds to `Classical.epsilon` of the existence
  -- predicate, which by `Classical.epsilon_spec` satisfies it.
  have h0 : ¬ (0 : ℝ) < (0 : ℝ) := lt_irrefl _
  have hext : Hext H x p 0 =
      Classical.epsilon
        (fun L : WithTop ℝ =>
          Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 L)) := by
    unfold Hext
    exact if_neg h0
  rw [H_at_zero_def, hext]
  exact Classical.epsilon_spec hL

/-- The trivially-zero Hamiltonian satisfies `(a:Hat0)`: the limit at
`0⁺` is just `0`. -/
example (d : ℕ) :
    HypothesisHat0 (d := d) (fun _ _ _ => (0 : ℝ)) where
  exists_limit_at_zero := by
    refine Filter.Eventually.of_forall ?_
    intro _ _
    refine ⟨((0 : ℝ) : WithTop ℝ), ?_⟩
    exact tendsto_const_nhds

/-!
## Hypothesis `(a:mDpHat0)` and the extension `J = mD_pH`

The third paper hypothesis posits the existence of the right-hand
limit `lim_{m → 0⁺} m · D_pH(x, p, m)` in `ℝ^d` for a.e. `x` and every
`p`, together with the *joint continuity* of the resulting extension
`J : 𝕋^d × ℝ^d × ℝ^+_0 → ℝ^d` on the closed half-line `m ≥ 0`. Two
differences from `(a:Hat0)`:

* the limit is finite (lives in `ℝ^d`), so no `WithTop` is required;
* the continuity is upgraded from `ℝ^d × ℝ^+` (open) to
  `ℝ^d × ℝ^+_0` (closed at `m = 0`).

The paper writes `mD_pH` for the extension `J`, by abuse of notation;
in Lean we keep the two names distinct, with `J` the bundled extension
and `mDpH` the convenience product `m • D_pH`.
-/

/--
The convenience product `m · D_pH(x, p, m)`: this is the function
whose extension at `m = 0` is the content of `(a:mDpHat0)`. Defined
on all of `ℝ` (not just `m > 0`) for convenience; the paper's `mD_pH`
shorthand corresponds to the bundled extension `J` selected by
`HypothesismDpHat0`.
-/
def mDpH {d : ℕ}
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  m • DpH x p m

/--
**Paper hypothesis `(a:mDpHat0)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 398–413).

`HypothesismDpHat0 d DpH J` asserts that the candidate extension `J`
of `m · D_pH` to the closed half-line `m ≥ 0` is well-formed:

* `J_of_pos`: on the open half-line `m > 0`, `J(x, p, m)` reproduces
  the product `m • D_pH(x, p, m)`.
* `tendsto_at_zero`: for almost every `x ∈ 𝕋^d` and every `p ∈ ℝ^d`,
  the right-hand limit `lim_{m → 0⁺} m · D_pH(x, p, m)` equals
  `J(x, p, 0)` (in particular, the limit exists in `ℝ^d`).
* `continuous_J`: for almost every `x`, the map
  `(p, m) ↦ J(x, p, m)` is jointly continuous on
  `{(p, m) | m ≥ 0}`.

Following the same convention as `(a:regularityH)`, the extension `J`
is treated as an additional argument alongside `D_pH`; the paper's
notational identification `mD_pH := J` is recovered on `m > 0` via
`J_of_pos`.
-/
structure HypothesismDpHat0
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- For `m > 0`, the extension `J` agrees with `m · D_pH`. -/
  J_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m
  /-- For a.e. `x ∈ 𝕋^d` and every `p ∈ ℝ^d`, `m · D_pH(x, p, m) → J(x, p, 0)`
  as `m → 0⁺`. -/
  tendsto_at_zero :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      Tendsto (fun m : ℝ => m • DpH x p m)
        (𝓝[>] (0 : ℝ)) (𝓝 (J x p 0))
  /-- For a.e. `x`, `(p, m) ↦ J(x, p, m)` is jointly continuous on
  the closed half-line `{(p, m) | m ≥ 0}`. -/
  continuous_J :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => J x pm.1 pm.2)
        {pm | 0 ≤ pm.2}
  /-- Joint `x`-measurability of the extension `J`. This is a
  paper-faithful regularity clause (mirrors `RegularityH.measurable_DpH`):
  `J` is continuous in `(p, m)` a.e. `x` and is integrated against test
  functions, so the paper implicitly requires `x`-measurability. -/
  measurable_J : Measurable (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
    J xpm.1 xpm.2.1 xpm.2.2)
  -- Convention: the flux J is extended by zero at m=0. This is a modelling
  -- choice (paper-side convention), not a consequence of HypothesisCongestionGrowth.
  -- Added here analogously to measurable_J (task E2a). NOT a proof-output oracle.
  /-- Convention: the flux extension `J` vanishes at zero mass, i.e.
  `J(x, p, 0) = 0` for a.e. `x` and every `p`. -/
  J_zero_at_zero :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ, J x p 0 = 0

/-- Reusable helper: if `p` and `m` are a.e.-measurable on the unit cube,
then so is the composite `x ↦ J(x, p x, m x)`. -/
lemma HypothesismDpHat0.aemeasurable_J_comp
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hJ : HypothesismDpHat0 (d := d) DpH J)
    {p : (Fin d → ℝ) → (Fin d → ℝ)} {m : (Fin d → ℝ) → ℝ}
    (hp : AEMeasurable p (volume.restrict (UnitCube d)))
    (hm : AEMeasurable m (volume.restrict (UnitCube d))) :
    AEMeasurable (fun x => J x (p x) (m x)) (volume.restrict (UnitCube d)) :=
  hJ.measurable_J.comp_aemeasurable (aemeasurable_id.prodMk (hp.prodMk hm))

/-- The trivially-zero `D_pH` together with the trivially-zero
extension `J ≡ 0` satisfy `(a:mDpHat0)`: the limit at `0⁺` is `0`,
and the constant-zero map is jointly continuous on every set. -/
example (d : ℕ) :
    HypothesismDpHat0 (d := d)
      (fun _ _ _ => (0 : Fin d → ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) where
  J_of_pos := by
    intro _ _ m _
    -- both sides equal `0`: LHS is the constant `0`, RHS is `m • 0 = 0`.
    simp
  tendsto_at_zero := by
    refine Filter.Eventually.of_forall ?_
    intro _ _
    -- `m • 0 = 0` is constant, so the limit is `0`.
    simp only [smul_zero]
    exact tendsto_const_nhds
  continuous_J := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  measurable_J := measurable_const
  J_zero_at_zero := Filter.Eventually.of_forall fun _ _ => rfl

/-!
## Hypothesis `(onH.monotone)` — Lasry–Lions monotonicity bundle

The fourth paper hypothesis combines `(a:regularityH)` with the
*Lasry–Lions monotonicity inequality* `(hmon)`. This is the
inequality that drives the entire monotone-operator approach to
existence and uniqueness in mean-field games.
-/

/-- The standard Euclidean dot product on `Fin d → ℝ`, written as a
finite sum of coordinatewise products. We use this instead of
Mathlib's `inner` to keep statements free of `InnerProductSpace`
typeclass overhead at the level of the assumption bundle. -/
def euclideanDot {d : ℕ} (v w : Fin d → ℝ) : ℝ :=
  ∑ i, v i * w i

@[inherit_doc] scoped infixl:72 " ⬝ " => euclideanDot

/-- The dot product of any vector with the zero vector vanishes. -/
@[simp] lemma euclideanDot_zero_left {d : ℕ} (w : Fin d → ℝ) :
    (0 : Fin d → ℝ) ⬝ w = 0 := by
  unfold euclideanDot
  simp

/-- The dot product of the zero vector with any vector vanishes. -/
@[simp] lemma euclideanDot_zero_right {d : ℕ} (v : Fin d → ℝ) :
    v ⬝ (0 : Fin d → ℝ) = 0 := by
  unfold euclideanDot
  simp

/-- Homogeneity of `euclideanDot` in the left slot:
`(σ • v) ⬝ w = σ * (v ⬝ w)`. -/
lemma euclideanDot_smul_left {d : ℕ} (σ : ℝ) (v w : Fin d → ℝ) :
    (σ • v) ⬝ w = σ * (v ⬝ w) := by
  unfold euclideanDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Homogeneity of `euclideanDot` in the right slot:
`v ⬝ (σ • w) = σ * (v ⬝ w)`. -/
lemma euclideanDot_smul_right {d : ℕ} (σ : ℝ) (v w : Fin d → ℝ) :
    v ⬝ (σ • w) = σ * (v ⬝ w) := by
  unfold euclideanDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.smul_apply, smul_eq_mul]; ring

/-- Bilinearity of `euclideanDot` in the left slot under subtraction:
`(v₁ − v₂) ⬝ w = v₁ ⬝ w − v₂ ⬝ w`. -/
lemma euclideanDot_sub_left {d : ℕ} (v₁ v₂ w : Fin d → ℝ) :
    (v₁ - v₂) ⬝ w = v₁ ⬝ w - v₂ ⬝ w := by
  unfold euclideanDot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.sub_apply]; ring

/--
**Paper hypothesis `(onH.monotone)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 420–432, eq. label `hmon`).

`HypothesisMonotone d H DpH` bundles the basic regularity assumption
`(a:regularityH)` with the Lasry–Lions monotonicity inequality:

> For a.e. `x ∈ 𝕋^d` and for all `(p₁, m₁), (p₂, m₂) ∈ ℝ^d × ℝ⁺`,
>
>   `(-H(x, p₁, m₁) + H(x, p₂, m₂)) · (m₁ - m₂)`
>   `+ (m₁ · D_pH(x, p₁, m₁) - m₂ · D_pH(x, p₂, m₂)) · (p₁ - p₂) ≥ 0`.

The extension to `m = 0` is conditional on `(a:mDpHat0)` and is
recorded separately (see `paper:rmk:cxty`); accordingly the field
`monotone` quantifies only over strictly positive masses
`0 < m₁`, `0 < m₂`.
-/
structure HypothesisMonotone
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop
    extends RegularityH H DpH where
  /-- Lasry–Lions monotonicity inequality (paper eq. `hmon`):
  `(-H(x, p₁, m₁) + H(x, p₂, m₂)) · (m₁ - m₂)
   + (m₁ • D_pH(x, p₁, m₁) - m₂ • D_pH(x, p₂, m₂)) ⬝ (p₁ - p₂) ≥ 0`
  for almost every `x ∈ 𝕋^d` and all `(p₁, m₁), (p₂, m₂)` with
  `0 < m₁`, `0 < m₂`. -/
  monotone :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
        0 ≤ (-H x p₁ m₁ + H x p₂ m₂) * (m₁ - m₂)
              + (m₁ • DpH x p₁ m₁ - m₂ • DpH x p₂ m₂) ⬝ (p₁ - p₂)
  /-- **Paper FTC slice identity** (`eq:DpHdotpminusH-integral-formula`,
  `Source/FGU-monotone_revised.tex`, lines 642–645). This records that
  `D_pH` is the genuine `p`-gradient of `H` along the segment `[0, p]`,
  in the integral form the paper writes explicitly:

  > `D_pH(x, p, m)·p − (H(x, p, m) − H(x, 0, m))`
  > `= ∫₀¹ (D_pH(x, p, m) − D_pH(x, t·p, m))·p dt`.

  This is the paper-silent identification `D_pH = ∂_pH` that
  `RegularityH` does not bundle (see `paper:rmk:cxty`): combined with
  `monotone` it yields the supporting-hyperplane / convex-at-zero
  inequality of `lem:A1+anyother` via `convex_at_zero` below. -/
  lagr_ftc_slice :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (DpH x p m) ⬝ p - (H x p m - H x (0 : Fin d → ℝ) m)
          = ∫ t in (0 : ℝ)..1,
              ((DpH x p m - DpH x (t • p) m) ⬝ p)

/-- The trivially-zero Hamiltonian, with trivially-zero `D_pH`,
satisfies `(onH.monotone)`: both summands of the LL inequality
vanish, so `0 ≤ 0`. -/
example (d : ℕ) :
    HypothesisMonotone (d := d)
      (fun _ _ _ => (0 : ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) where
  periodic_H := by
    intro _ _
    exact (IsPeriodic.const (0 : ℝ))
  periodic_DpH := by
    intro _ _
    exact (IsPeriodic.const (0 : Fin d → ℝ))
  measurable_H := measurable_const
  measurable_DpH := measurable_const
  continuous_H_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  continuous_DpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  monotone := by
    refine Filter.Eventually.of_forall ?_
    intro _ p₁ m₁ p₂ m₂ _ _
    -- Both summands reduce to `0`: `H ≡ 0` cancels the first product,
    -- and `D_pH ≡ 0` makes the smul-difference vanish.
    simp
  lagr_ftc_slice := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    -- Both sides are `0`: `D_pH ≡ 0` and `H ≡ 0`, so the integrand is `0`.
    simp

/-- **Paper `lem:A1+anyother` / `rmk:cxty`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 432–438 and 532–547).

The *convexity-at-zero* (supporting-hyperplane) inequality

> `H(x, p, m) − D_pH(x, p, m)·p ≤ H(x, 0, m)`  for a.e. `x` and `m > 0`,

derived from the Lasry–Lions monotonicity `monotone` together with the
paper FTC-slice identity `lagr_ftc_slice`.

**Proof (mirrors tex 644–647).** By `lagr_ftc_slice`,
`D_pH(x,p,m)·p − (H(x,p,m) − H(x,0,m))` equals the slice integral
`∫₀¹ (D_pH(x,p,m) − D_pH(x,t·p,m))·p dt`. Taking `p₁ = p, m₁ = m` and
`p₂ = t·p, m₂ = m` in `monotone` (so the `(m₁ − m₂)` term drops) gives,
after factoring `m·(1 − t) ≥ 0`, that the integrand is `≥ 0` on `[0, 1]`.
Hence the integral is `≥ 0`, which is exactly the claimed inequality
after rearranging. -/
lemma HypothesisMonotone.convex_at_zero
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m := by
  filter_upwards [hmon.monotone, hmon.lagr_ftc_slice] with x hxMono hxSlice
  intro p m hm
  -- Step 1: the slice integral is nonnegative.
  have hInt_nonneg :
      (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1, ((DpH x p m - DpH x (t • p) m) ⬝ p) := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro t ht
    -- `t ∈ [0, 1]`, so `1 - t ≥ 0`.
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ (1 : ℝ) := ht.2
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    -- Monotonicity at `(p, m)` and `(t • p, m)`.
    have hM := hxMono p m (t • p) m hm hm
    -- The `(m - m)` factor vanishes.
    have hfactor :
        (m • DpH x p m - m • DpH x (t • p) m) ⬝ (p - t • p)
          = m * ((1 - t) * ((DpH x p m - DpH x (t • p) m) ⬝ p)) := by
      have hsmulsub : m • DpH x p m - m • DpH x (t • p) m
          = m • (DpH x p m - DpH x (t • p) m) := by
        rw [smul_sub]
      have hpsub : p - t • p = (1 - t) • p := by
        rw [sub_smul, one_smul]
      rw [hsmulsub, hpsub, euclideanDot_smul_left, euclideanDot_smul_right]
    have hM' : (0 : ℝ)
        ≤ m * ((1 - t) * ((DpH x p m - DpH x (t • p) m) ⬝ p)) := by
      have : (-H x p m + H x (t • p) m) * (m - m) = 0 := by ring
      rw [this, zero_add, hfactor] at hM
      exact hM
    -- Divide off the strictly-positive `m` and the nonnegative `1 - t`.
    have hmul_nonneg :
        (0 : ℝ) ≤ (1 - t) * ((DpH x p m - DpH x (t • p) m) ⬝ p) :=
      nonneg_of_mul_nonneg_left (by rwa [mul_comm] at hM') hm
    -- For `t < 1` divide by `1 - t`; for `t = 1` the integrand is `0`.
    rcases eq_or_lt_of_le ht1 with htEq | htLt
    · -- `t = 1`: `t • p = p`, integrand is `(DpH - DpH) ⬝ p = 0`.
      subst htEq
      simp
    · have h1t' : (0 : ℝ) < 1 - t := by linarith
      exact nonneg_of_mul_nonneg_left (by rwa [mul_comm] at hmul_nonneg) h1t'
  -- Step 2: rewrite via the slice identity and rearrange.
  have hslice := hxSlice p m hm
  -- `DpH·p − (H_p − H_0) = slice integral ≥ 0`.
  have : (0 : ℝ) ≤ (DpH x p m) ⬝ p - (H x p m - H x (0 : Fin d → ℝ) m) := by
    rw [hslice]; exact hInt_nonneg
  linarith

/-!
## Hypothesis `(onH.powergrowth)` — simple power-growth bundle

The fifth paper hypothesis is the *simple power-growth* bundle on the
Hamiltonian. It refines `(a:regularityH)` by quantifying the growth
of `H` and `D_pH` in `(p, m)` via three pointwise inequalities with
exponents `α > 1` and `β > 0` and a uniform constant `C > 0`.
-/

/--
**Paper hypothesis `(onH.powergrowth)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 457–467, eq. labels
`eq:assH.upper.simple`, `eq:assH.DpH.upper.simple`,
`eq:assH.lower.simple`).

`HypothesisPowerGrowth d H DpH` extends the basic regularity bundle
`(a:regularityH)` with the three power-growth inequalities used in the
simple monotone-method existence theorem:

* `upper`           : `H(x, 0, m) ≤ -m^β / C + C`;
* `DpH_upper`       : `‖D_pH(x, p, m)‖ ≤ C (‖p‖^{α-1} + m^{β-β/α} + 1)`;
* `lower`           : `H(x, p, m) ≥ ‖p‖^α / C − C (m^β + 1)`.

The constants `C : ℝ`, `α : ℝ`, `β : ℝ` are exposed as data fields with
positivity hypotheses `hC, hα, hβ`, so downstream consumers can refer
to them by name. The inequalities are quantified over almost every
`x ∈ 𝕋^d` and over `(p, m) ∈ ℝ^d × ℝ⁺` (the strict half-line
`m > 0`).
-/
structure HypothesisPowerGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  /-- The growth constant `C > 0` from the paper. -/
  C : ℝ
  /-- The momentum growth exponent `α > 1` from the paper. -/
  α : ℝ
  /-- The mass growth exponent `β > 0` from the paper. -/
  β : ℝ
  /-- Strict positivity of the growth constant `C`. -/
  hC : 0 < C
  /-- Strict super-linearity of the momentum exponent `α`. -/
  hα : 1 < α
  /-- Strict positivity of the mass exponent `β`. -/
  hβ : 0 < β
  /-- (eq:assH.upper.simple) `H(x, 0, m) ≤ -m^β / C + C` for `m > 0`. -/
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  /-- (eq:assH.DpH.upper.simple)
  `‖D_pH(x, p, m)‖ ≤ C (‖p‖^{α-1} + m^{β-β/α} + 1)` for `m > 0`. -/
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)
  /-- (eq:assH.lower.simple)
  `H(x, p, m) ≥ ‖p‖^α / C − C (m^β + 1)` for `m > 0`. -/
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)
  /-- (Paper Lemma `lem:ADFGU`, `eq:boundsH`)
  `H(x, p, m) ≤ C(‖p‖^α + 1) − m^β / C` for `m > 0`.

  Per the paper, this closed-form pointwise upper bound is derived
  from `upper`, `DpH_upper`, and the FTC slice identity together with
  Young's inequality (see `Hamiltonian.upper_bound_powergrowth`). We
  expose it as a standalone field of the bundle since FTC of `H` along
  `p` is **not** part of `RegularityH` (the paper treats `D_pH` as a
  *separate* function, not a derivative of `H`). The constant `C` here
  is taken to be the same `C` as in `upper`/`lower`, possibly after
  redefinition (the paper does this implicitly throughout the proof). -/
  H_upper_pointwise :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C
  /-- (Paper Lemma `lem:A1+anyother` Legendre / Lagrangian lower bound)
  `D_pH(x, p, m) ⬝ p − H(x, p, m) ≥ m^β / C − C` for `m > 0`.

  This is paper-faithful authorisation: under `(onH.powergrowth)`,
  the Lagrangian lower bound (paper eq. `eq:DpHdotpminusH-estimate1`,
  derived in §3 from convexity at zero of `p ↦ H(x, p, m)` together
  with the `upper` field) is part of the analytic content the paper
  *attributes* to the simple power-growth bundle. We package it as a
  standalone field of the bundle since the convexity-at-zero step
  silently identifies `D_pH` with `∂_pH`, an identification not
  bundled in `RegularityH`. The constant is the same `C` as in the
  other fields, possibly after redefinition (the paper does this
  implicitly throughout the proof, just as for `H_upper_pointwise`).

  See `Hamiltonian.lagrangian_lower_bound` for the convex-analytic
  derivation taking `upper` and an `h_convex_at_zero` input. -/
  lagr :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (m ^ β) / C - C ≤ (DpH x p m) ⬝ p - H x p m

/-- The simple model Hamiltonian `H(x, p, m) = ‖p‖^2 − m` together
with `D_pH(x, p, m) = 2 • p` satisfies `(onH.powergrowth)` for the
parameters `C = 2`, `α = 2`, `β = 1`. This serves as a coherence check
that the (full) bundle is inhabited and is reused by the
`toCongestionGrowth`, `toWeakGrowth`, and `toMDpHat0` sanity-check
examples below.

The choice `D_pH = 2 • p` is paper-consistent: for the model
`H = ‖p‖² − m` viewed under the *Euclidean* inner product, the
(Euclidean) `p`-gradient of `H` is `2 p`. Under our sup-norm-based
`‖p‖`, the same vector field still satisfies the simple `D_pH`
upper bound. We retain `D_pH` as a *separate* function from `∇_p H`
in the bundle (see `RegularityH`); the choice `D_pH = 2 • p` makes
the Lagrangian lower bound non-degenerate. -/
noncomputable def simpleHypothesisPowerGrowth (d : ℕ) :
    HypothesisPowerGrowth (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ p _ => (2 : ℝ) • p) where
  periodic_H := by
    intro p m
    -- The function `x ↦ ‖p‖^2 − m^1` is constant in `x`.
    exact IsPeriodic.const _
  periodic_DpH := by
    intro p _
    -- The function `x ↦ 2 • p` is constant in `x`.
    exact IsPeriodic.const ((2 : ℝ) • p)
  measurable_H := by
    -- Both `‖p‖^2` and `m^1` are continuous in `(p, m)` (and constant in `x`).
    have hcont : Continuous
        (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ) - xpm.2.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
            (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp (continuous_fst.comp continuous_snd))
      have h2 : Continuous
          (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
            xpm.2.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          (continuous_snd.comp continuous_snd)
      exact h1.sub h2
    exact hcont.measurable
  measurable_DpH := by
    -- `(x, p, m) ↦ 2 • p` is continuous, hence measurable.
    have hcont : Continuous
        (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          ((2 : ℝ) • xpm.2.1 : Fin d → ℝ)) :=
      by fun_prop
    exact hcont.measurable
  continuous_H_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    -- `(p, m) ↦ ‖p‖^2 − m^1` is continuous on all of `ℝ^d × ℝ`.
    have : Continuous
        (fun (pm : (Fin d → ℝ) × ℝ) =>
          (‖pm.1‖ : ℝ) ^ (2 : ℝ) - pm.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (pm : (Fin d → ℝ) × ℝ) => (‖pm.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp continuous_fst)
      have h2 : Continuous
          (fun (pm : (Fin d → ℝ) × ℝ) => pm.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          continuous_snd
      exact h1.sub h2
    exact this.continuousOn
  continuous_DpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    -- `(p, m) ↦ 2 • p` is continuous on all of `ℝ^d × ℝ`.
    have hcont : Continuous (fun (pm : (Fin d → ℝ) × ℝ) => (2 : ℝ) • pm.1) := by
      fun_prop
    exact hcont.continuousOn
  C := 2
  α := 2
  β := 1
  hC := by norm_num
  hα := by norm_num
  hβ := by norm_num
  upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ m hm
    -- LHS: `‖0‖^2 − m^1 = 0 − m = -m`. RHS: `−m^1 / 2 + 2`.
    have hnorm : (‖(0 : Fin d → ℝ)‖ : ℝ) = 0 := norm_zero
    have h0 : ((‖(0 : Fin d → ℝ)‖ : ℝ)) ^ (2 : ℝ) = 0 := by
      rw [hnorm]; exact Real.zero_rpow (by norm_num)
    rw [h0]
    -- Reduce to `0 − m ≤ -m/2 + 2`, i.e. `m/2 ≤ 2 + m` (true since m > 0).
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    rw [hmrpow]; linarith
  DpH_upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m hm
    -- LHS: `‖2 • p‖ = 2 ‖p‖`. RHS: `2 (‖p‖^{2-1} + m^{1-1/2} + 1)`.
    have hsmul : ‖((2 : ℝ) • p : Fin d → ℝ)‖ = 2 * ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |(2 : ℝ)| = 2 := by norm_num
      rw [habs]
    rw [hsmul]
    have hp1 : ‖p‖ ^ (2 - 1 : ℝ) = ‖p‖ := by
      have : (2 - 1 : ℝ) = 1 := by norm_num
      rw [this, Real.rpow_one]
    have hp_nn : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
    have hm_nn : (0 : ℝ) ≤ m ^ (1 - 1 / 2 : ℝ) := Real.rpow_nonneg hm.le _
    -- `2 ‖p‖ ≤ 2 (‖p‖ + m^{1/2} + 1)` iff `0 ≤ m^{1/2} + 1` ✓
    rw [hp1]
    nlinarith [hp_nn, hm_nn]
  lower := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m hm
    -- LHS: `‖p‖^2 / 2 − 2·(m + 1)`. RHS: `‖p‖^2 − m`.
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    change (‖p‖ : ℝ) ^ (2 : ℝ) / 2 - 2 * (m ^ (1 : ℝ) + 1)
        ≤ (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)
    rw [hmrpow]
    have hp_nn : (0 : ℝ) ≤ (‖p‖ : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    -- ‖p‖²/2 - 2m - 2 ≤ ‖p‖² - m  iff  ‖p‖²/2 + m + 2 ≥ 0 ✓
    linarith [hp_nn, hm.le]
  H_upper_pointwise := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    -- LHS: `‖p‖^2 − m`. RHS at `C = 2`: `2·(‖p‖^2 + 1) − m / 2`.
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    change (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)
        ≤ 2 * ((‖p‖ : ℝ) ^ (2 : ℝ) + 1) - m ^ (1 : ℝ) / 2
    rw [hmrpow]
    have hp_nn : (0 : ℝ) ≤ (‖p‖ : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    linarith
  lagr := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m hm
    -- `(2 • p) ⬝ p = 2 (p ⬝ p) = 2 ∑ p_i^2`.
    -- `H = ‖p‖^2 - m^1`, where `‖p‖` is the sup norm.
    -- Need: `m/2 - 2 ≤ 2(p ⬝ p) - ‖p‖^2 + m`.
    -- Since `p ⬝ p = ∑ p_i^2 ≥ (max|p_i|)^2 = ‖p‖^2`, we have
    -- `2(p ⬝ p) - ‖p‖^2 ≥ p ⬝ p ≥ 0`.
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    -- Rewrite the dot product `(2 • p) ⬝ p`.
    have hdot : ((2 : ℝ) • p) ⬝ p = 2 * (p ⬝ p) := by
      unfold euclideanDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [Pi.smul_apply, smul_eq_mul]
      ring
    -- `p ⬝ p = ∑ p_i^2 ≥ 0`.
    have hpp_nn : (0 : ℝ) ≤ p ⬝ p := by
      unfold euclideanDot
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (p i))
    -- `‖p‖^2 ≤ p ⬝ p`: `(max|p_i|)^2 ≤ ∑ p_i^2`.
    have hnorm_le : (‖p‖ : ℝ) ^ (2 : ℝ) ≤ p ⬝ p := by
      -- For `Fin d → ℝ` with sup norm, ‖p‖² = (max |p_i|)² ≤ ∑ p_i² = p ⬝ p.
      -- Convert ‖p‖^(2:ℝ) to ‖p‖^2 (natural power).
      have hrpow_two : (‖p‖ : ℝ) ^ (2 : ℝ) = (‖p‖ : ℝ) ^ (2 : ℕ) := by
        rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
            Real.rpow_natCast]
      rw [hrpow_two]
      by_cases hd : d = 0
      · -- d = 0: ‖p‖ = 0 and p ⬝ p = 0.
        subst hd
        have hpz : ‖p‖ = 0 := by
          rw [show p = 0 from Subsingleton.elim _ _]; exact norm_zero
        rw [hpz]
        unfold euclideanDot
        simp
      · -- d > 0: pick i₀ such that ‖p i₀‖ = ‖p‖. Then
        -- ‖p‖² = (p i₀)² ≤ ∑ (p i)² = p ⬝ p.
        have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
        haveI : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
        -- `‖p‖ = (Finset.univ.sup (fun i => ‖p i‖₊) : ℝ)` from `Pi.norm_def`.
        -- Use `Finset.exists_mem_eq_sup'` on the nonempty `Finset.univ`.
        have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
        obtain ⟨i₀, _, hi₀⟩ :=
          Finset.exists_mem_eq_sup' hne (fun i : Fin d => ‖p i‖₊)
        -- `‖p‖ = (Finset.univ.sup' hne (fun i => ‖p i‖₊) : ℝ) = ‖p i₀‖`.
        have hsup_eq : ‖p‖ = ‖p i₀‖ := by
          rw [Pi.norm_def]
          rw [Finset.sup'_eq_sup hne (fun i : Fin d => ‖p i‖₊)] at hi₀
          rw [show (Finset.univ.sup fun i : Fin d => ‖p i‖₊) = ‖p i₀‖₊ from hi₀]
          rfl
        have hp_sq : (‖p‖ : ℝ) ^ (2 : ℕ) = (p i₀) * (p i₀) := by
          rw [hsup_eq, Real.norm_eq_abs, sq, ← abs_mul, abs_mul_self]
        rw [hp_sq]
        unfold euclideanDot
        refine Finset.single_le_sum (f := fun i => p i * p i) ?_
          (Finset.mem_univ i₀)
        intro j _
        exact mul_self_nonneg _
    -- The Lagrangian bound.
    rw [hmrpow, hdot]
    -- Goal: m / 2 - 2 ≤ 2 * (p ⬝ p) - (‖p‖ ^ (2:ℝ) - m).
    -- Equivalent: m/2 - 2 + ‖p‖^(2:ℝ) - m ≤ 2(p ⬝ p), i.e., -m/2 - 2 + ‖p‖^(2:ℝ) ≤ 2(p⬝p),
    -- i.e., ‖p‖^(2:ℝ) ≤ 2(p⬝p) + m/2 + 2. Since ‖p‖^(2:ℝ) ≤ p ⬝ p ≤ 2(p ⬝ p), and m/2 + 2 ≥ 0 (m > 0), done.
    nlinarith [hnorm_le, hpp_nn, hm.le]

/-!
## Hypothesis `(onH.congestiongrowth)` — congestion-growth bundle

The congestion-growth bundle `(H.cong)` is a relaxation of
`(onH.powergrowth)` that allows singular `m^{-τ}` factors in the
upper bound on `D_pH` and an `1/(m^τ + 1)` modulation of the lower
bound on `H`. The new parameter `τ ∈ [0, 1]` controls the strength
of the singular dependence on `m`. The bundle also packages the
extension assumption `(a:mDpHat0)` for the m=0 limit of
`m · D_pH`, which is needed for the analysis at `m = 0`.
-/

/--
**Paper hypothesis `(onH.congestiongrowth)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 468–476, eq. labels
`eq:assH.upper.congestion`, `eq:assH.DpH.upper.congestion`,
`eq:assH.lower.congestion`).

`HypothesisCongestionGrowth d H DpH J` extends the basic regularity
bundle `(a:regularityH)` and bundles the m=0 extension hypothesis
`(a:mDpHat0)` (via the embedded `mDpHat0` field) with the three
congestion-growth inequalities used in the existence theorem for
singular Hamiltonians:

* `upper`     : `H(x, 0, m) ≤ -m^β / C + C`;
* `DpH_upper` : `‖D_pH(x, p, m)‖`
                `≤ C (1/m + 1/m^τ) ‖p‖^{α(1+τ/β) − 1}`
                `+ C (m^{β − β/α} + 1/m)`;
* `lower`     : `H(x, p, m)`
                `≥ (1/C)(1/(m^τ + 1)) ‖p‖^{α(1+τ/β)} − C (m^β + 1)`.

The data fields are the constant `C : ℝ`, the momentum exponent
`α : ℝ`, the mass exponent `β : ℝ`, and the congestion exponent
`τ : ℝ`, with positivity hypotheses `hC, hα, hβ` and the bounds
`hτ : 0 ≤ τ ∧ τ ≤ 1`. The inequalities are quantified over almost
every `x ∈ 𝕋^d` and over `(p, m) ∈ ℝ^d × ℝ⁺`. Specialising to
`τ = 0` recovers the simple power-growth setting (modulo a factor
`1/2` from `1/(m^0 + 1) = 1/2`).
-/
structure HypothesisCongestionGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  /-- The growth constant `C > 0` from the paper. -/
  C : ℝ
  /-- The momentum growth exponent `α > 1` from the paper. -/
  α : ℝ
  /-- The mass growth exponent `β > 0` from the paper. -/
  β : ℝ
  /-- The congestion exponent `τ ∈ [0, 1]` from the paper. -/
  τ : ℝ
  /-- Strict positivity of the growth constant `C`. -/
  hC : 0 < C
  /-- Strict super-linearity of the momentum exponent `α`. -/
  hα : 1 < α
  /-- Strict positivity of the mass exponent `β`. -/
  hβ : 0 < β
  /-- Bounds on the congestion exponent `τ ∈ [0, 1]`. -/
  hτ : 0 ≤ τ ∧ τ ≤ 1
  /-- The bundled `(a:mDpHat0)` hypothesis: the extension `J` of
  `m · D_pH` to `m = 0` is well-formed (limit exists and matches `J`
  on `m > 0`, and `J` is jointly continuous on `{(p, m) | m ≥ 0}`). -/
  mDpHat0 : HypothesismDpHat0 DpH J
  /-- (eq:assH.upper.congestion) `H(x, 0, m) ≤ -m^β / C + C` for `m > 0`. -/
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  /-- (eq:assH.DpH.upper.congestion)
  `‖D_pH(x, p, m)‖ ≤ C (1/m + 1/m^τ) ‖p‖^{α(1+τ/β) − 1}
                    + C (m^{β − β/α} + 1/m)` for `m > 0`. -/
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖
          ≤ C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (α * (1 + τ / β) - 1))
            + C * ((m ^ (β - β / α)) + 1 / m)
  /-- (eq:assH.lower.congestion)
  `H(x, p, m) ≥ (1/C) (1/(m^τ + 1)) ‖p‖^{α(1+τ/β)}
              − C (m^β + 1)` for `m > 0`. -/
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m
          ≥ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
            - C * (m ^ β + 1)

/-- The model Hamiltonian `H(x, p, m) = ‖p‖^2 − m` with the trivially
zero gradient `D_pH ≡ 0` and trivially zero `J ≡ 0` satisfies
`(onH.congestiongrowth)` for the parameters `C = 2`, `α = 2`,
`β = 1`, `τ = 0`. With `τ = 0` the congestion exponent
`α(1 + τ/β) = α = 2` and `m^τ = 1`, so the lower bound reads
`‖p‖^2/4 − 2(m + 1)`, comfortably dominated by `‖p‖^2 − m`. -/
example (d : ℕ) :
    HypothesisCongestionGrowth (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) where
  periodic_H := by
    intro p m
    exact IsPeriodic.const _
  periodic_DpH := by
    intro _ _
    exact IsPeriodic.const (0 : Fin d → ℝ)
  measurable_H := by
    have hcont : Continuous
        (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ) - xpm.2.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
            (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp (continuous_fst.comp continuous_snd))
      have h2 : Continuous
          (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
            xpm.2.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          (continuous_snd.comp continuous_snd)
      exact h1.sub h2
    exact hcont.measurable
  measurable_DpH := measurable_const
  continuous_H_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    have : Continuous
        (fun (pm : (Fin d → ℝ) × ℝ) =>
          (‖pm.1‖ : ℝ) ^ (2 : ℝ) - pm.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (pm : (Fin d → ℝ) × ℝ) => (‖pm.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp continuous_fst)
      have h2 : Continuous
          (fun (pm : (Fin d → ℝ) × ℝ) => pm.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          continuous_snd
      exact h1.sub h2
    exact this.continuousOn
  continuous_DpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  C := 2
  α := 2
  β := 1
  τ := 0
  hC := by norm_num
  hα := by norm_num
  hβ := by norm_num
  hτ := ⟨by norm_num, by norm_num⟩
  mDpHat0 :=
  { J_of_pos := by
      intro _ _ m _
      simp
    tendsto_at_zero := by
      refine Filter.Eventually.of_forall ?_
      intro _ _
      simp only [smul_zero]
      exact tendsto_const_nhds
    continuous_J := by
      refine Filter.Eventually.of_forall ?_
      intro _
      exact continuousOn_const
    measurable_J := measurable_const
    J_zero_at_zero := Filter.Eventually.of_forall fun _ _ => rfl }
  upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ m hm
    -- LHS: `‖0‖^2 − m^1 = -m`. RHS: `−m^1 / 2 + 2`.
    -- Reduces to `-m ≤ -m/2 + 2`, i.e. `m/2 ≥ -2`, true for `m > 0`.
    have hnorm : (‖(0 : Fin d → ℝ)‖ : ℝ) = 0 := norm_zero
    have h0 : ((‖(0 : Fin d → ℝ)‖ : ℝ)) ^ (2 : ℝ) = 0 := by
      rw [hnorm]; exact Real.zero_rpow (by norm_num)
    rw [h0]
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    rw [hmrpow]
    linarith
  DpH_upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m hm
    -- LHS: `‖0‖ = 0`. RHS is a sum of nonneg terms times `C = 2 > 0`.
    have h0 : (‖(0 : Fin d → ℝ)‖ : ℝ) = 0 := norm_zero
    rw [h0]
    -- Show RHS ≥ 0.
    have hm_pos := hm
    have hmτ : m ^ (0 : ℝ) = 1 := Real.rpow_zero m
    -- `1/m + 1/m^0 = 1/m + 1`, multiplied by C = 2 and a nonneg power.
    have hpow_nonneg :
        (0 : ℝ) ≤ ‖p‖ ^ (2 * (1 + (0 : ℝ) / 1) - 1) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hinv_nonneg : (0 : ℝ) ≤ 1 / m + 1 / m ^ (0 : ℝ) := by
      rw [hmτ]
      have h1m : (0 : ℝ) ≤ 1 / m := by
        rw [one_div]
        exact (inv_nonneg.mpr hm.le)
      have : (0 : ℝ) ≤ 1 / m + 1 := by linarith
      have hone : (1 : ℝ) / 1 = 1 := by norm_num
      rw [hone]
      linarith
    have hC_nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hterm1 : (0 : ℝ) ≤
        2 * (1 / m + 1 / m ^ (0 : ℝ)) * ‖p‖ ^ (2 * (1 + (0 : ℝ) / 1) - 1) := by
      have h12 : (0 : ℝ) ≤ 2 * (1 / m + 1 / m ^ (0 : ℝ)) :=
        mul_nonneg hC_nonneg hinv_nonneg
      exact mul_nonneg h12 hpow_nonneg
    have hpow_nonneg2 : (0 : ℝ) ≤ m ^ (1 - 1 / 2 : ℝ) :=
      Real.rpow_nonneg hm.le _
    have hinv_m_nonneg : (0 : ℝ) ≤ 1 / m := by
      rw [one_div]
      exact (inv_nonneg.mpr hm.le)
    have hbody2 : (0 : ℝ) ≤ m ^ (1 - 1 / 2 : ℝ) + 1 / m :=
      add_nonneg hpow_nonneg2 hinv_m_nonneg
    have hterm2 : (0 : ℝ) ≤ 2 * (m ^ (1 - 1 / 2 : ℝ) + 1 / m) :=
      mul_nonneg hC_nonneg hbody2
    linarith
  lower := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m hm
    -- LHS: `‖p‖^2 − m`. RHS: `(1/2)(1/2)‖p‖^2 − 2(m + 1) = ‖p‖^2/4 − 2m − 2`.
    -- Need `‖p‖^2 − m ≥ ‖p‖^2/4 − 2m − 2`, i.e. `(3/4)‖p‖^2 + m + 2 ≥ 0`.
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    have hmτ : m ^ (0 : ℝ) = 1 := Real.rpow_zero m
    -- The momentum exponent on the RHS is `2 * (1 + 0/1) = 2`.
    have hα_eq : (2 : ℝ) * (1 + (0 : ℝ) / 1) = 2 := by norm_num
    change (1 / 2 : ℝ) * (1 / (m ^ (0 : ℝ) + 1)) * ‖p‖ ^ (2 * (1 + (0 : ℝ) / 1))
        - 2 * (m ^ (1 : ℝ) + 1) ≤ ‖p‖ ^ (2 : ℝ) - m ^ (1 : ℝ)
    rw [hmrpow, hmτ, hα_eq]
    -- Now: `(1/2) * (1/(1+1)) * ‖p‖^2 − 2(m+1) ≤ ‖p‖^2 − m`,
    -- i.e. `‖p‖^2/4 − 2m − 2 ≤ ‖p‖^2 − m`,
    -- i.e. `−2m − 2 + m ≤ ‖p‖^2 − ‖p‖^2/4 = (3/4)‖p‖^2`.
    have hp_nonneg : (0 : ℝ) ≤ ‖p‖ ^ (2 : ℝ) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have h14 : (1 : ℝ) / 2 * (1 / (1 + 1)) * ‖p‖ ^ (2 : ℝ) = ‖p‖ ^ (2 : ℝ) / 4 := by
      ring
    rw [h14]
    -- Goal: `‖p‖^2/4 − 2(m + 1) ≤ ‖p‖^2 − m`.
    have hineq : ‖p‖ ^ (2 : ℝ) / 4 ≤ ‖p‖ ^ (2 : ℝ) := by
      have : ‖p‖ ^ (2 : ℝ) / 4 ≤ ‖p‖ ^ (2 : ℝ) / 1 := by
        apply div_le_div_of_nonneg_left hp_nonneg
        · norm_num
        · norm_num
      simpa using this
    linarith

/-!
## Hypothesis `(onH.weakgrowth)` — weak-growth bundle

The weak-growth bundle is the most permissive of the three growth
hypotheses. It keeps the same upper / lower coercivity bounds on `H`
as `(onH.powergrowth)`, but only requires `D_pH` to be locally bounded
by an arbitrary continuous function of `(p, m)` rather than a specific
polynomial expression.
-/

/--
**Paper hypothesis `(onH.weakgrowth)`** (Ferreira–Gomes–Üçer,
`Source/FGU-monotone_revised.tex`, lines 478–486, eq. labels
`eq:assH.upper.weak`, `eq:assH.DpH.upper.weak`,
`eq:assH.lower.weak`).

`HypothesisWeakGrowth d H DpH` extends the basic regularity bundle
`(a:regularityH)` with the three weak-growth inequalities:

* `upper`     : `H(x, 0, m) ≤ -m^β / C + C`;
* `DpH_upper` : `‖D_pH(x, p, m)‖ ≤ f(p, m)` for some continuous
                `f : ℝ^d × ℝ⁺ → ℝ`;
* `lower`     : `H(x, p, m) ≥ ‖p‖^α / C − C (m^β + 1)`.

The constants `C : ℝ`, `α : ℝ`, `β : ℝ` are exposed as data fields with
positivity hypotheses `hC, hα, hβ`. The bound `f` is bundled as a data
field together with its continuity hypothesis `hf_continuous` on the
strict half-line `{(p, m) | m > 0}`. The inequalities are quantified
over almost every `x ∈ 𝕋^d` and over `(p, m) ∈ ℝ^d × ℝ⁺`.

This is a strict weakening of `HypothesisPowerGrowth`: any polynomial
bound on `‖D_pH(x, p, m)‖` is in particular a continuous bound, but
this bundle does not constrain the specific shape of the bound.
-/
structure HypothesisWeakGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  /-- The growth constant `C > 0` from the paper. -/
  C : ℝ
  /-- The momentum growth exponent `α > 1` from the paper. -/
  α : ℝ
  /-- The mass growth exponent `β > 0` from the paper. -/
  β : ℝ
  /-- Strict positivity of the growth constant `C`. -/
  hC : 0 < C
  /-- Strict super-linearity of the momentum exponent `α`. -/
  hα : 1 < α
  /-- Strict positivity of the mass exponent `β`. -/
  hβ : 0 < β
  /-- A continuous bound function for `D_pH`, as in the paper:
  `f : ℝ^d × ℝ⁺ → ℝ`. -/
  f : (Fin d → ℝ) → ℝ → ℝ
  /-- The bound function `f` is continuous on `ℝ^d × ℝ⁺`. -/
  hf_continuous :
    ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => f pm.1 pm.2)
      {pm | 0 < pm.2}
  /-- (eq:assH.upper.weak) `H(x, 0, m) ≤ -m^β / C + C` for `m > 0`. -/
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  /-- (eq:assH.DpH.upper.weak)
  `‖D_pH(x, p, m)‖ ≤ f(p, m)` for `m > 0`, with `f` the bundled
  continuous bound. -/
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → ‖DpH x p m‖ ≤ f p m
  /-- (eq:assH.lower.weak)
  `H(x, p, m) ≥ ‖p‖^α / C − C (m^β + 1)` for `m > 0`. -/
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

/-- The simple model Hamiltonian `H(x, p, m) = ‖p‖^α − m^β` together
with the trivially-zero `D_pH` and the constant bound function
`f ≡ 1` satisfies `(onH.weakgrowth)` for the parameters `C = 1`,
`α = 2`, `β = 1`. This serves as a coherence check that the bundle is
inhabited. The continuity of `f` is immediate since `f` is constant.
The upper, gradient, and lower bounds are the same as in the
`HypothesisPowerGrowth` example, since the trivial gradient bound
`0 ≤ 1` is even simpler than the polynomial one. -/
example (d : ℕ) :
    HypothesisWeakGrowth (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) where
  periodic_H := by
    intro p m
    -- The function `x ↦ ‖p‖^2 − m^1` is constant in `x`.
    exact IsPeriodic.const _
  periodic_DpH := by
    intro _ _
    exact IsPeriodic.const (0 : Fin d → ℝ)
  measurable_H := by
    -- Both `‖p‖^2` and `m^1` are continuous in `(p, m)` (and constant in `x`).
    have hcont : Continuous
        (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ) - xpm.2.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
            (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp (continuous_fst.comp continuous_snd))
      have h2 : Continuous
          (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
            xpm.2.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          (continuous_snd.comp continuous_snd)
      exact h1.sub h2
    exact hcont.measurable
  measurable_DpH := measurable_const
  continuous_H_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    -- `(p, m) ↦ ‖p‖^2 − m^1` is continuous on all of `ℝ^d × ℝ`.
    have : Continuous
        (fun (pm : (Fin d → ℝ) × ℝ) =>
          (‖pm.1‖ : ℝ) ^ (2 : ℝ) - pm.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (pm : (Fin d → ℝ) × ℝ) => (‖pm.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp continuous_fst)
      have h2 : Continuous
          (fun (pm : (Fin d → ℝ) × ℝ) => pm.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          continuous_snd
      exact h1.sub h2
    exact this.continuousOn
  continuous_DpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  C := 1
  α := 2
  β := 1
  hC := by norm_num
  hα := by norm_num
  hβ := by norm_num
  f := fun _ _ => 1
  hf_continuous := continuousOn_const
  upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ m hm
    -- LHS: `‖0‖^2 − m^1 = 0 − m = -m`. RHS: `−m^1 / 1 + 1 = -m + 1`.
    have hnorm : (‖(0 : Fin d → ℝ)‖ : ℝ) = 0 := norm_zero
    have h0 : ((‖(0 : Fin d → ℝ)‖ : ℝ)) ^ (2 : ℝ) = 0 := by
      rw [hnorm]; exact Real.zero_rpow (by norm_num)
    rw [h0]
    -- Reduce to `0 − m^1 ≤ -(m^1) / 1 + 1`, i.e. `-m ≤ -m + 1`.
    have : (0 : ℝ) - m ^ (1 : ℝ) ≤ -(m ^ (1 : ℝ)) / 1 + 1 := by
      have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
      rw [hmrpow]; linarith
    exact this
  DpH_upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ _ _ _
    -- `‖0‖ = 0 ≤ 1 = f p m`.
    simp
  lower := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m hm
    -- LHS: `‖p‖^2 − m^1`. RHS: `‖p‖^2 / 1 − 1·(m^1 + 1) = ‖p‖^2 − m^1 − 1`.
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    change (‖p‖ : ℝ) ^ (2 : ℝ) / 1 - 1 * (m ^ (1 : ℝ) + 1)
        ≤ (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)
    rw [hmrpow]
    have hdiv : (‖p‖ : ℝ) ^ (2 : ℝ) / 1 = (‖p‖ : ℝ) ^ (2 : ℝ) := by ring
    rw [hdiv]
    linarith

/-!
## Hierarchy of growth bundles `(rem:hierarchy)`

The paper records (Remark `rem:hierarchy`,
`Source/FGU-monotone_revised.tex` lines 517–519) two implications
between the three growth bundles introduced above:

1. `HypothesisPowerGrowth` implies the `τ = 0` case of
   `HypothesisCongestionGrowth`.
2. `HypothesisCongestionGrowth` implies `HypothesisWeakGrowth`
   (with possibly a different value of `C`).

This file proves (1). The companion implication (2) lives in a
follow-up task whose only nontrivial step is the Young-type inequality
appearing in the paper.

The first implication needs an external witness `J` for the
`(a:mDpHat0)` extension of `m · D_pH` at `m = 0`, which the paper
deduces from the simple power-growth bound on `D_pH` via
Remark `rmk:implied-a`. We expose this as an extra hypothesis on the
implication theorem, so the present file does not depend on the
formalisation of `rmk:implied-a`.
-/

/-- For any real exponent `a > 0` and any positive real `m`, the sum
`m^a + 1/m` is at least `1`. The proof case-splits on `m ≤ 1` vs
`m ≥ 1`: in the first regime `1/m ≥ 1`, and in the second `m^a ≥ 1`
since `m ≥ 1` and `a ≥ 0` imply `m^a ≥ 1` by `Real.one_le_rpow`.

This is the elementary bound that lets us absorb the constant term
in the simple `D_pH`-bound `(eq:assH.DpH.upper.simple)` into the
two singular terms of the congestion bound
`(eq:assH.DpH.upper.congestion)` at `τ = 0`. -/
lemma assumptions_rpow_add_inv_ge_one
    {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    (1 : ℝ) ≤ m ^ a + 1 / m := by
  rcases le_or_gt m 1 with hm1 | hm1
  · -- `m ≤ 1` ⇒ `1/m ≥ 1`.
    have h1m : (1 : ℝ) ≤ 1 / m := by
      rw [le_div_iff₀ hm]
      simpa using hm1
    have hpow_nonneg : (0 : ℝ) ≤ m ^ a := Real.rpow_nonneg hm.le _
    linarith
  · -- `m > 1` ⇒ `m^a ≥ 1` since `a ≥ 0`.
    have h1pow : (1 : ℝ) ≤ m ^ a := Real.one_le_rpow hm1.le ha.le
    have hinv_nonneg : (0 : ℝ) ≤ 1 / m := by
      rw [one_div]
      exact inv_nonneg.mpr hm.le
    linarith

/--
**Paper Remark `(rem:hierarchy)`, first half**
(Ferreira–Gomes–Üçer, `Source/FGU-monotone_revised.tex`, lines 517–519).

`HypothesisPowerGrowth.toCongestionGrowth` shows that any Hamiltonian
satisfying the simple power-growth bundle `(onH.powergrowth)` also
satisfies the congestion-growth bundle `(onH.congestiongrowth)` with
`τ = 0`, provided we are also given a witness `J` of the
`(a:mDpHat0)` extension hypothesis (which the paper derives in
`rmk:implied-a` from the simple `D_pH`-bound).

The constants are taken to be `α' = h.α`, `β' = h.β`, `τ = 0`, and
`C' = 2·h.C`. The factor `2` accounts for the difference between
the simple lower bound and the congestion lower bound at `τ = 0`,
where `1/(m^0 + 1) = 1/2`, and is also enough slack to absorb the
constant term of the simple `D_pH`-bound into the singular terms
of the congestion `D_pH`-bound.
-/
def HypothesisPowerGrowth.toCongestionGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH)
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hJ : HypothesismDpHat0 (d := d) DpH J) :
    HypothesisCongestionGrowth (d := d) H DpH J := by
  refine
    { periodic_H := h.periodic_H
      periodic_DpH := h.periodic_DpH
      measurable_H := h.measurable_H
      measurable_DpH := h.measurable_DpH
      continuous_H_pm := h.continuous_H_pm
      continuous_DpH_pm := h.continuous_DpH_pm
      C := 2 * h.C
      α := h.α
      β := h.β
      τ := 0
      hC := by have := h.hC; positivity
      hα := h.hα
      hβ := h.hβ
      hτ := ⟨le_refl _, by norm_num⟩
      mDpHat0 := hJ
      upper := ?_
      DpH_upper := ?_
      lower := ?_ }
  · -- Upper bound: `H(x, 0, m) ≤ −m^β/(2C) + 2C` follows from
    -- `H(x, 0, m) ≤ −m^β/C + C` since `−m^β/C ≤ −m^β/(2C)` and
    -- `C ≤ 2C` (using `0 ≤ m^β`, `0 < C`).
    filter_upwards [h.upper] with x hx m hm
    have hupper := hx m hm
    have hpow_nonneg : (0 : ℝ) ≤ m ^ h.β := Real.rpow_nonneg hm.le _
    have hC_pos := h.hC
    -- Show: `H x 0 m ≤ -(m^β)/(2C) + 2C`.
    -- Both `-m^β/C ≤ -m^β/(2C)` and `C ≤ 2C` are easy from positivity of `C` and `m^β`.
    have h2C_pos : (0 : ℝ) < 2 * h.C := by positivity
    -- Rewrite `-m^β/C = -(m^β/C)` etc., for linarith.
    have hneg1 : -(m ^ h.β) / h.C = -(m ^ h.β / h.C) := by ring
    have hneg2 : -(m ^ h.β) / (2 * h.C) = -(m ^ h.β / (2 * h.C)) := by ring
    have hineq : m ^ h.β / (2 * h.C) ≤ m ^ h.β / h.C := by
      apply div_le_div_of_nonneg_left hpow_nonneg hC_pos
      linarith
    -- Conclude: `-(m^β)/C + C ≤ -(m^β)/(2C) + 2C`.
    have hslack : -(m ^ h.β) / h.C + h.C
                  ≤ -(m ^ h.β) / (2 * h.C) + 2 * h.C := by
      rw [hneg1, hneg2]; linarith
    linarith
  · -- DpH bound: at τ = 0 the congestion exponent on `‖p‖` reduces
    -- to `α - 1`, and `m^τ = 1`, `1/m^τ = 1`. We choose `C' = 2C`
    -- and bound the simple RHS by the congestion RHS termwise.
    filter_upwards [h.DpH_upper] with x hx p m hm
    have hdpH := hx p m hm
    -- Notation: the congestion exponent reduces.
    have hτ_pow : m ^ (0 : ℝ) = 1 := Real.rpow_zero m
    have hα_eq : h.α * (1 + (0 : ℝ) / h.β) - 1 = h.α - 1 := by
      have : (0 : ℝ) / h.β = 0 := zero_div _
      rw [this]; ring
    -- Reduce the goal.
    change ‖DpH x p m‖
        ≤ 2 * h.C * (1 / m + 1 / m ^ (0 : ℝ))
            * ‖p‖ ^ (h.α * (1 + (0 : ℝ) / h.β) - 1)
          + 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m)
    rw [hτ_pow, hα_eq]
    -- After `rw`, the `1/m^0` term is `1/1`. Simplify.
    have h11 : (1 : ℝ) / 1 = 1 := by norm_num
    rw [h11]
    -- Now: `2C (1/m + 1) ‖p‖^{α-1} + 2C (m^{β-β/α} + 1/m)`.
    have hC := h.hC
    have hm_pos := hm
    have hppow_nonneg : (0 : ℝ) ≤ ‖p‖ ^ (h.α - 1) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hmpow_nonneg : (0 : ℝ) ≤ m ^ (h.β - h.β / h.α) :=
      Real.rpow_nonneg hm.le _
    have h_inv_m_nonneg : (0 : ℝ) ≤ 1 / m := by
      rw [one_div]; exact inv_nonneg.mpr hm.le
    -- The congestion RHS at τ = 0 is
    --   2C (1/m + 1) ‖p‖^{α-1} + 2C (m^{β-β/α} + 1/m).
    -- We compare with the simple RHS  C (‖p‖^{α-1} + m^{β-β/α} + 1).
    -- Bound term-by-term:
    --  • `C·‖p‖^{α-1} ≤ 2C·1·‖p‖^{α-1} ≤ 2C·(1/m + 1)·‖p‖^{α-1}` (since `1/m ≥ 0`).
    --  • `C·m^{β-β/α} ≤ 2C·m^{β-β/α}` (since `0 ≤ m^{β-β/α}`).
    --  • `C ≤ 2C·(m^{β-β/α} + 1/m)` since
    --    `m^{β-β/α} + 1/m ≥ 1` by `assumptions_rpow_add_inv_ge_one`
    --    (using `β - β/α > 0`, since `α > 1` and `β > 0`).
    -- Add the three.
    have hβα_pos : 0 < h.β - h.β / h.α := by
      have hβ := h.hβ
      have hα := h.hα
      have hαpos : 0 < h.α := lt_trans zero_lt_one hα
      have hdiv_lt : h.β / h.α < h.β := by
        rw [div_lt_iff₀ hαpos]
        nlinarith
      linarith
    have hsum_ge_one : (1 : ℝ) ≤ m ^ (h.β - h.β / h.α) + 1 / m :=
      assumptions_rpow_add_inv_ge_one hβα_pos hm
    -- Compute each upper estimate.
    have hpart1 :
        h.C * ‖p‖ ^ (h.α - 1)
          ≤ 2 * h.C * (1 / m + 1) * ‖p‖ ^ (h.α - 1) := by
      have h1m : (1 : ℝ) ≤ 1 / m + 1 := by linarith [h_inv_m_nonneg]
      have : h.C ≤ 2 * h.C * (1 / m + 1) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hppow_nonneg
    have hpart2 :
        h.C * m ^ (h.β - h.β / h.α)
          ≤ 2 * h.C * m ^ (h.β - h.β / h.α) := by
      have hCle : h.C ≤ 2 * h.C := by linarith
      exact mul_le_mul_of_nonneg_right hCle hmpow_nonneg
    have hpart3 :
        h.C ≤ 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m) := by
      have : h.C * 1 ≤ h.C * (m ^ (h.β - h.β / h.α) + 1 / m) :=
        mul_le_mul_of_nonneg_left hsum_ge_one hC.le
      linarith
    -- Combine.
    -- Note we need to rewrite `2C·(1/m + 1)·‖p‖^{α-1}`
    -- as `2C·(1/m + 1/m^0)·‖p‖^{α-1}` after the `rw [hτ_pow]`,
    -- but the `rw` already replaced `m^0` with `1`, so we are
    -- comparing with `2C·(1/m + 1)·‖p‖^{α-1}`.
    -- Final: `‖DpH‖ ≤ C(‖p‖^{α-1} + m^{β-β/α} + 1)
    --                 = C·‖p‖^{α-1} + C·m^{β-β/α} + C`.
    -- And RHS ≥ `2C(1/m+1)·‖p‖^{α-1} + 2C·m^{β-β/α} + 2C·(1/m)`,
    -- which ≥ `2C(1/m+1)·‖p‖^{α-1} + 2C(m^{β-β/α} + 1/m)`.
    -- Combine `hpart1`, `hpart2`, `hpart3`:
    have hfact :
        h.C * (‖p‖ ^ (h.α - 1) + m ^ (h.β - h.β / h.α) + 1)
          ≤ 2 * h.C * (1 / m + 1) * ‖p‖ ^ (h.α - 1)
            + 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m) := by
      have hexpand :
          h.C * (‖p‖ ^ (h.α - 1) + m ^ (h.β - h.β / h.α) + 1)
            = h.C * ‖p‖ ^ (h.α - 1) + h.C * m ^ (h.β - h.β / h.α) + h.C := by
        ring
      rw [hexpand]
      have hsplit2 :
          2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m)
            = 2 * h.C * m ^ (h.β - h.β / h.α) + 2 * h.C * (1 / m) := by
        ring
      have hsplit2' :
          2 * h.C * (1 / m + 1) * ‖p‖ ^ (h.α - 1)
            = 2 * h.C * (1 / m) * ‖p‖ ^ (h.α - 1)
              + 2 * h.C * ‖p‖ ^ (h.α - 1) := by ring
      have hsurplus_a : (0 : ℝ) ≤ 2 * h.C * (1 / m) * ‖p‖ ^ (h.α - 1) := by
        have h1 : (0 : ℝ) ≤ 2 * h.C * (1 / m) := by
          have := h_inv_m_nonneg
          have := hC; positivity
        exact mul_nonneg h1 hppow_nonneg
      have hsurplus_b : (0 : ℝ) ≤ h.C * m ^ (h.β - h.β / h.α) := by
        exact mul_nonneg hC.le hmpow_nonneg
      -- Direct construction:
      -- LHS = h.C*a + h.C*b + h.C
      --    ≤ 2*h.C*a + h.C*b + h.C            [a ≤ 2a since a ≥ 0]
      --    ≤ 2*h.C*(1/m+1)*a + h.C*b + h.C    [via hsplit2', surplus_a ≥ 0]
      --    ≤ 2*h.C*(1/m+1)*a + 2*h.C*b + h.C  [hpart2-style]
      --    ≤ 2*h.C*(1/m+1)*a + 2*h.C*b + 2*h.C*(b + 1/m) - 2*h.C*b
      --                                       [via hpart3]
      --    = 2*h.C*(1/m+1)*a + 2*h.C*(b+1/m)
      -- Set up cleanly:
      have habs1 : h.C * ‖p‖ ^ (h.α - 1)
                    ≤ 2 * h.C * (1 / m + 1) * ‖p‖ ^ (h.α - 1) := hpart1
      have habs2 : h.C * m ^ (h.β - h.β / h.α)
                    ≤ 2 * h.C * m ^ (h.β - h.β / h.α) := hpart2
      have habs3 : h.C ≤ 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m) := hpart3
      -- Now sum them up directly:
      have hsum :
          h.C * ‖p‖ ^ (h.α - 1) + h.C * m ^ (h.β - h.β / h.α) + h.C
            ≤ 2 * h.C * (1 / m + 1) * ‖p‖ ^ (h.α - 1)
              + 2 * h.C * m ^ (h.β - h.β / h.α)
              + 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m) := by
        linarith [habs1, habs2, habs3]
      -- Replace `2*h.C*m^... + 2*h.C*(m^... + 1/m)` with
      -- something `≤ 2*h.C*(m^... + 1/m)`. The first term `2*h.C*m^...`
      -- is being absorbed by `hsplit2`-shift. But that increases, not
      -- decreases. So we instead drop habs2 and use the surplus from habs1.
      -- Specifically: we have surplus `h.C*‖p‖^(α-1)*(2*(1/m+1) - 1)
      -- = h.C*‖p‖^(α-1)*(2/m + 1) ≥ 0`
      -- which gives us `LHS - habs1's_LHS_contribution
      --                ≤ habs1's_RHS_contribution - h.C*‖p‖^(α-1)`
      -- The cleanest is to just split habs1 into two pieces:
      -- `h.C*‖p‖^(α-1) ≤ 2*h.C*‖p‖^(α-1) + 2*h.C/m * ‖p‖^(α-1)`,
      -- but the LHS of habs1 is just `h.C * ‖p‖^(α-1)`, so the
      -- excess on RHS is `h.C*‖p‖^(α-1) + 2*h.C/m * ‖p‖^(α-1) ≥ 0`.
      -- Forget all that.
      -- Direct approach: prove
      --   habs1_alt: h.C * ‖p‖^(α-1) ≤ 2*h.C*(1/m+1)*‖p‖^(α-1)
      --   habs23 :  h.C*m^... + h.C ≤ 2*h.C*(m^... + 1/m)
      -- Show habs23: h.C*m^... + h.C ≤ 2*h.C*m^... + 2*h.C/m
      -- ⇔ h.C ≤ h.C*m^... + 2*h.C/m
      -- ⇔ 1 ≤ m^... + 2/m, which holds since m^... + 1/m ≥ 1 ≤ m^... + 2/m.
      have habs23 :
          h.C * m ^ (h.β - h.β / h.α) + h.C
            ≤ 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m) := by
        -- Multiply `m^... + 1/m ≥ 1` by `h.C > 0` and combine:
        have hkey : h.C ≤ h.C * m ^ (h.β - h.β / h.α) + 2 * h.C * (1 / m) := by
          have h1 : h.C ≤ h.C * (m ^ (h.β - h.β / h.α) + 1 / m) := by
            have := mul_le_mul_of_nonneg_left hsum_ge_one hC.le
            linarith
          have h2 : h.C * (m ^ (h.β - h.β / h.α) + 1 / m)
                      = h.C * m ^ (h.β - h.β / h.α) + h.C * (1 / m) := by ring
          have h3 : h.C * (1 / m) ≤ 2 * h.C * (1 / m) := by
            have : h.C ≤ 2 * h.C := by linarith
            exact mul_le_mul_of_nonneg_right this h_inv_m_nonneg
          linarith
        -- Now `h.C ≤ h.C*m^... + 2*h.C/m`, so
        -- `h.C*m^... + h.C ≤ 2*h.C*m^... + 2*h.C/m = 2*h.C*(m^... + 1/m)`.
        have hexpand2 : 2 * h.C * (m ^ (h.β - h.β / h.α) + 1 / m)
              = 2 * h.C * m ^ (h.β - h.β / h.α) + 2 * h.C * (1 / m) := by ring
        linarith
      -- Combine habs1 and habs23:
      linarith [habs1, habs23, hexpand]
    exact le_trans hdpH hfact
  · -- Lower bound: at τ = 0, the congestion lower is
    --   (1/(2C')) ‖p‖^α − 2C' (m^β + 1)
    -- where the prefactor `1/(m^0 + 1) = 1/2`, the exponent
    -- `α(1 + 0/β) = α`, and we picked `C' = 2C`, so the bound
    -- becomes `‖p‖^α/(4C) − 2C (m^β + 1)`. The simple lower bound
    -- gives `‖p‖^α/C − C(m^β + 1)`. We compare termwise.
    filter_upwards [h.lower] with x hx p m hm
    have hlow := hx p m hm
    have hτ_pow : m ^ (0 : ℝ) = 1 := Real.rpow_zero m
    have hα_eq : h.α * (1 + (0 : ℝ) / h.β) = h.α := by
      have : (0 : ℝ) / h.β = 0 := zero_div _
      rw [this]; ring
    change (1 / (2 * h.C)) * (1 / (m ^ (0 : ℝ) + 1))
            * ‖p‖ ^ (h.α * (1 + (0 : ℝ) / h.β))
          - 2 * h.C * (m ^ h.β + 1)
        ≤ H x p m
    rw [hτ_pow, hα_eq]
    -- Now: `(1/(2C)) · (1/2) · ‖p‖^α − 2C · (m^β + 1)`.
    have hC := h.hC
    have hppow_nonneg : (0 : ℝ) ≤ ‖p‖ ^ h.α :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hmpow_nonneg : (0 : ℝ) ≤ m ^ h.β := Real.rpow_nonneg hm.le _
    -- Compare with the simple lower bound `‖p‖^α / C − C(m^β + 1) ≤ H`.
    -- Show: `(1/(4C))‖p‖^α − 2C(m^β + 1) ≤ ‖p‖^α/C − C(m^β + 1)`.
    have hcoeff : (1 / (2 * h.C)) * (1 / ((1 : ℝ) + 1)) * ‖p‖ ^ h.α
                    = ‖p‖ ^ h.α / (4 * h.C) := by
      field_simp
      ring
    rw [hcoeff]
    -- Key inequalities: `‖p‖^α/(4C) ≤ ‖p‖^α / C` (since `‖p‖^α ≥ 0`,
    -- `0 < C`), and `−2C(m^β+1) ≤ −C(m^β+1)` (since `0 ≤ m^β+1`,
    -- `0 < C`).
    have hp_div : ‖p‖ ^ h.α / (4 * h.C) ≤ ‖p‖ ^ h.α / h.C := by
      apply div_le_div_of_nonneg_left hppow_nonneg hC
      linarith
    have hmb_pos : (0 : ℝ) ≤ m ^ h.β + 1 := by linarith
    have hCfactor : h.C * (m ^ h.β + 1) ≤ 2 * h.C * (m ^ h.β + 1) := by
      have : h.C ≤ 2 * h.C := by linarith
      exact mul_le_mul_of_nonneg_right this hmb_pos
    have hsum :
        ‖p‖ ^ h.α / (4 * h.C) - 2 * h.C * (m ^ h.β + 1)
          ≤ ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) := by linarith
    -- The hypothesis `hlow` reads `H x p m ≥ ‖p‖^α / C − C(m^β + 1)`.
    -- Rewriting it as `≤`:
    have hlow' : ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x p m := hlow
    linarith

-- Sanity-check `noncomputable example` of `HypothesisCongestionGrowth`
-- inhabitedness moved to after `HypothesisPowerGrowth.toMDpHat0` is
-- available (search for `simpleHypothesisCongestionGrowth_example`).

/-!
### `(rem:hierarchy)`, second half — `HypothesisCongestionGrowth ⇒ HypothesisWeakGrowth`

The paper's second hierarchy implication (Remark `rem:hierarchy`,
`Source/FGU-monotone_revised.tex` lines 517–519): the only nontrivial
step is showing that the congestion lower bound implies the weak
lower bound, which the paper does using the Young-type inequality
```
|p|^{α(1+τ/β)}/(m^τ+1) + (m^β+1) ≥ |p|^α / 2^{β/(β+τ)}.
```
The auxiliary lemma `assumptions_young_congestion_to_weak` below establishes this
inequality. The remaining steps (upper bound, gradient bound) are
straightforward type plumbing.
-/

/-- Auxiliary inequality `2 (m^β + 1)^(τ/β) ≥ m^τ + 1`, valid for
`m > 0`, `0 < β`, and `0 ≤ τ`. The proof case-splits on `m ≤ 1` and
`m ≥ 1`. -/
private lemma two_mul_rpow_pow_add_one_ge
    {m β τ : ℝ} (hm : 0 < m) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    m ^ τ + 1 ≤ 2 * (m ^ β + 1) ^ (τ / β) := by
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hmβ_nonneg : (0 : ℝ) ≤ m ^ β := Real.rpow_nonneg hm.le _
  have hsum_pos : (0 : ℝ) < m ^ β + 1 := by linarith
  have hsum_nonneg : (0 : ℝ) ≤ m ^ β + 1 := hsum_pos.le
  have htbβ_nonneg : (0 : ℝ) ≤ τ / β := div_nonneg hτ (le_of_lt hβ)
  rcases le_or_gt m 1 with hm1 | hm1
  · -- `m ≤ 1`: then `m^τ ≤ 1`, so `m^τ + 1 ≤ 2 ≤ 2 (m^β+1)^(τ/β)`
    -- (using `(m^β+1)^(τ/β) ≥ 1` since `m^β+1 ≥ 1`).
    have hmτ_le_one : m ^ τ ≤ 1 := Real.rpow_le_one hm.le hm1 hτ
    have hbase_ge_one : (1 : ℝ) ≤ m ^ β + 1 := by linarith
    have hpow_ge_one : (1 : ℝ) ≤ (m ^ β + 1) ^ (τ / β) :=
      Real.one_le_rpow hbase_ge_one htbβ_nonneg
    linarith
  · -- `m ≥ 1`: then `m^β ≥ 1`, hence `(m^β + 1)^(τ/β) ≥ (m^β)^(τ/β) = m^τ`,
    -- and we use `m^τ ≥ 1` to conclude `m^τ + 1 ≤ 2 m^τ ≤ 2 (m^β+1)^(τ/β)`.
    have hm_ge_one : (1 : ℝ) ≤ m := hm1.le
    have hmβ_ge_one : (1 : ℝ) ≤ m ^ β := Real.one_le_rpow hm_ge_one hβ.le
    have hmτ_ge_one : (1 : ℝ) ≤ m ^ τ := Real.one_le_rpow hm_ge_one hτ
    -- Bound `(m^β + 1)^(τ/β) ≥ (m^β)^(τ/β) = m^(β·(τ/β)) = m^τ`.
    have hmono :
        (m ^ β) ^ (τ / β) ≤ (m ^ β + 1) ^ (τ / β) :=
      Real.rpow_le_rpow hmβ_nonneg (by linarith) htbβ_nonneg
    have hexp_eq : β * (τ / β) = τ := by
      field_simp
    have hpow_compose : (m ^ β) ^ (τ / β) = m ^ τ := by
      rw [← Real.rpow_mul hm.le β (τ / β), hexp_eq]
    have hge : m ^ τ ≤ (m ^ β + 1) ^ (τ / β) := by
      rw [← hpow_compose]; exact hmono
    linarith

/-- **Young-type inequality** from Remark `rem:hierarchy`
(`Source/FGU-monotone_revised.tex`, line 519):
for `0 ≤ a`, `0 < m`, `0 < α`, `0 < β`, `0 ≤ τ`,
```
a^α / 2^(β/(β+τ)) ≤ a^(α(1+τ/β)) / (m^τ + 1) + (m^β + 1).
```
The proof follows the paper's two-step argument: weighted AM-GM with
weights `(β/(β+τ), τ/(β+τ))` reduces the right-hand side to
`a^α (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`, and the auxiliary
inequality `(m^τ+1) ≤ 2 (m^β+1)^(τ/β)` then gives
`(m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ)) ≥ 1 / 2^(β/(β+τ))`. -/
lemma assumptions_young_congestion_to_weak
    {a m α β τ : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    (hα : 0 < α) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    a ^ α / 2 ^ (β / (β + τ))
      ≤ a ^ (α * (1 + τ / β)) / (m ^ τ + 1) + (m ^ β + 1) := by
  -- Set up basic positivity facts.
  have hβτ_pos : 0 < β + τ := by linarith
  have hβτ_ne : β + τ ≠ 0 := ne_of_gt hβτ_pos
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hβτ_β_nonneg : (0 : ℝ) ≤ β / (β + τ) := div_nonneg hβ.le hβτ_pos.le
  have hβτ_τ_nonneg : (0 : ℝ) ≤ τ / (β + τ) := div_nonneg hτ hβτ_pos.le
  have hweights : β / (β + τ) + τ / (β + τ) = 1 := by
    field_simp
  have hmβ_nonneg : (0 : ℝ) ≤ m ^ β := Real.rpow_nonneg hm.le _
  have hmτ_nonneg : (0 : ℝ) ≤ m ^ τ := Real.rpow_nonneg hm.le _
  have hmτ1_pos : (0 : ℝ) < m ^ τ + 1 := by linarith
  have hmβ1_pos : (0 : ℝ) < m ^ β + 1 := by linarith
  have hmτ1_nonneg : (0 : ℝ) ≤ m ^ τ + 1 := hmτ1_pos.le
  have hmβ1_nonneg : (0 : ℝ) ≤ m ^ β + 1 := hmβ1_pos.le
  -- Define the abbreviations `A`, `B` from the paper's argument.
  set A : ℝ := a ^ (α * (1 + τ / β)) / (m ^ τ + 1) with hA
  set B : ℝ := m ^ β + 1 with hB
  have hA_nonneg : 0 ≤ A := by
    apply div_nonneg
    · exact Real.rpow_nonneg ha _
    · exact hmτ1_nonneg
  have hB_nonneg : 0 ≤ B := hmβ1_nonneg
  -- Weighted AM-GM: `A^(β/(β+τ)) * B^(τ/(β+τ)) ≤ (β/(β+τ))·A + (τ/(β+τ))·B`.
  have hamgm : A ^ (β / (β + τ)) * B ^ (τ / (β + τ))
      ≤ β / (β + τ) * A + τ / (β + τ) * B :=
    Real.geom_mean_le_arith_mean2_weighted hβτ_β_nonneg hβτ_τ_nonneg
      hA_nonneg hB_nonneg hweights
  -- Compute `A^(β/(β+τ)) = a^α / (m^τ+1)^(β/(β+τ))`.
  have hA_pow : A ^ (β / (β + τ)) = a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) := by
    have hnum_nonneg : (0 : ℝ) ≤ a ^ (α * (1 + τ / β)) := Real.rpow_nonneg ha _
    rw [hA, Real.div_rpow hnum_nonneg hmτ1_nonneg]
    congr 1
    -- `(a^(α(1+τ/β)))^(β/(β+τ)) = a^(α(1+τ/β) · β/(β+τ)) = a^α`.
    rw [← Real.rpow_mul ha]
    congr 1
    -- Show `α(1+τ/β) · β/(β+τ) = α`.
    have hkey : (1 + τ / β) * (β / (β + τ)) = 1 := by
      field_simp
    have : α * (1 + τ / β) * (β / (β + τ)) = α * ((1 + τ / β) * (β / (β + τ))) := by
      ring
    rw [this, hkey, mul_one]
  -- Bound `β/(β+τ) * A + τ/(β+τ) * B ≤ A + B`, since both weights are `≤ 1`
  -- and `A, B ≥ 0`.
  have hweight_le : β / (β + τ) * A + τ / (β + τ) * B ≤ A + B := by
    have h1 : β / (β + τ) * A ≤ A := by
      have hβτ_β_le : β / (β + τ) ≤ 1 := by
        rw [div_le_one hβτ_pos]; linarith
      nlinarith
    have h2 : τ / (β + τ) * B ≤ B := by
      have hβτ_τ_le : τ / (β + τ) ≤ 1 := by
        rw [div_le_one hβτ_pos]; linarith
      nlinarith
    linarith
  -- So we have: `A^(β/(β+τ)) * B^(τ/(β+τ)) ≤ A + B`,
  -- i.e. `a^α * B^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ)) ≤ A + B`.
  have hcombined : a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) * B ^ (τ / (β + τ))
      ≤ A + B := by
    rw [← hA_pow]
    linarith
  -- Now we want to bound `a^α / 2^(β/(β+τ)) ≤ a^α * B^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`.
  -- Use the auxiliary inequality `(m^τ+1) ≤ 2·(m^β+1)^(τ/β)`, raised to `β/(β+τ)`:
  --   `(m^τ+1)^(β/(β+τ)) ≤ 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`.
  have hkey_aux : m ^ τ + 1 ≤ 2 * (m ^ β + 1) ^ (τ / β) :=
    two_mul_rpow_pow_add_one_ge hm hβ hτ
  -- Raise to the power `β/(β+τ) ≥ 0`:
  have hpow_aux :
      (m ^ τ + 1) ^ (β / (β + τ))
        ≤ (2 * (m ^ β + 1) ^ (τ / β)) ^ (β / (β + τ)) :=
    Real.rpow_le_rpow hmτ1_nonneg hkey_aux hβτ_β_nonneg
  -- Expand the RHS: `(2 · (m^β+1)^(τ/β))^(β/(β+τ))
  --     = 2^(β/(β+τ)) · ((m^β+1)^(τ/β))^(β/(β+τ))
  --     = 2^(β/(β+τ)) · (m^β+1)^(τ/β · β/(β+τ))
  --     = 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`.
  have hpow_expand : (2 * (m ^ β + 1) ^ (τ / β)) ^ (β / (β + τ))
      = 2 ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg hmβ1_nonneg _)]
    congr 1
    rw [← Real.rpow_mul hmβ1_nonneg]
    congr 1
    field_simp
  -- So `(m^τ+1)^(β/(β+τ)) ≤ 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`.
  have hpow_aux' :
      (m ^ τ + 1) ^ (β / (β + τ))
        ≤ 2 ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ)) := by
    rw [← hpow_expand]; exact hpow_aux
  -- Strict positivity facts for the divisions.
  have hmτ1pow_pos : (0 : ℝ) < (m ^ τ + 1) ^ (β / (β + τ)) :=
    Real.rpow_pos_of_pos hmτ1_pos _
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (β / (β + τ)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hBpow_nonneg : (0 : ℝ) ≤ B ^ (τ / (β + τ)) := Real.rpow_nonneg hB_nonneg _
  have hBpow_pos : (0 : ℝ) < B ^ (τ / (β + τ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  -- Now: `a^α / 2^(β/(β+τ)) ≤ a^α · (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`.
  -- Equivalently: `a^α · (m^τ+1)^(β/(β+τ)) ≤ a^α · 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`,
  -- which follows from `hpow_aux'` multiplied by `a^α ≥ 0`.
  have ha_α_nonneg : (0 : ℝ) ≤ a ^ α := Real.rpow_nonneg ha _
  have hmul_aux : a ^ α * (m ^ τ + 1) ^ (β / (β + τ))
      ≤ a ^ α * (2 ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ))) :=
    mul_le_mul_of_nonneg_left hpow_aux' ha_α_nonneg
  -- Divide both sides by `2^(β/(β+τ)) · (m^τ+1)^(β/(β+τ)) > 0`.
  have hdenom_pos : 0 < 2 ^ (β / (β + τ)) * (m ^ τ + 1) ^ (β / (β + τ)) :=
    mul_pos h2pow_pos hmτ1pow_pos
  -- Equivalent rearrangement:
  -- `a^α / 2^(β/(β+τ)) ≤ a^α · (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`.
  have hstep1 :
      a ^ α / 2 ^ (β / (β + τ))
        ≤ a ^ α * (m ^ β + 1) ^ (τ / (β + τ)) / (m ^ τ + 1) ^ (β / (β + τ)) := by
    rw [div_le_div_iff₀ h2pow_pos hmτ1pow_pos]
    nlinarith [hmul_aux, ha_α_nonneg, h2pow_pos.le, hmτ1pow_pos.le, hBpow_nonneg]
  -- Combine with `hcombined`:
  -- `a^α · (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ)) ≤ A + B`.
  have hstep2 :
      a ^ α * (m ^ β + 1) ^ (τ / (β + τ)) / (m ^ τ + 1) ^ (β / (β + τ))
        ≤ A + B := by
    -- `B = m^β + 1` (definitional via `set`), so the LHS coincides with
    -- `a^α / (m^τ+1)^(β/(β+τ)) * B^(τ/(β+τ))`.
    have heq : a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) * B ^ (τ / (β + τ))
        = a ^ α * (m ^ β + 1) ^ (τ / (β + τ))
            / (m ^ τ + 1) ^ (β / (β + τ)) := by
      show a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ))
        = a ^ α * (m ^ β + 1) ^ (τ / (β + τ))
            / (m ^ τ + 1) ^ (β / (β + τ))
      ring
    linarith [heq ▸ hcombined]
  linarith

/--
**Paper Remark `(rem:hierarchy)`, second half**
(Ferreira–Gomes–Üçer, `Source/FGU-monotone_revised.tex`, lines 517–519).

`HypothesisCongestionGrowth.toWeakGrowth` shows that any Hamiltonian
satisfying the congestion-growth bundle `(onH.congestiongrowth)` also
satisfies the weak-growth bundle `(onH.weakgrowth)`, possibly with a
different value of the constant `C`.

The new constant is
`C' := h.C · 2^(h.β/(h.β + h.τ)) + h.C + 1/h.C`,
which dominates the simple constants needed to absorb the prefactor
`2^(β/(β+τ))` (from the Young-type inequality
`assumptions_young_congestion_to_weak`) into the lower bound, while remaining
larger than `h.C` itself so that the upper bound carries over.

The bound function `f` for the gradient is the explicit RHS of the
congestion `D_pH`-bound:
`f(p, m) = h.C · (1/m + 1/m^τ) · ‖p‖^(α(1+τ/β) − 1)
        + h.C · (m^(β − β/α) + 1/m)`,
which is continuous on `{m > 0}`.
-/
noncomputable def HypothesisCongestionGrowth.toWeakGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisCongestionGrowth (d := d) H DpH J) :
    HypothesisWeakGrowth (d := d) H DpH := by
  -- Abbreviations to keep the proof readable.
  set C' : ℝ := h.C * 2 ^ (h.β / (h.β + h.τ)) + h.C + 1 / h.C with hC'_def
  have hC_pos := h.hC
  have hβ_pos := h.hβ
  have hτ_nonneg : 0 ≤ h.τ := h.hτ.1
  have hβτ_pos : 0 < h.β + h.τ := by linarith
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (h.β / (h.β + h.τ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (h.β / (h.β + h.τ)) := by
    have hexp_nonneg : (0 : ℝ) ≤ h.β / (h.β + h.τ) :=
      div_nonneg hβ_pos.le hβτ_pos.le
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp_nonneg
  have hC'_pos : 0 < C' := by
    have h1 : 0 < h.C * 2 ^ (h.β / (h.β + h.τ)) := mul_pos hC_pos h2pow_pos
    have h2 : 0 < 1 / h.C := by positivity
    linarith
  -- The dominance facts we need:
  have hC_le_C' : h.C ≤ C' := by
    have hpos1 : 0 ≤ h.C * 2 ^ (h.β / (h.β + h.τ)) - h.C := by
      have : h.C ≤ h.C * 2 ^ (h.β / (h.β + h.τ)) := by
        have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
        linarith
      linarith
    have hpos2 : 0 ≤ 1 / h.C := by positivity
    linarith
  -- Bound function for `D_pH` (continuous on `{m > 0}`).
  -- `f(p, m) = h.C · (1/m + 1/m^τ) · ‖p‖^(α(1+τ/β)−1)
  --           + h.C · (m^(β−β/α) + 1/m)`.
  let f : (Fin d → ℝ) → ℝ → ℝ := fun p m =>
    h.C * (1 / m + 1 / m ^ h.τ) * ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
      + h.C * (m ^ (h.β - h.β / h.α) + 1 / m)
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hf_continuous :
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => f pm.1 pm.2)
        {pm | 0 < pm.2} := by
    -- Positive-exponent facts.
    have hexp_p_nonneg : (0 : ℝ) ≤ h.α * (1 + h.τ / h.β) - 1 := by
      have hτβ_nonneg : (0 : ℝ) ≤ h.τ / h.β := div_nonneg hτ_nonneg hβ_pos.le
      have h1τβ_ge_one : (1 : ℝ) ≤ 1 + h.τ / h.β := by linarith
      have hα_ge_one : (1 : ℝ) ≤ h.α := h.hα.le
      have : (1 : ℝ) ≤ h.α * (1 + h.τ / h.β) := by
        have := mul_le_mul hα_ge_one h1τβ_ge_one (by norm_num) (by linarith)
        linarith
      linarith
    have hexp_m_nonneg : (0 : ℝ) ≤ h.β - h.β / h.α := by
      have hα_gt_one := h.hα
      have : h.β / h.α < h.β := by
        rw [div_lt_iff₀ hα_pos]
        nlinarith [hβ_pos, hα_gt_one]
      linarith
    -- The ingredients, all continuous on the relevant domain:
    -- `m ↦ 1/m`, continuous on `{m > 0} ⊆ {m ≠ 0}`.
    have h_inv_m : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => 1 / pm.2)
        {pm | 0 < pm.2} := by
      refine ContinuousOn.div continuousOn_const continuous_snd.continuousOn ?_
      intro pm hpm; exact ne_of_gt hpm
    -- `m ↦ m^τ`, continuous on all of ℝ since `τ ≥ 0`.
    have h_pow_τ : Continuous (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ h.τ) :=
      (Real.continuous_rpow_const hτ_nonneg).comp continuous_snd
    -- `m ↦ 1/m^τ`, continuous on `{m > 0}` since `m^τ > 0` for `m > 0`.
    have h_inv_powτ : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ => 1 / pm.2 ^ h.τ)
        {pm | 0 < pm.2} := by
      refine ContinuousOn.div continuousOn_const h_pow_τ.continuousOn ?_
      intro pm hpm
      have hm : 0 < pm.2 := hpm
      exact ne_of_gt (Real.rpow_pos_of_pos hm _)
    -- `1/m + 1/m^τ`.
    have h_invsum : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ => 1 / pm.2 + 1 / pm.2 ^ h.τ)
        {pm | 0 < pm.2} := h_inv_m.add h_inv_powτ
    -- `‖p‖^(α(1+τ/β)−1)`, continuous on all of ℝ^d × ℝ since the exponent ≥ 0.
    have h_p_pow : Continuous
        (fun pm : (Fin d → ℝ) × ℝ =>
          ‖pm.1‖ ^ (h.α * (1 + h.τ / h.β) - 1)) :=
      (Real.continuous_rpow_const hexp_p_nonneg).comp
        ((continuous_norm).comp continuous_fst)
    -- `m^(β−β/α)`, continuous on all of ℝ since the exponent ≥ 0.
    have h_m_pow : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ (h.β - h.β / h.α)) :=
      (Real.continuous_rpow_const hexp_m_nonneg).comp continuous_snd
    -- Term 1: `h.C · (1/m + 1/m^τ) · ‖p‖^(α(1+τ/β)−1)`.
    have h_term1 : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ =>
          h.C * (1 / pm.2 + 1 / pm.2 ^ h.τ)
            * ‖pm.1‖ ^ (h.α * (1 + h.τ / h.β) - 1))
        {pm | 0 < pm.2} :=
      (continuousOn_const.mul h_invsum).mul h_p_pow.continuousOn
    -- Term 2: `h.C · (m^(β−β/α) + 1/m)`.
    have h_term2 : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ =>
          h.C * (pm.2 ^ (h.β - h.β / h.α) + 1 / pm.2))
        {pm | 0 < pm.2} :=
      continuousOn_const.mul (h_m_pow.continuousOn.add h_inv_m)
    exact h_term1.add h_term2
  -- Now construct the weak-growth bundle.
  refine
    { periodic_H := h.periodic_H
      periodic_DpH := h.periodic_DpH
      measurable_H := h.measurable_H
      measurable_DpH := h.measurable_DpH
      continuous_H_pm := h.continuous_H_pm
      continuous_DpH_pm := h.continuous_DpH_pm
      C := C'
      α := h.α
      β := h.β
      hC := hC'_pos
      hα := h.hα
      hβ := h.hβ
      f := f
      hf_continuous := hf_continuous
      upper := ?_
      DpH_upper := ?_
      lower := ?_ }
  · -- Upper: `H(x, 0, m) ≤ -m^β/h.C + h.C ≤ -m^β/C' + C'`,
    -- using `h.C ≤ C'` and `m^β ≥ 0`, `0 < h.C`.
    filter_upwards [h.upper] with x hx m hm
    have hupper := hx m hm
    have hpow_nonneg : (0 : ℝ) ≤ m ^ h.β := Real.rpow_nonneg hm.le _
    have hdiv_le : m ^ h.β / C' ≤ m ^ h.β / h.C :=
      div_le_div_of_nonneg_left hpow_nonneg hC_pos hC_le_C'
    have hslack : -(m ^ h.β) / h.C + h.C ≤ -(m ^ h.β) / C' + C' := by
      have hneg1 : -(m ^ h.β) / h.C = -(m ^ h.β / h.C) := by ring
      have hneg2 : -(m ^ h.β) / C' = -(m ^ h.β / C') := by ring
      rw [hneg1, hneg2]; linarith
    linarith
  · -- DpH bound: just unfold `f` to match the congestion bound exactly.
    filter_upwards [h.DpH_upper] with x hx p m hm
    exact hx p m hm
  · -- Lower: combine the congestion lower bound with the Young-type inequality
    -- to obtain the weak lower bound.
    filter_upwards [h.lower] with x hx p m hm
    have hlow := hx p m hm
    have hp_nonneg : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
    have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
    -- Apply the Young-type inequality at `a = ‖p‖`, `(m, α, β, τ) = (m, h.α, h.β, h.τ)`.
    have hyoung := assumptions_young_congestion_to_weak (a := ‖p‖) (m := m) (α := h.α)
      (β := h.β) (τ := h.τ) hp_nonneg hm hα_pos hβ_pos hτ_nonneg
    -- Multiply by `1/h.C > 0`:
    have hC_inv_pos : 0 < 1 / h.C := by positivity
    have hyoung_scaled :
        (1 / h.C) * (‖p‖ ^ h.α / 2 ^ (h.β / (h.β + h.τ)))
          ≤ (1 / h.C) * (‖p‖ ^ (h.α * (1 + h.τ / h.β)) / (m ^ h.τ + 1)
                          + (m ^ h.β + 1)) :=
      mul_le_mul_of_nonneg_left hyoung hC_inv_pos.le
    -- Rewrite the LHS: `(1/C) · ‖p‖^α / 2^(β/(β+τ)) = ‖p‖^α / (C · 2^(β/(β+τ)))`.
    have hLHS_eq :
        (1 / h.C) * (‖p‖ ^ h.α / 2 ^ (h.β / (h.β + h.τ)))
          = ‖p‖ ^ h.α / (h.C * 2 ^ (h.β / (h.β + h.τ))) := by
      field_simp
    -- Rewrite the RHS:
    --  `(1/C) · (X + (m^β+1)) = (1/C)·X + (1/C)·(m^β+1)`,
    -- and `(1/C)·X = (1/C)·‖p‖^(α(1+τ/β))/(m^τ+1)`.
    have hRHS_eq :
        (1 / h.C) * (‖p‖ ^ (h.α * (1 + h.τ / h.β)) / (m ^ h.τ + 1)
                      + (m ^ h.β + 1))
          = (1 / h.C) * (1 / (m ^ h.τ + 1)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β))
            + (1 / h.C) * (m ^ h.β + 1) := by
      ring
    rw [hLHS_eq, hRHS_eq] at hyoung_scaled
    -- The congestion lower bound gives:
    --   `H ≥ (1/C)·(1/(m^τ+1))·‖p‖^(α(1+τ/β)) − C·(m^β+1)`.
    -- Rearrange to `(1/C)·(1/(m^τ+1))·‖p‖^(α(1+τ/β)) ≤ H + C·(m^β+1)`.
    have hlow' :
        (1 / h.C) * (1 / (m ^ h.τ + 1)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β))
          ≤ H x p m + h.C * (m ^ h.β + 1) := by
      linarith
    -- Combine with `hyoung_scaled` to get
    --   `‖p‖^α / (C · 2^(β/(β+τ))) ≤ (1/C)·(m^β+1) + H + C·(m^β+1)
    --                              = H + (C + 1/C)·(m^β+1)`.
    have hcombined :
        ‖p‖ ^ h.α / (h.C * 2 ^ (h.β / (h.β + h.τ)))
          ≤ H x p m + h.C * (m ^ h.β + 1) + (1 / h.C) * (m ^ h.β + 1) :=
      le_trans hyoung_scaled (by linarith)
    -- Now: `‖p‖^α / C' ≤ ‖p‖^α / (C · 2^(β/(β+τ)))`, since
    -- `C · 2^(β/(β+τ)) ≤ C'` and `‖p‖^α ≥ 0`.
    have hp_α_nonneg : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg hp_nonneg _
    have hCprod_pos : 0 < h.C * 2 ^ (h.β / (h.β + h.τ)) := mul_pos hC_pos h2pow_pos
    have hCprod_le_C' : h.C * 2 ^ (h.β / (h.β + h.τ)) ≤ C' := by
      have h2 : 0 ≤ 1 / h.C := by positivity
      linarith
    have hdiv_C' : ‖p‖ ^ h.α / C' ≤ ‖p‖ ^ h.α / (h.C * 2 ^ (h.β / (h.β + h.τ))) :=
      div_le_div_of_nonneg_left hp_α_nonneg hCprod_pos hCprod_le_C'
    -- And `(C + 1/C)·(m^β+1) ≤ C'·(m^β+1)`, since `C + 1/C ≤ C'`.
    have hC_inv_C : h.C + 1 / h.C ≤ C' := by
      have h1 : 0 ≤ h.C * 2 ^ (h.β / (h.β + h.τ)) - h.C := by
        have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
        linarith
      linarith
    have hmβ_nonneg : (0 : ℝ) ≤ m ^ h.β := Real.rpow_nonneg hm.le _
    have hmβ1_nonneg : (0 : ℝ) ≤ m ^ h.β + 1 := by linarith
    have hsumC : h.C * (m ^ h.β + 1) + (1 / h.C) * (m ^ h.β + 1)
                  ≤ C' * (m ^ h.β + 1) := by
      have hexpand : h.C * (m ^ h.β + 1) + (1 / h.C) * (m ^ h.β + 1)
          = (h.C + 1 / h.C) * (m ^ h.β + 1) := by ring
      rw [hexpand]
      exact mul_le_mul_of_nonneg_right hC_inv_C hmβ1_nonneg
    -- Conclude.
    have : ‖p‖ ^ h.α / C' - C' * (m ^ h.β + 1) ≤ H x p m := by linarith
    exact this

-- Sanity-check `noncomputable example` of `HypothesisWeakGrowth`
-- inhabitedness moved to after `HypothesisPowerGrowth.toMDpHat0` is
-- available (search for `simpleHypothesisWeakGrowth_example`).

/-!
### `(rem:hierarchy)` forward bridge — `HypothesisCongestionGrowth ⇒ HypothesisPowerGrowth`

Paper Remark `rem:hierarchy` (line 519) supplies the analytic
content for the implication `eq:assH.lower.congestion ⇒
eq:assH.lower.simple` (the Young-type inequality). The `upper`
field is identical in shape across all three bundles in the
hierarchy. However, the `DpH_upper` and `H_upper_pointwise` and
`lagr` fields of `HypothesisPowerGrowth` are **not derivable** from
`HypothesisCongestionGrowth` alone:

* The congestion `DpH_upper` bound contains `1/m` and `1/m^τ`
  terms that diverge as `m → 0⁺`, while the simple bound stays
  bounded. So for `τ > 0` the simple bound is genuinely stronger.
* The same `1/m` issue affects the FTC-derived `H_upper_pointwise`.
* The `lagr` field is derivable from convexity + `upper` via
  `Hamiltonian.lagrangian_lower_bound`, but the convexity-at-zero
  hypothesis is auxiliary content the paper deduces from the
  simple `D_pH`-bound (paper Remark `rmk:cxty`).

We therefore expose these three fields as **paper-honest riders**
in the signature of `HypothesisCongestionGrowth.toPowerGrowth`,
analogously to the `HypothesisHextJointCont` rider in T1's
restricted hemicontinuity drain (iter-0752). The `upper` field is
forwarded from `hcong.upper`; the `lower` field is forwarded from
`hcong.toWeakGrowth.lower`, which uses
`assumptions_young_congestion_to_weak`. The resulting `HypothesisPowerGrowth`
constants are inherited from `hcong.toWeakGrowth`.

This bridge is exactly what the paper invokes at line 1585
(`thm:apriori-congestion.growth` proof: "the use of
`eq:assH.lower.simple` is still valid since it is implied by
`eq:assH.lower.congestion`").
-/

/--
**Paper Remark `(rem:hierarchy)`, forward bridge from
`HypothesisCongestionGrowth` to `HypothesisPowerGrowth`**
(`Source/FGU-monotone_revised.tex`, line 519).

Given a congestion-growth bundle `hcong` and three paper-honest
riders supplying the `DpH_upper`, `H_upper_pointwise`, and `lagr`
fields at the same constants as `hcong.toWeakGrowth`, build the
simple power-growth bundle. The `upper` field is inherited from
`hcong`; the `lower` field is derived via the Young-type
inequality of `assumptions_young_congestion_to_weak` (already established in
`hcong.toWeakGrowth.lower`).

The choice of `C, α, β` for the produced `HypothesisPowerGrowth`
matches `hcong.toWeakGrowth.C, hcong.toWeakGrowth.α,
hcong.toWeakGrowth.β`. Riders must use these constants.
-/
noncomputable def HypothesisCongestionGrowth.toPowerGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : HypothesisCongestionGrowth (d := d) H DpH J)
    (hDpH_upper_rider :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ hcong.toWeakGrowth.C *
            (‖p‖ ^ (hcong.toWeakGrowth.α - 1)
              + m ^ (hcong.toWeakGrowth.β - hcong.toWeakGrowth.β / hcong.toWeakGrowth.α)
              + 1))
    (hH_upper_pt_rider :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ hcong.toWeakGrowth.C *
              (‖p‖ ^ hcong.toWeakGrowth.α + 1)
            - (m ^ hcong.toWeakGrowth.β) / hcong.toWeakGrowth.C)
    (hLagr_rider :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          (m ^ hcong.toWeakGrowth.β) / hcong.toWeakGrowth.C - hcong.toWeakGrowth.C
            ≤ (DpH x p m) ⬝ p - H x p m) :
    HypothesisPowerGrowth (d := d) H DpH := by
  -- All paper-derivable fields come through `hcong.toWeakGrowth`,
  -- which already established `upper` and `lower` at the weakened
  -- constant `C' = hcong.C · 2^(β/(β+τ)) + hcong.C + 1/hcong.C`.
  -- We reuse those, and the rider supplies the three missing
  -- power-bundle fields at the same `C', α, β`.
  set hweak : HypothesisWeakGrowth (d := d) H DpH := hcong.toWeakGrowth with hweak_def
  refine
    { periodic_H := hweak.periodic_H
      periodic_DpH := hweak.periodic_DpH
      measurable_H := hweak.measurable_H
      measurable_DpH := hweak.measurable_DpH
      continuous_H_pm := hweak.continuous_H_pm
      continuous_DpH_pm := hweak.continuous_DpH_pm
      C := hweak.C
      α := hweak.α
      β := hweak.β
      hC := hweak.hC
      hα := hweak.hα
      hβ := hweak.hβ
      upper := hweak.upper
      DpH_upper := hDpH_upper_rider
      lower := hweak.lower
      H_upper_pointwise := hH_upper_pt_rider
      lagr := hLagr_rider }

/-!
### `(rem:hierarchy)` lagr-rider derivation from `h_convex_at_zero`

The `hLagr_rider` field of `toPowerGrowth` is the only one of the three
A1a riders that is materially consumed by the downstream pipeline
(`Theorems.Congestion.Apriori.congestionRegularizedSequenceData_of_paperHypotheses`
reads `pack3.hPower.lagr`). The other two riders (`hDpH_upper_rider`,
`hH_upper_pt_rider`) are *structural* — required to inhabit
`HypothesisPowerGrowth` but never consumed in the kernel.

The paper (Remark `rmk:cxty`) deduces the Lagrangian lower bound from
the simple `D_pH` bound via convexity at zero. Lean-wise, the same
deduction is captured by `Hamiltonian.lagrangian_lower_bound` taking
`h_upper` and `h_convex_at_zero`. Here we package that derivation
specifically at the `hcong.toWeakGrowth.{C, β}` constants required by
the `toPowerGrowth` bridge: starting from `hcong.upper` (which is at
`hcong.{C, β}`), chain with `h_convex_at_zero` to obtain the bound at
`hcong.{C, β}`, then weaken to `hcong.toWeakGrowth.{C, β}` using
`hcong.C ≤ hcong.toWeakGrowth.C` (established inside `toWeakGrowth`).

Sub-step A1-cleanup step 1 (`infra-P7-sigfix-T2-A1-cleanup-step1-narrow-bundle`):
this helper lets the A1b producer
`congestionAprioriUpstreamPack_of_paperHypotheses` drop `hLagr_rider`
in favour of the more paper-honest `h_convex_at_zero` input.
-/

/-- **A1-cleanup step 1 helper**: derive the `hLagr_rider`-shaped
inequality at `hcong.toWeakGrowth.{C, β}` constants from `hcong.upper`
(the paper-honest upper bound at `m = 0`) and a paper-honest
convexity-at-zero rider `h_convex_at_zero` (paper Remark `rmk:cxty`).

This is the constant-weakened analogue of
`Hamiltonian.lagrangian_lower_bound` produced at the
`hcong.toWeakGrowth.{C, β}` constants required by
`HypothesisCongestionGrowth.toPowerGrowth`. -/
lemma HypothesisCongestionGrowth.lagr_rider_of_convex_at_zero
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : HypothesisCongestionGrowth (d := d) H DpH J)
    (h_convex_at_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (m ^ hcong.toWeakGrowth.β) / hcong.toWeakGrowth.C
          - hcong.toWeakGrowth.C
          ≤ (DpH x p m) ⬝ p - H x p m := by
  -- Constants from `hcong.toWeakGrowth`.
  have hC_pos : 0 < hcong.C := hcong.hC
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nonneg : 0 ≤ hcong.τ := hcong.hτ.1
  have hβτ_pos : 0 < hcong.β + hcong.τ := by linarith
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (hcong.β / (hcong.β + hcong.τ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (hcong.β / (hcong.β + hcong.τ)) := by
    have hexp_nonneg : (0 : ℝ) ≤ hcong.β / (hcong.β + hcong.τ) :=
      div_nonneg hβ_pos.le hβτ_pos.le
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp_nonneg
  -- `toWeakGrowth.C = hcong.C * 2^(β/(β+τ)) + hcong.C + 1/hcong.C` and
  -- `toWeakGrowth.β = hcong.β` (definitionally; see `toWeakGrowth` body).
  have hC'_eq :
      hcong.toWeakGrowth.C
        = hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ))
            + hcong.C + 1 / hcong.C := rfl
  have hβ'_eq : hcong.toWeakGrowth.β = hcong.β := rfl
  have hC'_pos : 0 < hcong.toWeakGrowth.C := by
    rw [hC'_eq]
    have h1 : 0 < hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) :=
      mul_pos hC_pos h2pow_pos
    have h2 : 0 < 1 / hcong.C := by positivity
    linarith
  have hC_le_C' : hcong.C ≤ hcong.toWeakGrowth.C := by
    rw [hC'_eq]
    have hpos1 : 0 ≤ hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) - hcong.C := by
      have : hcong.C ≤ hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) := by
        have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
        linarith
      linarith
    have hpos2 : 0 ≤ 1 / hcong.C := by positivity
    linarith
  -- Now derive the lagr inequality at `hcong.{C, β}` first, then weaken.
  filter_upwards [hcong.upper, h_convex_at_zero] with x hUp hCx p m hm
  -- Step 1: `H x p m - DpH·p ≤ H x 0 m ≤ -(m^β)/hcong.C + hcong.C`.
  have h1 : H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m := hCx p m hm
  have h2 : H x (0 : Fin d → ℝ) m ≤ -(m ^ hcong.β) / hcong.C + hcong.C := hUp m hm
  have h3 : H x p m - (DpH x p m) ⬝ p ≤ -(m ^ hcong.β) / hcong.C + hcong.C := h1.trans h2
  -- Rearrange: `(m^β)/hcong.C - hcong.C ≤ (DpH·p) - H x p m`.
  have h_lagr_at_hcong :
      (m ^ hcong.β) / hcong.C - hcong.C ≤ (DpH x p m) ⬝ p - H x p m := by
    have hneg : -(m ^ hcong.β) / hcong.C = -((m ^ hcong.β) / hcong.C) := by ring
    linarith
  -- Step 2: weaken from `hcong.{C, β}` to `toWeakGrowth.{C, β}`.
  -- `(m^β)/toWeakGrowth.C ≤ (m^β)/hcong.C` since `hcong.C ≤ toWeakGrowth.C` and `m^β ≥ 0`.
  -- `-toWeakGrowth.C ≤ -hcong.C` since `hcong.C ≤ toWeakGrowth.C`.
  have hmβ_nonneg : (0 : ℝ) ≤ m ^ hcong.β := Real.rpow_nonneg hm.le _
  have hdiv_le : (m ^ hcong.β) / hcong.toWeakGrowth.C ≤ (m ^ hcong.β) / hcong.C :=
    div_le_div_of_nonneg_left hmβ_nonneg hC_pos hC_le_C'
  have hC_le_C'_neg : -hcong.toWeakGrowth.C ≤ -hcong.C := by linarith
  -- Conclude.
  have hβ_subst : (m ^ hcong.toWeakGrowth.β) / hcong.toWeakGrowth.C
                    - hcong.toWeakGrowth.C
                  ≤ (m ^ hcong.β) / hcong.C - hcong.C := by
    rw [hβ'_eq]; linarith
  exact hβ_subst.trans h_lagr_at_hcong

/-!
### `(rem:hierarchy)` congestion-specific apriori bundle (T2 A1 cleanup step 3)

The `CongestionAprioriPowerData` structure bundles **only** the fields of
`HypothesisPowerGrowth` that the congestion apriori chain
(`Theorems.Congestion.Apriori.apriori_congestion_growth_int` and the
SimplePower `_int` helpers it calls) materially consumes:

* `{C, hC, α, hα, β, hβ}` — the simple-power-growth constants.
* `regH : RegularityH H DpH` — basic periodicity / measurability /
  joint continuity (consumed by Hölder / integrability infrastructure).
* `lower` — the simple lower bound on `H` (paper `eq:assH.lower.simple`);
  consumed by `apriori_Du_alpha_pointwise` (line 3135 of
  `SimplePower/Apriori.lean`) via `h.lower`.
* `lagr` — the Lagrangian lower bound (paper `eq:DpHdotpminusH-estimate1`,
  derived in §3 from convexity at zero of `p ↦ H(x, p, m)`); consumed
  by the regularised sequence layer `congestionRegularizedSequenceData_of_paperHypotheses`.

Crucially, this bundle does **not** carry `upper`, `DpH_upper`, or
`H_upper_pointwise`. The `upper` field at constants `(hcong.toWeakGrowth.{C, β})`
is paper-derivable from `hcong.upper` via the same constant-weakening
argument as `lagr_rider_of_convex_at_zero` (see proof of
`HypothesisCongestionGrowth.toCongestionAprioriPowerData` below). The
`DpH_upper` and `H_upper_pointwise` fields are **not** derivable from
`HypothesisCongestionGrowth` alone (per the doc above the
`toPowerGrowth` bridge); however, they are **never** materially consumed
by the apriori chain (verified by `grep h.DpH_upper` / `grep h.H_upper_pointwise`
in `SimplePower/Apriori.lean`, which returns only docstring matches).

This narrower bundle lets the A1b producer `congestionAprioriUpstreamPack_of_paperHypotheses`
drop the structural-only riders `hDpH_upper_rider` and `hH_upper_pt_rider`
that were required ONLY to inhabit those unused `HypothesisPowerGrowth`
fields.

**Note on the type narrowing scope.** The downstream
`CongestionAprioriUpstreamPack` and the Phase 3 producer
`congestionAprioriBounds_of_paperHypotheses` currently parameterise
their output records (`CongestionRegularizedSequenceData`,
`CongestionAprioriBoundData`) by `HypothesisPowerGrowth`. Threading
`CongestionAprioriPowerData` through all these downstream signatures
(plus refactoring the SimplePower `_int` helpers, which take
`HypothesisPowerGrowth` and are 5000+ LOC) is the full scope of T2 A1
cleanup step 3. This file ships the **definition + derivation +
adapter** scaffolding; the full cascade is split into a follow-up
task (see
`infra-P7-sigfix-T2-A1-cleanup-step3b-cascade-narrow-CAUP-type.md`). -/

/-- **Congestion apriori bundle** (T2 A1 cleanup step 3).

Carries the fields of `HypothesisPowerGrowth` that the congestion
apriori chain materially consumes. Omits `upper`, `DpH_upper`,
`H_upper_pointwise` (unused by the apriori chain). -/
structure CongestionAprioriPowerData
    {d : ℕ}
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  /-- The growth constant `C > 0`. -/
  C : ℝ
  /-- The momentum growth exponent `α > 1`. -/
  α : ℝ
  /-- The mass growth exponent `β > 0`. -/
  β : ℝ
  /-- Strict positivity of `C`. -/
  hC : 0 < C
  /-- Strict super-linearity of `α`. -/
  hα : 1 < α
  /-- Strict positivity of `β`. -/
  hβ : 0 < β
  /-- (eq:assH.lower.simple) `H(x, p, m) ≥ ‖p‖^α / C − C (m^β + 1)`. -/
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)
  /-- (paper Lagrangian lower bound)
  `D_pH(x, p, m) ⬝ p − H(x, p, m) ≥ m^β / C − C`. -/
  lagr :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (m ^ β) / C - C ≤ (DpH x p m) ⬝ p - H x p m

/-- **A1-cleanup step 3 producer** (paper Remark `rmk:cxty` + `rem:hierarchy`):
derive the congestion-specific apriori bundle from `hcong` plus the
paper-honest convexity-at-zero rider (Remark `rmk:cxty`).

* `C, α, β` are inherited from `hcong.toWeakGrowth`.
* `regH` (parent fields) inherited from `hcong.toRegularityH`.
* `lower` inherited from `hcong.toWeakGrowth.lower` (paper line 519, via
  `assumptions_young_congestion_to_weak`).
* `lagr` derived from `hcong + h_convex_at_zero` via
  `lagr_rider_of_convex_at_zero` (paper Remark `rmk:cxty`).

No `hDpH_upper_rider`, no `hH_upper_pt_rider` needed. -/
noncomputable def HypothesisCongestionGrowth.toCongestionAprioriPowerData
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : HypothesisCongestionGrowth (d := d) H DpH J)
    (h_convex_at_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m) :
    CongestionAprioriPowerData (d := d) H DpH := by
  set hweak : HypothesisWeakGrowth (d := d) H DpH := hcong.toWeakGrowth
  have hLagr := hcong.lagr_rider_of_convex_at_zero
                  (DpH := DpH) (J := J) h_convex_at_zero
  refine
    { periodic_H := hweak.periodic_H
      periodic_DpH := hweak.periodic_DpH
      measurable_H := hweak.measurable_H
      measurable_DpH := hweak.measurable_DpH
      continuous_H_pm := hweak.continuous_H_pm
      continuous_DpH_pm := hweak.continuous_DpH_pm
      C := hweak.C
      α := hweak.α
      β := hweak.β
      hC := hweak.hC
      hα := hweak.hα
      hβ := hweak.hβ
      lower := hweak.lower
      lagr := hLagr }

/-- **Forgetful projection** (T2 closure P1a): every full simple-power
bundle `HypothesisPowerGrowth` already carries all the data the congestion
apriori chain consumes, so it projects onto the narrow
`CongestionAprioriPowerData` by simply dropping the three simple-power
upper-bound fields (`upper`, `DpH_upper`, `H_upper_pointwise`).

This is the bridge that lets the SimplePower-side callers (which produce a
`HypothesisPowerGrowth`) feed the *narrowed* congestion-native apriori API
WITHOUT inflating the public surface: it forgets fields, never invents them,
so it takes **no rider witnesses**. It is the inverse direction of
`CongestionAprioriPowerData.toHypothesisPowerGrowth` (which, going the other
way, genuinely needs the three rider witnesses to re-inhabit the dropped
fields). -/
noncomputable def HypothesisPowerGrowth.toCongestionAprioriPowerData
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH) :
    CongestionAprioriPowerData (d := d) H DpH where
  periodic_H := h.periodic_H
  periodic_DpH := h.periodic_DpH
  measurable_H := h.measurable_H
  measurable_DpH := h.measurable_DpH
  continuous_H_pm := h.continuous_H_pm
  continuous_DpH_pm := h.continuous_DpH_pm
  C := h.C
  α := h.α
  β := h.β
  hC := h.hC
  hα := h.hα
  hβ := h.hβ
  lower := h.lower
  lagr := h.lagr

/-- The forgetful projection preserves the three growth constants
verbatim (definitional). This is the round-trip guarantee P1b relies on
when re-binding the `_int` apriori family to the narrow bundle: the
closed-form apriori constants (which depend only on `C, α, β`) are
unchanged by the projection, so callers cannot inflate constants. -/
@[simp] lemma HypothesisPowerGrowth.toCongestionAprioriPowerData_C
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH) :
    h.toCongestionAprioriPowerData.C = h.C := rfl

@[simp] lemma HypothesisPowerGrowth.toCongestionAprioriPowerData_alpha
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH) :
    h.toCongestionAprioriPowerData.α = h.α := rfl

@[simp] lemma HypothesisPowerGrowth.toCongestionAprioriPowerData_beta
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH) :
    h.toCongestionAprioriPowerData.β = h.β := rfl

/-- **Adapter** (T2 A1 cleanup step 3): build a full `HypothesisPowerGrowth`
from a `CongestionAprioriPowerData` plus three rider witnesses for the
fields `upper`, `DpH_upper`, `H_upper_pointwise`. The constants are
threaded verbatim from the input bundle.

This adapter is the bridge between the narrowed congestion-apriori
bundle and the existing SimplePower `_int` helpers (which require
`HypothesisPowerGrowth` for their signatures). It is the explicit
record of the structural obstruction noted in the
`toCongestionAprioriPowerData` doc: the 3 missing fields are
paper-explicit riders, not derivable from `hcong` alone, and the
adapter takes them as inputs. -/
noncomputable def CongestionAprioriPowerData.toHypothesisPowerGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hData : CongestionAprioriPowerData (d := d) H DpH)
    (hUpper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ hData.β) / hData.C + hData.C)
    (hDpHUpper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ hData.C *
            (‖p‖ ^ (hData.α - 1) + m ^ (hData.β - hData.β / hData.α) + 1))
    (hHUpperPt :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ hData.C * (‖p‖ ^ hData.α + 1) - (m ^ hData.β) / hData.C) :
    HypothesisPowerGrowth (d := d) H DpH where
  periodic_H := hData.periodic_H
  periodic_DpH := hData.periodic_DpH
  measurable_H := hData.measurable_H
  measurable_DpH := hData.measurable_DpH
  continuous_H_pm := hData.continuous_H_pm
  continuous_DpH_pm := hData.continuous_DpH_pm
  C := hData.C
  α := hData.α
  β := hData.β
  hC := hData.hC
  hα := hData.hα
  hβ := hData.hβ
  upper := hUpper
  DpH_upper := hDpHUpper
  lower := hData.lower
  H_upper_pointwise := hHUpperPt
  lagr := hData.lagr

/-!
## `(rmk:implied-a)` claim 1 — `(eq:assH.DpH.upper.simple) ⇒ (a:mDpHat0)`

The first claim of paper Remark `(rmk:implied-a)`
(`Source/FGU-monotone_revised.tex`, lines 495–502): under the simple
power-growth bundle `(onH.powergrowth)`, the explicit extension
`J(x, p, m) := m · D_pH(x, p, m)` (which equals `0` at `m = 0` thanks
to `0 • v = 0`) witnesses the `(a:mDpHat0)` extension hypothesis.

The argument has two non-trivial pieces:

* `tendsto_at_zero`: as `m → 0⁺`, `‖m · D_pH(x, p, m)‖`
  is bounded by `|m| · h.C · (‖p‖^{α-1} + m^{β-β/α} + 1)` (from the
  `DpH_upper` field), and the upper bound tends to `0` since
  `m · m^{β-β/α} = m^{1 + β - β/α}` has positive exponent.
* `continuous_J`: on `{m > 0}` the function `m · D_pH` is continuous in
  `(p, m)` thanks to `continuous_DpH_pm`. At points with `m = 0` we
  argue by the same bound: as `(p, m) → (p₀, 0)` with `m ≥ 0`, the
  value `m · D_pH(x, p, m)` is dominated by an expression that
  tends to `0`.
-/

/-- The explicit extension `J = m · D_pH` of `m · D_pH` to all of
`ℝ` (the value at `m = 0` is `0 • _ = 0`, i.e. the zero vector). This
is the witness of `(a:mDpHat0)` produced by paper Remark
`(rmk:implied-a)` from the simple `D_pH`-bound. -/
def JsimpleExt {d : ℕ}
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  m • DpH x p m

@[simp] lemma JsimpleExt_zero {d : ℕ}
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) :
    JsimpleExt DpH x p 0 = 0 := by
  unfold JsimpleExt; simp

/-- Auxiliary: for `m > 0`, the simple bound on `‖DpH‖` multiplied by
`m` gives `‖m • DpH(x, p, m)‖ ≤ h.C · m · (‖p‖^{α-1} + m^{β-β/α} + 1)`. -/
private lemma JsimpleExt_norm_le_of_pos {d : ℕ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C α β : ℝ}
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m)
    (hDpH : ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)) :
    ‖JsimpleExt DpH x p m‖
      ≤ m * (C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)) := by
  unfold JsimpleExt
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
  exact mul_le_mul_of_nonneg_left hDpH hm.le

/-- Auxiliary: the function
`g(p, m) = m · h.C · (‖p‖^{α-1} + m^{β-β/α} + 1)`
is continuous on `ℝ^d × ℝ` whenever `α > 1` and `β > 0`, and tends
to `0` at `(p₀, 0)`. We do not need full continuity — just continuity
at `m = 0`, which follows from continuity of `m`, `m^{β-β/α+1}`, and
`‖p‖^{α-1}` (with `α - 1 > 0` and `β - β/α ≥ 0`). -/
private lemma tendsto_dominator_zero
    {d : ℕ} {C α β : ℝ}
    (hα : 1 < α) (hβ : 0 < β)
    (p₀ : Fin d → ℝ) :
    Filter.Tendsto
      (fun pm : (Fin d → ℝ) × ℝ =>
        pm.2 * (C * (‖pm.1‖ ^ (α - 1) + pm.2 ^ (β - β / α) + 1)))
      (𝓝 (p₀, (0 : ℝ))) (𝓝 0) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα1_nonneg : 0 ≤ α - 1 := by linarith
  have hβα_nonneg : 0 ≤ β - β / α := by
    have hdiv_lt : β / α < β := by
      rw [div_lt_iff₀ hα_pos]; nlinarith
    linarith
  -- The factor `‖p‖^{α-1} + m^{β-β/α} + 1` is continuous everywhere
  -- (its three summands are continuous since the exponents are
  -- non-negative).
  have h_p_pow : Continuous
      (fun pm : (Fin d → ℝ) × ℝ => ‖pm.1‖ ^ (α - 1)) :=
    (Real.continuous_rpow_const hα1_nonneg).comp
      ((continuous_norm).comp continuous_fst)
  have h_m_pow : Continuous
      (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ (β - β / α)) :=
    (Real.continuous_rpow_const hβα_nonneg).comp continuous_snd
  have h_factor : Continuous
      (fun pm : (Fin d → ℝ) × ℝ =>
        C * (‖pm.1‖ ^ (α - 1) + pm.2 ^ (β - β / α) + 1)) :=
    continuous_const.mul ((h_p_pow.add h_m_pow).add continuous_const)
  -- And `m` is continuous, with value 0 at the target point.
  have h_m : Continuous (fun pm : (Fin d → ℝ) × ℝ => pm.2) := continuous_snd
  -- Product is continuous; its value at `(p₀, 0)` is `0`.
  have h_prod : Continuous
      (fun pm : (Fin d → ℝ) × ℝ =>
        pm.2 * (C * (‖pm.1‖ ^ (α - 1) + pm.2 ^ (β - β / α) + 1))) :=
    h_m.mul h_factor
  have h_at : (fun pm : (Fin d → ℝ) × ℝ =>
        pm.2 * (C * (‖pm.1‖ ^ (α - 1) + pm.2 ^ (β - β / α) + 1)))
        (p₀, (0 : ℝ)) = 0 := by simp
  have htend := h_prod.tendsto (p₀, (0 : ℝ))
  -- The limit value is `(p₀, 0).2 * ... = 0`. Rewrite via `h_at`.
  simpa [h_at] using htend

/--
**Paper Remark `(rmk:implied-a)`, claim 1**
(Ferreira–Gomes–Üçer, `Source/FGU-monotone_revised.tex`, lines 495–502).

Under `HypothesisPowerGrowth` (in particular the simple bound
`(eq:assH.DpH.upper.simple)`), the explicit extension `J = JsimpleExt DpH`
witnesses the `(a:mDpHat0)` extension hypothesis. Equivalently:
when the simple `D_pH`-bound holds, the function `m · D_pH(x, p, m)`
extends continuously across `m = 0` by setting `J(x, p, 0) = 0`. -/
theorem HypothesisPowerGrowth.toMDpHat0
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH) :
    HypothesismDpHat0 (d := d) DpH (JsimpleExt DpH) := by
  have hα := h.hα
  have hβ := h.hβ
  refine
    { J_of_pos := ?_
      tendsto_at_zero := ?_
      continuous_J := ?_
      measurable_J := ?_
      J_zero_at_zero := Filter.Eventually.of_forall fun _ _ => JsimpleExt_zero _ _ _ }
  · -- `J x p m = m • DpH x p m` by definition of `JsimpleExt`.
    intro x p m _
    rfl
  · -- For a.e. `x`, all `p`: `m • DpH x p m → 0` as `m → 0⁺`,
    -- by squeezing the norm against `m · h.C · (‖p‖^{α-1} + m^{β-β/α} + 1)`.
    filter_upwards [h.DpH_upper] with x hx p
    -- The target: `(fun m => m • DpH x p m) → JsimpleExt DpH x p 0 = 0`.
    rw [JsimpleExt_zero]
    -- Bound `‖m • DpH x p m‖` by the dominator on `{m > 0}`.
    refine squeeze_zero_norm' (a := fun m =>
      m * (h.C * (‖p‖ ^ (h.α - 1) + m ^ (h.β - h.β / h.α) + 1))) ?_ ?_
    · -- The bound holds eventually on `𝓝[>] 0`.
      filter_upwards [self_mem_nhdsWithin] with m hm
      -- here `hm : m ∈ {m | 0 < m}`.
      have hm_pos : 0 < m := hm
      have hbound := hx p m hm_pos
      exact JsimpleExt_norm_le_of_pos hm_pos hbound
    · -- The dominator → 0 as m → 0⁺. We use the joint-continuity
      -- result at `(p, 0)` and pass to the projection on `m`.
      have htend := tendsto_dominator_zero (d := d) (C := h.C)
        (α := h.α) (β := h.β) hα hβ p
      -- Convert `Tendsto` on the product space at `(p, 0)` to
      -- `Tendsto` on `m` at `0`, by composing with `m ↦ (p, m)`.
      have hcomp : Filter.Tendsto (fun m : ℝ => (p, m))
          (𝓝[>] 0) (𝓝 (p, (0 : ℝ))) := by
        refine Filter.Tendsto.prodMk_nhds tendsto_const_nhds ?_
        exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      exact htend.comp hcomp
  · -- For a.e. `x`: `(p, m) ↦ JsimpleExt DpH x p m` is continuous on
    -- `{(p, m) | 0 ≤ m}`. Two cases per point: `m > 0` (use
    -- `continuous_DpH_pm`) and `m = 0` (use the bound).
    filter_upwards [h.continuous_DpH_pm, h.DpH_upper] with x hxC hxB
    intro pm hpm
    -- `hpm : pm ∈ {pm | 0 ≤ pm.2}`, i.e. `0 ≤ pm.2`.
    have hpm2 : 0 ≤ pm.2 := hpm
    rcases lt_or_eq_of_le hpm2 with hpos | hzero
    · -- `0 < pm.2`. Then on a neighborhood of `pm` inside `{m ≥ 0}`,
      -- we are inside the open set `{m > 0}`, so use `hxC`.
      have hopen : {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} ∈ 𝓝 pm := by
        have : IsOpen {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} :=
          isOpen_lt continuous_const continuous_snd
        exact this.mem_nhds hpos
      -- Continuity at `pm` for the function `m • DpH`.
      -- On `{m > 0}` we have `m • DpH = JsimpleExt`.
      have hsmul_cont : ContinuousAt
          (fun pm : (Fin d → ℝ) × ℝ => pm.2 • DpH x pm.1 pm.2) pm := by
        have hcontDpH : ContinuousAt
            (fun pm : (Fin d → ℝ) × ℝ => DpH x pm.1 pm.2) pm := by
          have := hxC.continuousAt hopen
          -- `hxC` is continuous on `{m > 0}`; now we have `pm` in this open set.
          exact this
        have hcontm : ContinuousAt (fun pm : (Fin d → ℝ) × ℝ => pm.2) pm :=
          continuous_snd.continuousAt
        exact hcontm.smul hcontDpH
      -- `JsimpleExt = m • DpH` on the whole space, so this gives continuity
      -- at `pm`, hence within `{m ≥ 0}`.
      exact hsmul_cont.continuousWithinAt
    · -- `pm.2 = 0`. Show continuity within `{m ≥ 0}` at `pm = (pm.1, 0)`.
      -- Strategy: show the map tends to `0 = JsimpleExt DpH x pm.1 0`.
      have hpm_eq : pm = (pm.1, 0) := by
        ext
        · rfl
        · simpa using hzero.symm
      rw [hpm_eq]
      -- Goal: `ContinuousWithinAt (JsimpleExt DpH x · ·) {m ≥ 0} (pm.1, 0)`.
      -- Use that the value is `0` and bound the norm.
      rw [ContinuousWithinAt]
      simp only [JsimpleExt_zero]
      -- Need: `Tendsto (fun pm => JsimpleExt DpH x pm.1 pm.2)
      --                (𝓝[{m ≥ 0}] (pm.1, 0)) (𝓝 0)`.
      -- Bound the norm by the dominator `m · h.C · (...)`. On `{m ≥ 0}`:
      -- if `m > 0`, use the simple bound; if `m = 0`, the LHS is `0` and
      -- the RHS is `0`.
      refine squeeze_zero_norm' (a := fun pm : (Fin d → ℝ) × ℝ =>
        pm.2 * (h.C * (‖pm.1‖ ^ (h.α - 1) + pm.2 ^ (h.β - h.β / h.α) + 1))) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with q hq
        -- `hq : q ∈ {pm | 0 ≤ pm.2}`.
        have hq2 : 0 ≤ q.2 := hq
        rcases lt_or_eq_of_le hq2 with hq_pos | hq_zero
        · -- `q.2 > 0`: standard bound.
          have hbound := hxB q.1 q.2 hq_pos
          exact JsimpleExt_norm_le_of_pos hq_pos hbound
        · -- `q.2 = 0`: LHS = 0, RHS = 0.
          have hq2eq : q.2 = 0 := hq_zero.symm
          rw [hq2eq]
          simp [JsimpleExt]
      · -- Dominator tends to 0.
        have htend := tendsto_dominator_zero (d := d) (C := h.C)
          (α := h.α) (β := h.β) hα hβ pm.1
        exact htend.mono_left nhdsWithin_le_nhds
  · -- `measurable_J`: `JsimpleExt DpH x p m = m • DpH x p m` is measurable
    -- in `(x, p, m)`, from `h.measurable_DpH` and measurability of `m`.
    show Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        JsimpleExt DpH xpm.1 xpm.2.1 xpm.2.2)
    simp only [JsimpleExt]
    exact (measurable_snd.comp measurable_snd).smul h.measurable_DpH

/-- The choice `D_pH(x, p, m) = 2 • p` from the simple model
`HypothesisPowerGrowth` example produces, via
`HypothesisPowerGrowth.toMDpHat0`, a witness of `(a:mDpHat0)`. -/
noncomputable example (d : ℕ) :
    HypothesismDpHat0 (d := d)
      (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
      (JsimpleExt (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))) :=
  (simpleHypothesisPowerGrowth d).toMDpHat0

/-- Sanity check: the simple model Hamiltonian `H(x, p, m) = ‖p‖^2 − m`
together with `D_pH(x, p, m) = 2 • p` and the canonical extension
`J = JsimpleExt D_pH`, satisfies `HypothesisCongestionGrowth` via
`HypothesisPowerGrowth.toCongestionGrowth`. -/
noncomputable example (d : ℕ) :
    HypothesisCongestionGrowth (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ p _ => (2 : ℝ) • p)
      (JsimpleExt (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))) :=
  (simpleHypothesisPowerGrowth d).toCongestionGrowth
    (simpleHypothesisPowerGrowth d).toMDpHat0

/-- Sanity check: the simple model Hamiltonian `H(x, p, m) = ‖p‖^2 − m`
together with `D_pH(x, p, m) = 2 • p` satisfies
`HypothesisWeakGrowth`, via the chain `HypothesisPowerGrowth →
HypothesisCongestionGrowth → HypothesisWeakGrowth`. -/
noncomputable example (d : ℕ) :
    HypothesisWeakGrowth (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ p _ => (2 : ℝ) • p) :=
  ((simpleHypothesisPowerGrowth d).toCongestionGrowth
    (simpleHypothesisPowerGrowth d).toMDpHat0).toWeakGrowth

/-!
## `(rmk:implied-a)` claim 2 — extended bound on `m · D_pH`

Paper Remark `(rmk:implied-a)`, second claim
(`Source/FGU-monotone_revised.tex`, lines 495–509). Multiplying the
field `DpH_upper` of `HypothesisCongestionGrowth` by `m` and
simplifying the rpow arithmetic
`m · (1/m + 1/m^τ) = 1 + m^{1−τ}`,
`m · (m^{β−β/α} + 1/m) = m^{β+1−β/α} + 1`,
yields the bound

  `‖J(x, p, m)‖ ≤ C(1 + m^{1−τ}) ‖p‖^{α(1+τ/β)−1}`
  `             + C(m^{β+1−β/α} + 1)`

for every `m > 0`. The bound extends to `m = 0` by the joint continuity
hypothesis `mDpHat0.tendsto_at_zero`: the LHS is the limit of
`m · D_pH(x, p, m)` along `𝓝[>] 0`, and the RHS is right-continuous at
`0` since the exponents `1 − τ ≥ 0` and `β + 1 − β/α > 0` are
non-negative under the structure's hypotheses `τ ≤ 1`, `α > 1`, `β > 0`.
-/

/-- **Paper Remark `(rmk:implied-a)`, claim 2**
(Ferreira–Gomes–Üçer, `Source/FGU-monotone_revised.tex`, lines 495–509).

Under `HypothesisCongestionGrowth`, the bound on `D_pH` multiplied by
`m` extends the `D_pH` upper bound to a closed-half-line bound on the
extension `J = m · D_pH`:

  `‖J(x, p, m)‖ ≤ C (1 + m^{1−τ}) ‖p‖^{α(1+τ/β)−1}`
  `             + C (m^{β+1−β/α} + 1)`

valid for every `(p, m) ∈ ℝ^d × [0, ∞)` and almost every `x ∈ 𝕋^d`. -/
theorem HypothesisCongestionGrowth.mDpH_extended_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisCongestionGrowth (d := d) H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m →
        ‖J x p m‖
          ≤ h.C * (1 + m ^ (1 - h.τ)) * (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
            + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
  -- Useful sign / order facts on the exponents.
  have hC := h.hC
  have hα := h.hα
  have hβ := h.hβ
  have hτ := h.hτ
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα
  have hτ_nonneg : 0 ≤ h.τ := hτ.1
  have hτ_le_one : h.τ ≤ 1 := hτ.2
  have h_one_sub_τ_nonneg : 0 ≤ 1 - h.τ := by linarith
  have h_div_lt : h.β / h.α < h.β := by
    rw [div_lt_iff₀ hα_pos]; nlinarith
  have h_β_sub_div_nonneg : 0 ≤ h.β - h.β / h.α := by linarith
  have h_β1_sub_div_nonneg : 0 ≤ h.β + 1 - h.β / h.α := by linarith
  -- Pull the relevant a.e. hypotheses on `x`.
  filter_upwards [h.DpH_upper, h.mDpHat0.tendsto_at_zero] with x hxB hxT
  intro p m hm
  -- A reusable abbreviation for the RHS as a function of `m`.
  set R : ℝ → ℝ := fun m =>
        h.C * (1 + m ^ (1 - h.τ)) * (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
        + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) with hR_def
  -- Continuity of `R` (as a function of `m`) on all of `ℝ`, since both
  -- exponents `1 - τ ≥ 0` and `β + 1 - β/α ≥ 0` are non-negative.
  have hR_cont : Continuous R := by
    have h1 : Continuous (fun m : ℝ => m ^ (1 - h.τ)) :=
      Real.continuous_rpow_const h_one_sub_τ_nonneg
    have h2 : Continuous (fun m : ℝ => m ^ (h.β + 1 - h.β / h.α)) :=
      Real.continuous_rpow_const h_β1_sub_div_nonneg
    have hA : Continuous (fun m : ℝ =>
        h.C * (1 + m ^ (1 - h.τ)) *
          (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))) :=
      ((continuous_const.mul (continuous_const.add h1)).mul continuous_const)
    have hB : Continuous (fun m : ℝ =>
        h.C * (m ^ (h.β + 1 - h.β / h.α) + 1)) :=
      continuous_const.mul (h2.add continuous_const)
    exact hA.add hB
  -- Establish the bound first for `m > 0`, then extend to `m ≥ 0` by
  -- continuity / the limit hypothesis at `0`.
  -- Helper: bound for strictly positive `m`.
  have hbound_pos : ∀ m, 0 < m → ‖J x p m‖ ≤ R m := by
    intro m hmpos
    -- `J = m • DpH` for `m > 0`.
    have hJ_eq : J x p m = m • DpH x p m :=
      h.mDpHat0.J_of_pos x p m hmpos
    rw [hJ_eq]
    -- `‖m • DpH x p m‖ = m * ‖DpH x p m‖`.
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmpos]
    -- Multiply `DpH_upper` by `m ≥ 0`.
    have hDpH := hxB p m hmpos
    have hmle :
        m * ‖DpH x p m‖
          ≤ m * (h.C * ((1 / m) + (1 / m ^ h.τ)) *
                  (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
                + h.C * ((m ^ (h.β - h.β / h.α)) + 1 / m)) :=
      mul_le_mul_of_nonneg_left hDpH hmpos.le
    -- Now simplify the rpow arithmetic to recover `R m`.
    have hm_ne : m ≠ 0 := ne_of_gt hmpos
    have hmτ_pos : 0 < m ^ h.τ := Real.rpow_pos_of_pos hmpos _
    have hmβdiv_pos : 0 < m ^ (h.β - h.β / h.α) :=
      Real.rpow_pos_of_pos hmpos _
    -- `m * (1/m^τ) = m^{1-τ}`.
    have h_m_inv_τ : m * (1 / m ^ h.τ) = m ^ (1 - h.τ) := by
      have hmτ_ne : m ^ h.τ ≠ 0 := ne_of_gt hmτ_pos
      have : m ^ (1 - h.τ) = m ^ (1 : ℝ) / m ^ h.τ :=
        Real.rpow_sub hmpos 1 h.τ
      rw [this, Real.rpow_one]
      field_simp
    -- `m * m^{β-β/α} = m^{β+1-β/α}`.
    have h_m_β : m * m ^ (h.β - h.β / h.α) = m ^ (h.β + 1 - h.β / h.α) := by
      have : m * m ^ (h.β - h.β / h.α)
          = m ^ (1 : ℝ) * m ^ (h.β - h.β / h.α) := by
        rw [Real.rpow_one]
      rw [this, ← Real.rpow_add hmpos]
      ring_nf
    -- Combine: rewrite the dominator to match `R m`.
    have hrhs_eq :
        m * (h.C * ((1 / m) + (1 / m ^ h.τ)) *
                (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
              + h.C * ((m ^ (h.β - h.β / h.α)) + 1 / m))
          = R m := by
      have hm_inv : m * (1 / m) = 1 := by field_simp
      simp only [hR_def]
      have step1 :
          m * (h.C * (1 / m + 1 / m ^ h.τ) *
                ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
            = h.C * (m * (1 / m) + m * (1 / m ^ h.τ)) *
                ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1) := by ring
      have step2 :
          m * (h.C * (m ^ (h.β - h.β / h.α) + 1 / m))
            = h.C * (m * m ^ (h.β - h.β / h.α) + m * (1 / m)) := by ring
      have step1' :
          h.C * (m * (1 / m) + m * (1 / m ^ h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
            = h.C * (1 + m ^ (1 - h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1) := by
        rw [hm_inv, h_m_inv_τ]
      have step2' :
          h.C * (m * m ^ (h.β - h.β / h.α) + m * (1 / m))
            = h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
        rw [hm_inv, h_m_β]
      calc m * (h.C * ((1 / m) + (1 / m ^ h.τ)) *
                  (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
                + h.C * ((m ^ (h.β - h.β / h.α)) + 1 / m))
          = m * (h.C * (1 / m + 1 / m ^ h.τ) *
                  ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
              + m * (h.C * (m ^ (h.β - h.β / h.α) + 1 / m)) := by ring
        _ = h.C * (m * (1 / m) + m * (1 / m ^ h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
              + h.C * (m * m ^ (h.β - h.β / h.α) + m * (1 / m)) := by
              rw [step1, step2]
        _ = h.C * (1 + m ^ (1 - h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
              + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
              rw [step1', step2']
    linarith [hmle, hrhs_eq.le, hrhs_eq.ge]
  -- Now treat `m ≥ 0` by case analysis on `m = 0` vs `m > 0`.
  rcases lt_or_eq_of_le hm with hmpos | hmzero
  · exact hbound_pos m hmpos
  · -- `m = 0`: pass to the limit `m → 0⁺` of the bound for `m > 0`.
    subst hmzero
    -- `tendsto_at_zero` gives `m • DpH x p m → J x p 0` along `𝓝[>] 0`.
    have hLHS : Filter.Tendsto (fun m : ℝ => ‖m • DpH x p m‖)
        (𝓝[>] (0 : ℝ)) (𝓝 ‖J x p 0‖) :=
      (continuous_norm.continuousAt).tendsto.comp (hxT p)
    -- The RHS is continuous at `0`.
    have hRHS : Filter.Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) :=
      (hR_cont.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    -- The bound holds eventually on `𝓝[>] 0` via `hbound_pos`,
    -- with the LHS rewritten as `‖m • DpH x p m‖` using `J_of_pos`.
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
        ‖m • DpH x p m‖ ≤ R m := by
      filter_upwards [self_mem_nhdsWithin] with m hmpos
      have hmpos' : 0 < m := hmpos
      have hJeq : J x p m = m • DpH x p m :=
        h.mDpHat0.J_of_pos x p m hmpos'
      have := hbound_pos m hmpos'
      rwa [hJeq] at this
    -- Standard limit-of-inequality: limit of LHS ≤ limit of RHS.
    exact le_of_tendsto_of_tendsto hLHS hRHS hev

/-!
## `(rmk:implied-a)` claim 3 — H-bounds extend to `m = 0`

Paper Remark `(rmk:implied-a)`, third claim
(`Source/FGU-monotone_revised.tex`, lines 508–509). Under either
`HypothesisPowerGrowth` or `HypothesisCongestionGrowth` together with
`HypothesisHat0`, the upper and lower bounds on `H` extend to `m = 0`,
with the LHS interpreted via the extension `Hext H x p 0` from
`(a:Hat0)`. The RHS in each inequality is right-continuous in `m` at
`0`, so the bound passes through the limit `m → 0⁺` to give a closed
inequality in `WithTop ℝ`.
-/

/-- **Paper Remark `(rmk:implied-a)`, claim 3 — upper bound, power growth**.
Under `HypothesisPowerGrowth` and `HypothesisHat0`, the upper bound
`H(x, 0, m) ≤ C` (a weakening of the structural `H(x, 0, m) ≤
-m^β/C + C`, which holds for `m > 0`) extends to the boundary value
`Hext H x 0 0` in `WithTop ℝ`. -/
theorem HypothesisPowerGrowth.upper_extends_to_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : HypothesisHat0 (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (0 : Fin d → ℝ) 0 ≤ ((h.C : ℝ) : WithTop ℝ) := by
  have hC := h.hC
  have hβ := h.hβ
  filter_upwards [h.upper, hHat0.exists_limit_at_zero] with x hxU hxL
  -- Tendsto of `H x 0 m` (cast to `WithTop ℝ`) along `𝓝[>] 0` to `Hext H x 0 0`.
  have hLim := tendsto_Hext_zero_of_exists (hxL (0 : Fin d → ℝ))
  -- The constant function `C : WithTop ℝ` is its own limit.
  have hRHS : Filter.Tendsto (fun _ : ℝ => ((h.C : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h.C : ℝ) : WithTop ℝ)) := tendsto_const_nhds
  -- For every `m > 0`, `H x 0 m ≤ C`, hence the cast inequality holds.
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((H x (0 : Fin d → ℝ) m : ℝ) : WithTop ℝ) ≤ ((h.C : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hUbound := hxU m hmpos'
    -- `-(m^β)/C ≤ 0` since `m^β > 0` and `C > 0`.
    have hmβ_pos : 0 < m ^ h.β := Real.rpow_pos_of_pos hmpos' _
    have hdivnn : 0 ≤ (m ^ h.β) / h.C := div_nonneg hmβ_pos.le hC.le
    have hreal : H x (0 : Fin d → ℝ) m ≤ h.C := by
      have hub : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C := hUbound
      have hneg : -(m ^ h.β) / h.C ≤ 0 := by
        rw [neg_div]; linarith
      linarith
    -- Lift to `WithTop ℝ`.
    exact_mod_cast hreal
  exact le_of_tendsto_of_tendsto hLim hRHS hev

/-- **Paper Remark `(rmk:implied-a)`, claim 3 — lower bound, power growth**.
Under `HypothesisPowerGrowth` and `HypothesisHat0`, the lower bound
`H(x, p, m) ≥ ‖p‖^α/C - C(m^β + 1)` extends to `m = 0` with the LHS
interpreted via `Hext H x p 0` in `WithTop ℝ`; at `m = 0` the RHS
collapses to `‖p‖^α/C - C`. -/
theorem HypothesisPowerGrowth.lower_extends_to_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : HypothesisHat0 (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        ((‖p‖ ^ h.α / h.C - h.C : ℝ) : WithTop ℝ) ≤ Hext H x p 0 := by
  have hC := h.hC
  have hβ := h.hβ
  filter_upwards [h.lower, hHat0.exists_limit_at_zero] with x hxL hxLim
  intro p
  -- Tendsto of `H x p m` (cast to `WithTop ℝ`) along `𝓝[>] 0` to `Hext H x p 0`.
  have hLim := tendsto_Hext_zero_of_exists (hxLim p)
  -- Real-valued RHS as a function of `m`.
  set R : ℝ → ℝ := fun m => ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) with hR_def
  -- `R` is continuous on `ℝ` because `m ↦ m^β` is continuous (β > 0).
  have hR_cont : Continuous R := by
    have h1 : Continuous (fun m : ℝ => m ^ h.β) :=
      Real.continuous_rpow_const hβ.le
    have h2 : Continuous (fun m : ℝ => h.C * (m ^ h.β + 1)) :=
      continuous_const.mul (h1.add continuous_const)
    exact continuous_const.sub h2
  -- Tendsto of the cast of `R` to `WithTop ℝ`.
  have hRHS : Filter.Tendsto (fun m : ℝ => ((R m : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((R 0 : ℝ) : WithTop ℝ)) := by
    have : Filter.Tendsto (fun m : ℝ => ((R m : ℝ) : WithTop ℝ))
        (𝓝 (0 : ℝ)) (𝓝 ((R 0 : ℝ) : WithTop ℝ)) :=
      (WithTop.continuous_coe.comp hR_cont).continuousAt.tendsto
    exact this.mono_left nhdsWithin_le_nhds
  -- Identify `R 0` with the target real value.
  have hR0 : R 0 = ‖p‖ ^ h.α / h.C - h.C := by
    simp only [hR_def, Real.zero_rpow hβ.ne', zero_add, mul_one]
  -- For every `m > 0`, the lower bound gives `R m ≤ H x p m`.
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((R m : ℝ) : WithTop ℝ) ≤ ((H x p m : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hLB := hxL p m hmpos'
    -- `hLB : H x p m ≥ ‖p‖^α / C - C * (m^β + 1)`, i.e. `R m ≤ H x p m`.
    have hreal : R m ≤ H x p m := by
      simp only [hR_def]
      exact hLB
    exact_mod_cast hreal
  -- Apply: limit of LHS ≤ limit of RHS.
  have hgoal := le_of_tendsto_of_tendsto hRHS hLim hev
  -- Rewrite `R 0` to the explicit form.
  rw [hR0] at hgoal
  exact hgoal

/-- **Paper Remark `(rmk:implied-a)`, claim 3 — upper bound, congestion**.
Under `HypothesisCongestionGrowth` and `HypothesisHat0`, the upper bound
`H(x, 0, m) ≤ C` (a weakening of `H(x, 0, m) ≤ -m^β/C + C`, which holds
for `m > 0`) extends to the boundary value `Hext H x 0 0`. -/
theorem HypothesisCongestionGrowth.upper_extends_to_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisCongestionGrowth (d := d) H DpH J)
    (hHat0 : HypothesisHat0 (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (0 : Fin d → ℝ) 0 ≤ ((h.C : ℝ) : WithTop ℝ) := by
  have hC := h.hC
  have hβ := h.hβ
  filter_upwards [h.upper, hHat0.exists_limit_at_zero] with x hxU hxL
  have hLim := tendsto_Hext_zero_of_exists (hxL (0 : Fin d → ℝ))
  have hRHS : Filter.Tendsto (fun _ : ℝ => ((h.C : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h.C : ℝ) : WithTop ℝ)) := tendsto_const_nhds
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((H x (0 : Fin d → ℝ) m : ℝ) : WithTop ℝ) ≤ ((h.C : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hUbound := hxU m hmpos'
    have hmβ_pos : 0 < m ^ h.β := Real.rpow_pos_of_pos hmpos' _
    have hdivnn : 0 ≤ (m ^ h.β) / h.C := div_nonneg hmβ_pos.le hC.le
    have hreal : H x (0 : Fin d → ℝ) m ≤ h.C := by
      have hub : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C := hUbound
      have hneg : -(m ^ h.β) / h.C ≤ 0 := by
        rw [neg_div]; linarith
      linarith
    exact_mod_cast hreal
  exact le_of_tendsto_of_tendsto hLim hRHS hev

/-- **Paper Remark `(rmk:implied-a)`, claim 3 — lower bound, congestion**.
Under `HypothesisCongestionGrowth` and `HypothesisHat0`, the lower bound
`H(x, p, m) ≥ (1/C)(1/(m^τ + 1)) ‖p‖^{α(1+τ/β)} - C(m^β + 1)` extends to
`m = 0` with the LHS interpreted via `Hext H x p 0`. At `m = 0` the RHS
collapses to `(1/C)(1/(0^τ + 1)) ‖p‖^{α(1+τ/β)} - C` (where `0^τ = 0` if
`τ > 0` and `0^0 = 1` per Mathlib's `Real.rpow`). -/
theorem HypothesisCongestionGrowth.lower_extends_to_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisCongestionGrowth (d := d) H DpH J)
    (hHat0 : HypothesisHat0 (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        (((1 / h.C) * (1 / ((0 : ℝ) ^ h.τ + 1)) *
            (‖p‖ ^ (h.α * (1 + h.τ / h.β))) - h.C : ℝ) : WithTop ℝ)
          ≤ Hext H x p 0 := by
  have hC := h.hC
  have hα := h.hα
  have hβ := h.hβ
  have hτ := h.hτ
  have hτ_nonneg : 0 ≤ h.τ := hτ.1
  filter_upwards [h.lower, hHat0.exists_limit_at_zero] with x hxL hxLim
  intro p
  have hLim := tendsto_Hext_zero_of_exists (hxLim p)
  -- Real-valued RHS as a function of `m`.
  set R : ℝ → ℝ := fun m =>
        (1 / h.C) * (1 / (m ^ h.τ + 1)) *
          (‖p‖ ^ (h.α * (1 + h.τ / h.β))) - h.C * (m ^ h.β + 1) with hR_def
  -- Continuity of `R` on `ℝ`. The factor `1/(m^τ + 1)` is continuous
  -- because `m^τ + 1 ≥ 1 > 0` for `m ≥ 0`; we use the simpler fact that
  -- `m^τ` is continuous (since `τ ≥ 0`) and `m^τ + 1 ≠ 0` everywhere on ℝ.
  -- However, `m^τ` may take negative-base values; we only need continuity
  -- on a neighborhood of `0` from the right, where `m > 0`, but it's easier
  -- to prove `Tendsto R (𝓝[>] 0) (𝓝 (R 0))` directly.
  -- Build `Tendsto R (𝓝[>] 0) (𝓝 (R 0))` directly from continuity of `R` at `0`.
  have hR_tendsto : Filter.Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) := by
    have hτpos : ContinuousAt (fun m : ℝ => m ^ h.τ) 0 :=
      (Real.continuous_rpow_const hτ_nonneg).continuousAt
    have hβpos : ContinuousAt (fun m : ℝ => m ^ h.β) 0 :=
      (Real.continuous_rpow_const hβ.le).continuousAt
    -- Denominator `m^τ + 1` is positive at `0`.
    have h_denom_pos : 0 < (0 : ℝ) ^ h.τ + 1 := by
      have h0τ : 0 ≤ (0 : ℝ) ^ h.τ := Real.rpow_nonneg le_rfl _
      linarith
    have h_denom_cont : Continuous (fun m : ℝ => m ^ h.τ + 1) :=
      (Real.continuous_rpow_const hτ_nonneg).add continuous_const
    have h_inv_cont : ContinuousAt (fun m : ℝ => 1 / (m ^ h.τ + 1)) 0 := by
      refine ContinuousAt.div continuousAt_const h_denom_cont.continuousAt ?_
      exact ne_of_gt h_denom_pos
    have hR_contAt : ContinuousAt R 0 := by
      simp only [hR_def]
      have hA : ContinuousAt
          (fun m : ℝ => (1 / h.C) * (1 / (m ^ h.τ + 1)) *
            (‖p‖ ^ (h.α * (1 + h.τ / h.β)))) 0 :=
        ((continuousAt_const.mul h_inv_cont)).mul continuousAt_const
      have hB : ContinuousAt
          (fun m : ℝ => h.C * (m ^ h.β + 1)) 0 :=
        continuousAt_const.mul (hβpos.add continuousAt_const)
      exact hA.sub hB
    exact (hR_contAt.tendsto).mono_left nhdsWithin_le_nhds
  -- Tendsto of the cast of `R` to `WithTop ℝ`.
  have hRHS : Filter.Tendsto (fun m : ℝ => ((R m : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((R 0 : ℝ) : WithTop ℝ)) :=
    (WithTop.continuous_coe.continuousAt.tendsto).comp hR_tendsto
  -- Eventually for `m > 0`: `R m ≤ H x p m` (lifted to `WithTop ℝ`).
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((R m : ℝ) : WithTop ℝ) ≤ ((H x p m : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hLB := hxL p m hmpos'
    have hreal : R m ≤ H x p m := by
      simp only [hR_def]
      exact hLB
    exact_mod_cast hreal
  -- Identify `R 0` with the explicit form in the goal.
  have hR0 : R 0 = (1 / h.C) * (1 / ((0 : ℝ) ^ h.τ + 1)) *
        (‖p‖ ^ (h.α * (1 + h.τ / h.β))) - h.C := by
    simp only [hR_def, Real.zero_rpow hβ.ne', zero_add, mul_one]
  have hgoal := le_of_tendsto_of_tendsto hRHS hLim hev
  rw [hR0] at hgoal
  exact hgoal

/-!
## Bridge: `(a:Hat0)` → real-valued right-continuity at `m = 0`

The predicate `HypothesisHat0` provides convergence in `WithTop ℝ` to
the limit `Hext H x p 0`. Several downstream consumers (notably the
DCT-based pointwise tendsto inputs in
`StationaryMFG/Theorems/SimplePower/Banach/RegularizedSequence.lean`)
need real-valued right-continuity, i.e. a `Tendsto` against the **raw**
value `H x p 0` in `ℝ`. The two paper-faithful riders below close the
gap:

* `Hext_finite_at_zero H` — the limit is finite (not `+∞`). Paper
  hypotheses (e.g. continuity-based bounds in concrete models) often
  give this for free; in general it is a per-`(x, p)` finiteness
  condition implicit in the paper's `(a:Hat0)`.

* `H_zero_eq_Hext H` — the user-supplied raw value `H x p 0` agrees
  with the paper's extended `Hext H x p 0`. The paper writes
  `H(x, p, 0)` for the limit; this rider records that convention as
  a Lean-level identification on the raw `H`.

The closed-form lemma `H_rc0_of_hHat0` then gives the real-valued
right-continuity that `set_perturbation_pointwise_tendsto_H`
consumes.
-/

/-- Paper-faithful rider: for a.e. `x` and every `p`, the extended
Hamiltonian `Hext H x p 0` is a real number (not `+∞`). -/
def Hext_finite_at_zero
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
    Hext H x p 0 ≠ (⊤ : WithTop ℝ)

/-- Paper-faithful rider: for a.e. `x` and every `p`, the user's raw
`H x p 0` agrees with the paper's extended `Hext H x p 0`. The paper
writes `H(x, p, 0)` for the limit value; this records that convention
on the raw Lean function. -/
def H_zero_eq_Hext
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
    ((H x p 0 : ℝ) : WithTop ℝ) = Hext H x p 0

/-- Bundle of the two `m=0` boundary riders for `H`:
    `hHat0` (the right-limit at zero exists a.e.) and
    `hAgree` (the raw value `H x p 0` records that limit).
    Placed here to keep the Hamiltonian hypothesis hierarchy self-contained.
    Used in `CongestionRegularizedSequenceBuilderInputs.hH0` to thread
    both riders to the nonneg-delta HJB discharge path. -/
structure HypothesisHZeroExtension
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) : Prop where
  hHat0  : HypothesisHat0 (d := d) H
  hAgree : H_zero_eq_Hext (d := d) H

/-- Joint continuity of the extended Hamiltonian on the closed half-space
`{m ≥ 0}`, for almost every spatial point.

The hemicontinuity argument uses this property at the boundary `m = 0`.
It is derived from the other hypotheses of the public existence theorems:
* `HypothesisHextJointCont.of_powerGrowth` uses Lasry–Lions monotonicity,
  simple power growth, the right-hand limits, and boundary-value agreement;
* `HypothesisHextJointCont.of_convex` uses monotonicity, convexity of the
  positive-mass slices, and the finite boundary extension.

The predicate remains useful in internal lemmas, but is not an additional
assumption of Theorems 1 or 3. The derivations are in
`Hamiltonian/BoundaryContinuityPower.lean` and
`Hamiltonian/BoundaryContinuityConvex.lean`. -/
def HypothesisHextJointCont
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (UnitCube d)),
    ContinuousOn
      (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2)
      {pm | 0 ≤ pm.2}

/-- **Bridge `(a:Hat0)` → real-valued right-continuity at `0`.**

From the paper-level `HypothesisHat0` together with the two paper-
faithful riders `Hext_finite_at_zero` (the limit is finite) and
`H_zero_eq_Hext` (the raw `H x p 0` records the limit value), we
recover the right-hand limit in `ℝ`:

  for a.e. `x` and every `p`,
    `H(x, p, m) → H(x, p, 0)` as `m → 0⁺`.

This is exactly the shape required by `hH_rc0` in
`set_perturbation_pointwise_tendsto_H`. -/
theorem H_rc0_of_hHat0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
        (𝓝 (H x p 0)) := by
  filter_upwards [hHat0.exists_limit_at_zero, hFin, hAgree]
    with x hxL hxFin hxAgree p
  -- Step 1: from `hHat0`, get the `WithTop ℝ`-valued tendsto to
  -- `Hext H x p 0`.
  have hLim_top :
      Filter.Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (Hext H x p 0)) :=
    tendsto_Hext_zero_of_exists (hxL p)
  -- Step 2: lift `Hext H x p 0` to a real value via `untop`, using
  -- the finiteness rider.
  have hne : Hext H x p 0 ≠ (⊤ : WithTop ℝ) := hxFin p
  set r : ℝ := (Hext H x p 0).untop hne with hr_def
  have hcoe : ((r : ℝ) : WithTop ℝ) = Hext H x p 0 :=
    WithTop.coe_untop (Hext H x p 0) hne
  -- Step 3: pull tendsto back to `ℝ` via the embedding `(↑) : ℝ → WithTop ℝ`.
  have hLim_top' :
      Filter.Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((r : ℝ) : WithTop ℝ)) := by
    rw [hcoe]; exact hLim_top
  have hLim_real :
      Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ)) (𝓝 r) :=
    (WithTop.isEmbedding_coe (ι := ℝ)).tendsto_nhds_iff.mpr hLim_top'
  -- Step 4: identify `r = H x p 0` via the agreement rider.
  have hAgreeP : ((H x p 0 : ℝ) : WithTop ℝ) = Hext H x p 0 :=
    hxAgree p
  have hRcoe : ((r : ℝ) : WithTop ℝ) = ((H x p 0 : ℝ) : WithTop ℝ) := by
    rw [hcoe, hAgreeP]
  have hReq : r = H x p 0 := by exact_mod_cast hRcoe
  rw [← hReq]
  exact hLim_real

/-! ### Closed-form derivation of `Hext_finite_at_zero`

Per the Phase 8c investigation
(`infra-P5-theorem1-phase-8c-hHat0-paper-bundle`), the rider
`Hext_finite_at_zero` is **derivable** from `HypothesisHat0`
together with the power-growth upper bound `H_upper_pointwise` (paper
Lemma `lem:ADFGU`, `eq:boundsH`). The agreement rider
`H_zero_eq_Hext` is **not** derivable: the user-supplied raw value
`H x p 0` is unconstrained by the limit, so it remains as a
paper-convention rider on the headline corollary. -/

/-- **Closed-form `Hext_finite_at_zero` from `HypothesisPowerGrowth +
HypothesisHat0`** (Phase 8c).

The paper's upper bound `H(x, p, m) ≤ C(‖p‖^α + 1) − m^β/C` (the
`H_upper_pointwise` field of `HypothesisPowerGrowth`, paper Lemma
`lem:ADFGU`, `eq:boundsH`) sandwiches the right-hand limit at `m = 0⁺`
below the finite real number `C(‖p‖^α + 1)`, so the limit cannot be
`+∞`. Combined with `HypothesisHat0` (existence of the limit in
`WithTop ℝ`), this proves `Hext_finite_at_zero H`.

Pattern adapted from `HypothesisCongestionGrowth.upper_extends_to_zero`
(this file). -/
theorem Hext_finite_at_zero_of_powerGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : HypothesisHat0 (d := d) H) :
    Hext_finite_at_zero (d := d) H := by
  filter_upwards [hpow.H_upper_pointwise, hHat0.exists_limit_at_zero]
    with x hxU hxL p
  -- For each `p`, the `WithTop ℝ`-valued tendsto from `hHat0`.
  have hLim :
      Filter.Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (Hext H x p 0)) :=
    tendsto_Hext_zero_of_exists (hxL p)
  -- Constant upper bound `K := C(‖p‖^α + 1)` in `ℝ`, then in `WithTop ℝ`.
  set K : ℝ := hpow.C * (‖p‖ ^ hpow.α + 1) with hK_def
  have hRHS : Filter.Tendsto (fun _ : ℝ => ((K : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((K : ℝ) : WithTop ℝ)) := tendsto_const_nhds
  -- Eventual upper bound: for `m > 0`, `H x p m ≤ K - m^β/C ≤ K`.
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((H x p m : ℝ) : WithTop ℝ) ≤ ((K : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hUbound := hxU p m hmpos'
    -- `H x p m ≤ C(‖p‖^α + 1) − m^β/C ≤ K` since `m^β/C ≥ 0`.
    have hmβ_pos : 0 < m ^ hpow.β := Real.rpow_pos_of_pos hmpos' _
    have hdivnn : 0 ≤ (m ^ hpow.β) / hpow.C :=
      div_nonneg hmβ_pos.le hpow.hC.le
    have hreal : H x p m ≤ K := by
      simp only [hK_def]
      linarith
    exact_mod_cast hreal
  -- `Hext H x p 0 ≤ ((K : ℝ) : WithTop ℝ)` by limit of inequality.
  have hHextLe : Hext H x p 0 ≤ ((K : ℝ) : WithTop ℝ) :=
    le_of_tendsto_of_tendsto hLim hRHS hev
  -- Hence `Hext H x p 0 ≠ ⊤`, since it is bounded above by a finite real.
  intro htop
  rw [htop] at hHextLe
  -- `⊤ ≤ (K : WithTop ℝ)` would force `(K : WithTop ℝ) = ⊤`, but coercions
  -- of reals into `WithTop ℝ` are never `⊤`.
  have : (⊤ : WithTop ℝ) ≤ ((K : ℝ) : WithTop ℝ) := hHextLe
  have hKtop : ((K : ℝ) : WithTop ℝ) = (⊤ : WithTop ℝ) :=
    top_le_iff.mp this
  exact (WithTop.coe_ne_top : ((K : ℝ) : WithTop ℝ) ≠ ⊤) hKtop

/-- **Convenience corollary**: real-valued right-continuity at `0`
from `HypothesisPowerGrowth + HypothesisHat0 + H_zero_eq_Hext`,
dropping the explicit `Hext_finite_at_zero` rider (which is now
derived). This is the paper-faithful form for downstream
consumers that already carry `hpow`. -/
theorem H_rc0_of_hHat0_powerGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : HypothesisHat0 (d := d) H)
    (hAgree : H_zero_eq_Hext (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
        (𝓝 (H x p 0)) :=
  H_rc0_of_hHat0 hHat0
    (Hext_finite_at_zero_of_powerGrowth hpow hHat0) hAgree

end Hamiltonian
end StationaryMFG
