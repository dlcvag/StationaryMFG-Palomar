module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.Sobolev
public import StationaryMFG.Solutions.MFGOperator
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# The congestion domain `𝓚`

This module defines the convex set `𝓚` that serves as the domain of the
regularised MFG operator under congestion-growth Hamiltonians
(`Source/FGU-monotone_revised.tex` line 1329, eq. `def-domainK`):

```
𝓚 := { (μ, υ) ∈ L^{β̄}(𝕋^d) × W^{1,γ̄}(𝕋^d) :
        essinf μ > 0  and  |Dυ|^{α(1+τ/β)} / (μ^τ + 1) ∈ L^{β̄'}(𝕋^d) }.
```

Working in `𝓚` (rather than the larger `MFGDomain`) avoids singularities at
`μ = 0` since `essinf μ > 0` forces a strict positive lower bound a.e.

## Deliverables in this file

* `congestionDomainK` — the set, as a bare-pair `Set` in the project's
  bare-function discipline (CONVENTIONS §1b).
* `mem_congestionDomainK_iff` — definitional unfold.
* `congestionDomainK_subset_bar` — easy `⊆` direction of the closure
  identity (paper line 1334): every element of `𝓚` lies in the closure
  target `MFGDomain betaBar gammaBar`. The hard `⊇` direction
  (approximation by `μ_n = μ + 1/n`) is deferred to follow-up
  `infra-P5-domainK-closure` per CONVENTIONS §8.
* `congestionDomainK_nonempty` — non-vacuity via the constant pair
  `(μ ≡ 1/2, υ ≡ 0)`.

## Bare-pair caveat

The bare-pair `Set` does not carry a topology, so the literal Mathlib
`closure` operator is unavailable here. We record the easy direction of
the closure identity as a set inclusion `congestionDomainK ⊆ MFGDomain`
and document the deferred direction.

## Paper reference

`Source/FGU-monotone_revised.tex` §`sec:proof-congestion`, lines
1329–1336, equation `def-domainK`.
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Solutions.MFG
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Cube measure facts

Two structural facts about the cube-restricted Lebesgue measure used
throughout this file:

* It is finite (cube volume = 1).
* It is non-zero (cube volume = 1 ≠ 0), giving `NeZero` so that
  `essInf_const'` is available.
-/

private lemma isFiniteMeasure_cube :
    IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩

/-! ## The set `𝓚`

The congestion domain is parameterised by:

* extended exponents `betaBar, betaBarPrime, gammaBar : ℝ≥0∞`
  (in practice `betaBar` and `betaBarPrime` are Hölder conjugates;
  the present definition does not bake in that constraint, leaving it
  for downstream use sites);
* growth parameters `α β τ : ℝ` (positive, with `αt = α(1 + τ/β)` the
  exponent appearing in the paper's bound).

The integrability condition records an explicit weak-derivative witness
`Du` for the second component, since `MemSobolevPer` only asserts
existence of such a witness.
-/

/-- The congestion domain `𝓚` (paper eq. `def-domainK`, line 1329).

A pair `(μ, υ) : ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)` belongs to
`congestionDomainK` iff:

1. `μ ∈ L^{β̄}_per(𝕋^d)`;
2. `υ ∈ W^{1,γ̄}_per(𝕋^d)`;
3. there is a positive constant `c > 0` such that `c ≤ μ` a.e. on the
   unit cube — an equivalent formulation of `essInf μ > 0` (paper line
   1329) that bakes in the witness lower bound, avoiding the
   `IsBoundedUnder` hypothesis required by `MeasureTheory.ae_essInf_le`.
   The corresponding `essInf` inequality `0 < c ≤ essInf μ` then follows
   from `le_essInf_of_ae_le`.
4. there is an explicit weak-derivative witness `Du` for `υ` such that
   `|Dυ|^{α(1+τ/β)} / (μ^τ + 1) ∈ L^{β̄'}_per`.

The `α(1 + τ/β)` exponent is computed from the inputs `α β τ`. -/
def congestionDomainK
    (betaBar betaBarPrime gammaBar : ℝ≥0∞)
    (α β τ : ℝ) :
    Set (((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)) :=
  { p |
    MemLpPer betaBar p.1 ∧
      MemSobolevPer gammaBar p.2 ∧
      (∃ c : ℝ, 0 < c ∧
        (fun _ => c) ≤ᵐ[Measure.restrict volume (UnitCube d)] p.1) ∧
      ∃ Du : Fin d → (Fin d → ℝ) → ℝ,
        (∀ i, HasWeakDerivPer i p.2 (Du i)) ∧
          MemLpPer betaBarPrime
            (fun x =>
              (‖fun i => Du i x‖ ^ (α * (1 + τ / β))) /
                (p.1 x ^ τ + 1)) }

/-- Definitional unfold of `congestionDomainK`. -/
lemma mem_congestionDomainK_iff
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} {α β τ : ℝ}
    {p : ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)} :
    p ∈ congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ ↔
      MemLpPer betaBar p.1 ∧
        MemSobolevPer gammaBar p.2 ∧
        (∃ c : ℝ, 0 < c ∧
          (fun _ => c) ≤ᵐ[Measure.restrict volume (UnitCube d)] p.1) ∧
        ∃ Du : Fin d → (Fin d → ℝ) → ℝ,
          (∀ i, HasWeakDerivPer i p.2 (Du i)) ∧
            MemLpPer betaBarPrime
              (fun x =>
                (‖fun i => Du i x‖ ^ (α * (1 + τ / β))) /
                  (p.1 x ^ τ + 1)) := Iff.rfl

/-! ## Easy direction of the closure identity

`congestionDomainK ⊆ MFGDomain betaBar gammaBar`. The substantive content
is that `0 < essInf μ` implies `0 ≤ᵐ μ`. This is the easy `⊆` direction
of the closure identity in paper line 1334; the converse `⊇` direction
(density of `𝓚` in `MFGDomain`) is deferred to the follow-up task
`infra-P5-domainK-closure` because the bare-pair `Set` lacks a
topological closure operator.
-/

/-- Helper: an a.e. positive constant lower bound implies non-negativity
a.e. -/
private lemma ae_nonneg_of_ae_le_pos
    {f : (Fin d → ℝ) → ℝ} {c : ℝ} (hc : 0 < c)
    (hle : (fun _ => c) ≤ᵐ[Measure.restrict volume (UnitCube d)] f) :
    0 ≤ᵐ[Measure.restrict volume (UnitCube d)] f := by
  filter_upwards [hle] with x hx
  exact le_of_lt (lt_of_lt_of_le hc hx)

/-- **Easy direction of the closure identity** (paper line 1334,
sub-bullet `infra:P5-domainK-closure`).

Every pair in the congestion domain `𝓚` lies in `MFGDomain betaBar
gammaBar`, the closure target. -/
theorem congestionDomainK_subset_bar
    (betaBar betaBarPrime gammaBar : ℝ≥0∞) (α β τ : ℝ) :
    congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ
      ⊆ MFGDomain (d := d) betaBar gammaBar := by
  rintro ⟨μ, υ⟩ ⟨hμLp, hυSob, ⟨c, hc, hle⟩, _hwit⟩
  refine ⟨hμLp, hυSob, ?_⟩
  exact ae_nonneg_of_ae_le_pos hc hle

/-! ## Non-vacuity: the constant pair `(μ ≡ 1/2, υ ≡ 0) ∈ 𝓚` -/

/-- The constant zero function has zero as a weak partial derivative in
every coordinate direction. -/
private lemma hasWeakDerivPer_zero_zero (i : Fin d) :
    HasWeakDerivPer (d := d) i
      (fun _ : (Fin d → ℝ) => (0 : ℝ))
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      isFiniteMeasure_cube
    exact MemLp.toMemLpPer (memLp_const (0 : ℝ))
  · intro φ
    -- `(0) * φ = 0` and `0 * ∂_i φ = 0`, both integrals vanish.
    have h0a : (fun x : Fin d → ℝ =>
        (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
      funext x; ring
    have h0b : (fun x : Fin d → ℝ => (0 : ℝ) *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
      funext x; ring
    rw [h0a, h0b]
    simp [periodicIntegral_const]

/-- The constant zero function lies in `MemSobolevPer p` for any `p`. -/
private lemma memSobolevPer_zero (p : ℝ≥0∞) :
    MemSobolevPer (d := d) p (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      isFiniteMeasure_cube
    exact MemLp.toMemLpPer (memLp_const (0 : ℝ))
  · refine ⟨fun _ => (fun _ : (Fin d → ℝ) => (0 : ℝ)), ?_⟩
    intro i
    exact hasWeakDerivPer_zero_zero (d := d) i

/-- **Non-vacuity** (constant pair witness). The pair `(μ ≡ 1/2, υ ≡ 0)`
lies in `𝓚`. The constant `1/2` was chosen for the `essInf μ = 1/2 > 0`
unit test; any positive constant works. -/
theorem congestionDomainK_nonempty
    (betaBar betaBarPrime gammaBar : ℝ≥0∞) (α β τ : ℝ) :
    ((fun _ : (Fin d → ℝ) => ((1 : ℝ) / 2)),
        (fun _ : (Fin d → ℝ) => (0 : ℝ))) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    isFiniteMeasure_cube
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `MemLpPer betaBar (fun _ => 1/2)`
    exact MemLp.toMemLpPer (memLp_const ((1 : ℝ) / 2))
  · -- `MemSobolevPer gammaBar (fun _ => 0)`
    exact memSobolevPer_zero (d := d) gammaBar
  · -- Positivity witness `c = 1/2`: `(fun _ => 1/2) ≤ᵐ (fun _ => 1/2)`.
    refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
    exact Filter.Eventually.of_forall fun _ => le_refl _
  · -- Integrability witness: choose `Du = 0`. The ratio simplifies to a
    -- constant `c := 0 ^ (α(1+τ/β)) / ((1/2)^τ + 1)`, which is in `L^p` on
    -- the finite-measure cube for any `p` via `memLp_const`.
    refine ⟨fun _ => (fun _ : (Fin d → ℝ) => (0 : ℝ)), ?_, ?_⟩
    · intro i; exact hasWeakDerivPer_zero_zero (d := d) i
    · -- The ratio is a constant function of `x`. Reduce to a constant
      -- function via a pointwise identity.
      have hnorm_zero : (‖(fun _ : Fin d => (0 : ℝ))‖ : ℝ) = 0 := by
        have h0 : (fun _ : Fin d => (0 : ℝ)) = 0 := by funext _; rfl
        rw [h0]
        exact norm_zero
      have hconst :
          (fun x : Fin d → ℝ =>
              (‖fun _ : Fin d => (0 : ℝ)‖ ^ (α * (1 + τ / β))) /
                (((1 : ℝ) / 2) ^ τ + 1)) =
          (fun _ : Fin d → ℝ =>
              ((0 : ℝ) ^ (α * (1 + τ / β))) /
                (((1 : ℝ) / 2) ^ τ + 1)) := by
        funext x
        rw [hnorm_zero]
      rw [hconst]
      exact MemLp.toMemLpPer (memLp_const _)

/-! ## Density direction of the closure identity (paper line 1334)

The hard `⊇` direction of `closure 𝓚 = MFGDomain` (paper line 1334):
every `(μ, υ) ∈ MFGDomain` is the L^{β̄}-norm limit of a sequence in
`𝓚`, with the υ-component held fixed.

The witness sequence is `μ_n := μ + 1/(n+1)`, the standard
approximation. `μ_n` is bounded below by `1/(n+1) > 0`, so
`essinf μ_n > 0`; the integrability of `|Du|^{αt}/(μ_n^τ + 1)` is
inherited from the L^{β̄'}-integrability of `|Du|^{αt}` itself (the
denominator is ≥ 1 since `μ_n^τ ≥ 0`). The latter is supplied as a
hypothesis: in the paper's setting it follows from the congestion
exponent constraint `αt · β̄' ≤ γ̄` (eq. `eq:gamma.congestion`), but
we do **not** surface that as a free exponent inequality here per
CONVENTIONS §8 — instead we let downstream consumers discharge it
from their `HypothesisCongestionGrowth` bundle.

The L^{β̄} convergence `eLpNormPer betaBar (μ_n - μ) → 0` reduces to
the constant-function `L^p` norm `‖1/(n+1)‖ₑ * cube_volume^{1/p}`,
which tends to `0`.
-/

/-- Auxiliary: the L^{β̄}-seminorm of a constant function on the unit
cube equals the absolute value of the constant times `1^{1/p} = 1`.
This packages `MeasureTheory.eLpNorm_const` for the cube-restricted
measure. -/
private lemma eLpNormPer_const_unitCube
    {p : ℝ≥0∞} (hp : p ≠ 0) (c : ℝ) :
    eLpNormPer (d := d) p (fun _ : Fin d → ℝ => c) = ‖c‖ₑ := by
  unfold eLpNormPer
  have hμuniv :
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
          Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      volume_unitCube]
  have hμ_ne :
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) ≠ 0 := by
    intro h; rw [h] at hμuniv; simp at hμuniv
  rw [MeasureTheory.eLpNorm_const c hp hμ_ne, hμuniv, ENNReal.one_rpow,
    mul_one]

/-- For `p ≠ 0`, the L^{β̄}-seminorm of `μ_n - μ`, where
`μ_n := μ + 1/(n+1)` and `μ` is fixed, tends to `0` as `n → ∞`. The
difference is the constant function `1/(n+1)`, whose L^p-seminorm
on the cube (volume 1) equals `‖1/(n+1)‖ₑ → 0`. -/
private lemma tendsto_eLpNormPer_const_inv_succ
    {p : ℝ≥0∞} (hp : p ≠ 0) :
    Filter.Tendsto (fun n : ℕ =>
        eLpNormPer (d := d) p
          (fun _ : Fin d → ℝ => (1 : ℝ) / ((n : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by
  -- Reduce to `‖1/(n+1)‖ₑ → 0`.
  have hrewrite :
      ∀ n : ℕ, eLpNormPer (d := d) p
          (fun _ : Fin d → ℝ => (1 : ℝ) / ((n : ℝ) + 1))
        = ‖((1 : ℝ) / ((n : ℝ) + 1))‖ₑ := by
    intro n
    exact eLpNormPer_const_unitCube (d := d) hp _
  -- Tendsto in ℝ: `1/(n+1) → 0`.
  have htR : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- Continuity of `enorm` at `0`: `‖x‖ₑ → 0` as `x → 0` in ℝ.
  have hcont : Filter.Tendsto (fun x : ℝ => ‖x‖ₑ)
      (𝓝 0) (𝓝 0) := by
    have : Filter.Tendsto (fun x : ℝ => ‖x‖ₑ) (𝓝 (0 : ℝ)) (𝓝 ‖(0 : ℝ)‖ₑ) :=
      (continuous_enorm).tendsto _
    simpa using this
  have hcomp :
      Filter.Tendsto (fun n : ℕ => ‖((1 : ℝ) / ((n : ℝ) + 1))‖ₑ)
        Filter.atTop (𝓝 0) := hcont.comp htR
  -- Rewrite back.
  apply hcomp.congr'
  exact Filter.Eventually.of_forall fun n => (hrewrite n).symm

/-- Auxiliary: a positive constant `c > 0` is in `MemLpPer p` on the
unit cube, for any `p`. -/
private lemma memLpPer_const (p : ℝ≥0∞) (c : ℝ) :
    MemLpPer (d := d) p (fun _ : Fin d → ℝ => c) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    isFiniteMeasure_cube
  exact MemLp.toMemLpPer (memLp_const c)

/-- **Density direction of the closure identity** (paper line 1334,
sub-bullet `infra:P5-domainK-closure`).

For every `(μ, υ) ∈ MFGDomain betaBar gammaBar` equipped with an
explicit weak-derivative witness `Du` for `υ` whose `αt`-power is
`L^{β̄'}`-integrable, there exists a sequence `(μ_n)` of bare
functions such that for all `n`, the pair `(μ_n, υ)` lies in the
congestion domain `𝓚`, and `μ_n` converges to `μ` in `L^{β̄}_per`:
`eLpNormPer betaBar (μ_n − μ) → 0`.

The witness is `μ_n := μ + 1/(n+1)`. The integrability hypothesis
`MemLpPer betaBarPrime (fun x => ‖Du x‖^{αt})` is — in the paper's
setting — a consequence of the congestion-bundle exponent constraint
`αt · β̄' ≤ γ̄` (eq. `eq:gamma.congestion`). Per CONVENTIONS §8 we do
**not** surface that exponent inequality as a hypothesis here; instead
the integrability premise is exposed directly, and downstream
consumers discharge it from their bundle.

The hypothesis `hτ : 0 ≤ τ` ensures `μ_n^τ ≥ 0` so the denominator
`μ_n^τ + 1 ≥ 1`, making the ratio bounded pointwise by `|Du|^{αt}`.
-/
theorem congestionDomainK_dense_in_bar
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} (hbetaBar : betaBar ≠ 0)
    {α β τ : ℝ} (hτ : 0 ≤ τ)
    {μ υ : (Fin d → ℝ) → ℝ}
    (hpair : (μ, υ) ∈ MFGDomain (d := d) betaBar gammaBar)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hDu : ∀ i, HasWeakDerivPer i υ (Du i))
    (hDu_int :
      MemLpPer betaBarPrime
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ (α * (1 + τ / β)))) :
    ∃ μs : ℕ → (Fin d → ℝ) → ℝ,
      (∀ n,
          (μs n, υ) ∈
            congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ)
        ∧ Filter.Tendsto (fun n => eLpNormPer betaBar (μs n - μ))
            Filter.atTop (𝓝 0) := by
  -- Unpack the MFGDomain hypothesis: `μ` is in L^{β̄}_per, υ is W^{1,γ̄}_per,
  -- and `0 ≤ μ` a.e. on the unit cube.
  obtain ⟨hμLp, hυSob, hμ_nn⟩ := hpair
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    isFiniteMeasure_cube
  -- The approximating sequence `μ_n := μ + 1/(n+1)`.
  refine ⟨fun n x => μ x + 1 / ((n : ℝ) + 1), ?_, ?_⟩
  · -- Membership: `(μ_n, υ) ∈ 𝓚` for every `n`.
    intro n
    set cn : ℝ := (1 : ℝ) / ((n : ℝ) + 1) with hcn_def
    have hcn_pos : 0 < cn := by
      have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      simpa [hcn_def] using one_div_pos.mpr hn1_pos
    refine ⟨?_, hυSob, ?_, ?_⟩
    · -- `MemLpPer betaBar (μ + cn)`: closure of `MemLp` under addition.
      have h1 : MemLpPer (d := d) betaBar
          (fun _ : Fin d → ℝ => cn) := memLpPer_const (d := d) betaBar cn
      have hsum : MemLp (μ + fun _ : Fin d → ℝ => cn)
          betaBar (Measure.restrict volume (UnitCube d)) :=
        MemLp.add hμLp h1
      -- Pointwise the function `(μ + fun _ => cn)` equals `fun x => μ x + cn`.
      have hpointwise :
          (μ + fun _ : Fin d → ℝ => cn) =
            (fun x : Fin d → ℝ => μ x + cn) := by
        funext x; rfl
      rw [hpointwise] at hsum
      exact MemLp.toMemLpPer hsum
    · -- Positivity witness: `c = cn = 1/(n+1)` and `cn ≤ μ + cn` a.e.
      refine ⟨cn, hcn_pos, ?_⟩
      filter_upwards [hμ_nn] with x hx
      -- `cn ≤ μ x + cn` since `0 ≤ μ x`.
      have hx' : (0 : ℝ) ≤ μ x := hx
      linarith
    · -- Integrability witness: same `Du` works.
      -- The ratio `‖Du x‖^{αt} / ((μ x + cn)^τ + 1)` is dominated by
      -- `‖Du x‖^{αt}`, which is in L^{β̄'}_per.
      refine ⟨Du, hDu, ?_⟩
      set αt : ℝ := α * (1 + τ / β) with hαtdef
      -- Pointwise bound: `‖Du x‖^{αt} / ((μ x + cn)^τ + 1) ≤ ‖Du x‖^{αt}`.
      -- Use `MemLp.of_le_mul` with `c = 1`.
      have hμ_meas : AEStronglyMeasurable μ
          (Measure.restrict volume (UnitCube d)) := hμLp.aestronglyMeasurable
      have hDu_meas : AEStronglyMeasurable
          (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt)
          (Measure.restrict volume (UnitCube d)) :=
        hDu_int.aestronglyMeasurable
      -- AEStronglyMeasurable of `(μ + cn)^τ`.
      have hμcn_meas : AEStronglyMeasurable
          (fun x : Fin d → ℝ => μ x + cn)
          (Measure.restrict volume (UnitCube d)) :=
        hμ_meas.add aestronglyMeasurable_const
      have hμcn_τ_meas : AEStronglyMeasurable
          (fun x : Fin d → ℝ => (μ x + cn) ^ τ)
          (Measure.restrict volume (UnitCube d)) :=
        (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμcn_meas
      have hdenom_meas : AEStronglyMeasurable
          (fun x : Fin d → ℝ => (μ x + cn) ^ τ + 1)
          (Measure.restrict volume (UnitCube d)) :=
        hμcn_τ_meas.add aestronglyMeasurable_const
      have hratio_meas : AEStronglyMeasurable
          (fun x : Fin d → ℝ =>
            (‖fun i => Du i x‖ ^ αt) / ((μ x + cn) ^ τ + 1))
          (Measure.restrict volume (UnitCube d)) :=
        AEStronglyMeasurable.div₀ hDu_meas hdenom_meas
      apply MemLp.toMemLpPer
      apply MemLp.of_le_mul (c := 1) hDu_int.toMemLp hratio_meas
      -- Pointwise bound: `0 ≤ ‖Du x‖^{αt} ≤ 1 * ‖‖Du x‖^{αt}‖` and the
      -- ratio satisfies `ratio ≤ ‖Du x‖^{αt}` because `μ x + cn > 0`
      -- (via `hμ_nn` + `cn > 0`) and `τ ≥ 0`, hence
      -- `(μ x + cn)^τ + 1 ≥ 1`.
      filter_upwards [hμ_nn] with x hxμ
      -- `μ x ≥ 0`, so `μ x + cn ≥ cn > 0`, so `(μ x + cn)^τ ≥ 0`,
      -- so denominator ≥ 1.
      have hxμ' : (0 : ℝ) ≤ μ x := hxμ
      have hμcn_pos : 0 < μ x + cn := by linarith
      have hμcn_pow_nn : 0 ≤ (μ x + cn) ^ τ :=
        Real.rpow_nonneg hμcn_pos.le τ
      have hdenom_ge_one : (1 : ℝ) ≤ (μ x + cn) ^ τ + 1 := by linarith
      have hdenom_pos : (0 : ℝ) < (μ x + cn) ^ τ + 1 := by linarith
      have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
        Real.rpow_nonneg (norm_nonneg _) αt
      -- LHS = ratio = num/denom; bound by num.
      have hratio_le : (‖fun i => Du i x‖ ^ αt) / ((μ x + cn) ^ τ + 1)
          ≤ ‖fun i => Du i x‖ ^ αt := by
        rw [div_le_iff₀ hdenom_pos]
        nlinarith [hnum_nn, hdenom_ge_one]
      have hratio_nn : 0 ≤ (‖fun i => Du i x‖ ^ αt) / ((μ x + cn) ^ τ + 1) :=
        div_nonneg hnum_nn hdenom_pos.le
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnum_nn,
        abs_of_nonneg hratio_nn, one_mul]
      exact hratio_le
  · -- L^{β̄}-convergence: `μ_n - μ = fun _ => 1/(n+1)`.
    have hdiff :
        ∀ n : ℕ,
          (fun x => μ x + 1 / ((n : ℝ) + 1)) - μ
            = (fun _ : Fin d → ℝ => (1 : ℝ) / ((n : ℝ) + 1)) := by
      intro n; funext x
      simp only [Pi.sub_apply]
      ring
    have hsub :
        ∀ n : ℕ,
          eLpNormPer betaBar
              ((fun x => μ x + 1 / ((n : ℝ) + 1)) - μ)
            = eLpNormPer betaBar
                (fun _ : Fin d → ℝ => (1 : ℝ) / ((n : ℝ) + 1)) := by
      intro n; rw [hdiff n]
    -- Reduce the goal to the const-form tendsto.
    apply (tendsto_eLpNormPer_const_inv_succ (d := d) hbetaBar).congr'
    exact Filter.Eventually.of_forall fun n => (hsub n).symm

/-- **Closure equality** (paper line 1334, sub-bullet
`infra:P5-domainK-closure`).

Packages the easy `⊆` direction (`congestionDomainK_subset_bar`) with
the density direction (`congestionDomainK_dense_in_bar`) into a single
sequential-closure equality:

* every element of `𝓚` lies in `MFGDomain`;
* every `(μ, υ) ∈ MFGDomain` (equipped with an `L^{β̄'}`-integrable
  `αt`-power weak-derivative witness `Du` for `υ`) is the L^{β̄}-norm
  limit of a sequence in `𝓚` with υ-component held fixed.

The `L^{β̄'}`-integrability premise on the witness is the legitimate
content of the closure identity in the paper's setting, where it
follows from the congestion-bundle exponent constraint `αt · β̄' ≤ γ̄`
(eq. `eq:gamma.congestion`); per CONVENTIONS §8 we expose it directly
rather than via a free exponent inequality. -/
theorem congestionDomainK_closure_eq_bar
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} (hbetaBar : betaBar ≠ 0)
    {α β τ : ℝ} (hτ : 0 ≤ τ) :
    -- ⊆: 𝓚 ⊆ MFGDomain.
    (congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ
        ⊆ MFGDomain (d := d) betaBar gammaBar)
    ∧
    -- ⊇ (sequential density): every (μ, υ) ∈ MFGDomain with a witness
    -- |Du|^{αt} ∈ L^{β̄'}_per is approximated by a sequence in 𝓚.
    ∀ {μ υ : (Fin d → ℝ) → ℝ}
      (_ : (μ, υ) ∈ MFGDomain (d := d) betaBar gammaBar)
      (Du : Fin d → (Fin d → ℝ) → ℝ)
      (_ : ∀ i, HasWeakDerivPer i υ (Du i))
      (_ : MemLpPer betaBarPrime
            (fun x : Fin d → ℝ =>
              ‖fun i => Du i x‖ ^ (α * (1 + τ / β)))),
      ∃ μs : ℕ → (Fin d → ℝ) → ℝ,
        (∀ n,
            (μs n, υ) ∈
              congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ)
          ∧ Filter.Tendsto (fun n => eLpNormPer betaBar (μs n - μ))
              Filter.atTop (𝓝 0) := by
  refine ⟨congestionDomainK_subset_bar (d := d) betaBar betaBarPrime gammaBar α β τ, ?_⟩
  intro μ υ hpair Du hDu hDu_int
  exact congestionDomainK_dense_in_bar (d := d) hbetaBar hτ hpair Du hDu hDu_int

/-! ## Unit tests -/

/-- Non-vacuity unit test (paper line 1336 — `essinf μ > 0`): the constant
pair `(μ ≡ 1/2, υ ≡ 0)` lies in `𝓚`, with `essInf μ = 1/2 > 0`. -/
example :
    ((fun _ : (Fin 1 → ℝ) => ((1 : ℝ) / 2)),
        (fun _ : (Fin 1 → ℝ) => (0 : ℝ))) ∈
      congestionDomainK (d := 1) (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (1 : ℝ) (1 : ℝ) (1 : ℝ) :=
  congestionDomainK_nonempty (d := 1)
    (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 1 1

/-- The same constant pair lies in the closure target `MFGDomain`,
illustrating `congestionDomainK_subset_bar`. -/
example :
    ((fun _ : (Fin 1 → ℝ) => ((1 : ℝ) / 2)),
        (fun _ : (Fin 1 → ℝ) => (0 : ℝ))) ∈
      MFGDomain (d := 1) (2 : ℝ≥0∞) (2 : ℝ≥0∞) :=
  congestionDomainK_subset_bar (d := 1)
    (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 1 1
    (congestionDomainK_nonempty (d := 1)
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 1 1)

/-! ## Convexity of `𝓚` (paper line 1341, unlabeled lemma)

The convex-set property of `𝓚` is established in two steps:

* `congestionDomainK_of_essinf_ratio_pos` — auxiliary lemma (paper line
  1345): replacing `μ` by another `L^{β̄}_per` function `μ'` whose
  essinf-ratio with `μ` is positive preserves membership in `𝓚`.
* `congestionDomainK_convex` — the headline theorem. Uses the auxiliary
  lemma twice (combining the `μ`-component) and convexity of
  `r ↦ r^{αt}` (combining the `υ`-component).

The convexity argument requires `αt = α(1+τ/β) ≥ 1` (so that
`r ↦ r^{αt}` is convex on `[0,∞)`) and `τ ≥ 0` (so that the denominator
`μ^τ + 1 ≥ 1`).
-/

/-- **Auxiliary lemma** (paper line 1345). If `(μ, υ) ∈ 𝓚` and there
exists `c' > 0` with `c' · μ ≤ μ'` a.e. (formalising `essinf(μ'/μ) > 0`)
and `μ' ∈ L^{β̄}_per`, then `(μ', υ) ∈ 𝓚`.

The hypothesis `0 ≤ τ` ensures that `μ^τ` is monotone in `μ`, so the
new denominator `μ'^τ + 1` is bounded below by a positive multiple of
`μ^τ + 1`. -/
theorem congestionDomainK_of_essinf_ratio_pos
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} {α β τ : ℝ} (hτ : 0 ≤ τ)
    {μ υ μ' : (Fin d → ℝ) → ℝ}
    (hpair : (μ, υ) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ)
    (hμ' : MemLpPer betaBar μ')
    (c' : ℝ) (hc' : 0 < c')
    (hratio :
      (fun x => c' * μ x) ≤ᵐ[Measure.restrict volume (UnitCube d)] μ') :
    (μ', υ) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ := by
  obtain ⟨hμLp, hυSob, ⟨cμ, hcμ_pos, hμ_lower⟩, ⟨Du, hDu, hDu_int⟩⟩ := hpair
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    isFiniteMeasure_cube
  refine ⟨hμ', hυSob, ?_, ?_⟩
  · -- Positivity for `μ'`: choose `c_new := c' * cμ > 0`.
    refine ⟨c' * cμ, mul_pos hc' hcμ_pos, ?_⟩
    filter_upwards [hμ_lower, hratio] with x hμx hratiox
    -- `c' * cμ ≤ c' * μ x ≤ μ' x`.
    have h1 : c' * cμ ≤ c' * μ x :=
      mul_le_mul_of_nonneg_left hμx hc'.le
    exact h1.trans hratiox
  · -- Integrability of new ratio. Same `Du`. The new denominator is
    -- bounded below by `K * (μ^τ + 1)` for some `K > 0`, so the new
    -- ratio is bounded by `K⁻¹` times the old ratio.
    refine ⟨Du, hDu, ?_⟩
    set αt : ℝ := α * (1 + τ / β) with hαt_def
    -- Choose K := min(c'^τ, 1) ≥ 0, but we want a strictly positive K.
    set K : ℝ := min (c' ^ τ) 1 with hK_def
    have hK_pos : 0 < K := by
      have : 0 < c' ^ τ := Real.rpow_pos_of_pos hc' τ
      simp [hK_def, lt_min_iff, this]
    -- AEStronglyMeasurable of new ratio.
    have hμ'_meas : AEStronglyMeasurable μ'
        (Measure.restrict volume (UnitCube d)) := hμ'.aestronglyMeasurable
    have hμ_meas : AEStronglyMeasurable μ
        (Measure.restrict volume (UnitCube d)) :=
      hμLp.aestronglyMeasurable
    have hμτ_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => μ x ^ τ)
        (Measure.restrict volume (UnitCube d)) :=
      (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμ_meas
    have hdenom_old_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => μ x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      hμτ_meas.add aestronglyMeasurable_const
    -- Measurability of the numerator: numerator = (ratio) * (old denom) a.e.
    have hnum_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt)
        (Measure.restrict volume (UnitCube d)) := by
      have hprod : AEStronglyMeasurable
          (fun x => (‖fun i => Du i x‖ ^ αt / (μ x ^ τ + 1)) *
            (μ x ^ τ + 1))
          (Measure.restrict volume (UnitCube d)) :=
        hDu_int.aestronglyMeasurable.mul hdenom_old_meas
      apply hprod.congr
      filter_upwards [hμ_lower] with x hμx
      have hμx_nn : 0 ≤ μ x := hcμ_pos.le.trans hμx
      have : 0 < μ x ^ τ + 1 := by
        have := Real.rpow_nonneg hμx_nn τ; linarith
      field_simp
    have hμ'τ_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => μ' x ^ τ)
        (Measure.restrict volume (UnitCube d)) :=
      (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμ'_meas
    have hdenom_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => μ' x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      hμ'τ_meas.add aestronglyMeasurable_const
    have hratio_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          (‖fun i => Du i x‖ ^ αt) / (μ' x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) :=
      AEStronglyMeasurable.div₀ hnum_meas hdenom_meas
    -- Use MemLp.of_le_mul with c = K⁻¹, and the old ratio as `g`.
    apply MemLp.toMemLpPer
    apply MemLp.of_le_mul (c := K⁻¹) hDu_int.toMemLp hratio_meas
    -- Pointwise bound. For a.e. x:
    -- |‖Du‖^αt / (μ'^τ + 1)| ≤ K⁻¹ * |‖Du‖^αt / (μ^τ + 1)|.
    filter_upwards [hμ_lower, hratio] with x hμx hratiox
    -- μ x ≥ cμ > 0.
    have hμx_pos : 0 < μ x := lt_of_lt_of_le hcμ_pos hμx
    have hμx_nn : 0 ≤ μ x := hμx_pos.le
    -- μ' x ≥ c' * μ x > 0.
    have hcμx_le : c' * μ x ≤ μ' x := hratiox
    have hμ'x_pos : 0 < μ' x :=
      lt_of_lt_of_le (mul_pos hc' hμx_pos) hcμx_le
    have hμ'x_nn : 0 ≤ μ' x := hμ'x_pos.le
    -- (μ' x)^τ ≥ (c' * μ x)^τ = c'^τ * (μ x)^τ.
    have hcμx_nn : 0 ≤ c' * μ x := mul_nonneg hc'.le hμx_nn
    have h1 : (c' * μ x) ^ τ ≤ μ' x ^ τ :=
      Real.rpow_le_rpow hcμx_nn hcμx_le hτ
    have h2 : (c' * μ x) ^ τ = c' ^ τ * μ x ^ τ :=
      Real.mul_rpow hc'.le hμx_nn
    have h3 : c' ^ τ * μ x ^ τ ≤ μ' x ^ τ := by rw [← h2]; exact h1
    -- denom_new := μ'^τ + 1; denom_old := μ^τ + 1.
    -- We want: K * (μ^τ + 1) ≤ μ'^τ + 1, i.e. K * μ^τ + K ≤ μ'^τ + 1.
    have hμx_τ_nn : 0 ≤ μ x ^ τ := Real.rpow_nonneg hμx_nn τ
    have hμ'x_τ_nn : 0 ≤ μ' x ^ τ := Real.rpow_nonneg hμ'x_nn τ
    have hK_le_cτ : K ≤ c' ^ τ := min_le_left _ _
    have hK_le_one : K ≤ 1 := min_le_right _ _
    -- K * μ^τ ≤ c'^τ * μ^τ ≤ μ'^τ.
    have hKμτ_le : K * μ x ^ τ ≤ μ' x ^ τ :=
      le_trans (mul_le_mul_of_nonneg_right hK_le_cτ hμx_τ_nn) h3
    -- K * (μ^τ + 1) = K * μ^τ + K ≤ μ'^τ + 1.
    have hKsum_le : K * (μ x ^ τ + 1) ≤ μ' x ^ τ + 1 := by
      have : K * (μ x ^ τ + 1) = K * μ x ^ τ + K := by ring
      rw [this]
      linarith
    -- Pointwise bound on the new ratio in terms of the old.
    have hdenom_old_pos : 0 < μ x ^ τ + 1 := by linarith
    have hdenom_new_pos : 0 < μ' x ^ τ + 1 := by linarith
    have hdenom_new_pos' : 0 < K * (μ x ^ τ + 1) :=
      mul_pos hK_pos hdenom_old_pos
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) αt
    -- new_ratio ≤ num / (K * denom_old) = K⁻¹ * (num / denom_old).
    have hstep : (‖fun i => Du i x‖ ^ αt) / (μ' x ^ τ + 1) ≤
        (‖fun i => Du i x‖ ^ αt) / (K * (μ x ^ τ + 1)) := by
      apply div_le_div_of_nonneg_left hnum_nn hdenom_new_pos' hKsum_le
    have hstep' : (‖fun i => Du i x‖ ^ αt) / (K * (μ x ^ τ + 1)) =
        K⁻¹ * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)) := by
      field_simp
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    -- nonneg of ratios.
    have hratio_new_nn : 0 ≤
        (‖fun i => Du i x‖ ^ αt) / (μ' x ^ τ + 1) :=
      div_nonneg hnum_nn hdenom_new_pos.le
    have hratio_old_nn : 0 ≤
        (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) :=
      div_nonneg hnum_nn hdenom_old_pos.le
    rw [abs_of_nonneg hratio_new_nn, abs_of_nonneg hratio_old_nn]
    calc (‖fun i => Du i x‖ ^ αt) / (μ' x ^ τ + 1)
        ≤ (‖fun i => Du i x‖ ^ αt) / (K * (μ x ^ τ + 1)) := hstep
      _ = K⁻¹ * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)) := hstep'

/-! ### Convexity -/

/-- **Convexity of the congestion domain `𝓚`** (paper line 1341,
unlabeled lemma).

For `αt := α (1 + τ/β) ≥ 1`, `1 ≤ β̄`, `1 ≤ γ̄`, and `0 ≤ τ`, the
congestion domain `𝓚` is a convex subset of the bare-pair vector space
`((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)`.

The proof follows the paper: given `(μ_1, υ_1), (μ_2, υ_2) ∈ 𝓚` and a
convex combination `(a, b)` with `a + b = 1`, the `μ`-component
`a·μ_1 + b·μ_2` satisfies `essinf(·/μ_i) > 0` (witnessed by `a` or `b`
respectively, when positive), so the auxiliary lemma yields
`(a·μ_1 + b·μ_2, υ_1) ∈ 𝓚` and `(a·μ_1 + b·μ_2, υ_2) ∈ 𝓚`. The
`υ`-component combination then uses convexity of `r ↦ r^{αt}` to
dominate the new ratio by `a · ratio_1 + b · ratio_2`. -/
theorem congestionDomainK_convex
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    (hβ : 1 ≤ betaBar) (hγ : 1 ≤ gammaBar)
    {α β τ : ℝ} (hτ : 0 ≤ τ) (hαt : 1 ≤ α * (1 + τ / β)) :
    Convex ℝ
      (congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ) := by
  rw [convex_iff_add_mem]
  rintro ⟨μ₁, υ₁⟩ hp₁ ⟨μ₂, υ₂⟩ hp₂ a b ha hb hab
  -- Unpack.
  obtain ⟨hμ₁Lp, hυ₁Sob, ⟨c₁, hc₁_pos, hμ₁_lower⟩, ⟨Du₁, hDu₁, hDu₁_int⟩⟩ := hp₁
  obtain ⟨hμ₂Lp, hυ₂Sob, ⟨c₂, hc₂_pos, hμ₂_lower⟩, ⟨Du₂, hDu₂, hDu₂_int⟩⟩ := hp₂
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    isFiniteMeasure_cube
  set αt : ℝ := α * (1 + τ / β) with hαt_def
  -- The new μ and υ.
  set μ' : (Fin d → ℝ) → ℝ := a • μ₁ + b • μ₂ with hμ'_def
  set υ' : (Fin d → ℝ) → ℝ := a • υ₁ + b • υ₂ with hυ'_def
  -- Closure properties.
  have hμ'_Lp : MemLpPer betaBar μ' :=
    (hμ₁Lp.const_smul a).add (hμ₂Lp.const_smul b)
  have hυ'_Sob : MemSobolevPer gammaBar υ' :=
    memSobolevPer_add (d := d) hγ
      (memSobolevPer_const_smul (d := d) a ⟨hυ₁Sob.1, hυ₁Sob.2⟩)
      (memSobolevPer_const_smul (d := d) b ⟨hυ₂Sob.1, hυ₂Sob.2⟩)
  -- a.e. lower bound for μ'.
  have hμ'_lower :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        a * μ₁ x ≤ μ' x ∧ b * μ₂ x ≤ μ' x ∧
        a * c₁ + b * c₂ ≤ μ' x := by
    filter_upwards [hμ₁_lower, hμ₂_lower] with x hx₁ hx₂
    have hμ₁_nn : 0 ≤ μ₁ x := hc₁_pos.le.trans hx₁
    have hμ₂_nn : 0 ≤ μ₂ x := hc₂_pos.le.trans hx₂
    have hμ'_eq : μ' x = a * μ₁ x + b * μ₂ x := by
      simp [hμ'_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hμ'_eq]; nlinarith [mul_nonneg hb hμ₂_nn]
    · rw [hμ'_eq]; nlinarith [mul_nonneg ha hμ₁_nn]
    · rw [hμ'_eq]
      have ha₁ : a * c₁ ≤ a * μ₁ x := mul_le_mul_of_nonneg_left hx₁ ha
      have hb₂ : b * c₂ ≤ b * μ₂ x := mul_le_mul_of_nonneg_left hx₂ hb
      linarith
  -- Positivity constant for μ': c' := a c₁ + b c₂. This is > 0 since
  -- a + b = 1 and c₁, c₂ > 0, and a, b ≥ 0.
  have hc'_pos : 0 < a * c₁ + b * c₂ := by
    -- a + b = 1, so at least one of a, b > 0.
    rcases lt_or_eq_of_le ha with ha_pos | ha_zero
    · have : 0 < a * c₁ := mul_pos ha_pos hc₁_pos
      have : 0 ≤ b * c₂ := mul_nonneg hb hc₂_pos.le
      linarith
    · have ha_zero' : a = 0 := ha_zero.symm
      have hb_one : b = 1 := by linarith
      have : 0 < b * c₂ := by rw [hb_one]; simp [hc₂_pos]
      have : 0 ≤ a * c₁ := mul_nonneg ha hc₁_pos.le
      linarith
  -- Step 1: (μ', υ_1) ∈ 𝓚 and (μ', υ_2) ∈ 𝓚.
  -- Need: μ' ∈ L^β̄, and a positive constant c' s.t. c' * μ_1 ≤ μ'.
  -- Use c' = a if a > 0; otherwise a = 0 means μ' = b·μ₂ = μ₂ ≥ c₂.
  -- We handle both via a unified construction.
  -- For (μ', υ_1) we use c' = a and need a > 0; for (μ', υ_2) we use
  -- c' = b. If a or b is 0, the corresponding component drops out and
  -- we use the other directly.
  -- We split on whether a = 0 or b = 0.
  by_cases ha_zero : a = 0
  · -- a = 0, so b = 1, and μ' = μ₂, υ' = υ₂. Hence (μ', υ') = (μ₂, υ₂).
    have hb_one : b = 1 := by linarith
    have hμ'_eq : μ' = μ₂ := by
      ext x
      simp [hμ'_def, ha_zero, hb_one, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    have hυ'_eq : υ' = υ₂ := by
      ext x
      simp [hυ'_def, ha_zero, hb_one, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    change (a • (μ₁, υ₁) + b • (μ₂, υ₂)) ∈ _
    have hpair_eq : a • (μ₁, υ₁) + b • (μ₂, υ₂) = (μ', υ') := by
      ext <;> simp [hμ'_def, hυ'_def, Prod.smul_def]
    rw [hpair_eq, hμ'_eq, hυ'_eq]
    exact ⟨hμ₂Lp, hυ₂Sob, ⟨c₂, hc₂_pos, hμ₂_lower⟩,
      ⟨Du₂, hDu₂, hDu₂_int⟩⟩
  · -- a ≠ 0, so a > 0 (since a ≥ 0).
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
    by_cases hb_zero : b = 0
    · -- b = 0, so a = 1, and μ' = μ₁, υ' = υ₁.
      have ha_one : a = 1 := by linarith
      have hμ'_eq : μ' = μ₁ := by
        ext x
        simp [hμ'_def, hb_zero, ha_one, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
      have hυ'_eq : υ' = υ₁ := by
        ext x
        simp [hυ'_def, hb_zero, ha_one, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
      change (a • (μ₁, υ₁) + b • (μ₂, υ₂)) ∈ _
      have hpair_eq : a • (μ₁, υ₁) + b • (μ₂, υ₂) = (μ', υ') := by
        ext <;> simp [hμ'_def, hυ'_def, Prod.smul_def]
      rw [hpair_eq, hμ'_eq, hυ'_eq]
      exact ⟨hμ₁Lp, hυ₁Sob, ⟨c₁, hc₁_pos, hμ₁_lower⟩,
        ⟨Du₁, hDu₁, hDu₁_int⟩⟩
    · -- a > 0 and b > 0: the main case.
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb_zero)
      -- Get (μ', υ_1) ∈ 𝓚 via aux with c' = a.
      have hratio₁ :
          (fun x => a * μ₁ x) ≤ᵐ[Measure.restrict volume (UnitCube d)] μ' := by
        filter_upwards [hμ'_lower] with x hx
        exact hx.1
      have hpair₁ : (μ', υ₁) ∈
          congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ :=
        congestionDomainK_of_essinf_ratio_pos (d := d) hτ
          ⟨hμ₁Lp, hυ₁Sob, ⟨c₁, hc₁_pos, hμ₁_lower⟩,
            ⟨Du₁, hDu₁, hDu₁_int⟩⟩
          hμ'_Lp a ha_pos hratio₁
      -- Get (μ', υ_2) ∈ 𝓚 via aux with c' = b.
      have hratio₂ :
          (fun x => b * μ₂ x) ≤ᵐ[Measure.restrict volume (UnitCube d)] μ' := by
        filter_upwards [hμ'_lower] with x hx
        exact hx.2.1
      have hpair₂ : (μ', υ₂) ∈
          congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ :=
        congestionDomainK_of_essinf_ratio_pos (d := d) hτ
          ⟨hμ₂Lp, hυ₂Sob, ⟨c₂, hc₂_pos, hμ₂_lower⟩,
            ⟨Du₂, hDu₂, hDu₂_int⟩⟩
          hμ'_Lp b hb_pos hratio₂
      -- Unpack the integrability witnesses for `(μ', υ_1)` and
      -- `(μ', υ_2)` (these have the *new* denominator `μ'^τ + 1`).
      obtain ⟨_, _, ⟨c'₁, hc'₁_pos, _⟩, Du₁', hDu₁', hDu₁'_int⟩ := hpair₁
      obtain ⟨_, _, ⟨_, _, _⟩, Du₂', hDu₂', hDu₂'_int⟩ := hpair₂
      -- Now build the membership of (μ', υ').
      refine ⟨hμ'_Lp, hυ'_Sob, ?_, ?_⟩
      · -- positivity of μ': c' := a c₁ + b c₂ > 0.
        refine ⟨a * c₁ + b * c₂, hc'_pos, ?_⟩
        filter_upwards [hμ'_lower] with x hx
        exact hx.2.2
      · -- Integrability witness for (μ', υ').
        -- Witness derivative: a • Du₁ i + b • Du₂ i (still using the
        -- original Du₁ Du₂, since υ' = a υ₁ + b υ₂ has those as weak
        -- partial derivatives).
        refine ⟨fun i => a • Du₁ i + b • Du₂ i, ?_, ?_⟩
        · intro i
          -- Linearity of weak derivative.
          have hadd : HasWeakDerivPer i (a • υ₁ + b • υ₂)
              (a • Du₁ i + b • Du₂ i) := by
            have hL₁ : HasWeakDerivPer i (a • υ₁) (a • Du₁ i) :=
              hasWeakDerivPer_const_smul (d := d) i a (hDu₁ i)
            have hL₂ : HasWeakDerivPer i (b • υ₂) (b • Du₂ i) :=
              hasWeakDerivPer_const_smul (d := d) i b (hDu₂ i)
            -- L¹_per of `a • υ₁` and `b • υ₂` follow from
            -- MemSobolevPer => MemLpPer => MemLpPer 1.
            have hυ₁_smul_L1 : MemLpPer 1 (a • υ₁) :=
              memLpPer_one_of_mono (d := d) hγ (hυ₁Sob.1.const_smul a)
            have hυ₂_smul_L1 : MemLpPer 1 (b • υ₂) :=
              memLpPer_one_of_mono (d := d) hγ (hυ₂Sob.1.const_smul b)
            exact hasWeakDerivPer_add (d := d) i hυ₁_smul_L1 hυ₂_smul_L1
              hL₁ hL₂
          -- The `υ'` definition unfolds. Goal matches `hadd`.
          exact hadd
        · -- Show the new-ratio function is in `MemLpPer betaBarPrime`.
          -- Use convexity bound: `|a Du₁ + b Du₂|^αt ≤ a |Du₁|^αt + b |Du₂|^αt`,
          -- so the new ratio is bounded by `a * ratio_1 + b * ratio_2`.
          -- The `Du i'` witness in `hpair_i` is the *same* as `Du_i`
          -- because the auxiliary preserves the witness, but we don't
          -- need this fact: we redo the integrability directly.
          -- Goal: MemLpPer betaBarPrime
          --   (fun x => ‖a • Du₁ + b • Du₂‖ ^ αt / ((μ'(x))^τ + 1))
          set ratioNew : (Fin d → ℝ) → ℝ := fun x =>
            (‖fun i => (a • Du₁ i + b • Du₂ i) x‖ ^ αt) /
              (μ' x ^ τ + 1) with hratioNew_def
          -- Define the bounding function: a * ratio₁'(x) + b * ratio₂'(x),
          -- where ratio_i' uses the new denominator.
          set ratio₁' : (Fin d → ℝ) → ℝ := fun x =>
            (‖fun i => Du₁ i x‖ ^ αt) / (μ' x ^ τ + 1) with _h1
          set ratio₂' : (Fin d → ℝ) → ℝ := fun x =>
            (‖fun i => Du₂ i x‖ ^ αt) / (μ' x ^ τ + 1) with _h2
          -- Both ratio_i' are MemLpPer betaBarPrime by the aux lemma's
          -- output. We apply the aux lemma with `υ_i` as the υ-component
          -- to get `MemLpPer betaBarPrime` of the ratio with `Du₁` resp
          -- `Du₂`.
          -- Actually, we need to be careful: the witness in `hpair_i` is
          -- some `Du_i'`, which need NOT equal `Du_i`. But the aux lemma
          -- preserves the witness `Du`, so `Du_i' = Du_i` defeq:
          -- Helper: numerator `‖Du_j‖^αt` is AEStronglyMeasurable, derived
          -- from the membership of the ratio with old denominator.
          have hμ₁_meas : AEStronglyMeasurable μ₁
              (Measure.restrict volume (UnitCube d)) :=
            hμ₁Lp.aestronglyMeasurable
          have hμ₂_meas : AEStronglyMeasurable μ₂
              (Measure.restrict volume (UnitCube d)) :=
            hμ₂Lp.aestronglyMeasurable
          have hμ'_meas_global : AEStronglyMeasurable μ'
              (Measure.restrict volume (UnitCube d)) :=
            hμ'_Lp.aestronglyMeasurable
          have hμ₁τ_meas_g : AEStronglyMeasurable
              (fun x : Fin d → ℝ => μ₁ x ^ τ)
              (Measure.restrict volume (UnitCube d)) :=
            (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμ₁_meas
          have hμ₂τ_meas_g : AEStronglyMeasurable
              (fun x : Fin d → ℝ => μ₂ x ^ τ)
              (Measure.restrict volume (UnitCube d)) :=
            (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμ₂_meas
          have hdenom₁_meas : AEStronglyMeasurable
              (fun x : Fin d → ℝ => μ₁ x ^ τ + 1)
              (Measure.restrict volume (UnitCube d)) :=
            hμ₁τ_meas_g.add aestronglyMeasurable_const
          have hdenom₂_meas : AEStronglyMeasurable
              (fun x : Fin d → ℝ => μ₂ x ^ τ + 1)
              (Measure.restrict volume (UnitCube d)) :=
            hμ₂τ_meas_g.add aestronglyMeasurable_const
          have hμ'τ_meas_g : AEStronglyMeasurable
              (fun x : Fin d → ℝ => μ' x ^ τ)
              (Measure.restrict volume (UnitCube d)) :=
            (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμ'_meas_global
          have hdenom'_meas : AEStronglyMeasurable
              (fun x : Fin d → ℝ => μ' x ^ τ + 1)
              (Measure.restrict volume (UnitCube d)) :=
            hμ'τ_meas_g.add aestronglyMeasurable_const
          -- numerator of ratio_1: ratio_1 * denom_old_1 a.e. equals num.
          have hnum₁_meas : AEStronglyMeasurable
              (fun x : Fin d → ℝ => ‖fun i => Du₁ i x‖ ^ αt)
              (Measure.restrict volume (UnitCube d)) := by
            have hprod : AEStronglyMeasurable
                (fun x => (‖fun i => Du₁ i x‖ ^ αt / (μ₁ x ^ τ + 1)) *
                  (μ₁ x ^ τ + 1))
                (Measure.restrict volume (UnitCube d)) :=
              hDu₁_int.aestronglyMeasurable.mul hdenom₁_meas
            apply hprod.congr
            filter_upwards [hμ₁_lower] with x hμ₁x
            have hμ₁x_nn : 0 ≤ μ₁ x := hc₁_pos.le.trans hμ₁x
            have : 0 < μ₁ x ^ τ + 1 := by
              have := Real.rpow_nonneg hμ₁x_nn τ; linarith
            field_simp
          have hnum₂_meas : AEStronglyMeasurable
              (fun x : Fin d → ℝ => ‖fun i => Du₂ i x‖ ^ αt)
              (Measure.restrict volume (UnitCube d)) := by
            have hprod : AEStronglyMeasurable
                (fun x => (‖fun i => Du₂ i x‖ ^ αt / (μ₂ x ^ τ + 1)) *
                  (μ₂ x ^ τ + 1))
                (Measure.restrict volume (UnitCube d)) :=
              hDu₂_int.aestronglyMeasurable.mul hdenom₂_meas
            apply hprod.congr
            filter_upwards [hμ₂_lower] with x hμ₂x
            have hμ₂x_nn : 0 ≤ μ₂ x := hc₂_pos.le.trans hμ₂x
            have : 0 < μ₂ x ^ τ + 1 := by
              have := Real.rpow_nonneg hμ₂x_nn τ; linarith
            field_simp
          have hratio₁'_mem : MemLpPer betaBarPrime ratio₁' := by
            -- ratio₁' = num₁ / denom_new(μ').
            have hratio_meas : AEStronglyMeasurable ratio₁'
                (Measure.restrict volume (UnitCube d)) :=
              AEStronglyMeasurable.div₀ hnum₁_meas hdenom'_meas
            set K : ℝ := min (a ^ τ) 1 with hK_def
            have hK_pos : 0 < K := by
              have : 0 < a ^ τ := Real.rpow_pos_of_pos ha_pos τ
              simp [hK_def, this]
            apply MemLp.toMemLpPer
            apply MemLp.of_le_mul (c := K⁻¹) hDu₁_int.toMemLp hratio_meas
            filter_upwards [hμ₁_lower, hratio₁] with x hμ₁x hratiox
            have hμ₁x_pos : 0 < μ₁ x := lt_of_lt_of_le hc₁_pos hμ₁x
            have hμ₁x_nn : 0 ≤ μ₁ x := hμ₁x_pos.le
            have hμ'x_pos : 0 < μ' x :=
              lt_of_lt_of_le (mul_pos ha_pos hμ₁x_pos) hratiox
            have hμ'x_nn : 0 ≤ μ' x := hμ'x_pos.le
            have hcμx_nn : 0 ≤ a * μ₁ x := mul_nonneg ha hμ₁x_nn
            have h1 : (a * μ₁ x) ^ τ ≤ μ' x ^ τ :=
              Real.rpow_le_rpow hcμx_nn hratiox hτ
            have h2 : (a * μ₁ x) ^ τ = a ^ τ * μ₁ x ^ τ :=
              Real.mul_rpow ha hμ₁x_nn
            have h3 : a ^ τ * μ₁ x ^ τ ≤ μ' x ^ τ := by rw [← h2]; exact h1
            have hμ₁x_τ_nn : 0 ≤ μ₁ x ^ τ := Real.rpow_nonneg hμ₁x_nn τ
            have hμ'x_τ_nn : 0 ≤ μ' x ^ τ := Real.rpow_nonneg hμ'x_nn τ
            have hK_le_aτ : K ≤ a ^ τ := min_le_left _ _
            have hK_le_one : K ≤ 1 := min_le_right _ _
            have hKμτ_le : K * μ₁ x ^ τ ≤ μ' x ^ τ :=
              le_trans (mul_le_mul_of_nonneg_right hK_le_aτ hμ₁x_τ_nn) h3
            have hKsum_le : K * (μ₁ x ^ τ + 1) ≤ μ' x ^ τ + 1 := by
              have : K * (μ₁ x ^ τ + 1) = K * μ₁ x ^ τ + K := by ring
              rw [this]; linarith
            have hdenom_old_pos : 0 < μ₁ x ^ τ + 1 := by linarith
            have hdenom_new_pos : 0 < μ' x ^ τ + 1 := by linarith
            have hdenom_new_pos' : 0 < K * (μ₁ x ^ τ + 1) :=
              mul_pos hK_pos hdenom_old_pos
            have hnum_nn : 0 ≤ ‖fun i => Du₁ i x‖ ^ αt :=
              Real.rpow_nonneg (norm_nonneg _) αt
            have hstep : (‖fun i => Du₁ i x‖ ^ αt) / (μ' x ^ τ + 1) ≤
                (‖fun i => Du₁ i x‖ ^ αt) / (K * (μ₁ x ^ τ + 1)) := by
              apply div_le_div_of_nonneg_left hnum_nn hdenom_new_pos' hKsum_le
            have hstep' : (‖fun i => Du₁ i x‖ ^ αt) /
                  (K * (μ₁ x ^ τ + 1)) =
                K⁻¹ * ((‖fun i => Du₁ i x‖ ^ αt) / (μ₁ x ^ τ + 1)) := by
              field_simp
            change ‖ratio₁' x‖ ≤ K⁻¹ * ‖_‖
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
            have hratio_new_nn : 0 ≤ ratio₁' x :=
              div_nonneg hnum_nn hdenom_new_pos.le
            have hratio_old_nn : 0 ≤
                (‖fun i => Du₁ i x‖ ^ αt) / (μ₁ x ^ τ + 1) :=
              div_nonneg hnum_nn hdenom_old_pos.le
            rw [abs_of_nonneg hratio_new_nn, abs_of_nonneg hratio_old_nn]
            calc ratio₁' x = (‖fun i => Du₁ i x‖ ^ αt) / (μ' x ^ τ + 1) := rfl
              _ ≤ (‖fun i => Du₁ i x‖ ^ αt) / (K * (μ₁ x ^ τ + 1)) := hstep
              _ = K⁻¹ * ((‖fun i => Du₁ i x‖ ^ αt) / (μ₁ x ^ τ + 1)) :=
                  hstep'
          have hratio₂'_mem : MemLpPer betaBarPrime ratio₂' := by
            have hratio_meas : AEStronglyMeasurable ratio₂'
                (Measure.restrict volume (UnitCube d)) :=
              AEStronglyMeasurable.div₀ hnum₂_meas hdenom'_meas
            set K : ℝ := min (b ^ τ) 1 with hK_def
            have hK_pos : 0 < K := by
              have : 0 < b ^ τ := Real.rpow_pos_of_pos hb_pos τ
              simp [hK_def, lt_min_iff, this]
            apply MemLp.toMemLpPer
            apply MemLp.of_le_mul (c := K⁻¹) hDu₂_int.toMemLp hratio_meas
            filter_upwards [hμ₂_lower, hratio₂] with x hμ₂x hratiox
            have hμ₂x_pos : 0 < μ₂ x := lt_of_lt_of_le hc₂_pos hμ₂x
            have hμ₂x_nn : 0 ≤ μ₂ x := hμ₂x_pos.le
            have hμ'x_pos : 0 < μ' x :=
              lt_of_lt_of_le (mul_pos hb_pos hμ₂x_pos) hratiox
            have hμ'x_nn : 0 ≤ μ' x := hμ'x_pos.le
            have hcμx_nn : 0 ≤ b * μ₂ x := mul_nonneg hb hμ₂x_nn
            have h1 : (b * μ₂ x) ^ τ ≤ μ' x ^ τ :=
              Real.rpow_le_rpow hcμx_nn hratiox hτ
            have h2 : (b * μ₂ x) ^ τ = b ^ τ * μ₂ x ^ τ :=
              Real.mul_rpow hb hμ₂x_nn
            have h3 : b ^ τ * μ₂ x ^ τ ≤ μ' x ^ τ := by rw [← h2]; exact h1
            have hμ₂x_τ_nn : 0 ≤ μ₂ x ^ τ := Real.rpow_nonneg hμ₂x_nn τ
            have hμ'x_τ_nn : 0 ≤ μ' x ^ τ := Real.rpow_nonneg hμ'x_nn τ
            have hK_le_bτ : K ≤ b ^ τ := min_le_left _ _
            have hK_le_one : K ≤ 1 := min_le_right _ _
            have hKμτ_le : K * μ₂ x ^ τ ≤ μ' x ^ τ :=
              le_trans (mul_le_mul_of_nonneg_right hK_le_bτ hμ₂x_τ_nn) h3
            have hKsum_le : K * (μ₂ x ^ τ + 1) ≤ μ' x ^ τ + 1 := by
              have : K * (μ₂ x ^ τ + 1) = K * μ₂ x ^ τ + K := by ring
              rw [this]; linarith
            have hdenom_old_pos : 0 < μ₂ x ^ τ + 1 := by linarith
            have hdenom_new_pos : 0 < μ' x ^ τ + 1 := by linarith
            have hdenom_new_pos' : 0 < K * (μ₂ x ^ τ + 1) :=
              mul_pos hK_pos hdenom_old_pos
            have hnum_nn : 0 ≤ ‖fun i => Du₂ i x‖ ^ αt :=
              Real.rpow_nonneg (norm_nonneg _) αt
            have hstep : (‖fun i => Du₂ i x‖ ^ αt) / (μ' x ^ τ + 1) ≤
                (‖fun i => Du₂ i x‖ ^ αt) / (K * (μ₂ x ^ τ + 1)) := by
              apply div_le_div_of_nonneg_left hnum_nn hdenom_new_pos' hKsum_le
            have hstep' : (‖fun i => Du₂ i x‖ ^ αt) /
                  (K * (μ₂ x ^ τ + 1)) =
                K⁻¹ * ((‖fun i => Du₂ i x‖ ^ αt) / (μ₂ x ^ τ + 1)) := by
              field_simp
            change ‖ratio₂' x‖ ≤ K⁻¹ * ‖_‖
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
            have hratio_new_nn : 0 ≤ ratio₂' x :=
              div_nonneg hnum_nn hdenom_new_pos.le
            have hratio_old_nn : 0 ≤
                (‖fun i => Du₂ i x‖ ^ αt) / (μ₂ x ^ τ + 1) :=
              div_nonneg hnum_nn hdenom_old_pos.le
            rw [abs_of_nonneg hratio_new_nn, abs_of_nonneg hratio_old_nn]
            calc ratio₂' x = (‖fun i => Du₂ i x‖ ^ αt) / (μ' x ^ τ + 1) := rfl
              _ ≤ (‖fun i => Du₂ i x‖ ^ αt) / (K * (μ₂ x ^ τ + 1)) := hstep
              _ = K⁻¹ * ((‖fun i => Du₂ i x‖ ^ αt) / (μ₂ x ^ τ + 1)) :=
                  hstep'
          -- Now build the bound function.
          set bound : (Fin d → ℝ) → ℝ := fun x =>
            a * ratio₁' x + b * ratio₂' x with hbound_def
          have hbound_mem : MemLpPer betaBarPrime bound := by
            have h1 : MemLpPer betaBarPrime (a • ratio₁') :=
              hratio₁'_mem.const_smul a
            have h2 : MemLpPer betaBarPrime (b • ratio₂') :=
              hratio₂'_mem.const_smul b
            have hsum := h1.add h2
            -- Pointwise (a • ratio₁' + b • ratio₂') = bound.
            have heq : (a • ratio₁' + b • ratio₂') = bound := by
              funext x
              simp [hbound_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [← heq]
            exact MemLp.toMemLpPer hsum
          -- Pointwise bound: ratioNew ≤ bound a.e.
          have hratio_meas : AEStronglyMeasurable ratioNew
              (Measure.restrict volume (UnitCube d)) := by
            have hμ'_meas : AEStronglyMeasurable μ'
                (Measure.restrict volume (UnitCube d)) :=
              hμ'_Lp.aestronglyMeasurable
            have hμ'τ_meas : AEStronglyMeasurable
                (fun x : Fin d → ℝ => μ' x ^ τ)
                (Measure.restrict volume (UnitCube d)) :=
              (Real.continuous_rpow_const hτ).comp_aestronglyMeasurable hμ'_meas
            have hdenom_meas : AEStronglyMeasurable
                (fun x : Fin d → ℝ => μ' x ^ τ + 1)
                (Measure.restrict volume (UnitCube d)) :=
              hμ'τ_meas.add aestronglyMeasurable_const
            -- Numerator: ‖a • Du₁ + b • Du₂‖ is continuous in
            -- (Du₁ x, Du₂ x), so AEStronglyMeasurable. We measure
            -- against the L^β̄' integrability witness's measurability.
            -- Use HasWeakDerivPer's MemLpPer 1 of Du₁_i, Du₂_i:
            have hDu₁_meas : ∀ i, AEStronglyMeasurable (Du₁ i)
                (Measure.restrict volume (UnitCube d)) :=
              fun i => (hDu₁ i).memLpPer.aestronglyMeasurable
            have hDu₂_meas : ∀ i, AEStronglyMeasurable (Du₂ i)
                (Measure.restrict volume (UnitCube d)) :=
              fun i => (hDu₂ i).memLpPer.aestronglyMeasurable
            -- The function x ↦ ‖fun i => (a • Du₁ i + b • Du₂ i) x‖
            -- is AEStronglyMeasurable.
            have hcomb_meas : ∀ i, AEStronglyMeasurable
                (fun x => (a • Du₁ i + b • Du₂ i) x)
                (Measure.restrict volume (UnitCube d)) := by
              intro i
              have h1 : AEStronglyMeasurable (fun x => (a • Du₁ i) x)
                  (Measure.restrict volume (UnitCube d)) :=
                (hDu₁_meas i).const_smul a
              have h2 : AEStronglyMeasurable (fun x => (b • Du₂ i) x)
                  (Measure.restrict volume (UnitCube d)) :=
                (hDu₂_meas i).const_smul b
              exact h1.add h2
            -- For `Fin d → ℝ` (Polish/Borel/second-countable), AEStronglyMeasurable
            -- is equivalent to AEMeasurable. We build aemeasurability of the
            -- Pi-valued function via `aemeasurable_pi_iff` from each coordinate.
            have hvec_meas : AEStronglyMeasurable
                (fun x => fun i => (a • Du₁ i + b • Du₂ i) x)
                (Measure.restrict volume (UnitCube d)) := by
              rw [aestronglyMeasurable_iff_aemeasurable]
              exact AEMeasurable.of_eval fun i =>
                (hcomb_meas i).aemeasurable
            have hnorm_meas : AEStronglyMeasurable
                (fun x => ‖fun i => (a • Du₁ i + b • Du₂ i) x‖)
                (Measure.restrict volume (UnitCube d)) :=
              hvec_meas.norm
            have hαt_nn : (0 : ℝ) ≤ αt := le_trans zero_le_one hαt
            have hnum_meas : AEStronglyMeasurable
                (fun x => ‖fun i => (a • Du₁ i + b • Du₂ i) x‖ ^ αt)
                (Measure.restrict volume (UnitCube d)) :=
              (Real.continuous_rpow_const hαt_nn).comp_aestronglyMeasurable
                hnorm_meas
            exact AEStronglyMeasurable.div₀ hnum_meas hdenom_meas
          -- Pointwise: ratioNew x ≤ bound x.
          apply MemLp.toMemLpPer
          apply MemLp.of_le_mul (c := 1) hbound_mem.toMemLp hratio_meas
          -- Combine the closure facts pointwise.
          filter_upwards [hμ'_lower] with x hx
          -- Compute pointwise. Let v_j i := Du_j i x; use convexity
          -- of the αt-power.
          set V₁ : Fin d → ℝ := fun i => Du₁ i x
          set V₂ : Fin d → ℝ := fun i => Du₂ i x
          have hcomb_eq : (fun i => (a • Du₁ i + b • Du₂ i) x) =
              a • V₁ + b • V₂ := by
            funext i
            simp [V₁, V₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          -- Norm bound: ‖a V₁ + b V₂‖ ≤ a ‖V₁‖ + b ‖V₂‖.
          have hnorm_le : ‖a • V₁ + b • V₂‖ ≤ a * ‖V₁‖ + b * ‖V₂‖ := by
            have h1 : ‖(a : ℝ) • V₁‖ = a * ‖V₁‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
            have h2 : ‖(b : ℝ) • V₂‖ = b * ‖V₂‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
            calc ‖a • V₁ + b • V₂‖ ≤ ‖(a : ℝ) • V₁‖ + ‖(b : ℝ) • V₂‖ :=
                  norm_add_le _ _
              _ = a * ‖V₁‖ + b * ‖V₂‖ := by rw [h1, h2]
          have hV₁_nn : 0 ≤ ‖V₁‖ := norm_nonneg _
          have hV₂_nn : 0 ≤ ‖V₂‖ := norm_nonneg _
          have hcomb_nn : 0 ≤ a * ‖V₁‖ + b * ‖V₂‖ :=
            add_nonneg (mul_nonneg ha hV₁_nn) (mul_nonneg hb hV₂_nn)
          have hnorm_nn : 0 ≤ ‖a • V₁ + b • V₂‖ := norm_nonneg _
          -- Now apply convexity of r ↦ r^αt for αt ≥ 1: take r-power of both sides.
          have hpow_le_pow :
              ‖a • V₁ + b • V₂‖ ^ αt ≤ (a * ‖V₁‖ + b * ‖V₂‖) ^ αt :=
            Real.rpow_le_rpow hnorm_nn hnorm_le (le_trans zero_le_one hαt)
          -- Convexity bound: (a u + b v)^αt ≤ a u^αt + b v^αt for u,v ≥ 0
          -- and a + b = 1 with a, b ≥ 0, αt ≥ 1.
          have hconv :
              (a * ‖V₁‖ + b * ‖V₂‖) ^ αt ≤
                a * ‖V₁‖ ^ αt + b * ‖V₂‖ ^ αt := by
            -- Use Real.rpow_arith_mean_le_arith_mean_rpow with two-element sum.
            -- The 2-element form uses Finset.univ on Fin 2.
            -- A direct approach: invoke `convexOn_rpow hαt` and use ConvexOn.
            have hconvex : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun r => r ^ αt) :=
              convexOn_rpow hαt
            have hVm₁ : (‖V₁‖ : ℝ) ∈ Set.Ici (0 : ℝ) := hV₁_nn
            have hVm₂ : (‖V₂‖ : ℝ) ∈ Set.Ici (0 : ℝ) := hV₂_nn
            have := hconvex.2 hVm₁ hVm₂ ha hb hab
            -- this: (fun r => r^αt) (a • ‖V₁‖ + b • ‖V₂‖) ≤
            --   a • (‖V₁‖^αt) + b • (‖V₂‖^αt)
            simpa [smul_eq_mul] using this
          -- Combined: ‖V_combo‖^αt ≤ a ‖V₁‖^αt + b ‖V₂‖^αt.
          have hV_combo_le : ‖a • V₁ + b • V₂‖ ^ αt ≤
              a * ‖V₁‖ ^ αt + b * ‖V₂‖ ^ αt := le_trans hpow_le_pow hconv
          -- Denominator μ' x ^ τ + 1 > 0: compute.
          have hμx_nn : 0 ≤ μ' x := by
            have h := hx.2.2
            linarith
          have hμx_τ_nn : 0 ≤ μ' x ^ τ := Real.rpow_nonneg hμx_nn τ
          have hdenom_pos : 0 < μ' x ^ τ + 1 := by linarith
          -- Now divide both sides of `hV_combo_le` by `μ' x ^ τ + 1`.
          have hratio_div : (‖a • V₁ + b • V₂‖ ^ αt) / (μ' x ^ τ + 1) ≤
              (a * ‖V₁‖ ^ αt + b * ‖V₂‖ ^ αt) / (μ' x ^ τ + 1) :=
            div_le_div_of_nonneg_right hV_combo_le hdenom_pos.le
          have hsplit : (a * ‖V₁‖ ^ αt + b * ‖V₂‖ ^ αt) / (μ' x ^ τ + 1) =
              a * ratio₁' x + b * ratio₂' x := by
            simp only [ratio₁', ratio₂', V₁, V₂]
            field_simp
          change ‖ratioNew x‖ ≤ 1 * ‖bound x‖
          rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
          -- ratioNew x ≥ 0:
          have hratioNew_nn : 0 ≤ ratioNew x := by
            simp only [hratioNew_def]
            apply div_nonneg
            · exact Real.rpow_nonneg (norm_nonneg _) _
            · exact hdenom_pos.le
          have hratio₁'_nn : 0 ≤ ratio₁' x :=
            div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hdenom_pos.le
          have hratio₂'_nn : 0 ≤ ratio₂' x :=
            div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hdenom_pos.le
          have hbound_nn : 0 ≤ bound x := by
            simp only [hbound_def]
            exact add_nonneg (mul_nonneg ha hratio₁'_nn)
              (mul_nonneg hb hratio₂'_nn)
          rw [abs_of_nonneg hratioNew_nn, abs_of_nonneg hbound_nn]
          change ratioNew x ≤ bound x
          simp only [hratioNew_def, hbound_def, hcomb_eq]
          calc (‖a • V₁ + b • V₂‖ ^ αt) / (μ' x ^ τ + 1)
              ≤ (a * ‖V₁‖ ^ αt + b * ‖V₂‖ ^ αt) / (μ' x ^ τ + 1) := hratio_div
            _ = a * ratio₁' x + b * ratio₂' x := hsplit

/-! ### Unit test: midpoint of two explicit `𝓚`-elements lies in `𝓚` -/

/-- Unit test: the midpoint of two equal copies of the constant pair
`(μ ≡ 1/2, υ ≡ 0)` lies in `𝓚`, since `𝓚` is convex. -/
example :
    ((1 / 2 : ℝ) • (fun _ : (Fin 1 → ℝ) => ((1 : ℝ) / 2)) +
        (1 / 2 : ℝ) • (fun _ : (Fin 1 → ℝ) => ((1 : ℝ) / 2)),
      (1 / 2 : ℝ) • (fun _ : (Fin 1 → ℝ) => (0 : ℝ)) +
        (1 / 2 : ℝ) • (fun _ : (Fin 1 → ℝ) => (0 : ℝ))) ∈
      congestionDomainK (d := 1) (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
  have hconv : Convex ℝ (congestionDomainK (d := 1) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (2 : ℝ≥0∞) (1 : ℝ) (1 : ℝ) (1 : ℝ)) :=
    congestionDomainK_convex (d := 1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1 * (1 + 1 / 1))
  have hmem : ((fun _ : (Fin 1 → ℝ) => ((1 : ℝ) / 2)),
      (fun _ : (Fin 1 → ℝ) => (0 : ℝ))) ∈
        congestionDomainK (d := 1) (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          1 1 1 :=
    congestionDomainK_nonempty (d := 1)
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 1 1
  exact hconv hmem hmem (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

end Congestion

end StationaryMFG
