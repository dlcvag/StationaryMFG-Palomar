module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.Domain
public import StationaryMFG.Hamiltonian.Congestion
public import StationaryMFG.Periodic.LpInclusion

@[expose] public section

/-!
# `A_ε` is well-defined on the congestion domain `𝓚`
(`paper:lem:Aepsi.congestion.well-defined`, paper line 1352)

This module formalises paper Lemma `lem:Aepsi.congestion.well-defined`:
the regularised operator `A_ε` from `defAepsi` is a well-defined map
`𝓚 → L^{β̄'}_per × W^{-1,γ̄'}_per`. The pivotal fact (paper line 1357)
is the pointwise estimate

```
(1/μ + 1/μ^τ)·(μ^τ + 1) ≤ 3·(essinf μ)^{-1} + 3   a.e.
```

which, given `(μ, υ) ∈ 𝓚` (so `essinf μ > 0` and
`|Dυ|^{αt} / (μ^τ + 1) ∈ L^{β̄'}` with `αt := α(1+τ/β)`), upgrades the
ratio integrability to the full

```
(1/μ + 1/μ^τ)·(|Dυ|^{αt} + 1) ∈ L^{β̄'}.
```

Combined with the lower and upper bounds on `H` from
`Hamiltonian.upper_bound_congestiongrowth` and the lower
counterpart, this places `H(x, Dυ, μ) - V` in `L^{β̄'}`. The
flux side `μ · D_pH(x, Dυ, μ)` lands in `L^{γ̄'}` via
`mDpH_mem_Lp_gammaBar'_congestion` (`Hamiltonian/Congestion.lean`).

## Deliverables

* `aux_ratio_pointwise_bound` (private) — the load-bearing pointwise
  inequality of paper line 1357.
* `aEpsi_congestion_HJB_memLp` — AC1, the `MemLpPer β̄'` certificate
  for `x ↦ H(x, Du, m) - V(x)`, given a primal upper bound on `H` and
  the flux/lower hypotheses bundled.
* `aEpsi_congestion_flux_memLp` — AC2, the `MemLpPer γ̄'` certificate
  for `x ↦ m(x) · D_pH(x, Du, m)`.
* `aEpsi_eps_u_term_memLp` — AC3, the ε-Gateaux scalar term
  `x ↦ ε · |u|^{γ̄ - 2} · u ∈ L^{β̄'}` (via the embedding `γ̄' ↪ β̄'`).
* `aEpsi_eps_Du_term_memLp` — AC4, the ε-Gateaux vector term
  `x ↦ ε · |Du|^{γ̄ - 2} · Du_i ∈ L^{γ̄'}`.
* `aEpsi_congestion_well_defined` — AC5, the pair-functional packaging:
  given `MemLpPer`-certified summands, the value of the bare-pair
  integral is a well-defined real.

## Paper reference

`Source/FGU-monotone_revised.tex` §`sec:proof-congestion`, lines
1352–1360.
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## Public Carathéodory measurability helpers (child P3a7b3)

These expose the a.e.-strong measurability of the Carathéodory composition
`x ↦ H x (Du · x) (m x)` and of the assembled HJB summand
`x ↦ -(u x) - H x (Du · x) (m x) + V x`. They mirror the (formerly private)
`aestronglyMeasurable_comp_H` of `Existence.lean`, re-exported here in the
`WellDefined.lean` import root (reachable from `LimitPassage.lean`) so the
`hF_meas` side goal of `aEpsi_congestion_HJB_memLp` can be discharged
internally at the limit test pair. -/

/-- **Carathéodory composition helper.** The map
`x ↦ H x (fun i => Du i x) (m x)` is a.e.-strongly measurable whenever `H` is
jointly measurable (`hcong.measurable_H`) and `m`, `Du i` are
a.e.-strongly measurable. -/
theorem aestronglyMeasurable_comp_H
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => H xpm.1 xpm.2.1 xpm.2.2))
    {m : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hDu : ∀ i, AEStronglyMeasurable (Du i) (volume.restrict (UnitCube d))) :
    AEStronglyMeasurable
      (fun x => H x (fun i => Du i x) (m x)) (volume.restrict (UnitCube d)) := by
  have hid : AEMeasurable (fun x : Fin d → ℝ => x) (volume.restrict (UnitCube d)) :=
    aemeasurable_id
  have hDu' : AEMeasurable (fun x => (fun i => Du i x))
      (volume.restrict (UnitCube d)) := by
    rw [aemeasurable_pi_iff]
    intro i
    exact (aestronglyMeasurable_iff_aemeasurable.mp (hDu i))
  have hm' : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm
  have hprod : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i => Du i x), m x))
      (volume.restrict (UnitCube d)) :=
    hid.prodMk (hDu'.prodMk hm')
  have hcomp : AEMeasurable
      (fun x => H x (fun i => Du i x) (m x)) (volume.restrict (UnitCube d)) :=
    hH.comp_aemeasurable hprod
  exact aestronglyMeasurable_iff_aemeasurable.mpr hcomp

/-- **A.e.-strong measurability of the assembled HJB summand**
`x ↦ -(u x) - H x (fun i => Du i x) (m x) + V x`, the exact `hF_meas` shape
expected by `aEpsi_congestion_HJB_memLp`. Discharged from joint measurability
of `H` and a.e.-strong measurability of `u`, `m`, `Du i`, `V`. -/
theorem aestronglyMeasurable_HJBsummand
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => H xpm.1 xpm.2.1 xpm.2.2))
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hu : AEStronglyMeasurable u (volume.restrict (UnitCube d)))
    (hDu : ∀ i, AEStronglyMeasurable (Du i) (volume.restrict (UnitCube d))) :
    AEStronglyMeasurable
      (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x)
      (volume.restrict (UnitCube d)) :=
  ((hu.neg).sub (aestronglyMeasurable_comp_H hH hm hDu)).add hV

/-! ## The pivotal pointwise inequality (paper line 1357)

For `μ x ≥ c > 0` and `τ ∈ [0, 1]`,
`(1/μ x + 1/μ x^τ) · (μ x^τ + 1) ≤ 3 · c⁻¹ + 3`.

Expanding the product gives four summands
`μ^{τ-1} + 1/μ + 1 + 1/μ^τ`. Bounds for each (using `0 < c ≤ μ` and
`τ ∈ [0, 1]`):

* `μ^{τ-1} ≤ c^{τ-1} ≤ 1/c + 1`. (Power `τ - 1 ≤ 0` is non-increasing.)
* `1/μ ≤ 1/c`.
* `1 ≤ 1`.
* `1/μ^τ ≤ 1/c^τ ≤ 1/c + 1` (using `c ≤ μ` and `τ ≥ 0`, plus a
  case split on `c ≤ 1` vs `c > 1`).
-/

/-- **Pointwise core estimate of paper line 1357** (a relaxed form
sufficient for our purposes).

For `c ≤ μ x` with `0 < c` and `τ ∈ [0, 1]`:

```
(1/μ x + 1/μ x^τ) · (μ x^τ + 1) ≤ K(c)
```

for an explicit positive constant `K(c)` depending only on `c` (and
not on `μ x` or `τ`). The paper's `3·c⁻¹ + 3` is one specific
realization; here we use the slightly looser `(2/c + 2)·(2/c + 2)`
which simplifies the algebra.

Note: we use `μ ≥ c > 0` (hence `μ > 0`) and `τ ∈ [0, 1]`. -/
private lemma aux_ratio_pointwise_bound
    {μx c τ : ℝ} (hc : 0 < c) (hμ : c ≤ μx)
    (hτ_nn : 0 ≤ τ) (hτ_le : τ ≤ 1) :
    (1 / μx + 1 / μx ^ τ) * (μx ^ τ + 1)
      ≤ (2 / c + 2) * (2 / c + 2) := by
  have hμx_pos : 0 < μx := lt_of_lt_of_le hc hμ
  have hμx_nn : 0 ≤ μx := hμx_pos.le
  have hμxτ_pos : 0 < μx ^ τ := Real.rpow_pos_of_pos hμx_pos τ
  have hμxτ_nn : 0 ≤ μx ^ τ := hμxτ_pos.le
  -- Bound each factor.
  -- Factor 1: `1/μ + 1/μ^τ ≤ 1/c + 1/c^τ ≤ 2/c + 2`.
  -- (since `μ ≥ c > 0` gives `1/μ ≤ 1/c`; and `μ^τ ≥ c^τ` from
  --  `Real.rpow_le_rpow` plus `τ ≥ 0` gives `1/μ^τ ≤ 1/c^τ`. Then
  --  `1/c^τ ≤ 1/c + 1` by case-split on `c ≤ 1` vs `c > 1`.)
  have hμτ_ge_cτ : c ^ τ ≤ μx ^ τ :=
    Real.rpow_le_rpow hc.le hμ hτ_nn
  have hcτ_pos : 0 < c ^ τ := Real.rpow_pos_of_pos hc τ
  have h_inv_μ_le : 1 / μx ≤ 1 / c := by
    rw [div_le_div_iff₀ hμx_pos hc]; linarith
  have h_inv_μτ_le : 1 / μx ^ τ ≤ 1 / c ^ τ := by
    rw [div_le_div_iff₀ hμxτ_pos hcτ_pos]; linarith
  -- `1/c^τ ≤ 1/c + 1`: case-split on `c`.
  have h_inv_cτ_le : 1 / c ^ τ ≤ 1 / c + 1 := by
    by_cases h1 : 1 ≤ c
    · -- `c ≥ 1`: then `c^τ ≥ c^0 = 1` for `τ ≥ 0`, so `1/c^τ ≤ 1`.
      have h_cτ_ge_one : (1 : ℝ) ≤ c ^ τ := by
        have h0 : c ^ (0 : ℝ) ≤ c ^ τ :=
          Real.rpow_le_rpow_of_exponent_le h1 hτ_nn
        rw [Real.rpow_zero] at h0; exact h0
      have : 1 / c ^ τ ≤ 1 := by
        rw [div_le_iff₀ hcτ_pos]; linarith
      have hinv_c_nn : 0 ≤ 1 / c := by positivity
      linarith
    · push_neg at h1
      have hcle1 : c < 1 := h1
      -- `c < 1` and `0 ≤ τ ≤ 1`: `c^τ ≥ c^1 = c`, so `1/c^τ ≤ 1/c`.
      have h_cτ_ge_c : c ≤ c ^ τ := by
        have hRHS : c ^ τ ≥ c ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_ge hc hcle1.le hτ_le
        rw [Real.rpow_one] at hRHS; exact hRHS
      have : 1 / c ^ τ ≤ 1 / c := by
        rw [div_le_div_iff₀ hcτ_pos hc]; linarith
      linarith
  have h_factor1 : 1 / μx + 1 / μx ^ τ ≤ 2 / c + 1 := by
    have h1 : 1 / μx ≤ 1 / c := h_inv_μ_le
    have h2 : 1 / μx ^ τ ≤ 1 / c + 1 := le_trans h_inv_μτ_le h_inv_cτ_le
    have : 2 / c = 1 / c + 1 / c := by ring
    linarith [this]
  have h_factor1' : 1 / μx + 1 / μx ^ τ ≤ 2 / c + 2 := by linarith
  -- Factor 2: `μ^τ + 1 ≤ ?`. This is unbounded in μ! So we cannot
  -- bound the product by bounding each factor in isolation.
  -- BUT: we can use the inequality directly by computing the product.
  -- Note: factor 1 is bounded, but factor 2 is not. Hence "K depends
  -- on c" cannot work without using their interaction.
  -- We need the interaction: `(1/μ + 1/μ^τ)(μ^τ + 1) = μ^{τ-1} + 1/μ
  -- + 1 + 1/μ^τ`. The `μ^{τ-1}` term is bounded by `1/c + 1` (since
  -- `τ - 1 ≤ 0` and `μ ≥ c`), `1/μ ≤ 1/c`, `1 ≤ 1`, `1/μ^τ ≤ 1/c + 1`.
  -- Sum: `3/c + 3` bound.
  -- Direct expansion. Use `field_simp` carefully.
  have hμx_ne : μx ≠ 0 := ne_of_gt hμx_pos
  have hμxτ_ne : μx ^ τ ≠ 0 := ne_of_gt hμxτ_pos
  -- Compute LHS step-by-step:
  -- (1/μ + 1/μ^τ)(μ^τ + 1)
  --   = (1/μ)·μ^τ + 1/μ + (1/μ^τ)·μ^τ + 1/μ^τ
  --   = μ^τ/μ + 1/μ + 1 + 1/μ^τ.
  have h_expand :
      (1 / μx + 1 / μx ^ τ) * (μx ^ τ + 1)
        = μx ^ τ / μx + 1 / μx + 1 + 1 / μx ^ τ := by
    field_simp
    ring
  -- Bound `μ^τ / μ`. Since `μ ≥ c > 0`, `1/μ ≤ 1/c`. And `μ^τ ≤ μ` for
  -- `τ ≤ 1` and `μ ≥ 1`, OR `μ^τ ≤ 1` for `τ ≥ 0` and `μ ≤ 1`. We
  -- handle both cases via `μ^τ ≤ μ + 1`, which holds since
  -- `μ^τ ≤ μ^1 + 1 = μ + 1` for `μ ≥ 1, τ ≤ 1`, and `μ^τ ≤ 1 ≤ μ + 1`
  -- for `0 < μ ≤ 1`.
  have h_μτ_le : μx ^ τ ≤ μx + 1 := by
    by_cases hμ1 : 1 ≤ μx
    · -- μ ≥ 1, τ ≤ 1: μ^τ ≤ μ^1 = μ.
      have h := Real.rpow_le_rpow_of_exponent_le hμ1 hτ_le
      rw [Real.rpow_one] at h; linarith
    · push_neg at hμ1
      -- 0 < μ < 1, τ ≥ 0: μ^τ ≤ μ^0 = 1.
      have h := Real.rpow_le_rpow_of_exponent_ge hμx_pos hμ1.le hτ_nn
      rw [Real.rpow_zero] at h; linarith
  have h_μτ_div : μx ^ τ / μx ≤ (μx + 1) / μx := by
    rw [div_le_div_iff₀ hμx_pos hμx_pos]
    exact mul_le_mul_of_nonneg_right h_μτ_le hμx_pos.le
  -- (μ + 1)/μ = 1 + 1/μ ≤ 1 + 1/c.
  have h_split : (μx + 1) / μx = 1 + 1 / μx := by
    field_simp
  have h_μτ_div' : μx ^ τ / μx ≤ 1 + 1 / c := by
    rw [h_split] at h_μτ_div
    linarith [h_inv_μ_le]
  -- Combine:
  rw [h_expand]
  -- Goal: μ^τ/μ + 1/μ + 1 + 1/μ^τ ≤ (2/c + 2)(2/c + 2).
  -- Use h_μτ_div' (≤ 1 + 1/c), h_inv_μ_le (1/μ ≤ 1/c),
  -- 1 ≤ 1, h_inv_μτ_le (1/μ^τ ≤ 1/c^τ ≤ 1/c + 1).
  have h_inv_μτ_full : 1 / μx ^ τ ≤ 1 / c + 1 := le_trans h_inv_μτ_le h_inv_cτ_le
  have hcinv_pos : 0 < 1 / c := by positivity
  -- Sum: ≤ (1 + 1/c) + 1/c + 1 + (1/c + 1) = 3 + 3/c.
  -- And (2/c + 2)·(2/c + 2) = 4/c² + 8/c + 4 ≥ 3 + 3/c when 1/c ≥ 0.
  -- Need (2/c + 2)² ≥ 3 + 3/c. (2/c + 2)² ≥ (2/c)² + 2·(2/c)·2
  --   = 4/c² + 8/c. So (2/c + 2)² = 4/c² + 8/c + 4. We need
  -- 4/c² + 8/c + 4 ≥ 3 + 3/c, i.e. 4/c² + 5/c + 1 ≥ 0, which holds
  -- since 1/c > 0 and 4/c² > 0.
  have hsum : μx ^ τ / μx + 1 / μx + 1 + 1 / μx ^ τ ≤ 3 + 3 * (1 / c) := by
    linarith
  have hRHS : 3 + 3 * (1 / c) ≤ (2 / c + 2) * (2 / c + 2) := by
    have h1c_pos : 0 ≤ 1 / c := hcinv_pos.le
    have h_sq : 0 ≤ (1 / c) * (1 / c) := mul_nonneg h1c_pos h1c_pos
    have h_eq : 2 / c = 2 * (1 / c) := by ring
    rw [h_eq]
    nlinarith [h_sq, h1c_pos]
  linarith

/-! ## AC1: HJB-side `MemLpPer β̄'`

The function `x ↦ H(x, Du, m) - V(x)` lies in `MemLpPer β̄'` provided:

* `(m, u) ∈ 𝓚` (so `MemLpPer β̄' (|Du|^{αt}/(μ^τ + 1))` and `c ≤ μ` a.e.);
* `V ∈ MemLpPer β̄'`;
* an a.e. bound `|H(x, p, mm)| ≤ K · (1/mm + 1/mm^τ) · (‖p‖^{αt} + 1)
                                 + K · (mm^β + 1)` (from
  `upper_bound_congestiongrowth` and the symmetric lower bound).

We package the load-bearing inputs as hypotheses so this lemma is a
clean dominator argument and does not re-derive the upper / lower bound
manipulations of `Hamiltonian/Congestion.lean`.
-/

/-- Bound for `(1/m + 1/m^τ)(|Du|^{αt} + 1)` in `L^{β̄'}` from a pair
in `𝓚`. -/
private lemma ratio_full_memLp_betaBarPrime
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} {α β τ : ℝ}
    (hτ_nn : 0 ≤ τ) (hτ_le : τ ≤ 1)
    {μ υ : (Fin d → ℝ) → ℝ}
    (hpair : (μ, υ) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ) :
    ∃ Du : Fin d → (Fin d → ℝ) → ℝ,
      (∀ i, HasWeakDerivPer i υ (Du i)) ∧
        MemLpPer betaBarPrime
          (fun x : (Fin d → ℝ) =>
            (1 / μ x + 1 / μ x ^ τ) *
              (‖fun i => Du i x‖ ^ (α * (1 + τ / β)) + 1)) := by
  obtain ⟨_hμLp, _hυSob, ⟨c, hc_pos, hμ_lower⟩, ⟨Du, hDu, hDu_int⟩⟩ := hpair
  refine ⟨Du, hDu, ?_⟩
  set αt : ℝ := α * (1 + τ / β) with hαt_def
  -- The hypothesis gives `(‖Du‖^αt) / (μ^τ + 1) ∈ MemLpPer β̄'`.
  -- We need `(1/μ + 1/μ^τ)(‖Du‖^αt + 1)` in the same space. Strategy:
  -- show pointwise bound `LHS ≤ (3/c + 3) · ((‖Du‖^αt) / (μ^τ + 1)) + (3/c + 3)`,
  -- using the decomposition
  -- (1/μ + 1/μ^τ)(‖Du‖^αt + 1) = ((1/μ + 1/μ^τ)(μ^τ + 1)) · (‖Du‖^αt + 1) / (μ^τ + 1)
  --                            ≤ (3/c + 3) · (‖Du‖^αt + 1) / (μ^τ + 1)
  --                            = (3/c + 3) · [‖Du‖^αt / (μ^τ + 1) + 1 / (μ^τ + 1)].
  -- And `1/(μ^τ + 1) ≤ 1` since `μ^τ ≥ 0`.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Measurability building blocks.
  have hμ_meas : AEStronglyMeasurable μ
      (Measure.restrict volume (UnitCube d)) :=
    _hμLp.aestronglyMeasurable
  have hμτ_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => μ x ^ τ)
      (Measure.restrict volume (UnitCube d)) :=
    (Real.continuous_rpow_const hτ_nn).comp_aestronglyMeasurable hμ_meas
  have hinvμ_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => 1 / μ x)
      (Measure.restrict volume (UnitCube d)) := by
    refine AEStronglyMeasurable.div₀ aestronglyMeasurable_const hμ_meas
  have hinvμτ_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => 1 / μ x ^ τ)
      (Measure.restrict volume (UnitCube d)) := by
    refine AEStronglyMeasurable.div₀ aestronglyMeasurable_const hμτ_meas
  have h_sum_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => 1 / μ x + 1 / μ x ^ τ)
      (Measure.restrict volume (UnitCube d)) :=
    hinvμ_meas.add hinvμτ_meas
  -- AE strong measurability of `‖Du‖^αt + 1`. Use that the ratio is
  -- AEStronglyMeasurable, and `μ^τ + 1 > 0` so we can multiply back.
  have hDu_int_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ =>
        (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1))
      (Measure.restrict volume (UnitCube d)) :=
    hDu_int.aestronglyMeasurable
  have hdenom_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => μ x ^ τ + 1)
      (Measure.restrict volume (UnitCube d)) :=
    hμτ_meas.add aestronglyMeasurable_const
  -- Numerator from ratio · denominator.
  have hnum_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt)
      (Measure.restrict volume (UnitCube d)) := by
    have hprod : AEStronglyMeasurable
        (fun x => ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1))
                    * (μ x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) :=
      hDu_int_meas.mul hdenom_meas
    apply hprod.congr
    filter_upwards [hμ_lower] with x hx
    have hxμ_nn : 0 ≤ μ x := hc_pos.le.trans hx
    have h_denom_pos : 0 < μ x ^ τ + 1 := by
      have := Real.rpow_nonneg hxμ_nn τ; linarith
    field_simp
  have h_full_meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ =>
        (1 / μ x + 1 / μ x ^ τ) *
          (‖fun i => Du i x‖ ^ αt + 1))
      (Measure.restrict volume (UnitCube d)) :=
    h_sum_meas.mul (hnum_meas.add aestronglyMeasurable_const)
  -- Constant function `1`'s `MemLpPer β̄'` membership.
  have h_one_memLp : MemLpPer (d := d) betaBarPrime
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  -- Bound `K := 3 / c + 3 > 0`.
  set K : ℝ := (2 / c + 2) * (2 / c + 2) with hK_def
  have hK_pos : 0 < K := by
    have h1 : 0 < 2 / c := by positivity
    have h2 : 0 < 2 / c + 2 := by linarith
    exact mul_pos h2 h2
  -- Combined dominator function: `K · (ratio + 1)`.
  have h_dom_memLp : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) =>
        K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) + 1)) := by
    have hscaled : MemLpPer (d := d) betaBarPrime
        (fun x : (Fin d → ℝ) =>
          K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)) + K) := by
      have hAdd : MemLpPer (d := d) betaBarPrime
          (fun x : (Fin d → ℝ) =>
            (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)) := hDu_int
      have h_K_smul : MemLpPer (d := d) betaBarPrime
          (fun x : (Fin d → ℝ) =>
            K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1))) := by
        have hh := hAdd.const_smul (𝕜 := ℝ) K
        -- hh : MemLpPer betaBarPrime (K • fun x => ...)
        -- Need: MemLpPer betaBarPrime (fun x => K * ...). They are
        -- propositionally equal via funext + smul_eq_mul.
        have hfun_eq : (K • fun x : Fin d → ℝ =>
              (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1))
              = (fun x : Fin d → ℝ =>
                  K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1))) := by
          funext x; simp [Pi.smul_apply, smul_eq_mul]
        rw [hfun_eq] at hh
        exact hh
      have h_K_const : MemLpPer (d := d) betaBarPrime
          (fun _ : (Fin d → ℝ) => K) := MemLp.toMemLpPer (memLp_const K)
      exact h_K_smul.add h_K_const
    -- Pointwise the two are equal.
    have heq :
        (fun x : Fin d → ℝ =>
          K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) + 1))
        = (fun x : Fin d → ℝ =>
            K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)) + K) := by
      funext x; ring
    rw [heq]
    -- hscaled has the form `MemLpPer (… + …)` but as a function-sum not `fun x => … + …`.
    -- Convert by funext.
    have hsum_eq :
        ((fun x : Fin d → ℝ =>
            K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)))
          + fun _ : Fin d → ℝ => K)
        = (fun x : Fin d → ℝ =>
            K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)) + K) := by
      funext x; rfl
    rw [← hsum_eq]
    exact hscaled
  -- Pointwise bound `|LHS x| ≤ 1 · |dom x|` a.e.
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) h_dom_memLp.toMemLp h_full_meas
  filter_upwards [hμ_lower] with x hx
  have hxμ : c ≤ μ x := hx
  have hxμ_pos : 0 < μ x := lt_of_lt_of_le hc_pos hxμ
  have hxμ_nn : 0 ≤ μ x := hxμ_pos.le
  have hxμτ_pos : 0 < μ x ^ τ := Real.rpow_pos_of_pos hxμ_pos τ
  have hxμτ_nn : 0 ≤ μ x ^ τ := hxμτ_pos.le
  have h_denom_pos : 0 < μ x ^ τ + 1 := by linarith
  have h_denom_ge_one : (1 : ℝ) ≤ μ x ^ τ + 1 := by linarith
  -- Pointwise key estimate: paper line 1357.
  have h_ratio_le : (1 / μ x + 1 / μ x ^ τ) * (μ x ^ τ + 1) ≤ K :=
    aux_ratio_pointwise_bound hc_pos hxμ hτ_nn hτ_le
  -- Compute the LHS as: (1/μ + 1/μ^τ)·(‖Du‖^αt + 1)
  --   = [(1/μ + 1/μ^τ)·(μ^τ + 1)] · (‖Du‖^αt + 1) / (μ^τ + 1)
  --   ≤ K · (‖Du‖^αt + 1) / (μ^τ + 1)
  --   = K · (‖Du‖^αt / (μ^τ + 1) + 1 / (μ^τ + 1))
  --   ≤ K · (‖Du‖^αt / (μ^τ + 1) + 1).
  have h_num_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
    Real.rpow_nonneg (norm_nonneg _) αt
  have h_num1_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt + 1 := by linarith
  have h_invSum_nn : 0 ≤ 1 / μ x + 1 / μ x ^ τ := by
    have h1 : 0 ≤ 1 / μ x := by positivity
    have h2 : 0 ≤ 1 / μ x ^ τ := by positivity
    linarith
  have h_LHS_nn : 0 ≤ (1 / μ x + 1 / μ x ^ τ) *
        (‖fun i => Du i x‖ ^ αt + 1) :=
    mul_nonneg h_invSum_nn h_num1_nn
  -- Key step: (1/μ + 1/μ^τ) ≤ K / (μ^τ + 1) since
  -- (1/μ + 1/μ^τ)(μ^τ + 1) ≤ K, dividing by `μ^τ + 1 > 0`.
  have h_invSum_le : 1 / μ x + 1 / μ x ^ τ ≤ K / (μ x ^ τ + 1) := by
    rw [le_div_iff₀ h_denom_pos]
    exact h_ratio_le
  have h_step1 :
      (1 / μ x + 1 / μ x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1)
        ≤ K / (μ x ^ τ + 1) * (‖fun i => Du i x‖ ^ αt + 1) :=
    mul_le_mul_of_nonneg_right h_invSum_le h_num1_nn
  -- K / (μ^τ + 1) · (‖Du‖^αt + 1) = K · ((‖Du‖^αt + 1) / (μ^τ + 1))
  --                               = K · (‖Du‖^αt / (μ^τ + 1) + 1 / (μ^τ + 1)).
  have h_eq1 : K / (μ x ^ τ + 1) * (‖fun i => Du i x‖ ^ αt + 1)
      = K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)
               + 1 / (μ x ^ τ + 1)) := by
    have h_denom_ne : μ x ^ τ + 1 ≠ 0 := ne_of_gt h_denom_pos
    field_simp
  -- 1 / (μ^τ + 1) ≤ 1 since `μ^τ + 1 ≥ 1`.
  have h_invDenom_le : 1 / (μ x ^ τ + 1) ≤ 1 := by
    rw [div_le_iff₀ h_denom_pos]; linarith
  have h_step2 :
      K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)
              + 1 / (μ x ^ τ + 1))
        ≤ K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) + 1) := by
    apply mul_le_mul_of_nonneg_left _ hK_pos.le
    have h_ratio_nn : 0 ≤ (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) :=
      div_nonneg h_num_nn h_denom_pos.le
    linarith
  have h_combine :
      (1 / μ x + 1 / μ x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1)
        ≤ K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) + 1) := by
    calc (1 / μ x + 1 / μ x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1)
        ≤ K / (μ x ^ τ + 1) * (‖fun i => Du i x‖ ^ αt + 1) := h_step1
      _ = K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1)
                + 1 / (μ x ^ τ + 1)) := h_eq1
      _ ≤ K * ((‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) + 1) := h_step2
  -- Repackage as `‖LHS‖ ≤ 1 · ‖dom‖`.
  have h_dom_nn : 0 ≤ K * ((‖fun i => Du i x‖ ^ αt) /
        (μ x ^ τ + 1) + 1) := by
    have h_ratio_nn : 0 ≤ (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) :=
      div_nonneg h_num_nn h_denom_pos.le
    have : 0 ≤ (‖fun i => Du i x‖ ^ αt) / (μ x ^ τ + 1) + 1 := by linarith
    exact mul_nonneg hK_pos.le this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_LHS_nn,
      abs_of_nonneg h_dom_nn, one_mul]
  exact h_combine

/-- **AC1: HJB-side `MemLpPer β̄'`.**

For `(m, u) ∈ 𝓚` and `V ∈ L^{β̄'}_per`, given an a.e. bound on `|H|` of
the form

```
|H(x, p, mm)| ≤ K · (1/mm + 1/mm^τ) · (‖p‖^{αt} + 1)
              + K · (mm^β + 1)            (a.e. x, mm > 0)
```

(which follows from `upper_bound_congestiongrowth` paired with the
analogous lower bound `lower_congestion_of_alternative` in
`Hamiltonian/Congestion.lean`), the function

```
x ↦ -u(x) - H(x, Du(x), m(x)) + V(x)
```

lies in `MemLpPer β̄'`.

The `Du` used here is the bundle's weak-gradient witness from `hmu`,
extracted via `Exists.choose`. Callers wanting a *specific* `Du` can
take advantage of the uniqueness of weak derivatives a.e. and a
congruence lemma to rewrite the literal.

The proof is the dominator argument: bound `|H|` pointwise by the sum
of the ratio piece (handled via `ratio_full_memLp_betaBarPrime`) and a
`m^β + 1` piece (handled via the `MemLpPer β̄` membership of `m` plus
the inclusion `L^{β̄} ↪ L^{β̄'}` when `β̄' ≤ β̄`); `u, V ∈ L^{β̄'}` are
separate summands.

The `MemLpPer β̄' u` and `MemLpPer β̄' (m^β + 1)` hypotheses are
threaded explicitly because they are paper-exponent residues (they
follow from `m ∈ L^{β̄}_per` with `β̄' ≤ β̄`, plus the Sobolev embedding
`W^{1,γ̄} ↪ L^{β̄'}` for `u`); per CONVENTIONS §8 we expose them as
hypotheses rather than baking in the exponent identities. -/
theorem aEpsi_congestion_HJB_memLp
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {α β τ : ℝ} (hτ_nn : 0 ≤ τ) (hτ_le : τ ≤ 1)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hmu : (m, u) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ)
    (hV : MemLpPer (d := d) betaBarPrime V)
    (hu : MemLpPer (d := d) betaBarPrime u)
    -- The chosen Du witness (the bundle's). Pinned via `Exists.choose`
    -- of the integrability witness in `hmu` so the supplied Du is
    -- defeq to the one whose ratio integrability is certified.
    -- `K` and the a.e. pointwise bound on `|H|`.
    (K : ℝ) (hK_pos : 0 < K)
    (hH_bound :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ p mm, 0 < mm →
          |H x p mm| ≤
            K * ((1 / mm) + (1 / mm ^ τ))
                  * (‖p‖ ^ (α * (1 + τ / β)) + 1)
              + K * (mm ^ β + 1))
    -- AE strong measurability of the assembled function (caller-supplied
    -- using `Classical.choose hmu.2.2.2` for the Du).
    (hF_meas :
      AEStronglyMeasurable
        (fun x => -(u x) - H x (fun i => (hmu.2.2.2.choose i) x) (m x) + V x)
        (Measure.restrict volume (UnitCube d)))
    -- Dominator MemLpPer for `m^β + 1`. (Follows from `m ∈ L^{β̄}_per`
    -- and `β̄' ≤ β̄`; threaded explicitly per CONVENTIONS §8.)
    (hmβ_dom :
      MemLpPer (d := d) betaBarPrime
        (fun x : (Fin d → ℝ) => m x ^ β + 1))
    -- A.e. positivity of `m` (needed to invoke the H-bound, which
    -- requires `mm > 0`). Follows from `essinf m > 0` in `hmu`.
    (hm_pos : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x) :
    MemLpPer (d := d) betaBarPrime
      (fun x => -(u x) - H x (fun i => (hmu.2.2.2.choose i) x) (m x) + V x) := by
  -- Use the bundle's Du witness via Exists.choose.
  set Du : Fin d → (Fin d → ℝ) → ℝ := hmu.2.2.2.choose with hDu_def
  have hDu_spec := hmu.2.2.2.choose_spec
  -- Extract pieces *before* destructuring, while `hmu` is still around.
  have hmu_copy := hmu
  obtain ⟨_hμLp, _hυSob, ⟨c, hc_pos, hμ_lower⟩, _hwit⟩ := hmu_copy
  set αt : ℝ := α * (1 + τ / β) with hαt_def
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Re-derive the ratio integrability for the bundle-chosen `Du`:
  have h_ratio : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) =>
        (1 / m x + 1 / m x ^ τ) *
          (‖fun i => Du i x‖ ^ αt + 1)) := by
    -- The bundle's `choose_spec.2` gives us
    -- `MemLpPer β̄' (‖Du‖^αt / (m^τ + 1))`.
    have hDu_int : MemLpPer (d := d) betaBarPrime
        (fun x : (Fin d → ℝ) =>
          (‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1)) := hDu_spec.2
    -- Same dominator argument as in `ratio_full_memLp_betaBarPrime`:
    have hμ_meas : AEStronglyMeasurable m
        (Measure.restrict volume (UnitCube d)) :=
      _hμLp.aestronglyMeasurable
    have hμτ_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => m x ^ τ)
        (Measure.restrict volume (UnitCube d)) :=
      (Real.continuous_rpow_const hτ_nn).comp_aestronglyMeasurable hμ_meas
    have hinvμ_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => 1 / m x)
        (Measure.restrict volume (UnitCube d)) :=
      AEStronglyMeasurable.div₀ aestronglyMeasurable_const hμ_meas
    have hinvμτ_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => 1 / m x ^ τ)
        (Measure.restrict volume (UnitCube d)) :=
      AEStronglyMeasurable.div₀ aestronglyMeasurable_const hμτ_meas
    have h_sum_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => 1 / m x + 1 / m x ^ τ)
        (Measure.restrict volume (UnitCube d)) :=
      hinvμ_meas.add hinvμτ_meas
    have hDu_int_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          (‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) :=
      hDu_int.aestronglyMeasurable
    have hdenom_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => m x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      hμτ_meas.add aestronglyMeasurable_const
    have hnum_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt)
        (Measure.restrict volume (UnitCube d)) := by
      have hprod : AEStronglyMeasurable
          (fun x => ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1))
                      * (m x ^ τ + 1))
          (Measure.restrict volume (UnitCube d)) :=
        hDu_int_meas.mul hdenom_meas
      apply hprod.congr
      filter_upwards [hμ_lower] with x hx
      have hxμ_nn : 0 ≤ m x := hc_pos.le.trans hx
      have h_denom_pos : 0 < m x ^ τ + 1 := by
        have := Real.rpow_nonneg hxμ_nn τ; linarith
      field_simp
    have h_full_meas : AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          (1 / m x + 1 / m x ^ τ) *
            (‖fun i => Du i x‖ ^ αt + 1))
        (Measure.restrict volume (UnitCube d)) :=
      h_sum_meas.mul (hnum_meas.add aestronglyMeasurable_const)
    set K_aux : ℝ := (2 / c + 2) * (2 / c + 2) with hK_aux_def
    have hK_aux_pos : 0 < K_aux := by
      have h1 : 0 < 2 / c := by positivity
      have h2 : 0 < 2 / c + 2 := by linarith
      exact mul_pos h2 h2
    have h_dom_memLp : MemLpPer (d := d) betaBarPrime
        (fun x : (Fin d → ℝ) =>
          K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1)) := by
      have h_K_smul : MemLpPer (d := d) betaBarPrime
          (fun x : (Fin d → ℝ) =>
            K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1))) := by
        have hh := hDu_int.const_smul (𝕜 := ℝ) K_aux
        have hfun_eq : (K_aux • fun x : Fin d → ℝ =>
              (‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1))
              = (fun x : Fin d → ℝ =>
                  K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1))) := by
          funext x; simp [Pi.smul_apply, smul_eq_mul]
        rw [hfun_eq] at hh
        exact hh
      have h_K_const : MemLpPer (d := d) betaBarPrime
          (fun _ : (Fin d → ℝ) => K_aux) := MemLp.toMemLpPer (memLp_const K_aux)
      have h_sum := h_K_smul.add h_K_const
      have hsum_eq :
          ((fun x : Fin d → ℝ =>
              K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1)))
            + fun _ : Fin d → ℝ => K_aux)
          = (fun x : Fin d → ℝ =>
              K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1)) := by
        funext x
        change K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1)) + K_aux
            = K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1)
        ring
      rw [hsum_eq] at h_sum
      exact h_sum
    apply MemLp.toMemLpPer
    apply MemLp.of_le_mul (c := 1) h_dom_memLp.toMemLp h_full_meas
    filter_upwards [hμ_lower] with x hx
    have hxμ : c ≤ m x := hx
    have hxμ_pos : 0 < m x := lt_of_lt_of_le hc_pos hxμ
    have hxμ_nn : 0 ≤ m x := hxμ_pos.le
    have hxμτ_pos : 0 < m x ^ τ := Real.rpow_pos_of_pos hxμ_pos τ
    have hxμτ_nn : 0 ≤ m x ^ τ := hxμτ_pos.le
    have h_denom_pos : 0 < m x ^ τ + 1 := by linarith
    have h_denom_ge_one : (1 : ℝ) ≤ m x ^ τ + 1 := by linarith
    have h_ratio_le : (1 / m x + 1 / m x ^ τ) * (m x ^ τ + 1) ≤ K_aux :=
      aux_ratio_pointwise_bound hc_pos hxμ hτ_nn hτ_le
    have h_num_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) αt
    have h_num1_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt + 1 := by linarith
    have h_invSum_nn : 0 ≤ 1 / m x + 1 / m x ^ τ := by
      have h1 : 0 ≤ 1 / m x := by positivity
      have h2 : 0 ≤ 1 / m x ^ τ := by positivity
      linarith
    have h_LHS_nn : 0 ≤ (1 / m x + 1 / m x ^ τ) *
          (‖fun i => Du i x‖ ^ αt + 1) :=
      mul_nonneg h_invSum_nn h_num1_nn
    have h_invSum_le : 1 / m x + 1 / m x ^ τ ≤ K_aux / (m x ^ τ + 1) := by
      rw [le_div_iff₀ h_denom_pos]; exact h_ratio_le
    have h_step1 :
        (1 / m x + 1 / m x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1)
          ≤ K_aux / (m x ^ τ + 1) * (‖fun i => Du i x‖ ^ αt + 1) :=
      mul_le_mul_of_nonneg_right h_invSum_le h_num1_nn
    have h_eq1 : K_aux / (m x ^ τ + 1) * (‖fun i => Du i x‖ ^ αt + 1)
        = K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1)
                 + 1 / (m x ^ τ + 1)) := by
      have h_denom_ne : m x ^ τ + 1 ≠ 0 := ne_of_gt h_denom_pos
      field_simp
    have h_invDenom_le : 1 / (m x ^ τ + 1) ≤ 1 := by
      rw [div_le_iff₀ h_denom_pos]; linarith
    have h_step2 :
        K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1)
                + 1 / (m x ^ τ + 1))
          ≤ K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1) := by
      apply mul_le_mul_of_nonneg_left _ hK_aux_pos.le
      have h_ratio_nn : 0 ≤ (‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) :=
        div_nonneg h_num_nn h_denom_pos.le
      linarith
    have h_combine :
        (1 / m x + 1 / m x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1)
          ≤ K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1) := by
      calc (1 / m x + 1 / m x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1)
          ≤ K_aux / (m x ^ τ + 1) * (‖fun i => Du i x‖ ^ αt + 1) := h_step1
        _ = K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1)
                  + 1 / (m x ^ τ + 1)) := h_eq1
        _ ≤ K_aux * ((‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1) := h_step2
    have h_dom_nn : 0 ≤ K_aux * ((‖fun i => Du i x‖ ^ αt) /
          (m x ^ τ + 1) + 1) := by
      have h_ratio_nn : 0 ≤ (‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) :=
        div_nonneg h_num_nn h_denom_pos.le
      have : 0 ≤ (‖fun i => Du i x‖ ^ αt) / (m x ^ τ + 1) + 1 := by linarith
      exact mul_nonneg hK_aux_pos.le this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_LHS_nn,
        abs_of_nonneg h_dom_nn, one_mul]
    exact h_combine
  -- Step 2: scale by `K`.
  have h_K_ratio : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) =>
        K * ((1 / m x + 1 / m x ^ τ) *
          (‖fun i => Du i x‖ ^ αt + 1))) := by
    have hh := h_ratio.const_smul (𝕜 := ℝ) K
    have hfun_eq : (K • fun x : Fin d → ℝ =>
          (1 / m x + 1 / m x ^ τ) * (‖fun i => Du i x‖ ^ αt + 1))
          = (fun x : Fin d → ℝ =>
              K * ((1 / m x + 1 / m x ^ τ) *
                (‖fun i => Du i x‖ ^ αt + 1))) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun_eq] at hh
    exact hh
  -- Step 3: scale `m^β + 1` by `K`.
  have h_K_mβ : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) => K * (m x ^ β + 1)) := by
    have hh := hmβ_dom.const_smul (𝕜 := ℝ) K
    have hfun_eq : (K • fun x : Fin d → ℝ => m x ^ β + 1)
        = (fun x : Fin d → ℝ => K * (m x ^ β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun_eq] at hh
    exact hh
  -- Step 4: dominator = K · ratio + K · (m^β + 1) + |u| + |V|.
  have h_abs_u : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) => |u x|) := by
    -- |u x| = ‖u x‖ for real-valued u; we use AEStronglyMeasurable.norm.
    have hu_meas := hu.aestronglyMeasurable
    have h_norm := hu_meas.norm
    -- `MemLpPer p (fun x => ‖u x‖)` follows from `MemLpPer p u` directly.
    -- For real, `‖u x‖ = |u x|`. Use the eLpNorm congruence.
    have h_un : MemLpPer (d := d) betaBarPrime (fun x => ‖u x‖) := by
      refine ⟨h_norm, ?_⟩
      have heq : eLpNormPer betaBarPrime (fun x => ‖u x‖)
          = eLpNormPer betaBarPrime u := by
        unfold eLpNormPer
        rw [eLpNorm_norm _ hu_meas]
      rw [heq]; exact hu.eLpNormPer_lt_top
    have heq : (fun x : Fin d → ℝ => |u x|) = (fun x => ‖u x‖) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq]; exact h_un
  have h_abs_V : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) => |V x|) := by
    have hV_meas := hV.aestronglyMeasurable
    have h_norm := hV_meas.norm
    have h_Vn : MemLpPer (d := d) betaBarPrime (fun x => ‖V x‖) := by
      refine ⟨h_norm, ?_⟩
      have heq : eLpNormPer betaBarPrime (fun x => ‖V x‖)
          = eLpNormPer betaBarPrime V := by
        unfold eLpNormPer
        rw [eLpNorm_norm _ hV_meas]
      rw [heq]; exact hV.eLpNormPer_lt_top
    have heq : (fun x : Fin d → ℝ => |V x|) = (fun x => ‖V x‖) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq]; exact h_Vn
  -- Combine: dom := K·ratio + K·(m^β + 1) + |u| + |V|.
  have h_dom_combined : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) =>
        K * ((1 / m x + 1 / m x ^ τ) *
              (‖fun i => Du i x‖ ^ αt + 1))
          + K * (m x ^ β + 1) + |u x| + |V x|) :=
    ((h_K_ratio.add h_K_mβ).add h_abs_u).add h_abs_V
  -- Pointwise bound with constant 1.
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) h_dom_combined.toMemLp hF_meas
  filter_upwards [hH_bound, hμ_lower, hm_pos] with x hxH hxμ hxm_pos
  -- Set p := fun i => Du i x.
  set p_x : Fin d → ℝ := fun i => Du i x with hp_x_def
  -- Apply the H bound.
  have hxμ' : 0 < m x := hxm_pos
  have hH_abs := hxH p_x (m x) hxμ'
  -- Triangle: |F| = |-u - H + V| ≤ |u| + |H| + |V|.
  have h_tri :
      ‖-(u x) - H x p_x (m x) + V x‖
        ≤ |u x| + |H x p_x (m x)| + |V x| := by
    rw [Real.norm_eq_abs]
    -- Rewrite -(u x) - H + V = -(u x + H) + V. Or rewrite step by step.
    have heq_decomp : -(u x) - H x p_x (m x) + V x
        = (-(u x) + (-(H x p_x (m x)))) + V x := by ring
    rw [heq_decomp]
    calc |(-(u x) + -(H x p_x (m x))) + V x|
        ≤ |-(u x) + -(H x p_x (m x))| + |V x| := abs_add_le _ _
      _ ≤ (|-(u x)| + |-(H x p_x (m x))|) + |V x| := by
          gcongr
          exact abs_add_le _ _
      _ = (|u x| + |H x p_x (m x)|) + |V x| := by
          rw [abs_neg, abs_neg]
      _ = |u x| + |H x p_x (m x)| + |V x| := by ring
  -- Combine triangle + H bound.
  have h_total :
      ‖-(u x) - H x p_x (m x) + V x‖
        ≤ K * ((1 / m x) + (1 / m x ^ τ))
              * (‖p_x‖ ^ αt + 1)
          + K * (m x ^ β + 1) + |u x| + |V x| := by
    have h_inner :
        |u x| + |H x p_x (m x)| + |V x|
          ≤ K * ((1 / m x) + (1 / m x ^ τ))
                * (‖p_x‖ ^ αt + 1)
            + K * (m x ^ β + 1) + |u x| + |V x| := by
      linarith [hH_abs]
    exact le_trans h_tri h_inner
  -- Dominator is non-negative (each summand).
  have h_ratio_nn : 0 ≤ K * ((1 / m x + 1 / m x ^ τ) *
            (‖p_x‖ ^ αt + 1)) := by
    have h_invSum_nn : 0 ≤ 1 / m x + 1 / m x ^ τ := by
      have h1 : 0 ≤ 1 / m x := by positivity
      have h2 : 0 ≤ 1 / m x ^ τ := by positivity
      linarith
    have h_pαt_nn : 0 ≤ ‖p_x‖ ^ αt := Real.rpow_nonneg (norm_nonneg _) _
    have h_p1_nn : 0 ≤ ‖p_x‖ ^ αt + 1 := by linarith
    have h_prod_nn : 0 ≤ (1 / m x + 1 / m x ^ τ) * (‖p_x‖ ^ αt + 1) :=
      mul_nonneg h_invSum_nn h_p1_nn
    exact mul_nonneg hK_pos.le h_prod_nn
  have h_mβ_nn : 0 ≤ K * (m x ^ β + 1) := by
    have hxμ_nn : 0 ≤ m x := hxμ'.le
    have h_mβ : 0 ≤ m x ^ β := Real.rpow_nonneg hxμ_nn _
    have : 0 ≤ m x ^ β + 1 := by linarith
    exact mul_nonneg hK_pos.le this
  have h_dom_nn :
      0 ≤ K * ((1 / m x + 1 / m x ^ τ) *
              (‖p_x‖ ^ αt + 1))
          + K * (m x ^ β + 1) + |u x| + |V x| := by
    have habs1 : 0 ≤ |u x| := abs_nonneg _
    have habs2 : 0 ≤ |V x| := abs_nonneg _
    linarith
  -- Goal: `‖f x‖ ≤ 1 * ‖dom x‖` where dom is the combined function.
  -- After `Real.norm_eq_abs` and `abs_of_nonneg h_dom_nn`, RHS becomes
  -- `1 * dom`. After `one_mul`, RHS becomes `dom`. LHS becomes `|f x|`,
  -- so we need `|f x| ≤ dom`. This is `h_total` modulo a `ring` rearrangement.
  change ‖-(u x) - H x p_x (m x) + V x‖
        ≤ 1 * ‖K * ((1 / m x + 1 / m x ^ τ) * (‖p_x‖ ^ αt + 1))
              + K * (m x ^ β + 1) + |u x| + |V x|‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_dom_nn, one_mul]
  -- Goal: |...| ≤ K * ((1/m + 1/m^τ) * (‖p_x‖^αt + 1)) + K * (m^β + 1) + |u| + |V|.
  -- h_total has K * (1/m + 1/m^τ) * (‖p_x‖^αt + 1) (associativity diff).
  have h_eq : K * ((1 / m x) + (1 / m x ^ τ)) * (‖p_x‖ ^ αt + 1)
      = K * ((1 / m x + 1 / m x ^ τ) * (‖p_x‖ ^ αt + 1)) := by ring
  rw [← h_eq]
  exact h_total

/-- **AC2: flux-side `MemLpPer γ̄'`.**

For `(m, u) ∈ 𝓚`, given an a.e. bound on `‖DpH‖` of the form

```
‖DpH(x, p, mm)‖ ≤ C · (1/mm + 1/mm^τ) · ‖p‖^{αt - 1}
                 + C · (m^{β - β/α} + 1/mm)        (a.e. x, mm > 0)
```

(this is `(eq:assH.DpH.upper.congestion)`, i.e. `h.DpH_upper` in
`CongestionGrowthCore`), and the dominator integrability of the
post-multiplication function

```
G(x) := C · (1 + m(x)^{1 - τ}) · ‖Du(x)‖^{αt - 1}
       + C · (m(x)^{β + 1 - β/α} + 1)
```

in `L^{γ̄'}_per`, the vector field `x ↦ m(x) · D_pH(x, Du(x), m(x))`
lies in `MemLpPer γ̄'`. This is a direct application of
`mDpH_mem_Lp_gammaBar'_congestion`.

The `MemLpPer γ̄'` certificate of `G` is threaded explicitly per
CONVENTIONS §8: it follows from `m ∈ L^{β̄}_per`, `Du ∈ L^{γ̄}_per`,
and the congestion exponent identity `1/γ̄' = (1-τ)/β̄ + (αt-1)/γ̄`,
but is exposed as a hypothesis to keep this lemma agnostic. -/
theorem aEpsi_congestion_flux_memLp
    {C α β τ : ℝ}
    {m : (Fin d → ℝ) → ℝ} {Du : (Fin d → ℝ) → (Fin d → ℝ)}
    (F : (Fin d → ℝ) → (Fin d → ℝ))
    (hF_meas :
      AEStronglyMeasurable F (Measure.restrict volume (UnitCube d)))
    (hF_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖F x‖ ≤ C * (1 + m x ^ (1 - τ))
                  * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
              + C * (m x ^ (β + 1 - β / α) + 1))
    {q : ℝ≥0∞}
    (hG_mem :
      MemLpPer (d := d) q
        (fun x : (Fin d → ℝ) =>
          C * (1 + m x ^ (1 - τ))
              * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1))) :
    MemLpPer (d := d) q F :=
  Hamiltonian.mDpH_mem_Lp_gammaBar'_congestion (d := d)
    (q := q) m Du F hF_meas hF_le hG_mem

/-! ## AC3, AC4: ε-Gateaux p-Laplacian terms

The ε-Gateaux derivative of `(1/γ̄)·‖u‖_{W^{1,γ̄}}^{γ̄}` produces two
contributions:

* scalar: `x ↦ |u(x)|^{γ̄ - 2} · u(x)`,
* vector: `x ↦ |Du(x)|^{γ̄ - 2} · Du_i(x)`.

Both are bounded pointwise by `|·|^{γ̄ - 1}`, so they sit in `L^{γ̄'}`
once `u ∈ L^{γ̄}` (resp. `Du ∈ L^{γ̄}`). The L^{β̄'} membership in AC3
follows from the embedding `L^{γ̄'} ↪ L^{β̄'}` whenever `β̄' ≤ γ̄'`. -/

/-- **AC3: ε-Gateaux scalar term `MemLpPer β̄'`.**

For `MemSobolevPer γ̄ u` and `0 < ε`, given the a.e.-strong
measurability of the scalar p-Laplacian term and a `MemLpPer γ̄'`
dominator certificate (from the Sobolev embedding `L^{γ̄} ↪
L^{γ̄(γ̄-1)/(γ̄-1)} = L^{γ̄'⁻¹·…}`), the function
`x ↦ ε · |u(x)|^{γ̄ - 2} · u(x)` lies in `MemLpPer β̄'` provided
`β̄' ≤ γ̄'` (the embedding `L^{γ̄'} ↪ L^{β̄'}` holds on the
finite-measure unit cube).

Strategy: reduce to `|u|^{γ̄-1} ∈ L^{γ̄/(γ̄-1)} = L^{γ̄'}`. The
hypothesis `hScalar_dom : MemLpPer γ̄' (|u|^{γ̄-1})` is threaded; per
CONVENTIONS §8 the standard reduction of `MemLp p (|u|^{p-1}) ↔
MemLp p (·^{p-1}) ∘ |·|` is left to the supplier.
-/
theorem aEpsi_eps_u_term_memLp
    {γBar : ℝ}
    {betaBarPrime gammaBarPrime : ℝ≥0∞}
    (hβγ : betaBarPrime ≤ gammaBarPrime)
    (hγPrime_top : gammaBarPrime ≠ ⊤)
    (ε : ℝ) {u : (Fin d → ℝ) → ℝ}
    (h_scalar_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => ε * |u x| ^ (γBar - 2) * u x)
        (Measure.restrict volume (UnitCube d)))
    (h_scalar_dom :
      MemLpPer (d := d) gammaBarPrime
        (fun x : (Fin d → ℝ) => |u x| ^ (γBar - 1))) :
    MemLpPer (d := d) betaBarPrime
      (fun x => ε * |u x| ^ (γBar - 2) * u x) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Pointwise bound: `|ε · |u|^{γ̄-2} · u| = |ε| · |u|^{γ̄-1}` (since
  -- `|u|^{γ̄-2} · |u| = |u|^{γ̄-1}` for `|u| ≥ 0`).
  -- Hence the function is dominated by `|ε| · (|u|^{γ̄-1})`, which is
  -- in `MemLpPer γ̄'` and thus (by mono_exponent_finite) in
  -- `MemLpPer β̄'` when `β̄' ≤ γ̄'`.
  -- Step 1: bring the scalar dominator into `MemLpPer β̄'` via
  -- mono_exponent_finite.
  have h_scalar_betaPrime : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) => |u x| ^ (γBar - 1)) :=
    MemLpPer.mono_exponent_finite hβγ hγPrime_top h_scalar_dom
  -- Step 2: ε · (|u|^{γ̄-1}) is in MemLpPer β̄'.
  have h_eps_dom : MemLpPer (d := d) betaBarPrime
      (fun x : (Fin d → ℝ) => |ε| * |u x| ^ (γBar - 1)) := by
    have hh := h_scalar_betaPrime.const_smul (𝕜 := ℝ) |ε|
    have hfun_eq : (|ε| • fun x : Fin d → ℝ => |u x| ^ (γBar - 1))
        = (fun x : Fin d → ℝ => |ε| * |u x| ^ (γBar - 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun_eq] at hh
    exact hh
  -- Pointwise bound: `|ε · |u|^{γ̄-2} · u| ≤ 1 · |ε · |u|^{γ̄-1}|`.
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) h_eps_dom.toMemLp h_scalar_meas
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- LHS_norm = |ε · |u|^{γ̄-2} · u|. We show it equals |ε| · |u|^{γ̄-1}
  -- by case-splitting on `u x = 0`.
  have h_rhs_nn : 0 ≤ |ε| * |u x| ^ (γBar - 1) :=
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
  have h_lhs_eq :
      ‖ε * |u x| ^ (γBar - 2) * u x‖ ≤ |ε| * |u x| ^ (γBar - 1) := by
    by_cases hux : u x = 0
    · -- LHS norm = 0, RHS ≥ 0.
      have h_lhs_zero : ‖ε * |u x| ^ (γBar - 2) * u x‖ = 0 := by
        rw [hux]
        simp
      rw [h_lhs_zero]
      exact h_rhs_nn
    · have hux_pos : 0 < |u x| := abs_pos.mpr hux
      have h_pow_eq : |u x| ^ (γBar - 2) * |u x| = |u x| ^ (γBar - 1) := by
        have h := Real.rpow_add hux_pos (γBar - 2) 1
        have h' : |u x| ^ ((γBar - 2) + 1) = |u x| ^ (γBar - 2) * |u x| ^ (1 : ℝ) := h
        rw [Real.rpow_one] at h'
        have hexp : (γBar - 2) + 1 = γBar - 1 := by ring
        rw [hexp] at h'
        exact h'.symm
      have h_norm_eq : ‖ε * |u x| ^ (γBar - 2) * u x‖
                      = |ε| * |u x| ^ (γBar - 2) * |u x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [h_norm_eq, mul_assoc, h_pow_eq]
  -- Conclude: norm of LHS ≤ 1 · ‖dom‖.
  have h_norm_dom : ‖|ε| * |u x| ^ (γBar - 1)‖ = |ε| * |u x| ^ (γBar - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg h_rhs_nn]
  linarith [h_norm_dom, h_lhs_eq]

/-- **AC4: ε-Gateaux vector term `MemLpPer γ̄'`.**

For `Du i ∈ L^{γ̄}_per` (component of a `MemSobolevPer γ̄` weak
gradient), the function `x ↦ ε · |Du(x)|^{γ̄ - 2} · Du_i(x)` lies in
`MemLpPer γ̄'` provided we have a `MemLpPer γ̄'` dominator certificate
for `|Du|^{γ̄-1}`. Per CONVENTIONS §8, the dominator is exposed as a
hypothesis. -/
theorem aEpsi_eps_Du_term_memLp
    {γBar : ℝ}
    {gammaBarPrime : ℝ≥0∞}
    (ε : ℝ) {Du : Fin d → (Fin d → ℝ) → ℝ} (i : Fin d)
    (h_vec_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          ε * ‖fun j => Du j x‖ ^ (γBar - 2) * Du i x)
        (Measure.restrict volume (UnitCube d)))
    (h_vec_dom :
      MemLpPer (d := d) gammaBarPrime
        (fun x : (Fin d → ℝ) =>
          ‖fun j => Du j x‖ ^ (γBar - 1))) :
    MemLpPer (d := d) gammaBarPrime
      (fun x => ε * ‖fun j => Du j x‖ ^ (γBar - 2) * Du i x) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- |ε · ‖Du‖^{γ̄-2} · Du_i| ≤ |ε| · ‖Du‖^{γ̄-2} · ‖Du‖ = |ε| · ‖Du‖^{γ̄-1}
  -- since `|Du_i| ≤ ‖Du‖`.
  have h_eps_dom : MemLpPer (d := d) gammaBarPrime
      (fun x : (Fin d → ℝ) =>
        |ε| * ‖fun j => Du j x‖ ^ (γBar - 1)) := by
    have hh := h_vec_dom.const_smul (𝕜 := ℝ) |ε|
    have hfun_eq : (|ε| • fun x : Fin d → ℝ => ‖fun j => Du j x‖ ^ (γBar - 1))
        = (fun x : Fin d → ℝ => |ε| * ‖fun j => Du j x‖ ^ (γBar - 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun_eq] at hh
    exact hh
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) h_eps_dom.toMemLp h_vec_meas
  refine Filter.Eventually.of_forall (fun x => ?_)
  set p : Fin d → ℝ := fun j => Du j x with hp_def
  have hp_norm_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have h_pi_le : |p i| ≤ ‖p‖ := by
    have := norm_le_pi_norm p i
    simpa [Real.norm_eq_abs] using this
  have h_rhs_nn : 0 ≤ |ε| * ‖p‖ ^ (γBar - 1) :=
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp_norm_nn _)
  -- Show: ‖ε · ‖p‖^{γ̄-2} · p_i‖ ≤ |ε| · ‖p‖^{γ̄-1}.
  have h_main :
      ‖ε * ‖p‖ ^ (γBar - 2) * Du i x‖
        ≤ |ε| * ‖p‖ ^ (γBar - 1) := by
    -- Replace `Du i x` by `p i` (definitionally).
    have hpi : Du i x = p i := rfl
    rw [hpi]
    have h_norm_eq : ‖ε * ‖p‖ ^ (γBar - 2) * p i‖
                    = |ε| * ‖p‖ ^ (γBar - 2) * |p i| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hp_norm_nn _)]
    rw [h_norm_eq]
    by_cases hp0 : ‖p‖ = 0
    · -- ‖p‖ = 0 implies p = 0, so p i = 0; LHS = 0.
      have hp_eq_zero : p = 0 := norm_eq_zero.mp hp0
      have hpi_zero : p i = 0 := by rw [hp_eq_zero]; rfl
      rw [hpi_zero]
      simp [h_rhs_nn]
    · have hp_pos : 0 < ‖p‖ := lt_of_le_of_ne hp_norm_nn (Ne.symm hp0)
      have h_pow_eq : ‖p‖ ^ (γBar - 2) * ‖p‖ = ‖p‖ ^ (γBar - 1) := by
        have h := Real.rpow_add hp_pos (γBar - 2) 1
        have h' : ‖p‖ ^ ((γBar - 2) + 1) = ‖p‖ ^ (γBar - 2) * ‖p‖ ^ (1 : ℝ) := h
        rw [Real.rpow_one] at h'
        have hexp : (γBar - 2) + 1 = γBar - 1 := by ring
        rw [hexp] at h'
        exact h'.symm
      have h_pow_nn : 0 ≤ ‖p‖ ^ (γBar - 2) := Real.rpow_nonneg hp_norm_nn _
      calc |ε| * ‖p‖ ^ (γBar - 2) * |p i|
          ≤ |ε| * ‖p‖ ^ (γBar - 2) * ‖p‖ :=
            mul_le_mul_of_nonneg_left h_pi_le
              (mul_nonneg (abs_nonneg _) h_pow_nn)
        _ = |ε| * (‖p‖ ^ (γBar - 2) * ‖p‖) := by ring
        _ = |ε| * ‖p‖ ^ (γBar - 1) := by rw [h_pow_eq]
  have h_norm_dom : ‖|ε| * ‖p‖ ^ (γBar - 1)‖ = |ε| * ‖p‖ ^ (γBar - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg h_rhs_nn]
  linarith [h_norm_dom, h_main]

/-! ## AC5: pair-functional well-definedness

We package all summands. Given `MemLpPer`-certificates for the five
primal-side functions and Hölder-conjugate-pair certificates for the
test-side functions, every integrand in the pair functional is
integrable, hence the value of the functional is a real number.

This is the analogue of `mfgPairing_holder_bound` in
`Solutions/MFGOperator.lean`, restricted to the `A_ε` form.
-/

/-- **AC5: well-definedness of the pair functional**.

Given the five `MemLpPer`-certified primal-side functions and Hölder
test-side functions, every summand of the pairing is integrable, so
the value of the pair functional is finite. We package this as a
single statement: each of the five summand-integrands is integrable
on the unit cube. -/
theorem aEpsi_congestion_well_defined
    {p q : ℝ}
    (hpq : p.HolderConjugate q)
    {F_HJB F_mass G_val η ν : (Fin d → ℝ) → ℝ}
    {F_flux G_grad Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hF_HJB : MemLpPer (d := d) (ENNReal.ofReal q) F_HJB)
    (hF_flux : ∀ i, MemLpPer (d := d) (ENNReal.ofReal q) (F_flux i))
    (hF_mass : MemLpPer (d := d) (ENNReal.ofReal q) F_mass)
    (hG_grad : ∀ i, MemLpPer (d := d) (ENNReal.ofReal q) (G_grad i))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal q) G_val)
    (hη : MemLpPer (d := d) (ENNReal.ofReal p) η)
    (hν : MemLpPer (d := d) (ENNReal.ofReal p) ν)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal p) (Dν i)) :
    -- Every summand is integrable on the unit cube.
    IntegrableOn (fun x => F_HJB x * η x) (UnitCube d) ∧
    (∀ i, IntegrableOn (fun x => F_flux i x * Dν i x) (UnitCube d)) ∧
    IntegrableOn (fun x => F_mass x * ν x) (UnitCube d) ∧
    (∀ i, IntegrableOn (fun x => G_grad i x * Dν i x) (UnitCube d)) ∧
    IntegrableOn (fun x => G_val x * ν x) (UnitCube d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact MemLpPer.integrable_mul hpq.symm hF_HJB hη
  · intro i; exact MemLpPer.integrable_mul hpq.symm (hF_flux i) (hDν i)
  · exact MemLpPer.integrable_mul hpq.symm hF_mass hν
  · intro i; exact MemLpPer.integrable_mul hpq.symm (hG_grad i) (hDν i)
  · exact MemLpPer.integrable_mul hpq.symm hG_val hν

/-! ## Membership-only `L^{γ̄'}` / `L^{β̄'}` dischargers (T2 BB1c child B2)

The well-definedness lemmas above expose, per CONVENTIONS §8, the scalar
and vector `L^{γ̄'}` dominators (`|u|^{γ̄-1}`, `‖Du‖^{γ̄-1}`, `m^β`, `m-1`)
as caller-side hypotheses. This block discharges those dominators
**directly from `L^{β̄}`/`L^{γ̄}` membership** at the paper exponents
`β̄ = β+1`, `γ̄ = α(β+1)/β`, `γ̄' = γ̄/(γ̄-1)`, `β̄' = (β+1)/β`, using the
`rpow`-closure building block `MemLpPer.rpow_closure`
(`Periodic/Lp.lean`) and the finite-cube exponent inclusion
`MemLpPer.mono_exponent_finite`. No exponent-monotonicity rider and no
free per-element hypothesis is used — the riders are genuine Hölder /
`rpow`-closure consequences of membership.

These feed the membership-only auxiliary-hypothesis producer (child C). -/

open StationaryMFG.Periodic in
/-- **`hGval`/`hGgrad` dominator from membership.** For `f ∈ L^{γ̄}_per`
with `γ̄ = α(β+1)/β`, the dominator `‖f‖^{γ̄-1}` lies in `L^{γ̄'}_per`
(`γ̄' = γ̄/(γ̄-1)`), since `γ̄'·(γ̄-1) = γ̄` (rpow-closure). -/
theorem rpow_gammaBar_minus_one_memLp_gammaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) f) :
    MemLpPer (d := d)
      (ENNReal.ofReal ((α * (β + 1) / β) / (α * (β + 1) / β - 1)))
      (fun x => ‖f x‖ ^ (α * (β + 1) / β - 1)) := by
  set γbar : ℝ := α * (β + 1) / β with hγbar
  have hβbar_pos : 0 < β + 1 := by linarith
  have hγbar_pos : 0 < γbar := by rw [hγbar]; positivity
  have hγbar_gt_one : 1 < γbar := by rw [hγbar, lt_div_iff₀ hβ]; nlinarith
  have hγbarm1_pos : 0 < γbar - 1 := by linarith
  -- target exponent `γ̄'` satisfies `γ̄'·(γ̄-1) = γ̄`.
  have hmul : ENNReal.ofReal (γbar / (γbar - 1)) * ENNReal.ofReal (γbar - 1)
      = ENNReal.ofReal γbar := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  exact MemLpPer.rpow_closure (d := d) hγbarm1_pos
    (by rw [hmul]; exact hf)

open StationaryMFG.Periodic in
/-- **`hmβ_dom` dominator from membership.** For `m ∈ L^{β̄}_per` with
`β̄ = β+1`, the dominator `m^β` lies in `L^{β̄'}_per` (`β̄' = (β+1)/β`),
since `β̄'·β = β̄` (rpow-closure on `‖m‖^β`, with `m ≥ 0` a.e.). -/
theorem rpow_beta_memLp_betaBar'
    {β : ℝ} (hβ : 0 < β)
    {m : (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hm_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] m) :
    MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => m x ^ β) := by
  have hβbar_pos : 0 < β + 1 := by linarith
  -- `‖m‖^β ∈ L^{β̄'}` by rpow-closure; `β̄'·β = β̄`.
  have hmul : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have habs : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => ‖m x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hmul]; exact hm)
  -- Transport `‖m‖^β = m^β` a.e. via `m ≥ 0`.
  have hae : (fun x => ‖m x‖ ^ β) =ᵐ[Measure.restrict volume (UnitCube d)]
      (fun x => m x ^ β) := by
    filter_upwards [hm_nn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae habs.toMemLp)

/-- **`hMass` dominator from membership.** For `m ∈ L^{β̄}_per` with
`β̄ = β+1`, `F_mass m = m - 1 ∈ L^{γ̄'}_per`, using the (true) inclusion
`γ̄' ≤ β̄` (`MemLpPer.mono_exponent_finite` on the finite cube). -/
theorem mass_memLp_gammaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {m : (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m) :
    MemLpPer (d := d)
      (ENNReal.ofReal ((α * (β + 1) / β) / (α * (β + 1) / β - 1)))
      (fun x => m x - 1) := by
  set γbar : ℝ := α * (β + 1) / β with hγbar
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβbar_pos : 0 < β + 1 := by linarith
  have hγbar_pos : 0 < γbar := by rw [hγbar]; positivity
  have hγbar_gt_one : 1 < γbar := by rw [hγbar, lt_div_iff₀ hβ]; nlinarith
  have hγbar'_pos : 0 < γbar / (γbar - 1) := by
    apply div_pos hγbar_pos; linarith
  -- `m - 1 ∈ L^{β̄}` (constant `1` is integrable on the finite cube).
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hone : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
  have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => m x - 1) := by
    have := hm.add (hone.const_smul (𝕜 := ℝ) (-1 : ℝ))
    have heq : (m + (-1 : ℝ) • fun _ : (Fin d → ℝ) => (1 : ℝ))
        = (fun x => m x - 1) := by
      funext x; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [heq] at this
  -- Inclusion `γ̄' ≤ β̄ = β + 1` (the TRUE exponent inequality).
  have hγbarm1_pos : 0 < γbar - 1 := by linarith
  have hle : ENNReal.ofReal (γbar / (γbar - 1)) ≤ ENNReal.ofReal (β + 1) := by
    apply ENNReal.ofReal_le_ofReal
    -- `γ̄/(γ̄-1) ≤ β+1` ⟺ `γ̄ ≤ (β+1)(γ̄-1)` (since `γ̄-1 > 0`).
    rw [div_le_iff₀ hγbarm1_pos]
    -- Cross fact: `β·γ̄ = α(β+1)`.
    have hcross : β * γbar = α * (β + 1) := by
      rw [hγbar]; field_simp
    -- `(β+1)(γ̄-1) - γ̄ ≥ 0`: multiply by `β > 0` and use `β·γ̄ = α(β+1)`, `α ≥ 1`.
    nlinarith [hcross, hβ, hα, hγbar_gt_one, mul_pos hβ (sub_pos.mpr hγbar_gt_one)]
  exact MemLpPer.mono_exponent_finite hle ENNReal.ofReal_ne_top hsub

/-- **`hu` certificate from membership.** For `u ∈ L^{γ̄}_per` with
`γ̄ = α(β+1)/β`, `u ∈ L^{β̄'}_per` (`β̄' = (β+1)/β`), via `β̄' ≤ γ̄`
(`= α·β̄'` with `α ≥ 1`) and `MemLpPer.mono_exponent_finite`. -/
theorem u_memLp_betaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {u : (Fin d → ℝ) → ℝ}
    (hu : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) u) :
    MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) u := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hle : ENNReal.ofReal ((β + 1) / β) ≤ ENNReal.ofReal (α * (β + 1) / β) := by
    apply ENNReal.ofReal_le_ofReal
    have hnum : β + 1 ≤ α * (β + 1) := by nlinarith [hβ, hα]
    have : (β + 1) / β ≤ (α * (β + 1)) / β := by gcongr
    simpa [mul_div_assoc] using this
  exact MemLpPer.mono_exponent_finite hle ENNReal.ofReal_ne_top hu

end Congestion
end StationaryMFG
