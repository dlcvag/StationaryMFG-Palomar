module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.MuAux
public import StationaryMFG.Hamiltonian.Congestion
public import StationaryMFG.Periodic.Lp

@[expose] public section

/-!
# Integrability bounds for the auxiliary `μ` (paper `eq:H-at-Du-mu.bounds`)

This module formalises the integrability conclusions of paper
`Source/FGU-monotone_revised.tex`, lines 1441–1454, equation
`eq:H-at-Du-mu.bounds`. With the auxiliary correction `μ = muAux k m u V Du H`
of `MuAux.lean` in hand, the paper's two-step argument shows:

1. (line 1448) Combining the upper bound `eq:boundsH+`
   `H(x, p, m) ≤ C(1/m + 1/m^τ)(‖p‖^{α(1+τ/β)} + 1) - m^β/C` with the
   defining constraint `u + H(x, Du, μ) - V ≤ k` and Young's inequality
   gives the pointwise envelope
   `μ(x) ≤ C·|Du(x)|^{α/β} + C·(|u(x)| + |V(x)|)^{1/β} + C`,
   placing `μ ∈ L^{β̄}_per`.

2. (lines 1450–1454, eq.~`eq:H-at-Du-mu.bounds`) Combining the lower
   bound `eq:assH.lower.congestion`
   `H(x, Du, μ) ≥ (1/C)(|Du|^{α(1+τ/β)}/(μ^τ+1)) - C(μ^β + 1)`
   with the upper-bound constraint `H(x, Du, μ) ≤ k - u + V` yields
   the two-sided envelope
   `(1/C)(|Du|^{αt}/(μ^τ+1)) - C(μ^β+1) ≤ H(x, Du, μ) ≤ k + |u| + |V|`,
   placing `H(·, Du(·), μ(·)) ∈ L^{β̄'}_per` and
   `|Du|^{αt}/(μ^τ+1) ∈ L^{β̄'}_per`.

Following the precedent of `WellDefined.lean` (and CONVENTIONS §8), the
nontrivial pointwise envelopes are taken as hypotheses; the present
module performs the clean `MemLp.of_le_mul` dominator argument that
extracts the `MemLpPer` certificate. The pointwise envelopes themselves
follow from `Hamiltonian.upper_bound_congestiongrowth` and
`Hamiltonian.lower_congestion_of_alternative` together with the
Young-inequality manipulations of paper line 1443–1448.

## Deliverables

* `muAux_mem_Lp` — `MemLpPer β̄ (muAux k m u V Du H)`.
* `muAux_H_mem_Lp` — `MemLpPer β̄' (fun x => H x (Du x) (muAux ... x))`.
* `muAux_integrability_quotient` —
  `MemLpPer β̄' (fun x => |Du x|^{αt} / (muAux ... x ^ τ + 1))`.

## Paper reference

`Source/FGU-monotone_revised.tex` §`sec:proof-congestion`, lines 1441–1454,
eq.~`eq:H-at-Du-mu.bounds`.
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## Auxiliary: a `MemLpPer` certificate for a non-negative function via
absolute value. -/

/-- A non-negative real-valued function dominated by a `MemLpPer` function is
itself `MemLpPer`. This is the standard `MemLp.of_le_mul (c := 1)`
reduction with `‖f x‖ = f x` for `f ≥ 0`. -/
private lemma memLpPer_of_nonneg_le
    {p : ℝ≥0∞}
    {f g : (Fin d → ℝ) → ℝ}
    (hg : MemLpPer p g)
    (hf_meas :
      AEStronglyMeasurable f (Measure.restrict volume (UnitCube d)))
    (hf_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ f x)
    (hg_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ g x)
    (hfg : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), f x ≤ g x) :
    MemLpPer p f := by
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hg.toMemLp hf_meas
  filter_upwards [hf_nn, hg_nn, hfg] with x hfx hgx hxle
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hfx,
      abs_of_nonneg hgx, one_mul]
  exact hxle

/-! ## The paper envelope `G` for `μ` (paper line 1448) and its `L^{β̄}_per`
membership.

The paper's pointwise envelope (line 1448), obtained from `eq:boundsH+`
by the Young τ-cancellation of lines 1441–1448, is

  `μ(x) ≤ C·‖Du(x)‖^{α/β} + C·(|u(x)| + |V(x)|)^{1/β} + C`.

We package it (with the `max (m x) 0` summand absorbing the `A ≤ 0`
witness branch and the additive constant normalised to `1`) as the
explicit function `muAuxEnvelope`.  This block (child2a2-B) discharges
the **`L^{β̄}_per` membership** and pointwise non-negativity of that
envelope; the pointwise domination `μ ≤ muAuxEnvelope` (the full Young
reduction at the parametric upper bound) is the sibling task child2a2-A.

The exponent on `Du` is `α/β` (NOT `αt/β`): only this exponent lands in
`L^{β̄}_per` from the available `Du i ∈ L^{γ̄}_per`, since
`β̄ · (α/β) = γ̄ = α(β+1)/β` exactly. -/

/-- A local copy of the coordinatewise `MemLpPer` assembly for a vector
field given by its components, valid for any exponent `p`.

Adapted from `StationaryMFG.Congestion.congestion_memLpPer_pi_of_coord`
(itself adapted from `Hamiltonian.Estimates.memLpPer_pi_of_coord`); both
are `private`, so we re-derive the statement here.  For a family
`Du i ∈ L^p_per`, the assembled vector `x ↦ (fun i => Du i x)` is also
`L^p_per`, dominated coordinatewise by the sum of absolute values. -/
private theorem muIntegrability_pi_of_coord
    {p : ℝ≥0∞} (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hDu : ∀ i, MemLpPer (d := d) p (Du i)) :
    MemLpPer (d := d) p (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Du i x| with hDom_def
  have habs_memLp : ∀ i, MemLpPer (d := d) p (fun x => |Du i x|) := by
    intro i
    have h2 := (hDu i).toMemLp.norm
    have heq : (fun x => ‖Du i x‖) = fun x => |Du i x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h2
    exact MemLp.toMemLpPer h2
  have hDom_memLp : MemLpPer (d := d) p Dom := by
    have hsum :
        MemLp (fun x => ∑ i : Fin d, (fun x => |Du i x|) x) p
          (Measure.restrict volume (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (habs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖(fun i : Fin d => Du i x)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hsum_nn : 0 ≤ ∑ i, |Du i x| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpi : ‖(fun i : Fin d => Du i x)‖ ≤ ∑ i, |Du i x| := by
      rw [pi_norm_le_iff_of_nonneg hsum_nn]
      intro i
      have h1 : ‖Du i x‖ = |Du i x| := Real.norm_eq_abs _
      rw [h1]
      exact Finset.single_le_sum (f := fun j => |Du j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn, one_mul]
    exact hpi
  have hmeas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x)
        (Measure.restrict volume (UnitCube d)) := by
    have hAEm : AEMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x)
        (Measure.restrict volume (UnitCube d)) :=
      aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
    exact hAEm.aestronglyMeasurable
  exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)

/-! ## The Young τ-cancellation core (paper lines 1441–1448)

The heart of the pointwise envelope `μ ≤ G` is a *purely real-analytic*
Young inequality.  At the infimum `μ = muAux x` with `μ ≥ 1`, the HJB
constraint combined with the parametric congestion upper bound
`H ≤ K·(1/μ + 1/μ^τ)·(‖Du‖^{αt} + 1) − δ·μ^β` rearranges to

  `δ·μ^β ≤ K·(1/μ + 1/μ^τ)·(P + 1) + A`,   `P := ‖Du x‖^{αt}`, `A := u − V − k`.

Multiplying by `μ^τ` (using `μ ≥ 1`, `τ ≤ 1` so `μ^{τ-1} ≤ 1`) and applying
a *scaled* Young inequality with the Hölder-conjugate pair
`r = (β+τ)/β`, `s = (β+τ)/τ` to absorb the `μ^τ·A` term into the leading
`μ^{β+τ}` term yields the clean polynomial bound

  `μ^{β+τ} ≤ C₁·(P + 1) + C₂·|A|^{(β+τ)/β)}`

with constants `C₁, C₂` depending only on `K, δ, β, τ` (NOT on `μ, P, A`).
This is the genuinely load-bearing arithmetic; the final `^{1/(β+τ)}`
extraction (giving the exponent `αt/(β+τ) = α/β` on `Du`) is the sibling
assembly step. -/

/-- **Young τ-cancellation core** (paper lines 1441–1448).

For fixed exponents `0 < β`, `0 ≤ τ ≤ 1` and constants `0 < δ`, `0 < K`,
there exist nonnegative constants `C₁, C₂` such that for *every*
`μ ≥ 1`, `P ≥ 0`, `A : ℝ` satisfying the rearranged HJB bound

  `δ·μ^β ≤ K·(1/μ + 1/μ^τ)·(P + 1) + A`,

one has

  `μ^{β+τ} ≤ C₁·(P + 1) + C₂·|A|^{(β+τ)/β}`.

The constants are uniform in `(μ, P, A)`, so the per-`x` application in the
envelope assembly can pull them out front.  The proof multiplies the
hypothesis by `μ^τ`, uses `μ^{τ-1} ≤ 1` (from `μ ≥ 1`, `τ ≤ 1`), and applies
a scaled Mathlib `Real.young_inequality_of_nonneg` with conjugates
`(β+τ)/β` and `(β+τ)/τ` to absorb the `μ^τ·A` cross-term. -/
theorem young_tau_cancellation_core
    {β τ δ K : ℝ}
    (hβ : 0 < β) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hK : 0 < K) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ μ P A : ℝ, 1 ≤ μ → 0 ≤ P →
        δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A →
        μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
  -- The Hölder-conjugate pair `r = (β+τ)/β`, `s = (β+τ)/τ`.
  have hβτ_pos : 0 < β + τ := by linarith
  set r : ℝ := (β + τ) / β with hr_def
  set s : ℝ := (β + τ) / τ with hs_def
  have hr_pos : 0 < r := by rw [hr_def]; positivity
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hr_gt_one : 1 < r := by
    rw [hr_def]
    rw [lt_div_iff₀ hβ, one_mul]; linarith
  have hconj : r.HolderConjugate s := by
    rw [Real.holderConjugate_iff]
    refine ⟨hr_gt_one, ?_⟩
    rw [hr_def, hs_def]
    field_simp
  -- Scaling parameter `t > 0` chosen so the Young `μ^τ` term contributes
  -- coefficient `δ/2` on `μ^{β+τ}`.
  set t : ℝ := (2 / (δ * s)) ^ (1 / s) with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]; exact Real.rpow_pos_of_pos (by positivity) _
  -- `t^s = 2/(δ·s)`, so `1/(t^s · s) = δ/2`.
  have hts_eq : t ^ s = 2 / (δ * s) := by
    rw [ht_def, ← Real.rpow_mul (by positivity)]
    rw [show (1 / s) * s = 1 by field_simp, Real.rpow_one]
  -- The two output constants.
  refine ⟨4 * K / δ, (2 / δ) * (t ^ r / r), ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro μ P A hμ hP hHJB
  have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ
  have hP1_pos : 0 < P + 1 := by linarith
  have hμτ_pos : 0 < μ ^ τ := Real.rpow_pos_of_pos hμ_pos τ
  have hμβ_pos : 0 < μ ^ β := Real.rpow_pos_of_pos hμ_pos β
  -- Multiply the HJB bound by `μ^τ > 0`.
  have hmul : δ * μ ^ β * μ ^ τ
      ≤ (K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A) * μ ^ τ :=
    mul_le_mul_of_nonneg_right hHJB hμτ_pos.le
  -- `μ^β · μ^τ = μ^{β+τ}`.
  have hpow_add : μ ^ β * μ ^ τ = μ ^ (β + τ) := by
    rw [← Real.rpow_add hμ_pos]
  -- `(1/μ + 1/μ^τ) · μ^τ = μ^{τ-1} + 1 ≤ 2`.
  have hμτm1 : μ ^ (τ - 1) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hμ
    linarith
  have hcoef_le : ((1 / μ) + (1 / μ ^ τ)) * μ ^ τ ≤ 2 := by
    have e1 : (1 / μ) * μ ^ τ = μ ^ (τ - 1) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hμ_pos]
      congr 1; ring
    have e2 : (1 / μ ^ τ) * μ ^ τ = 1 := by
      field_simp
    have : ((1 / μ) + (1 / μ ^ τ)) * μ ^ τ
        = (1 / μ) * μ ^ τ + (1 / μ ^ τ) * μ ^ τ := by ring
    rw [this, e1, e2]
    linarith
  -- Combine: `δ·μ^{β+τ} ≤ 2K·(P+1) + A·μ^τ`.
  have hKnn : 0 ≤ K := hK.le
  have hstep1 : δ * μ ^ (β + τ) ≤ 2 * K * (P + 1) + A * μ ^ τ := by
    have hexp : (K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A) * μ ^ τ
        = K * (((1 / μ) + (1 / μ ^ τ)) * μ ^ τ) * (P + 1) + A * μ ^ τ := by
      ring
    rw [hexp] at hmul
    have hbound2 :
        K * (((1 / μ) + (1 / μ ^ τ)) * μ ^ τ) * (P + 1)
          ≤ K * 2 * (P + 1) := by
      apply mul_le_mul_of_nonneg_right _ hP1_pos.le
      exact mul_le_mul_of_nonneg_left hcoef_le hKnn
    have hlhs : δ * μ ^ β * μ ^ τ = δ * μ ^ (β + τ) := by
      rw [mul_assoc, hpow_add]
    rw [hlhs] at hmul
    calc δ * μ ^ (β + τ)
        ≤ K * (((1 / μ) + (1 / μ ^ τ)) * μ ^ τ) * (P + 1) + A * μ ^ τ := hmul
      _ ≤ K * 2 * (P + 1) + A * μ ^ τ := by linarith
      _ = 2 * K * (P + 1) + A * μ ^ τ := by ring
  -- Bound `A·μ^τ ≤ |A|·μ^τ` and apply scaled Young.
  have hAμ : A * μ ^ τ ≤ |A| * μ ^ τ :=
    mul_le_mul_of_nonneg_right (le_abs_self A) hμτ_pos.le
  -- Scaled Young on `(|A|·t)·(μ^τ / t)`.
  have hyoung := Real.young_inequality_of_nonneg
    (a := |A| * t) (b := μ ^ τ / t)
    (by positivity) (by positivity) hconj
  -- `(|A|·t)·(μ^τ/t) = |A|·μ^τ`.
  have hprod : (|A| * t) * (μ ^ τ / t) = |A| * μ ^ τ := by
    field_simp
  rw [hprod] at hyoung
  -- `(μ^τ/t)^s = μ^{β+τ} / t^s`, and `1/(t^s·s) = δ/2`.
  have hμτ_div_s : (μ ^ τ / t) ^ s = μ ^ (β + τ) / t ^ s := by
    rw [Real.div_rpow hμτ_pos.le ht_pos.le]
    congr 1
    rw [← Real.rpow_mul hμ_pos.le]
    congr 1
    rw [hs_def]; field_simp
  -- `(|A|·t)^r = |A|^r · t^r`.
  have hAt_r : (|A| * t) ^ r = |A| ^ r * t ^ r := by
    rw [Real.mul_rpow (abs_nonneg A) ht_pos.le]
  rw [hμτ_div_s, hAt_r] at hyoung
  -- So `|A|·μ^τ ≤ (|A|^r·t^r)/r + (μ^{β+τ}/t^s)/s`.
  -- The `μ^{β+τ}` coefficient is `1/(t^s·s) = δ/2`.
  have hcoef : (μ ^ (β + τ) / t ^ s) / s = (δ / 2) * μ ^ (β + τ) := by
    rw [hts_eq]
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ
    field_simp
  rw [hcoef] at hyoung
  -- Assemble: `δ·μ^{β+τ} ≤ 2K(P+1) + |A|^r·t^r/r + (δ/2)·μ^{β+τ}`.
  have hfinal : δ * μ ^ (β + τ)
      ≤ 2 * K * (P + 1) + (|A| ^ r * t ^ r / r + (δ / 2) * μ ^ (β + τ)) := by
    calc δ * μ ^ (β + τ)
        ≤ 2 * K * (P + 1) + A * μ ^ τ := hstep1
      _ ≤ 2 * K * (P + 1) + |A| * μ ^ τ := by linarith
      _ ≤ 2 * K * (P + 1)
            + (|A| ^ r * t ^ r / r + (δ / 2) * μ ^ (β + τ)) := by linarith
  -- Absorb `(δ/2)·μ^{β+τ}`: `(δ/2)·μ^{β+τ} ≤ 2K(P+1) + |A|^r·t^r/r`.
  have habsorb : (δ / 2) * μ ^ (β + τ)
      ≤ 2 * K * (P + 1) + |A| ^ r * t ^ r / r := by linarith
  -- Divide by `δ/2 > 0`: `μ^{β+τ} ≤ (4K/δ)(P+1) + (2/δ)·|A|^r·t^r/r`.
  have hμβτ_nn : 0 ≤ μ ^ (β + τ) := (Real.rpow_pos_of_pos hμ_pos _).le
  have hAr_nn : 0 ≤ |A| ^ r := Real.rpow_nonneg (abs_nonneg A) r
  -- Final inequality, matching the declared constants.
  have hgoal : μ ^ (β + τ)
      ≤ (4 * K / δ) * (P + 1) + ((2 / δ) * (t ^ r / r)) * |A| ^ ((β + τ) / β) := by
    have hrr : r = (β + τ) / β := hr_def
    have h2 : (2 / δ) * ((δ / 2) * μ ^ (β + τ)) = μ ^ (β + τ) := by
      field_simp
    have hmul2 : (2 / δ) * ((δ / 2) * μ ^ (β + τ))
        ≤ (2 / δ) * (2 * K * (P + 1) + |A| ^ r * t ^ r / r) :=
      mul_le_mul_of_nonneg_left habsorb (by positivity)
    rw [h2] at hmul2
    calc μ ^ (β + τ)
        ≤ (2 / δ) * (2 * K * (P + 1) + |A| ^ r * t ^ r / r) := hmul2
      _ = (4 * K / δ) * (P + 1) + ((2 / δ) * (t ^ r / r)) * |A| ^ r := by ring
      _ = (4 * K / δ) * (P + 1)
            + ((2 / δ) * (t ^ r / r)) * |A| ^ ((β + τ) / β) := by rw [hrr]
  exact hgoal

/-- The paper envelope for `μ` (paper line 1448), parametrised by a
non-negative constant `C` (which the sibling task supplies from
`H_upper_congestion_of_hmon`):

  `muAuxEnvelope C m u V Du α β x`
    `= C·‖Du(x)‖^{α/β} + C·(|u(x)| + |V(x)|)^{1/β} + 1 + max (m x) 0`.

The `+ 1 + max (m x) 0` summands absorb the additive constant and the
`A ≤ 0` witness branch (`max (m x) 1`) of `muAux_nonempty_of_large_bound`. -/
def muAuxEnvelope
    (C : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (α β : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x =>
    C * ‖(fun i => Du i x)‖ ^ (α / β)
      + C * (|u x| + |V x|) ^ (1 / β)
      + C + max (m x) 0

/-- The paper envelope is pointwise non-negative when `0 ≤ C`. -/
theorem muAuxEnvelope_nonneg
    {C : ℝ} (hC : 0 ≤ C)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {α β : ℝ} (x : Fin d → ℝ) :
    0 ≤ muAuxEnvelope C m u V Du α β x := by
  unfold muAuxEnvelope
  have h1 : 0 ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
    mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
  have h2 : 0 ≤ C * (|u x| + |V x|) ^ (1 / β) :=
    mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have h3 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
  linarith [hC]

set_option maxHeartbeats 800000 in
-- The `rpow`/`MemLp` assembly of four summands (each routed through the
-- Mathlib bridge `MemLpPer = MemLp`) plus the final `funext` collapse of
-- the pointwise sum to `muAuxEnvelope` exceeds the default heartbeat
-- budget; the bound here is comfortable headroom, not a sign of a stuck goal.
/-- **Paper line 1448 — the envelope `G` lies in `L^{β̄}_per`.**

With `β̄ = β + 1`, `β̄' = (β+1)/β`, `γ̄ = α(β+1)/β`, given the
membership certificates

* `hm_mem : m ∈ L^{β̄}_per`,
* `hu_mem : u ∈ L^{β̄'}_per`, `hV_mem : V ∈ L^{β̄'}_per`,
* `hDu_mem i : Du i ∈ L^{γ̄}_per`,

the paper envelope `muAuxEnvelope C m u V Du α β` lies in `L^{β̄}_per`.

The two `rpow` exponent identities are exact `ENNReal` facts:
`β̄·(α/β) = γ̄` and `β̄·(1/β) = β̄'`. -/
theorem muAuxEnvelope_memLp
    {C : ℝ}
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) (Du i)) :
    MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAuxEnvelope C m u V Du α β) := by
  set betaBar : ℝ≥0∞ := ENNReal.ofReal (β + 1) with hbetaBar
  -- (1) `‖Du‖^{α/β} ∈ L^{β̄}_per` via `rpow_closure`; `β̄·(α/β) = γ̄`.
  have hDu_vec :
      MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x) :=
    muIntegrability_pi_of_coord Du hDu_mem
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hαβ_pos : 0 < α / β := by positivity
  -- `‖Du‖^{α/β} ∈ L^{γ̄/(α/β)} = L^{β̄}` via vector-capable `MemLp.norm_rpow_div`.
  set qE : ℝ≥0∞ := ENNReal.ofReal (α / β) with hqE_def
  have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
  have hqE_toReal : qE.toReal = α / β := by
    rw [hqE_def]; exact ENNReal.toReal_ofReal hαβ_pos.le
  have hDu_rpow_div :
      MemLp (fun x : (Fin d → ℝ) =>
              ‖(fun i : Fin d => Du i x)‖ ^ qE.toReal)
            (ENNReal.ofReal (α * (β + 1) / β) / qE)
            (Measure.restrict volume (UnitCube d)) :=
    MemLp.norm_rpow_div hDu_vec.toMemLp qE
  -- `γ̄ / (α/β) = β̄ = β + 1`.
  have hdiv_real : α * (β + 1) / β / (α / β) = β + 1 := by
    have hαne : α ≠ 0 := ne_of_gt (lt_trans one_pos hα)
    field_simp
  have hdiv :
      ENNReal.ofReal (α * (β + 1) / β) / qE = betaBar := by
    rw [hqE_def, hbetaBar,
      ← ENNReal.ofReal_div_of_pos hαβ_pos, hdiv_real]
  have hDu_pow :
      MemLpPer (d := d) betaBar
        (fun x => ‖(fun i => Du i x)‖ ^ (α / β)) := by
    have h := hDu_rpow_div
    rw [hdiv, hqE_toReal] at h
    exact MemLp.toMemLpPer h
  -- (2) `(|u|+|V|)^{1/β} ∈ L^{β̄}_per` via `rpow_closure`; `β̄·(1/β) = β̄'`.
  have huabs : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hsum : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => |u x| + |V x|) := huabs.add hVabs
  have hexp_uV :
      betaBar * ENNReal.ofReal (1 / β) = ENNReal.ofReal ((β + 1) / β) := by
    rw [hbetaBar, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_one_div]
  have hβinv_pos : 0 < 1 / β := by positivity
  have huV_pow_norm :
      MemLpPer (d := d) betaBar
        (fun x => ‖(|u x| + |V x|)‖ ^ (1 / β)) :=
    MemLpPer.rpow_closure (d := d) hβinv_pos (by rw [hexp_uV]; exact hsum)
  have huV_pow :
      MemLpPer (d := d) betaBar
        (fun x => (|u x| + |V x|) ^ (1 / β)) := by
    have heq : (fun x => ‖(|u x| + |V x|)‖ ^ (1 / β))
        = (fun x => (|u x| + |V x|) ^ (1 / β)) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rwa [heq] at huV_pow_norm
  -- (3) `max (m x) 0 ∈ L^{β̄}_per` via `MemLp.pos_part`.
  have hmax : MemLpPer (d := d) betaBar (fun x => max (m x) 0) :=
    MemLp.toMemLpPer hm_mem.toMemLp.pos_part
  -- (4) constant `C ∈ L^{β̄}_per`.
  have hone : MemLpPer (d := d) betaBar (fun _ : (Fin d → ℝ) => (C : ℝ)) :=
    MemLpPer.const (d := d) (C : ℝ)
  -- Assemble: `C·(…) + C·(…) + 1 + max (m x) 0`.
  have hCDu : MemLpPer (d := d) betaBar
      (fun x => C * ‖(fun i => Du i x)‖ ^ (α / β)) := by
    have := hDu_pow.const_smul (𝕜 := ℝ) C
    have heq : (C • fun x => ‖(fun i => Du i x)‖ ^ (α / β))
        = fun x => C * ‖(fun i => Du i x)‖ ^ (α / β) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  have hCuV : MemLpPer (d := d) betaBar
      (fun x => C * (|u x| + |V x|) ^ (1 / β)) := by
    have := huV_pow.const_smul (𝕜 := ℝ) C
    have heq : (C • fun x => (|u x| + |V x|) ^ (1 / β))
        = fun x => C * (|u x| + |V x|) ^ (1 / β) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  have hfinal := ((hCDu.add hCuV).add hone).add hmax
  have heq : ((fun x => C * ‖(fun i => Du i x)‖ ^ (α / β))
        + (fun x => C * (|u x| + |V x|) ^ (1 / β))
        + (fun _ : (Fin d → ℝ) => (C : ℝ))
        + (fun x => max (m x) 0))
      = muAuxEnvelope C m u V Du α β := by
    funext x
    simp only [Pi.add_apply, muAuxEnvelope]
  rwa [heq] at hfinal

/-- **`rpow` subadditivity** with a constant factor (paper line 1448
splitting step): for `0 ≤ s` and `0 ≤ a, b`,

  `(a + b) ^ s ≤ 2 ^ s · (a ^ s + b ^ s)`.

Proof: `(a+b)^s ≤ (2·max a b)^s = 2^s·(max a b)^s ≤ 2^s·(a^s + b^s)`, where
the last step uses `(max a b)^s ≤ a^s + b^s` (one of the two `rpow`s equals
`(max a b)^s`, the other is `≥ 0`). Reproved locally (the analogous
`Apriori` helper is private). -/
private lemma rpow_add_two_le {s a b : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ s ≤ 2 ^ s * (a ^ s + b ^ s) := by
  have ha_s : (0 : ℝ) ≤ a ^ s := Real.rpow_nonneg ha s
  have hb_s : (0 : ℝ) ≤ b ^ s := Real.rpow_nonneg hb s
  -- `(max a b) ^ s ≤ a ^ s + b ^ s`.
  have hmax_s : (max a b) ^ s ≤ a ^ s + b ^ s := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  -- `(a + b) ^ s ≤ (2 · max a b) ^ s`.
  have hab_le : a + b ≤ 2 * max a b := by
    have h1 : a ≤ max a b := le_max_left _ _
    have h2 : b ≤ max a b := le_max_right _ _
    linarith
  have hab_nn : (0 : ℝ) ≤ a + b := by linarith
  calc (a + b) ^ s
      ≤ (2 * max a b) ^ s := Real.rpow_le_rpow hab_nn hab_le hs
    _ = 2 ^ s * (max a b) ^ s := by
        rw [Real.mul_rpow (by norm_num) (le_trans ha (le_max_left _ _))]
    _ ≤ 2 ^ s * (a ^ s + b ^ s) := by
        have h2s : (0 : ℝ) ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
        exact mul_le_mul_of_nonneg_left hmax_s h2s

/-- **Paper line 1448 — pointwise envelope bound `μ ≤ G`.**

Assembles `H_upper_congestion_of_hmon` (the parametric upper bound on `H`)
and `young_tau_cancellation_core` (the Young τ-cancellation arithmetic core)
into the pointwise envelope `muAux ≤ muAuxEnvelope C …` that feeds
`muAux_mem_Lp` (with `G := muAuxEnvelope C …`, certified `MemLpPer` by
`muAuxEnvelope_memLp`).

`hcont` (continuity of `H(x, Du x, ·)` over all of `ℝ`, including `μ ≤ 0`)
is taken as an a.e. hypothesis: it is **not** derivable from
`hmon`/`hcong` (`RegularityH.continuous_H_pm` only gives continuity for
`m > 0`), and every sibling lemma (`muAux_levelSet_ae`, …) takes it the
same way.

The key exponent match is `α(1 + τ/β)/(β + τ) = α/β`, discharged inline. -/
theorem muAux_le_envelope_of_congestionGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon  : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        muAux k m u V Du H x
          ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x := by
  -- Bundle data and the parametric `H` upper bound.
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hβ : 0 < β := hcong.hβ
  have hα : 1 < α := hcong.hα
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ1 : τ ≤ 1 := hcong.hτ.2
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβτ_pos : 0 < β + τ := by linarith
  have hβτ_ne : β + τ ≠ 0 := ne_of_gt hβτ_pos
  obtain ⟨K, δ, hK, hδ, hH_upper⟩ := H_upper_congestion_of_hmon hmon hcong
  -- `H_upper` is stated with `hcong.{α,β,τ}`; rewrite to our `set` names.
  have hH_upper' :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ K * ((1 / mm) + (1 / mm ^ τ)) * (‖p‖ ^ αt + 1)
                    - δ * mm ^ β := by
    filter_upwards [hH_upper] with x hx
    intro p mm hmm
    exact hx p mm hmm
  -- The exponent identities.
  have hαt_s : αt * (1 / (β + τ)) = α / β := by
    rw [hαtdef]; field_simp
  have hq_s : ((β + τ) / β) * (1 / (β + τ)) = 1 / β := by
    field_simp
  -- The Young core (uniform constants), unified across `τ = 0`/`τ > 0`.
  set s : ℝ := 1 / (β + τ) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_nn : 0 ≤ s := hs_pos.le
  obtain ⟨C₁, C₂, hC₁, hC₂, hcore⟩ :
      ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
        ∀ μ P A : ℝ, 1 ≤ μ → 0 ≤ P →
          δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A →
          μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
    rcases eq_or_lt_of_le hτ_nn with hτ0 | hτpos
    · -- `τ = 0`: `μ^τ = 1`, no Young needed.
      refine ⟨2 * K / δ, 1 / δ, by positivity, by positivity, ?_⟩
      intro μ P A hμ hP hHJB
      have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ
      have hμτ1 : μ ^ τ = 1 := by rw [← hτ0]; exact Real.rpow_zero μ
      have hinvμ_le : 1 / μ ≤ 1 := by
        rw [div_le_one hμ_pos]; exact hμ
      have hcoef : (1 / μ) + (1 / μ ^ τ) ≤ 2 := by
        rw [hμτ1, div_one]; linarith
      have hP1_nn : (0 : ℝ) ≤ P + 1 := by linarith
      have hstep : δ * μ ^ β ≤ K * 2 * (P + 1) + A := by
        have h1 : K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1)
            ≤ K * 2 * (P + 1) := by
          apply mul_le_mul_of_nonneg_right _ hP1_nn
          exact mul_le_mul_of_nonneg_left hcoef hK.le
        linarith
      have hβτ_eq : β + τ = β := by rw [← hτ0]; ring
      have hqexp : (β + τ) / β = 1 := by rw [hβτ_eq]; field_simp
      rw [hqexp, Real.rpow_one, hβτ_eq]
      have hA_le : A ≤ |A| := le_abs_self A
      have h2 : δ * μ ^ β ≤ 2 * K * (P + 1) + |A| := by linarith
      -- Divide by `δ > 0`.
      have hμβ_le : μ ^ β ≤ (2 * K / δ) * (P + 1) + (1 / δ) * |A| := by
        have hδinv : 0 < 1 / δ := by positivity
        have := mul_le_mul_of_nonneg_left h2 hδinv.le
        rw [show (1 / δ) * (δ * μ ^ β) = μ ^ β by field_simp] at this
        calc μ ^ β
            ≤ (1 / δ) * (2 * K * (P + 1) + |A|) := this
          _ = (2 * K / δ) * (P + 1) + (1 / δ) * |A| := by ring
      exact hμβ_le
    · -- `τ > 0`: the landed core.
      exact young_tau_cancellation_core hβ hτpos hτ1 hδ hK
  -- The final envelope constant: dominates all three sub-coefficients.
  set B1 : ℝ := 2 ^ s * C₁ ^ s * 2 ^ s with hB1_def
  set B2 : ℝ := 2 ^ s * C₂ ^ s * 2 ^ ((1 : ℝ) / β) with hB2_def
  set B3 : ℝ := 2 ^ s * C₁ ^ s * 2 ^ s
                  + 2 ^ s * C₂ ^ s * 2 ^ ((1 : ℝ) / β) * |k| ^ ((1 : ℝ) / β)
                with hB3_def
  have hB1_nn : 0 ≤ B1 := by rw [hB1_def]; positivity
  have hB2_nn : 0 ≤ B2 := by rw [hB2_def]; positivity
  have hB3_nn : 0 ≤ B3 := by rw [hB3_def]; positivity
  refine ⟨max B1 (max B2 (max B3 1)), ?_, ?_⟩
  · exact le_trans hB1_nn (le_max_left _ _)
  set C : ℝ := max B1 (max B2 (max B3 1)) with hC_def
  have hC_ge_B1 : B1 ≤ C := le_max_left _ _
  have hC_ge_B2 : B2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_ge_B3 : B3 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC_ge_one : (1 : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC_nn : 0 ≤ C := le_trans (by norm_num) hC_ge_one
  -- Per-`x` assembly.
  filter_upwards [hH_upper', hcont, hne] with x hHu_x hcont_x hne_x
  -- `μ := muAux x` lies in `muAuxSet`.
  have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
    muAuxSet_isClosed hcont_x
  have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
    muAuxSet_bddBelow k m u V Du H x
  have h_mem : muAux k m u V Du H x ∈ muAuxSet k m u V Du H x :=
    h_closed.csInf_mem hne_x h_bdd
  set μ : ℝ := muAux k m u V Du H x with hμ_def
  obtain ⟨hμ_nn, hmle, hHJB⟩ := h_mem
  -- Envelope is `≥ C ≥ 1`, used for the small-`μ` branch.
  have hEnv_ge_C : C ≤ muAuxEnvelope C m u V Du α β x := by
    unfold muAuxEnvelope
    have h1 : (0 : ℝ) ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : (0 : ℝ) ≤ C * (|u x| + |V x|) ^ (1 / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by positivity) _)
    have h3 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
    linarith
  -- Envelope dominates `max (m x) 0`.
  have hEnv_ge_max : max (m x) 0 ≤ muAuxEnvelope C m u V Du α β x := by
    unfold muAuxEnvelope
    have h1 : (0 : ℝ) ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : (0 : ℝ) ≤ C * (|u x| + |V x|) ^ (1 / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by positivity) _)
    linarith [hC_nn]
  rcases le_or_gt μ 1 with hμ_le1 | hμ_gt1
  · -- Small `μ`: `μ ≤ 1 ≤ C ≤ envelope`.
    exact le_trans hμ_le1 (le_trans hC_ge_one hEnv_ge_C)
  · -- `μ > 1`: apply the upper bound + Young core.
    have hμ_ge1 : (1 : ℝ) ≤ μ := hμ_gt1.le
    have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ_ge1
    -- If `μ = m x`, the `max (m x) 0` summand absorbs it directly.
    rcases le_or_gt μ (m x) with hμ_lem | hμ_gtm
    · have hμ_eq_m : μ = m x := le_antisymm hμ_lem hmle
      have : μ ≤ max (m x) 0 := by rw [hμ_eq_m]; exact le_max_left _ _
      exact le_trans this hEnv_ge_max
    -- Otherwise `μ > m x`: the HJB constraint is tight at the infimum.
    have htight : k ≤ u x + H x (fun i => Du i x) μ - V x := by
      by_contra hlt
      push_neg at hlt
      -- `g ν := u x + H x (Du x) ν - V x` is continuous, `g μ < k`.
      set g : ℝ → ℝ := fun ν => u x + H x (fun i => Du i x) ν - V x with hg_def
      have hg_cont : Continuous g :=
        (continuous_const.add hcont_x).sub continuous_const
      have hgμ : g μ < k := hlt
      -- Continuity gives a `δ₀`-ball around `μ` where `g < k`.
      have hpre : IsOpen (g ⁻¹' Set.Iio k) := hg_cont.isOpen_preimage _ isOpen_Iio
      have hμ_pre : μ ∈ g ⁻¹' Set.Iio k := hgμ
      obtain ⟨δ₀, hδ₀_pos, hball⟩ := Metric.isOpen_iff.mp hpre μ hμ_pre
      -- Choose `ν < μ` close to `μ`, still `≥ m x` and `≥ 0`.
      set ν : ℝ := max (max (m x) 0) (μ - δ₀ / 2) with hν_def
      have hν_lt : ν < μ := by
        rw [hν_def]
        apply max_lt
        · exact max_lt hμ_gtm hμ_pos
        · linarith
      have hν_ge_mx0 : max (m x) 0 ≤ ν := le_max_left _ _
      have hν_ge_m : m x ≤ ν := le_trans (le_max_left _ _) hν_ge_mx0
      have hν_nn : 0 ≤ ν := le_trans (le_max_right _ _) hν_ge_mx0
      have hν_gt : μ - δ₀ / 2 ≤ ν := le_max_right _ _
      -- `ν ∈ ball μ δ₀`, hence `g ν < k`.
      have hν_ball : ν ∈ Metric.ball μ δ₀ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith
        · linarith
      have hgν : g ν < k := hball hν_ball
      -- So `ν ∈ muAuxSet`, contradicting `μ = sInf`.
      have hν_mem : ν ∈ muAuxSet k m u V Du H x :=
        ⟨hν_nn, hν_ge_m, le_of_lt hgν⟩
      have hμ_le_ν : muAux k m u V Du H x ≤ ν :=
        csInf_le h_bdd hν_mem
      rw [← hμ_def] at hμ_le_ν
      linarith
    -- Abbreviations.
    set P : ℝ := ‖(fun i => Du i x)‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    set A : ℝ := u x - V x - k with hA_def
    -- `H` upper bound at `(Du x, μ)`.
    have hHbd : H x (fun i => Du i x) μ
        ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) - δ * μ ^ β :=
      hHu_x (fun i => Du i x) μ hμ_pos
    -- Tightness `k ≤ u + H − V` + the upper bound give the Young hypothesis.
    have hHJB_rearr :
        δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A := by
      have hAeq : A = u x - V x - k := hA_def
      linarith [hHbd, htight, hAeq]
    -- The Young core.
    have hcore_x :
        μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) :=
      hcore μ P A hμ_ge1 hP_nn hHJB_rearr
    -- Take `^ s`, `s = 1/(β+τ)`, to recover `μ`.
    have hμ_eq : μ = (μ ^ (β + τ)) ^ s := by
      rw [hs_def, ← Real.rpow_mul hμ_pos.le]
      rw [mul_one_div, div_self hβτ_ne, Real.rpow_one]
    have hrhs_nn : 0 ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
      have ht1 : (0 : ℝ) ≤ C₁ * (P + 1) := by positivity
      have ht2 : (0 : ℝ) ≤ C₂ * |A| ^ ((β + τ) / β) := by positivity
      linarith
    have hμ_le_rpow :
        μ ≤ (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s := by
      rw [hμ_eq]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hμ_pos.le _) hcore_x hs_nn
    -- Split the two summands of the base.
    have hsplit1 :
        (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s
          ≤ 2 ^ s * ((C₁ * (P + 1)) ^ s
              + (C₂ * |A| ^ ((β + τ) / β)) ^ s) :=
      rpow_add_two_le hs_nn (by positivity) (by positivity)
    -- `(C₁(P+1))^s = C₁^s (P+1)^s ≤ C₁^s 2^s (P^s + 1)`.
    have hPexpand : (C₁ * (P + 1)) ^ s
        ≤ C₁ ^ s * (2 ^ s * (P ^ s + 1)) := by
      have he1 : (C₁ * (P + 1)) ^ s = C₁ ^ s * (P + 1) ^ s :=
        Real.mul_rpow hC₁ (by linarith)
      rw [he1]
      have he2 : (P + 1) ^ s ≤ 2 ^ s * (P ^ s + 1 ^ s) :=
        rpow_add_two_le hs_nn hP_nn (by norm_num)
      rw [Real.one_rpow] at he2
      have hC₁s_nn : (0 : ℝ) ≤ C₁ ^ s := Real.rpow_nonneg hC₁ s
      exact mul_le_mul_of_nonneg_left he2 hC₁s_nn
    -- `P^s = ‖Du x‖^{α/β}`.
    have hP_s : P ^ s = ‖(fun i => Du i x)‖ ^ (α / β) := by
      rw [hP_def, ← Real.rpow_mul (norm_nonneg _), hs_def, hαt_s]
    -- `(C₂|A|^q)^s = C₂^s |A|^{1/β}`.
    have hAexpand : (C₂ * |A| ^ ((β + τ) / β)) ^ s
        = C₂ ^ s * |A| ^ ((1 : ℝ) / β) := by
      rw [Real.mul_rpow hC₂ (Real.rpow_nonneg (abs_nonneg _) _),
          ← Real.rpow_mul (abs_nonneg _), hs_def, hq_s]
    -- `|A|^{1/β} ≤ (|u|+|V|+|k|)^{1/β} ≤ 2^{1/β}((|u|+|V|)^{1/β}+|k|^{1/β})`.
    have hβinv_nn : (0 : ℝ) ≤ 1 / β := by positivity
    have hA_abs_le : |A| ≤ |u x| + |V x| + |k| := by
      have huv : |u x - V x| ≤ |u x| + |V x| := by
        have h := abs_add_le (u x) (-(V x))
        rw [abs_neg] at h
        rw [sub_eq_add_neg]; exact h
      have hk : |u x - V x - k| ≤ |u x - V x| + |k| := by
        have h := abs_add_le (u x - V x) (-k)
        rw [abs_neg] at h
        rw [show u x - V x - k = (u x - V x) + (-k) by ring]; exact h
      rw [hA_def]; linarith
    have hAbound : |A| ^ ((1 : ℝ) / β)
        ≤ 2 ^ ((1 : ℝ) / β)
            * ((|u x| + |V x|) ^ ((1 : ℝ) / β) + |k| ^ ((1 : ℝ) / β)) := by
      have hstep1 : |A| ^ ((1 : ℝ) / β)
          ≤ (|u x| + |V x| + |k|) ^ ((1 : ℝ) / β) :=
        Real.rpow_le_rpow (abs_nonneg _) hA_abs_le hβinv_nn
      have hstep2 : (|u x| + |V x| + |k|) ^ ((1 : ℝ) / β)
          ≤ 2 ^ ((1 : ℝ) / β)
              * ((|u x| + |V x|) ^ ((1 : ℝ) / β) + |k| ^ ((1 : ℝ) / β)) :=
        rpow_add_two_le hβinv_nn (by positivity) (abs_nonneg _)
      linarith
    -- Now assemble the chain to `B1·X + B2·Y + B3`.
    set X : ℝ := ‖(fun i => Du i x)‖ ^ (α / β) with hX_def
    set Y : ℝ := (|u x| + |V x|) ^ ((1 : ℝ) / β) with hY_def
    have hX_nn : 0 ≤ X := Real.rpow_nonneg (norm_nonneg _) _
    have hY_nn : 0 ≤ Y := Real.rpow_nonneg (by positivity) _
    have h2s_nn : (0 : ℝ) ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
    have hC₂s_nn : (0 : ℝ) ≤ C₂ ^ s := Real.rpow_nonneg hC₂ s
    have hk_nn : (0 : ℝ) ≤ |k| ^ ((1 : ℝ) / β) :=
      Real.rpow_nonneg (abs_nonneg _) _
    -- Combine `hsplit1`, `hPexpand`, `hP_s`, `hAexpand`, `hAbound`.
    have hchain : μ ≤ B1 * X + B2 * Y + B3 := by
      have hA_term :
          (C₂ * |A| ^ ((β + τ) / β)) ^ s
            ≤ C₂ ^ s * (2 ^ ((1 : ℝ) / β) * (Y + |k| ^ ((1 : ℝ) / β))) := by
        rw [hAexpand]
        rw [hY_def]
        exact mul_le_mul_of_nonneg_left hAbound hC₂s_nn
      have hP_term :
          (C₁ * (P + 1)) ^ s ≤ C₁ ^ s * (2 ^ s * (X + 1)) := by
        rw [← hP_s]; exact hPexpand
      calc μ
          ≤ (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s := hμ_le_rpow
        _ ≤ 2 ^ s * ((C₁ * (P + 1)) ^ s
              + (C₂ * |A| ^ ((β + τ) / β)) ^ s) := hsplit1
        _ ≤ 2 ^ s * (C₁ ^ s * (2 ^ s * (X + 1))
              + C₂ ^ s * (2 ^ ((1 : ℝ) / β) * (Y + |k| ^ ((1 : ℝ) / β)))) := by
            apply mul_le_mul_of_nonneg_left _ h2s_nn
            linarith
        _ = B1 * X + B2 * Y + B3 := by
            rw [hB1_def, hB2_def, hB3_def]; ring
    -- Dominate by the envelope.
    have hfinal : B1 * X + B2 * Y + B3
        ≤ muAuxEnvelope C m u V Du α β x := by
      have henv : muAuxEnvelope C m u V Du α β x
          = C * X + C * Y + C + max (m x) 0 := by
        rw [hX_def, hY_def]; rfl
      rw [henv]
      have e1 : B1 * X ≤ C * X := mul_le_mul_of_nonneg_right hC_ge_B1 hX_nn
      have e2 : B2 * Y ≤ C * Y := mul_le_mul_of_nonneg_right hC_ge_B2 hY_nn
      have e3 : B3 ≤ C := hC_ge_B3
      have e4 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
      linarith
    exact le_trans hchain hfinal

/-- **Positive-witness sibling of `muAux_le_envelope_of_congestionGrowth`**
(paper line 1448 on the a.e. set `{0 < m x}`).

Identical conclusion (`muAux ≤ muAuxEnvelope C …` a.e.), but the standing
continuity hypothesis is weakened from full-`ℝ` `Continuous` to
`ContinuousOn (Set.Ioi 0)`, at the cost of the extra a.e. positivity witness
`hm_pos : 0 < m x`. Sound because on `{0 < m x}` the infimum `μ x ≥ m x > 0`
and every admissible candidate is `≥ m x > 0`, so the closedness/tightness
arguments only ever evaluate `H(x, Du x, ·)` on the open half-line `(0,∞)`.
Routes closedness through `muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos`
and rebuilds the tightness contradiction with the `ContinuousWithinAt`→`nhds`
trick of `muAux_product_identity_of_m_pos`. The original is kept untouched. -/
theorem muAux_le_envelope_of_congestionGrowth_of_m_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        muAux k m u V Du H x
          ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x := by
  -- Bundle data and the parametric `H` upper bound.
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hβ : 0 < β := hcong.hβ
  have hα : 1 < α := hcong.hα
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ1 : τ ≤ 1 := hcong.hτ.2
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβτ_pos : 0 < β + τ := by linarith
  have hβτ_ne : β + τ ≠ 0 := ne_of_gt hβτ_pos
  obtain ⟨K, δ, hK, hδ, hH_upper⟩ := H_upper_congestion_of_hmon hmon hcong
  -- `H_upper` is stated with `hcong.{α,β,τ}`; rewrite to our `set` names.
  have hH_upper' :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ K * ((1 / mm) + (1 / mm ^ τ)) * (‖p‖ ^ αt + 1)
                    - δ * mm ^ β := by
    filter_upwards [hH_upper] with x hx
    intro p mm hmm
    exact hx p mm hmm
  -- The exponent identities.
  have hαt_s : αt * (1 / (β + τ)) = α / β := by
    rw [hαtdef]; field_simp
  have hq_s : ((β + τ) / β) * (1 / (β + τ)) = 1 / β := by
    field_simp
  -- The Young core (uniform constants), unified across `τ = 0`/`τ > 0`.
  set s : ℝ := 1 / (β + τ) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_nn : 0 ≤ s := hs_pos.le
  obtain ⟨C₁, C₂, hC₁, hC₂, hcore⟩ :
      ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
        ∀ μ P A : ℝ, 1 ≤ μ → 0 ≤ P →
          δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A →
          μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
    rcases eq_or_lt_of_le hτ_nn with hτ0 | hτpos
    · -- `τ = 0`: `μ^τ = 1`, no Young needed.
      refine ⟨2 * K / δ, 1 / δ, by positivity, by positivity, ?_⟩
      intro μ P A hμ hP hHJB
      have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ
      have hμτ1 : μ ^ τ = 1 := by rw [← hτ0]; exact Real.rpow_zero μ
      have hinvμ_le : 1 / μ ≤ 1 := by
        rw [div_le_one hμ_pos]; exact hμ
      have hcoef : (1 / μ) + (1 / μ ^ τ) ≤ 2 := by
        rw [hμτ1, div_one]; linarith
      have hP1_nn : (0 : ℝ) ≤ P + 1 := by linarith
      have hstep : δ * μ ^ β ≤ K * 2 * (P + 1) + A := by
        have h1 : K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1)
            ≤ K * 2 * (P + 1) := by
          apply mul_le_mul_of_nonneg_right _ hP1_nn
          exact mul_le_mul_of_nonneg_left hcoef hK.le
        linarith
      have hβτ_eq : β + τ = β := by rw [← hτ0]; ring
      have hqexp : (β + τ) / β = 1 := by rw [hβτ_eq]; field_simp
      rw [hqexp, Real.rpow_one, hβτ_eq]
      have hA_le : A ≤ |A| := le_abs_self A
      have h2 : δ * μ ^ β ≤ 2 * K * (P + 1) + |A| := by linarith
      -- Divide by `δ > 0`.
      have hμβ_le : μ ^ β ≤ (2 * K / δ) * (P + 1) + (1 / δ) * |A| := by
        have hδinv : 0 < 1 / δ := by positivity
        have := mul_le_mul_of_nonneg_left h2 hδinv.le
        rw [show (1 / δ) * (δ * μ ^ β) = μ ^ β by field_simp] at this
        calc μ ^ β
            ≤ (1 / δ) * (2 * K * (P + 1) + |A|) := this
          _ = (2 * K / δ) * (P + 1) + (1 / δ) * |A| := by ring
      exact hμβ_le
    · -- `τ > 0`: the landed core.
      exact young_tau_cancellation_core hβ hτpos hτ1 hδ hK
  -- The final envelope constant: dominates all three sub-coefficients.
  set B1 : ℝ := 2 ^ s * C₁ ^ s * 2 ^ s with hB1_def
  set B2 : ℝ := 2 ^ s * C₂ ^ s * 2 ^ ((1 : ℝ) / β) with hB2_def
  set B3 : ℝ := 2 ^ s * C₁ ^ s * 2 ^ s
                  + 2 ^ s * C₂ ^ s * 2 ^ ((1 : ℝ) / β) * |k| ^ ((1 : ℝ) / β)
                with hB3_def
  have hB1_nn : 0 ≤ B1 := by rw [hB1_def]; positivity
  have hB2_nn : 0 ≤ B2 := by rw [hB2_def]; positivity
  have hB3_nn : 0 ≤ B3 := by rw [hB3_def]; positivity
  refine ⟨max B1 (max B2 (max B3 1)), ?_, ?_⟩
  · exact le_trans hB1_nn (le_max_left _ _)
  set C : ℝ := max B1 (max B2 (max B3 1)) with hC_def
  have hC_ge_B1 : B1 ≤ C := le_max_left _ _
  have hC_ge_B2 : B2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_ge_B3 : B3 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC_ge_one : (1 : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC_nn : 0 ≤ C := le_trans (by norm_num) hC_ge_one
  -- Per-`x` assembly (now also carrying `hmx : 0 < m x`).
  filter_upwards [hH_upper', hcont, hne, hm_pos]
    with x hHu_x hcont_x hne_x hmx
  -- `μ := muAux x` lies in `muAuxSet`. Closedness via the on-`(0,∞)` sibling.
  have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
    muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hmx hcont_x
  have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
    muAuxSet_bddBelow k m u V Du H x
  have h_mem : muAux k m u V Du H x ∈ muAuxSet k m u V Du H x :=
    h_closed.csInf_mem hne_x h_bdd
  set μ : ℝ := muAux k m u V Du H x with hμ_def
  obtain ⟨hμ_nn, hmle, hHJB⟩ := h_mem
  -- Envelope is `≥ C ≥ 1`, used for the small-`μ` branch.
  have hEnv_ge_C : C ≤ muAuxEnvelope C m u V Du α β x := by
    unfold muAuxEnvelope
    have h1 : (0 : ℝ) ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : (0 : ℝ) ≤ C * (|u x| + |V x|) ^ (1 / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by positivity) _)
    have h3 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
    linarith
  -- Envelope dominates `max (m x) 0`.
  have hEnv_ge_max : max (m x) 0 ≤ muAuxEnvelope C m u V Du α β x := by
    unfold muAuxEnvelope
    have h1 : (0 : ℝ) ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : (0 : ℝ) ≤ C * (|u x| + |V x|) ^ (1 / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by positivity) _)
    linarith [hC_nn]
  rcases le_or_gt μ 1 with hμ_le1 | hμ_gt1
  · -- Small `μ`: `μ ≤ 1 ≤ C ≤ envelope`.
    exact le_trans hμ_le1 (le_trans hC_ge_one hEnv_ge_C)
  · -- `μ > 1`: apply the upper bound + Young core.
    have hμ_ge1 : (1 : ℝ) ≤ μ := hμ_gt1.le
    have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ_ge1
    -- If `μ = m x`, the `max (m x) 0` summand absorbs it directly.
    rcases le_or_gt μ (m x) with hμ_lem | hμ_gtm
    · have hμ_eq_m : μ = m x := le_antisymm hμ_lem hmle
      have : μ ≤ max (m x) 0 := by rw [hμ_eq_m]; exact le_max_left _ _
      exact le_trans this hEnv_ge_max
    -- Otherwise `μ > m x`: the HJB constraint is tight at the infimum.
    have htight : k ≤ u x + H x (fun i => Du i x) μ - V x := by
      by_contra hlt
      push_neg at hlt
      -- `g ν := u x + H x (Du x) ν - V x` is continuous *on `Ioi 0`*, `g μ < k`.
      set g : ℝ → ℝ := fun ν => u x + H x (fun i => Du i x) ν - V x with hg_def
      have hg_contOn : ContinuousOn g (Set.Ioi 0) :=
        (continuousOn_const.add hcont_x).sub continuousOn_const
      have hgμ : g μ < k := hlt
      -- `μ ∈ Ioi 0` (since `μ > m x > 0`), so the relative preimage of `Iio k`
      -- intersected with the open `Ioi 0` is a genuine neighbourhood of `μ`.
      have hμ_mem_Ioi : μ ∈ Set.Ioi (0 : ℝ) := hμ_pos
      have h_cont_at : ContinuousWithinAt g (Set.Ioi 0) μ :=
        hg_contOn μ hμ_mem_Ioi
      have h_cont_at' : ContinuousAt g μ :=
        h_cont_at.continuousAt (isOpen_Ioi.mem_nhds hμ_mem_Ioi)
      have hpre_nhds : g ⁻¹' Set.Iio k ∈ nhds μ :=
        h_cont_at'.preimage_mem_nhds (isOpen_Iio.mem_nhds hgμ)
      have hIoi_nhds : Set.Ioi (0 : ℝ) ∈ nhds μ :=
        isOpen_Ioi.mem_nhds hμ_mem_Ioi
      have hball_nhds : (g ⁻¹' Set.Iio k) ∩ Set.Ioi 0 ∈ nhds μ :=
        Filter.inter_mem hpre_nhds hIoi_nhds
      obtain ⟨δ₀, hδ₀_pos, hball⟩ := Metric.mem_nhds_iff.mp hball_nhds
      -- Choose `ν < μ` close to `μ`, still `≥ m x` and `≥ 0`.
      set ν : ℝ := max (max (m x) 0) (μ - δ₀ / 2) with hν_def
      have hν_lt : ν < μ := by
        rw [hν_def]
        apply max_lt
        · exact max_lt hμ_gtm hμ_pos
        · linarith
      have hν_ge_mx0 : max (m x) 0 ≤ ν := le_max_left _ _
      have hν_ge_m : m x ≤ ν := le_trans (le_max_left _ _) hν_ge_mx0
      have hν_nn : 0 ≤ ν := le_trans (le_max_right _ _) hν_ge_mx0
      have hν_gt : μ - δ₀ / 2 ≤ ν := le_max_right _ _
      -- `ν ∈ ball μ δ₀`, hence `ν ∈ {g < k} ∩ Ioi 0`.
      have hν_ball : ν ∈ Metric.ball μ δ₀ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith
        · linarith
      have hν_in : ν ∈ (g ⁻¹' Set.Iio k) ∩ Set.Ioi 0 := hball hν_ball
      have hgν : g ν < k := hν_in.1
      -- So `ν ∈ muAuxSet`, contradicting `μ = sInf`.
      have hν_mem : ν ∈ muAuxSet k m u V Du H x :=
        ⟨hν_nn, hν_ge_m, le_of_lt hgν⟩
      have hμ_le_ν : muAux k m u V Du H x ≤ ν :=
        csInf_le h_bdd hν_mem
      rw [← hμ_def] at hμ_le_ν
      linarith
    -- Abbreviations.
    set P : ℝ := ‖(fun i => Du i x)‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    set A : ℝ := u x - V x - k with hA_def
    -- `H` upper bound at `(Du x, μ)`.
    have hHbd : H x (fun i => Du i x) μ
        ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) - δ * μ ^ β :=
      hHu_x (fun i => Du i x) μ hμ_pos
    -- Tightness `k ≤ u + H − V` + the upper bound give the Young hypothesis.
    have hHJB_rearr :
        δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A := by
      have hAeq : A = u x - V x - k := hA_def
      linarith [hHbd, htight, hAeq]
    -- The Young core.
    have hcore_x :
        μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) :=
      hcore μ P A hμ_ge1 hP_nn hHJB_rearr
    -- Take `^ s`, `s = 1/(β+τ)`, to recover `μ`.
    have hμ_eq : μ = (μ ^ (β + τ)) ^ s := by
      rw [hs_def, ← Real.rpow_mul hμ_pos.le]
      rw [mul_one_div, div_self hβτ_ne, Real.rpow_one]
    have hrhs_nn : 0 ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
      have ht1 : (0 : ℝ) ≤ C₁ * (P + 1) := by positivity
      have ht2 : (0 : ℝ) ≤ C₂ * |A| ^ ((β + τ) / β) := by positivity
      linarith
    have hμ_le_rpow :
        μ ≤ (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s := by
      rw [hμ_eq]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hμ_pos.le _) hcore_x hs_nn
    -- Split the two summands of the base.
    have hsplit1 :
        (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s
          ≤ 2 ^ s * ((C₁ * (P + 1)) ^ s
              + (C₂ * |A| ^ ((β + τ) / β)) ^ s) :=
      rpow_add_two_le hs_nn (by positivity) (by positivity)
    -- `(C₁(P+1))^s = C₁^s (P+1)^s ≤ C₁^s 2^s (P^s + 1)`.
    have hPexpand : (C₁ * (P + 1)) ^ s
        ≤ C₁ ^ s * (2 ^ s * (P ^ s + 1)) := by
      have he1 : (C₁ * (P + 1)) ^ s = C₁ ^ s * (P + 1) ^ s :=
        Real.mul_rpow hC₁ (by linarith)
      rw [he1]
      have he2 : (P + 1) ^ s ≤ 2 ^ s * (P ^ s + 1 ^ s) :=
        rpow_add_two_le hs_nn hP_nn (by norm_num)
      rw [Real.one_rpow] at he2
      have hC₁s_nn : (0 : ℝ) ≤ C₁ ^ s := Real.rpow_nonneg hC₁ s
      exact mul_le_mul_of_nonneg_left he2 hC₁s_nn
    -- `P^s = ‖Du x‖^{α/β}`.
    have hP_s : P ^ s = ‖(fun i => Du i x)‖ ^ (α / β) := by
      rw [hP_def, ← Real.rpow_mul (norm_nonneg _), hs_def, hαt_s]
    -- `(C₂|A|^q)^s = C₂^s |A|^{1/β}`.
    have hAexpand : (C₂ * |A| ^ ((β + τ) / β)) ^ s
        = C₂ ^ s * |A| ^ ((1 : ℝ) / β) := by
      rw [Real.mul_rpow hC₂ (Real.rpow_nonneg (abs_nonneg _) _),
          ← Real.rpow_mul (abs_nonneg _), hs_def, hq_s]
    -- `|A|^{1/β} ≤ (|u|+|V|+|k|)^{1/β} ≤ 2^{1/β}((|u|+|V|)^{1/β}+|k|^{1/β})`.
    have hβinv_nn : (0 : ℝ) ≤ 1 / β := by positivity
    have hA_abs_le : |A| ≤ |u x| + |V x| + |k| := by
      have huv : |u x - V x| ≤ |u x| + |V x| := by
        have h := abs_add_le (u x) (-(V x))
        rw [abs_neg] at h
        rw [sub_eq_add_neg]; exact h
      have hk : |u x - V x - k| ≤ |u x - V x| + |k| := by
        have h := abs_add_le (u x - V x) (-k)
        rw [abs_neg] at h
        rw [show u x - V x - k = (u x - V x) + (-k) by ring]; exact h
      rw [hA_def]; linarith
    have hAbound : |A| ^ ((1 : ℝ) / β)
        ≤ 2 ^ ((1 : ℝ) / β)
            * ((|u x| + |V x|) ^ ((1 : ℝ) / β) + |k| ^ ((1 : ℝ) / β)) := by
      have hstep1 : |A| ^ ((1 : ℝ) / β)
          ≤ (|u x| + |V x| + |k|) ^ ((1 : ℝ) / β) :=
        Real.rpow_le_rpow (abs_nonneg _) hA_abs_le hβinv_nn
      have hstep2 : (|u x| + |V x| + |k|) ^ ((1 : ℝ) / β)
          ≤ 2 ^ ((1 : ℝ) / β)
              * ((|u x| + |V x|) ^ ((1 : ℝ) / β) + |k| ^ ((1 : ℝ) / β)) :=
        rpow_add_two_le hβinv_nn (by positivity) (abs_nonneg _)
      linarith
    -- Now assemble the chain to `B1·X + B2·Y + B3`.
    set X : ℝ := ‖(fun i => Du i x)‖ ^ (α / β) with hX_def
    set Y : ℝ := (|u x| + |V x|) ^ ((1 : ℝ) / β) with hY_def
    have hX_nn : 0 ≤ X := Real.rpow_nonneg (norm_nonneg _) _
    have hY_nn : 0 ≤ Y := Real.rpow_nonneg (by positivity) _
    have h2s_nn : (0 : ℝ) ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
    have hC₂s_nn : (0 : ℝ) ≤ C₂ ^ s := Real.rpow_nonneg hC₂ s
    have hk_nn : (0 : ℝ) ≤ |k| ^ ((1 : ℝ) / β) :=
      Real.rpow_nonneg (abs_nonneg _) _
    -- Combine `hsplit1`, `hPexpand`, `hP_s`, `hAexpand`, `hAbound`.
    have hchain : μ ≤ B1 * X + B2 * Y + B3 := by
      have hA_term :
          (C₂ * |A| ^ ((β + τ) / β)) ^ s
            ≤ C₂ ^ s * (2 ^ ((1 : ℝ) / β) * (Y + |k| ^ ((1 : ℝ) / β))) := by
        rw [hAexpand]
        rw [hY_def]
        exact mul_le_mul_of_nonneg_left hAbound hC₂s_nn
      have hP_term :
          (C₁ * (P + 1)) ^ s ≤ C₁ ^ s * (2 ^ s * (X + 1)) := by
        rw [← hP_s]; exact hPexpand
      calc μ
          ≤ (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s := hμ_le_rpow
        _ ≤ 2 ^ s * ((C₁ * (P + 1)) ^ s
              + (C₂ * |A| ^ ((β + τ) / β)) ^ s) := hsplit1
        _ ≤ 2 ^ s * (C₁ ^ s * (2 ^ s * (X + 1))
              + C₂ ^ s * (2 ^ ((1 : ℝ) / β) * (Y + |k| ^ ((1 : ℝ) / β)))) := by
            apply mul_le_mul_of_nonneg_left _ h2s_nn
            linarith
        _ = B1 * X + B2 * Y + B3 := by
            rw [hB1_def, hB2_def, hB3_def]; ring
    -- Dominate by the envelope.
    have hfinal : B1 * X + B2 * Y + B3
        ≤ muAuxEnvelope C m u V Du α β x := by
      have henv : muAuxEnvelope C m u V Du α β x
          = C * X + C * Y + C + max (m x) 0 := by
        rw [hX_def, hY_def]; rfl
      rw [henv]
      have e1 : B1 * X ≤ C * X := mul_le_mul_of_nonneg_right hC_ge_B1 hX_nn
      have e2 : B2 * Y ≤ C * Y := mul_le_mul_of_nonneg_right hC_ge_B2 hY_nn
      have e3 : B3 ≤ C := hC_ge_B3
      have e4 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
      linarith
    exact le_trans hchain hfinal

/-- **Nonnegative-witness sibling of `muAux_le_envelope_of_congestionGrowth`**
(paper line 1448, δ-truncation route, lines 1417–1506).

Identical conclusion (`muAux ≤ muAuxEnvelope C …` a.e.) and the same weakened
on-`(0,∞)` continuity hypothesis as `_of_m_pos`, but assuming only `0 ≤ m`
*nowhere* — in fact requiring no positivity/nonnegativity witness on `m` at all.
The key observation: the envelope proof never uses HJB-membership of `μ x`. It
needs only `0 ≤ μ x` and `m x ≤ μ x`, both of which follow directly from
non-emptiness of `muAuxSet` (every element is `≥ 0` and `≥ m x`, so the infimum
`μ x` is too). On the boundary `{m x = 0}` the `μ ≤ 1` branch and the
`μ = m x` branch both dominate by the envelope's constant / `max (m x) 0`
summand, and the `μ > m x` Young branch evaluates `H(x, Du x, μ)` only at
`μ > 1 > 0`, staying inside `Ioi 0`. The tightness contradiction reuses the
`ContinuousWithinAt`→`nhds` perturbation of `muAux_product_identity_of_m_nonneg`
(`csInf_le`, no closedness needed). The `_of_m_pos` original is kept untouched. -/
theorem muAux_le_envelope_of_congestionGrowth_of_m_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        muAux k m u V Du H x
          ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hβ : 0 < β := hcong.hβ
  have hα : 1 < α := hcong.hα
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ1 : τ ≤ 1 := hcong.hτ.2
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβτ_pos : 0 < β + τ := by linarith
  have hβτ_ne : β + τ ≠ 0 := ne_of_gt hβτ_pos
  obtain ⟨K, δ, hK, hδ, hH_upper⟩ := H_upper_congestion_of_hmon hmon hcong
  have hH_upper' :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ K * ((1 / mm) + (1 / mm ^ τ)) * (‖p‖ ^ αt + 1)
                    - δ * mm ^ β := by
    filter_upwards [hH_upper] with x hx
    intro p mm hmm
    exact hx p mm hmm
  have hαt_s : αt * (1 / (β + τ)) = α / β := by
    rw [hαtdef]; field_simp
  have hq_s : ((β + τ) / β) * (1 / (β + τ)) = 1 / β := by
    field_simp
  set s : ℝ := 1 / (β + τ) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_nn : 0 ≤ s := hs_pos.le
  obtain ⟨C₁, C₂, hC₁, hC₂, hcore⟩ :
      ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
        ∀ μ P A : ℝ, 1 ≤ μ → 0 ≤ P →
          δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A →
          μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
    rcases eq_or_lt_of_le hτ_nn with hτ0 | hτpos
    · refine ⟨2 * K / δ, 1 / δ, by positivity, by positivity, ?_⟩
      intro μ P A hμ hP hHJB
      have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ
      have hμτ1 : μ ^ τ = 1 := by rw [← hτ0]; exact Real.rpow_zero μ
      have hinvμ_le : 1 / μ ≤ 1 := by
        rw [div_le_one hμ_pos]; exact hμ
      have hcoef : (1 / μ) + (1 / μ ^ τ) ≤ 2 := by
        rw [hμτ1, div_one]; linarith
      have hP1_nn : (0 : ℝ) ≤ P + 1 := by linarith
      have hstep : δ * μ ^ β ≤ K * 2 * (P + 1) + A := by
        have h1 : K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1)
            ≤ K * 2 * (P + 1) := by
          apply mul_le_mul_of_nonneg_right _ hP1_nn
          exact mul_le_mul_of_nonneg_left hcoef hK.le
        linarith
      have hβτ_eq : β + τ = β := by rw [← hτ0]; ring
      have hqexp : (β + τ) / β = 1 := by rw [hβτ_eq]; field_simp
      rw [hqexp, Real.rpow_one, hβτ_eq]
      have hA_le : A ≤ |A| := le_abs_self A
      have h2 : δ * μ ^ β ≤ 2 * K * (P + 1) + |A| := by linarith
      have hμβ_le : μ ^ β ≤ (2 * K / δ) * (P + 1) + (1 / δ) * |A| := by
        have hδinv : 0 < 1 / δ := by positivity
        have := mul_le_mul_of_nonneg_left h2 hδinv.le
        rw [show (1 / δ) * (δ * μ ^ β) = μ ^ β by field_simp] at this
        calc μ ^ β
            ≤ (1 / δ) * (2 * K * (P + 1) + |A|) := this
          _ = (2 * K / δ) * (P + 1) + (1 / δ) * |A| := by ring
      exact hμβ_le
    · exact young_tau_cancellation_core hβ hτpos hτ1 hδ hK
  set B1 : ℝ := 2 ^ s * C₁ ^ s * 2 ^ s with hB1_def
  set B2 : ℝ := 2 ^ s * C₂ ^ s * 2 ^ ((1 : ℝ) / β) with hB2_def
  set B3 : ℝ := 2 ^ s * C₁ ^ s * 2 ^ s
                  + 2 ^ s * C₂ ^ s * 2 ^ ((1 : ℝ) / β) * |k| ^ ((1 : ℝ) / β)
                with hB3_def
  have hB1_nn : 0 ≤ B1 := by rw [hB1_def]; positivity
  have hB2_nn : 0 ≤ B2 := by rw [hB2_def]; positivity
  have hB3_nn : 0 ≤ B3 := by rw [hB3_def]; positivity
  refine ⟨max B1 (max B2 (max B3 1)), ?_, ?_⟩
  · exact le_trans hB1_nn (le_max_left _ _)
  set C : ℝ := max B1 (max B2 (max B3 1)) with hC_def
  have hC_ge_B1 : B1 ≤ C := le_max_left _ _
  have hC_ge_B2 : B2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_ge_B3 : B3 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC_ge_one : (1 : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC_nn : 0 ≤ C := le_trans (by norm_num) hC_ge_one
  -- Per-`x` assembly. No positivity witness: we read `0 ≤ μ x` and `m x ≤ μ x`
  -- straight off non-emptiness of `muAuxSet` via `le_csInf`.
  filter_upwards [hH_upper', hcont, hne]
    with x hHu_x hcont_x hne_x
  set μ : ℝ := muAux k m u V Du H x with hμ_def
  -- `μ x = sInf (muAuxSet …)` is `≥ 0` and `≥ m x` because every element is.
  have hμ_nn : 0 ≤ μ := le_csInf hne_x (fun b hb => hb.1)
  have hmle : m x ≤ μ := le_csInf hne_x (fun b hb => hb.2.1)
  have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
    muAuxSet_bddBelow k m u V Du H x
  -- Envelope is `≥ C ≥ 1`, used for the small-`μ` branch.
  have hEnv_ge_C : C ≤ muAuxEnvelope C m u V Du α β x := by
    unfold muAuxEnvelope
    have h1 : (0 : ℝ) ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : (0 : ℝ) ≤ C * (|u x| + |V x|) ^ (1 / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by positivity) _)
    have h3 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
    linarith
  -- Envelope dominates `max (m x) 0`.
  have hEnv_ge_max : max (m x) 0 ≤ muAuxEnvelope C m u V Du α β x := by
    unfold muAuxEnvelope
    have h1 : (0 : ℝ) ≤ C * ‖(fun i => Du i x)‖ ^ (α / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : (0 : ℝ) ≤ C * (|u x| + |V x|) ^ (1 / β) :=
      mul_nonneg hC_nn (Real.rpow_nonneg (by positivity) _)
    linarith [hC_nn]
  rcases le_or_gt μ 1 with hμ_le1 | hμ_gt1
  · -- Small `μ`: `μ ≤ 1 ≤ C ≤ envelope`.
    exact le_trans hμ_le1 (le_trans hC_ge_one hEnv_ge_C)
  · -- `μ > 1`: apply the upper bound + Young core (evaluates `H` at `μ > 0`).
    have hμ_ge1 : (1 : ℝ) ≤ μ := hμ_gt1.le
    have hμ_pos : 0 < μ := lt_of_lt_of_le one_pos hμ_ge1
    -- If `μ ≤ m x`, then `μ = m x` and `max (m x) 0` absorbs it directly.
    rcases le_or_gt μ (m x) with hμ_lem | hμ_gtm
    · have hμ_eq_m : μ = m x := le_antisymm hμ_lem hmle
      have : μ ≤ max (m x) 0 := by rw [hμ_eq_m]; exact le_max_left _ _
      exact le_trans this hEnv_ge_max
    -- Otherwise `μ > m x ≥ 0`: HJB is tight at the infimum.
    have htight : k ≤ u x + H x (fun i => Du i x) μ - V x := by
      by_contra hlt
      push_neg at hlt
      set g : ℝ → ℝ := fun ν => u x + H x (fun i => Du i x) ν - V x with hg_def
      have hg_contOn : ContinuousOn g (Set.Ioi 0) :=
        (continuousOn_const.add hcont_x).sub continuousOn_const
      have hgμ : g μ < k := hlt
      have hμ_mem_Ioi : μ ∈ Set.Ioi (0 : ℝ) := hμ_pos
      have h_cont_at : ContinuousWithinAt g (Set.Ioi 0) μ :=
        hg_contOn μ hμ_mem_Ioi
      have h_cont_at' : ContinuousAt g μ :=
        h_cont_at.continuousAt (isOpen_Ioi.mem_nhds hμ_mem_Ioi)
      have hpre_nhds : g ⁻¹' Set.Iio k ∈ nhds μ :=
        h_cont_at'.preimage_mem_nhds (isOpen_Iio.mem_nhds hgμ)
      have hIoi_nhds : Set.Ioi (0 : ℝ) ∈ nhds μ :=
        isOpen_Ioi.mem_nhds hμ_mem_Ioi
      have hball_nhds : (g ⁻¹' Set.Iio k) ∩ Set.Ioi 0 ∈ nhds μ :=
        Filter.inter_mem hpre_nhds hIoi_nhds
      obtain ⟨δ₀, hδ₀_pos, hball⟩ := Metric.mem_nhds_iff.mp hball_nhds
      set ν : ℝ := max (max (m x) 0) (μ - δ₀ / 2) with hν_def
      have hν_lt : ν < μ := by
        rw [hν_def]
        apply max_lt
        · exact max_lt hμ_gtm hμ_pos
        · linarith
      have hν_ge_mx0 : max (m x) 0 ≤ ν := le_max_left _ _
      have hν_ge_m : m x ≤ ν := le_trans (le_max_left _ _) hν_ge_mx0
      have hν_nn : 0 ≤ ν := le_trans (le_max_right _ _) hν_ge_mx0
      have hν_gt : μ - δ₀ / 2 ≤ ν := le_max_right _ _
      have hν_ball : ν ∈ Metric.ball μ δ₀ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith
        · linarith
      have hν_in : ν ∈ (g ⁻¹' Set.Iio k) ∩ Set.Ioi 0 := hball hν_ball
      have hgν : g ν < k := hν_in.1
      have hν_mem : ν ∈ muAuxSet k m u V Du H x :=
        ⟨hν_nn, hν_ge_m, le_of_lt hgν⟩
      have hμ_le_ν : muAux k m u V Du H x ≤ ν :=
        csInf_le h_bdd hν_mem
      rw [← hμ_def] at hμ_le_ν
      linarith
    set P : ℝ := ‖(fun i => Du i x)‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    set A : ℝ := u x - V x - k with hA_def
    have hHbd : H x (fun i => Du i x) μ
        ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) - δ * μ ^ β :=
      hHu_x (fun i => Du i x) μ hμ_pos
    have hHJB_rearr :
        δ * μ ^ β ≤ K * ((1 / μ) + (1 / μ ^ τ)) * (P + 1) + A := by
      have hAeq : A = u x - V x - k := hA_def
      linarith [hHbd, htight, hAeq]
    have hcore_x :
        μ ^ (β + τ) ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) :=
      hcore μ P A hμ_ge1 hP_nn hHJB_rearr
    have hμ_eq : μ = (μ ^ (β + τ)) ^ s := by
      rw [hs_def, ← Real.rpow_mul hμ_pos.le]
      rw [mul_one_div, div_self hβτ_ne, Real.rpow_one]
    have hrhs_nn : 0 ≤ C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β) := by
      have ht1 : (0 : ℝ) ≤ C₁ * (P + 1) := by positivity
      have ht2 : (0 : ℝ) ≤ C₂ * |A| ^ ((β + τ) / β) := by positivity
      linarith
    have hμ_le_rpow :
        μ ≤ (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s := by
      rw [hμ_eq]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hμ_pos.le _) hcore_x hs_nn
    have hsplit1 :
        (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s
          ≤ 2 ^ s * ((C₁ * (P + 1)) ^ s
              + (C₂ * |A| ^ ((β + τ) / β)) ^ s) :=
      rpow_add_two_le hs_nn (by positivity) (by positivity)
    have hPexpand : (C₁ * (P + 1)) ^ s
        ≤ C₁ ^ s * (2 ^ s * (P ^ s + 1)) := by
      have he1 : (C₁ * (P + 1)) ^ s = C₁ ^ s * (P + 1) ^ s :=
        Real.mul_rpow hC₁ (by linarith)
      rw [he1]
      have he2 : (P + 1) ^ s ≤ 2 ^ s * (P ^ s + 1 ^ s) :=
        rpow_add_two_le hs_nn hP_nn (by norm_num)
      rw [Real.one_rpow] at he2
      have hC₁s_nn : (0 : ℝ) ≤ C₁ ^ s := Real.rpow_nonneg hC₁ s
      exact mul_le_mul_of_nonneg_left he2 hC₁s_nn
    have hP_s : P ^ s = ‖(fun i => Du i x)‖ ^ (α / β) := by
      rw [hP_def, ← Real.rpow_mul (norm_nonneg _), hs_def, hαt_s]
    have hAexpand : (C₂ * |A| ^ ((β + τ) / β)) ^ s
        = C₂ ^ s * |A| ^ ((1 : ℝ) / β) := by
      rw [Real.mul_rpow hC₂ (Real.rpow_nonneg (abs_nonneg _) _),
          ← Real.rpow_mul (abs_nonneg _), hs_def, hq_s]
    have hβinv_nn : (0 : ℝ) ≤ 1 / β := by positivity
    have hA_abs_le : |A| ≤ |u x| + |V x| + |k| := by
      have huv : |u x - V x| ≤ |u x| + |V x| := by
        have h := abs_add_le (u x) (-(V x))
        rw [abs_neg] at h
        rw [sub_eq_add_neg]; exact h
      have hk : |u x - V x - k| ≤ |u x - V x| + |k| := by
        have h := abs_add_le (u x - V x) (-k)
        rw [abs_neg] at h
        rw [show u x - V x - k = (u x - V x) + (-k) by ring]; exact h
      rw [hA_def]; linarith
    have hAbound : |A| ^ ((1 : ℝ) / β)
        ≤ 2 ^ ((1 : ℝ) / β)
            * ((|u x| + |V x|) ^ ((1 : ℝ) / β) + |k| ^ ((1 : ℝ) / β)) := by
      have hstep1 : |A| ^ ((1 : ℝ) / β)
          ≤ (|u x| + |V x| + |k|) ^ ((1 : ℝ) / β) :=
        Real.rpow_le_rpow (abs_nonneg _) hA_abs_le hβinv_nn
      have hstep2 : (|u x| + |V x| + |k|) ^ ((1 : ℝ) / β)
          ≤ 2 ^ ((1 : ℝ) / β)
              * ((|u x| + |V x|) ^ ((1 : ℝ) / β) + |k| ^ ((1 : ℝ) / β)) :=
        rpow_add_two_le hβinv_nn (by positivity) (abs_nonneg _)
      linarith
    set X : ℝ := ‖(fun i => Du i x)‖ ^ (α / β) with hX_def
    set Y : ℝ := (|u x| + |V x|) ^ ((1 : ℝ) / β) with hY_def
    have hX_nn : 0 ≤ X := Real.rpow_nonneg (norm_nonneg _) _
    have hY_nn : 0 ≤ Y := Real.rpow_nonneg (by positivity) _
    have h2s_nn : (0 : ℝ) ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
    have hC₂s_nn : (0 : ℝ) ≤ C₂ ^ s := Real.rpow_nonneg hC₂ s
    have hk_nn : (0 : ℝ) ≤ |k| ^ ((1 : ℝ) / β) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hchain : μ ≤ B1 * X + B2 * Y + B3 := by
      have hA_term :
          (C₂ * |A| ^ ((β + τ) / β)) ^ s
            ≤ C₂ ^ s * (2 ^ ((1 : ℝ) / β) * (Y + |k| ^ ((1 : ℝ) / β))) := by
        rw [hAexpand]
        rw [hY_def]
        exact mul_le_mul_of_nonneg_left hAbound hC₂s_nn
      have hP_term :
          (C₁ * (P + 1)) ^ s ≤ C₁ ^ s * (2 ^ s * (X + 1)) := by
        rw [← hP_s]; exact hPexpand
      calc μ
          ≤ (C₁ * (P + 1) + C₂ * |A| ^ ((β + τ) / β)) ^ s := hμ_le_rpow
        _ ≤ 2 ^ s * ((C₁ * (P + 1)) ^ s
              + (C₂ * |A| ^ ((β + τ) / β)) ^ s) := hsplit1
        _ ≤ 2 ^ s * (C₁ ^ s * (2 ^ s * (X + 1))
              + C₂ ^ s * (2 ^ ((1 : ℝ) / β) * (Y + |k| ^ ((1 : ℝ) / β)))) := by
            apply mul_le_mul_of_nonneg_left _ h2s_nn
            linarith
        _ = B1 * X + B2 * Y + B3 := by
            rw [hB1_def, hB2_def, hB3_def]; ring
    have hfinal : B1 * X + B2 * Y + B3
        ≤ muAuxEnvelope C m u V Du α β x := by
      have henv : muAuxEnvelope C m u V Du α β x
          = C * X + C * Y + C + max (m x) 0 := by
        rw [hX_def, hY_def]; rfl
      rw [henv]
      have e1 : B1 * X ≤ C * X := mul_le_mul_of_nonneg_right hC_ge_B1 hX_nn
      have e2 : B2 * Y ≤ C * Y := mul_le_mul_of_nonneg_right hC_ge_B2 hY_nn
      have e3 : B3 ≤ C := hC_ge_B3
      have e4 : (0 : ℝ) ≤ max (m x) 0 := le_max_right _ _
      linarith
    exact le_trans hchain hfinal

/-! ## (1) `μ ∈ L^{β̄}_per` (paper line 1448) -/

/-- **Paper line 1448** — `μ ∈ L^{β̄}_per`.

Given the auxiliary correction `muAux k m u V Du H` and a pointwise
envelope (derivable from `eq:boundsH+` plus Young, paper lines 1442–1448)

  `μ(x) ≤ G(x)`     a.e. on the unit cube,

with `G ∈ L^{β̄}_per` and `G ≥ 0`, the auxiliary `μ` lies in `L^{β̄}_per`.

The dominator `G` is the paper's
`C·|Du(x)|^{α/β} + C·(|u(x)| + |V(x)|)^{1/β} + C`,
but is exposed as a hypothesis for modularity (see CONVENTIONS §8). -/
theorem muAux_mem_Lp
    {betaBar : ℝ≥0∞}
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {G : (Fin d → ℝ) → ℝ}
    (hG_mem : MemLpPer (d := d) betaBar G)
    (hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x)
    (h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)))
    (h_ne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        muAux k m u V Du H x ≤ G x) :
    MemLpPer (d := d) betaBar (muAux k m u V Du H) := by
  -- `muAux ≥ 0` follows from the constraint set being a subset of `[0, ∞)`.
  have h_mu_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAux k m u V Du H x := by
    filter_upwards [h_ne] with x hx
    apply le_csInf hx
    intro b hb
    exact hb.1
  exact memLpPer_of_nonneg_le hG_mem h_meas h_mu_nn hG_nn h_envelope

/-- **Witness-context assembly of `μ ∈ L^{β̄}_per` (paper line 1448).**

This bundles the five inputs of `muAux_mem_Lp` from the congestion
existence context.  The density/value/gradient functions are the
(plain) measurable coercions of the abstract VI witness, so their joint
measurability is available outright (no a.e. representative needed —
friction point 2 of the per-δ VI task dissolves once `m = ⇑w.1` is the
Lp coercion, which is `StronglyMeasurable`).

The pointwise full-`ℝ` antitonicity (`h_anti`) and continuity (`h_cont`)
of `μ₀ ↦ H(x, Du(x), μ₀)`, plus pointwise nonemptiness (`h_ne_all`) of
the constraint set, are taken as standing hypotheses: `muAux_measurable`
requires them on *all* of `ℝ` (and pointwise), whereas the sibling
`antitone_in_m` only yields `AntitoneOn (0,∞)` and the parametric
`muAux_nonempty_of_large_bound` only yields the a.e. version.  This
mirrors the iter-0927 pattern of carrying the full-ℝ continuity as an
explicit hypothesis.

Inputs:
* `hm_meas, hu_meas, hV_meas, hDu_meas` — plain measurability of the
  density/value/cost/gradient functions (from the Lp coercions).
* the four `MemLpPer` certificates of `muAuxEnvelope_memLp`.
* `hcont`/`hne` — the a.e. continuity and a.e. nonemptiness feeding
  `muAux_le_envelope_of_congestionGrowth`.
* `h_anti`/`h_cont`/`h_ne_all` — the pointwise full-ℝ data for
  `muAux_measurable`. -/
theorem muAux_mem_Lp_of_witnessData
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) := by
  -- (5) The envelope bound and its non-negative constant.
  obtain ⟨C, hC_nn, h_envelope⟩ :=
    muAux_le_envelope_of_congestionGrowth hmon hcong (m := m) (u := u)
      (V := V) (Du := Du) (k := k) hcont hne
  -- (1) The envelope lies in `L^{β̄}_per`.
  have hG_mem :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
        (muAuxEnvelope C m u V Du hcong.α hcong.β) :=
    muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm_mem hu_mem hV_mem hDu_mem
  -- (2) The envelope is pointwise non-negative.
  have hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x :=
    Filter.Eventually.of_forall
      (fun x => muAuxEnvelope_nonneg hC_nn (m := m) (u := u) (V := V)
        (Du := Du) (α := hcong.α) (β := hcong.β) x)
  -- (3) `μ` is measurable hence AE-strongly-measurable.
  -- The HJB-constraint sublevel set is measurable for each `a`:
  -- `x ↦ u x + H x (Du x) a - V x` is measurable, with `H(·, Du ·, a)`
  -- a composition of `H`'s joint measurability with the measurable
  -- product `x ↦ (x, (fun i => Du i x), a)`.
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  have h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)) :=
    h_mu_meas.aestronglyMeasurable
  -- Assemble via `muAux_mem_Lp`.
  exact muAux_mem_Lp hG_mem hG_nn h_meas hne h_envelope

/-- **a.e.-on-`(0,∞)` measurability of `μ` assuming `0 < m x`**
(positive-witness route, child-F).

Unlike `muAux_measurable_of_Ici0` (which demands the pointwise closed-`Ici 0`
antitonicity/continuity and pointwise nonemptiness for *every* `x`), this
sibling needs only the genuinely-available a.e.-on-`Ioi 0` data threaded with
`hae_m_pos`, so `muAux`/`muAuxSet` are only ever evaluated on `{0 < m x}`.
Because the hypotheses are a.e. rather than pointwise, the conclusion is
`AEMeasurable` (w.r.t. the torus measure) rather than `Measurable` — which is
exactly what the downstream `AEStronglyMeasurable` consumers require.

Proof: on the measurable good set `S` (positivity ∩ a.e. antitonicity ∩ a.e.
continuity ∩ a.e. nonemptiness, with null complement) the level-set identity
of `muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos` (MuAux.lean:601) holds,
so `μ` agrees a.e. with a genuinely measurable piecewise function. -/
theorem muAux_measurable_of_Ioi0_of_m_pos
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k })
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty) :
    AEMeasurable (muAux k m u V Du H) (volume.restrict (UnitCube d)) := by
  classical
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμmdef
  -- The a.e.-full good set, as the complement of the union of four null sets.
  set B₁ : Set (Fin d → ℝ) := toMeasurable μm { x | ¬ (0 < m x) } with hB₁
  set B₂ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) }
    with hB₂
  set B₃ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀)
        (Set.Ioi 0) } with hB₃
  set B₄ : Set (Fin d → ℝ) :=
    toMeasurable μm { x | ¬ (muAuxSet k m u V Du H x).Nonempty } with hB₄
  set Bad : Set (Fin d → ℝ) := B₁ ∪ B₂ ∪ B₃ ∪ B₄ with hBad
  -- Each piece is measurable and null.
  have hB₁_meas : MeasurableSet B₁ := measurableSet_toMeasurable _ _
  have hB₂_meas : MeasurableSet B₂ := measurableSet_toMeasurable _ _
  have hB₃_meas : MeasurableSet B₃ := measurableSet_toMeasurable _ _
  have hB₄_meas : MeasurableSet B₄ := measurableSet_toMeasurable _ _
  have hBad_meas : MeasurableSet Bad :=
    ((hB₁_meas.union hB₂_meas).union hB₃_meas).union hB₄_meas
  have hB₁_null : μm B₁ = 0 := by
    rw [hB₁, measure_toMeasurable]
    simpa using (ae_iff.mp hae_m_pos)
  have hB₂_null : μm B₂ = 0 := by
    rw [hB₂, measure_toMeasurable]
    simpa using (ae_iff.mp hae_anti)
  have hB₃_null : μm B₃ = 0 := by
    rw [hB₃, measure_toMeasurable]
    simpa using (ae_iff.mp hae_cont)
  have hB₄_null : μm B₄ = 0 := by
    rw [hB₄, measure_toMeasurable]
    simpa using (ae_iff.mp hae_ne)
  have hBad_null : μm Bad = 0 := by
    have h12 : μm (B₁ ∪ B₂) = 0 :=
      measure_union_null hB₁_null hB₂_null
    have h123 : μm (B₁ ∪ B₂ ∪ B₃) = 0 :=
      measure_union_null h12 hB₃_null
    exact measure_union_null h123 hB₄_null
  -- On `Badᶜ` all four facts hold genuinely.
  have hgood : ∀ x ∈ Badᶜ,
      0 < m x ∧
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      (muAuxSet k m u V Du H x).Nonempty := by
    intro x hx
    simp only [hBad, Set.mem_compl_iff, Set.mem_union, not_or] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; exact hx1 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx2 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx3 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx4 (subset_toMeasurable _ _ h)
  -- The candidate measurable function: `μ` on `Badᶜ`, `0` on `Bad`.
  set g : (Fin d → ℝ) → ℝ := Bad.piecewise (fun _ => 0) (muAux k m u V Du H)
    with hgdef
  -- On `Badᶜ`, the level-set identity holds genuinely.
  have hlevel : ∀ a : ℝ, ∀ x ∈ Badᶜ,
      (muAux k m u V Du H x ≤ a ↔
        x ∈ ({ y : Fin d → ℝ | m y ≤ a } ∩
          { y : Fin d → ℝ | u y + H y (fun i => Du i y) a - V y ≤ k })) := by
    intro a x hx
    obtain ⟨hx_pos, hx_anti, hx_cont, hx_ne⟩ := hgood x hx
    rcases lt_or_ge a 0 with ha_neg | ha_nn
    · -- `a < 0`: `μ x ≥ m x > 0 > a`, so `μ x ≤ a` is false; RHS also false.
      have hμ_pos : 0 < muAux k m u V Du H x :=
        lt_of_lt_of_le hx_pos (le_csInf hx_ne (fun b hb => hb.2.1))
      constructor
      · intro hle; exact absurd (lt_of_lt_of_le hμ_pos hle) (by linarith)
      · intro hmem
        exact absurd (lt_of_lt_of_le hx_pos hmem.1) (by linarith)
    · -- `a ≥ 0`: the on-`Ioi 0` level-set identity.
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      exact muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos
        hx_pos ha_nn hx_cont hx_anti hx_ne
  refine ⟨g, ?_, ?_⟩
  · -- `g` is measurable.
    refine measurable_of_restrict_of_restrict_compl hBad_meas ?_ ?_
    · -- On `Bad`, `g = 0`.
      have : Bad.domRestrict g = fun _ => (0 : ℝ) := by
        funext x
        simp only [Set.domRestrict_apply, hgdef, Set.piecewise_eq_of_mem _ _ _ x.2]
      rw [this]; exact measurable_const
    · -- On `Badᶜ`, `g = μ`; measurable via the level-set identity.
      have hrestrict_eq :
          Badᶜ.domRestrict g = Badᶜ.domRestrict (muAux k m u V Du H) := by
        funext x
        have hxnot : (x : Fin d → ℝ) ∉ Bad := by
          have := x.2; rwa [Set.mem_compl_iff] at this
        simp only [Set.domRestrict_apply, hgdef,
          Set.piecewise_eq_of_notMem _ _ _ hxnot]
      rw [hrestrict_eq]
      refine measurable_of_Iic (fun a => ?_)
      have hset :
          (Badᶜ.domRestrict (muAux k m u V Du H)) ⁻¹' Set.Iic a =
            Subtype.val ⁻¹'
              ({ y : Fin d → ℝ | m y ≤ a } ∩
                { y : Fin d → ℝ | u y + H y (fun i => Du i y) a - V y ≤ k }) := by
        ext x
        simp only [Set.domRestrict_apply, Set.mem_preimage, Set.mem_Iic]
        exact hlevel a x.1 x.2
      rw [hset]
      exact (measurable_subtype_coe
        ((hm_meas measurableSet_Iic).inter (hHJB_meas a)))
  · -- `μ =ᵐ[μm] g`: they agree off the null set `Bad`.
    have hcompl : Set.EqOn (muAux k m u V Du H) g Badᶜ := by
      intro x hx
      have hxnot : x ∉ Bad := by rwa [Set.mem_compl_iff] at hx
      simp only [hgdef, Set.piecewise_eq_of_notMem _ _ _ hxnot]
    refine Filter.eventuallyEq_of_mem (s := Badᶜ) ?_ hcompl
    rw [mem_ae_iff, compl_compl]
    exact hBad_null

/-- If all rational `Iic`-preimages of a real-valued function are null-measurable,
the function is a.e.-measurable.

This is the `NullMeasurableSet` analogue of `measurable_of_Iic`: a function whose
rational-threshold sublevel sets are only known to be null-measurable is still
a.e.-measurable. The rationals form a countable generating family, so the union of
the (null) disagreement sets between each `f⁻¹'(Iic q)` and its `toMeasurable`
superset is null; on the complement of that null set the function agrees with a
genuinely measurable modification built from the rational sublevel sets. -/
theorem aemeasurable_of_nullMeasurable_Iic_rat
    {δ : Type*} {mδ : MeasurableSpace δ} {μ : Measure δ}
    {f : δ → ℝ}
    (h : ∀ q : ℚ, NullMeasurableSet (f ⁻¹' Set.Iic (q : ℝ)) μ) :
    AEMeasurable f μ := by
  classical
  -- Genuine measurable supersets agreeing a.e.
  set T : ℚ → Set δ := fun q => toMeasurable μ (f ⁻¹' Set.Iic (q : ℝ)) with hT
  have hT_meas : ∀ q, MeasurableSet (T q) := fun q => measurableSet_toMeasurable _ _
  have hT_ae : ∀ q, T q =ᵐ[μ] f ⁻¹' Set.Iic (q : ℝ) := fun q => (h q).toMeasurable_ae_eq
  -- The null "bad" set where some rational level set disagrees with `T`.
  set N₀ : Set δ := ⋃ q : ℚ, {x | (x ∈ T q) ≠ (x ∈ f ⁻¹' Set.Iic (q : ℝ))} with hN₀
  have hN₀_null : μ N₀ = 0 := by
    refine measure_iUnion_null (fun q => ?_)
    have := (hT_ae q)
    have heq : {x | (x ∈ T q) ≠ (x ∈ f ⁻¹' Set.Iic (q : ℝ))} =
        {x | ¬ ((x ∈ T q) ↔ (x ∈ f ⁻¹' Set.Iic (q : ℝ)))} := by
      ext x; simp [eq_iff_iff]
    rw [heq]
    refine ae_iff.mp ?_
    filter_upwards [this] with x hx
    simpa [Set.mem_setOf_eq] using hx
  set N : Set δ := toMeasurable μ N₀ with hNdef
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN_null : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact hN₀_null
  have hN₀_sub : N₀ ⊆ N := subset_toMeasurable _ _
  -- On `Nᶜ`, all rational level sets coincide with `T q`.
  have hagree : ∀ q : ℚ, ∀ x ∈ Nᶜ, (x ∈ T q ↔ f x ≤ (q : ℝ)) := by
    intro q x hx
    have hxN₀ : x ∉ N₀ := fun hc => hx (hN₀_sub hc)
    have : ¬ ((x ∈ T q) ≠ (x ∈ f ⁻¹' Set.Iic (q : ℝ))) := by
      intro hc
      exact hxN₀ (Set.mem_iUnion.2 ⟨q, hc⟩)
    rw [not_ne_iff] at this
    simpa [Set.mem_preimage, Set.mem_Iic] using this
  -- The measurable modification.
  set g : δ → ℝ := fun x => if x ∈ N then 0 else f x with hgdef
  have hg_meas : Measurable g := by
    refine measurable_of_Iic (fun a => ?_)
    have hsplit : g ⁻¹' Set.Iic a =
        (N ∩ g ⁻¹' Set.Iic a) ∪ (Nᶜ ∩ g ⁻¹' Set.Iic a) := by
      rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    rw [hsplit]
    refine MeasurableSet.union ?_ ?_
    · -- On `N`, `g = 0`.
      have : N ∩ g ⁻¹' Set.Iic a = if (0 : ℝ) ≤ a then N else ∅ := by
        ext x
        by_cases h0 : (0 : ℝ) ≤ a
        · simp only [h0, if_true]
          constructor
          · rintro ⟨hxN, _⟩; exact hxN
          · intro hxN; exact ⟨hxN, by simp [hgdef, hxN, h0]⟩
        · simp only [h0, if_false]
          constructor
          · rintro ⟨hxN, hxle⟩
            simp only [Set.mem_preimage, Set.mem_Iic, hgdef, hxN, if_true] at hxle
            exact absurd hxle h0
          · intro hx; exact absurd hx (Set.notMem_empty x)
      rw [this]; split <;> [exact hN_meas; exact MeasurableSet.empty]
    · -- On `Nᶜ`, `g = f`; level set is intersection over rationals of `T`.
      have hset : Nᶜ ∩ g ⁻¹' Set.Iic a =
          Nᶜ ∩ (⋂ q : {q : ℚ // a < (q : ℝ)}, T (q : ℚ)) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_iInter]
        constructor
        · rintro ⟨hxN, hxle⟩
          refine ⟨hxN, ?_⟩
          intro q
          rw [hagree (q : ℚ) x hxN]
          have hxnotN : x ∉ N := hxN
          have hgx : g x = f x := by simp [hgdef, hxnotN]
          rw [hgx] at hxle
          exact le_trans hxle (le_of_lt q.2)
        · rintro ⟨hxN, hq⟩
          refine ⟨hxN, ?_⟩
          have hxnotN : x ∉ N := hxN
          have hgx : g x = f x := by simp [hgdef, hxnotN]
          rw [hgx]
          by_contra hlt
          push_neg at hlt
          obtain ⟨q, haq, hqf⟩ := exists_rat_btwn hlt
          have := hq ⟨q, haq⟩
          rw [hagree q x hxN] at this
          exact absurd (lt_of_le_of_lt this hqf) (lt_irrefl _)
      rw [hset]
      exact hN_meas.compl.inter (MeasurableSet.iInter (fun q => hT_meas (q : ℚ)))
  refine ⟨g, hg_meas, ?_⟩
  have : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]; simpa using hN_null
  filter_upwards [this] with x hx
  simp [hgdef, hx]

/-- **`AEStronglyMeasurable V` sibling of `muAux_measurable_of_Ioi0_of_m_pos`**
(child-G).

Same conclusion (`AEMeasurable (muAux …) μm`), but the HJB-constraint sublevel
sets are only assumed `NullMeasurableSet` (which is what one obtains when `V` is
merely `AEStronglyMeasurable` rather than `Measurable`). On the a.e.-full good set
the level-set identity gives `μ⁻¹(Iic q) =ᵐ ({m ≤ q} ∩ {HJB ≤ k}) ∩ Badᶜ` for each
rational `q`, hence each rational sublevel set of `μ` is null-measurable; we then
conclude via `aemeasurable_of_nullMeasurable_Iic_rat`. The `_pos` original is kept
untouched. -/
theorem muAux_measurable_of_Ioi0_of_m_pos_aesm
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k } (volume.restrict (UnitCube d)))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty) :
    AEMeasurable (muAux k m u V Du H) (volume.restrict (UnitCube d)) := by
  classical
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμmdef
  set B₁ : Set (Fin d → ℝ) := toMeasurable μm { x | ¬ (0 < m x) } with hB₁
  set B₂ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) }
    with hB₂
  set B₃ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀)
        (Set.Ioi 0) } with hB₃
  set B₄ : Set (Fin d → ℝ) :=
    toMeasurable μm { x | ¬ (muAuxSet k m u V Du H x).Nonempty } with hB₄
  set Bad : Set (Fin d → ℝ) := B₁ ∪ B₂ ∪ B₃ ∪ B₄ with hBad
  have hB₁_meas : MeasurableSet B₁ := measurableSet_toMeasurable _ _
  have hB₂_meas : MeasurableSet B₂ := measurableSet_toMeasurable _ _
  have hB₃_meas : MeasurableSet B₃ := measurableSet_toMeasurable _ _
  have hB₄_meas : MeasurableSet B₄ := measurableSet_toMeasurable _ _
  have hBad_meas : MeasurableSet Bad :=
    ((hB₁_meas.union hB₂_meas).union hB₃_meas).union hB₄_meas
  have hB₁_null : μm B₁ = 0 := by
    rw [hB₁, measure_toMeasurable]; simpa using (ae_iff.mp hae_m_pos)
  have hB₂_null : μm B₂ = 0 := by
    rw [hB₂, measure_toMeasurable]; simpa using (ae_iff.mp hae_anti)
  have hB₃_null : μm B₃ = 0 := by
    rw [hB₃, measure_toMeasurable]; simpa using (ae_iff.mp hae_cont)
  have hB₄_null : μm B₄ = 0 := by
    rw [hB₄, measure_toMeasurable]; simpa using (ae_iff.mp hae_ne)
  have hBad_null : μm Bad = 0 := by
    have h12 : μm (B₁ ∪ B₂) = 0 := measure_union_null hB₁_null hB₂_null
    have h123 : μm (B₁ ∪ B₂ ∪ B₃) = 0 := measure_union_null h12 hB₃_null
    exact measure_union_null h123 hB₄_null
  have hgood : ∀ x ∈ Badᶜ,
      0 < m x ∧
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      (muAuxSet k m u V Du H x).Nonempty := by
    intro x hx
    simp only [hBad, Set.mem_compl_iff, Set.mem_union, not_or] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; exact hx1 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx2 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx3 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx4 (subset_toMeasurable _ _ h)
  have hlevel : ∀ a : ℝ, ∀ x ∈ Badᶜ,
      (muAux k m u V Du H x ≤ a ↔
        x ∈ ({ y : Fin d → ℝ | m y ≤ a } ∩
          { y : Fin d → ℝ | u y + H y (fun i => Du i y) a - V y ≤ k })) := by
    intro a x hx
    obtain ⟨hx_pos, hx_anti, hx_cont, hx_ne⟩ := hgood x hx
    rcases lt_or_ge a 0 with ha_neg | ha_nn
    · have hμ_pos : 0 < muAux k m u V Du H x :=
        lt_of_lt_of_le hx_pos (le_csInf hx_ne (fun b hb => hb.2.1))
      constructor
      · intro hle; exact absurd (lt_of_lt_of_le hμ_pos hle) (by linarith)
      · intro hmem
        exact absurd (lt_of_lt_of_le hx_pos hmem.1) (by linarith)
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      exact muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos
        hx_pos ha_nn hx_cont hx_anti hx_ne
  -- For each rational `q`, the level set `μ⁻¹(Iic q)` is null-measurable.
  refine aemeasurable_of_nullMeasurable_Iic_rat (fun q => ?_)
  set a : ℝ := (q : ℝ) with hadef
  set Lq : Set (Fin d → ℝ) :=
    ({ y : Fin d → ℝ | m y ≤ a } ∩
      { y : Fin d → ℝ | u y + H y (fun i => Du i y) a - V y ≤ k }) with hLq
  have hLq_nmeas : NullMeasurableSet Lq μm := by
    rw [hLq]
    exact (hm_meas measurableSet_Iic).nullMeasurableSet.inter (hHJB_nmeas a)
  have hpre_inter : (muAux k m u V Du H ⁻¹' Set.Iic a) ∩ Badᶜ = Lq ∩ Badᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hle, hx⟩; exact ⟨(hlevel a x hx).1 hle, hx⟩
    · rintro ⟨hxL, hx⟩; exact ⟨(hlevel a x hx).2 hxL, hx⟩
  have hae_eq :
      (muAux k m u V Du H ⁻¹' Set.Iic a) =ᵐ[μm] ((Lq ∩ Badᶜ : Set (Fin d → ℝ))) := by
    have hsub : (Lq ∩ Badᶜ) ⊆ (muAux k m u V Du H ⁻¹' Set.Iic a) := by
      rw [← hpre_inter]; exact Set.inter_subset_left
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · have : (muAux k m u V Du H ⁻¹' Set.Iic a) \ (Lq ∩ Badᶜ) ⊆ Bad := by
        intro x hx
        by_contra hxBad
        have hxc : x ∈ Badᶜ := hxBad
        have : x ∈ (muAux k m u V Du H ⁻¹' Set.Iic a) ∩ Badᶜ := ⟨hx.1, hxc⟩
        rw [hpre_inter] at this
        exact hx.2 this
      exact measure_mono_null this hBad_null
    · have : (Lq ∩ Badᶜ) \ (muAux k m u V Du H ⁻¹' Set.Iic a) = ∅ := by
        rw [Set.diff_eq_empty]; exact hsub
      rw [this]; simp
  have hRHS_nmeas : NullMeasurableSet (Lq ∩ Badᶜ) μm :=
    hLq_nmeas.inter hBad_meas.compl.nullMeasurableSet
  exact hRHS_nmeas.congr hae_eq.symm

/-- **Nonnegative-witness `AEStronglyMeasurable V` sibling**
(δ-truncation route, child-D step 1).

Same conclusion (`AEMeasurable (muAux …) μm`) as `muAux_measurable_of_Ioi0_of_m_pos_aesm`,
but the strict positivity `0 < m` is weakened to mere nonnegativity `0 ≤ m`. The
boundary value `H(x, Du x, 0)` is **never** assumed continuous; it enters only as
a measurable *value* through the rational sublevel sets `hHJB_nmeas q` (including
`q = 0`). The level-set identity used is the boundary-free
`muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg`

    μ x ≤ q ↔ m x ≤ q ∧ (HJB(q) ≤ k ∨ μ x ≤ 0)        (q ≥ 0)

with the `{μ ≤ 0}` set characterized boundary-freely by
`muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg`

    μ x ≤ 0 ↔ ∀ n, ∃ q' : ℚ, m x ≤ q' ∧ 0 ≤ q' ∧ q' < 1/(n+1) ∧ HJB(q') ≤ k.

Both pieces are (null-)measurable from `hm_meas` and `hHJB_nmeas` (over all
rationals, incl. `0`), so each rational sublevel of `μ` is null-measurable and we
conclude via `aemeasurable_of_nullMeasurable_Iic_rat`. NO `Set.Ici 0`, NO
`Measurable V`, NO `∀ x` pointwise rider, NO boundary continuity. The `_pos`
originals are kept untouched. -/
theorem muAux_measurable_of_Ioi0_of_m_nonneg_aesm
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k } (volume.restrict (UnitCube d)))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty) :
    AEMeasurable (muAux k m u V Du H) (volume.restrict (UnitCube d)) := by
  classical
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμmdef
  -- Good set: nonnegativity ∩ antitonicity ∩ continuity ∩ nonemptiness.
  set B₁ : Set (Fin d → ℝ) := toMeasurable μm { x | ¬ (0 ≤ m x) } with hB₁
  set B₂ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) }
    with hB₂
  set B₃ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀)
        (Set.Ioi 0) } with hB₃
  set B₄ : Set (Fin d → ℝ) :=
    toMeasurable μm { x | ¬ (muAuxSet k m u V Du H x).Nonempty } with hB₄
  set Bad : Set (Fin d → ℝ) := B₁ ∪ B₂ ∪ B₃ ∪ B₄ with hBad
  have hB₁_meas : MeasurableSet B₁ := measurableSet_toMeasurable _ _
  have hB₂_meas : MeasurableSet B₂ := measurableSet_toMeasurable _ _
  have hB₃_meas : MeasurableSet B₃ := measurableSet_toMeasurable _ _
  have hB₄_meas : MeasurableSet B₄ := measurableSet_toMeasurable _ _
  have hBad_meas : MeasurableSet Bad :=
    ((hB₁_meas.union hB₂_meas).union hB₃_meas).union hB₄_meas
  have hB₁_null : μm B₁ = 0 := by
    rw [hB₁, measure_toMeasurable]; simpa using (ae_iff.mp hae_m_nn)
  have hB₂_null : μm B₂ = 0 := by
    rw [hB₂, measure_toMeasurable]; simpa using (ae_iff.mp hae_anti)
  have hB₃_null : μm B₃ = 0 := by
    rw [hB₃, measure_toMeasurable]; simpa using (ae_iff.mp hae_cont)
  have hB₄_null : μm B₄ = 0 := by
    rw [hB₄, measure_toMeasurable]; simpa using (ae_iff.mp hae_ne)
  have hBad_null : μm Bad = 0 := by
    have h12 : μm (B₁ ∪ B₂) = 0 := measure_union_null hB₁_null hB₂_null
    have h123 : μm (B₁ ∪ B₂ ∪ B₃) = 0 := measure_union_null h12 hB₃_null
    exact measure_union_null h123 hB₄_null
  have hgood : ∀ x ∈ Badᶜ,
      0 ≤ m x ∧
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      (muAuxSet k m u V Du H x).Nonempty := by
    intro x hx
    simp only [hBad, Set.mem_compl_iff, Set.mem_union, not_or] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; exact hx1 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx2 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx3 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx4 (subset_toMeasurable _ _ h)
  -- The boundary-free `{μ ≤ 0}` set, expressed measurably.
  set Z : Set (Fin d → ℝ) :=
    { x : Fin d → ℝ | ∀ n : ℕ, ∃ q : ℚ,
        m x ≤ (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ k } with hZdef
  -- `Z` is null-measurable: a countable `⋂ₙ ⋃_q` of null-measurable conditions.
  have hZ_nmeas : NullMeasurableSet Z μm := by
    have hZ_eq : Z =
        ⋂ n : ℕ, ⋃ q : ℚ,
          ({ x : Fin d → ℝ | m x ≤ (q : ℝ) } ∩
            { x : Fin d → ℝ |
              0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) } ∩
            { x : Fin d → ℝ |
              u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ k }) := by
      ext x
      simp only [hZdef, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
        Set.mem_inter_iff]
      constructor
      · intro h n
        obtain ⟨q, h1, h2, h3, h4⟩ := h n
        exact ⟨q, ⟨h1, h2, h3⟩, h4⟩
      · intro h n
        obtain ⟨q, ⟨h1, h2, h3⟩, h4⟩ := h n
        exact ⟨q, h1, h2, h3, h4⟩
    rw [hZ_eq]
    refine NullMeasurableSet.iInter (fun n => ?_)
    refine NullMeasurableSet.iUnion (fun q => ?_)
    -- The middle factor is `x`-independent: whole space or empty.
    have hmid : NullMeasurableSet
        { x : Fin d → ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) } μm := by
      by_cases hcond : 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1)
      · have : { x : Fin d → ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) }
            = Set.univ := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hcond
        rw [this]; exact MeasurableSet.univ.nullMeasurableSet
      · have : { x : Fin d → ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) }
            = (∅ : Set (Fin d → ℝ)) := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact hcond
        rw [this]; exact MeasurableSet.empty.nullMeasurableSet
    exact ((hm_meas measurableSet_Iic).nullMeasurableSet.inter hmid).inter
      (hHJB_nmeas (q : ℝ))
  -- On `Badᶜ`, `Z` agrees with `{μ ≤ 0}`.
  have hZ_level : ∀ x ∈ Badᶜ, (x ∈ Z ↔ muAux k m u V Du H x ≤ 0) := by
    intro x hx
    obtain ⟨hx_nn, hx_anti, _, hx_ne⟩ := hgood x hx
    rw [hZdef, Set.mem_setOf_eq,
      muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg hx_nn hx_anti hx_ne]
  -- The level-set identity on the good set, for rational thresholds `q`.
  have hlevel : ∀ q : ℚ, ∀ x ∈ Badᶜ,
      (muAux k m u V Du H x ≤ (q : ℝ) ↔
        x ∈ ({ y : Fin d → ℝ | m y ≤ (q : ℝ) } ∩
          (({ y : Fin d → ℝ |
              u y + H y (fun i => Du i y) (q : ℝ) - V y ≤ k }) ∪ Z))) := by
    intro q x hx
    obtain ⟨hx_nn, hx_anti, hx_cont, hx_ne⟩ := hgood x hx
    rcases lt_or_ge (q : ℝ) 0 with hq_neg | hq_nn
    · -- `q < 0`: `μ x ≥ 0 > q`, so LHS false; RHS false (`m x ≤ q < 0 ≤ m x`).
      have hμ_nn : 0 ≤ muAux k m u V Du H x := muAux_nonneg x
      constructor
      · intro hle; exact absurd (le_trans hμ_nn hle) (by linarith)
      · intro hmem
        exact absurd (le_trans hx_nn hmem.1) (by linarith)
    · -- `q ≥ 0`: boundary-free level-set identity.
      rw [muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg
        hx_nn hq_nn hx_cont hx_anti hx_ne]
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨hm, hdisj⟩
        refine ⟨hm, ?_⟩
        rcases hdisj with hHJB | hμ0
        · exact Or.inl hHJB
        · exact Or.inr ((hZ_level x hx).2 hμ0)
      · rintro ⟨hm, hdisj⟩
        refine ⟨hm, ?_⟩
        rcases hdisj with hHJB | hZmem
        · exact Or.inl hHJB
        · exact Or.inr ((hZ_level x hx).1 hZmem)
  -- For each rational `q`, the level set `μ⁻¹(Iic q)` is null-measurable.
  refine aemeasurable_of_nullMeasurable_Iic_rat (fun q => ?_)
  set Lq : Set (Fin d → ℝ) :=
    ({ y : Fin d → ℝ | m y ≤ (q : ℝ) } ∩
      (({ y : Fin d → ℝ |
          u y + H y (fun i => Du i y) (q : ℝ) - V y ≤ k }) ∪ Z)) with hLq
  have hLq_nmeas : NullMeasurableSet Lq μm := by
    rw [hLq]
    exact (hm_meas measurableSet_Iic).nullMeasurableSet.inter
      ((hHJB_nmeas (q : ℝ)).union hZ_nmeas)
  have hpre_inter :
      (muAux k m u V Du H ⁻¹' Set.Iic (q : ℝ)) ∩ Badᶜ = Lq ∩ Badᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hle, hx⟩; exact ⟨(hlevel q x hx).1 hle, hx⟩
    · rintro ⟨hxL, hx⟩; exact ⟨(hlevel q x hx).2 hxL, hx⟩
  have hae_eq :
      (muAux k m u V Du H ⁻¹' Set.Iic (q : ℝ)) =ᵐ[μm]
        ((Lq ∩ Badᶜ : Set (Fin d → ℝ))) := by
    have hsub : (Lq ∩ Badᶜ) ⊆ (muAux k m u V Du H ⁻¹' Set.Iic (q : ℝ)) := by
      rw [← hpre_inter]; exact Set.inter_subset_left
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · have : (muAux k m u V Du H ⁻¹' Set.Iic (q : ℝ)) \ (Lq ∩ Badᶜ) ⊆ Bad := by
        intro x hx
        by_contra hxBad
        have hxc : x ∈ Badᶜ := hxBad
        have : x ∈ (muAux k m u V Du H ⁻¹' Set.Iic (q : ℝ)) ∩ Badᶜ := ⟨hx.1, hxc⟩
        rw [hpre_inter] at this
        exact hx.2 this
      exact measure_mono_null this hBad_null
    · have : (Lq ∩ Badᶜ) \ (muAux k m u V Du H ⁻¹' Set.Iic (q : ℝ)) = ∅ := by
        rw [Set.diff_eq_empty]; exact hsub
      rw [this]; simp
  have hRHS_nmeas : NullMeasurableSet (Lq ∩ Badᶜ) μm :=
    hLq_nmeas.inter hBad_meas.compl.nullMeasurableSet
  exact hRHS_nmeas.congr hae_eq.symm

/-- **Positive-witness sibling of `muAux_mem_Lp_of_witnessData`**
(paper line 1448 on the a.e. set `{0 < m x}`).

Identical conclusion (`μ ∈ L^{β̄}_per`), but the standing continuity feeding
the envelope is weakened from full-`ℝ` `Continuous` to `ContinuousOn (Ioi 0)`,
at the cost of the extra a.e. positivity witness `hm_pos : 0 < m x`. The
envelope bound is produced by `muAux_le_envelope_of_congestionGrowth_of_m_pos`;
measurability still routes through `muAux_measurable_of_Ici0` (whose
`h_anti`/`h_cont` data on `Ici 0` are taken as standing pointwise hypotheses,
exactly as in the original). The original is kept untouched. -/
theorem muAux_mem_Lp_of_witnessData_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) := by
  -- (5) The envelope bound and its non-negative constant (positive-witness).
  obtain ⟨C, hC_nn, h_envelope⟩ :=
    muAux_le_envelope_of_congestionGrowth_of_m_pos hmon hcong (m := m) (u := u)
      (V := V) (Du := Du) (k := k) hcont hne hm_pos
  -- (1) The envelope lies in `L^{β̄}_per`.
  have hG_mem :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
        (muAuxEnvelope C m u V Du hcong.α hcong.β) :=
    muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm_mem hu_mem hV_mem hDu_mem
  -- (2) The envelope is pointwise non-negative.
  have hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x :=
    Filter.Eventually.of_forall
      (fun x => muAuxEnvelope_nonneg hC_nn (m := m) (u := u) (V := V)
        (Du := Du) (α := hcong.α) (β := hcong.β) x)
  -- (3) `μ` is measurable hence AE-strongly-measurable.
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  have h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)) :=
    h_mu_meas.aestronglyMeasurable
  -- Assemble via `muAux_mem_Lp`.
  exact muAux_mem_Lp hG_mem hG_nn h_meas hne h_envelope

/-- **Nonnegative-witness sibling of `muAux_mem_Lp_of_witnessData`**
(paper line 1448, δ-truncation route, lines 1417–1506).

Identical conclusion (`μ ∈ L^{β̄}_per`), with the full-`ℝ` `Continuous`
hypothesis of the original weakened to on-`(0,∞)` continuity of `H(x, Du x, ·)`,
and *no positivity witness on `m`*. The envelope bound comes from
`muAux_le_envelope_of_congestionGrowth_of_m_nonneg` (which needs neither
positivity nor membership of `μ`); measurability still routes through the
nonneg-ready `muAux_measurable_of_Ici0` (whose `h_anti`/`h_cont` data on
`Ici 0` are taken as standing pointwise hypotheses, exactly as in the original
and in `_pos`). The originals are kept untouched. -/
theorem muAux_mem_Lp_of_witnessData_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) := by
  -- (5) The envelope bound and its non-negative constant (nonneg-witness).
  obtain ⟨C, hC_nn, h_envelope⟩ :=
    muAux_le_envelope_of_congestionGrowth_of_m_nonneg hmon hcong (m := m) (u := u)
      (V := V) (Du := Du) (k := k) hcont hne
  have hG_mem :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
        (muAuxEnvelope C m u V Du hcong.α hcong.β) :=
    muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm_mem hu_mem hV_mem hDu_mem
  have hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x :=
    Filter.Eventually.of_forall
      (fun x => muAuxEnvelope_nonneg hC_nn (m := m) (u := u) (V := V)
        (Du := Du) (α := hcong.α) (β := hcong.β) x)
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  have h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)) :=
    h_mu_meas.aestronglyMeasurable
  exact muAux_mem_Lp hG_mem hG_nn h_meas hne h_envelope

/-- **a.e.-rider sibling of `muAux_mem_Lp_of_witnessData_pos`** (child-F).

Identical conclusion (`μ ∈ L^{β̄}_per`), but the pointwise closed-`Ici 0`
antitonicity/continuity and pointwise nonemptiness are replaced by a.e.-on-`Ioi 0`
forms (`hae_anti`, with `hcont`/`hne` already a.e.), threaded with `hm_pos`.
Measurability routes through `muAux_measurable_of_Ioi0_of_m_pos` (yielding
`AEMeasurable`, upgraded to `AEStronglyMeasurable`); everything else is verbatim.
The original `_pos` lemma is kept untouched. -/
theorem muAux_mem_Lp_of_witnessData_pos'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) := by
  obtain ⟨C, hC_nn, h_envelope⟩ :=
    muAux_le_envelope_of_congestionGrowth_of_m_pos hmon hcong (m := m) (u := u)
      (V := V) (Du := Du) (k := k) hcont hne hm_pos
  have hG_mem :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
        (muAuxEnvelope C m u V Du hcong.α hcong.β) :=
    muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm_mem hu_mem hV_mem hDu_mem
  have hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x :=
    Filter.Eventually.of_forall
      (fun x => muAuxEnvelope_nonneg hC_nn (m := m) (u := u) (V := V)
        (Du := Du) (α := hcong.α) (β := hcong.β) x)
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)) :=
    (muAux_measurable_of_Ioi0_of_m_pos hm_meas hHJB_meas hm_pos hae_anti
      hcont hne).aestronglyMeasurable
  exact muAux_mem_Lp hG_mem hG_nn h_meas hne h_envelope

/-- **`AEStronglyMeasurable V` sibling of `muAux_mem_Lp_of_witnessData_pos'`**
(child-G).

Identical to the primed version, but the potential `V` is only assumed
`AEStronglyMeasurable` (which is all that is available at the Apriori call site).
The HJB-constraint sublevel set is therefore only `NullMeasurableSet`, and
measurability routes through `muAux_measurable_of_Ioi0_of_m_pos_aesm`. The `_pos'`
original is kept untouched. -/
theorem muAux_mem_Lp_of_witnessData_pos_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) := by
  obtain ⟨C, hC_nn, h_envelope⟩ :=
    muAux_le_envelope_of_congestionGrowth_of_m_pos hmon hcong (m := m) (u := u)
      (V := V) (Du := Du) (k := k) hcont hne hm_pos
  have hG_mem :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
        (muAuxEnvelope C m u V Du hcong.α hcong.β) :=
    muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm_mem hu_mem hV_mem hDu_mem
  have hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x :=
    Filter.Eventually.of_forall
      (fun x => muAuxEnvelope_nonneg hC_nn (m := m) (u := u) (V := V)
        (Du := Du) (α := hcong.α) (β := hcong.β) x)
  have hHJB_nmeas :
      ∀ a : ℝ,
        NullMeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k }
          (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        AEMeasurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x)
          (volume.restrict (UnitCube d)) :=
      ((hu_meas.add hHcomp).aemeasurable).sub hV_aesm.aemeasurable
    exact hfun.nullMeasurableSet_preimage measurableSet_Iic
  have h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)) :=
    (muAux_measurable_of_Ioi0_of_m_pos_aesm hm_meas hHJB_nmeas hm_pos hae_anti
      hcont hne).aestronglyMeasurable
  exact muAux_mem_Lp hG_mem hG_nn h_meas hne h_envelope

/-- **Nonnegative-witness `AEStronglyMeasurable V` membership** (δ-truncation
route, child-D step 2).

Same conclusion (`μ ∈ L^{β̄}_per`) as `muAux_mem_Lp_of_witnessData_nonneg`, but
with a fully nonneg-clean signature: `V` is only `AEStronglyMeasurable` (NOT
`Measurable`), the antitonicity/continuity data live on `Ioi 0` and are a.e.
(NOT pointwise `Ici 0` riders), and `m` is only nonnegative a.e. (NOT `0 < m`).
The envelope bound comes from `muAux_le_envelope_of_congestionGrowth_of_m_nonneg`;
measurability routes through `muAux_measurable_of_Ioi0_of_m_nonneg_aesm` (no
boundary continuity, only the measurable boundary *value* via `hHJB_nmeas`). The
`muAux_measurable_of_Ici0`/`Measurable V` originals are kept untouched. -/
theorem muAux_mem_Lp_of_witnessData_nonneg_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) := by
  obtain ⟨C, hC_nn, h_envelope⟩ :=
    muAux_le_envelope_of_congestionGrowth_of_m_nonneg hmon hcong (m := m) (u := u)
      (V := V) (Du := Du) (k := k) hcont hne
  have hG_mem :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
        (muAuxEnvelope C m u V Du hcong.α hcong.β) :=
    muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm_mem hu_mem hV_mem hDu_mem
  have hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxEnvelope C m u V Du hcong.α hcong.β x :=
    Filter.Eventually.of_forall
      (fun x => muAuxEnvelope_nonneg hC_nn (m := m) (u := u) (V := V)
        (Du := Du) (α := hcong.α) (β := hcong.β) x)
  have hHJB_nmeas :
      ∀ a : ℝ,
        NullMeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k }
          (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        AEMeasurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x)
          (volume.restrict (UnitCube d)) :=
      ((hu_meas.add hHcomp).aemeasurable).sub hV_aesm.aemeasurable
    exact hfun.nullMeasurableSet_preimage measurableSet_Iic
  have h_meas :
      AEStronglyMeasurable (muAux k m u V Du H)
        (Measure.restrict volume (UnitCube d)) :=
    (muAux_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hm_nn hae_anti
      hcont hne).aestronglyMeasurable
  exact muAux_mem_Lp hG_mem hG_nn h_meas hne h_envelope

/-! ## (2) `H(·, Du, μ) ∈ L^{β̄'}_per` (paper eq. `eq:H-at-Du-mu.bounds`) -/

/-- **Paper eq. `eq:H-at-Du-mu.bounds` (line 1452), upper-side
integrability** — `H(·, Du, μ) ∈ L^{β̄'}_per`.

The two-sided envelope of the paper reads
`(1/C)·|Du|^{αt}/(μ^τ+1) - C·(μ^β+1) ≤ H(x, Du, μ) ≤ k + |u| + |V|`.
Hence `|H(x, Du, μ)| ≤ G(x)` a.e. for the dominator
`G(x) := |k| + |u(x)| + |V(x)| + C·(μ(x)^β + 1) + (1/C)·|Du(x)|^{αt}/(μ(x)^τ+1)`.
With each summand of `G` certified `MemLpPer β̄'` (a hypothesis), the
conclusion follows from `MemLp.of_le_mul (c := 1)`. -/
theorem muAux_H_mem_Lp
    {betaBarPrime : ℝ≥0∞}
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {G : (Fin d → ℝ) → ℝ}
    (hG_mem : MemLpPer (d := d) betaBarPrime G)
    (hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x)
    (h_meas :
      AEStronglyMeasurable
        (fun x => H x (fun i => Du i x) (muAux k m u V Du H x))
        (Measure.restrict volume (UnitCube d)))
    (h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        |H x (fun i => Du i x) (muAux k m u V Du H x)| ≤ G x) :
    MemLpPer (d := d) betaBarPrime
      (fun x => H x (fun i => Du i x) (muAux k m u V Du H x)) := by
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hG_mem.toMemLp h_meas
  filter_upwards [h_envelope, hG_nn] with x hx hgx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgx, one_mul]
  exact hx

/-! ## (3) `|Du|^{αt}/(μ^τ+1) ∈ L^{β̄'}_per` (paper eq. `eq:H-at-Du-mu.bounds`) -/

/-- **Paper eq. `eq:H-at-Du-mu.bounds` (line 1454), quotient
integrability** — `|Du|^{α(1+τ/β)}/(μ^τ + 1) ∈ L^{β̄'}_per`.

From the lower bound `(1/C)·|Du|^{αt}/(μ^τ+1) ≤ H(x, Du, μ) + C(μ^β+1)`
combined with the upper bound `H(x, Du, μ) ≤ k - u + V`, we obtain
`|Du|^{αt}/(μ^τ+1) ≤ C·(k + |u| + |V| + C(μ^β + 1))`. With this
dominator certified `MemLpPer β̄'` (a hypothesis bundling `μ ∈ L^{β̄}_per`,
`u, V ∈ L^{β̄'}_per`), the conclusion follows by
`MemLp.of_le_mul (c := 1)`. -/
theorem muAux_integrability_quotient
    {betaBarPrime : ℝ≥0∞}
    {α β τ : ℝ}
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {G : (Fin d → ℝ) → ℝ}
    (hG_mem : MemLpPer (d := d) betaBarPrime G)
    (hG_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x)
    (h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)))
    (h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x)
    (h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
              (muAux k m u V Du H x ^ τ + 1)) :
    MemLpPer (d := d) betaBarPrime
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
          (muAux k m u V Du H x ^ τ + 1)) :=
  memLpPer_of_nonneg_le hG_mem h_meas h_quotient_nn hG_nn h_envelope

/-- **Witness-context quotient integrability (paper eq.
`eq:H-at-Du-mu.bounds`, line 1454) — Step B of the per-δ VI glue.**

Produces the `hQuot_m_mem` input of `mdelta_admissibility` with
`m := muAux k …`:
```
|Du|^{α(1+τ/β)} / (muAux^τ + 1) ∈ L^{β̄'}_per,   β̄' = ENNReal.ofReal ((β+1)/β).
```

The dominator is the paper's
`G x := C·(|k| + |u x| + |V x| + C·(muAux^β + 1) + C)`, obtained by
combining `hcong.lower`
`(1/C)(1/(μ^τ+1))‖Du‖^{αt} − C(μ^β+1) ≤ H(x, Du, μ)` (for `μ > 0`)
with the HJB membership `H(x, Du, μ) ≤ k − u + V` carried inside
`μ = muAux ∈ muAuxSet`.  The `μ = 0` boundary case is closed by passing
to the limit `ν ↓ 0` in the lower bound, using the standing full-`ℝ`
continuity `h_cont` of `H(x, Du(x), ·)` (the extra `+ C` summand of `G`
absorbs the resulting constant).

Each summand of `G` lies in `L^{β̄'}_per`: `|u|, |V|` directly, the
constants on the finite-measure cube, and `muAux^β` via
`muAux_mem_Lp_of_witnessData` + `MemLpPer.rpow_closure` (`β̄'·β = β+1 = β̄`). -/
theorem muAux_quotient_dominator_memLp
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muAux k m u V Du H x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  -- `μ` measurable (same construction as in `muAux_mem_Lp_of_witnessData`).
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  -- `μ ∈ L^{β̄}_per` (reuse Step A).
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAux k m u V Du H) :=
    muAux_mem_Lp_of_witnessData hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  -- The dominator `G x := C·(|k| + |u x| + |V x| + C·(μ^β + 1) + C)`.
  set G : (Fin d → ℝ) → ℝ :=
    fun x =>
      C * (|k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C)
    with hG_def
  -- (a) `μ^β ∈ L^{β̄'}_per` via `rpow_closure` (`β̄'·β = β + 1`).
  have hμ_nn_all : ∀ x, 0 ≤ muAux k m u V Du H x := by
    intro x
    have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
      muAuxSet_isClosed_of_continuousOn (h_cont x)
    have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
      muAuxSet_bddBelow k m u V Du H x
    have h_mem : muAux k m u V Du H x ∈ muAuxSet k m u V Du H x :=
      h_closed.csInf_mem (h_ne_all x) h_bdd
    exact h_mem.1
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hμβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖muAux k m u V Du H x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hμ_Lp)
  have hμβ :
      MemLpPer (d := d) betaBarPrime
        (fun x => muAux k m u V Du H x ^ β) := by
    have heq : (fun x => ‖muAux k m u V Du H x‖ ^ β)
        = (fun x => muAux k m u V Du H x ^ β) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ_nn_all x)]
    rwa [heq] at hμβ_norm
  -- (b) finite-measure cube for constants.
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- (c) the absolute-value pieces of `u`, `V`.
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  -- A local `MemLpPer` transport along a *pointwise* equality of functions
  -- (the `add`/`const_smul` closures produce `Pi`-sum forms that we collapse
  -- to single lambdas).
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  -- (d) `G ∈ L^{β̄'}_per`.
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (muAux k m u V Du H x ^ β + 1)) :=
      memLpPer_of_eq ((hμβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (muAux k m u V Du H x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  -- (e) `G ≥ 0` a.e.
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hμβ_nn : 0 ≤ muAux k m u V Du H x ^ β :=
      Real.rpow_nonneg (hμ_nn_all x) _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (muAux k m u V Du H x ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  -- (f) measurability of the quotient.
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : Measurable
        (fun x : Fin d → ℝ => muAux k m u V Du H x ^ τ + 1) :=
      (h_mu_meas.pow_const τ).add measurable_const
    exact (hnum.div hden).aestronglyMeasurable
  -- (g) the quotient is non-negative a.e.
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muAux k m u V Du H x ^ τ + 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muAux k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muAux k m u V Du H x ^ τ :=
        Real.rpow_nonneg (hμ_nn_all x) _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  -- (h) the pointwise domination `Q x ≤ G x` a.e.
  have hlower := hcong.lower
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower] with x hlow_x
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    -- HJB membership at `μ`: `u + H(x, Du, μ) - V ≤ k`.
    have h_mem : μ ∈ muAuxSet k m u V Du H x := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn (h_cont x)
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      exact h_closed.csInf_mem (h_ne_all x) h_bdd
    have hμ_nn : 0 ≤ μ := h_mem.1
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ k := h_mem.2.2
    have hH_le : H x (fun i => Du i x) μ ≤ k - u x + V x := by linarith
    -- The lower bound at `μ` (continuity-extended to `μ = 0`).
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hμ_nn with hμ0 | hμpos
      · -- `μ = 0`: pass to the limit `ν ↓ 0` in the lower bound.
        set g : ℝ → ℝ :=
          fun ν => (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
          with hg_def
        -- `ν ↦ ν^τ`, `ν ↦ ν^β` are continuous on ℝ (`0 ≤ τ`, `0 ≤ β`).
        have hrpowτ : Continuous (fun ν : ℝ => ν ^ τ) :=
          Real.continuous_rpow_const hτ_nn
        have hrpowβ : Continuous (fun ν : ℝ => ν ^ β) :=
          Real.continuous_rpow_const hβ.le
        -- `g` is continuous at `0` (`0^τ + 1 = 1 ≠ 0`).
        have hden_ne0 : (0 : ℝ) ^ τ + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ (0 : ℝ) ^ τ := Real.rpow_nonneg le_rfl _
          positivity
        have hgcont : ContinuousAt g 0 := by
          have hden : ContinuousAt (fun ν : ℝ => ν ^ τ + 1) 0 :=
            (hrpowτ.continuousAt).add continuousAt_const
          have hquot : ContinuousAt (fun ν : ℝ => (1 / (ν ^ τ + 1))) 0 :=
            continuousAt_const.div hden hden_ne0
          exact ((continuousAt_const.mul hquot).mul continuousAt_const).sub
            (continuousAt_const.mul ((hrpowβ.continuousAt).add continuousAt_const))
        -- `g ν ≤ H(x, Du, ν)` for `ν > 0`; both sides continuous, so at `ν = 0`.
        have h_le_pos : ∀ ν ∈ Set.Ioi (0 : ℝ),
            g ν ≤ H x (fun i => Du i x) ν := by
          intro ν hν
          have hlb := hlow_x (fun i => Du i x) ν hν
          show (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
            ≤ H x (fun i => Du i x) ν
          rw [hP_def]
          exact hlb
        have htend_g :
            Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          hgcont.continuousWithinAt.tendsto
        have htend_H :
            Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H x (fun i => Du i x) 0)) := by
          -- `H(x, Du x, ·)` is continuous on `Ici 0`, in particular at `0`
          -- (which lies in `Ici 0`); restrict the limit from `Ici 0` to its
          -- subset `Ioi 0`.
          have hwithin :
              Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
                (nhdsWithin 0 (Set.Ici 0))
                (nhds (H x (fun i => Du i x) 0)) :=
            ((h_cont x) 0 Set.self_mem_Ici).tendsto
          exact hwithin.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
        have hg0_le : g 0 ≤ H x (fun i => Du i x) 0 :=
          le_of_tendsto_of_tendsto htend_g htend_H
            (Filter.eventually_iff_exists_mem.mpr
              ⟨Set.Ioi 0, self_mem_nhdsWithin, h_le_pos⟩)
        -- Conclude at `μ = 0` (`hμ0 : 0 = μ`).
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [← hμ0]
        exact hg0_le
      · -- `μ > 0`: direct lower bound.
        have hlb := hlow_x (fun i => Du i x) μ hμpos
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [hP_def]
        exact hlb
    -- Combine: `(1/C)·(1/(μ^τ+1))·P ≤ H + C(μ^β+1) ≤ k - u + V + C(μ^β+1)`.
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ k - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    -- Multiply through by `C` and simplify `(1/(μ^τ+1))·P = P/(μ^τ+1)`.
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    -- Finish: `C·(k - u + V + C(μ^β+1)) ≤ G x`.
    have hk_le : k - u x + V x ≤ |k| + |u x| + |V x| := by
      have h1 : k ≤ |k| := le_abs_self k
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hbound2 :
        C * (k - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := hbound2
  -- Assemble via the quotient integrability bridge.
  have hresult := muAux_integrability_quotient (betaBarPrime := betaBarPrime)
    (α := α) (β := β) (τ := τ) (k := k) (m := m) (u := u) (V := V)
    (Du := Du) (H := H) hG_mem hG_nn h_meas h_envelope h_quotient_nn
  exact hresult

/-- **Nonnegative-witness sibling of `muAux_quotient_dominator_memLp`** (paper
eq. `eq:H-at-Du-mu.bounds`, line 1454, δ-truncation route, lines 1417–1506).

Identical conclusion (`|Du|^{α(1+τ/β)}/(muAux^τ+1) ∈ L^{β̄'}_per`), but the
standing full-`ℝ` continuity feeding Step A (`μ ∈ L^{β̄}_per`) is weakened to
`ContinuousOn (Ioi 0)`, with *no positivity witness on `m`*. The only structural
change from the original is that Step A routes through
`muAux_mem_Lp_of_witnessData_nonneg` (via the nonneg envelope). The `μ = 0`
boundary of the lower bound is closed exactly as in the original, by passing to
the limit `ν ↓ 0` using the standing on-`Ici 0` continuity `h_cont`; the
non-negativity `0 ≤ μ x` and HJB membership are read off the `Ici 0`-closedness
`muAuxSet_isClosed_of_continuousOn (h_cont x)` (no positivity needed). The
originals are kept untouched. -/
theorem muAux_quotient_dominator_memLp_of_m_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muAux k m u V Du H x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  -- `μ ∈ L^{β̄}_per` (reuse Step A, nonneg-witness route).
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAux k m u V Du H) :=
    muAux_mem_Lp_of_witnessData_nonneg hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  set G : (Fin d → ℝ) → ℝ :=
    fun x =>
      C * (|k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C)
    with hG_def
  have hμ_nn_all : ∀ x, 0 ≤ muAux k m u V Du H x := by
    intro x
    have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
      muAuxSet_isClosed_of_continuousOn (h_cont x)
    have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
      muAuxSet_bddBelow k m u V Du H x
    have h_mem : muAux k m u V Du H x ∈ muAuxSet k m u V Du H x :=
      h_closed.csInf_mem (h_ne_all x) h_bdd
    exact h_mem.1
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hμβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖muAux k m u V Du H x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hμ_Lp)
  have hμβ :
      MemLpPer (d := d) betaBarPrime
        (fun x => muAux k m u V Du H x ^ β) := by
    have heq : (fun x => ‖muAux k m u V Du H x‖ ^ β)
        = (fun x => muAux k m u V Du H x ^ β) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ_nn_all x)]
    rwa [heq] at hμβ_norm
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (muAux k m u V Du H x ^ β + 1)) :=
      memLpPer_of_eq ((hμβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (muAux k m u V Du H x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hμβ_nn : 0 ≤ muAux k m u V Du H x ^ β :=
      Real.rpow_nonneg (hμ_nn_all x) _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (muAux k m u V Du H x ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : Measurable
        (fun x : Fin d → ℝ => muAux k m u V Du H x ^ τ + 1) :=
      (h_mu_meas.pow_const τ).add measurable_const
    exact (hnum.div hden).aestronglyMeasurable
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muAux k m u V Du H x ^ τ + 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muAux k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muAux k m u V Du H x ^ τ :=
        Real.rpow_nonneg (hμ_nn_all x) _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  have hlower := hcong.lower
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower] with x hlow_x
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have h_mem : μ ∈ muAuxSet k m u V Du H x := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn (h_cont x)
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      exact h_closed.csInf_mem (h_ne_all x) h_bdd
    have hμ_nn : 0 ≤ μ := h_mem.1
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ k := h_mem.2.2
    have hH_le : H x (fun i => Du i x) μ ≤ k - u x + V x := by linarith
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hμ_nn with hμ0 | hμpos
      · set g : ℝ → ℝ :=
          fun ν => (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
          with hg_def
        have hrpowτ : Continuous (fun ν : ℝ => ν ^ τ) :=
          Real.continuous_rpow_const hτ_nn
        have hrpowβ : Continuous (fun ν : ℝ => ν ^ β) :=
          Real.continuous_rpow_const hβ.le
        have hden_ne0 : (0 : ℝ) ^ τ + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ (0 : ℝ) ^ τ := Real.rpow_nonneg le_rfl _
          positivity
        have hgcont : ContinuousAt g 0 := by
          have hden : ContinuousAt (fun ν : ℝ => ν ^ τ + 1) 0 :=
            (hrpowτ.continuousAt).add continuousAt_const
          have hquot : ContinuousAt (fun ν : ℝ => (1 / (ν ^ τ + 1))) 0 :=
            continuousAt_const.div hden hden_ne0
          exact ((continuousAt_const.mul hquot).mul continuousAt_const).sub
            (continuousAt_const.mul ((hrpowβ.continuousAt).add continuousAt_const))
        have h_le_pos : ∀ ν ∈ Set.Ioi (0 : ℝ),
            g ν ≤ H x (fun i => Du i x) ν := by
          intro ν hν
          have hlb := hlow_x (fun i => Du i x) ν hν
          show (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
            ≤ H x (fun i => Du i x) ν
          rw [hP_def]
          exact hlb
        have htend_g :
            Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          hgcont.continuousWithinAt.tendsto
        have htend_H :
            Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H x (fun i => Du i x) 0)) := by
          have hwithin :
              Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
                (nhdsWithin 0 (Set.Ici 0))
                (nhds (H x (fun i => Du i x) 0)) :=
            ((h_cont x) 0 Set.self_mem_Ici).tendsto
          exact hwithin.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
        have hg0_le : g 0 ≤ H x (fun i => Du i x) 0 :=
          le_of_tendsto_of_tendsto htend_g htend_H
            (Filter.eventually_iff_exists_mem.mpr
              ⟨Set.Ioi 0, self_mem_nhdsWithin, h_le_pos⟩)
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [← hμ0]
        exact hg0_le
      · have hlb := hlow_x (fun i => Du i x) μ hμpos
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [hP_def]
        exact hlb
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ k - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : k - u x + V x ≤ |k| + |u x| + |V x| := by
      have h1 : k ≤ |k| := le_abs_self k
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hbound2 :
        C * (k - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := hbound2
  have hresult := muAux_integrability_quotient (betaBarPrime := betaBarPrime)
    (α := α) (β := β) (τ := τ) (k := k) (m := m) (u := u) (V := V)
    (Du := Du) (H := H) hG_mem hG_nn h_meas h_envelope h_quotient_nn
  exact hresult

/-- **Browder–Minty witness sibling of `muAux_quotient_dominator_memLp`**
(paper eq. `eq:H-at-Du-mu.bounds`, line 1454; the witness density `m` plays
the role of `μ = muAux`).

The Browder–Minty witness density `m` *itself* satisfies the HJB inequality
`u + H(·, Du, m) − V ≤ 0` a.e. (paper line 1397, `eq:congest.HJleq0`) and is
a.e. non-negative (E2a). These two facts are exactly the pair that
`muAuxSet`-membership supplies in the `muAux` route (`m x ≤ μ`, `0 ≤ μ`,
`u + H(·,Du,μ) − V ≤ k`), so the same Young/HJB envelope argument applies with
`μ := m x` and `k := 0`, putting the **witness density `m`** in the denominator
of the ratio rather than the auxiliary truncation `muAux`.

The envelope is `G x := C·(|u x| + |V x| + C·(m x ^ β + 1) + C)` (no `|k|`
summand since `k = 0`; the extra `+ C` absorbs the `m = 0` boundary constant).
Each summand lies in `L^{β̄'}_per`: `|u|`, `|V|` directly, the constants on the
finite-measure cube, and `m^β` via `MemLpPer.rpow_closure` (`β̄'·β = β+1 = β̄`).
The `m x = 0` boundary of the lower bound is closed by passing to the limit
`ν ↓ 0`, using the standing on-`Ici 0` continuity `h_cont` of `H(x, Du(x), ·)`.

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch: the only inputs are
the witness HJB inequality, the witness non-negativity, the free witness
`MemLpPer` facts, and the standing on-`Ici 0` continuity. -/
theorem witness_quotient_dominator_memLp
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : AEMeasurable m (Measure.restrict volume (UnitCube d)))
    (hDu_meas : ∀ i, AEMeasurable (Du i) (Measure.restrict volume (UnitCube d)))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hm_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0)) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (m x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  -- `m^β ∈ L^{β̄'}_per` (rpow-closure, `β̄'·β = β+1`).
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hmβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖m x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hm_mem)
  -- The envelope `G x := C·(|u x| + |V x| + C·(m x ^ β + 1) + C)`.
  set G : (Fin d → ℝ) → ℝ :=
    fun x => C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C)
    with hG_def
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  have hmβabs :
      MemLpPer (d := d) betaBarPrime (fun x => |m x| ^ β) := hmβ_norm
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (|m x| ^ β + 1)) :=
      memLpPer_of_eq ((hmβabs.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |u x| + |V x|
            + C * (|m x| ^ β + 1) + C) :=
      memLpPer_of_eq
        ((((huabs.add hVabs).add h2).add (hconst C)))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hmβ_nn : 0 ≤ |m x| ^ β :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hinner_nn :
        0 ≤ |u x| + |V x| + C * (|m x| ^ β + 1) + C := by
      have h2 : 0 ≤ C * (|m x| ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (m x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : AEMeasurable (fun x : Fin d → ℝ => fun i => Du i x)
        (Measure.restrict volume (UnitCube d)) :=
      AEMeasurable.of_eval hDu_meas
    have hnum : AEMeasurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt)
        (Measure.restrict volume (UnitCube d)) :=
      (hDuvec.norm.pow_const αt)
    have hden : AEMeasurable
        (fun x : Fin d → ℝ => m x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      (hm_meas.pow_const τ).add aemeasurable_const
    exact (hnum.div hden).aestronglyMeasurable
  -- The quotient is non-negative a.e. (`m ≥ 0` gives `m^τ ≥ 0`).
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (m x ^ τ + 1) := by
    filter_upwards [hm_nn] with x hmx
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < m x ^ τ + 1 := by
      have : 0 ≤ m x ^ τ := Real.rpow_nonneg hmx _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  have hlower := hcong.lower
  -- The envelope domination `quotient ≤ G`.
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (m x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower, hm_nn, hHJB] with x hlow_x hmx hHJB_x
    set μ : ℝ := m x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have hμ_nn : 0 ≤ μ := hmx
    -- HJB inequality at the witness: `u + H(·,Du,m) − V ≤ 0`.
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ 0 := hHJB_x
    have hH_le : H x (fun i => Du i x) μ ≤ - u x + V x := by linarith
    -- Lower bound of `H`, with the `μ = 0` boundary closed by a limit.
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hμ_nn with hμ0 | hμpos
      · set g : ℝ → ℝ :=
          fun ν => (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
          with hg_def
        have hrpowτ : Continuous (fun ν : ℝ => ν ^ τ) :=
          Real.continuous_rpow_const hτ_nn
        have hrpowβ : Continuous (fun ν : ℝ => ν ^ β) :=
          Real.continuous_rpow_const hβ.le
        have hden_ne0 : (0 : ℝ) ^ τ + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ (0 : ℝ) ^ τ := Real.rpow_nonneg le_rfl _
          positivity
        have hgcont : ContinuousAt g 0 := by
          have hden : ContinuousAt (fun ν : ℝ => ν ^ τ + 1) 0 :=
            (hrpowτ.continuousAt).add continuousAt_const
          have hquot : ContinuousAt (fun ν : ℝ => (1 / (ν ^ τ + 1))) 0 :=
            continuousAt_const.div hden hden_ne0
          exact ((continuousAt_const.mul hquot).mul continuousAt_const).sub
            (continuousAt_const.mul ((hrpowβ.continuousAt).add continuousAt_const))
        have h_le_pos : ∀ ν ∈ Set.Ioi (0 : ℝ),
            g ν ≤ H x (fun i => Du i x) ν := by
          intro ν hν
          have hlb := hlow_x (fun i => Du i x) ν hν
          show (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
            ≤ H x (fun i => Du i x) ν
          rw [hP_def]
          exact hlb
        have htend_g :
            Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          hgcont.continuousWithinAt.tendsto
        have htend_H :
            Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H x (fun i => Du i x) 0)) := by
          have hwithin :
              Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
                (nhdsWithin 0 (Set.Ici 0))
                (nhds (H x (fun i => Du i x) 0)) :=
            ((h_cont x) 0 Set.self_mem_Ici).tendsto
          exact hwithin.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
        have hg0_le : g 0 ≤ H x (fun i => Du i x) 0 :=
          le_of_tendsto_of_tendsto htend_g htend_H
            (Filter.eventually_iff_exists_mem.mpr
              ⟨Set.Ioi 0, self_mem_nhdsWithin, h_le_pos⟩)
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [← hμ0]
        exact hg0_le
      · have hlb := hlow_x (fun i => Du i x) μ hμpos
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [hP_def]
        exact hlb
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (- u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : - u x + V x ≤ |u x| + |V x| := by
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hmβ_eq : μ ^ β = |m x| ^ β := by
      rw [hμ_def, abs_of_nonneg hmx]
    have hbound2 :
        C * (- u x + V x + C * (μ ^ β + 1))
          ≤ C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      rw [hmβ_eq] at *
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (- u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C) := hbound2
  exact memLpPer_of_nonneg_le hG_mem h_meas h_quotient_nn hG_nn h_envelope

/-- **`(a:Hat0)` sibling of `witness_quotient_dominator_memLp`** (the
δ-truncation/boundary route; paper eq. `eq:H-at-Du-mu.bounds`, line 1454, with
the `{m=0}` boundary value interpreted via (a:Hat0), paper line 1435).

Identical conclusion to `witness_quotient_dominator_memLp`
(`|Du|^{α(1+τ/β)}/(m^τ+1) ∈ L^{β̄'}_per`), with the overstrong on-`Ici 0`
continuity hypothesis `h_cont` replaced by the two `m=0` boundary riders
`hHat0 : HypothesisHat0 H` and `hAgree : H_zero_eq_Hext H`, exactly the pair
threaded through `CongestionRegularizedSequenceBuilderInputs.hH0`.

The only departure from the original body is the `m x = 0` boundary of the
envelope's lower bound `g 0 ≤ H(x, Du x, 0)`: instead of using on-`Ici 0`
continuity of the section to pass to the limit, we cast `g` and `H` into
`WithTop ℝ`, use the right-hand limit `H(x, Du, ·) → Hext H x (Du x) 0` from
`hHat0` (`tendsto_Hext_zero_of_exists`), the pointwise bound `g ν ≤ H(ν)` for
`ν > 0` (`hcong.lower`), and `hAgree` to transport the resulting
`g 0 ≤ Hext 0 = H(0)` back to raw. NO Ici-0 continuity, NO `Hext_finite_at_zero`,
NO `0 < m` crutch. The original is kept untouched. -/
theorem witness_quotient_dominator_memLp_hH0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : AEMeasurable m (Measure.restrict volume (UnitCube d)))
    (hDu_meas : ∀ i, AEMeasurable (Du i) (Measure.restrict volume (UnitCube d)))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hm_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (m x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  -- `m^β ∈ L^{β̄'}_per` (rpow-closure, `β̄'·β = β+1`).
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hmβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖m x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hm_mem)
  -- The envelope `G x := C·(|u x| + |V x| + C·(m x ^ β + 1) + C)`.
  set G : (Fin d → ℝ) → ℝ :=
    fun x => C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C)
    with hG_def
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  have hmβabs :
      MemLpPer (d := d) betaBarPrime (fun x => |m x| ^ β) := hmβ_norm
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (|m x| ^ β + 1)) :=
      memLpPer_of_eq ((hmβabs.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |u x| + |V x|
            + C * (|m x| ^ β + 1) + C) :=
      memLpPer_of_eq
        ((((huabs.add hVabs).add h2).add (hconst C)))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hmβ_nn : 0 ≤ |m x| ^ β :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hinner_nn :
        0 ≤ |u x| + |V x| + C * (|m x| ^ β + 1) + C := by
      have h2 : 0 ≤ C * (|m x| ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (m x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : AEMeasurable (fun x : Fin d → ℝ => fun i => Du i x)
        (Measure.restrict volume (UnitCube d)) :=
      AEMeasurable.of_eval hDu_meas
    have hnum : AEMeasurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt)
        (Measure.restrict volume (UnitCube d)) :=
      (hDuvec.norm.pow_const αt)
    have hden : AEMeasurable
        (fun x : Fin d → ℝ => m x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      (hm_meas.pow_const τ).add aemeasurable_const
    exact (hnum.div hden).aestronglyMeasurable
  -- The quotient is non-negative a.e. (`m ≥ 0` gives `m^τ ≥ 0`).
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (m x ^ τ + 1) := by
    filter_upwards [hm_nn] with x hmx
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < m x ^ τ + 1 := by
      have : 0 ≤ m x ^ τ := Real.rpow_nonneg hmx _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  have hlower := hcong.lower
  -- The envelope domination `quotient ≤ G`.
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (m x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower, hm_nn, hHJB,
        hHat0.exists_limit_at_zero, hAgree]
      with x hlow_x hmx hHJB_x hx_limit hx_agree
    set μ : ℝ := m x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have hμ_nn : 0 ≤ μ := hmx
    -- HJB inequality at the witness: `u + H(·,Du,m) − V ≤ 0`.
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ 0 := hHJB_x
    have hH_le : H x (fun i => Du i x) μ ≤ - u x + V x := by linarith
    -- The explicit lower-bound formula `g ν ≤ H(x, Du x, ν)` for `ν > 0`.
    set g : ℝ → ℝ :=
      fun ν => (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
      with hg_def
    have hg_le_H : ∀ ν : ℝ, 0 < ν → g ν ≤ H x (fun i => Du i x) ν := by
      intro ν hν
      have hlb := hlow_x (fun i => Du i x) ν hν
      show (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
        ≤ H x (fun i => Du i x) ν
      rw [hP_def]; exact hlb
    -- Lower bound of `H`, with the `μ = 0` boundary closed via (a:Hat0).
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hμ_nn with hμ0 | hμpos
      · -- `μ = 0`: cast into `WithTop ℝ`, take the limit `ν ↓ 0`.
        have hrpowτ : Continuous (fun ν : ℝ => ν ^ τ) :=
          Real.continuous_rpow_const hτ_nn
        have hrpowβ : Continuous (fun ν : ℝ => ν ^ β) :=
          Real.continuous_rpow_const hβ.le
        have hden_ne0 : (0 : ℝ) ^ τ + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ (0 : ℝ) ^ τ := Real.rpow_nonneg le_rfl _
          positivity
        have hgcont : ContinuousAt g 0 := by
          have hden : ContinuousAt (fun ν : ℝ => ν ^ τ + 1) 0 :=
            (hrpowτ.continuousAt).add continuousAt_const
          have hquot : ContinuousAt (fun ν : ℝ => (1 / (ν ^ τ + 1))) 0 :=
            continuousAt_const.div hden hden_ne0
          exact ((continuousAt_const.mul hquot).mul continuousAt_const).sub
            (continuousAt_const.mul ((hrpowβ.continuousAt).add continuousAt_const))
        have hTendsto_g :
            Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          (hgcont.continuousWithinAt).tendsto
        have hTendsto_H :
            Filter.Tendsto
              (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
          Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
        have hAgree_x :
            ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
              = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
          rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
        have hTendsto_gW :
            Filter.Tendsto
              (fun ν : ℝ => ((g ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (((g 0 : ℝ) : WithTop ℝ))) :=
          (WithTop.continuous_coe.continuousAt).tendsto.comp hTendsto_g
        have hEv_gle :
            ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
              ((g ν : ℝ) : WithTop ℝ)
                ≤ ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) := by
          refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
            self_mem_nhdsWithin, fun ν hν => ?_⟩
          exact_mod_cast hg_le_H ν hν
        have hg0_le_Hext :
            ((g 0 : ℝ) : WithTop ℝ)
              ≤ Hamiltonian.H_at_zero H x (fun i => Du i x) :=
          le_of_tendsto_of_tendsto hTendsto_gW hTendsto_H hEv_gle
        have hg0_le_raw :
            ((g 0 : ℝ) : WithTop ℝ)
              ≤ ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) := by
          rw [hAgree_x]; exact hg0_le_Hext
        have hg0_le_raw' : g 0 ≤ H x (fun i => Du i x) 0 := by
          exact_mod_cast hg0_le_raw
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [← hμ0]
        exact hg0_le_raw'
      · have hlb := hlow_x (fun i => Du i x) μ hμpos
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [hP_def]
        exact hlb
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (- u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : - u x + V x ≤ |u x| + |V x| := by
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hmβ_eq : μ ^ β = |m x| ^ β := by
      rw [hμ_def, abs_of_nonneg hmx]
    have hbound2 :
        C * (- u x + V x + C * (μ ^ β + 1))
          ≤ C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      rw [hmβ_eq] at *
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (- u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|u x| + |V x| + C * (|m x| ^ β + 1) + C) := hbound2
  exact memLpPer_of_nonneg_le hG_mem h_meas h_quotient_nn hG_nn h_envelope

/-- **Positive-witness sibling of `muAux_quotient_dominator_memLp`** (paper eq.
`eq:H-at-Du-mu.bounds`, line 1454, on the a.e. set `{0 < m x}`).

Identical conclusion (`|Du|^{α(1+τ/β)}/(muAux^τ+1) ∈ L^{β̄'}_per`), but the
standing full-`ℝ` continuity feeding Step A (`μ ∈ L^{β̄}_per`) is weakened to
`ContinuousOn (Ioi 0)`, at the cost of the extra a.e. positivity witness
`hm_pos : 0 < m x`. The only structural change from the original is that Step A
routes through `muAux_mem_Lp_of_witnessData_pos` (child-A); every other use of
continuity in the original body is already on `Ici 0` via the standing pointwise
`h_cont`. The original is kept untouched. -/
theorem muAux_quotient_dominator_memLp_of_m_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muAux k m u V Du H x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  -- `μ` measurable (same construction as in `muAux_mem_Lp_of_witnessData`).
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  -- `μ ∈ L^{β̄}_per` (reuse Step A, positive-witness sibling).
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAux k m u V Du H) :=
    muAux_mem_Lp_of_witnessData_pos hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos h_anti h_cont h_ne_all
  -- The dominator `G x := C·(|k| + |u x| + |V x| + C·(μ^β + 1) + C)`.
  set G : (Fin d → ℝ) → ℝ :=
    fun x =>
      C * (|k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C)
    with hG_def
  -- (a) `μ^β ∈ L^{β̄'}_per` via `rpow_closure` (`β̄'·β = β + 1`).
  have hμ_nn_all : ∀ x, 0 ≤ muAux k m u V Du H x := by
    intro x
    have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
      muAuxSet_isClosed_of_continuousOn (h_cont x)
    have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
      muAuxSet_bddBelow k m u V Du H x
    have h_mem : muAux k m u V Du H x ∈ muAuxSet k m u V Du H x :=
      h_closed.csInf_mem (h_ne_all x) h_bdd
    exact h_mem.1
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hμβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖muAux k m u V Du H x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hμ_Lp)
  have hμβ :
      MemLpPer (d := d) betaBarPrime
        (fun x => muAux k m u V Du H x ^ β) := by
    have heq : (fun x => ‖muAux k m u V Du H x‖ ^ β)
        = (fun x => muAux k m u V Du H x ^ β) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ_nn_all x)]
    rwa [heq] at hμβ_norm
  -- (b) finite-measure cube for constants.
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- (c) the absolute-value pieces of `u`, `V`.
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  -- A local `MemLpPer` transport along a *pointwise* equality of functions.
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  -- (d) `G ∈ L^{β̄'}_per`.
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (muAux k m u V Du H x ^ β + 1)) :=
      memLpPer_of_eq ((hμβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (muAux k m u V Du H x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  -- (e) `G ≥ 0` a.e.
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hμβ_nn : 0 ≤ muAux k m u V Du H x ^ β :=
      Real.rpow_nonneg (hμ_nn_all x) _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (muAux k m u V Du H x ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  -- (f) measurability of the quotient.
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : Measurable
        (fun x : Fin d → ℝ => muAux k m u V Du H x ^ τ + 1) :=
      (h_mu_meas.pow_const τ).add measurable_const
    exact (hnum.div hden).aestronglyMeasurable
  -- (g) the quotient is non-negative a.e.
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muAux k m u V Du H x ^ τ + 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muAux k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muAux k m u V Du H x ^ τ :=
        Real.rpow_nonneg (hμ_nn_all x) _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  -- (h) the pointwise domination `Q x ≤ G x` a.e.
  have hlower := hcong.lower
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower] with x hlow_x
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have h_mem : μ ∈ muAuxSet k m u V Du H x := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn (h_cont x)
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      exact h_closed.csInf_mem (h_ne_all x) h_bdd
    have hμ_nn : 0 ≤ μ := h_mem.1
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ k := h_mem.2.2
    have hH_le : H x (fun i => Du i x) μ ≤ k - u x + V x := by linarith
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hμ_nn with hμ0 | hμpos
      · set g : ℝ → ℝ :=
          fun ν => (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
          with hg_def
        have hrpowτ : Continuous (fun ν : ℝ => ν ^ τ) :=
          Real.continuous_rpow_const hτ_nn
        have hrpowβ : Continuous (fun ν : ℝ => ν ^ β) :=
          Real.continuous_rpow_const hβ.le
        have hden_ne0 : (0 : ℝ) ^ τ + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ (0 : ℝ) ^ τ := Real.rpow_nonneg le_rfl _
          positivity
        have hgcont : ContinuousAt g 0 := by
          have hden : ContinuousAt (fun ν : ℝ => ν ^ τ + 1) 0 :=
            (hrpowτ.continuousAt).add continuousAt_const
          have hquot : ContinuousAt (fun ν : ℝ => (1 / (ν ^ τ + 1))) 0 :=
            continuousAt_const.div hden hden_ne0
          exact ((continuousAt_const.mul hquot).mul continuousAt_const).sub
            (continuousAt_const.mul ((hrpowβ.continuousAt).add continuousAt_const))
        have h_le_pos : ∀ ν ∈ Set.Ioi (0 : ℝ),
            g ν ≤ H x (fun i => Du i x) ν := by
          intro ν hν
          have hlb := hlow_x (fun i => Du i x) ν hν
          show (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
            ≤ H x (fun i => Du i x) ν
          rw [hP_def]
          exact hlb
        have htend_g :
            Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          hgcont.continuousWithinAt.tendsto
        have htend_H :
            Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H x (fun i => Du i x) 0)) := by
          have hwithin :
              Filter.Tendsto (fun ν => H x (fun i => Du i x) ν)
                (nhdsWithin 0 (Set.Ici 0))
                (nhds (H x (fun i => Du i x) 0)) :=
            ((h_cont x) 0 Set.self_mem_Ici).tendsto
          exact hwithin.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
        have hg0_le : g 0 ≤ H x (fun i => Du i x) 0 :=
          le_of_tendsto_of_tendsto htend_g htend_H
            (Filter.eventually_iff_exists_mem.mpr
              ⟨Set.Ioi 0, self_mem_nhdsWithin, h_le_pos⟩)
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [← hμ0]
        exact hg0_le
      · have hlb := hlow_x (fun i => Du i x) μ hμpos
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [hP_def]
        exact hlb
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ k - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : k - u x + V x ≤ |k| + |u x| + |V x| := by
      have h1 : k ≤ |k| := le_abs_self k
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hbound2 :
        C * (k - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := hbound2
  -- Assemble via the quotient integrability bridge.
  have hresult := muAux_integrability_quotient (betaBarPrime := betaBarPrime)
    (α := α) (β := β) (τ := τ) (k := k) (m := m) (u := u) (V := V)
    (Du := Du) (H := H) hG_mem hG_nn h_meas h_envelope h_quotient_nn
  exact hresult

/-- **a.e.-rider sibling of `muAux_quotient_dominator_memLp_of_m_pos`**
(child-F).

Identical conclusion, but the pointwise closed-`Ici 0` antitonicity/continuity
and pointwise nonemptiness are replaced by a.e.-on-`Ioi 0` forms threaded with
`hm_pos`. The unconditional `muAux_nonneg` supplies pointwise non-negativity of
`μ`; measurability of `μ` is `AEMeasurable` (via
`muAux_measurable_of_Ioi0_of_m_pos`); the lower-bound envelope is established on
the a.e. set `{0 < m x}` (so the `μ = 0` boundary case is vacuous, and the
closedness/membership use `muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos`). -/
theorem muAux_quotient_dominator_memLp_of_m_pos'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muAux k m u V Du H x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  have hHJB_meas :
      ∀ a : ℝ,
        MeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        Measurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x) :=
      (hu_meas.add hHcomp).sub hV_meas
    exact hfun measurableSet_Iic
  -- `μ` is `AEMeasurable` (a.e.-on-`Ioi 0` route).
  have h_mu_aemeas : AEMeasurable (muAux k m u V Du H)
      (Measure.restrict volume (UnitCube d)) :=
    muAux_measurable_of_Ioi0_of_m_pos hm_meas hHJB_meas hm_pos hae_anti hcont hne
  -- `μ ∈ L^{β̄}_per` (reuse Step A, a.e.-rider sibling).
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAux k m u V Du H) :=
    muAux_mem_Lp_of_witnessData_pos' hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  set G : (Fin d → ℝ) → ℝ :=
    fun x =>
      C * (|k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C)
    with hG_def
  -- `μ ≥ 0` everywhere (unconditional).
  have hμ_nn_all : ∀ x, 0 ≤ muAux k m u V Du H x := fun x => muAux_nonneg x
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hμβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖muAux k m u V Du H x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hμ_Lp)
  have hμβ :
      MemLpPer (d := d) betaBarPrime
        (fun x => muAux k m u V Du H x ^ β) := by
    have heq : (fun x => ‖muAux k m u V Du H x‖ ^ β)
        = (fun x => muAux k m u V Du H x ^ β) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ_nn_all x)]
    rwa [heq] at hμβ_norm
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (muAux k m u V Du H x ^ β + 1)) :=
      memLpPer_of_eq ((hμβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (muAux k m u V Du H x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hμβ_nn : 0 ≤ muAux k m u V Du H x ^ β :=
      Real.rpow_nonneg (hμ_nn_all x) _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (muAux k m u V Du H x ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  -- measurability of the quotient (a.e.-version).
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : AEMeasurable
        (fun x : Fin d → ℝ => muAux k m u V Du H x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      (h_mu_aemeas.pow_const τ).add aemeasurable_const
    exact (hnum.aemeasurable.div hden).aestronglyMeasurable
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muAux k m u V Du H x ^ τ + 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muAux k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muAux k m u V Du H x ^ τ :=
        Real.rpow_nonneg (hμ_nn_all x) _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  have hlower := hcong.lower
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower, hm_pos, hne, hcont] with x hlow_x hx_mpos hx_ne hx_cont
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have h_mem : μ ∈ muAuxSet k m u V Du H x := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hx_mpos hx_cont
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      exact h_closed.csInf_mem hx_ne h_bdd
    have hμ_nn : 0 ≤ μ := h_mem.1
    -- On `{0 < m x}`, the infimum is `≥ m x > 0`.
    have hμ_pos : 0 < μ :=
      lt_of_lt_of_le hx_mpos (le_csInf hx_ne (fun b hb => hb.2.1))
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ k := h_mem.2.2
    have hH_le : H x (fun i => Du i x) μ ≤ k - u x + V x := by linarith
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      have hlb := hlow_x (fun i => Du i x) μ hμ_pos
      show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
        ≤ H x (fun i => Du i x) μ
      rw [hP_def]
      exact hlb
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ k - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : k - u x + V x ≤ |k| + |u x| + |V x| := by
      have h1 : k ≤ |k| := le_abs_self k
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hbound2 :
        C * (k - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := hbound2
  have hresult := muAux_integrability_quotient (betaBarPrime := betaBarPrime)
    (α := α) (β := β) (τ := τ) (k := k) (m := m) (u := u) (V := V)
    (Du := Du) (H := H) hG_mem hG_nn h_meas h_envelope h_quotient_nn
  exact hresult

/-- **`AEStronglyMeasurable V` sibling of `muAux_quotient_dominator_memLp_of_m_pos'`**
(child-G).

Identical to the primed version, but `V` is only `AEStronglyMeasurable`. The HJB
sublevel set is `NullMeasurableSet` and measurability routes through the `_aesm`
siblings (`muAux_measurable_of_Ioi0_of_m_pos_aesm`,
`muAux_mem_Lp_of_witnessData_pos_aesm`). The `_pos'` original is kept untouched. -/
theorem muAux_quotient_dominator_memLp_of_m_pos_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_pos :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muAux k m u V Du H x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  have hHJB_nmeas :
      ∀ a : ℝ,
        NullMeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k }
          (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        AEMeasurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x)
          (volume.restrict (UnitCube d)) :=
      ((hu_meas.add hHcomp).aemeasurable).sub hV_aesm.aemeasurable
    exact hfun.nullMeasurableSet_preimage measurableSet_Iic
  -- `μ` is `AEMeasurable` (a.e.-on-`Ioi 0` route).
  have h_mu_aemeas : AEMeasurable (muAux k m u V Du H)
      (Measure.restrict volume (UnitCube d)) :=
    muAux_measurable_of_Ioi0_of_m_pos_aesm hm_meas hHJB_nmeas hm_pos hae_anti
      hcont hne
  -- `μ ∈ L^{β̄}_per` (reuse Step A, `_aesm` sibling).
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAux k m u V Du H) :=
    muAux_mem_Lp_of_witnessData_pos_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  set G : (Fin d → ℝ) → ℝ :=
    fun x =>
      C * (|k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C)
    with hG_def
  have hμ_nn_all : ∀ x, 0 ≤ muAux k m u V Du H x := fun x => muAux_nonneg x
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hμβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖muAux k m u V Du H x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hμ_Lp)
  have hμβ :
      MemLpPer (d := d) betaBarPrime
        (fun x => muAux k m u V Du H x ^ β) := by
    have heq : (fun x => ‖muAux k m u V Du H x‖ ^ β)
        = (fun x => muAux k m u V Du H x ^ β) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ_nn_all x)]
    rwa [heq] at hμβ_norm
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (muAux k m u V Du H x ^ β + 1)) :=
      memLpPer_of_eq ((hμβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (muAux k m u V Du H x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hμβ_nn : 0 ≤ muAux k m u V Du H x ^ β :=
      Real.rpow_nonneg (hμ_nn_all x) _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (muAux k m u V Du H x ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : AEMeasurable
        (fun x : Fin d → ℝ => muAux k m u V Du H x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      (h_mu_aemeas.pow_const τ).add aemeasurable_const
    exact (hnum.aemeasurable.div hden).aestronglyMeasurable
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muAux k m u V Du H x ^ τ + 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muAux k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muAux k m u V Du H x ^ τ :=
        Real.rpow_nonneg (hμ_nn_all x) _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  have hlower := hcong.lower
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower, hm_pos, hne, hcont] with x hlow_x hx_mpos hx_ne hx_cont
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have h_mem : μ ∈ muAuxSet k m u V Du H x := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hx_mpos hx_cont
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      exact h_closed.csInf_mem hx_ne h_bdd
    have hμ_nn : 0 ≤ μ := h_mem.1
    have hμ_pos : 0 < μ :=
      lt_of_lt_of_le hx_mpos (le_csInf hx_ne (fun b hb => hb.2.1))
    have hHJB : u x + H x (fun i => Du i x) μ - V x ≤ k := h_mem.2.2
    have hH_le : H x (fun i => Du i x) μ ≤ k - u x + V x := by linarith
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      have hlb := hlow_x (fun i => Du i x) μ hμ_pos
      show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
        ≤ H x (fun i => Du i x) μ
      rw [hP_def]
      exact hlb
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ k - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : k - u x + V x ≤ |k| + |u x| + |V x| := by
      have h1 : k ≤ |k| := le_abs_self k
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hbound2 :
        C * (k - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := hbound2
  have hresult := muAux_integrability_quotient (betaBarPrime := betaBarPrime)
    (α := α) (β := β) (τ := τ) (k := k) (m := m) (u := u) (V := V)
    (Du := Du) (H := H) hG_mem hG_nn h_meas h_envelope h_quotient_nn
  exact hresult

/-- **Nonneg-`aesm` sibling of `muAux_quotient_dominator_memLp_of_m_pos_aesm`**
(child-D2a, the δ-truncation route; paper eq. `eq:H-at-Du-mu.bounds` line 1454
with the `{μ=0}` boundary value interpreted in the sense of (a:Hat0), paper line
1435).

Identical conclusion (`|Du|^{α(1+τ/β)}/(muAux^τ+1) ∈ L^{β̄'}_per`), with the
`_pos_aesm` version's `hm_pos` replaced by `hm_nn : 0 ≤ m x` a.e. The boundary
case `{μ x = 0}` (where the `_pos_aesm` version uses `0 < μ` to invoke the
Hamiltonian lower bound) is handled via the paper's (a:Hat0) extension: from the
`μ ≤ 0` characterisation (`muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg`) we
get rationals `q_n ↓ 0` with `H(x,Du,q_n) ≤ k - u + V`; combined with the
right-hand limit `H(x,Du,·) → Hext H x (Du x) 0` (from `hHat0`,
`tendsto_Hext_zero_of_exists`) this bounds `Hext H x (Du x) 0 ≤ (k-u+V : WithTop)`,
which is **finite** (paper line 1435: "finite value because of the upper bound").
The agreement rider `hAgree : H_zero_eq_Hext H` transports this to the raw value
`H x (Du x) 0 ≤ k - u + V`, and the explicit lower-bound `g` (continuous at `0`)
then gives `g 0 ≤ H x (Du x) 0`. NO Ici-0 continuity, NO `Hext_finite_at_zero`.
The `_pos`/`_pos_aesm`/`_nonneg` (Ici-0) originals are kept untouched. -/
theorem muAux_quotient_dominator_memLp_of_m_nonneg_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muAux k m u V Du H x ^ hcong.τ + 1)) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  have hHJB_nmeas :
      ∀ a : ℝ,
        NullMeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ k }
          (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        AEMeasurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x)
          (volume.restrict (UnitCube d)) :=
      ((hu_meas.add hHcomp).aemeasurable).sub hV_aesm.aemeasurable
    exact hfun.nullMeasurableSet_preimage measurableSet_Iic
  -- `μ` is `AEMeasurable` (a.e.-on-`Ioi 0` route, nonneg `_aesm`).
  have h_mu_aemeas : AEMeasurable (muAux k m u V Du H)
      (Measure.restrict volume (UnitCube d)) :=
    muAux_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hm_nn hae_anti
      hcont hne
  -- `μ ∈ L^{β̄}_per` (reuse Step A, nonneg `_aesm` sibling).
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (muAux k m u V Du H) :=
    muAux_mem_Lp_of_witnessData_nonneg_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti
  set G : (Fin d → ℝ) → ℝ :=
    fun x =>
      C * (|k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C)
    with hG_def
  have hμ_nn_all : ∀ x, 0 ≤ muAux k m u V Du H x := fun x => muAux_nonneg x
  have hexp_mu :
      betaBarPrime * ENNReal.ofReal β = ENNReal.ofReal (β + 1) := by
    rw [hbbp_def, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hμβ_norm :
      MemLpPer (d := d) betaBarPrime
        (fun x => ‖muAux k m u V Du H x‖ ^ β) :=
    MemLpPer.rpow_closure (d := d) hβ (by rw [hexp_mu]; exact hμ_Lp)
  have hμβ :
      MemLpPer (d := d) betaBarPrime
        (fun x => muAux k m u V Du H x ^ β) := by
    have heq : (fun x => ‖muAux k m u V Du H x‖ ^ β)
        = (fun x => muAux k m u V Du H x ^ β) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ_nn_all x)]
    rwa [heq] at hμβ_norm
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (muAux k m u V Du H x ^ β + 1)) :=
      memLpPer_of_eq ((hμβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (muAux k m u V Du H x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hG_def]
    have hμβ_nn : 0 ≤ muAux k m u V Du H x ^ β :=
      Real.rpow_nonneg (hμ_nn_all x) _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (muAux k m u V Du H x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (muAux k m u V Du H x ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : AEMeasurable
        (fun x : Fin d → ℝ => muAux k m u V Du H x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      (h_mu_aemeas.pow_const τ).add aemeasurable_const
    exact (hnum.aemeasurable.div hden).aestronglyMeasurable
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muAux k m u V Du H x ^ τ + 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muAux k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muAux k m u V Du H x ^ τ :=
        Real.rpow_nonneg (hμ_nn_all x) _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  have hlower := hcong.lower
  -- The envelope bound. The only departure from `_pos_aesm`: the `{μ=0}`
  -- boundary is reached via the (a:Hat0) extension instead of `0 < μ`.
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muAux k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hlower, hm_nn, hne, hcont, hae_anti,
        hHat0.exists_limit_at_zero, hAgree]
      with x hlow_x hx_mnn hx_ne hx_cont hx_anti hx_limit hx_agree
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have hμ_nn : 0 ≤ μ := muAux_nonneg x
    -- The explicit lower-bound formula `g ν ≤ H(x, Du x, ν)` for `ν > 0`.
    set g : ℝ → ℝ :=
      fun ν => (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
      with hg_def
    have hg_le_H : ∀ ν : ℝ, 0 < ν → g ν ≤ H x (fun i => Du i x) ν := by
      intro ν hν
      have hlb := hlow_x (fun i => Du i x) ν hν
      show (1 / C) * (1 / (ν ^ τ + 1)) * P - C * (ν ^ β + 1)
        ≤ H x (fun i => Du i x) ν
      rw [hP_def]; exact hlb
    -- `H(x, Du x, μ) ≤ k - u x + V x`. On `μ > 0` from `μ ∈ muAuxSet`; on
    -- `μ = 0` from the (a:Hat0) extension + the `μ ≤ 0` rationals.
    set b : ℝ := k - u x + V x with hb_def
    have hH_le : H x (fun i => Du i x) μ ≤ b := by
      -- Level-set characterisation at `a = μ ≥ 0`, `le_rfl`: either `HJB(μ) ≤ k`
      -- or `μ ≤ 0` (= 0).
      have hiff :=
        muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg
          (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H) (x := x)
          (a := μ) hx_mnn hμ_nn hx_cont hx_anti hx_ne
      rcases (hiff.mp (le_refl μ)).2 with hHJB | hμle0
      · -- `HJB(μ) ≤ k`.
        rw [hb_def]; linarith
      · -- `μ ≤ 0`, i.e. `μ = 0`: route the boundary value through `Hext`.
        have hμ0 : μ = 0 := le_antisymm hμle0 hμ_nn
        have hwit := (muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg
          (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H) (x := x)
          hx_mnn hx_anti hx_ne).mp hμle0
        -- Raw `H x (Du x) 0 ≤ b`.
        have hraw_le' : H x (fun i => Du i x) 0 ≤ b := by
          by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
              (q : ℝ) = 0 ∧ m x ≤ (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧
                (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
                u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ k
          · -- Case A: a `q = 0` witness exists ⇒ raw `H(0) ≤ b` directly.
            obtain ⟨_, _, hq_eq0, _, _, _, hHJB_q⟩ := hzero
            have hH0 : u x + H x (fun i => Du i x) (0 : ℝ) - V x ≤ k := by
              rw [← hq_eq0]; exact hHJB_q
            rw [hb_def]; linarith
          · -- Case B: every witness is positive ⇒ `H(ν) ≤ b` for all `ν > 0`,
            -- hence `Hext H x (Du x) 0 ≤ b`; transport to raw via `hAgree`.
            -- `hzero : ¬ ∃ n q, (q:ℝ)=0 ∧ … ` (every admissible witness is `> 0`).
            have hTendsto :
                Filter.Tendsto
                  (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
                  (nhdsWithin 0 (Set.Ioi 0))
                  (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
              Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
            have hPointwise : ∀ ν : ℝ, 0 < ν → H x (fun i => Du i x) ν ≤ b := by
              intro ν hν
              obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
              obtain ⟨q, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ := hwit n
              have hq_lt_ν : (q : ℝ) < ν := by
                have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
                  simpa only [one_div] using hn
                exact lt_trans hq_hi h1
              have hq_pos : 0 < (q : ℝ) := by
                rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
                · exact absurd
                    ⟨n, q, hq0.symm, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ hzero
                · exact hq_pos
              have hHq : H x (fun i => Du i x) (q : ℝ) ≤ b := by
                rw [hb_def]; linarith [hHJB_q]
              have hanti_le :
                  H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
                hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
              exact le_trans hanti_le hHq
            have hEv :
                ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
                  ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ)
                    ≤ ((b : ℝ) : WithTop ℝ) := by
              refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
                self_mem_nhdsWithin, fun ν hν => ?_⟩
              exact_mod_cast hPointwise ν hν
            have hHext_le :
                Hamiltonian.H_at_zero H x (fun i => Du i x)
                  ≤ ((b : ℝ) : WithTop ℝ) :=
              le_of_tendsto hTendsto hEv
            have hAgree_x :
                ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
                  = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
              rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
            have hraw_le :
                ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
                  ≤ ((b : ℝ) : WithTop ℝ) := by
              rw [hAgree_x]; exact hHext_le
            exact_mod_cast hraw_le
        rw [hμ0]; exact hraw_le'
    -- From `H(μ) ≤ k - u + V` and the lower bound `g μ ≤ H(μ)`, conclude.
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hμ_nn with hμ0 | hμpos
      · -- `μ = 0`: `g` is continuous at `0` and `g ν ≤ H(ν)` for `ν > 0`, but we
        -- only need `g 0 ≤ H(0)`.  Take the limit of `g ν ≤ H(ν)` as `ν ↓ 0`.
        have hrpowτ : Continuous (fun ν : ℝ => ν ^ τ) :=
          Real.continuous_rpow_const hτ_nn
        have hrpowβ : Continuous (fun ν : ℝ => ν ^ β) :=
          Real.continuous_rpow_const hβ.le
        have hden_ne0 : (0 : ℝ) ^ τ + 1 ≠ 0 := by
          have : (0 : ℝ) ≤ (0 : ℝ) ^ τ := Real.rpow_nonneg le_rfl _
          positivity
        have hgcont : ContinuousAt g 0 := by
          have hden : ContinuousAt (fun ν : ℝ => ν ^ τ + 1) 0 :=
            (hrpowτ.continuousAt).add continuousAt_const
          have hquot : ContinuousAt (fun ν : ℝ => (1 / (ν ^ τ + 1))) 0 :=
            continuousAt_const.div hden hden_ne0
          exact ((continuousAt_const.mul hquot).mul continuousAt_const).sub
            (continuousAt_const.mul ((hrpowβ.continuousAt).add continuousAt_const))
        -- `H(0) ≤ k - u + V` is `hH_le` at `μ = 0`.  We need `g 0 ≤ H(0)`.
        -- `g 0 = lim_{ν↓0} g ν` and `g ν ≤ H(ν)`; but `H(ν)` need not converge
        -- to `H(0)` raw.  Instead use the (a:Hat0) extension: `H(ν) → Hext 0`,
        -- and `g ν → g 0`, with `g ν ≤ H(ν)` on `Ioi 0`, so `g 0 ≤ Hext 0`;
        -- finiteness (from `hH_le` already proven) lets us untop.
        have hTendsto_g :
            Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
          (hgcont.continuousWithinAt).tendsto
        have hTendsto_H :
            Filter.Tendsto
              (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
          Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
        -- `Hext H x (Du x) 0` is finite: it equals the cast of the raw value.
        have hAgree_x :
            ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
              = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
          rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
        -- Cast `g` into `WithTop ℝ` and compare limits.
        have hTendsto_gW :
            Filter.Tendsto
              (fun ν : ℝ => ((g ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (((g 0 : ℝ) : WithTop ℝ))) :=
          (WithTop.continuous_coe.continuousAt).tendsto.comp hTendsto_g
        have hEv_gle :
            ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
              ((g ν : ℝ) : WithTop ℝ)
                ≤ ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) := by
          refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
            self_mem_nhdsWithin, fun ν hν => ?_⟩
          exact_mod_cast hg_le_H ν hν
        have hg0_le_Hext :
            ((g 0 : ℝ) : WithTop ℝ)
              ≤ Hamiltonian.H_at_zero H x (fun i => Du i x) :=
          le_of_tendsto_of_tendsto hTendsto_gW hTendsto_H hEv_gle
        have hg0_le_raw :
            ((g 0 : ℝ) : WithTop ℝ)
              ≤ ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) := by
          rw [hAgree_x]; exact hg0_le_Hext
        have hg0_le_raw' : g 0 ≤ H x (fun i => Du i x) 0 := by
          exact_mod_cast hg0_le_raw
        show g μ ≤ H x (fun i => Du i x) μ
        rw [← hμ0]; exact hg0_le_raw'
      · -- `μ > 0`.
        exact hg_le_H μ hμpos
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμ_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hμ_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ k - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by
        field_simp
      rw [hlhs] at hmul
      exact hmul
    have hk_le : k - u x + V x ≤ |k| + |u x| + |V x| := by
      have h1 : k ≤ |k| := le_abs_self k
      have h3 : -u x ≤ |u x| := by
        have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith
    have hbound2 :
        C * (k - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (k - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (μ ^ β + 1) + C) := hbound2
  have hresult := muAux_integrability_quotient (betaBarPrime := betaBarPrime)
    (α := α) (β := β) (τ := τ) (k := k) (m := m) (u := u) (V := V)
    (Du := Du) (H := H) hG_mem hG_nn h_meas h_envelope h_quotient_nn
  exact hresult

/-! ## The δ-truncated test density `μδ = max{μ, δ}` (paper lines 1459–1460)

The paper's `lem:weak.is.strong` Step 1 cannot use `(μ, u)` directly as a test
function in the variational inequality because `essinf μ` may be `0` (the
density can vanish on positive-measure sets, paper lines 375, 1459, 1495).
The remedy (paper line 1459) is the **admissible truncation**

  `μ_δ(x) := max{μ(x), δ}`,  `δ > 0`,

which satisfies `essinf μ_δ ≥ δ > 0` (paper line 1460) while remaining in the
same Lᵖ class as `μ` (it is squeezed: `μ ≤ μ_δ ≤ μ + δ`). Taking `δ → 0`
recovers `μ` by dominated convergence.

This block provides `μ_δ` and the two admissibility facts that the δ→0 passage
needs and that are self-contained at the producer level:

* `muAuxPerDelta_essinf_pos` — `δ ≤ᵐ μ_δ` (encodes `essinf μ_δ ≥ δ > 0`);
* `muAuxPerDelta_mem_Lp` — `μ_δ ∈ L^{β̄}_per`, from `μ ∈ L^{β̄}_per` via the
  squeeze `μ_δ ≤ μ + δ` (and `μ + δ ∈ L^{β̄}_per` by `MemLpPer.add_const`).

These are the paper's two `μ_δ ∈ 𝒦` ingredients on the *density side*; the
quotient-integrability conjunct of `𝒦` is handled in the HJB re-drain via the
SAME dominator as `μ` (since `μ_δ^{τ+1} ≥ μ^{τ+1}` for `0 ≤ τ`). -/

/-- The δ-truncated auxiliary density `μ_δ(x) = max{μ(x), δ}` (paper line
1459). For `δ > 0` it is bounded below a.e. by `δ` (hence `essinf > 0`) and
shares the Lᵖ class of `μ`. -/
def muAuxPerDelta
    (k δ : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => max (muAux k m u V Du H x) δ

lemma muAuxPerDelta_def
    (k δ : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muAuxPerDelta k δ m u V Du H x = max (muAux k m u V Du H x) δ := rfl

/-- `μ ≤ μ_δ` pointwise (`max` dominates its first argument). -/
lemma muAux_le_muAuxPerDelta
    (k δ : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muAux k m u V Du H x ≤ muAuxPerDelta k δ m u V Du H x :=
  le_max_left _ _

/-- `δ ≤ μ_δ` pointwise (`max` dominates its second argument). Encodes the
paper's `essinf μ_δ ≥ δ > 0` (paper line 1460), here in the everywhere form
which a fortiori gives the a.e. lower bound. -/
lemma muAuxPerDelta_ge_delta
    (k δ : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    δ ≤ muAuxPerDelta k δ m u V Du H x :=
  le_max_right _ _

/-- **`μ_δ` is bounded below a.e. by `δ`** (paper line 1460, `essinf μ_δ ≥
δ`). The a.e.-`≥ δ` form is the input the δ-truncated test function needs to be
admissible in `𝒦` (the uniform-lower-bound / `essinf > 0` conjunct). -/
lemma muAuxPerDelta_essinf_pos
    {k δ : ℝ} (hδ : 0 < δ)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ} :
    (fun _ => δ) ≤ᵐ[Measure.restrict volume (UnitCube d)]
      (muAuxPerDelta k δ m u V Du H) := by
  filter_upwards with x using muAuxPerDelta_ge_delta k δ m u V Du H x

/-- **`μ_δ ≤ μ + δ`** pointwise (paper line 1459, the upper squeeze).
`max a δ ≤ a + δ` whenever `0 ≤ a`; here `μ ≥ 0` always (`muAux_nonneg`),
so the bound holds with `0 ≤ δ`. -/
lemma muAuxPerDelta_le_add
    {k δ : ℝ} (hδ : 0 ≤ δ)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (x : Fin d → ℝ) :
    muAuxPerDelta k δ m u V Du H x ≤ muAux k m u V Du H x + δ := by
  rw [muAuxPerDelta_def]
  rcases le_total (muAux k m u V Du H x) δ with h | h
  · rw [max_eq_right h]; linarith [muAux_nonneg (k := k) (m := m) (u := u)
      (V := V) (Du := Du) (H := H) x]
  · rw [max_eq_left h]; linarith

/-- **`μ_δ ∈ L^{β̄}_per`** (paper line 1459). From `μ ∈ L^{β̄}_per` via the
squeeze `μ ≤ μ_δ ≤ μ + δ`: the upper dominator `μ + δ` is in `L^{β̄}_per`
(`MemLpPer.add_const`), and `μ_δ ≥ 0` (since `μ ≥ 0` and `δ ≥ 0`). -/
theorem muAuxPerDelta_mem_Lp
    {betaBar : ℝ≥0∞}
    {k δ : ℝ} (hδ : 0 ≤ δ)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (h_mu_mem : MemLpPer (d := d) betaBar (muAux k m u V Du H)) :
    MemLpPer (d := d) betaBar (muAuxPerDelta k δ m u V Du H) := by
  -- AE-strong-measurability of `μ_δ = max μ δ` from that of `μ`.
  have h_meas :
      AEStronglyMeasurable (muAuxPerDelta k δ m u V Du H)
        (Measure.restrict volume (UnitCube d)) := by
    have hmu := h_mu_mem.aestronglyMeasurable
    have hsup := hmu.sup (aestronglyMeasurable_const
      (b := δ) (μ := Measure.restrict volume (UnitCube d)))
    refine hsup.congr ?_
    filter_upwards with x using rfl
  -- The dominator `μ + δ ∈ L^{β̄}_per`.
  have h_dom_mem : MemLpPer (d := d) betaBar (fun x => muAux k m u V Du H x + δ) :=
    h_mu_mem.add_const δ
  -- `0 ≤ μ_δ` (a.e.): `μ_δ ≥ δ ≥ 0`.
  have h_mud_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAuxPerDelta k δ m u V Du H x := by
    filter_upwards with x
    exact le_trans hδ (muAuxPerDelta_ge_delta k δ m u V Du H x)
  -- `0 ≤ μ + δ` (a.e.): `μ ≥ 0` everywhere and `δ ≥ 0`.
  have h_dom_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ muAux k m u V Du H x + δ := by
    filter_upwards with x
    exact add_nonneg (muAux_nonneg (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) x) hδ
  -- `μ_δ ≤ μ + δ` (a.e.).
  have h_le :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        muAuxPerDelta k δ m u V Du H x ≤ muAux k m u V Du H x + δ := by
    filter_upwards with x
    exact muAuxPerDelta_le_add hδ x
  exact memLpPer_of_nonneg_le h_dom_mem h_meas h_mud_nn h_dom_nn h_le

/-! ## Generic `max(·, δ)` density truncation (T2 phase6 BB VIid child-1)

The δ-truncated admissible density `m_δ = max(m, δ)` used in the
`eq:identity-congestion` first-variation argument (paper `lem:weak.is.strong`,
lines 1524–1551). This is the `muAuxPerDelta` template *generalised* to an
arbitrary bare density `m : (Fin d → ℝ) → ℝ`, so the same toolkit serves both
the HJB-side auxiliary density `muAux` and the witness density of the weak-VI
identity argument.

Deliverables (all generic over `m`, exponent `p : ℝ≥0∞`):
* `mPerDelta_pos` — strict positivity `0 < m_δ x` (everywhere, since `m_δ ≥ δ > 0`);
* `mPerDelta_memLpPer` — `m_δ ∈ L^p_per`, uniform in `δ ∈ (0, ∞)` (dominator `m + δ`);
* `mPerDelta_sub_tendsto_ae` — `m_δ(x) - m(x) → 0` as `δ → 0⁺`, a.e. (for `m ≥ 0`);
* `mPerDelta_sub_eLpNormPer_tendsto` — Lp convergence `m_δ → m` as `δ → 0⁺`
  (DCT with dominator `m + 1 ∈ L^p_per`).

These are precisely the density-side `m_δ ∈ 𝒦` ingredients the paper needs; the
ratio-integrability transport `m ↦ m_δ` inside `congestionDomainK` and the full
`(m_δ, u + tφ) ∈ 𝒦` membership are deferred to the downstream first-variation
children (they reuse `mem_congestionBanachK_of_densityMemLp`, which keeps the
value/gradient slots fixed and consumes a `congestionDomainK` membership of the
density). -/

/-- The δ-truncated density `m_δ(x) = max{m(x), δ}` (paper line 1524). -/
def mPerDelta (m : (Fin d → ℝ) → ℝ) (δ : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => max (m x) δ

@[simp] lemma mPerDelta_def (m : (Fin d → ℝ) → ℝ) (δ : ℝ) (x : Fin d → ℝ) :
    mPerDelta m δ x = max (m x) δ := rfl

/-- `m ≤ m_δ` pointwise (`max` dominates its first argument). -/
lemma le_mPerDelta (m : (Fin d → ℝ) → ℝ) (δ : ℝ) (x : Fin d → ℝ) :
    m x ≤ mPerDelta m δ x :=
  le_max_left _ _

/-- `δ ≤ m_δ` pointwise (`max` dominates its second argument). -/
lemma mPerDelta_ge_delta (m : (Fin d → ℝ) → ℝ) (δ : ℝ) (x : Fin d → ℝ) :
    δ ≤ mPerDelta m δ x :=
  le_max_right _ _

/-- **Strict positivity** of the truncated density (paper line 1524: `m_δ ≥ δ > 0`).
This holds *everywhere*, not just a.e., since `m_δ x = max(m x, δ) ≥ δ`. -/
lemma mPerDelta_pos {δ : ℝ} (hδ : 0 < δ) (m : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    0 < mPerDelta m δ x :=
  lt_of_lt_of_le hδ (mPerDelta_ge_delta m δ x)

/-- **`m_δ ≤ m + δ`** pointwise (the upper squeeze, paper line 1524), valid when
`0 ≤ m x` and `0 ≤ δ`: `max(a, δ) ≤ a + δ` whenever `0 ≤ a` and `0 ≤ δ`. -/
lemma mPerDelta_le_add {δ : ℝ} (hδ : 0 ≤ δ) {m : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hmx : 0 ≤ m x) :
    mPerDelta m δ x ≤ m x + δ := by
  rw [mPerDelta_def]
  rcases le_total (m x) δ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- **`m_δ ∈ L^p_per`** (paper line 1524), uniform in `δ ∈ (0, ∞)`. From
`m ∈ L^p_per` and a.e. non-negativity of `m`, via the squeeze
`m ≤ m_δ ≤ m + δ`: the upper dominator `m + δ ∈ L^p_per` (`MemLpPer.add_const`),
and `m_δ ≥ δ ≥ 0`. -/
theorem mPerDelta_memLpPer {p : ℝ≥0∞} {δ : ℝ} (hδ : 0 ≤ δ)
    {m : (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) p m)
    (hm_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x) :
    MemLpPer (d := d) p (mPerDelta m δ) := by
  -- AE-strong-measurability of `m_δ = max m δ` from that of `m`.
  have h_meas :
      AEStronglyMeasurable (mPerDelta m δ)
        (Measure.restrict volume (UnitCube d)) := by
    have hm := hm_mem.aestronglyMeasurable
    have hsup := hm.sup (aestronglyMeasurable_const
      (b := δ) (μ := Measure.restrict volume (UnitCube d)))
    exact hsup.congr (Filter.Eventually.of_forall fun x => rfl)
  -- The dominator `m + δ ∈ L^p_per`.
  have h_dom_mem : MemLpPer (d := d) p (fun x => m x + δ) :=
    hm_mem.add_const δ
  -- `0 ≤ m_δ` (a.e.): `m_δ ≥ δ ≥ 0`.
  have h_mud_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ mPerDelta m δ x := by
    filter_upwards with x
    exact le_trans hδ (mPerDelta_ge_delta m δ x)
  -- `0 ≤ m + δ` (a.e.): `m ≥ 0` a.e. and `δ ≥ 0`.
  have h_dom_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ m x + δ := by
    filter_upwards [hm_nn] with x hmx
    exact add_nonneg hmx hδ
  -- `m_δ ≤ m + δ` (a.e.).
  have h_le :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        mPerDelta m δ x ≤ m x + δ := by
    filter_upwards [hm_nn] with x hmx
    exact mPerDelta_le_add hδ hmx
  exact memLpPer_of_nonneg_le h_dom_mem h_meas h_mud_nn h_dom_nn h_le

/-- **Pointwise convergence** `m_δ(x) - m(x) → 0` as `δ → 0⁺`, for `0 ≤ m x`.
If `m x > 0`, then for `δ ≤ m x` we have `m_δ x = m x`, so the difference is
eventually `0`; if `m x = 0`, then `m_δ x - m x = m_δ x = δ → 0`. In both cases
the limit is `0`. -/
lemma mPerDelta_sub_tendsto_ae_pt {m : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hmx : 0 ≤ m x) :
    Filter.Tendsto (fun δ : ℝ => mPerDelta m δ x - m x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- On `δ ≤ m x` the difference is `max(m x, δ) - m x = 0`; squeeze with `0 ≤ · ≤ δ`.
  have h_eventually :
      ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (0 : ℝ) ≤ mPerDelta m δ x - m x ∧ mPerDelta m δ x - m x ≤ δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    refine ⟨?_, ?_⟩
    · have := le_mPerDelta m δ x; linarith
    · have := mPerDelta_le_add hδ0 hmx; linarith
  -- Squeeze theorem: `0 ≤ f ≤ δ` and `δ → 0`.
  have h0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
  have hδ_to0 : Filter.Tendsto (fun δ : ℝ => δ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Filter.Tendsto.mono_left Filter.tendsto_id nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 hδ_to0 ?_ ?_
  · filter_upwards [h_eventually] with δ hδ using hδ.1
  · filter_upwards [h_eventually] with δ hδ using hδ.2

/-- **A.e. pointwise convergence** `m_δ → m` as `δ → 0⁺` for an a.e.-non-negative
density `m` (paper line 1524, the `m_δ → m a.e.` step of the DCT passage). -/
lemma mPerDelta_sub_tendsto_ae {m : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      Filter.Tendsto (fun δ : ℝ => mPerDelta m δ x - m x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  filter_upwards [hm_nn] with x hmx
  exact mPerDelta_sub_tendsto_ae_pt hmx

/-- **`L^p_per` convergence** `m_δ → m` as `δ → 0⁺` (paper line 1524, the DCT
dominator bound `m_δ ≤ m + 1 ∈ L^{β̄}` and `m_δ → m` a.e.).

Proved via the filter Lebesgue dominated convergence theorem applied to the
integrand `‖m_δ - m‖ₑ^p`, with dominator `(‖m‖ₑ + 1)^p` (using the eventual
bound `δ ≤ 1` near `0⁺`), then continuity of `· ^ (1/p)` at `0`. -/
theorem mPerDelta_sub_eLpNormPer_tendsto {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp_top : p ≠ ⊤)
    {m : (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) p m)
    (hm_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x) :
    Filter.Tendsto
      (fun δ : ℝ => eLpNormPer (d := d) p (fun x => mPerDelta m δ x - m x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ
  set q : ℝ := p.toReal with hq
  have hq_pos : 0 < q := ENNReal.toReal_pos hp0 hp_top
  -- Rewrite each `eLpNormPer` as `(∫⁻ ‖·‖ₑ^q)^(1/q)`.
  have h_rw : ∀ δ : ℝ,
      eLpNormPer (d := d) p (fun x => mPerDelta m δ x - m x)
        = (∫⁻ x, ‖mPerDelta m δ x - m x‖ₑ ^ q ∂μ) ^ (1 / q) := by
    intro δ
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
    simpa only [mPerDelta, Pi.sub_def, Pi.sup_def] using
      (hm_mem.aestronglyMeasurable.sup (aestronglyMeasurable_const (b := δ))).sub
        hm_mem.aestronglyMeasurable
  simp_rw [h_rw]
  -- It suffices that the inner lintegral tends to `0` (then `(·)^(1/q)` is
  -- continuous at `0` with `0^(1/q) = 0`).
  haveI : IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- AE-strong-measurability of the difference, for every `δ`.
  have hms : ∀ δ : ℝ, AEStronglyMeasurable
      (fun x => mPerDelta m δ x - m x) μ := by
    intro δ
    have hm := hm_mem.aestronglyMeasurable
    have hmax : AEStronglyMeasurable (mPerDelta m δ) μ :=
      (hm.sup (aestronglyMeasurable_const (b := δ) (μ := μ))).congr
        (Filter.Eventually.of_forall fun x => rfl)
    exact hmax.sub hm
  -- Finiteness of the dominator integral `∫⁻ (1 + ‖m‖ₑ^q)`.
  have h_fin : (∫⁻ x, (1 + ‖m x‖ₑ ^ q) ∂μ) ≠ ∞ := by
    rw [MeasureTheory.lintegral_add_left measurable_const]
    apply ENNReal.add_ne_top.2
    refine ⟨?_, ?_⟩
    · rw [MeasureTheory.lintegral_const]
      exact (ENNReal.mul_lt_top ENNReal.one_lt_top (measure_lt_top μ Set.univ)).ne
    · exact (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        hp0 hp_top hm_mem.eLpNormPer_lt_top).ne
  -- Per-point pointwise domination `‖m_δ x - m x‖ₑ^q ≤ 1 + ‖m x‖ₑ^q` for `0 ≤ δ ≤ 1`.
  have h_dom_pt : ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ 1 → ∀ {x : Fin d → ℝ}, 0 ≤ m x →
      ‖mPerDelta m δ x - m x‖ₑ ^ q ≤ 1 + ‖m x‖ₑ ^ q := by
    intro δ hδ0 hδ1 x hmx
    have h_diff_nn : 0 ≤ mPerDelta m δ x - m x := by
      have := le_mPerDelta m δ x; linarith
    have h_diff_le : mPerDelta m δ x - m x ≤ 1 := by
      have := mPerDelta_le_add hδ0 hmx; linarith
    have h_enorm_le : ‖mPerDelta m δ x - m x‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal h_diff_nn]
      calc ENNReal.ofReal (mPerDelta m δ x - m x)
          ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_diff_le
        _ = 1 := by simp
    calc ‖mPerDelta m δ x - m x‖ₑ ^ q
        ≤ (1 : ℝ≥0∞) ^ q :=
          ENNReal.rpow_le_rpow h_enorm_le (le_of_lt hq_pos)
      _ = 1 := by simp
      _ ≤ 1 + ‖m x‖ₑ ^ q := le_self_add
  -- Per-point convergence of the integrand to `0`.
  have h_conv_pt : ∀ {x : Fin d → ℝ}, 0 ≤ m x →
      Filter.Tendsto (fun δ : ℝ => ‖mPerDelta m δ x - m x‖ₑ ^ q)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro x hmx
    have h_sub := mPerDelta_sub_tendsto_ae_pt (m := m) (x := x) hmx
    have h_enorm : Filter.Tendsto
        (fun δ : ℝ => ‖mPerDelta m δ x - m x‖ₑ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : Filter.Tendsto (fun y : ℝ => ‖y‖ₑ) (nhds 0) (nhds ‖(0:ℝ)‖ₑ) :=
        (continuous_enorm.tendsto 0)
      simpa [Function.comp_def] using hc.comp h_sub
    have hrpow : Filter.Tendsto (fun y : ℝ≥0∞ => y ^ q) (nhds 0) (nhds 0) :=
      (ENNReal.continuous_rpow_const (y := q)).tendsto' 0 0
        (ENNReal.zero_rpow_of_pos hq_pos)
    simpa [Function.comp_def] using hrpow.comp h_enorm
  -- The inner lintegral tends to `0`, via sequential dominated convergence.
  have h_inner :
      Filter.Tendsto
        (fun δ : ℝ => ∫⁻ x, ‖mPerDelta m δ x - m x‖ₑ ^ q ∂μ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Filter.tendsto_iff_seq_tendsto]
    intro u hu
    -- `u n → 0⁺`: eventually `0 < u n` and `u n ≤ 1`; pick a tail index `N`.
    have hu_pos : ∀ᶠ n in Filter.atTop, u n ∈ Set.Ioi (0:ℝ) :=
      hu.eventually self_mem_nhdsWithin
    have hu_le1 : ∀ᶠ n in Filter.atTop, u n ≤ 1 := by
      have hmem : ∀ᶠ n in Filter.atTop, u n ∈ Set.Iic (1:ℝ) :=
        hu.eventually (nhdsWithin_le_nhds
          (Iic_mem_nhds (by norm_num : (0:ℝ) < 1)))
      simpa [Set.mem_Iic] using hmem
    obtain ⟨N, hN⟩ := (hu_pos.and hu_le1).exists_forall_of_atTop
    -- Apply the AE sequential DCT to the shifted tail sequence `n ↦ u (n + N)`,
    -- on which `0 < u (n+N) ≤ 1`, then undo the shift.
    rw [← Filter.tendsto_add_atTop_iff_nat N]
    have hbase :=
      MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (μ := μ)
        (F := fun n x => ‖mPerDelta m (u (n + N)) x - m x‖ₑ ^ q)
        (f := fun _ => (0 : ℝ≥0∞))
        (bound := fun x => 1 + ‖m x‖ₑ ^ q)
        (fun n => (hms (u (n + N))).enorm.pow_const q)
        ?_ h_fin ?_
    · simpa using hbase
    · -- Domination on the tail: `0 < u (n+N) ≤ 1`.
      intro n
      obtain ⟨hpos, hle1⟩ := hN (n + N) (Nat.le_add_left N n)
      filter_upwards [hm_nn] with x hmx
      exact h_dom_pt (le_of_lt hpos) hle1 hmx
    · -- A.e. pointwise convergence along the shifted sequence.
      filter_upwards [hm_nn] with x hmx
      have hu_shift : Filter.Tendsto (fun n => u (n + N))
          Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
        hu.comp (Filter.tendsto_add_atTop_nat N)
      exact (h_conv_pt hmx).comp hu_shift
  -- Continuity of `· ^ (1/q)` at `0`: `0 ^ (1/q) = 0`.
  have h1q : (0 : ℝ) < 1 / q := by positivity
  have hcont : Filter.Tendsto (fun y : ℝ≥0∞ => y ^ (1 / q)) (nhds 0) (nhds 0) :=
    (ENNReal.continuous_rpow_const (y := 1 / q)).tendsto' 0 0
      (ENNReal.zero_rpow_of_pos h1q)
  exact hcont.comp h_inner

/-! ## `δ → 0⁺` DCT passage for the `μ_re`/`≥`-side perturbation
(child-5c-D1b-ii)

The dominated-convergence engine that drives the `h_DCT` integral inequality
on the `μ_re`/`≥` side of paper Lemma `lem:weak.is.strong` (`eq:congest.HJ0`).

On the `μ_aux`/`≤` side, `muAux_integral_tendsto_of_m_nonneg` (above) clamps
the auxiliary output **upward** by `max(μ x, δSeq n)`.  On the `μ_re`/`≥`
side the perturbation goes the other way: the per-`δ` integrand is built from
a perturbed-output sequence `μδ n` that converges pointwise (a.e.) to the
limit density `μ = μ_re k m …`, and the second factor is `μδ n − mδ n` for a
perturbed reference `mδ n → m`.

Rather than commit to one specific clamp shape (the exact `min`-truncation is
fixed downstream by the per-`δ` VI lemma), this lemma states the DCT passage
**generically** over the perturbed sequences `μδ`, `mδ`: it only needs

* a.e. pointwise convergence `μδ n x → μ x` and `mδ n x → m x`,
* a.e. continuity of `H(x, Du x, ·)` **at the limit point** `μ x`
  (packaged as the hypothesis `hae_cont_at`, which the `μ_re` consumer
  supplies via on-`(0,∞)` continuity at the interior point `μ x > 0` on
  `{m x > 0}` and via the vanishing-prefactor squeeze on `{m x = 0}`), and
* an integrable dominator with per-`n` measurability and bound hypotheses.

The boundary `{μ x = 0}` is handled exactly as in
`muAux_integral_tendsto_of_m_nonneg`: there the target integrand vanishes and
the sequence integrand is squeezed to `0` by the uniform first-factor envelope
`G1`.  No continuity of `H` at `0` and no positivity-of-`m` crutch is used. -/
theorem muRe_integral_tendsto
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u μ : (Fin d → ℝ) → ℝ}
    {μδ mδ : ℕ → (Fin d → ℝ) → ℝ}
    (hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hμδ_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => μδ n x) Filter.atTop (nhds (μ x)))
    (hmδ_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => mδ n x) Filter.atTop (nhds (m x)))
    (hae_cont_at :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < μ x →
          ContinuousAt (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (μ x))
    (G1 : (Fin d → ℝ) → ℝ)
    (hf1_bd :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        |u x + H x (fun i => Du i x) (μδ n x) - V x| ≤ G1 x)
    -- On `{μ x = 0}` the target integrand vanishes; the squeeze needs the
    -- second factor `μδ n − mδ n → μ x − m x = 0` there.  The hypothesis
    -- `hbdry` records that the target value is `0` whenever `μ x = 0`, which
    -- the `μ_re` consumer discharges from `μ x = 0 ⇒ m x = 0` (`μ_re ≤ m`,
    -- `m ≥ 0`).
    (hbdry :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        μ x = 0 → m x = 0)
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          (u x + H x (fun i => Du i x) (μδ n x) - V x) * (μδ n x - mδ n x))
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(u x + H x (fun i => Du i x) (μδ n x) - V x) * (μδ n x - mδ n x)‖
          ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (μδ n x) - V x) * (μδ n x - mδ n x)
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (nhds
        (∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Bundle the per-`n` first-factor bounds into a single a.e. statement.
  have hf1_all :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ n, |u x + H x (fun i => Du i x) (μδ n x) - V x| ≤ G1 x :=
    (ae_all_iff).mpr hf1_bd
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            (u x + H x (fun i => Du i x) (μδ n x) - V x) * (μδ n x - mδ n x))
          Filter.atTop
          (nhds
            ((u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x))) := by
    filter_upwards [hμ_nn, hμδ_lim, hmδ_lim, hae_cont_at, hbdry, hf1_all]
      with x hx_μnn hx_μlim hx_mlim hx_cont hx_bdry hx_f1
    -- Second factor always converges (no continuity of `H` needed for it).
    have h_second :
        Filter.Tendsto (fun n => μδ n x - mδ n x) Filter.atTop
          (nhds (μ x - m x)) := hx_μlim.sub hx_mlim
    rcases eq_or_lt_of_le hx_μnn with hμ0 | hμpos
    · -- `μ x = 0` (so `m x = 0`): target integrand vanishes, squeeze the
      -- sequence by `G1 x · |second| → 0`.
      have hμx0 : μ x = 0 := hμ0.symm
      have hmx0 : m x = 0 := hx_bdry hμx0
      have htarget0 :
          (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x) = 0 := by
        rw [hμx0, hmx0]; ring
      rw [htarget0]
      have h_abs_le :
          ∀ n,
            |(u x + H x (fun i => Du i x) (μδ n x) - V x) * (μδ n x - mδ n x)|
              ≤ G1 x * |μδ n x - mδ n x| := by
        intro n
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hx_f1 n) (abs_nonneg _)
      have h_second0 :
          Filter.Tendsto (fun n => μδ n x - mδ n x) Filter.atTop (nhds 0) := by
        have : μ x - m x = 0 := by rw [hμx0, hmx0]; ring
        rwa [this] at h_second
      have h_upper :
          Filter.Tendsto
            (fun n => G1 x * |μδ n x - mδ n x|) Filter.atTop (nhds 0) := by
        have habs : Filter.Tendsto (fun n => |μδ n x - mδ n x|)
            Filter.atTop (nhds 0) := by
          have := (continuous_abs.tendsto (0 : ℝ)).comp h_second0
          simpa [Function.comp_def] using this
        have := habs.const_mul (G1 x)
        simpa using this
      apply squeeze_zero_norm (fun n => ?_) h_upper
      simpa [Real.norm_eq_abs] using h_abs_le n
    · -- `0 < μ x`: continuity of `H(x, Du x, ·)` at the interior point `μ x`.
      have hμx_pos : (0 : ℝ) < μ x := hμpos
      have h_cont_at :
          ContinuousAt (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (μ x) :=
        hx_cont hμx_pos
      have h_H_lim :
          Filter.Tendsto
            (fun n => H x (fun i => Du i x) (μδ n x))
            Filter.atTop (nhds (H x (fun i => Du i x) (μ x))) :=
        (h_cont_at.tendsto).comp hx_μlim
      have h_first :
          Filter.Tendsto
            (fun n => u x + H x (fun i => Du i x) (μδ n x) - V x)
            Filter.atTop
            (nhds (u x + H x (fun i => Du i x) (μ x) - V x)) :=
        ((tendsto_const_nhds.add h_H_lim).sub tendsto_const_nhds)
      exact h_first.mul h_second
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hmeas hbound_int hbound h_lim

end Congestion
end StationaryMFG
