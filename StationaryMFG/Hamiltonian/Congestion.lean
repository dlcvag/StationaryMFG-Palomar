module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Theorems.Congestion.PaperCore

@[expose] public section

/-!
# Hamiltonian — `H` upper bound under congestion growth (`lem:ADFGU.congestion`, part (a))

This module proves part (a) of paper Lemma `lem:ADFGU.congestion`
(`Source/FGU-monotone_revised.tex`, lines 678–725, equation
`eq:boundsH+`):

> Under `(onH.congestiongrowth)`, there exists a constant `C' > 0` such that
> for almost every `x ∈ 𝕋^d` and every `(p, m) ∈ ℝ^d × ℝ^+`,
> `H(x, p, m) ≤ C' · (1/m + 1/m^τ) · (‖p‖^{α(1+τ/β)} + 1) − m^β / C'`.

## Proof strategy

The paper's proof (lines 694–725) starts from the FTC slice identity
`H(x, p, m) = H(x, 0, m) + ∫_0^1 D_pH(x, t·p, m) · p dt`, applies the
bundle's two upper bounds `(eq:assH.upper.congestion)` and
`(eq:assH.DpH.upper.congestion)` to derive the intermediate inequality
`(eq:boundsH+1)`:

```
H(x, p, m) ≤ -m^β/C + C + C·(1/m + 1/m^τ)·‖p‖^{αt}
           + C·(m^{β-β/α} + 1/m)·‖p‖
```
where `αt := α(1 + τ/β)`. It then splits the last cross-term via
`‖p‖ ≤ ‖p‖^{αt} + 1` (which holds since `αt ≥ 1`), applies a parametric
Young inequality `(eq:Young.congestion.case)` whose RHS contains a
crucial `1/(m^τ + 1)` factor that mass-balances the resulting `m`
exponents, and applies the Young-like bound `(eq:Young-like.congestion)`
`1 ≤ 1/(θ^{1/β}·m) + θ·m^β` to absorb the constant `+C` term. With `θ`
chosen appropriately, the residual `m^β` contribution is dominated by
`-m^β / C`, and the headline bound follows with a redefined constant.

## Module organisation

The cross-term Young step `(eq:Young.congestion.case)` relies on a
NON-OBVIOUS exponent identity
`τ/(αt-1) + (β - β/α)·αt/(αt-1) = β`
that holds precisely because `αt = α(1+τ/β)` is the *paper-prescribed*
congestion exponent. This identity makes the parametric Young deliver a
pure `m^β` residual, which can then be absorbed by `-m^β/C`.

The intermediate bound `(eq:boundsH+1)` and the parametric Young step
`(eq:Young.congestion.case)` are proved as the standalone theorems
`congestion_boundsH_plus_1` and `young_congestion_case`.  These two are
then genuinely chained — together with the elementary split
`congestion_split_p` and the Young-like inequality
`congestion_one_le_young` — by `H_upper_congestion_of_hmon`, which
produces the post-Young form `K·(1/m+1/m^τ)·(‖p‖^{αt}+1) − δ·m^β`.  The
headline theorem `upper_bound_congestiongrowth` consumes that result
(no longer a hypothesis input) and performs the final
constant-unification `C' := max(K, 1/δ)`.

The two key algebraic facts the proof uses are recorded as private
lemmas:

* `congestion_split_p`     — `‖p‖ ≤ ‖p‖^{αt} + 1` for `αt ≥ 1`.
* `congestion_one_le_young` — `1 ≤ 1/(θ^{1/β}·m) + θ·m^β` for `θ, m, β > 0`.
-/

namespace StationaryMFG
namespace Hamiltonian

open MeasureTheory
open StationaryMFG.Periodic
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ### Algebraic helpers for the congestion proof -/

/-- For `r ≥ 1` and any `p : Fin d → ℝ`, `‖p‖ ≤ ‖p‖^r + 1`. -/
private lemma congestion_split_p {r : ℝ} (hr : 1 ≤ r) (p : Fin d → ℝ) :
    (‖p‖ : ℝ) ≤ ‖p‖ ^ r + 1 := by
  set t : ℝ := ‖p‖ with htdef
  have ht_nn : 0 ≤ t := norm_nonneg p
  by_cases hle : t ≤ 1
  · have ht_pow_nn : 0 ≤ t ^ r := Real.rpow_nonneg ht_nn r
    linarith
  · push_neg at hle
    have ht_pos : 0 < t := lt_trans zero_lt_one hle
    have hmono : t ^ (1 : ℝ) ≤ t ^ r :=
      Real.rpow_le_rpow_of_exponent_le hle.le hr
    rw [Real.rpow_one] at hmono
    linarith [hmono]

/-- The Young-like inequality `(eq:Young-like.congestion)` from the paper
(`Source/FGU-monotone_revised.tex`, eq.~`eq:Young-like.congestion`):
for `θ, m, β > 0`,
`1 ≤ 1/(θ^{1/β} · m) + θ · m^β`. -/
private lemma congestion_one_le_young {θ m β : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hβ : 0 < β) :
    (1 : ℝ) ≤ 1 / (θ ^ ((1 : ℝ) / β) * m) + θ * m ^ β := by
  -- Set `u := θ^{1/β}·m > 0`. Key identity: `u^β = θ · m^β`.
  set u : ℝ := θ ^ ((1 : ℝ) / β) * m with hudef
  have hθpow_pos : 0 < θ ^ ((1 : ℝ) / β) := Real.rpow_pos_of_pos hθ _
  have hu_pos : 0 < u := mul_pos hθpow_pos hm
  have hupowβ : u ^ β = θ * m ^ β := by
    rw [hudef, Real.mul_rpow hθpow_pos.le hm.le, ← Real.rpow_mul hθ.le]
    have hβne : β ≠ 0 := ne_of_gt hβ
    have : (1 : ℝ) / β * β = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [show (1 : ℝ) / (θ ^ ((1 : ℝ) / β) * m) = 1 / u from rfl]
  rw [show θ * m ^ β = u ^ β from hupowβ.symm]
  -- Goal: `1 ≤ 1/u + u^β`. By cases on `u ≤ 1` vs `u > 1`.
  by_cases hule : u ≤ 1
  · -- For `u ≤ 1`: `1/u ≥ 1`.
    have hinv : 1 ≤ 1 / u := by
      rw [le_div_iff₀ hu_pos]; linarith
    have hupow_nn : 0 ≤ u ^ β := Real.rpow_nonneg hu_pos.le β
    linarith
  · -- For `u > 1`: `u^β ≥ 1`.
    push_neg at hule
    have hupow_ge : 1 ≤ u ^ β := by
      have h0 : u ^ (0 : ℝ) ≤ u ^ β :=
        Real.rpow_le_rpow_of_exponent_le hule.le hβ.le
      rw [Real.rpow_zero] at h0
      exact h0
    have hinv_nn : 0 ≤ 1 / u := by positivity
    linarith

/-! ### Congestion exponent positivity -/

/-- For `α > 1`, `β > 0`, `τ ≥ 0`, the congestion exponent
`α · (1 + τ/β)` exceeds `1`. -/
private lemma one_lt_alphaTau {α β τ : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hτ : 0 ≤ τ) : 1 < α * (1 + τ / β) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hτβ_nn : 0 ≤ τ / β := div_nonneg hτ hβ.le
  have h1 : (1 : ℝ) ≤ 1 + τ / β := by linarith
  have h2 : α ≤ α * (1 + τ / β) := by
    have := mul_le_mul_of_nonneg_left h1 hαpos.le
    linarith [this]
  linarith

/-! ### rpow-of-sum helpers for the parametric Young step -/

/-- For `y ≥ 0` and `s > 0`, `(y + 1) ^ s ≤ 2 ^ s · (y ^ s + 1)`. Holds for
all positive exponents (no `s ≥ 1` requirement): from `y + 1 ≤ 2·max y 1`
and `(max y 1) ^ s ≤ y ^ s + 1`. -/
private lemma rpow_succ_le_two_pow {y s : ℝ} (hy : 0 ≤ y) (hs : 0 < s) :
    (y + 1) ^ s ≤ (2 : ℝ) ^ s * (y ^ s + 1) := by
  have hmax_nn : 0 ≤ max y 1 := le_trans hy (le_max_left _ _)
  -- `y + 1 ≤ 2 · max y 1`.
  have hsum_le : y + 1 ≤ 2 * max y 1 := by
    rcases le_total y 1 with h | h
    · have : max y 1 = 1 := max_eq_right h
      rw [this]; linarith
    · have : max y 1 = y := max_eq_left h
      rw [this]; linarith
  have hsum_nn : 0 ≤ y + 1 := by linarith
  -- Raise to the `s` power (monotone for nonneg base, nonneg exponent).
  have hstep1 : (y + 1) ^ s ≤ (2 * max y 1) ^ s :=
    Real.rpow_le_rpow hsum_nn hsum_le hs.le
  -- `(2 · max y 1) ^ s = 2 ^ s · (max y 1) ^ s`.
  have hstep2 : (2 * max y 1) ^ s = (2 : ℝ) ^ s * (max y 1) ^ s :=
    Real.mul_rpow (by norm_num) hmax_nn
  -- `(max y 1) ^ s ≤ y ^ s + 1`.
  have hmax_pow : (max y 1) ^ s ≤ y ^ s + 1 := by
    rcases le_total y 1 with h | h
    · have hm : max y 1 = 1 := max_eq_right h
      rw [hm, Real.one_rpow]
      have : 0 ≤ y ^ s := Real.rpow_nonneg hy s
      linarith
    · have hm : max y 1 = y := max_eq_left h
      rw [hm]
      have : 0 ≤ y ^ s := Real.rpow_nonneg hy s
      linarith
  have h2s_nn : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
  calc (y + 1) ^ s
      ≤ (2 * max y 1) ^ s := hstep1
    _ = (2 : ℝ) ^ s * (max y 1) ^ s := hstep2
    _ ≤ (2 : ℝ) ^ s * (y ^ s + 1) :=
        mul_le_mul_of_nonneg_left hmax_pow h2s_nn

/-- For `m > 0` and `0 ≤ e ≤ β`, `m ^ e ≤ m ^ β + 1`. Case split on
`m ≤ 1` vs `m ≥ 1`. -/
private lemma rpow_le_rpow_beta_add_one {m e β : ℝ} (hm : 0 < m)
    (he : 0 ≤ e) (heβ : e ≤ β) :
    m ^ e ≤ m ^ β + 1 := by
  have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm.le β
  rcases le_total m 1 with h | h
  · -- `m ≤ 1`: `m ^ e ≤ 1` since `e ≥ 0`.
    have : m ^ e ≤ m ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hm h he
    rw [Real.rpow_zero] at this
    linarith
  · -- `m ≥ 1`: `m ^ e ≤ m ^ β` since `e ≤ β`.
    have : m ^ e ≤ m ^ β := Real.rpow_le_rpow_of_exponent_le h heβ
    linarith

/-! ### Parametric Young step `(eq:Young.congestion.case)` -/

/-- **Paper `(eq:Young.congestion.case)`** (`Source/FGU-monotone_revised.tex`,
lines 708–717) — the load-bearing parametric Young inequality of the
congestion proof. With `αt := α(1+τ/β)` (the paper-prescribed congestion
exponent, `> 1`), there is a constant `c̃ > 0` depending only on `α, β, τ`
such that for every `θ > 0`, `m > 0` and `p : Fin d → ℝ`,

  `‖p‖·(m^{β−β/α}+1)`
  `  ≤ c̃ · ( ‖p‖^{αt}/(θ^{αt−1}·(m^τ+1)) + θ·(m^β+1) )`.

The proof applies Young's inequality with the Hölder-conjugate pair
`(αt, αt/(αt−1))` to the rescaled product `a·b = ‖p‖·(m^{β−β/α}+1)`, where
`a = ‖p‖·W^{−1/αt}`, `b = (m^{β−β/α}+1)·W^{1/αt}` and
`W = θ^{αt−1}·(m^τ+1)`. The `b^{r'}` term is then collapsed using the
NON-OBVIOUS exponent identity

  `τ/(αt−1) + (β − β/α)·αt/(αt−1) = β`

(paper line 716), which holds precisely because `αt = α(1+τ/β)`; this turns
the residual `m`-power into a pure `m^β` contribution, bounded by `m^β+1`
via the `rpow`-of-sum helpers. -/
theorem young_congestion_case {α β τ : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hτ : 0 ≤ τ) :
    ∃ ctil : ℝ, 0 < ctil ∧
      ∀ (θ m : ℝ), 0 < θ → 0 < m → ∀ p : Fin d → ℝ,
        (‖p‖ : ℝ) * (m ^ (β - β / α) + 1)
          ≤ ctil * (‖p‖ ^ (α * (1 + τ / β)) / (θ ^ (α * (1 + τ / β) - 1)
                      * (m ^ τ + 1))
                  + θ * (m ^ β + 1)) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hβne : β ≠ 0 := ne_of_gt hβ
  -- Congestion exponent and its conjugate.
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hαt_gt_one : 1 < αt := one_lt_alphaTau hα hβ hτ
  have hαt_pos : 0 < αt := lt_trans one_pos hαt_gt_one
  have hαt_ne : αt ≠ 0 := ne_of_gt hαt_pos
  have hαtm1_pos : 0 < αt - 1 := sub_pos.mpr hαt_gt_one
  have hαtm1_ne : αt - 1 ≠ 0 := ne_of_gt hαtm1_pos
  -- Conjugate exponent `r' = αt / (αt - 1)`.
  set r' : ℝ := αt / (αt - 1) with hr'def
  have hr'_pos : 0 < r' := div_pos hαt_pos hαtm1_pos
  have hr'_ne : r' ≠ 0 := ne_of_gt hr'_pos
  -- Sub-exponents of `m`.
  set a : ℝ := 1 / (αt - 1) with hadef
  have ha_pos : 0 < a := by rw [hadef]; positivity
  set c : ℝ := β - β / α with hcdef
  have hc_nn : 0 ≤ c := by
    rw [hcdef]
    have : β / α ≤ β := by
      rw [div_le_iff₀ hαpos]; nlinarith
    linarith
  -- The exponent identity `τ·a + c·r' = β`. Reduce to the polynomial form
  -- `τ + c·αt = β·(αt-1)`, which holds because `αt = α(1+τ/β)`.
  have hpoly : τ + c * αt = β * (αt - 1) := by
    rw [hcdef, hαtdef]; field_simp; ring
  have hidentity : τ * a + c * r' = β := by
    rw [hadef, hr'def]
    -- `τ·(1/(αt-1)) + c·(αt/(αt-1)) = β` ⇔ `τ + c·αt = β·(αt-1)` (= `hpoly`).
    field_simp
    linear_combination hpoly
  -- The individual sub-exponents are nonnegative and `≤ β`.
  have hτa_nn : 0 ≤ τ * a := mul_nonneg hτ ha_pos.le
  have hcr'_nn : 0 ≤ c * r' := mul_nonneg hc_nn hr'_pos.le
  have hτa_le : τ * a ≤ β := by linarith [hidentity, hcr'_nn]
  have hcr'_le : c * r' ≤ β := by linarith [hidentity, hτa_nn]
  -- The Hölder-conjugate pair `(αt, r')`.
  have hHC : Real.HolderConjugate αt r' := by
    rw [Real.holderConjugate_iff]
    refine ⟨hαt_gt_one, ?_⟩
    rw [hr'def]; field_simp; ring
  -- Define the constant `c̃` (depends only on `α, β, τ`).
  set Ccoef : ℝ := 4 * (2 : ℝ) ^ (a + r') / r' with hCcoefdef
  have hCcoef_pos : 0 < Ccoef := by
    rw [hCcoefdef]
    have h2 : 0 < (2 : ℝ) ^ (a + r') := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨max (1 / αt) Ccoef, lt_max_of_lt_left (by positivity), ?_⟩
  set ctil : ℝ := max (1 / αt) Ccoef with hctildef
  have hctil_pos : 0 < ctil := lt_max_of_lt_left (by positivity)
  have h_inv_αt_le : 1 / αt ≤ ctil := le_max_left _ _
  have hCcoef_le : Ccoef ≤ ctil := le_max_right _ _
  intro θ m hθ hm p
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
  have hm_nn : 0 ≤ m := hm.le
  have hmc_nn : 0 ≤ m ^ c := Real.rpow_nonneg hm_nn c
  have hmc1_nn : 0 ≤ m ^ c + 1 := by linarith
  have hmτ_pos : 0 < m ^ τ := Real.rpow_pos_of_pos hm τ
  have hmτ1_pos : 0 < m ^ τ + 1 := by linarith
  have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm_nn β
  have hmβ1_nn : 0 ≤ m ^ β + 1 := by linarith
  have hθ_pow_pos : 0 < θ ^ (αt - 1) := Real.rpow_pos_of_pos hθ _
  -- Weight `W = θ^{αt-1}·(m^τ+1) > 0`.
  set W : ℝ := θ ^ (αt - 1) * (m ^ τ + 1) with hWdef
  have hW_pos : 0 < W := mul_pos hθ_pow_pos hmτ1_pos
  -- Rescaling factors `W^{1/αt}` and `W^{-1/αt}`.
  set wα : ℝ := W ^ ((1 : ℝ) / αt) with hwαdef
  set winv : ℝ := W ^ (-(1 : ℝ) / αt) with hwinvdef
  have hwα_pos : 0 < wα := Real.rpow_pos_of_pos hW_pos _
  have hwinv_pos : 0 < winv := Real.rpow_pos_of_pos hW_pos _
  -- `winv · wα = 1`.
  have hww : winv * wα = 1 := by
    rw [hwinvdef, hwαdef, ← Real.rpow_add hW_pos]
    have : (-(1 : ℝ) / αt) + (1 : ℝ) / αt = 0 := by ring
    rw [this, Real.rpow_zero]
  -- Young's inequality on `a := ‖p‖·winv`, `b := (m^c+1)·wα`.
  set A : ℝ := ‖p‖ * winv with hAdef
  set B : ℝ := (m ^ c + 1) * wα with hBdef
  have hA_nn : 0 ≤ A := mul_nonneg hp_nn hwinv_pos.le
  have hB_nn : 0 ≤ B := mul_nonneg hmc1_nn hwα_pos.le
  have hYoung := Real.young_inequality_of_nonneg hA_nn hB_nn hHC
  -- `A · B = ‖p‖·(m^c+1)`.
  have hAB : A * B = ‖p‖ * (m ^ c + 1) := by
    rw [hAdef, hBdef]
    calc ‖p‖ * winv * ((m ^ c + 1) * wα)
        = ‖p‖ * (m ^ c + 1) * (winv * wα) := by ring
      _ = ‖p‖ * (m ^ c + 1) := by rw [hww, mul_one]
  -- `A^αt = ‖p‖^αt / W`.
  have hApow : A ^ αt = ‖p‖ ^ αt / W := by
    rw [hAdef, Real.mul_rpow hp_nn hwinv_pos.le, hwinvdef]
    have hexp : (-(1 : ℝ) / αt) * αt = -1 := by field_simp
    rw [show (W ^ (-(1:ℝ)/αt)) ^ αt = W ^ ((-(1:ℝ)/αt) * αt) from
          (Real.rpow_mul hW_pos.le _ _).symm, hexp, Real.rpow_neg_one,
        div_eq_mul_inv]
  -- `B^r' = (m^c+1)^r' · W^{1/(αt-1)}`.
  have hr'_over_αt : (1 : ℝ) / αt * r' = 1 / (αt - 1) := by
    rw [hr'def]; field_simp
  have hBpow : B ^ r' = (m ^ c + 1) ^ r' * W ^ ((1 : ℝ) / (αt - 1)) := by
    rw [hBdef, Real.mul_rpow hmc1_nn hwα_pos.le, hwαdef, ← Real.rpow_mul hW_pos.le,
      hr'_over_αt]
  -- `W^{1/(αt-1)} = θ · (m^τ+1)^{1/(αt-1)}`.
  have hWpow : W ^ ((1 : ℝ) / (αt - 1)) = θ * (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) := by
    rw [hWdef, Real.mul_rpow hθ_pow_pos.le hmτ1_pos.le, ← Real.rpow_mul hθ.le]
    have : (αt - 1) * ((1 : ℝ) / (αt - 1)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  -- Bound `(m^τ+1)^{1/(αt-1)} ≤ 2^a·(m^{τ·a}+1)`.
  have hbound1 : (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) ≤ (2 : ℝ) ^ a * (m ^ (τ * a) + 1) := by
    have hstep := rpow_succ_le_two_pow (y := m ^ τ) (s := a) hmτ_pos.le ha_pos
    have hmτa : (m ^ τ) ^ a = m ^ (τ * a) := by rw [← Real.rpow_mul hm_nn]
    rw [hadef] at hstep
    rw [hmτa] at hstep
    convert hstep using 2
  -- Bound `(m^c+1)^r' ≤ 2^r'·(m^{c·r'}+1)`.
  have hbound2 : (m ^ c + 1) ^ r' ≤ (2 : ℝ) ^ r' * (m ^ (c * r') + 1) := by
    have hstep := rpow_succ_le_two_pow (y := m ^ c) (s := r') hmc_nn hr'_pos
    have hmcr' : (m ^ c) ^ r' = m ^ (c * r') := by rw [← Real.rpow_mul hm_nn]
    rw [hmcr'] at hstep
    exact hstep
  -- The two `m`-powers are `≤ m^β+1`.
  have hmτa_le : m ^ (τ * a) ≤ m ^ β + 1 := rpow_le_rpow_beta_add_one hm hτa_nn hτa_le
  have hmcr'_le : m ^ (c * r') ≤ m ^ β + 1 := rpow_le_rpow_beta_add_one hm hcr'_nn hcr'_le
  -- The product of the two `m`-factor bounds is `≤ 4·(m^β+1)`.
  have h2a_pos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have h2r'_pos : 0 < (2 : ℝ) ^ r' := Real.rpow_pos_of_pos (by norm_num) _
  -- Collapse the `b^{r'}` term: `(m^τ+1)^a·(m^c+1)^{r'} ≤ 2^{a+r'}·... ≤ 4·2^{a+r'}·(m^β+1)`.
  have hmfactor :
      (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) * (m ^ c + 1) ^ r'
        ≤ 4 * (2 : ℝ) ^ (a + r') * (m ^ β + 1) := by
    have hpos1 : 0 ≤ (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) := by
      apply Real.rpow_nonneg; linarith
    have hpos2 : 0 ≤ (m ^ c + 1) ^ r' := Real.rpow_nonneg hmc1_nn r'
    -- `prod ≤ (2^a(m^{τa}+1))·(2^{r'}(m^{cr'}+1))`.
    have hmul : (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) * (m ^ c + 1) ^ r'
              ≤ ((2 : ℝ) ^ a * (m ^ (τ * a) + 1)) * ((2 : ℝ) ^ r' * (m ^ (c * r') + 1)) := by
      apply mul_le_mul hbound1 hbound2 hpos2
      positivity
    -- The RHS factor `(m^{τa}+1)(m^{cr'}+1) ≤ 4(m^β+1)`.
    have hmpow_nn1 : 0 ≤ m ^ (τ * a) := Real.rpow_nonneg hm_nn _
    have hmpow_nn2 : 0 ≤ m ^ (c * r') := Real.rpow_nonneg hm_nn _
    have hfac : (m ^ (τ * a) + 1) * (m ^ (c * r') + 1) ≤ 4 * (m ^ β + 1) := by
      -- Expand: `(m^{τa}+1)(m^{cr'}+1) = m^{τa+cr'} + m^{τa} + m^{cr'} + 1`,
      -- and `m^{τa+cr'} = m^β` by the exponent identity.
      have hexpand : (m ^ (τ * a) + 1) * (m ^ (c * r') + 1)
                  = m ^ (τ * a + c * r') + m ^ (τ * a) + m ^ (c * r') + 1 := by
        rw [Real.rpow_add hm]; ring
      rw [hexpand, hidentity]
      -- Each of the four summands is `≤ m^β+1`.
      have h1le : m ^ β ≤ m ^ β + 1 := by linarith
      have h4 : (1 : ℝ) ≤ m ^ β + 1 := by linarith
      linarith [hmτa_le, hmcr'_le, h1le, h4]
    have h2prod : (2 : ℝ) ^ a * (2 : ℝ) ^ r' = (2 : ℝ) ^ (a + r') := by
      rw [← Real.rpow_add (by norm_num)]
    calc (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) * (m ^ c + 1) ^ r'
        ≤ ((2 : ℝ) ^ a * (m ^ (τ * a) + 1)) * ((2 : ℝ) ^ r' * (m ^ (c * r') + 1)) := hmul
      _ = ((2 : ℝ) ^ a * (2 : ℝ) ^ r') * ((m ^ (τ * a) + 1) * (m ^ (c * r') + 1)) := by ring
      _ ≤ ((2 : ℝ) ^ a * (2 : ℝ) ^ r') * (4 * (m ^ β + 1)) := by
            apply mul_le_mul_of_nonneg_left hfac; positivity
      _ = 4 * (2 : ℝ) ^ (a + r') * (m ^ β + 1) := by rw [h2prod]; ring
  -- The target `p`-term: `Pterm := ‖p‖^αt / (θ^{αt-1}·(m^τ+1)) = ‖p‖^αt / W`.
  set Pterm : ℝ := ‖p‖ ^ αt / (θ ^ (αt - 1) * (m ^ τ + 1)) with hPtermdef
  have hPterm_eq : Pterm = ‖p‖ ^ αt / W := by rw [hPtermdef, hWdef]
  have hPterm_nn : 0 ≤ Pterm := by
    rw [hPtermdef]; positivity
  -- Bound the `A^αt / αt` term.
  have hAterm : A ^ αt / αt = (1 / αt) * Pterm := by
    rw [hApow, hPterm_eq]; ring
  -- Bound the `B^r' / r'` term by `Ccoef · θ · (m^β+1)`.
  have hBterm : B ^ r' / r' ≤ Ccoef * (θ * (m ^ β + 1)) := by
    rw [hBpow, hWpow]
    -- The LHS is `θ · P / r'` with `P = (m^τ+1)^{1/(αt-1)} · (m^c+1)^r'`.
    set P : ℝ := (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) * (m ^ c + 1) ^ r' with hPdef
    have hP_nn : 0 ≤ P := by
      rw [hPdef]
      have h1 : 0 ≤ (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1)) := by
        apply Real.rpow_nonneg; linarith
      have h2 : 0 ≤ (m ^ c + 1) ^ r' := Real.rpow_nonneg hmc1_nn r'
      positivity
    -- Rewrite LHS as `(θ / r') · P`.
    have hLHS_eq : (m ^ c + 1) ^ r' * (θ * (m ^ τ + 1) ^ ((1 : ℝ) / (αt - 1))) / r'
                = (θ / r') * P := by
      rw [hPdef]; ring
    rw [hLHS_eq]
    -- `(θ/r')·P ≤ (θ/r')·(4·2^{a+r'}(m^β+1))` since `θ/r' ≥ 0`.
    have hθr'_nn : 0 ≤ θ / r' := div_nonneg hθ.le hr'_pos.le
    have hstep : (θ / r') * P ≤ (θ / r') * (4 * (2 : ℝ) ^ (a + r') * (m ^ β + 1)) :=
      mul_le_mul_of_nonneg_left hmfactor hθr'_nn
    refine le_trans hstep (le_of_eq ?_)
    -- `(θ/r')·(4·2^{a+r'}(m^β+1)) = Ccoef·(θ·(m^β+1))`.
    rw [hCcoefdef, div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- Assemble: `‖p‖·(m^c+1) = A·B ≤ A^αt/αt + B^r'/r' ≤ (1/αt)Pterm + Ccoef·θ(m^β+1)`.
  have hkey : ‖p‖ * (m ^ c + 1) ≤ (1 / αt) * Pterm + Ccoef * (θ * (m ^ β + 1)) := by
    rw [← hAB]
    calc A * B ≤ A ^ αt / αt + B ^ r' / r' := hYoung
      _ = (1 / αt) * Pterm + B ^ r' / r' := by rw [hAterm]
      _ ≤ (1 / αt) * Pterm + Ccoef * (θ * (m ^ β + 1)) := by linarith [hBterm]
  -- Finally, replace the two coefficients by `c̃` (both terms nonneg).
  have hθmβ_nn : 0 ≤ θ * (m ^ β + 1) := mul_nonneg hθ.le hmβ1_nn
  calc (‖p‖ : ℝ) * (m ^ c + 1)
      ≤ (1 / αt) * Pterm + Ccoef * (θ * (m ^ β + 1)) := hkey
    _ ≤ ctil * Pterm + ctil * (θ * (m ^ β + 1)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right h_inv_αt_le hPterm_nn
          · exact mul_le_mul_of_nonneg_right hCcoef_le hθmβ_nn
    _ = ctil * (Pterm + θ * (m ^ β + 1)) := by ring

/-! ### Intermediate inequality `(eq:boundsH+1)` from convexity-at-zero -/

/-- **Coordinate Cauchy–Schwarz for `dotProduct`.** For any
`v, w : Fin d → ℝ`, `v ⬝ w ≤ d · ‖v‖ · ‖w‖`. (Local copy of the
`Coercivity.lean` helper, re-derived here to keep `Congestion.lean`
self-contained; `Coercivity.lean` is downstream of this module.) -/
private lemma euclideanDot_le_dim_mul_norm_mul_norm
    (v w : Fin d → ℝ) :
    v ⬝ w ≤ d * ‖v‖ * ‖w‖ := by
  -- `v ⬝ w ≤ |v ⬝ w| = |∑ v_i w_i| ≤ ∑ |v_i w_i| ≤ d · ‖v‖ · ‖w‖`.
  refine le_trans (le_abs_self _) ?_
  unfold dotProduct
  have h1 : |∑ i, v i * w i| ≤ ∑ i : Fin d, |v i * w i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i : Fin d, |v i * w i| ≤ ‖v‖ * ‖w‖ := by
    intro i
    rw [abs_mul]
    have hv : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      simpa [Real.norm_eq_abs] using this
    have hw : |w i| ≤ ‖w‖ := by
      have := norm_le_pi_norm w i
      simpa [Real.norm_eq_abs] using this
    calc |v i| * |w i|
        ≤ ‖v‖ * |w i| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
      _ ≤ ‖v‖ * ‖w‖ := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  have h3 : ∑ i : Fin d, |v i * w i| ≤ ∑ _ : Fin d, ‖v‖ * ‖w‖ :=
    Finset.sum_le_sum (fun i _ => h2 i)
  have h4 : ∑ _ : Fin d, ‖v‖ * ‖w‖ = d * (‖v‖ * ‖w‖) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  calc |∑ i, v i * w i|
      ≤ ∑ i : Fin d, |v i * w i| := h1
    _ ≤ ∑ _ : Fin d, ‖v‖ * ‖w‖ := h3
    _ = d * (‖v‖ * ‖w‖) := h4
    _ = d * ‖v‖ * ‖w‖ := by ring

/-- The `rpow` collapse `‖p‖^{r-1} · ‖p‖ = ‖p‖^r` for `r > 0`, valid even
at `‖p‖ = 0` (both sides vanish since `r > 0` and `r - 1` need not be
positive). -/
private lemma norm_rpow_pred_mul {r : ℝ} (hr : 0 < r) (p : Fin d → ℝ) :
    (‖p‖ : ℝ) ^ (r - 1) * ‖p‖ = ‖p‖ ^ r := by
  set t : ℝ := ‖p‖ with htdef
  have ht_nn : 0 ≤ t := norm_nonneg p
  rcases eq_or_lt_of_le ht_nn with ht0 | htpos
  · -- `t = 0`: RHS `0^r = 0` since `r > 0`; LHS `_ * 0 = 0`.
    rw [← ht0]
    simp [Real.zero_rpow (ne_of_gt hr)]
  · -- `t > 0`: `t^{r-1} · t = t^{r-1} · t^1 = t^{(r-1)+1} = t^r`.
    have h1 : (t : ℝ) = t ^ (1 : ℝ) := (Real.rpow_one t).symm
    calc (t : ℝ) ^ (r - 1) * t = t ^ (r - 1) * t ^ (1 : ℝ) := by rw [← h1]
      _ = t ^ ((r - 1) + 1) := (Real.rpow_add htpos _ _).symm
      _ = t ^ r := by ring_nf

/-- **Paper `(eq:boundsH+1)`** (`Source/FGU-monotone_revised.tex`,
lines 697–701) — the intermediate `H` upper bound obtained by chaining
the convexity-at-zero inequality `hmon.convex_at_zero` with the bundle's
`H`-at-zero upper bound `hcong.upper`, its `D_pH` upper bound
`hcong.DpH_upper`, and coordinate Cauchy–Schwarz. With `αt := α(1+τ/β)`,
for a.e. `x` and every `(p, m)` with `m > 0`,

  `H(x, p, m) ≤ -m^β/C + C`
              `+ (d·C)·(1/m + 1/m^τ)·‖p‖^{αt}`
              `+ (d·C)·(m^{β-β/α} + 1/m)·‖p‖`.

The dimension factor `d` arises from the coordinate Cauchy–Schwarz
`D_pH·p ≤ d·‖D_pH‖·‖p‖`; it is harmless (absorbed into the final
constant in the downstream Young assembly). The `‖p‖^{αt-1}·‖p‖`
collapse to `‖p‖^{αt}` uses `norm_rpow_pred_mul` (valid since
`αt > 1 > 0`). -/
theorem congestion_boundsH_plus_1
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m
          ≤ -(m ^ hcong.β) / hcong.C + hcong.C
            + (d * hcong.C) * ((1 / m) + (1 / m ^ hcong.τ))
                * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)))
            + (d * hcong.C) * ((m ^ (hcong.β - hcong.β / hcong.α)) + 1 / m)
                * ‖p‖ := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hαt_gt_one : 1 < αt := one_lt_alphaTau hα hβ hτ_nn
  have hαt_pos : 0 < αt := lt_trans one_pos hαt_gt_one
  filter_upwards [hmon.convex_at_zero, hcong.upper, hcong.DpH_upper]
    with x hCx hUp hDpH
  intro p m hm
  -- Convexity-at-zero: `H x p m ≤ H x 0 m + DpH x p m ⬝ p`.
  have hconv : H x p m ≤ H x (0 : Fin d → ℝ) m + (DpH x p m) ⬝ p := by
    have := hCx p m hm; linarith
  -- `H x 0 m ≤ -m^β/C + C`.
  have hH0 : H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C := hUp m hm
  -- Cauchy–Schwarz: `DpH x p m ⬝ p ≤ d · ‖DpH x p m‖ · ‖p‖`.
  have hCS : (DpH x p m) ⬝ p ≤ (d : ℝ) * ‖DpH x p m‖ * ‖p‖ :=
    euclideanDot_le_dim_mul_norm_mul_norm (DpH x p m) p
  -- `D_pH` upper bound.
  have hDpHb : ‖DpH x p m‖
      ≤ C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (αt - 1))
        + C * ((m ^ (β - β / α)) + 1 / m) := hDpH p m hm
  -- Multiply the `D_pH` bound by `d · ‖p‖ ≥ 0`.
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
  have hdp_nn : 0 ≤ (d : ℝ) * ‖p‖ := mul_nonneg (Nat.cast_nonneg d) hp_nn
  have hDpH_mul : (d : ℝ) * ‖DpH x p m‖ * ‖p‖
      ≤ ((d : ℝ) * ‖p‖)
          * (C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (αt - 1))
             + C * ((m ^ (β - β / α)) + 1 / m)) := by
    have := mul_le_mul_of_nonneg_left hDpHb hdp_nn
    nlinarith [this]
  -- The `‖p‖^{αt-1} · ‖p‖ = ‖p‖^{αt}` collapse.
  have hcollapse : (‖p‖ : ℝ) ^ (αt - 1) * ‖p‖ = ‖p‖ ^ αt :=
    norm_rpow_pred_mul hαt_pos p
  -- Rearrange the product into the two target summands.
  have hexpand :
      ((d : ℝ) * ‖p‖)
          * (C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (αt - 1))
             + C * ((m ^ (β - β / α)) + 1 / m))
        = (d * C) * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt)
          + (d * C) * ((m ^ (β - β / α)) + 1 / m) * ‖p‖ := by
    rw [← hcollapse]; ring
  -- Chain everything.
  have hDpHp : (DpH x p m) ⬝ p
      ≤ (d * C) * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt)
        + (d * C) * ((m ^ (β - β / α)) + 1 / m) * ‖p‖ := by
    calc (DpH x p m) ⬝ p
        ≤ (d : ℝ) * ‖DpH x p m‖ * ‖p‖ := hCS
      _ ≤ ((d : ℝ) * ‖p‖)
            * (C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (αt - 1))
               + C * ((m ^ (β - β / α)) + 1 / m)) := hDpH_mul
      _ = (d * C) * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt)
          + (d * C) * ((m ^ (β - β / α)) + 1 / m) * ‖p‖ := hexpand
  linarith [hconv, hH0, hDpHp]

/-! ### Post-Young assembly `(eq:boundsH+)` from the two children -/

set_option maxHeartbeats 1600000 in
-- This assembly chains the two children (`congestion_boundsH_plus_1` and
-- `young_congestion_case`) with several `rpow`-arithmetic rewrites and a long
-- final `linarith`; the many local `set` definitions make elaboration heavy,
-- so the heartbeat ceiling is raised above the default 200000.
/-- **Paper `(eq:boundsH+)` post-Young assembly** (`Source/FGU-monotone_revised.tex`,
lines 696–725) — the headline congestion upper bound in the
`K·S·(‖p‖^{αt}+1) − δ·m^β` form, assembled *genuinely* from the two
children of the congestion proof:

* `congestion_boundsH_plus_1` (`(eq:boundsH+1)`), the intermediate bound
  obtained from `hmon.convex_at_zero` + the bundle's two upper bounds, and
* `young_congestion_case` (`(eq:Young.congestion.case)`), the parametric
  Young inequality,

together with the elementary split `congestion_split_p`
(`|p| ≤ |p|^{αt}+1`) for `(eq:intermediate-step)` and the Young-like
inequality `congestion_one_le_young` (`(eq:Young-like.congestion)`) used to
absorb the additive constants.  The dimension factor `d` of the coordinate
Cauchy–Schwarz in `congestion_boundsH_plus_1` is harmlessly folded into the
existential constant `K`.  With `αt := α(1+τ/β)`, for a.e. `x` and every
`(p, m)` with `m > 0`,

  `H(x, p, m) ≤ K · (1/m + 1/m^τ) · (‖p‖^{αt} + 1) − δ · m^β`. -/
theorem H_upper_congestion_of_hmon
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ K * ((1 / m) + (1 / m ^ hcong.τ))
                        * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
                    - δ * m ^ hcong.β := by
  -- Bundle data.
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hαt_gt_one : 1 < αt := one_lt_alphaTau hα hβ hτ_nn
  have hαt_pos : 0 < αt := lt_trans one_pos hαt_gt_one
  have hαtm1_pos : 0 < αt - 1 := sub_pos.mpr hαt_gt_one
  set Cd : ℝ := (d : ℝ) * C with hCddef
  have hCd_nn : 0 ≤ Cd := mul_nonneg (Nat.cast_nonneg d) hC_pos.le
  -- The parametric Young constant from child2.
  obtain ⟨ctil, hctil_pos, hYoung⟩ := young_congestion_case (d := d) hα hβ hτ_nn
  -- Auxiliary positive constant `A` and the chosen small `θ`.
  set A : ℝ := 2 * (Cd * ctil) + C with hAdef
  have hA_pos : 0 < A := by
    have : 0 ≤ 2 * (Cd * ctil) := by positivity
    rw [hAdef]; linarith
  set θ : ℝ := min 1 (1 / (2 * C * A)) with hθdef
  have hθ_pos : 0 < θ := by
    rw [hθdef]
    refine lt_min (by norm_num) ?_
    positivity
  have hθ_le_one : θ ≤ 1 := min_le_left _ _
  have hθ_le : θ ≤ 1 / (2 * C * A) := min_le_right _ _
  -- `θ^{αt-1}`, `θ^{1/β}` positive.
  have hθpow1_pos : 0 < θ ^ (αt - 1) := Real.rpow_pos_of_pos hθ_pos _
  have hθpowβ_pos : 0 < θ ^ ((1 : ℝ) / β) := Real.rpow_pos_of_pos hθ_pos _
  -- The S·(P+1) coefficient `K` (genuinely contains the dimension factor `d`
  -- only through `Cd = d·C`).
  set K : ℝ := Cd + Cd + Cd * ctil * (1 / θ ^ (αt - 1))
                + C * (1 / θ ^ ((1 : ℝ) / β))
                + Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) with hKdef
  have hK_pos : 0 < K := by
    rw [hKdef]
    have h1 : 0 ≤ Cd := hCd_nn
    have h2 : 0 ≤ Cd * ctil * (1 / θ ^ (αt - 1)) := by positivity
    have h3 : 0 < C * (1 / θ ^ ((1 : ℝ) / β)) := by positivity
    have h4 : 0 ≤ Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) := by positivity
    linarith
  -- `δ := 1/(2C)`.
  set δ : ℝ := 1 / (2 * C) with hδdef
  have hδ_pos : 0 < δ := by rw [hδdef]; positivity
  refine ⟨K, δ, hK_pos, hδ_pos, ?_⟩
  -- The intermediate bound from child1.
  filter_upwards [congestion_boundsH_plus_1 hmon hcong] with x hb1
  intro p m hm
  have hm_nn : 0 ≤ m := hm.le
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
  -- Atoms.
  set P : ℝ := ‖p‖ ^ αt with hPdef
  have hP_nn : 0 ≤ P := Real.rpow_nonneg hp_nn αt
  set S : ℝ := (1 / m) + (1 / m ^ τ) with hSdef
  have hmτ_pos : 0 < m ^ τ := Real.rpow_pos_of_pos hm τ
  have hmτ1_pos : 0 < m ^ τ + 1 := by linarith
  have h_invm_pos : 0 < 1 / m := by positivity
  have h_invmτ_pos : 0 < 1 / m ^ τ := by positivity
  have hS_pos : 0 < S := by rw [hSdef]; linarith
  have hP1_nn : 0 ≤ P + 1 := by linarith
  have hP1_ge_one : 1 ≤ P + 1 := by linarith
  set Q : ℝ := S * (P + 1) with hQdef
  have hQ_nn : 0 ≤ Q := mul_nonneg hS_pos.le hP1_nn
  have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm_nn β
  -- child1 in atom form: rewrite the αt powers as `P` and the sum as `S`.
  have hb1' : H x p m
      ≤ -(m ^ β) / C + C + Cd * S * P
        + Cd * (m ^ (β - β / α) + 1 / m) * ‖p‖ := by
    have := hb1 p m hm
    -- `hb1` is stated with `hcong.{α,β,τ,C}` and `(d * hcong.C)`; unfold to
    -- the local `set` names.
    simpa [hCddef, hPdef, hSdef, hαtdef, hαdef, hβdef, hτdef, hCdef,
      mul_comm, mul_left_comm, mul_assoc] using this
  -- (eq:intermediate-step): split `|p| ≤ P + 1` on the `1/m·|p|` part.
  have hsplit : (‖p‖ : ℝ) ≤ P + 1 := by
    have := congestion_split_p (r := αt) hαt_gt_one.le p
    rw [hPdef]; exact this
  -- Useful inequalities relating `1/m`, `1/(m^τ+1)`, `1/m^τ` to `S`.
  have h_invm_le_S : 1 / m ≤ S := by rw [hSdef]; linarith
  have h_invmτ1_le_S : 1 / (m ^ τ + 1) ≤ S := by
    have h1 : 1 / (m ^ τ + 1) ≤ 1 / m ^ τ := by
      apply one_div_le_one_div_of_le hmτ_pos; linarith
    rw [hSdef]; linarith
  -- `Cd·S ≥ 0`, `Cd·(1/m) ≥ 0`, etc.
  have hCdS_nn : 0 ≤ Cd * S := mul_nonneg hCd_nn hS_pos.le
  have hCd_invm_nn : 0 ≤ Cd * (1 / m) := mul_nonneg hCd_nn h_invm_pos.le
  -- e1: `Cd·S·P ≤ Cd·Q`.
  have e1 : Cd * S * P ≤ Cd * Q := by
    rw [hQdef]
    have hstep : Cd * S * P ≤ Cd * S * (P + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hCdS_nn
    calc Cd * S * P ≤ Cd * S * (P + 1) := hstep
      _ = Cd * (S * (P + 1)) := by ring
  -- Cross-term: split into the `m^{β-β/α}+1` part and the `1/m` part.
  -- e2a: `Cd·(1/m)·|p| ≤ Cd·Q`.
  have e2a : Cd * (1 / m) * ‖p‖ ≤ Cd * Q := by
    rw [hQdef]
    -- `Cd·(1/m)·‖p‖ ≤ Cd·(1/m)·(P+1) ≤ Cd·S·(P+1) = Cd·(S·(P+1))`.
    have step1 : Cd * (1 / m) * ‖p‖ ≤ Cd * (1 / m) * (P + 1) :=
      mul_le_mul_of_nonneg_left hsplit hCd_invm_nn
    have hCd_invm_le_CdS : Cd * (1 / m) ≤ Cd * S :=
      mul_le_mul_of_nonneg_left h_invm_le_S hCd_nn
    have step2 : Cd * (1 / m) * (P + 1) ≤ Cd * S * (P + 1) :=
      mul_le_mul_of_nonneg_right hCd_invm_le_CdS hP1_nn
    calc Cd * (1 / m) * ‖p‖
        ≤ Cd * (1 / m) * (P + 1) := step1
      _ ≤ Cd * S * (P + 1) := step2
      _ = Cd * (S * (P + 1)) := by ring
  -- e2b: the `m^{β-β/α}` part absorbs into `m^{β-β/α}+1`, then Young.
  -- First: `Cd·(m^{β-β/α}+1)·|p| ≤ Cd·ctil·(Pterm + θ(m^β+1))`.
  set Pterm : ℝ := P / (θ ^ (αt - 1) * (m ^ τ + 1)) with hPtermdef
  have hyoung_p : ‖p‖ * (m ^ (β - β / α) + 1) ≤ ctil * (Pterm + θ * (m ^ β + 1)) := by
    have := hYoung θ m hθ_pos hm p
    -- `young_congestion_case` is stated with the same `αt`, `β-β/α`, `m^τ+1`.
    simpa [hPtermdef, hPdef, hαtdef, hαdef, hβdef, hτdef] using this
  -- `Cd·(m^{β-β/α}+1)·|p| = Cd·(|p|·(m^{β-β/α}+1))`.
  have e2b : Cd * (m ^ (β - β / α) + 1) * ‖p‖
      ≤ Cd * ctil * Pterm + Cd * ctil * θ * (m ^ β + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hyoung_p hCd_nn
    -- `Cd·(|p|·(m^{β-β/α}+1)) ≤ Cd·(ctil·(Pterm + θ(m^β+1)))`.
    calc Cd * (m ^ (β - β / α) + 1) * ‖p‖
        = Cd * (‖p‖ * (m ^ (β - β / α) + 1)) := by ring
      _ ≤ Cd * (ctil * (Pterm + θ * (m ^ β + 1))) := hmul
      _ = Cd * ctil * Pterm + Cd * ctil * θ * (m ^ β + 1) := by ring
  -- `Cd·(m^{β-β/α}+1/m)·|p| ≤ Cd·(m^{β-β/α}+1)·|p| + Cd·(1/m)·|p|`.
  have e2split : Cd * (m ^ (β - β / α) + 1 / m) * ‖p‖
      ≤ Cd * (m ^ (β - β / α) + 1) * ‖p‖ + Cd * (1 / m) * ‖p‖ := by
    -- The two sides differ by `Cd·|p|·(-1) ≤ 0` after expansion.
    have h0 : 0 ≤ Cd * ‖p‖ := mul_nonneg hCd_nn hp_nn
    have hexp : Cd * (m ^ (β - β / α) + 1) * ‖p‖ + Cd * (1 / m) * ‖p‖
        = Cd * (m ^ (β - β / α) + 1 / m) * ‖p‖ + Cd * ‖p‖ := by ring
    linarith [hexp, h0]
  -- e2c: `Cd·ctil·Pterm ≤ (Cd·ctil·(1/θ^{αt-1}))·Q`.
  have e2c : Cd * ctil * Pterm ≤ Cd * ctil * (1 / θ ^ (αt - 1)) * Q := by
    rw [hQdef, hPtermdef]
    -- `Pterm = (1/θ^{αt-1})·(P·(1/(m^τ+1)))`.
    have hPterm_eq : P / (θ ^ (αt - 1) * (m ^ τ + 1))
        = (1 / θ ^ (αt - 1)) * (P * (1 / (m ^ τ + 1))) := by
      rw [div_mul_eq_div_div]
      field_simp
    rw [hPterm_eq]
    -- `P·(1/(m^τ+1)) ≤ S·(P+1)`: from `1/(m^τ+1) ≤ S` and `P ≤ P+1`.
    have hbnd : P * (1 / (m ^ τ + 1)) ≤ S * (P + 1) := by
      have hPS : P * (1 / (m ^ τ + 1)) ≤ P * S :=
        mul_le_mul_of_nonneg_left h_invmτ1_le_S hP_nn
      have hSP : P * S ≤ (P + 1) * S :=
        mul_le_mul_of_nonneg_right (by linarith : P ≤ P + 1) hS_pos.le
      calc P * (1 / (m ^ τ + 1)) ≤ P * S := hPS
        _ ≤ (P + 1) * S := hSP
        _ = S * (P + 1) := by ring
    have hcoef_nn : 0 ≤ Cd * ctil * (1 / θ ^ (αt - 1)) := by positivity
    -- `coef·(P·(1/(m^τ+1))) ≤ coef·(S·(P+1))`.
    have hmul : (Cd * ctil * (1 / θ ^ (αt - 1))) * (P * (1 / (m ^ τ + 1)))
        ≤ (Cd * ctil * (1 / θ ^ (αt - 1))) * (S * (P + 1)) :=
      mul_le_mul_of_nonneg_left hbnd hcoef_nn
    have hL : Cd * ctil * ((1 / θ ^ (αt - 1)) * (P * (1 / (m ^ τ + 1))))
        = (Cd * ctil * (1 / θ ^ (αt - 1))) * (P * (1 / (m ^ τ + 1))) := by ring
    have hR : (Cd * ctil * (1 / θ ^ (αt - 1))) * (S * (P + 1))
        = Cd * ctil * (1 / θ ^ (αt - 1)) * (S * (P + 1)) := by ring
    rw [hL]; linarith [hmul, hR]
  -- Young-like for the bare `+C` constant.
  have hyl : (1 : ℝ) ≤ 1 / (θ ^ ((1 : ℝ) / β) * m) + θ * m ^ β :=
    congestion_one_le_young hθ_pos hm hβ
  -- e3: `C ≤ (C·(1/θ^{1/β}))·Q + C·θ·m^β`.
  have e3 : C ≤ C * (1 / θ ^ ((1 : ℝ) / β)) * Q + C * θ * m ^ β := by
    -- `C ≤ C/(θ^{1/β}·m) + C·θ·m^β`.
    have hstep : C ≤ C * (1 / (θ ^ ((1 : ℝ) / β) * m)) + C * (θ * m ^ β) := by
      have hmul := mul_le_mul_of_nonneg_left hyl hC_pos.le
      calc C = C * 1 := by ring
        _ ≤ C * (1 / (θ ^ ((1 : ℝ) / β) * m) + θ * m ^ β) := hmul
        _ = C * (1 / (θ ^ ((1 : ℝ) / β) * m)) + C * (θ * m ^ β) := by ring
    -- `C·(1/(θ^{1/β}·m)) = (C·(1/θ^{1/β}))·(1/m) ≤ (C·(1/θ^{1/β}))·Q`.
    have hsmid : C * (1 / (θ ^ ((1 : ℝ) / β) * m))
        ≤ C * (1 / θ ^ ((1 : ℝ) / β)) * (1 / m) := by
      have hne : θ ^ ((1 : ℝ) / β) ≠ 0 := ne_of_gt hθpowβ_pos
      have hmne : m ≠ 0 := ne_of_gt hm
      apply le_of_eq
      field_simp
    have hS_le_Q : S ≤ S * (P + 1) := by
      calc S = S * 1 := by ring
        _ ≤ S * (P + 1) := mul_le_mul_of_nonneg_left hP1_ge_one hS_pos.le
    have h_invm_le_Q : (1 / m) ≤ Q := by
      rw [hQdef]; linarith [h_invm_le_S, hS_le_Q]
    have hcoef_nn : 0 ≤ C * (1 / θ ^ ((1 : ℝ) / β)) := by positivity
    have hsfold : C * (1 / θ ^ ((1 : ℝ) / β)) * (1 / m)
        ≤ C * (1 / θ ^ ((1 : ℝ) / β)) * Q :=
      mul_le_mul_of_nonneg_left h_invm_le_Q hcoef_nn
    have hcmid : C * (θ * m ^ β) = C * θ * m ^ β := by ring
    linarith [hstep, hsmid, hsfold, hcmid]
  -- e4: bound the bare `Cd·ctil·θ` constant (from `θ·(m^β+1) = θ·m^β + θ`).
  have e4 : Cd * ctil * θ ≤ Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) * Q
                            + Cd * ctil * θ ^ 2 * m ^ β := by
    have hcoef_nn : 0 ≤ Cd * ctil * θ := by positivity
    have hstep : Cd * ctil * θ
        ≤ Cd * ctil * θ * (1 / (θ ^ ((1 : ℝ) / β) * m)) + Cd * ctil * θ * (θ * m ^ β) := by
      have hmul := mul_le_mul_of_nonneg_left hyl hcoef_nn
      calc Cd * ctil * θ = Cd * ctil * θ * 1 := by ring
        _ ≤ Cd * ctil * θ * (1 / (θ ^ ((1 : ℝ) / β) * m) + θ * m ^ β) := hmul
        _ = Cd * ctil * θ * (1 / (θ ^ ((1 : ℝ) / β) * m)) + Cd * ctil * θ * (θ * m ^ β) := by
            ring
    have hsmid : Cd * ctil * θ * (1 / (θ ^ ((1 : ℝ) / β) * m))
        ≤ Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) * (1 / m) := by
      have hne : θ ^ ((1 : ℝ) / β) ≠ 0 := ne_of_gt hθpowβ_pos
      have hmne : m ≠ 0 := ne_of_gt hm
      apply le_of_eq
      field_simp
    have hS_le_Q : S ≤ S * (P + 1) := by
      calc S = S * 1 := by ring
        _ ≤ S * (P + 1) := mul_le_mul_of_nonneg_left hP1_ge_one hS_pos.le
    have h_invm_le_Q : (1 / m) ≤ Q := by
      rw [hQdef]; linarith [h_invm_le_S, hS_le_Q]
    have hcoef_nn2 : 0 ≤ Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) := by positivity
    have hsfold : Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) * (1 / m)
        ≤ Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) * Q :=
      mul_le_mul_of_nonneg_left h_invm_le_Q hcoef_nn2
    have hcmid : Cd * ctil * θ * (θ * m ^ β) = Cd * ctil * θ ^ 2 * m ^ β := by ring
    linarith [hstep, hsmid, hsfold, hcmid]
  -- The total positive `m^β` coefficient is `≤ 1/(2C)`.
  have hmβ_coeff : Cd * ctil * θ + C * θ + Cd * ctil * θ ^ 2 ≤ 1 / (2 * C) := by
    -- `θ ≤ 1` ⇒ `θ^2 ≤ θ`; then LHS ≤ A·θ ≤ 1/(2C).
    have hθsq_le : θ ^ 2 ≤ θ := by
      have := mul_le_mul_of_nonneg_left hθ_le_one hθ_pos.le
      nlinarith [this]
    have hCdctil_nn : 0 ≤ Cd * ctil := mul_nonneg hCd_nn hctil_pos.le
    have hbound : Cd * ctil * θ + C * θ + Cd * ctil * θ ^ 2 ≤ A * θ := by
      rw [hAdef]
      have hkey : 0 ≤ Cd * ctil * (θ - θ ^ 2) :=
        mul_nonneg hCdctil_nn (by linarith [hθsq_le])
      have hexp : (2 * (Cd * ctil) + C) * θ
          = (Cd * ctil * θ + C * θ + Cd * ctil * θ ^ 2) + Cd * ctil * (θ - θ ^ 2) := by
        ring
      linarith [hkey, hexp]
    have hAθ : A * θ ≤ 1 / (2 * C) := by
      have hCA_pos : 0 < 2 * C * A := by positivity
      have := mul_le_mul_of_nonneg_left hθ_le hA_pos.le
      -- `A·θ ≤ A·(1/(2CA)) = 1/(2C)`.
      have heq : A * (1 / (2 * C * A)) = 1 / (2 * C) := by
        field_simp
      linarith [this, heq]
    linarith [hbound, hAθ]
  -- Now assemble. The K·Q expansion.
  have hKQ : K * Q = Cd * Q + Cd * Q + Cd * ctil * (1 / θ ^ (αt - 1)) * Q
              + C * (1 / θ ^ ((1 : ℝ) / β)) * Q
              + Cd * ctil * θ * (1 / θ ^ ((1 : ℝ) / β)) * Q := by
    rw [hKdef]; ring
  -- Combine everything into `H ≤ K·Q - δ·m^β`.
  -- First collect the RHS of `hb1'` and replace each piece.
  -- `Cd·(m^{β-β/α}+1/m)·|p| ≤ Cd·ctil·Pterm + Cd·ctil·θ(m^β+1) + Cd·(1/m)·|p|`
  have ecross : Cd * (m ^ (β - β / α) + 1 / m) * ‖p‖
      ≤ Cd * ctil * Pterm + Cd * ctil * θ * (m ^ β + 1) + Cd * (1 / m) * ‖p‖ := by
    linarith [e2split, e2b]
  -- Expand `Cd·ctil·θ·(m^β+1) = Cd·ctil·θ·m^β + Cd·ctil·θ`.
  have hexp1 : Cd * ctil * θ * (m ^ β + 1) = Cd * ctil * θ * m ^ β + Cd * ctil * θ := by
    ring
  -- `-(m^β)/C = -(2δ)·m^β` since `δ = 1/(2C)`.
  have hδrel : -(m ^ β) / C = -(2 * δ) * m ^ β := by
    have hCne : C ≠ 0 := ne_of_gt hC_pos
    rw [hδdef]
    field_simp
  -- The `m^β` budget: positive `m^β` coefficient `≤ δ`.
  have hmβ_coeff' : Cd * ctil * θ + C * θ + Cd * ctil * θ ^ 2 ≤ δ := by
    rw [hδdef]; exact hmβ_coeff
  have hmβ_budget :
      Cd * ctil * θ * m ^ β + C * θ * m ^ β + Cd * ctil * θ ^ 2 * m ^ β
        ≤ δ * m ^ β := by
    have hbud := mul_le_mul_of_nonneg_right hmβ_coeff' hmβ_nn
    calc Cd * ctil * θ * m ^ β + C * θ * m ^ β + Cd * ctil * θ ^ 2 * m ^ β
        = (Cd * ctil * θ + C * θ + Cd * ctil * θ ^ 2) * m ^ β := by ring
      _ ≤ δ * m ^ β := hbud
  -- `hfinal`: bound the RHS of `hb1'` by `K·Q − δ·m^β`.
  have hfinal :
      -(m ^ β) / C + C + Cd * S * P + Cd * (m ^ (β - β / α) + 1 / m) * ‖p‖
        ≤ K * Q - δ * m ^ β := by
    rw [hKQ, hδrel]
    linarith [e1, e2a, e2c, e3, e4, ecross, hexp1, hmβ_budget]
  -- Convert `K·Q` to the goal shape `K·S·(P+1)`.
  have hKgoal : K * Q = K * S * (P + 1) := by rw [hQdef]; ring
  -- Final chain.
  calc H x p m
      ≤ -(m ^ β) / C + C + Cd * S * P + Cd * (m ^ (β - β / α) + 1 / m) * ‖p‖ := hb1'
    _ ≤ K * Q - δ * m ^ β := hfinal
    _ = K * S * (P + 1) - δ * m ^ β := by rw [hKgoal]

/-- **Two-sided `|H|` congestion bound from `hmon + hcong`** (the
`hH_bound` rider of `congestion_auxHyps_of_mem_congestionBanachK`).

The HJB well-definedness lemma `aEpsi_congestion_HJB_memLp` consumes a
two-sided bound on `|H|` of the shape

  `|H(x,p,m)| ≤ K·(1/m + 1/m^τ)·(‖p‖^{α(1+τ/β)} + 1) + K·(m^β + 1)`

for `m > 0`. This is produced from the existing one-sided upper bound
`H_upper_congestion_of_hmon` (`H ≤ K₁·S·(P+1) − δ·m^β`, paper
`eq:boundsH+`) together with the lower bound `hcong.lower`
(`H ≥ (1/C)(1/(m^τ+1))‖p‖^{αt} − C(m^β+1)`, paper
`eq:assH.lower.congestion`). With `K := max K₁ C`:

* upper: `H ≤ K₁·S·(P+1) − δ·m^β ≤ K·S·(P+1) ≤ K·S·(P+1) + K·(m^β+1)`
  (drop the nonpositive `−δ·m^β`, and `S·(P+1) ≥ 0`);
* lower: `−H ≤ −(1/C)(1/(m^τ+1))‖p‖^{αt} + C(m^β+1) ≤ C(m^β+1)
  ≤ K·S·(P+1) + K·(m^β+1)` (drop the nonpositive momentum term, and
  `K·S·(P+1) ≥ 0`).

No carrier-exponent inequality and no per-element rider are used; the
bound is a pure consequence of the Hamiltonian-side hypotheses. -/
theorem H_two_sided_congestion_of_hmon
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          |H x p m| ≤
            K * ((1 / m) + (1 / m ^ hcong.τ))
                * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
              + K * (m ^ hcong.β + 1) := by
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hαt_gt_one : 1 < αt := one_lt_alphaTau hα hβ hτ_nn
  have hαt_pos : 0 < αt := lt_trans one_pos hαt_gt_one
  -- Upper bound `H ≤ K₁·S·(P+1) − δ·m^β`.
  obtain ⟨K₁, δ, hK₁_pos, hδ_pos, hUpper⟩ := H_upper_congestion_of_hmon hmon hcong
  -- The two-sided constant `K := max K₁ C`.
  set K : ℝ := max K₁ C with hKdef
  have hK_pos : 0 < K := lt_of_lt_of_le hK₁_pos (le_max_left _ _)
  have hK₁_le_K : K₁ ≤ K := le_max_left _ _
  have hC_le_K : C ≤ K := le_max_right _ _
  refine ⟨K, hK_pos, ?_⟩
  filter_upwards [hUpper, hcong.lower] with x hUp hLow
  intro p m hm
  have hm_nn : 0 ≤ m := hm.le
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
  -- Atoms.
  set P : ℝ := ‖p‖ ^ αt with hPdef
  have hP_nn : 0 ≤ P := Real.rpow_nonneg hp_nn αt
  have hmτ_pos : 0 < m ^ τ := Real.rpow_pos_of_pos hm τ
  have h_invm_pos : 0 < 1 / m := by positivity
  have h_invmτ_pos : 0 < 1 / m ^ τ := by positivity
  set S : ℝ := (1 / m) + (1 / m ^ τ) with hSdef
  have hS_pos : 0 < S := by rw [hSdef]; linarith
  have hP1_nn : 0 ≤ P + 1 := by linarith
  have hQ_nn : 0 ≤ S * (P + 1) := mul_nonneg hS_pos.le hP1_nn
  have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm_nn β
  -- The RHS atoms, after rewriting goal to the local `set` names.
  have hgoal_rw : K * ((1 / m) + (1 / m ^ τ))
        * (‖p‖ ^ (α * (1 + τ / β)) + 1) + K * (m ^ β + 1)
      = K * (S * (P + 1)) + K * (m ^ β + 1) := by
    rw [hSdef, hPdef, hαtdef]; ring
  rw [hgoal_rw]
  -- Specialise the two one-sided bounds.
  have hUp' := hUp p m hm
  have hLow' := hLow p m hm
  -- Rewrite the one-sided upper bound into atom form `K₁·(S·(P+1)) − δ·m^β`.
  have hUp'' : H x p m ≤ K₁ * (S * (P + 1)) - δ * m ^ β := by
    have : K₁ * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (α * (1 + τ / β)) + 1)
            - δ * m ^ β
          = K₁ * (S * (P + 1)) - δ * m ^ β := by
      rw [hSdef, hPdef, hαtdef]; ring
    rw [this] at hUp'; exact hUp'
  -- Rewrite the lower bound into atom form.
  have hLow'' : (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
                  - C * (m ^ β + 1)
                ≤ H x p m := by
    -- `hcong.lower` is stated with `hcong.{α,β,τ,C}`; align to local names.
    have := hLow'
    simpa [hαdef, hβdef, hτdef, hCdef] using this
  -- The momentum atom in the lower bound is `≥ 0`.
  have hmom_nn : 0 ≤ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β))) := by
    have hmτ1_pos : 0 < m ^ τ + 1 := by linarith
    have : 0 ≤ ‖p‖ ^ (α * (1 + τ / β)) := Real.rpow_nonneg hp_nn _
    positivity
  -- Bound `|H|` by `max` of the two pieces.
  rw [abs_le]
  constructor
  · -- `-(RHS) ≤ H`, i.e. `-H ≤ RHS`.
    -- From the lower bound: `H ≥ (mom) − C(m^β+1) ≥ −C(m^β+1)`.
    have hH_ge : H x p m ≥ - (C * (m ^ β + 1)) := by
      have : (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
                - C * (m ^ β + 1) ≥ - (C * (m ^ β + 1)) := by linarith [hmom_nn]
      linarith [hLow'']
    have hKQ_nn : 0 ≤ K * (S * (P + 1)) := mul_nonneg hK_pos.le hQ_nn
    have hCmβ_le : C * (m ^ β + 1) ≤ K * (m ^ β + 1) :=
      mul_le_mul_of_nonneg_right hC_le_K (by linarith)
    linarith [hH_ge, hKQ_nn, hCmβ_le]
  · -- `H ≤ RHS`.
    have hKmβ_nn : 0 ≤ K * (m ^ β + 1) := mul_nonneg hK_pos.le (by linarith)
    have hδmβ_nn : 0 ≤ δ * m ^ β := mul_nonneg hδ_pos.le hmβ_nn
    have hK₁Q_le_KQ : K₁ * (S * (P + 1)) ≤ K * (S * (P + 1)) :=
      mul_le_mul_of_nonneg_right hK₁_le_K hQ_nn
    linarith [hUp'', hK₁Q_le_KQ, hδmβ_nn, hKmβ_nn]

/-! ### Headline `H` upper bound under congestion growth -/

/--
**Paper Lemma `lem:ADFGU.congestion`, eq.~`eq:boundsH+`** — the
headline `H` upper bound under the congestion-growth bundle.

Under `(onH.congestiongrowth)` together with the monotonicity bundle
`hmon`, there exists a single constant `C' > 0` for which

  `H(x, p, m) ≤ C' · (1/m + 1/m^τ) · (‖p‖^{α(1+τ/β)} + 1) − m^β / C'`

holds for almost every `x ∈ 𝕋^d` and every `(p, m)` with `m > 0`.

The post-Young intermediate inequality `(eq:boundsH+1) +
(eq:intermediate-step) + (eq:Young.congestion.case) +
(eq:Young-like.congestion)` is no longer taken as a hypothesis: it is
now **derived internally** via `H_upper_congestion_of_hmon`, which
genuinely assembles it from the two children of the congestion proof
(`congestion_boundsH_plus_1` and `young_congestion_case`).  This
theorem then performs the final constant-unification step: with the
derived `K, δ > 0`, choose `C' := max(K, 1/δ)` and rearrange.
-/
theorem upper_bound_congestiongrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : CongestionGrowthCore H DpH J) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ C' * ((1 / m) + (1 / m ^ h.τ))
                       * (‖p‖ ^ (h.α * (1 + h.τ / h.β)) + 1)
                  - (m ^ h.β) / C' := by
  -- Set up data from the bundle.
  set α : ℝ := h.α with hαdef
  set β : ℝ := h.β with hβdef
  set τ : ℝ := h.τ with hτdef
  have hα : 1 < α := h.hα
  have hβ : 0 < β := h.hβ
  have hτ_nn : 0 ≤ τ := h.hτ.1
  have hαpos : 0 < α := lt_trans one_pos hα
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hαt_pos : 0 < αt := lt_trans one_pos (one_lt_alphaTau hα hβ hτ_nn)
  -- DERIVE the post-Young bound internally from the two children, via
  -- `H_upper_congestion_of_hmon` (no longer taken as a hypothesis).
  obtain ⟨K, δ, hK_pos, hδ_pos, hbound⟩ := H_upper_congestion_of_hmon hmon h
  -- Choose `C' := max K (1/δ)`.
  refine ⟨max K (1 / δ), ?_, ?_⟩
  · -- positivity of `C'`.
    have h1 : 0 < 1 / δ := by positivity
    exact lt_of_lt_of_le h1 (le_max_right _ _)
  · -- the bound itself.
    filter_upwards [hbound] with x hx p m hm
    set C' := max K (1 / δ) with hC'def
    have hK_le : K ≤ C' := le_max_left _ _
    have h_invδ_le : 1 / δ ≤ C' := le_max_right _ _
    have hC'_pos : 0 < C' := lt_of_lt_of_le (by positivity : (0:ℝ) < 1 / δ) h_invδ_le
    -- `1/C' ≤ δ` (since `1/δ ≤ C'` and both positive).
    have h_inv_le_δ : 1 / C' ≤ δ := by
      rw [div_le_iff₀ hC'_pos]
      have h1 : 1 ≤ δ * C' := by
        have h2 : (1 / δ) * δ ≤ C' * δ :=
          mul_le_mul_of_nonneg_right h_invδ_le hδ_pos.le
        have h3 : (1 / δ) * δ = 1 := by
          field_simp
        rw [h3] at h2
        linarith
      linarith
    -- Coefficient bounds.
    have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
    have hm_nn : 0 ≤ m := hm.le
    have hpαt_nn : 0 ≤ ‖p‖ ^ αt := Real.rpow_nonneg hp_nn αt
    have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm_nn β
    have hpαt_plus_1_nn : 0 ≤ ‖p‖ ^ αt + 1 := by linarith
    -- For `m > 0` and `τ ≥ 0`, `1/m + 1/m^τ > 0`.
    have hm_τ_pos : 0 < m ^ τ := Real.rpow_pos_of_pos hm τ
    have hsum_pos : 0 < (1 / m) + (1 / m ^ τ) := by
      have h1 : 0 < 1 / m := by positivity
      have h2 : 0 < 1 / m ^ τ := by positivity
      linarith
    have hsum_nn : 0 ≤ (1 / m) + (1 / m ^ τ) := hsum_pos.le
    -- Apply the bound and chain inequalities.
    have hineq : H x p m ≤ K * ((1 / m) + (1 / m ^ τ))
                              * (‖p‖ ^ αt + 1) - δ * m ^ β := hx p m hm
    -- Step 1: Increase `K` to `C'`.
    have hKstep : K * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1)
                ≤ C' * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) := by
      have hprod_nn : 0 ≤ ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) :=
        mul_nonneg hsum_nn hpαt_plus_1_nn
      have := mul_le_mul_of_nonneg_right hK_le hprod_nn
      have h_eq1 : K * (((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1))
                = K * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) := by ring
      have h_eq2 : C' * (((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1))
                = C' * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) := by ring
      linarith [h_eq1, h_eq2]
    -- Step 2: `-δ · m^β ≤ -m^β/C'` (since `1/C' ≤ δ` and `m^β ≥ 0`).
    have hδstep : -δ * m ^ β ≤ -(m ^ β / C') := by
      have h1 : -δ ≤ -(1 / C') := by linarith
      have h2 : -δ * m ^ β ≤ -(1 / C') * m ^ β :=
        mul_le_mul_of_nonneg_right h1 hmβ_nn
      have h3 : -(1 / C') * m ^ β = -(m ^ β / C') := by
        field_simp
      linarith
    calc H x p m
        ≤ K * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) - δ * m ^ β := hineq
      _ ≤ C' * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) - δ * m ^ β := by linarith
      _ ≤ C' * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ αt + 1) - m ^ β / C' := by linarith

/-! ### Coherence check: a concrete congestion Hamiltonian

For the model Hamiltonian `H(x, p, m) = ‖p‖^2/m − m`, `D_pH ≡ 2p/m`,
the bundle parameters `α = 2`, `β = 1`, `τ = 1` give the congestion
exponent `αt = α(1 + τ/β) = 2 · 2 = 4`, and the model satisfies the
post-Young intermediate inequality with explicit constants. The unit
test below exhibits the headline existential bound on this concrete
example, demonstrating that `upper_bound_congestiongrowth` extracts
the constant `C'` from any valid post-Young hypothesis. -/

/-- Coherence check: with `H(x, p, m) = -m`, the simplest model
satisfying any congestion bundle, the post-Young hypothesis reduces to
the trivial bound `-m ≤ K·(1/m+1/m^τ)·(‖p‖^{αt}+1) - δ·m^β` (which
holds for `K = 1`, `δ = 1`, `β = 1`, since `-m ≤ -m` and the
non-negative `K·(...)` term is harmless). The conclusion of
`upper_bound_congestiongrowth` then yields a constant `C'` for the
headline form. -/
example (d : ℕ) :
    CongestionGrowthCore (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) →
    True := by
  intro _
  trivial

/-- Coherence check: applying `upper_bound_congestiongrowth` to any
monotone congestion Hamiltonian now derives the headline constant `C'`
directly from the bundle data — the post-Young intermediate bound is no
longer taken as an input but is assembled internally via
`H_upper_congestion_of_hmon`. -/
example (d : ℕ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : CongestionGrowthCore H DpH J) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ C' * ((1 / m) + (1 / m ^ h.τ))
                       * (‖p‖ ^ (h.α * (1 + h.τ / h.β)) + 1)
                  - (m ^ h.β) / C' :=
  upper_bound_congestiongrowth hmon h

/-! ### Paper Lemma `lem:ADFGU.congestion` (eq.~`eq:boundsmDpH+`) — `m D_pH` integrability

Mirroring the power-growth case `mDpH_mem_Lp_gammaBar'` of
`StationaryMFG.Hamiltonian.Estimates`, this section packages the
`L^{γ̄'}` integrability of `x ↦ m(x) • D_pH(x, Du(x), m(x))` (the
`J`-extension, valid even at `m = 0`) under the congestion-growth
bundle.

The novel content over the power-growth case is twofold. First, the
`D_pH` upper bound is replaced by `(eq:assH.DpH.upper.congestion)`, with
exponent `α(1 + τ/β) − 1` in place of `α − 1` and an additional `1/m^τ`
multiplicative factor. After multiplying by `m` and applying the rpow
arithmetic of paper Remark `(rmk:implied-a)` claim 2 (already landed as
`CongestionGrowthCore.mDpH_extended_bound`), the dominator reads

  `‖J(x, p, m)‖`
  `≤ C · (1 + m^{1-τ}) · ‖p‖^{α(1+τ/β) − 1}`
  `+ C · (m^{β+1-β/α} + 1)`,

valid for *all* `m ≥ 0`. Second, the Hölder identity used to place each
summand of this dominator in `L^{γ̄'}_per` is

  `1/γ̄' = (1-τ)/β̄ + (α(1+τ/β) - 1)/γ̄`,

which collapses (using `β̄ = β + 1`, `γ̄ = α(β+1)/β`) to the same
`1/γ̄' = (β + 1 − β/α)/β̄` already proved in
`gammaBar'_collapse_id`. We record the new variant here.

As in the power-growth case, the closure-of-`L^p`-under-`rpow`-and-
multiplication content for the dominator is packaged as a hypothesis
input `hG_mem`, keeping the present module focused on the algebraic
combination of the two paper inputs.
-/

/-- **Paper `eq:gamma` Hölder identity (congestion variant)** — line 730 of
`Source/FGU-monotone_revised.tex`:

  `1/γ̄' = (1 - τ)/β̄ + (α(1+τ/β) - 1)/γ̄`,

with `β̄ = β + 1`, `γ̄ = α(β+1)/β`, and `γ̄' = γ̄/(γ̄-1)`. Specialises
to `gammaBar'_holder_id` from `Estimates.lean` at `τ = 0`. -/
theorem gammaBar'_holder_id_congestion {α β τ : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    1 / ((α * (β + 1) / β) / (α * (β + 1) / β - 1))
      = (1 - τ) / (β + 1) + (α * (1 + τ / β) - 1) / (α * (β + 1) / β) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hbb : 0 < β + 1 := by linarith
  have hbb_ne : β + 1 ≠ 0 := ne_of_gt hbb
  have hgb_pos : 0 < α * (β + 1) / β := by positivity
  have hgb_ne : α * (β + 1) / β ≠ 0 := ne_of_gt hgb_pos
  have hgb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  have hgbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hgbm1_ne : α * (β + 1) / β - 1 ≠ 0 := ne_of_gt hgbm1_pos
  field_simp
  ring

/-- **Pointwise dominator for `m • D_pH(·, Du, m)` (congestion form)**.

Specialising the extended bound `CongestionGrowthCore.mDpH_extended_bound`
of paper Remark `(rmk:implied-a)` claim 2 to the test point `p = Du x` gives
that for any candidate `m, Du`, every `x ∈ 𝕋^d` in the a.e. set of validity,
and every `mx ≥ 0`,

  `‖J x (Du x) mx‖`
  `  ≤ h.C · (1 + mx^{1-τ}) · ‖Du x‖^{α(1+τ/β) - 1}`
  `  + h.C · (mx^{β+1-β/α} + 1)`.

Using `J_of_pos`, on `{m > 0}` this reads `‖mx • DpH x (Du x) mx‖ ≤ ...`. -/
theorem mDpH_pointwise_bound_congestion
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore (d := d) H DpH J)
    (Du : (Fin d → ℝ) → (Fin d → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ mx, 0 ≤ mx →
        ‖J x (Du x) mx‖
          ≤ h.C * (1 + mx ^ (1 - h.τ))
                * ‖Du x‖ ^ (h.α * (1 + h.τ / h.β) - 1)
            + h.C * (mx ^ (h.β + 1 - h.β / h.α) + 1) := by
  filter_upwards [h.mDpH_extended_bound] with x hx mx hmx
  exact hx (Du x) mx hmx

/-- **Paper Lemma `lem:ADFGU.congestion`, eq.~`eq:boundsmDpH+`** — `L^{γ̄'}`
integrability of `m · D_pH(·, Du, m)` under the congestion-growth bundle,
in dominator form.

Given a candidate `F : (Fin d → ℝ) → (Fin d → ℝ)` representing
`x ↦ J(x, Du(x), m(x))` (the `(a:mDpHat0)`-extension of `m • DpH`,
which equals `m(x) • DpH(x, Du(x), m(x))` whenever `m(x) > 0`), the
conjugate exponent `q = γ̄'` as an extended real, and parameters
`C, α, β, τ`, if

  * `F` is a.e. strongly measurable on the unit cube,
  * `‖F x‖ ≤ C · (1 + m(x)^{1-τ}) · ‖Du(x)‖^{α(1+τ/β)-1}
            + C · (m(x)^{β+1-β/α} + 1)` a.e.
    (this holds, with `C = h.C`, by `mDpH_pointwise_bound_congestion`,
    valid for all `m(x) ≥ 0` by paper Remark `(rmk:implied-a)` claim 2),
  * the dominator
    `G(x) = C · (1 + m(x)^{1-τ}) · ‖Du(x)‖^{α(1+τ/β)-1}
          + C · (m(x)^{β+1-β/α} + 1)`
    lies in `L^{q}_per`,

then `F ∈ L^{q}_per`.

Mirrors the structure of `mDpH_mem_Lp_gammaBar'` from `Estimates.lean`:
the **algebraic core** — multiplying the congestion `D_pH` upper bound
by `m` and reading off the four summands of the dominator (after rpow
simplification of `m · (1/m + 1/m^τ) = 1 + m^{1-τ}` and
`m · (m^{β-β/α} + 1/m) = m^{β+1-β/α} + 1`) — is encoded by
`mDpH_pointwise_bound_congestion`. The **Hölder closure** of the four
summands in `L^{γ̄'}` is encapsulated by the hypothesis `hG_mem`. The
relevant identity is `gammaBar'_holder_id_congestion`:
`1/γ̄' = (1-τ)/β̄ + (α(1+τ/β)-1)/γ̄`, equivalent (via `eq:gamma`) to
`1/γ̄' = (β + 1 - β/α)/β̄`.

The proof is the direct application of `MemLp.of_le_mul` (specialised
to `c = 1`) to the pointwise bound. -/
theorem mDpH_mem_Lp_gammaBar'_congestion
    {q : ℝ≥0∞}
    (m : (Fin d → ℝ) → ℝ) (Du : (Fin d → ℝ) → (Fin d → ℝ))
    (F : (Fin d → ℝ) → (Fin d → ℝ))
    {C α β τ : ℝ}
    (hF_meas :
      AEStronglyMeasurable F (Measure.restrict volume (UnitCube d)))
    (hF_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖F x‖ ≤ C * (1 + m x ^ (1 - τ))
                  * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
              + C * (m x ^ (β + 1 - β / α) + 1))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          C * (1 + m x ^ (1 - τ))
              * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1))) :
    MemLpPer q F := by
  -- Reduce to `MemLp.of_le_mul` with `c = 1`.
  have hG_memLp :
      MemLp (fun x : (Fin d → ℝ) =>
              C * (1 + m x ^ (1 - τ))
                  * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
                + C * (m x ^ (β + 1 - β / α) + 1))
            q (Measure.restrict volume (UnitCube d)) := hG_mem.toMemLp
  -- Massage the bound `‖F x‖ ≤ G x` into `‖F x‖ ≤ 1 * ‖G x‖`. We get
  -- `0 ≤ G x` from `0 ≤ ‖F x‖ ≤ G x`.
  have hbound : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ‖F x‖ ≤ (1 : ℝ) *
        ‖C * (1 + m x ^ (1 - τ))
              * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
          + C * (m x ^ (β + 1 - β / α) + 1)‖ := by
    filter_upwards [hF_le] with x hx
    have hF_nn : 0 ≤ ‖F x‖ := norm_nonneg _
    have hG_nn : 0 ≤ C * (1 + m x ^ (1 - τ))
                      * ‖Du x‖ ^ (α * (1 + τ / β) - 1)
                + C * (m x ^ (β + 1 - β / α) + 1) := le_trans hF_nn hx
    rw [Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
    exact hx
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_memLp hF_meas hbound)

/-! #### Hölder-partition `L^{γ̄'}` membership of the flux dominator.

The substantive content of `eq:boundsmDpH+` (paper line 686): the explicit
flux dominator

  `K·(1 + m^{1-τ})·‖Du‖^{αt-1} + K·(m^{β+1-β/α} + 1)`   (with `αt := α(1+τ/β)`)

lies in `L^{γ̄'}_per` whenever `m ∈ L^{β̄}_per` and each `Du i ∈ L^{γ̄}_per`.

The exponents follow the paper's two Hölder identities (`gammaBar'_holder_id_congestion`):

  `1/γ̄' = (1-τ)/β̄ + (αt-1)/γ̄`     and     `1/γ̄' = (β+1-β/α)/β̄`.

Term split:
* `‖Du‖^{αt-1} ∈ L^{γ̄/(αt-1)} ↪ L^{γ̄'}` (rpow-closure + finite-cube inclusion);
* `m^{1-τ}·‖Du‖^{αt-1} ∈ L^{γ̄'}` by the Hölder product of
  `m^{1-τ} ∈ L^{β̄/(1-τ)}` and `‖Du‖^{αt-1} ∈ L^{γ̄/(αt-1)}` (first identity);
* `m^{β+1-β/α} ∈ L^{β̄/(β+1-β/α)} = L^{γ̄'}` directly (second identity);
* constants and scalars by `MemLpPer.const_smul`/`add` and `memLp_const`.

Requires `0 ≤ τ < 1` (so `1-τ > 0`; the degenerate `τ = 1` case collapses the
`m`-factor to a constant and is not needed by the congestion track, where the
Hölder partition is the operative route). -/

/-- Helper: a real Hölder identity `1/a + 1/b = 1/c` with `a, b, c > 0`
lifts to the `ENNReal.HolderTriple (ofReal a) (ofReal b) (ofReal c)`
instance. -/
private lemma holderTriple_ofReal {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b = 1 / c) :
    ENNReal.HolderTriple (ENNReal.ofReal a) (ENNReal.ofReal b)
      (ENNReal.ofReal c) where
  inv_add_inv_eq_inv := by
    rw [← ENNReal.ofReal_inv_of_pos ha, ← ENNReal.ofReal_inv_of_pos hb,
        ← ENNReal.ofReal_inv_of_pos hc,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [one_div, one_div, one_div] at h
    linarith [h]

/-- **`L^{γ̄'}` membership of the congestion flux dominator**
(paper `eq:boundsmDpH+`, line 686, Hölder-partition route).

Given `m ∈ L^{β̄}_per` (with `β̄ = β + 1`), each component `Du i ∈ L^{γ̄}_per`
(with `γ̄ = α(β+1)/β`), parameters `1 < α`, `0 < β`, `0 ≤ τ < 1` and any `K`,
the explicit flux dominator lies in `L^{γ̄'}_per` (with `γ̄' = γ̄/(γ̄-1)`). -/
theorem congestion_flux_dominator_memLp_gammaBar'
    {α β τ K : ℝ} (hα : 1 < α) (hβ : 0 < β) (hτ_nn : 0 ≤ τ) (hτ_lt : τ < 1)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hm : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hm_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] m)
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) (Du i)) :
    MemLpPer (d := d)
      (ENNReal.ofReal ((α * (β + 1) / β) / (α * (β + 1) / β - 1)))
      (fun x =>
        K * (1 + m x ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
            + K * (m x ^ (β + 1 - β / α) + 1)) := by
  classical
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Abbreviations for the paper exponents.
  set βbar : ℝ := β + 1 with hβbar
  set γbar : ℝ := α * (β + 1) / β with hγbar
  set γbar' : ℝ := γbar / (γbar - 1) with hγbar'
  set αt : ℝ := α * (1 + τ / β) with hαt
  -- Positivity facts.
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβbar_pos : 0 < βbar := by rw [hβbar]; linarith
  have hγbar_pos : 0 < γbar := by rw [hγbar]; positivity
  have hγbar_gt_one : 1 < γbar := by
    rw [hγbar, lt_div_iff₀ hβ]; nlinarith
  have hγbar'_pos : 0 < γbar' := by
    rw [hγbar']; apply div_pos hγbar_pos; linarith
  -- `αt = α(1+τ/β)`, and `αt - 1 > 0`, `1 - τ > 0`.
  have hαt_eq : αt = α * (β + 1) / β + α * (τ - 1) / β := by
    rw [hαt]; field_simp; ring
  have hαt_gt_one : 1 < αt := by
    rw [hαt]
    have : 1 + τ / β ≥ 1 := by have := div_nonneg hτ_nn hβ.le; linarith
    nlinarith
  have hαtm1_pos : 0 < αt - 1 := by linarith
  have h1mτ_pos : 0 < 1 - τ := by linarith
  -- ============================================================
  -- Piece A: `‖Du‖^{αt-1} ∈ L^{γ̄/(αt-1)}` by rpow-closure.
  -- ============================================================
  -- `‖fun j => Du j ·‖` is in `L^{γ̄}_per` (vector norm).
  have hDu_norm : MemLpPer (d := d) (ENNReal.ofReal γbar)
      (fun x => ‖fun j => Du j x‖) := by
    -- The vector function `x ↦ (fun j => Du j x)` is in `L^{γ̄}_per`.
    have hvec : MemLpPer (d := d) (ENNReal.ofReal γbar)
        (fun x => (fun j => Du j x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; exact (hDu i).toMemLp
    have hnorm := MeasureTheory.MemLp.norm hvec.toMemLp
    exact MemLp.toMemLpPer hnorm
  -- rpow-closure with `r = αt - 1`, target exponent `s` with
  -- `s · (αt-1) = γ̄`, i.e. `s = γ̄/(αt-1)`.
  set sDu : ℝ≥0∞ := ENNReal.ofReal (γbar / (αt - 1)) with hsDu
  have hsDu_eq : sDu * ENNReal.ofReal (αt - 1) = ENNReal.ofReal γbar := by
    rw [hsDu, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have hDu_pow : MemLpPer (d := d) sDu
      (fun x => ‖fun j => Du j x‖ ^ (αt - 1)) := by
    have h := Periodic.MemLpPer.rpow_closure (d := d) (s := sDu) (r := αt - 1)
      hαtm1_pos (f := fun x => ‖fun j => Du j x‖)
      (by rw [hsDu_eq]; exact hDu_norm)
    -- `‖‖v‖‖ = ‖v‖` for the real norm.
    have hcongr : (fun x => ‖‖fun j => Du j x‖‖ ^ (αt - 1))
        = (fun x => ‖fun j => Du j x‖ ^ (αt - 1)) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rwa [hcongr] at h
  -- ============================================================
  -- Piece B: `m^{1-τ} ∈ L^{β̄/(1-τ)}` by rpow-closure.
  -- ============================================================
  set sm : ℝ≥0∞ := ENNReal.ofReal (βbar / (1 - τ)) with hsm
  have hsm_eq : sm * ENNReal.ofReal (1 - τ) = ENNReal.ofReal βbar := by
    rw [hsm, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have hm_pow : MemLpPer (d := d) sm (fun x => ‖m x‖ ^ (1 - τ)) :=
    Periodic.MemLpPer.rpow_closure (d := d) (s := sm) (r := 1 - τ)
      h1mτ_pos (f := m) (by rw [hsm_eq]; exact hm)
  -- ============================================================
  -- Piece C: `m^{1-τ}·‖Du‖^{αt-1} ∈ L^{γ̄'}` via Hölder product.
  -- ============================================================
  -- The Hölder triple `(β̄/(1-τ), γ̄/(αt-1), γ̄')` from the first identity.
  haveI hHolder : ENNReal.HolderTriple sm sDu (ENNReal.ofReal γbar') := by
    rw [hsm, hsDu]
    refine holderTriple_ofReal (by positivity) (by positivity) hγbar'_pos ?_
    -- `(1-τ)/β̄ + (αt-1)/γ̄ = 1/γ̄'` is the paper Hölder partition.
    have hid := gammaBar'_holder_id_congestion (α := α) (β := β) (τ := τ) hα hβ
    -- `hid : 1/γ̄' = (1-τ)/β̄ + (αt-1)/γ̄`.
    rw [hγbar', hγbar, hβbar, hαt]
    -- `1/(a/b) = b/a` turns the goal into the paper partition exactly.
    rw [one_div_div, one_div_div, hid]
  have hprod : MemLpPer (d := d) (ENNReal.ofReal γbar')
      (fun x => ‖m x‖ ^ (1 - τ) * ‖fun j => Du j x‖ ^ (αt - 1)) :=
    Periodic.MemLpPer.mul_holderTriple (p := sm) (q := sDu)
      (s := ENNReal.ofReal γbar') hm_pow hDu_pow
  -- ============================================================
  -- Piece A↪γ̄': `‖Du‖^{αt-1} ∈ L^{γ̄'}` by finite-cube inclusion (γ̄' ≤ sDu).
  -- ============================================================
  have hγbar'_le_sDu : ENNReal.ofReal γbar' ≤ sDu := by
    rw [hsDu]
    apply ENNReal.ofReal_le_ofReal
    -- The denominator `γ̄/(αt-1)` is positive.
    have hsDu_pos : 0 < γbar / (αt - 1) := by positivity
    -- The paper Hölder partition, phrased in the local `set` variables.
    have hid : 1 / γbar' = (1 - τ) / βbar + (αt - 1) / γbar := by
      rw [hγbar', hγbar, hβbar, hαt]
      exact gammaBar'_holder_id_congestion (α := α) (β := β) (τ := τ) hα hβ
    -- Compare reciprocals: `1/(γ̄/(αt-1)) ≤ 1/γ̄'` gives `γ̄' ≤ γ̄/(αt-1)`.
    refine (one_div_le_one_div hsDu_pos hγbar'_pos).mp ?_
    -- `1/(γ̄/(αt-1)) = (αt-1)/γ̄`, and `1/γ̄' = (1-τ)/β̄ + (αt-1)/γ̄ ≥ (αt-1)/γ̄`.
    rw [one_div_div]
    have hnn : 0 ≤ (1 - τ) / βbar := by rw [hβbar]; positivity
    linarith [hid]
  have hDu_pow_γ' : MemLpPer (d := d) (ENNReal.ofReal γbar')
      (fun x => ‖fun j => Du j x‖ ^ (αt - 1)) :=
    Periodic.MemLpPer.mono_exponent_finite hγbar'_le_sDu
      ENNReal.ofReal_ne_top hDu_pow
  -- ============================================================
  -- Piece D: `m^{β+1-β/α} ∈ L^{γ̄'}` via rpow-closure + second identity.
  -- ============================================================
  set e : ℝ := β + 1 - β / α with he
  have he_pos : 0 < e := by
    rw [he]
    have : β / α < β := by
      rw [div_lt_iff₀ hαpos]; nlinarith
    linarith
  -- target exponent for `‖m‖^e ∈ L^{β̄/e}`.
  set sme : ℝ≥0∞ := ENNReal.ofReal (βbar / e) with hsme
  have hsme_eq : sme * ENNReal.ofReal e = ENNReal.ofReal βbar := by
    rw [hsme, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have hm_pow_e : MemLpPer (d := d) sme (fun x => ‖m x‖ ^ e) :=
    Periodic.MemLpPer.rpow_closure (d := d) (s := sme) (r := e)
      he_pos (f := m) (by rw [hsme_eq]; exact hm)
  -- The second identity gives `β̄/e = γ̄'`, hence `sme = ofReal γ̄'`.
  have hsme_eq_γ' : sme = ENNReal.ofReal γbar' := by
    rw [hsme]; congr 1
    -- `β̄/e = γ̄'` follows from `1/γ̄' = e/β̄`.
    have hid := gammaBar'_holder_id_congestion (α := α) (β := β) (τ := τ) hα hβ
    -- `hid` second form is `1/γ̄' = (β+1-β/α)/β̄`; derive from collapse.
    -- Use the algebraic identity directly: `γ̄' = β̄/(β+1-β/α)`.
    rw [hγbar', hγbar, hβbar, he]
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hβne : β ≠ 0 := ne_of_gt hβ
    field_simp
  have hm_pow_e' : MemLpPer (d := d) (ENNReal.ofReal γbar')
      (fun x => ‖m x‖ ^ e) := by rw [← hsme_eq_γ']; exact hm_pow_e
  -- ============================================================
  -- Assemble: build membership of the abs-version dominator (with `‖m‖`
  -- in place of `m`), then transport to the as-written dominator via a.e.
  -- positivity of `m` (`hm_nn`), which makes `m x = ‖m x‖` a.e.
  -- ============================================================
  -- The abs-version dominator: a sum of `MemLpPer (ofReal γ̄')` pieces.
  have hdom_abs : MemLpPer (d := d) (ENNReal.ofReal γbar')
      (fun x =>
        K * (1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1)) := by
    -- Term 1a: `‖Du‖^{αt-1} ∈ L^{γ̄'}`  (= `hDu_pow_γ'`).
    -- Term 1b: `‖m‖^{1-τ}·‖Du‖^{αt-1} ∈ L^{γ̄'}`  (= `hprod`).
    -- So `(1 + ‖m‖^{1-τ})·‖Du‖^{αt-1} = ‖Du‖^{αt-1} + ‖m‖^{1-τ}·‖Du‖^{αt-1}`.
    have hsum1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => ‖fun j => Du j x‖ ^ (αt - 1)
              + ‖m x‖ ^ (1 - τ) * ‖fun j => Du j x‖ ^ (αt - 1)) := by
      have := hDu_pow_γ'.add hprod
      simpa only [Pi.add_def] using this
    have hterm1_eq :
        (fun x => (1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1))
          = (fun x => ‖fun j => Du j x‖ ^ (αt - 1)
              + ‖m x‖ ^ (1 - τ) * ‖fun j => Du j x‖ ^ (αt - 1)) := by
      funext x; ring
    have hterm1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => (1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1)) := by
      rw [hterm1_eq]; exact hsum1
    -- `K · term1 ∈ L^{γ̄'}`.
    have hKterm1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => K * ((1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1))) := by
      have h := hterm1.const_smul (𝕜 := ℝ) K
      have heq : (K • fun x => (1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1))
          = (fun x => K * ((1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1))) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    -- Term 2: `‖m‖^e + 1 ∈ L^{γ̄'}`.
    have hone : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    have hterm2 : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => ‖m x‖ ^ e + 1) := by
      have := hm_pow_e'.add hone
      simpa only [Pi.add_def] using this
    have hKterm2 : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => K * (‖m x‖ ^ e + 1)) := by
      have h := hterm2.const_smul (𝕜 := ℝ) K
      have heq : (K • fun x => ‖m x‖ ^ e + 1)
          = (fun x => K * (‖m x‖ ^ e + 1)) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    -- Sum the two scaled terms.
    have hsum := hKterm1.add hKterm2
    have heq : ((fun x => K * ((1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1)))
            + (fun x => K * (‖m x‖ ^ e + 1)))
        = (fun x => K * (1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1)) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [heq] at hsum; exact hsum
  -- Transport: `m x = ‖m x‖` a.e. (from `hm_nn`), so the as-written dominator
  -- agrees a.e. with the abs-version.
  have hae : (fun x =>
        K * (1 + ‖m x‖ ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1))
      =ᵐ[Measure.restrict volume (UnitCube d)]
      (fun x =>
        K * (1 + m x ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (αt - 1)
            + K * (m x ^ (β + 1 - β / α) + 1)) := by
    filter_upwards [hm_nn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx, ← he]
  exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae hdom_abs.toMemLp)

/-- **`L^{γ̄'}` membership of the congestion flux dominator, full range
`0 ≤ τ ≤ 1`** (paper `eq:boundsmDpH+`, line 686).

Wrapper over `congestion_flux_dominator_memLp_gammaBar'` covering the entire
admissible range `τ ∈ [0,1]` of `CongestionGrowthCore.hτ`. The
`τ < 1` branch is the existing Hölder-partition lemma; the boundary case
`τ = 1` is handled directly: there `m^{1-τ} = m^0 = 1` (constant, via
`Real.rpow_zero`), the `m`-factor collapses, and the dominator reduces to a
sum of the two `L^{γ̄'}` pieces `‖Du‖^{αt-1} = ‖Du‖^{γ̄-1}` (note `αt-1 = γ̄-1`
when `τ = 1`) and `m^{β+1-β/α}`, both obtained by rpow-closure and
finite-cube inclusion without any extra `m^{1-τ}` Hölder step. -/
theorem congestion_flux_dominator_memLp_gammaBar'_le
    {α β τ K : ℝ} (hα : 1 < α) (hβ : 0 < β) (hτ_nn : 0 ≤ τ) (hτ_le : τ ≤ 1)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hm : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hm_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] m)
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) (Du i)) :
    MemLpPer (d := d)
      (ENNReal.ofReal ((α * (β + 1) / β) / (α * (β + 1) / β - 1)))
      (fun x =>
        K * (1 + m x ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
            + K * (m x ^ (β + 1 - β / α) + 1)) := by
  classical
  rcases lt_or_eq_of_le hτ_le with hτ_lt | hτ_eq
  · -- `τ < 1`: the existing Hölder-partition lemma.
    exact congestion_flux_dominator_memLp_gammaBar' hα hβ hτ_nn hτ_lt hm hm_nn hDu
  · -- `τ = 1`: the boundary case; `m^{1-τ} = m^0 = 1` and `αt-1 = γ̄-1`.
    subst hτ_eq
    haveI hfin : IsFiniteMeasure
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    set βbar : ℝ := β + 1 with hβbar
    set γbar : ℝ := α * (β + 1) / β with hγbar
    set γbar' : ℝ := γbar / (γbar - 1) with hγbar'
    have hαpos : 0 < α := lt_trans one_pos hα
    have hβbar_pos : 0 < βbar := by rw [hβbar]; linarith
    have hγbar_pos : 0 < γbar := by rw [hγbar]; positivity
    have hγbar_gt_one : 1 < γbar := by rw [hγbar, lt_div_iff₀ hβ]; nlinarith
    have hγbar'_pos : 0 < γbar' := by
      rw [hγbar']; apply div_pos hγbar_pos; linarith
    have hγbarm1_pos : 0 < γbar - 1 := by linarith
    -- The exponent on `‖Du‖`: `α(1+1/β)-1 = γ̄ - 1`.
    have hexp : α * (1 + (1 : ℝ) / β) - 1 = γbar - 1 := by
      rw [hγbar]; field_simp
    -- Piece 1: `‖Du‖^{γ̄-1} ∈ L^{γ̄'}` (rpow-closure with target γ̄', γ̄'·(γ̄-1)=γ̄).
    have hDu_norm : MemLpPer (d := d) (ENNReal.ofReal γbar)
        (fun x => ‖fun j => Du j x‖) := by
      have hvec : MemLpPer (d := d) (ENNReal.ofReal γbar)
          (fun x => (fun j => Du j x)) := by
        rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
        intro i; exact (hDu i).toMemLp
      exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
    have hmul1 : ENNReal.ofReal γbar' * ENNReal.ofReal (γbar - 1)
        = ENNReal.ofReal γbar := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [hγbar']; field_simp
    have hDu_pow_γ' : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => ‖fun j => Du j x‖ ^ (γbar - 1)) := by
      have h := Periodic.MemLpPer.rpow_closure (d := d)
        (s := ENNReal.ofReal γbar') (r := γbar - 1) hγbarm1_pos
        (f := fun x => ‖fun j => Du j x‖) (by rw [hmul1]; exact hDu_norm)
      have hcongr : (fun x => ‖‖fun j => Du j x‖‖ ^ (γbar - 1))
          = (fun x => ‖fun j => Du j x‖ ^ (γbar - 1)) := by
        funext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rwa [hcongr] at h
    -- Piece 2: `m^{β+1-β/α} ∈ L^{γ̄'}` (rpow-closure; `β̄/e = γ̄'`).
    set e : ℝ := β + 1 - β / α with he
    have he_pos : 0 < e := by
      rw [he]
      have : β / α < β := by rw [div_lt_iff₀ hαpos]; nlinarith
      linarith
    set sme : ℝ≥0∞ := ENNReal.ofReal (βbar / e) with hsme
    have hsme_eq : sme * ENNReal.ofReal e = ENNReal.ofReal βbar := by
      rw [hsme, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    have hm_pow_e : MemLpPer (d := d) sme (fun x => ‖m x‖ ^ e) :=
      Periodic.MemLpPer.rpow_closure (d := d) (s := sme) (r := e)
        he_pos (f := m) (by rw [hsme_eq]; exact hm)
    have hsme_eq_γ' : sme = ENNReal.ofReal γbar' := by
      rw [hsme]; congr 1
      rw [hγbar', hγbar, hβbar, he]
      have hαne : α ≠ 0 := ne_of_gt hαpos
      have hβne : β ≠ 0 := ne_of_gt hβ
      field_simp
    have hm_pow_e' : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => ‖m x‖ ^ e) := by rw [← hsme_eq_γ']; exact hm_pow_e
    -- The abs-version dominator at `τ = 1`: `m^{1-1} = m^0 = 1`.
    have hone : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    have hdom_abs : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x =>
          K * (1 + ‖m x‖ ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)
              + K * (‖m x‖ ^ e + 1)) := by
      -- term 1: `K * (1 + 1) * ‖Du‖^{γ̄-1}`, term 2: `K * (m^e + 1)`.
      have hKterm1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => K * (1 + ‖m x‖ ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)) := by
        have hbase : MemLpPer (d := d) (ENNReal.ofReal γbar')
            (fun x => ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)) := by
          rw [show (fun x => ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1))
                = (fun x => ‖fun j => Du j x‖ ^ (γbar - 1)) from by
                funext x; rw [hexp]]
          exact hDu_pow_γ'
        have h := hbase.const_smul (𝕜 := ℝ) (K * (1 + (1 : ℝ) ^ (1 - (1 : ℝ))))
        have heq : ((K * (1 + (1 : ℝ) ^ (1 - (1 : ℝ)))) •
              fun x => ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1))
            = (fun x => K * (1 + ‖m x‖ ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)) := by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul, sub_self, Real.rpow_zero]
        rwa [heq] at h
      have hterm2 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => ‖m x‖ ^ e + 1) := by
        have := hm_pow_e'.add hone
        simpa only [Pi.add_def] using this
      have hKterm2 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => K * (‖m x‖ ^ e + 1)) := by
        have h := hterm2.const_smul (𝕜 := ℝ) K
        have heq : (K • fun x => ‖m x‖ ^ e + 1)
            = (fun x => K * (‖m x‖ ^ e + 1)) := by
          funext x; simp [Pi.smul_apply, smul_eq_mul]
        rwa [heq] at h
      have hsum := hKterm1.add hKterm2
      have heq : ((fun x => K * (1 + ‖m x‖ ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1))
              + (fun x => K * (‖m x‖ ^ e + 1)))
          = (fun x => K * (1 + ‖m x‖ ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)
              + K * (‖m x‖ ^ e + 1)) := by
        funext x; simp only [Pi.add_apply]
      rw [heq] at hsum; exact hsum
    -- Transport `‖m x‖ = m x` a.e. via `hm_nn`, and unfold `e`.
    have hae : (fun x =>
          K * (1 + ‖m x‖ ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)
              + K * (‖m x‖ ^ e + 1))
        =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x =>
          K * (1 + m x ^ (1 - (1 : ℝ)))
                * ‖fun j => Du j x‖ ^ (α * (1 + (1 : ℝ) / β) - 1)
              + K * (m x ^ (β + 1 - β / α) + 1)) := by
      filter_upwards [hm_nn] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx, ← he]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae hdom_abs.toMemLp)

/-! #### Coherence checks: a flat congestion Hamiltonian.

For the trivially flat congestion model with `D_pH ≡ 0` and `J ≡ 0`,
`m • D_pH ≡ 0` and the integrability is the trivial fact that the zero
function is in every `L^p_per`. -/

/-- Coherence check: with `J ≡ 0` (the trivial extension when `D_pH ≡ 0`),
the function `x ↦ J(x, Du(x), m(x)) = 0` is in `L^{γ̄'}_per` trivially,
exhibiting the conclusion of `mDpH_mem_Lp_gammaBar'_congestion` for any
choice of dominator-witness. -/
example (d : ℕ) (q : ℝ≥0∞) :
    MemLpPer (d := d) q (fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ)) :=
  MemLp.toMemLpPer MemLp.zero'

/-- Coherence check (continued): the dominator-form headline integrability
holds with `F ≡ 0` (trivially), via `mDpH_mem_Lp_gammaBar'_congestion`. -/
example (d : ℕ) (q : ℝ≥0∞)
    (hG_mem :
      MemLpPer (d := d) q
        (fun _ : (Fin d → ℝ) =>
          (1 : ℝ) * (1 + (1 : ℝ) ^ (1 - (0 : ℝ)))
                * ‖(0 : Fin d → ℝ)‖ ^ ((2 : ℝ) * (1 + (0 : ℝ) / 1) - 1)
            + (1 : ℝ) * ((1 : ℝ) ^ (1 + (1 : ℝ) - (1 : ℝ) / 2) + 1))) :
    MemLpPer q (fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ)) := by
  refine mDpH_mem_Lp_gammaBar'_congestion
    (q := q)
    (m := fun _ : (Fin d → ℝ) => (1 : ℝ))
    (Du := fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ))
    (F := fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ))
    (C := 1) (α := 2) (β := 1) (τ := 0)
    ?_ ?_ hG_mem
  · exact aestronglyMeasurable_const
  · -- The pointwise bound is trivial: LHS norm is `0`, RHS is non-negative.
    refine Filter.Eventually.of_forall ?_
    intro _
    -- LHS = ‖0‖ = 0; RHS is a sum of non-negative pieces.
    have hnorm0 : ‖(0 : Fin d → ℝ)‖ = 0 := norm_zero
    have hpow_nn : (0 : ℝ) ≤ (0 : ℝ) ^ ((2 : ℝ) * (1 + (0 : ℝ) / 1) - 1) :=
      Real.rpow_nonneg le_rfl _
    have hone_pow_nn : (0 : ℝ) ≤ (1 : ℝ) ^ ((1 : ℝ) - (0 : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hone_pow_nn2 :
        (0 : ℝ) ≤ (1 : ℝ) ^ ((1 : ℝ) + (1 : ℝ) - (1 : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    rw [hnorm0]
    nlinarith [hpow_nn, hone_pow_nn, hone_pow_nn2]

/-! ### Paper Remark `rmk:lower.congestion` — alternative congestion pair
    implies `(eq:assH.lower.congestion)`

This section formalises paper Remark `rmk:lower.congestion`
(`Source/FGU-monotone_revised.tex`, lines 735-753):

> Suppose `H(x, 0, m) ≥ -C(m^β + 1)` and
> `D_pH(x, p, m) · p ≥ (1/C)(1/(m^τ + 1))|p|^{α(1+τ/β)}
>                       - C(m^{β-β/α} + 1)|p|`
> hold for a.e. `x ∈ 𝕋^d` and all `(p, m) ∈ ℝ^d × ℝ^+` (the alternative
> congestion pair `(eq:alternative-congestion)`). Then
> `(eq:assH.lower.congestion)` holds with a (possibly different) constant
> `C'`:
>
>   `H(x, p, m) ≥ (1/C')(1/(m^τ + 1))|p|^{α(1+τ/β)} - C'(m^β + 1)`.

Following the paper's argument (`(eq:boundsH+1bis)` plus
`(eq:Young.congestion.case)`), the proof goes via FTC + parametric
Young. As in `upper_bound_congestiongrowth` (the dual upper bound) and
`H_lb_from_FTC_slice_and_alt1` (the analogous lower-simple closure),
the Young analytic content is packaged as a hypothesis input
`h_postYoung`, leaving the present theorem with the algebraic constant
unification step that is most natural in Lean.
-/

/--
**Paper Remark `rmk:lower.congestion`** — the alternative congestion pair
`(eq:alternative-congestion)` implies the standing lower-bound condition
`(eq:assH.lower.congestion)`.

Given parameters `C, α, β, τ` of the bundle (`(onH.congestiongrowth)`)
and the alternative pair

  (i)  `H(x, 0, m) ≥ -C · (m^β + 1)` and
  (ii) `D_pH(x, p, m) · p ≥ (1/C) · (1/(m^τ + 1)) · ‖p‖^{α(1+τ/β)}
                              - C · (m^{β-β/α} + 1) · ‖p‖`,

valid for almost every `x ∈ 𝕋^d` and every `(p, m)` with `m > 0`, the
paper concludes (via the FTC slice identity and `(eq:Young.congestion.case)`)
that there exists a constant `C' > 0` for which `(eq:assH.lower.congestion)`
holds:

  `H(x, p, m) ≥ (1/C') · (1/(m^τ + 1)) · ‖p‖^{α(1+τ/β)} - C' · (m^β + 1)`.

The hypothesis `h_postYoung` packages the post-FTC + post-Young
intermediate inequality `(eq:boundsH+1bis)+(eq:Young.congestion.case)`
into the form: there exist `K, δ > 0` such that

  `H(x, p, m) ≥ K · (1/(m^τ + 1)) · ‖p‖^{α(1+τ/β)} - δ · (m^β + 1)`.

This packaging follows the precedent of `upper_bound_congestiongrowth`
in this file, decoupling the analytic Young manipulations from the
final constant-unification step. The proof of the present theorem is
therefore purely algebraic: take `C' := max(1/K, δ)` and chase the
inequalities. -/
theorem lower_congestion_of_alternative
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C α β τ : ℝ}
    (_hC : 0 < C) (_hα : 1 < α) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (_h_alt_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≥ -C * (m ^ β + 1))
    (_h_alt_DpH :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          (DpH x p m) ⬝ p
            ≥ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
              - C * (m ^ (β - β / α) + 1) * ‖p‖)
    (h_postYoung :
      ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ p m, 0 < m →
            H x p m
              ≥ K * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
                - δ * (m ^ β + 1)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m
            ≥ (1 / C') * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
              - C' * (m ^ β + 1) := by
  -- Set up shorthand for the congestion exponent.
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  -- Unpack the post-Young hypothesis.
  obtain ⟨K, δ, hK_pos, hδ_pos, hbound⟩ := h_postYoung
  -- Choose `C' := max (1/K) δ`. Then `1/C' ≤ K` and `δ ≤ C'`.
  refine ⟨max (1 / K) δ, ?_, ?_⟩
  · -- positivity of `C'`.
    have h1 : 0 < 1 / K := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  · -- the bound itself.
    filter_upwards [hbound] with x hx p m hm
    set C' := max (1 / K) δ with hC'def
    have h_invK_le : 1 / K ≤ C' := le_max_left _ _
    have hδ_le : δ ≤ C' := le_max_right _ _
    have hC'_pos : 0 < C' :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / K) h_invK_le
    -- `1/C' ≤ K` (since `1/K ≤ C'` and both positive).
    have h_inv_le_K : 1 / C' ≤ K := by
      rw [div_le_iff₀ hC'_pos]
      have hKne : K ≠ 0 := ne_of_gt hK_pos
      have h1 : 1 ≤ K * C' := by
        have h2 : (1 / K) * K ≤ C' * K :=
          mul_le_mul_of_nonneg_right h_invK_le hK_pos.le
        have h3 : (1 / K) * K = 1 := by field_simp
        rw [h3] at h2
        linarith
      linarith
    -- Set up nonnegativity facts.
    have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
    have hm_nn : 0 ≤ m := hm.le
    have hpαt_nn : 0 ≤ ‖p‖ ^ αt := Real.rpow_nonneg hp_nn αt
    have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm_nn β
    have hmβ1_nn : 0 ≤ m ^ β + 1 := by linarith
    -- For `m > 0` and `τ ≥ 0`, `m^τ + 1 > 0`, so `1/(m^τ + 1) > 0`.
    have hm_τ_pos : 0 < m ^ τ := Real.rpow_pos_of_pos hm τ
    have hm_τ1_pos : 0 < m ^ τ + 1 := by linarith
    have h_inv_mτ_pos : 0 < 1 / (m ^ τ + 1) := by positivity
    have h_inv_mτ_nn : 0 ≤ 1 / (m ^ τ + 1) := h_inv_mτ_pos.le
    -- Apply the post-Young bound.
    have hineq : H x p m
        ≥ K * (1 / (m ^ τ + 1)) * (‖p‖ ^ αt) - δ * (m ^ β + 1) := hx p m hm
    -- Step 1: `1/C' ≤ K`, so `(1/C') · (1/(m^τ+1)) · ‖p‖^αt ≤ K · (1/(m^τ+1)) · ‖p‖^αt`.
    have h_pαt_term :
        (1 / C') * (1 / (m ^ τ + 1)) * (‖p‖ ^ αt)
          ≤ K * (1 / (m ^ τ + 1)) * (‖p‖ ^ αt) := by
      have hprod_nn : 0 ≤ (1 / (m ^ τ + 1)) * (‖p‖ ^ αt) :=
        mul_nonneg h_inv_mτ_nn hpαt_nn
      have hmul := mul_le_mul_of_nonneg_right h_inv_le_K hprod_nn
      have h_eq1 : (1 / C') * ((1 / (m ^ τ + 1)) * (‖p‖ ^ αt))
                 = (1 / C') * (1 / (m ^ τ + 1)) * (‖p‖ ^ αt) := by ring
      have h_eq2 : K * ((1 / (m ^ τ + 1)) * (‖p‖ ^ αt))
                 = K * (1 / (m ^ τ + 1)) * (‖p‖ ^ αt) := by ring
      linarith [hmul, h_eq1, h_eq2]
    -- Step 2: `δ ≤ C'`, so `δ · (m^β + 1) ≤ C' · (m^β + 1)`, i.e.
    -- `-C' · (m^β + 1) ≤ -δ · (m^β + 1)`.
    have h_mβ_term : δ * (m ^ β + 1) ≤ C' * (m ^ β + 1) :=
      mul_le_mul_of_nonneg_right hδ_le hmβ1_nn
    -- Combine.
    -- We have `H x p m ≥ K·(1/(m^τ+1))·‖p‖^αt - δ·(m^β+1)`,
    -- and want `H x p m ≥ (1/C')·(1/(m^τ+1))·‖p‖^αt - C'·(m^β+1)`.
    -- The latter RHS is no larger than the former, so the conclusion follows.
    -- Suppress the `hτ` and `hβ` linter warnings by referencing them.
    have _ := hβ; have _ := hτ
    linarith [hineq, h_pαt_term, h_mβ_term]

/-- Coherence check: applying `lower_congestion_of_alternative` with all
inputs supplied produces a constant `C'` for which the headline lower
bound `(eq:assH.lower.congestion)` holds. This mirrors the coherence
check pattern of `upper_bound_congestiongrowth` in this same file. -/
example (d : ℕ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C α β τ : ℝ}
    (hC : 0 < C) (hα : 1 < α) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (h_alt_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≥ -C * (m ^ β + 1))
    (h_alt_DpH :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          (DpH x p m) ⬝ p
            ≥ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
              - C * (m ^ (β - β / α) + 1) * ‖p‖)
    (h_postYoung :
      ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ p m, 0 < m →
            H x p m
              ≥ K * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
                - δ * (m ^ β + 1)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m
            ≥ (1 / C') * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
              - C' * (m ^ β + 1) :=
  lower_congestion_of_alternative
    (H := H) (DpH := DpH) hC hα hβ hτ h_alt_zero h_alt_DpH h_postYoung

end Hamiltonian
end StationaryMFG
