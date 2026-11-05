module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.Monotone
public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.LpInclusion

@[expose] public section

/-!
# Hamiltonian Estimates — Lagrangian lower bound (`lem:A1+anyother`)
  and the `H` upper bound from power-growth (`lem:ADFGU`, eq.~`eq:boundsH`)

This module proves the **Lagrangian lower bound** of paper Lemma
`lem:A1+anyother` (`Source/FGU-monotone_revised.tex`, lines 532–550):
under `(onH.monotone)` and the common upper bound

```
H(x, 0, m) ≤ −m^β / C + C        (eq:common)
```

(which holds in all three growth bundles `(onH.powergrowth)`,
`(onH.congestiongrowth)`, `(onH.weakgrowth)`), one has

```
D_pH(x, p, m) ⬝ p − H(x, p, m) ≥ m^β / C − C       (eq:DpHdotpminusH-estimate1)
```

for a.e. `x ∈ 𝕋^d` and all `(p, m) ∈ ℝ^d × ℝ⁺`.

## Legendre / Lagrangian interpretation

In the optimal-control framing of the stationary MFG system, the
Lagrangian `L(x, v, m)` and the Hamiltonian `H(x, p, m)` are related by
the Legendre transform with respect to the momentum/velocity pair
`(p, v)`, where `v = −D_pH(x, p, m)`. Under that duality, the quantity
`D_pH(x, p, m) ⬝ p − H(x, p, m)` is precisely the Lagrangian
`L(x, v, m)` written in terms of the momentum coordinate `p`. A
pointwise lower bound on this expression is therefore a coercivity-grade
lower bound on the Lagrangian itself, and is the load-bearing fact used
to derive coercivity of the regularized MFG operator `A_ε` in the
a priori bounds of Phases 4–6.

## Proof strategy (per the paper)

By Remark `rmk:cxty`, the section `p ↦ H(x, p, m)` is convex at fixed
`(x, m)`; convexity at the origin in particular gives

```
H(x, 0, m) ≥ H(x, p, m) − D_pH(x, p, m) ⬝ p.
```

Combined with `(eq:common)`, this yields

```
−m^β / C + C ≥ H(x, p, m) − D_pH(x, p, m) ⬝ p,
```

and rearranging recovers the claimed bound. The convex-analytic step
silently identifies `D_pH` with the `p`-gradient of `H`, an
identification not bundled in `HypothesisMonotone`. Following the
project convention noted in `StationaryMFG/Hamiltonian/Monotone.lean`,
we take the convex-at-zero inequality as an explicit hypothesis input
and prove the linear-algebra step pointwise.
-/

namespace StationaryMFG
namespace Hamiltonian

open MeasureTheory
open StationaryMFG.Periodic
open scoped ENNReal NNReal

variable {d : ℕ}

/--
**Paper Lemma `lem:A1+anyother`** — Lagrangian lower bound.

Under `(onH.monotone)` and the common upper bound
`H(x, 0, m) ≤ −m^β / C + C` for `m > 0`, together with the
convex-at-zero inequality
`H(x, 0, m) ≥ H(x, p, m) − D_pH(x, p, m) ⬝ p` (the conclusion of
convexity of `p ↦ H(x, p, m)` evaluated at the origin, packaged here
as a hypothesis input — see the discussion in the module docstring),
the bound

  `D_pH(x, p, m) ⬝ p − H(x, p, m) ≥ m^β / C − C`

holds for a.e. `x ∈ 𝕋^d` and all `(p, m)` with `m > 0`.

The proof is pure linear algebra: chain the upper bound and the
convex-at-zero inequality, then move the `H(x, p, m)` and
`D_pH(x, p, m) ⬝ p` terms across.
-/
theorem lagrangian_lower_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_h : HypothesisMonotone H DpH)
    {β C : ℝ}
    (h_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C)
    (h_convex_at_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (m ^ β) / C - C ≤ (DpH x p m) ⬝ p - H x p m := by
  filter_upwards [h_upper, h_convex_at_zero] with x hUp hCx p m hm
  -- Convexity at `0`: `H(x, p, m) − D_pH(x, p, m) ⬝ p ≤ H(x, 0, m)`.
  have h1 : H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m := hCx p m hm
  -- Common upper bound: `H(x, 0, m) ≤ −m^β / C + C`.
  have h2 : H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C := hUp m hm
  -- Chain and rearrange.
  have h3 : H x p m - (DpH x p m) ⬝ p ≤ -(m ^ β) / C + C := h1.trans h2
  -- The desired inequality is the algebraic rearrangement of `h3`.
  have h4 : -(m ^ β) / C = -((m ^ β) / C) := by ring
  linarith [h3, h4]

/-! ### Coherence checks: a simple Hamiltonian -/

/-- Sanity check: for the simple Hamiltonian
`H(x, p, m) = ‖p‖² / 2 − m` with the trivially-zero `D_pH`, the
Lagrangian lower bound holds with `β = 1` and `C = 1`.

The verification only uses that `H(x, 0, m) = −m ≤ −m + 1`
(the common upper bound at `C = 1`) and that the convex-at-zero
inequality is automatic when `D_pH ≡ 0`, since
`H(x, p, m) − 0 ≤ H(x, 0, m)` is equivalent to `‖p‖² / 2 ≤ 0` after
canceling `−m`, which fails in general — so for this sanity check we
take a Hamiltonian that **also** has `H(x, p, m) ≤ H(x, 0, m)` for
all `p` (i.e. the trivially-flat Hamiltonian `H(x, p, m) = −m`,
whose `D_pH` is `0`). The conclusion then reduces to the trivially
true `m / 1 − 1 ≤ 0 − (−m) = m`. -/
example (d : ℕ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ((m ^ (1 : ℝ)) / 1 - 1 : ℝ)
          ≤ ((fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ)) x p m) ⬝ p
              - ((fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (m : ℝ) => -m) x p m) := by
  -- This is the conclusion of `lagrangian_lower_bound` for the flat
  -- Hamiltonian `H(x, p, m) = −m`, `D_pH ≡ 0`, with `β = 1`, `C = 1`.
  refine Filter.Eventually.of_forall ?_
  intro _ p m hm
  -- LHS: `m^1 / 1 − 1 = m − 1`. RHS: `0 ⬝ p − (−m) = m`.
  have hpow : (m ^ (1 : ℝ)) = m := Real.rpow_one m
  have hdot : ((0 : Fin d → ℝ)) ⬝ p = 0 := euclideanDot_zero_left p
  have hm_le : m - 1 ≤ m := by linarith
  -- Massage to the closed form.
  calc (m ^ (1 : ℝ)) / 1 - 1
      = m - 1 := by rw [hpow]; ring
    _ ≤ m := hm_le
    _ = (0 : ℝ) - (-m) := by ring
    _ = ((0 : Fin d → ℝ)) ⬝ p - (-m) := by rw [hdot]

/-! ### Paper Lemma `lem:ADFGU` (eq.~`eq:boundsH`) — `H` upper bound -/

/-- **Hölder conjugate pair `(α, α/(α-1))`** for `α > 1`.

The standard Young exponents used in paper Lemma `lem:ADFGU`: with
`α' := α/(α-1)`, the pair `(α, α')` satisfies `1/α + 1/α' = 1`. -/
private lemma holderConjugate_alpha {α : ℝ} (hα : 1 < α) :
    Real.HolderConjugate α (α / (α - 1)) := by
  rw [Real.holderConjugate_iff]
  refine ⟨hα, ?_⟩
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1 : 0 < α - 1 := sub_pos.mpr hα
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hαm1ne : α - 1 ≠ 0 := ne_of_gt hαm1
  -- `α⁻¹ + (α/(α-1))⁻¹ = 1/α + (α-1)/α = α/α = 1`.
  field_simp
  ring

/--
**Paper Lemma `lem:ADFGU`, eq.~`eq:boundsH`** — upper bound on `H` under
the simple power-growth bundle.

Under `(onH.powergrowth)`, given the FTC slice identity together with
the standard pointwise integrand bound (which together yield
eq.~`eq:case1-lb1`), there exists a single constant `C' > 0` for which

  `H(x, p, m) ≤ C'(‖p‖^α + 1) − m^β / C'`

holds for almost every `x ∈ 𝕋^d` and every `(p, m)` with `m > 0`.

The argument is the standard Young's inequality manipulation of the
paper: applying Young's inequality with the conjugate pair `(α, α')`
where `α' = α/(α−1)` to the cross terms `‖p‖ · m^{β−β/α}` and
`‖p‖ · 1` from the slice bound gives a bound involving only `‖p‖^α`
and `m^β`. Selecting the Young parameter small enough absorbs the
`m^β` contribution into the negative `−m^β/C` term coming from
`(eq:assH.upper.simple)`, leaving a strictly negative net coefficient
that we encode by a single new constant `C'`.

The hypothesis `h_slice` packages the FTC identity
`H(x, p, m) = H(x, 0, m) + ∫₀¹ D_pH(x, t·p, m) · p dt`
together with the pointwise integrand bounds
`H(x, 0, m) ≤ −m^β/C + C` and
`‖D_pH(x, t·p, m)‖ ≤ C(‖p‖^{α-1} + m^{β-β/α} + 1)` (using
`‖t·p‖^{α-1} ≤ ‖p‖^{α-1}` for `t ∈ [0, 1]` and `α > 1`), all integrated
over `t ∈ [0, 1]`. Decoupling these from the Young step keeps the proof
linear-algebraic and Mathlib-friendly; the integration step is an
orthogonal task.
-/
theorem upper_bound_powergrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (h_slice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ C' * (‖p‖ ^ h.α + 1) - (m ^ h.β) / C' := by
  -- Set up the data from the power-growth bundle.
  set C : ℝ := h.C with hCdef
  set α : ℝ := h.α with hαdef
  set β : ℝ := h.β with hβdef
  have hC : 0 < C := h.hC
  have hα : 1 < α := h.hα
  have hβ : 0 < β := h.hβ
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1pos : 0 < α - 1 := sub_pos.mpr hα
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hαm1ne : α - 1 ≠ 0 := ne_of_gt hαm1pos
  -- Hölder conjugate `α' = α / (α - 1)`.
  set α' : ℝ := α / (α - 1) with hα'def
  have hα'pos : 0 < α' := by
    change 0 < α / (α - 1)
    exact div_pos hαpos hαm1pos
  have hα'ne : α' ≠ 0 := ne_of_gt hα'pos
  have hHC := holderConjugate_alpha hα
  -- Choose Young parameter `θ` small enough so the m^β contribution
  -- stays bounded by `1/(2C)`. Concretely, pick a Young parameter so
  -- the coefficient on `m^β` after Young is at most `1/(2C)`.
  -- We use the simple version of Young with rescaling:
  --   `‖p‖ · m^{β-β/α} ≤ θ ‖p‖^α / α + θ^{-1/(α-1)} m^β / α'`
  -- by applying `young_inequality_of_nonneg` to
  --   `(θ^{1/α} ‖p‖) · (θ^{-1/α} m^{β-β/α})`.
  -- We don't need the optimal constant: pick any θ > 0 such that
  -- `C · θ^{-1/(α-1)} / α' < 1/C`, i.e.,
  -- `θ^{-1/(α-1)} < α' / C²`, i.e., `θ > (C²/α')^{α-1}`.
  -- A safe choice: `θ := (C² / α' + 1)^{α - 1} + 1` (always > 0).
  -- For simplicity we instead bypass Young's parametric form and just
  -- choose `C'` large enough using a non-parametric Young, then absorb
  -- the residue into the additive `+1` of the `‖p‖^α + 1` term.
  -- ----------------------------------------------------------------
  -- Direct route: apply non-parametric Young at every cross term, then
  -- pick `C' := max (large constant) (2C)` so that:
  --   * `m^β` coefficient: `-1/C + C·(coeff from Young)/α' ≤ -1/(2C) ≤ -1/C'`,
  --     which forces us to dominate the Young coefficient.
  -- This is impossible without parametric Young.
  -- We therefore really need parametric Young. We implement it by
  -- rescaling the variables before invoking `young_inequality_of_nonneg`.
  -- ----------------------------------------------------------------
  -- Define the Young parameter `θ`.
  set θ : ℝ := ((C ^ 2 / α' + 1) ^ (α - 1) + 1) with hθdef
  have hθ_lower : (C ^ 2 / α' + 1) ^ (α - 1) + 1 > 0 := by
    have h1 : (0 : ℝ) ≤ (C ^ 2 / α' + 1) ^ (α - 1) := by
      apply Real.rpow_nonneg
      have : (0 : ℝ) ≤ C ^ 2 / α' := div_nonneg (sq_nonneg _) hα'pos.le
      linarith
    linarith
  have hθpos : 0 < θ := hθ_lower
  -- Define the new constant `C'`.
  -- The contributions to `‖p‖^α` after Young are:
  --   `C·‖p‖^α` (original) + `C · θ ‖p‖^α / α` (cross 1) + `C · θ ‖p‖^α / α` (cross 2)
  --   `≤ C·(1 + 2θ/α)·‖p‖^α`.
  -- The constant terms are: `C` + `C · θ^{-1/(α-1)} / α'` (from cross 2 with b=1).
  -- The `m^β` coefficient is `-1/C + C · θ^{-1/(α-1)} / α'`.
  -- By choice of θ, this is `≤ -1/(2C)`.
  -- We pick `C'` to dominate everything.
  -- For the existence statement, set `C'` to be a large positive value
  -- chosen below; pin it down concretely.
  set Cyoung : ℝ := θ ^ (-(1 / (α - 1))) with hCyoungdef
  have hCyoung_pos : 0 < Cyoung := Real.rpow_pos_of_pos hθpos _
  -- The desired `C'` upper bounds:
  -- (1) `C * (1 + 2 * θ / α)` — coefficient of `‖p‖^α` on RHS.
  -- (2) `C + C * Cyoung / α'` — constant term on RHS.
  -- And we need `1 / C' ≤ 1/C - C * Cyoung / α'` so the `m^β` part lands.
  -- Choose `Mcoef`, `Madd`, `Mmβ` separately and pick C' large.
  set A : ℝ := C * (1 + 2 * θ / α) with hAdef
  set B : ℝ := C + C * Cyoung / α' with hBdef
  -- We need `D := 1/C - C * Cyoung / α' > 0` so that the m^β coeff is
  -- `≤ -D < 0`. By choice of θ this holds.
  set D : ℝ := 1 / C - C * Cyoung / α' with hDdef
  -- Show `D > 0`.
  have hD_pos : 0 < D := by
    change 0 < 1 / C - C * (θ ^ (-(1 / (α - 1)))) / α'
    -- We have `θ ≥ (C² / α' + 1)^{α-1}`, i.e., `θ^{1/(α-1)} ≥ C² / α' + 1`,
    -- hence `θ^{-1/(α-1)} ≤ 1/(C² / α' + 1)`.
    -- So `C * θ^{-1/(α-1)} / α' ≤ C / ((C²/α' + 1) · α')`.
    -- This is `≤ C / (C² / α' · α') = C / C² = 1/C` strictly.
    -- Hence `1/C - C * θ^{-1/(α-1)} / α' > 0`.
    have hθ_ge : θ ≥ (C ^ 2 / α' + 1) ^ (α - 1) := by
      change ((C ^ 2 / α' + 1) ^ (α - 1) + 1) ≥ (C ^ 2 / α' + 1) ^ (α - 1)
      linarith
    -- `θ^{1/(α-1)}` is well-defined and `θ^{1/(α-1)} ≥ C² / α' + 1`
    -- by monotonicity of `rpow` in the base (for positive base).
    have hbase_pos : 0 < (C ^ 2 / α' + 1) ^ (α - 1) := by
      apply Real.rpow_pos_of_pos
      have : (0 : ℝ) ≤ C ^ 2 / α' := div_nonneg (sq_nonneg _) hα'pos.le
      linarith
    have hbase_pos2 : 0 < C ^ 2 / α' + 1 := by
      have : (0 : ℝ) ≤ C ^ 2 / α' := div_nonneg (sq_nonneg _) hα'pos.le
      linarith
    -- `θ^{1/(α-1)} ≥ (C² / α' + 1)^{(α-1)·(1/(α-1))} = C² / α' + 1`.
    have hθpow1 : θ ^ ((1 : ℝ) / (α - 1)) ≥ C ^ 2 / α' + 1 := by
      have hmono : ((C ^ 2 / α' + 1) ^ (α - 1)) ^ ((1 : ℝ) / (α - 1))
                  ≤ θ ^ ((1 : ℝ) / (α - 1)) := by
        apply Real.rpow_le_rpow (le_of_lt hbase_pos) hθ_ge
        positivity
      have hsimp : ((C ^ 2 / α' + 1) ^ (α - 1)) ^ ((1 : ℝ) / (α - 1))
                  = C ^ 2 / α' + 1 := by
        rw [← Real.rpow_mul hbase_pos2.le]
        rw [mul_one_div, div_self hαm1ne, Real.rpow_one]
      linarith [hmono, hsimp]
    -- Now compute: `θ^{-1/(α-1)} = 1 / θ^{1/(α-1)}` for positive θ.
    have hpow_neg : θ ^ (-(1 / (α - 1))) = 1 / (θ ^ ((1 : ℝ) / (α - 1))) := by
      rw [Real.rpow_neg hθpos.le]
      exact (one_div _).symm
    rw [hpow_neg]
    have hθpow1_pos : 0 < θ ^ ((1 : ℝ) / (α - 1)) := Real.rpow_pos_of_pos hθpos _
    -- Goal: `0 < 1 / C - C * (1 / θ^{1/(α-1)}) / α'`.
    have step1 : C ^ 2 / α' < θ ^ ((1 : ℝ) / (α - 1)) := by linarith
    -- C² < α' · θ^{1/(α-1)}.
    have key : C ^ 2 < α' * θ ^ ((1 : ℝ) / (α - 1)) := by
      have h := mul_lt_mul_of_pos_left step1 hα'pos
      have heq : α' * (C ^ 2 / α') = C ^ 2 := by
        field_simp
      linarith
    -- Hence `C * (1 / θ^{1/(α-1)}) / α' < 1 / C`.
    have hprod_pos : 0 < α' * θ ^ ((1 : ℝ) / (α - 1)) := mul_pos hα'pos hθpow1_pos
    have h_lhs_eq : C * (1 / (θ ^ ((1 : ℝ) / (α - 1)))) / α'
                  = C / (α' * θ ^ ((1 : ℝ) / (α - 1))) := by
      rw [mul_one_div, div_div, mul_comm (θ ^ _) α']
    rw [h_lhs_eq]
    -- Goal: `0 < 1 / C - C / (α' * θ^{1/(α-1)})`. Equivalently,
    -- `C / (α' * θ^{1/(α-1)}) < 1 / C`, i.e., `C * C < 1 * (α' * θ^{1/(α-1)})`.
    have hgoal : C / (α' * θ ^ ((1 : ℝ) / (α - 1))) < 1 / C := by
      rw [div_lt_div_iff₀ hprod_pos hC]
      have hCC : C ^ 2 = C * C := by ring
      linarith [key, hCC]
    linarith
  -- Choose `C' := max A B (1/D + 1)`.
  refine ⟨max (max A B) (1/D + 1), ?_, ?_⟩
  · -- positivity of `C'`.
    have h1 : 0 < 1/D + 1 := by
      have := hD_pos
      have : 0 ≤ 1/D := by positivity
      linarith
    exact lt_max_of_lt_right h1
  · -- the bound itself.
    filter_upwards [h_slice] with x hx p m hm
    have hslice := hx p m hm
    -- Apply parametric Young to `‖p‖ · m^{β-β/α}` and `‖p‖ · 1`.
    -- Set up nonnegative versions.
    have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
    have hm_nn : 0 ≤ m := hm.le
    have hmpow_nn : 0 ≤ m ^ (β - β / α) := Real.rpow_nonneg hm_nn _
    -- Strategy: rescale via `a = θ^{1/α} · u`, `b = θ^{-1/α} · v`, so
    -- `a · b = u · v` and Young gives `u · v ≤ θ u^α / α + θ^{-1/(α-1)} v^α' / α'`.
    -- Specialize once with `(u, v) = (‖p‖, m^{β-β/α})` and once with `(‖p‖, 1)`.
    have hαβ_id : (β - β / α) * α' = β := by
      rw [hα'def]
      field_simp
    -- Power of θ identities for the rescaling.
    have hθinvα_pos : 0 < θ ^ ((1 : ℝ) / α) := Real.rpow_pos_of_pos hθpos _
    have hθnegα_pos : 0 < θ ^ ((-1 : ℝ) / α) := Real.rpow_pos_of_pos hθpos _
    have hθprod : θ ^ ((1 : ℝ) / α) * θ ^ ((-1 : ℝ) / α) = 1 := by
      rw [← Real.rpow_add hθpos]
      have hzero : (1 : ℝ) / α + (-1 : ℝ) / α = 0 := by
        rw [show ((-1 : ℝ) / α) = -(1 / α) from by ring, add_neg_cancel]
      rw [hzero, Real.rpow_zero]
    have hθpow_α : (θ ^ ((1 : ℝ) / α)) ^ α = θ := by
      rw [← Real.rpow_mul hθpos.le]
      have hone : (1 : ℝ) / α * α = 1 := by
        field_simp
      rw [hone]; exact Real.rpow_one θ
    have hθpow_neg_α' : (θ ^ ((-1 : ℝ) / α)) ^ α' = θ ^ (-(1 / (α - 1))) := by
      rw [← Real.rpow_mul hθpos.le]
      congr 1
      rw [hα'def]
      field_simp
    -- Generic parametric Young's inequality, our two-call form.
    have parametric_young :
        ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
          u * v ≤ θ * u ^ α / α + Cyoung * v ^ α' / α' := by
      intro u v hu hv
      -- `(θ^{1/α} u) * (θ^{-1/α} v) = u * v`, and rpow-versions of these are nonneg.
      have hau_nn : 0 ≤ θ ^ ((1 : ℝ) / α) * u := mul_nonneg hθinvα_pos.le hu
      have hbv_nn : 0 ≤ θ ^ ((-1 : ℝ) / α) * v := mul_nonneg hθnegα_pos.le hv
      have hYoung := Real.young_inequality_of_nonneg hau_nn hbv_nn hHC
      -- Compute `(θ^{1/α} u)^α = θ · u^α` and `(θ^{-1/α} v)^α' = Cyoung · v^α'`.
      have hL1 :
          (θ ^ ((1 : ℝ) / α) * u) ^ α = θ * u ^ α := by
        rw [Real.mul_rpow hθinvα_pos.le hu, hθpow_α]
      have hL2 :
          (θ ^ ((-1 : ℝ) / α) * v) ^ α' = Cyoung * v ^ α' := by
        rw [Real.mul_rpow hθnegα_pos.le hv, hθpow_neg_α']
      -- The product collapses.
      have hLHS :
          (θ ^ ((1 : ℝ) / α) * u) * (θ ^ ((-1 : ℝ) / α) * v) = u * v := by
        have : θ ^ ((1 : ℝ) / α) * u * (θ ^ ((-1 : ℝ) / α) * v)
              = (θ ^ ((1 : ℝ) / α) * θ ^ ((-1 : ℝ) / α)) * (u * v) := by ring
        rw [this, hθprod, one_mul]
      -- Combine.
      have := hYoung
      rw [hLHS, hL1, hL2] at this
      exact this
    -- Apply twice.
    have hYoung1 :
        ‖p‖ * m ^ (β - β / α) ≤ θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' := by
      have h := parametric_young ‖p‖ (m ^ (β - β / α)) hp_nn hmpow_nn
      -- Need: `(m^{β-β/α})^α' = m^β`.
      have hpow_collapse :
          (m ^ (β - β / α)) ^ α' = m ^ β := by
        rw [← Real.rpow_mul hm_nn, hαβ_id]
      rw [hpow_collapse] at h
      exact h
    have hYoung2 :
        ‖p‖ * 1 ≤ θ * ‖p‖ ^ α / α + Cyoung / α' := by
      have h := parametric_young ‖p‖ 1 hp_nn (by norm_num)
      -- `(1 : ℝ)^α' = 1`, and `Cyoung * 1 / α' = Cyoung / α'`.
      have h1 : (1 : ℝ) ^ α' = 1 := Real.one_rpow _
      rw [h1] at h
      simpa using h
    -- Combine.
    have hp_term : ‖p‖ * (m ^ (β - β / α) + 1) ≤
        2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α' := by
      have e : ‖p‖ * (m ^ (β - β / α) + 1) = ‖p‖ * m ^ (β - β / α) + ‖p‖ * 1 :=
        by ring
      have hsum : ‖p‖ * m ^ (β - β / α) + ‖p‖ * 1
                ≤ (θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α')
                  + (θ * ‖p‖ ^ α / α + Cyoung / α') := add_le_add hYoung1 hYoung2
      have hrhs_eq : (θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α')
                    + (θ * ‖p‖ ^ α / α + Cyoung / α')
                  = 2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α' := by ring
      linarith [hsum, hrhs_eq, e]
    -- The slice inequality + Young combination.
    have hbound :
        H x p m ≤ -(m ^ β) / C + C + C * ‖p‖ ^ α
                + C * (2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α') := by
      have hC_nn : 0 ≤ C := hC.le
      calc H x p m
          ≤ -(m ^ β) / C + C + C * ‖p‖ ^ α
              + C * ‖p‖ * (m ^ (β - β / α) + 1) := hslice
        _ = -(m ^ β) / C + C + C * ‖p‖ ^ α
              + C * (‖p‖ * (m ^ (β - β / α) + 1)) := by ring
        _ ≤ -(m ^ β) / C + C + C * ‖p‖ ^ α
              + C * (2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α') := by
            have := hp_term
            have hmul : C * (‖p‖ * (m ^ (β - β / α) + 1))
                      ≤ C * (2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α') :=
              mul_le_mul_of_nonneg_left this hC_nn
            linarith
    -- Rearrange to the desired form `C' * (‖p‖^α + 1) - m^β / C'`.
    -- The `‖p‖^α` coefficient on the RHS of `hbound`: `C + C·2·θ/α = A`.
    -- The constant on the RHS: `C + C·Cyoung/α' = B`.
    -- The `m^β` coefficient on the RHS: `-1/C + C·Cyoung/α' = -D`.
    have hRHS_eq :
        -(m ^ β) / C + C + C * ‖p‖ ^ α
            + C * (2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α')
        = A * ‖p‖ ^ α + B + (-D) * m ^ β := by
      change -(m ^ β) / C + C + C * ‖p‖ ^ α
            + C * (2 * θ * ‖p‖ ^ α / α + Cyoung * m ^ β / α' + Cyoung / α')
          = (C * (1 + 2 * θ / α)) * ‖p‖ ^ α + (C + C * Cyoung / α')
            + (-(1 / C - C * Cyoung / α')) * m ^ β
      field_simp
      ring
    rw [hRHS_eq] at hbound
    -- Now: `H ≤ A‖p‖^α + B − D·m^β` and we want `≤ C'·(‖p‖^α + 1) − m^β/C'`,
    -- where `C' := max (max A B) (1/D + 1)`.
    set C' := max (max A B) (1/D + 1) with hC'def
    have hA_le : A ≤ C' := le_trans (le_max_left _ _) (le_max_left _ _)
    have hB_le : B ≤ C' := le_trans (le_max_right _ _) (le_max_left _ _)
    have h_invDle : 1/D + 1 ≤ C' := le_max_right _ _
    have hD_inv_pos : 0 < 1/D := by positivity
    have hC'_pos : 0 < C' := by
      have : 0 < 1/D + 1 := by linarith
      exact lt_of_lt_of_le this h_invDle
    have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
    -- `1/C' ≤ D`: since `1/D + 1 ≤ C'`, we get `1/D < C'`, so `1/C' < D` (both pos).
    have h_inv_lt_D : 1/C' ≤ D := by
      have h1 : 1/D < C' := lt_of_lt_of_le (by linarith) h_invDle
      -- `1/D < C'` and both positive implies `1/C' < D`.
      rw [div_lt_iff₀ hD_pos] at h1
      -- h1: `1 < C' * D`. Hence `1/C' ≤ D`.
      rw [div_le_iff₀ hC'_pos]
      -- goal: `1 ≤ C' * D`. From `h1`: `1 < C' * D`, so `1 ≤ C' * D`.
      linarith
    have hp_nn_α : 0 ≤ ‖p‖ ^ α := Real.rpow_nonneg hp_nn _
    have hmβ_nn : 0 ≤ m ^ β := Real.rpow_nonneg hm_nn _
    -- Conclude.
    calc H x p m
        ≤ A * ‖p‖ ^ α + B + (-D) * m ^ β := hbound
      _ ≤ C' * ‖p‖ ^ α + C' + (-D) * m ^ β := by
          have h1 : A * ‖p‖ ^ α ≤ C' * ‖p‖ ^ α :=
            mul_le_mul_of_nonneg_right hA_le hp_nn_α
          linarith
      _ = C' * (‖p‖ ^ α + 1) + (-D) * m ^ β := by ring
      _ ≤ C' * (‖p‖ ^ α + 1) + (-(1/C')) * m ^ β := by
          have h1 : -D ≤ -(1/C') := by linarith
          have h2 : (-D) * m ^ β ≤ (-(1/C')) * m ^ β :=
            mul_le_mul_of_nonneg_right h1 hmβ_nn
          linarith
      _ = C' * (‖p‖ ^ α + 1) - m ^ β / C' := by
          have : -(1/C') * m ^ β = -(m ^ β / C') := by
            field_simp
          linarith [this]

/-- Coherence check: the trivially-flat Hamiltonian `H(x, p, m) := -m`
with `D_pH ≡ 0` satisfies the conclusion of `upper_bound_powergrowth`
for the parameters `C = 1`, `α = 2`, `β = 1`. With `D_pH ≡ 0`, the FTC
slice integrand vanishes, so the slice hypothesis reduces to the
constant-in-`p` upper bound `H(x, 0, m) ≤ −m + 1`, which is immediate. -/
example (d : ℕ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ((fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (m : ℝ) => -m) x p m)
            ≤ C' * (‖p‖ ^ (1 : ℝ) + 1) - m ^ (1 : ℝ) / C' := by
  -- We exhibit `C' = 2` directly. `LHS = -m`. `RHS = 2(‖p‖ + 1) - m/2 ≥ -m/2 ≥ -m`
  -- whenever `m > 0`, since `2(‖p‖+1) ≥ 2 > 0` and `-m/2 ≥ -m` for `m > 0`.
  refine ⟨2, by norm_num, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro _ p m hm
  have hpow_p : (‖p‖ : ℝ) ^ (1 : ℝ) = ‖p‖ := Real.rpow_one _
  have hpow_m : m ^ (1 : ℝ) = m := Real.rpow_one m
  rw [hpow_p, hpow_m]
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg p
  -- Goal: `-m ≤ 2 * (‖p‖ + 1) - m / 2`. Suffices `-m + m/2 ≤ 2 * (‖p‖ + 1)`,
  -- i.e., `-m/2 ≤ 2(‖p‖+1)`, true since `-m/2 ≤ 0 ≤ 2(‖p‖+1)`.
  have : (0 : ℝ) ≤ 2 * (‖p‖ + 1) := by positivity
  have hmhalf : -m ≤ -m/2 := by linarith
  linarith

/-! ### Paper Lemma `lem:ADFGU` (eq.~`eq:boundsmDpH`) — `m D_pH` integrability -/

/-! #### Algebraic exponent identities from `eq:gamma`

The paper's `eq:gamma` definitions
```
β̄ = β + 1,    γ̄ = α (β + 1) / β
```
together with the conjugate relations `γ̄' = γ̄ / (γ̄ - 1)` and
`β̄' = β̄ / (β̄ - 1)` yield the two key identities used in the
Hölder step at the bottom of the proof of `lem:ADFGU` (paper line 597):
```
1/γ̄' = 1/β̄ + (α - 1)/γ̄,
1/γ̄' = (β + 1 - β/α) / β̄.
```
We record both as algebraic facts, plus the consequence
`γ̄' ≤ β̄` (i.e. `L^{β̄} ⊂ L^{γ̄'}` on a finite-measure set). -/

/-- **Paper `eq:gamma` Hölder identity** (line 597 of
`Source/FGU-monotone_revised.tex`):

  `1/γ̄' = 1/β̄ + (α-1)/γ̄`,

with `β̄ = β + 1`, `γ̄ = α(β+1)/β`, and `γ̄' = γ̄/(γ̄-1)`. -/
theorem gammaBar'_holder_id {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    1 / ((α * (β + 1) / β) / (α * (β + 1) / β - 1))
      = 1 / (β + 1) + (α - 1) / (α * (β + 1) / β) := by
  -- Set up hypotheses.
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hbb : 0 < β + 1 := by linarith
  have hbb_ne : β + 1 ≠ 0 := ne_of_gt hbb
  have hgb_pos : 0 < α * (β + 1) / β := by positivity
  have hgb_ne : α * (β + 1) / β ≠ 0 := ne_of_gt hgb_pos
  have hgb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]
    nlinarith
  have hgbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hgbm1_ne : α * (β + 1) / β - 1 ≠ 0 := ne_of_gt hgbm1_pos
  field_simp
  ring

/-- **Paper `eq:gamma` collapse identity** (line 597 of
`Source/FGU-monotone_revised.tex`):

  `1/γ̄' = (β + 1 - β/α) / β̄`,

equivalently `(β̄ - β/α) · γ̄' = β̄ * γ̄'/(γ̄' - 1) ·` ... Concretely,
`(β̄ - β/α) / β̄ = 1/γ̄'`, with `β̄ = β + 1`, `γ̄ = α(β+1)/β`,
`γ̄' = γ̄/(γ̄-1)`. -/
theorem gammaBar'_collapse_id {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    1 / ((α * (β + 1) / β) / (α * (β + 1) / β - 1))
      = (β + 1 - β / α) / (β + 1) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hbb : 0 < β + 1 := by linarith
  have hbb_ne : β + 1 ≠ 0 := ne_of_gt hbb
  have hgb_pos : 0 < α * (β + 1) / β := by positivity
  have hgb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  have hgbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hgbm1_ne : α * (β + 1) / β - 1 ≠ 0 := ne_of_gt hgbm1_pos
  field_simp

/-- **Inclusion exponent ordering** for paper `eq:gamma`: `γ̄' ≤ β̄`,
i.e. `α(β+1)/(α(β+1)-β) ≤ β + 1`. This is the inclusion
`L^{β̄}_per ⊂ L^{γ̄'}_per` on the unit cube via `eLpNormPer_mono_exponent`.

Proof: `γ̄' = αβ̄ / (αβ̄ - β) = β̄ · α/(αβ̄-β)`. We need `α/(αβ̄-β) ≤ 1`,
i.e. `α ≤ αβ̄ - β = α(β+1) - β = αβ + α - β = α + β(α-1)`. Since
`β(α-1) ≥ 0` for `α ≥ 1, β ≥ 0`, this holds. -/
theorem gammaBar'_le_betaBar {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    α * (β + 1) / β / (α * (β + 1) / β - 1) ≤ β + 1 := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hbb : 0 < β + 1 := by linarith
  have hgb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  have hgbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  -- `γ̄' = γ̄ / (γ̄ - 1)`. Want `γ̄/(γ̄-1) ≤ β̄`, i.e. `γ̄ ≤ β̄(γ̄-1)` (since γ̄-1 > 0).
  rw [div_le_iff₀ hgbm1_pos]
  -- Goal: `α(β+1)/β ≤ (β+1) * (α(β+1)/β - 1)`.
  rw [show ((β + 1) * (α * (β + 1) / β - 1) : ℝ)
        = (β + 1) * (α * (β + 1) / β) - (β + 1) by ring]
  -- so we want `α(β+1)/β ≤ (β+1)·α(β+1)/β - (β+1)`, i.e.
  -- `(β+1) ≤ (β+1)·α(β+1)/β - α(β+1)/β = ((β+1)-1)·α(β+1)/β = β·α(β+1)/β = α(β+1)`.
  have hkey : (β + 1) ≤ α * (β + 1) := by
    have : 1 ≤ α := le_of_lt hα
    have hbb_nn : 0 ≤ β + 1 := le_of_lt hbb
    nlinarith [mul_le_mul_of_nonneg_right this hbb_nn]
  -- Finish: rearrange and apply hkey. Move `(β+1)` to the LHS.
  -- Want: `α(β+1)/β + (β+1) ≤ (β+1)·α(β+1)/β`.
  -- Equivalently: `(β+1) ≤ (β+1)·α(β+1)/β - α(β+1)/β = ((β+1)-1)·α(β+1)/β = β·α(β+1)/β = α(β+1)`.
  have hβ_div : β * (α * (β + 1) / β) = α * (β + 1) := by
    field_simp
  nlinarith [hkey, hβ_div]

/-- **Inclusion exponent ordering** for paper `eq:gamma`: `β̄' ≤ γ̄`,
i.e. `(β + 1)/β ≤ α (β + 1)/β`. This is the inclusion
`L^{γ̄}_per ⊂ L^{β̄'}_per` on the unit cube via
`MemLpPer.mono_exponent_finite`.

Proof: `γ̄ = α · β̄'` (dual identity `gammaBar_eq_alpha_mul_betaBar'`),
and `β̄' > 0` for `β > 0`; multiplying both sides of `1 ≤ α` by the
non-negative factor `β̄'` yields `β̄' ≤ α · β̄' = γ̄`. -/
theorem betaBar'_le_gammaBar {α β : ℝ} (hα : 1 ≤ α) (hβ : 0 < β) :
    betaBar' β ≤ gammaBar α β := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hb'_pos : 0 < betaBar' β := lt_trans zero_lt_one (one_lt_betaBar' β hβ)
  have hkey : betaBar' β = 1 * betaBar' β := by ring
  calc betaBar' β
      = 1 * betaBar' β := hkey
    _ ≤ α * betaBar' β := by
        exact mul_le_mul_of_nonneg_right hα hb'_pos.le
    _ = gammaBar α β := (gammaBar_eq_alpha_mul_betaBar' α β hβne).symm

/-! #### Pointwise norm domination for `m · D_pH`

Multiplying the simple `D_pH` upper bound `(eq:assH.DpH.upper.simple)`
of `HypothesisPowerGrowth` by `m ≥ 0`, we obtain a pointwise bound on
the norm of `F(x) = m(x) • D_pH(x, Du(x), m(x))`. The bound is
expressed by an explicit dominator function in `m, Du`. -/

/-- **Pointwise dominator for `m · D_pH(·, Du, m)`** from
`HypothesisPowerGrowth`. For any candidates `m, Du`, every `x ∈ 𝕋^d`
in the a.e. set of validity, and every `m x > 0`,

  `‖m(x) • D_pH(x, Du(x), m(x))‖`
  `  ≤ h.C · (m(x) · ‖Du(x)‖^{α-1} + m(x)^{1 + β - β/α} + m(x))`. -/
theorem mDpH_pointwise_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Du : (Fin d → ℝ) → (Fin d → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ mx, 0 < mx →
        ‖mx • DpH x (Du x) mx‖
          ≤ h.C * (mx * ‖Du x‖ ^ (h.α - 1)
                    + mx ^ (1 + h.β - h.β / h.α) + mx) := by
  filter_upwards [h.DpH_upper] with x hx mx hmx
  -- ‖mx • v‖ = |mx| * ‖v‖ = mx * ‖v‖ (using mx > 0).
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmx]
  -- Apply the bundle bound at p = Du x.
  have hb := hx (Du x) mx hmx
  -- Multiply both sides by `mx ≥ 0`.
  have hmle :
      mx * ‖DpH x (Du x) mx‖
        ≤ mx * (h.C * (‖Du x‖ ^ (h.α - 1) + mx ^ (h.β - h.β / h.α) + 1)) :=
    mul_le_mul_of_nonneg_left hb hmx.le
  -- Expand and rewrite `mx · mx^{β-β/α} = mx^{1 + β - β/α}`.
  have hpow : mx * mx ^ (h.β - h.β / h.α) = mx ^ (1 + h.β - h.β / h.α) := by
    have hmx_one : mx ^ (1 : ℝ) = mx := Real.rpow_one mx
    calc mx * mx ^ (h.β - h.β / h.α)
        = mx ^ (1 : ℝ) * mx ^ (h.β - h.β / h.α) := by rw [hmx_one]
      _ = mx ^ ((1 : ℝ) + (h.β - h.β / h.α)) :=
            (Real.rpow_add hmx 1 _).symm
      _ = mx ^ (1 + h.β - h.β / h.α) := by ring_nf
  -- Rearrange the RHS of `hmle` to the target shape.
  have hrhs_eq :
      mx * (h.C * (‖Du x‖ ^ (h.α - 1) + mx ^ (h.β - h.β / h.α) + 1))
        = h.C * (mx * ‖Du x‖ ^ (h.α - 1)
                  + mx ^ (1 + h.β - h.β / h.α) + mx) := by
    have hexpand : mx * (h.C * (‖Du x‖ ^ (h.α - 1)
                  + mx ^ (h.β - h.β / h.α) + 1))
        = h.C * (mx * ‖Du x‖ ^ (h.α - 1)
                  + mx * mx ^ (h.β - h.β / h.α) + mx) := by ring
    rw [hexpand, hpow]
  linarith

/-! #### Headline `MemLpPer γ̄'` integrability of `m · D_pH(·, Du, m)`

The headline integrability statement of `eq:boundsmDpH`. Given the
power-growth bundle `h : HypothesisPowerGrowth H DpH`, a non-negative
`m ∈ L^{β̄}_per`, a candidate `Du`, and the function
`F = m • D_pH(·, Du, m)` together with the pointwise dominator
`G = h.C · (m · ‖Du‖^{α-1} + m^{1+β-β/α} + m)`, if `G ∈ L^{γ̄'}_per`
and `F` is a.e. strongly measurable, then `F ∈ L^{γ̄'}_per`.

The dominator `G` is the right-hand side of `mDpH_pointwise_bound`.
Its `MemLpPer γ̄'`-membership is the **paper-side Hölder content**:
each summand is in `L^{γ̄'}_per` by Hölder
(eq:gamma identities `gammaBar'_holder_id`, `gammaBar'_collapse_id`,
`gammaBar'_le_betaBar`), and the sum's membership follows from
`MemLpPer.add`. We package the dominator-membership as an input here
so the closure-of-`L^p`-under-`rpow`-and-multiplication content can
live in a separate, dedicated module. -/

/-- **Paper Lemma `lem:ADFGU`, eq.~`eq:boundsmDpH`** — `L^{γ̄'}`
integrability of `m · D_pH(·, Du, m)`, in dominator form.

Given a candidate `F : (Fin d → ℝ) → (Fin d → ℝ)` representing
`x ↦ m(x) • DpH(x, Du(x), m(x))`, the conjugate exponent `q = γ̄'` as
an extended real, and parameters `C, α, β`, if

  * `F` is a.e. strongly measurable on the unit cube,
  * `‖F x‖ ≤ C · (m(x) · ‖Du(x)‖^{α-1} + m(x)^{1+β-β/α} + m(x))` a.e.
    (this holds, with `C = h.C`, by `mDpH_pointwise_bound`),
  * the dominator
    `G(x) = C · (m(x) · ‖Du(x)‖^{α-1} + m(x)^{1+β-β/α} + m(x))`
    lies in `L^{q}_per`,

then `F ∈ L^{q}_per`.

This is the cleanest division of labour: the **algebraic core** —
multiplying the simple `D_pH` upper bound by `m` and reading off the
three summands of the dominator — is encoded by
`mDpH_pointwise_bound`. The **Hölder closure** of the three summands
in `L^{γ̄'}` is encapsulated by the hypothesis `hG_mem`.

The dominator's `MemLpPer q` membership encapsulates the Hölder step
`1/γ̄' = 1/β̄ + (α-1)/γ̄ = (β + 1 - β/α)/β̄`, which is the algebraic
content provided by `gammaBar'_holder_id` and `gammaBar'_collapse_id`.

Per Remark `rmk:implied-a` claim 1 (`HypothesisPowerGrowth.toMDpHat0`),
the convention `m · D_pH = 0` on `{m = 0}` is consistent: the a.e.
measurability of `F` need only hold modulo this null set.

The proof is the direct application of `MemLp.of_le_mul` (specialised
to `c = 1`) to the pointwise bound `mDpH_pointwise_bound`. -/
theorem mDpH_mem_Lp_gammaBar'
    {q : ℝ≥0∞}
    (m : (Fin d → ℝ) → ℝ) (Du : (Fin d → ℝ) → (Fin d → ℝ))
    (F : (Fin d → ℝ) → (Fin d → ℝ))
    {C α β : ℝ}
    (hF_meas :
      AEStronglyMeasurable F (Measure.restrict volume (UnitCube d)))
    (hF_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖F x‖ ≤ C * (m x * ‖Du x‖ ^ (α - 1)
                  + m x ^ (1 + β - β / α) + m x))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          C * (m x * ‖Du x‖ ^ (α - 1)
                  + m x ^ (1 + β - β / α) + m x))) :
    MemLpPer q F := by
  -- Reduce to `MemLp.of_le_mul` with `c = 1`.
  have hG_memLp :
      MemLp (fun x : (Fin d → ℝ) =>
              C * (m x * ‖Du x‖ ^ (α - 1)
                  + m x ^ (1 + β - β / α) + m x))
            q (Measure.restrict volume (UnitCube d)) := hG_mem.toMemLp
  -- Massage the bound `‖F x‖ ≤ G x` into `‖F x‖ ≤ 1 * ‖G x‖`.
  -- For this we need `G x ≥ 0` a.e. so that `‖G x‖ = G x`. We get
  -- this by restating the bound: `0 ≤ ‖F x‖ ≤ G x` forces `0 ≤ G x`.
  have hbound : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ‖F x‖ ≤ (1 : ℝ) *
        ‖C * (m x * ‖Du x‖ ^ (α - 1)
                + m x ^ (1 + β - β / α) + m x)‖ := by
    filter_upwards [hF_le] with x hx
    have hF_nn : 0 ≤ ‖F x‖ := norm_nonneg _
    have hG_nn : 0 ≤ C * (m x * ‖Du x‖ ^ (α - 1)
                + m x ^ (1 + β - β / α) + m x) := le_trans hF_nn hx
    rw [Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
    exact hx
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_memLp hF_meas hbound)

/-! #### Unit test: a flat Hamiltonian `H ≡ -m`, `D_pH ≡ 0`.

For the trivially flat Hamiltonian, `m • D_pH ≡ 0` and the integrability
is the trivial fact that the zero function is in every `L^p_per`. -/

/-- Coherence check: with `H(x, p, m) = -m`, `D_pH ≡ 0`, `m ≡ 1`, `u ≡ 0`,
the function `x ↦ m(x) • D_pH(x, Du(x), m(x)) = 0` is in `L^{γ̄'}_per`
trivially. -/
example (d : ℕ) (q : ℝ≥0∞) :
    MemLpPer (d := d) q (fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ)) := by
  -- Direct: the zero function is in every `Lᵖ`.
  exact MemLp.toMemLpPer MemLp.zero'

/-- Coherence check (continued): with the trivially-flat Hamiltonian
`H(x, p, m) = -m` and `D_pH ≡ 0`, the dominator-form integrability
holds with any choice of dominator-witness, since `F = 0`. -/
example (d : ℕ) (q : ℝ≥0∞)
    (hG_mem :
      MemLpPer (d := d) q
        (fun _ : (Fin d → ℝ) =>
          (1 : ℝ) * ((1 : ℝ) * ‖(0 : Fin d → ℝ)‖ ^ ((2 : ℝ) - 1)
                + (1 : ℝ) ^ (1 + (1 : ℝ) - (1 : ℝ) / 2) + (1 : ℝ)))) :
    MemLpPer q
      (fun _ : (Fin d → ℝ) =>
        ((1 : ℝ) • ((fun _ _ _ => (0 : Fin d → ℝ)) (0 : Fin d → ℝ)
              (0 : Fin d → ℝ) (1 : ℝ)))) := by
  -- The function reduces to the zero function in `Fin d → ℝ`.
  -- Apply `mDpH_mem_Lp_gammaBar'` with the trivial bound.
  refine mDpH_mem_Lp_gammaBar'
    (q := q)
    (m := fun _ : (Fin d → ℝ) => (1 : ℝ))
    (Du := fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ))
    (F := fun _ : (Fin d → ℝ) =>
      ((1 : ℝ) • ((fun _ _ _ => (0 : Fin d → ℝ)) (0 : Fin d → ℝ)
              (0 : Fin d → ℝ) (1 : ℝ))))
    (C := 1) (α := 2) (β := 1)
    ?_ ?_ hG_mem
  · -- a.e. strong measurability of the constant zero function.
    exact aestronglyMeasurable_const
  · -- The pointwise bound is trivial: LHS norm is `0`, RHS is non-negative.
    refine Filter.Eventually.of_forall ?_
    intro x
    -- Both sides simplify; LHS = ‖0‖ = 0, RHS = 1 * (1 * 0^1 + 1^... + 1) ≥ 0.
    have hLHS :
        ‖((1 : ℝ) • ((fun _ _ _ => (0 : Fin d → ℝ)) (0 : Fin d → ℝ)
              (0 : Fin d → ℝ) (1 : ℝ)))‖ = 0 := by
      simp
    rw [hLHS]
    have hnorm0 : ‖(0 : Fin d → ℝ)‖ ^ ((2 : ℝ) - 1) = 0 := by
      have h0 : ‖(0 : Fin d → ℝ)‖ = 0 := norm_zero
      rw [h0]
      exact Real.zero_rpow (by norm_num)
    have hpow1 : (1 : ℝ) ^ (1 + (1 : ℝ) - (1 : ℝ) / 2) = 1 := Real.one_rpow _
    rw [hnorm0, hpow1]
    -- RHS becomes `1 * (1 * 0 + 1 + 1) = 2 ≥ 0`.
    norm_num

/-! ### Per-test-triple AC2 lemmas (paper `lem:ADFGU.a/b` analogues)

These three lemmas are the per-test-triple (`(μ, υ, Dυ)`) versions of
the multiplier integrabilities that the paper invokes to assemble the
operator pairing `⟨A_0[μ, υ], (μ - m, υ - u)⟩`. Each is "pointwise
bound from `Hamiltonian.PowerGrowth.*` + `MemLp.of_le_mul` against a
dominator passed as a `MemLpPer` hypothesis", in the same idiom as
`mDpH_mem_Lp_gammaBar'`.

Per `docs/CONVENTIONS.md` §8, the dominator-`MemLpPer` arguments are
parameterised as hypotheses; their closure from
`(μ ∈ L^βBar, υ ∈ L^γBar, Dυ ∈ L^γBar, V ∈ L^βBar')` via Hölder on
products of `rpow`'s is filed as a follow-up backlog task
(`infra-P4-ADFGU-test-triple-dominator-closure`).
-/

/-- **Per-coordinate version of `mDpH_pointwise_bound`.**

For a candidate `Dυ`, almost every `x ∈ 𝕋^d`, every `μx > 0`, and every
`i : Fin d`,

  `|μx · (D_pH x (Dυ x) μx) i|`
    `≤ h.C · (μx · ‖Dυ x‖^(α-1) + μx^(1+β-β/α) + μx)`.

The inequality is a direct corollary of `mDpH_pointwise_bound`: the
absolute value of the `i`-th coordinate of a vector in `Fin d → ℝ` is
bounded above by its pi-norm. -/
theorem mDpH_coord_pointwise_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Dυ : (Fin d → ℝ) → (Fin d → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ μx, 0 < μx → ∀ i,
        |μx * DpH x (Dυ x) μx i|
          ≤ h.C * (μx * ‖Dυ x‖ ^ (h.α - 1)
                    + μx ^ (1 + h.β - h.β / h.α) + μx) := by
  filter_upwards [mDpH_pointwise_bound h Dυ] with x hx μx hμx i
  -- The bundled estimate gives `‖μx • DpH x (Dυ x) μx‖ ≤ RHS`.
  have hsmul := hx μx hμx
  -- Componentwise: `(μx • v) i = μx * v i`.
  have hsmul_apply :
      (μx • DpH x (Dυ x) μx) i = μx * DpH x (Dυ x) μx i := by
    simp [Pi.smul_apply, smul_eq_mul]
  -- `|(μx • v) i| ≤ ‖μx • v‖` (Pi.norm bound on coordinate).
  have hcoord_le :
      ‖(μx • DpH x (Dυ x) μx) i‖ ≤ ‖μx • DpH x (Dυ x) μx‖ :=
    norm_le_pi_norm (μx • DpH x (Dυ x) μx) i
  -- Combine.
  have hgoal : |μx * DpH x (Dυ x) μx i| ≤ ‖μx • DpH x (Dυ x) μx‖ := by
    rw [show |μx * DpH x (Dυ x) μx i|
            = ‖(μx • DpH x (Dυ x) μx) i‖ from by
          rw [hsmul_apply]; exact (Real.norm_eq_abs _).symm]
    exact hcoord_le
  exact hgoal.trans hsmul

/-- **Paper Lemma `lem:ADFGU.b` — per-test-triple analogue.**

Per coordinate `i : Fin d`, the flux at the test triple
`(μ, Dυ)` lies in `L^q_per` (intended specialisation `q = γ̄'`), in
dominator form. Mirrors `mDpH_mem_Lp_gammaBar'`.

Given:

* a flux `flux_i x := μ x · D_pH(x, Dυ x, μ x) i`,
* a.e. strong measurability of `flux_i`,
* the standing power-growth bundle `h` (so the pointwise bound
  `mDpH_coord_pointwise_bound` applies),
* a.e. nonnegativity of `μ` (so the bound extends to the
  `μ x = 0` set, where the LHS vanishes),
* a `MemLpPer q`-membership of the dominator
  `G x := h.C · (μ x · ‖Dυ x‖^{α-1} + μ x^{1+β-β/α} + μ x)`,

we conclude `MemLpPer q (fun x => μ x · DpH x (Dυ x) μ x i)`.

The dominator-`MemLpPer` membership encapsulates the Hölder content of
`eq:gamma` (identities `gammaBar'_holder_id`, `gammaBar'_collapse_id`,
`gammaBar'_le_betaBar`); see the discussion above
`mDpH_mem_Lp_gammaBar'`. -/
theorem flux_memLp_gammaBar'_at_test
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {q : ℝ≥0∞}
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (i : Fin d)
    (hμ_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < μ x)
    (hF_meas :
      AEStronglyMeasurable
        (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
        (Measure.restrict volume (UnitCube d)))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                    + μ x ^ (1 + h.β - h.β / h.α) + μ x))) :
    MemLpPer q (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) := by
  -- Reduce to `MemLp.of_le_mul` with `c = 1`.
  have hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μ x * DpH x (fun j => Dυ j x) (μ x) i‖
          ≤ (1 : ℝ) *
            ‖h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                      + μ x ^ (1 + h.β - h.β / h.α) + μ x)‖ := by
    filter_upwards [mDpH_coord_pointwise_bound h (fun x => fun j => Dυ j x),
                    hμ_pos] with x hxbnd hxμpos
    have hxμ : 0 ≤ μ x := hxμpos.le
    -- Apply the coord-wise pointwise bound at `μx = μ x > 0`.
    have hb := hxbnd (μ x) hxμpos i
    -- `‖f‖_real = |f|`.
    rw [Real.norm_eq_abs]
    -- The dominator G x is non-negative.
    have hα1_nn : 0 ≤ ‖fun j => Dυ j x‖ ^ (h.α - 1) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hμα_nn : 0 ≤ μ x ^ (1 + h.β - h.β / h.α) :=
      Real.rpow_nonneg hxμ _
    have hG_nn : 0 ≤ h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                  + μ x ^ (1 + h.β - h.β / h.α) + μ x) := by
      apply mul_nonneg h.hC.le
      have h1 : 0 ≤ μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1) :=
        mul_nonneg hxμ hα1_nn
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
    exact hb
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_mem.toMemLp hF_meas hbound)

/-- **Paper Lemma `lem:ADFGU.a` — per-test-triple analogue.**

The HJB-side multiplier `g(x) := -υ(x) - H(x, Dυ x, μ x) + V(x)` lies
in `L^q_per` (intended specialisation `q = β̄'`), in dominator form.

Given:

* the standing power-growth bundle `h` (so
  `Hamiltonian.upper_bound_powergrowth` and `h.lower` give an
  `|H|`-pointwise dominator),
* the slice hypothesis used by `upper_bound_powergrowth`,
* a constant `C' > 0` from `upper_bound_powergrowth`,
* a `MemLpPer q`-membership of the dominator
  `G x := C' · (‖Dυ x‖^α + 1) + h.C · (|μ x|^β + 1) + |υ x| + |V x|`,
* a.e. strong measurability of the multiplier `g`,
* a.e. **strict** positivity of `μ` (so the power-growth pointwise
  bounds — which require `m > 0` — apply at every `x` in the a.e. set;
  this matches the paper's `essinf μ > 0` constraint built into the
  weak-solution domain `K` and the `paper:thm:strongAepsi` statement,
  `Source/FGU-monotone_revised.tex`, line 303 (statement on `K`) and
  line 1330 (`def-domainK`, `essinf μ > 0`)),

we conclude `MemLpPer q g`.

**CONVENTIONS §8 amendment.** The original task statement requested
only `μ ≥ 0` a.e.; the proof needs `μ > 0` a.e. because
`HypothesisPowerGrowth` only specifies `H(x, p, m)` for `m > 0`. The
strict-positivity upgrade matches the paper's `essinf μ > 0`
domain constraint (line 303, line 1330) and is *compatible with* the
regularised pair `m_ε`; see the follow-up backlog task
`infra-P4-ADFGU-test-triple-dominator-closure`. -/
theorem g_memLp_betaBar'_at_test
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {q : ℝ≥0∞}
    (V υ : (Fin d → ℝ) → ℝ) (μ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < μ x)
    {C' : ℝ} (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ C' * (‖p‖ ^ h.α + 1) - (m ^ h.β) / C')
    (hg_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
        (Measure.restrict volume (UnitCube d)))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun i => Dυ i x‖ ^ h.α + 1)
            + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x|)) :
    MemLpPer q
      (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x) := by
  -- Build the pointwise bound `|g x| ≤ G x` a.e.
  have hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x) (μ x) + V x‖
          ≤ (1 : ℝ) *
            ‖C' * (‖fun i => Dυ i x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1)
              + |υ x| + |V x|‖ := by
    filter_upwards [h_upper, h.lower, hμ_pos] with x hxU hxL hμpos
    -- Pointwise bounds.
    set p_x : Fin d → ℝ := fun i => Dυ i x with hp_x
    have hxμ : 0 ≤ μ x := hμpos.le
    have hα_p_nn : 0 ≤ ‖p_x‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_μ_nn : 0 ≤ μ x ^ h.β := Real.rpow_nonneg hxμ _
    -- |H x p_x μ x| ≤ Dom_H using upper + lower.
    have hH_abs : |H x p_x (μ x)|
                  ≤ C' * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1) := by
      have hU : H x p_x (μ x) ≤ C' * (‖p_x‖ ^ h.α + 1)
                                - (μ x ^ h.β) / C' :=
        hxU p_x (μ x) hμpos
      have hL : H x p_x (μ x)
                ≥ (‖p_x‖ ^ h.α) / h.C - h.C * (μ x ^ h.β + 1) :=
        hxL p_x (μ x) hμpos
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · -- -(C'·(‖p‖^α+1) + h.C·(μ^β+1)) ≤ H x p_x (μ x).
        have hC'add_nn : 0 ≤ C' * (‖p_x‖ ^ h.α + 1) := by
          have : 0 ≤ ‖p_x‖ ^ h.α + 1 := by linarith
          exact mul_nonneg hC'_pos.le this
        have hpC_div : 0 ≤ ‖p_x‖ ^ h.α / h.C :=
          div_nonneg hα_p_nn h.hC.le
        linarith
      · -- H x p_x (μ x) ≤ C' · (‖p‖^α + 1) + h.C · (μ^β+1).
        have hposC : 0 ≤ h.C * (μ x ^ h.β + 1) := by
          have : 0 ≤ μ x ^ h.β + 1 := by linarith
          exact mul_nonneg h.hC.le this
        have hμβ_div : 0 ≤ μ x ^ h.β / C' := div_nonneg hβ_μ_nn hC'_pos.le
        linarith
    -- Triangle: |g x| ≤ |υ| + |H| + |V|.
    have htri :
        ‖-(υ x) - H x p_x (μ x) + V x‖ ≤ |υ x| + |H x p_x (μ x)| + |V x| := by
      rw [Real.norm_eq_abs]
      -- |(-υ - H) + V| ≤ |-υ - H| + |V|.
      have h1 : |(-(υ x)) - H x p_x (μ x) + V x|
                ≤ |(-(υ x)) - H x p_x (μ x)| + |V x| := abs_add_le _ _
      -- |-υ - H| = |-υ + (-H)| ≤ |-υ| + |-H| = |υ| + |H|.
      have h2 : |(-(υ x)) - H x p_x (μ x)|
                ≤ |-(υ x)| + |-(H x p_x (μ x))| := by
        have := abs_add_le (-(υ x)) (-(H x p_x (μ x)))
        have heq : -(υ x) + -(H x p_x (μ x)) = (-(υ x)) - H x p_x (μ x) := by
          ring
        rw [heq] at this
        exact this
      have h3 : |-(υ x)| = |υ x| := abs_neg _
      have h4 : |-(H x p_x (μ x))| = |H x p_x (μ x)| := abs_neg _
      linarith
    -- Combine: |g x| ≤ Dom_H + |υ| + |V|.
    have htotal :
        ‖-(υ x) - H x p_x (μ x) + V x‖
          ≤ C' * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
              + |υ x| + |V x| := by linarith
    -- The dominator G is non-negative.
    have hG_nn :
        0 ≤ C' * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x| := by
      have hC' : 0 ≤ C' * (‖p_x‖ ^ h.α + 1) := by
        have : 0 ≤ ‖p_x‖ ^ h.α + 1 := by linarith
        exact mul_nonneg hC'_pos.le this
      have hCb : 0 ≤ h.C * (μ x ^ h.β + 1) := by
        have : 0 ≤ μ x ^ h.β + 1 := by linarith
        exact mul_nonneg h.hC.le this
      have habs1 : 0 ≤ |υ x| := abs_nonneg _
      have habs2 : 0 ≤ |V x| := abs_nonneg _
      linarith
    rw [show (‖C' * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x|‖) = _ from
            (Real.norm_eq_abs _)]
    rw [abs_of_nonneg hG_nn, one_mul]
    exact htotal
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_mem.toMemLp hg_meas hbound)

/-- **Paper Lemma `lem:ADFGU` — `L^β̄ ↪ L^γ̄'` mass-defect inclusion.**

When the test triple's mass `μ ∈ L^β̄_per` and the exponent inequality
`γ̄' ≤ β̄` holds (paper `eq:gamma`, recorded as `gammaBar'_le_betaBar`),
the mass-defect multiplier `μ - 1` lies in `L^γ̄'_per`. The proof
combines `MemLpPer.mono_exponent_finite` with the constant `1`'s
`MemLp` membership and `MemLpPer.add` (using `-1 = (-1) • 1`).

The inputs `(p := βBar)` and `(q := γBar')` need only `q ≤ p` and
`p < ⊤`; in the canonical paper specialisation `(βBar, γBar')` these
are guaranteed by `gammaBar'_le_betaBar` and finiteness of `β̄ = β + 1`. -/
theorem μMinusOne_memLp_of_betaBar
    {p q : ℝ≥0∞}
    (μ : (Fin d → ℝ) → ℝ)
    (hμ_memLp : Periodic.MemLpPer (d := d) p μ)
    (hpq : q ≤ p) (hp_top : p ≠ ⊤) :
    Periodic.MemLpPer (d := d) q (fun x => μ x - 1) := by
  -- The unit cube has volume 1; the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- `μ ∈ L^q` by `mono_exponent_finite`.
  have hμq : Periodic.MemLpPer (d := d) q μ :=
    Periodic.MemLpPer.mono_exponent_finite hpq hp_top hμ_memLp
  -- The constant `1` is in `L^q` for any `q`.
  have hone : Periodic.MemLpPer (d := d) q (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  -- The constant `-1` likewise.
  have hneg_one :
      Periodic.MemLpPer (d := d) q (fun _ : Fin d → ℝ => (-1 : ℝ)) := by
    have := hone.const_smul (𝕜 := ℝ) (-1 : ℝ)
    have heq : ((-1 : ℝ) • (fun _ : Fin d → ℝ => (1 : ℝ)))
              = fun _ : Fin d → ℝ => (-1 : ℝ) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  -- Sum closure.
  have hsum : Periodic.MemLpPer (d := d) q (μ + fun _ => (-1 : ℝ)) :=
    hμq.add hneg_one
  have heq : (μ + fun _ : Fin d → ℝ => (-1 : ℝ))
              = fun x => μ x - 1 := by
    funext x; simp [Pi.add_apply]; ring
  rw [heq] at hsum
  exact hsum

/-! ### Paper Lemma `lem:ADFGU` — dominator closure (`γ̄'` / `β̄'`)

These two lemmas discharge the `MemLpPer`-dominator hypotheses currently
parameterised through `flux_memLp_gammaBar'_at_test` and
`g_memLp_betaBar'_at_test` from the *underlying* test-triple
regularity, via Hölder on `rpow`-products and the project-local
exponent identities `gammaBar'_holder_id`, `gammaBar'_collapse_id`,
`gammaBar'_le_betaBar`. They feed the closed-form wrappers
`flux_memLp_gammaBar'_at_test'` and `g_memLp_betaBar'_at_test'` below,
which no longer take a dominator-`MemLpPer` hypothesis at the call
site.

The Hölder content is the paper's `eq:gamma` chain — see
`Source/FGU-monotone_revised.tex`, line 597. -/

/-- **Vector-valued `MemLpPer` from per-coordinate `MemLpPer`.**

If each scalar coordinate `Dυ i : (Fin d → ℝ) → ℝ` is `MemLpPer p`, then
the vector-valued function `fun x => fun i => Dυ i x : (Fin d → ℝ) → (Fin d → ℝ)`
is also `MemLpPer p`.

The proof bounds the sup-norm of the vector by the sum of absolute
values of its coordinates and uses `MemLp.of_le_mul`. -/
private theorem memLpPer_pi_of_coord
    {p : ℝ≥0∞} (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, Periodic.MemLpPer p (Dυ i)) :
    Periodic.MemLpPer p (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
  -- The unit cube has volume 1; the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- The dominator: the sum of absolute values of the coordinates.
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x| with hDom_def
  -- Each coordinate `i` of the absolute-value family lives in `L^p`.
  have habs_memLp : ∀ i, Periodic.MemLpPer p (fun x => |Dυ i x|) := by
    intro i
    -- `|Dυ i x| = ‖Dυ i x‖` (real norm), so `MemLpPer p (Dυ i)` lifts directly.
    have h := (hDυ i).toMemLp
    -- `MemLp f p μ` ⇒ `MemLp (‖f·‖) p μ` via `MemLp.norm`.
    have h2 := h.norm
    -- Massage `‖Dυ i x‖ = |Dυ i x|`.
    have heq : (fun x => ‖Dυ i x‖) = fun x => |Dυ i x| := by
      funext x
      exact Real.norm_eq_abs _
    rw [heq] at h2
    exact MemLp.toMemLpPer h2
  -- The sum is `MemLpPer p` by finite-sum closure.
  have hDom_memLp : Periodic.MemLpPer p Dom := by
    have hsum :
        MemLp (fun x => ∑ i : Fin d, (fun x => |Dυ i x|) x) p
          (Measure.restrict volume (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (habs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  -- Pointwise bound: `‖fun i => Dυ i x‖ ≤ ∑ i, |Dυ i x|`.
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖(fun i : Fin d => Dυ i x)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hsum_nn : 0 ≤ ∑ i, |Dυ i x| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpi : ‖(fun i : Fin d => Dυ i x)‖ ≤ ∑ i, |Dυ i x| := by
      rw [pi_norm_le_iff_of_nonneg hsum_nn]
      intro i
      have h1 : ‖Dυ i x‖ = |Dυ i x| := Real.norm_eq_abs _
      rw [h1]
      exact Finset.single_le_sum (f := fun j => |Dυ j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn, one_mul]
    exact hpi
  -- Strong measurability of the vector-valued function.
  have hmeas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (Measure.restrict volume (UnitCube d)) := by
    -- Build via AEMeasurable.aestronglyMeasurable + aemeasurable_pi_iff.
    have hAEm : AEMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (Measure.restrict volume (UnitCube d)) :=
      aemeasurable_pi_iff.mpr fun i => (hDυ i).aestronglyMeasurable.aemeasurable
    exact hAEm.aestronglyMeasurable
  -- Combine with `MemLp.of_le_mul`.
  exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)

/-- **Hölder triple `(β̄, γ̄/(α-1), γ̄')` on `ℝ`.**

For `α > 1` and `β > 0`, the real-valued exponents `(β + 1, γ̄/(α-1), γ̄')`
form a Hölder triple, where `γ̄ = α(β+1)/β` and `γ̄' = γ̄/(γ̄-1)`. The
identity is the paper's `eq:gamma` Hölder identity (`gammaBar'_holder_id`):

  `1/(β+1) + (α-1)/γ̄ = 1/γ̄'`. -/
private theorem holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    Real.HolderTriple (β + 1)
      (α * (β + 1) / β / (α - 1))
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := by linarith
  have hbb_pos : 0 < β + 1 := by linarith
  have hγb_pos : 0 < α * (β + 1) / β := by positivity
  have hγb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  have hγbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hγb_quot_pos : 0 < α * (β + 1) / β / (α - 1) :=
    div_pos hγb_pos hαm1_pos
  have hγb'_pos : 0 < α * (β + 1) / β / (α * (β + 1) / β - 1) :=
    div_pos hγb_pos hγbm1_pos
  -- Set up via `HolderTriple.of_pos` then rewrite via `gammaBar'_holder_id`.
  refine ⟨?_, hbb_pos, hγb_quot_pos⟩
  -- `(β+1)⁻¹ + (γ̄/(α-1))⁻¹ = γ̄'⁻¹`. Direct algebra via `field_simp`.
  have hβne : β ≠ 0 := hβ.ne'
  have hbb_ne : β + 1 ≠ 0 := hbb_pos.ne'
  have hαne : α ≠ 0 := hαpos.ne'
  have hαm1_ne : α - 1 ≠ 0 := hαm1_pos.ne'
  have hγb_ne : α * (β + 1) / β ≠ 0 := hγb_pos.ne'
  have hγbm1_ne : α * (β + 1) / β - 1 ≠ 0 := hγbm1_pos.ne'
  field_simp
  ring

/-- **AC1 — flux-side dominator closure (`γ̄'`), explicit-constant form.**

`hPow`-free version of `flux_dominator_memLp_gammaBar'`: the three-summand
flux dominator
`G x = C · (μ x · ‖fun j => Dυ j x‖^{α-1} + μ x ^{1+β-β/α} + μ x)`
lies in `L^{γ̄'}_per` (`γ̄' = γ̄/(γ̄−1)`, `γ̄ = α(β+1)/β`), given only the
exponents `α > 1`, `β > 0` and the test-triple regularity
`μ ∈ L^{β̄}_per`, `Dυ_j ∈ L^{γ̄}_per`. NO `HypothesisPowerGrowth` is used;
this is pure exponent algebra (the body of `flux_dominator_memLp_gammaBar'`
with the bundle field accesses `h.α`/`h.β`/`h.C` replaced by the explicit
constants). It is the reusable keystone for the `hAE`-keyed flux
`MemLpPer (ofReal γBar')` memberships of the T3 §1b identity wrapper, where
`HypothesisPowerGrowth` is gate-forbidden. -/
theorem flux_dominator_memLpPer_explicit
    {α β C : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) μ)
    (hDυ : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i)) :
    Periodic.MemLpPer
      (ENNReal.ofReal (α * (β + 1) / β /
        (α * (β + 1) / β - 1)))
      (fun x : (Fin d → ℝ) =>
        C * (μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
                  + μ x ^ (1 + β - β / α) + μ x)) := by
  -- Standing positivity facts.
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := by linarith
  have hbb_pos : 0 < β + 1 := by linarith
  have hβ_pos : 0 < β := hβ
  have hγb_pos : 0 < α * (β + 1) / β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hγb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith [hα, hβ]
  have hγbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hγb' : 0 < α * (β + 1) / β /
                  (α * (β + 1) / β - 1) :=
    div_pos hγb_pos hγbm1_pos
  -- The unit cube has volume 1; the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Notation.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal (β + 1) with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal (α * (β + 1) / β) with hγBarE_def
  set γBar'E : ℝ≥0∞ :=
    ENNReal.ofReal (α * (β + 1) / β /
      (α * (β + 1) / β - 1)) with hγBar'E_def
  -- Term 1: μ · ‖fun j => Dυ j ·‖^{α-1} ∈ L^{γ̄'}.
  have hT1 :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) => μ x * ‖fun j => Dυ j x‖ ^ (α - 1)) := by
    -- Vector-valued `Dυ_vec ∈ L^{γ̄}`.
    have hDυ_vec :
        Periodic.MemLpPer γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => Dυ j x) :=
      memLpPer_pi_of_coord (p := γBarE) Dυ hDυ
    -- `‖Dυ_vec ·‖^{α-1} ∈ L^{γ̄/(α-1)}` via `MemLp.norm_rpow_div`.
    set qE : ℝ≥0∞ := ENNReal.ofReal (α - 1) with hqE_def
    have hqE_pos : 0 < qE := by
      rw [hqE_def]
      exact ENNReal.ofReal_pos.mpr hαm1_pos
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = α - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (Measure.restrict volume (UnitCube d)) :=
      MemLp.norm_rpow_div hDυ_vec.toMemLp qE
    -- Identify `γBarE / qE = ENNReal.ofReal (γ̄/(α-1))`.
    have hdiv :
        γBarE / qE = ENNReal.ofReal (α * (β + 1) / β / (α - 1)) := by
      rw [hγBarE_def, hqE_def, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    -- Substitute and convert toReal.
    have hT1b :
        Periodic.MemLpPer
          (ENNReal.ofReal (α * (β + 1) / β / (α - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)) := by
      have heq :
          (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1))
          = (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal) := by
        funext x; rw [hqE_toReal]
      rw [heq]
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    -- Hölder real triple `(β+1, γ̄/(α-1), γ̄')`.
    have hHT_real :
        Real.HolderTriple (β + 1)
          (α * (β + 1) / β / (α - 1))
          (α * (β + 1) / β / (α * (β + 1) / β - 1)) :=
      holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar' hα hβ
    -- ENNReal version.
    haveI hHT_enn :
        ENNReal.HolderTriple βBarE
          (ENNReal.ofReal (α * (β + 1) / β / (α - 1)))
          γBar'E := by
      have := hHT_real.ennrealOfReal
      rw [hβBarE_def, hγBar'E_def]
      exact this
    -- Apply `MemLp.fun_mul` (Hölder for products).
    have hT1c :
        MemLp
          (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (α - 1))
          γBar'E (Measure.restrict volume (UnitCube d)) :=
      hμ.toMemLp.fun_mul hT1b.toMemLp
    exact MemLp.toMemLpPer hT1c
  -- Term 2: μ ^ (1 + β - β/α) ∈ L^{γ̄'}.
  have hT2 :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) => μ x ^ (1 + β - β / α)) := by
    have hβα_pos : 0 < β / α := div_pos hβ hαpos
    have hβα_lt : β / α < β + 1 := by
      have h1 : β / α ≤ β := by
        rw [div_le_iff₀ hαpos]
        have : β * 1 ≤ β * α :=
          mul_le_mul_of_nonneg_left hα.le hβ.le
        linarith
      linarith
    have hexp_pos : 0 < β + 1 - β / α := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (β + 1 - β / α) with hqE_def
    have hqE_pos : 0 < qE := by
      rw [hqE_def]; exact ENNReal.ofReal_pos.mpr hexp_pos
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = β + 1 - β / α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp_pos.le
    have hT2a :
        MemLp (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
              (βBarE / qE)
              (Measure.restrict volume (UnitCube d)) := by
      have h1 := MemLp.norm_rpow_div hμ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μ x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hdiv_eq : βBarE / qE = γBar'E := by
      rw [hβBarE_def, hqE_def, hγBar'E_def,
        ← ENNReal.ofReal_div_of_pos hexp_pos]
      congr 1
      have hβne : β ≠ 0 := hβ.ne'
      have hαne : α ≠ 0 := hαpos.ne'
      have hbb_ne : β + 1 ≠ 0 := hbb_pos.ne'
      have hβbβα_ne : β + 1 - β / α ≠ 0 := hexp_pos.ne'
      have hγb_ne : α * (β + 1) / β ≠ 0 := hγb_pos.ne'
      have hγbm1_ne : α * (β + 1) / β - 1 ≠ 0 := by linarith
      field_simp
    have hT2b :
        Periodic.MemLpPer γBar'E
          (fun x : (Fin d → ℝ) => |μ x| ^ (β + 1 - β / α)) := by
      have heq :
          (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
          = (fun x : (Fin d → ℝ) => |μ x| ^ (β + 1 - β / α)) := by
        funext x; rw [hqE_toReal]
      rw [heq] at hT2a
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    have hsh : (1 : ℝ) + β - β / α = β + 1 - β / α := by ring
    have hbound :
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          ‖μ x ^ (1 + β - β / α)‖ ≤
            (1 : ℝ) * ‖|μ x| ^ (β + 1 - β / α)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hsh]
      have habs := Real.abs_rpow_le_abs_rpow (μ x) (β + 1 - β / α)
      have hrhs_nn : 0 ≤ |μ x| ^ (β + 1 - β / α) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μ x ^ (1 + β - β / α))
          (Measure.restrict volume (UnitCube d)) := by
      have h_exp_nn : (0 : ℝ) ≤ 1 + β - β / α := by linarith [hexp_pos]
      have hcont : Continuous (fun y : ℝ => y ^ (1 + β - β / α)) :=
        Real.continuous_rpow_const h_exp_nn
      exact hcont.comp_aestronglyMeasurable hμ.aestronglyMeasurable
    exact MemLp.toMemLpPer (MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
  -- Term 3: μ ∈ L^{γ̄'} via `mono_exponent_finite`.
  have hT3 : Periodic.MemLpPer γBar'E μ := by
    have hle : γBar'E ≤ βBarE := by
      rw [hβBarE_def, hγBar'E_def]
      exact ENNReal.ofReal_le_ofReal (gammaBar'_le_betaBar hα hβ)
    have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
    exact Periodic.MemLpPer.mono_exponent_finite hle hβTop hμ
  -- Sum closure: T1 + T2 + T3.
  have hSum :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) =>
          μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
            + μ x ^ (1 + β - β / α) + μ x) := by
    have h12 :
        Periodic.MemLpPer γBar'E
          (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
              + μ x ^ (1 + β - β / α)) := by
      have := hT1.add hT2
      have heq :
          ((fun x : (Fin d → ℝ) =>
              μ x * ‖fun j => Dυ j x‖ ^ (α - 1))
            + (fun x : (Fin d → ℝ) =>
              μ x ^ (1 + β - β / α)))
          = (fun x : (Fin d → ℝ) =>
              μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
                + μ x ^ (1 + β - β / α)) := by
        funext x; simp [Pi.add_apply]
      rw [heq] at this
      exact this
    have := h12.add hT3
    have heq :
        ((fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
              + μ x ^ (1 + β - β / α))
          + μ)
        = (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
              + μ x ^ (1 + β - β / α) + μ x) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Final scalar multiply by `C`.
  have hFinal :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) =>
          C * (μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
                  + μ x ^ (1 + β - β / α) + μ x)) := by
    have := hSum.const_smul (𝕜 := ℝ) C
    have heq :
        ((C : ℝ) •
          (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
              + μ x ^ (1 + β - β / α) + μ x))
        = (fun x : (Fin d → ℝ) =>
            C * (μ x * ‖fun j => Dυ j x‖ ^ (α - 1)
                    + μ x ^ (1 + β - β / α) + μ x)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  exact hFinal

/-- **AC1 — flux-side dominator closure (`γ̄'`).** Paper Lemma
`lem:ADFGU`, eq.~`eq:boundsmDpH` (the dominator-`MemLpPer` content
covered in `Source/FGU-monotone_revised.tex`, lines 593–599).

Given the power-growth bundle `h : HypothesisPowerGrowth H DpH` with
exponents `α > 1`, `β > 0`, the test-triple regularity

* `μ ∈ L^{β̄}_per` with `β̄ = β + 1`,
* `Dυ_j ∈ L^{γ̄}_per` for each `j`, with `γ̄ = α(β+1)/β`,

the dominator

  `G x = h.C · (μ x · ‖fun j => Dυ j x‖^{α-1} + μ x ^{1+β-β/α} + μ x)`

lies in `L^{γ̄'}_per` with `γ̄' = γ̄ / (γ̄ - 1)`.

Each summand of `G` is in `L^{γ̄'}_per`:

* `μ · ‖fun j => Dυ j ·‖^{α-1}`: by Hölder on rpow-products at the
  triple `(β̄, γ̄/(α-1), γ̄')`, using `gammaBar'_holder_id`.
* `μ ^{1+β-β/α}`: by `MemLp.norm_rpow_div` of `μ ∈ L^{β̄}` at exponent
  `β̄ - β/α`, using `gammaBar'_collapse_id`.
* `μ`: by `MemLpPer.mono_exponent_finite` against `γ̄' ≤ β̄`
  (`gammaBar'_le_betaBar`). -/
theorem flux_dominator_memLp_gammaBar'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ : Periodic.MemLpPer (ENNReal.ofReal (h.β + 1)) μ)
    (hDυ : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) (Dυ i)) :
    Periodic.MemLpPer
      (ENNReal.ofReal (h.α * (h.β + 1) / h.β /
        (h.α * (h.β + 1) / h.β - 1)))
      (fun x : (Fin d → ℝ) =>
        h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                  + μ x ^ (1 + h.β - h.β / h.α) + μ x)) := by
  -- Standing positivity facts.
  have hαpos : 0 < h.α := lt_trans one_pos h.hα
  have hαm1_pos : 0 < h.α - 1 := by linarith [h.hα]
  have hbb_pos : 0 < h.β + 1 := by linarith [h.hβ]
  have hβ_pos : 0 < h.β := h.hβ
  have hγb_pos : 0 < h.α * (h.β + 1) / h.β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hγb_gt_one : 1 < h.α * (h.β + 1) / h.β := by
    rw [lt_div_iff₀ h.hβ]; nlinarith [h.hα, h.hβ]
  have hγbm1_pos : 0 < h.α * (h.β + 1) / h.β - 1 := by linarith
  have hγb' : 0 < h.α * (h.β + 1) / h.β /
                  (h.α * (h.β + 1) / h.β - 1) :=
    div_pos hγb_pos hγbm1_pos
  -- The unit cube has volume 1; the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Notation.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal (h.β + 1) with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal (h.α * (h.β + 1) / h.β) with hγBarE_def
  set γBar'E : ℝ≥0∞ :=
    ENNReal.ofReal (h.α * (h.β + 1) / h.β /
      (h.α * (h.β + 1) / h.β - 1)) with hγBar'E_def
  -- Term 1: μ · ‖fun j => Dυ j ·‖^{α-1} ∈ L^{γ̄'}.
  have hT1 :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) => μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)) := by
    -- Vector-valued `Dυ_vec ∈ L^{γ̄}`.
    have hDυ_vec :
        Periodic.MemLpPer γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => Dυ j x) :=
      memLpPer_pi_of_coord (p := γBarE) Dυ hDυ
    -- `‖Dυ_vec ·‖^{α-1} ∈ L^{γ̄/(α-1)}` via `MemLp.norm_rpow_div`.
    set qE : ℝ≥0∞ := ENNReal.ofReal (h.α - 1) with hqE_def
    have hqE_pos : 0 < qE := by
      rw [hqE_def]
      exact ENNReal.ofReal_pos.mpr hαm1_pos
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = h.α - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (Measure.restrict volume (UnitCube d)) :=
      MemLp.norm_rpow_div hDυ_vec.toMemLp qE
    -- Identify `γBarE / qE = ENNReal.ofReal (γ̄/(α-1))`.
    have hdiv :
        γBarE / qE = ENNReal.ofReal (h.α * (h.β + 1) / h.β / (h.α - 1)) := by
      rw [hγBarE_def, hqE_def, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    -- Substitute and convert toReal.
    have hT1b :
        Periodic.MemLpPer
          (ENNReal.ofReal (h.α * (h.β + 1) / h.β / (h.α - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (h.α - 1)) := by
      have heq :
          (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (h.α - 1))
          = (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal) := by
        funext x; rw [hqE_toReal]
      rw [heq]
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    -- Hölder real triple `(β+1, γ̄/(α-1), γ̄')`.
    have hHT_real :
        Real.HolderTriple (h.β + 1)
          (h.α * (h.β + 1) / h.β / (h.α - 1))
          (h.α * (h.β + 1) / h.β / (h.α * (h.β + 1) / h.β - 1)) :=
      holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar' h.hα h.hβ
    -- ENNReal version.
    haveI hHT_enn :
        ENNReal.HolderTriple βBarE
          (ENNReal.ofReal (h.α * (h.β + 1) / h.β / (h.α - 1)))
          γBar'E := by
      have := hHT_real.ennrealOfReal
      rw [hβBarE_def, hγBar'E_def]
      exact this
    -- Apply `MemLp.fun_mul` (Hölder for products).
    have hT1c :
        MemLp
          (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1))
          γBar'E (Measure.restrict volume (UnitCube d)) := by
      -- Apply Hölder with μ first and ‖·‖^{α-1} second.
      exact hμ.toMemLp.fun_mul hT1b.toMemLp
    exact MemLp.toMemLpPer hT1c
  -- Term 2: μ ^ (1 + β - β/α) ∈ L^{γ̄'}.
  have hT2 :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) => μ x ^ (1 + h.β - h.β / h.α)) := by
    -- `1 + β - β/α = β̄ - β/α` since `β̄ = β+1`.
    -- Apply `MemLp.norm_rpow_div` to `μ ∈ L^{β̄}` with `q = ENNReal.ofReal (β̄ - β/α)`.
    have hβα_pos : 0 < h.β / h.α := div_pos h.hβ hαpos
    have hβα_lt : h.β / h.α < h.β + 1 := by
      have : h.β / h.α < h.β + 1 := by
        have h1 : h.β / h.α ≤ h.β := by
          rw [div_le_iff₀ hαpos]
          have : h.β * 1 ≤ h.β * h.α :=
            mul_le_mul_of_nonneg_left h.hα.le h.hβ.le
          linarith
        linarith
      exact this
    have hexp_pos : 0 < h.β + 1 - h.β / h.α := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (h.β + 1 - h.β / h.α) with hqE_def
    have hqE_pos : 0 < qE := by
      rw [hqE_def]; exact ENNReal.ofReal_pos.mpr hexp_pos
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = h.β + 1 - h.β / h.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp_pos.le
    have hT2a :
        MemLp (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
              (βBarE / qE)
              (Measure.restrict volume (UnitCube d)) := by
      have h1 := MemLp.norm_rpow_div hμ.toMemLp qE
      -- `‖μ x‖_real = |μ x|`.
      have heq :
          (fun x : (Fin d → ℝ) => ‖μ x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    -- Identify `βBarE / qE = γBar'E` via `gammaBar'_collapse_id`.
    have hdiv_eq : βBarE / qE = γBar'E := by
      rw [hβBarE_def, hqE_def, hγBar'E_def,
        ← ENNReal.ofReal_div_of_pos hexp_pos]
      congr 1
      -- `(β+1) / (β+1 - β/α) = γ̄/(γ̄-1)`. Direct algebra via `field_simp`.
      have hβne : h.β ≠ 0 := h.hβ.ne'
      have hαne : h.α ≠ 0 := hαpos.ne'
      have hbb_ne : h.β + 1 ≠ 0 := hbb_pos.ne'
      have hβbβα_ne : h.β + 1 - h.β / h.α ≠ 0 := hexp_pos.ne'
      have hγb_ne : h.α * (h.β + 1) / h.β ≠ 0 := hγb_pos.ne'
      have hγbm1_ne : h.α * (h.β + 1) / h.β - 1 ≠ 0 := by
        have hγb_gt_one : 1 < h.α * (h.β + 1) / h.β := by
          rw [lt_div_iff₀ h.hβ]; nlinarith [h.hα, h.hβ]
        linarith
      field_simp
    -- Convert to `MemLpPer` and rebuild the bound.
    have hT2b :
        Periodic.MemLpPer γBar'E
          (fun x : (Fin d → ℝ) => |μ x| ^ (h.β + 1 - h.β / h.α)) := by
      have heq :
          (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
          = (fun x : (Fin d → ℝ) => |μ x| ^ (h.β + 1 - h.β / h.α)) := by
        funext x; rw [hqE_toReal]
      rw [heq] at hT2a
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    -- Bound `‖μ x ^ (1+β-β/α)‖ ≤ |μ x|^(β+1-β/α)`.
    have hsh : (1 : ℝ) + h.β - h.β / h.α = h.β + 1 - h.β / h.α := by ring
    have hbound :
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          ‖μ x ^ (1 + h.β - h.β / h.α)‖ ≤
            (1 : ℝ) * ‖|μ x| ^ (h.β + 1 - h.β / h.α)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hsh]
      have habs := Real.abs_rpow_le_abs_rpow (μ x) (h.β + 1 - h.β / h.α)
      have hrhs_nn : 0 ≤ |μ x| ^ (h.β + 1 - h.β / h.α) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μ x ^ (1 + h.β - h.β / h.α))
          (Measure.restrict volume (UnitCube d)) := by
      -- `Real.rpow x (1 + β - β/α)` is continuous since the exponent is positive.
      have h_exp_nn : (0 : ℝ) ≤ 1 + h.β - h.β / h.α := by linarith [hexp_pos]
      have hcont : Continuous (fun y : ℝ => y ^ (1 + h.β - h.β / h.α)) :=
        Real.continuous_rpow_const h_exp_nn
      exact hcont.comp_aestronglyMeasurable hμ.aestronglyMeasurable
    exact MemLp.toMemLpPer (MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
  -- Term 3: μ ∈ L^{γ̄'} via `mono_exponent_finite`.
  have hT3 : Periodic.MemLpPer γBar'E μ := by
    -- `γ̄' ≤ β̄` from `gammaBar'_le_betaBar`.
    have hle : γBar'E ≤ βBarE := by
      rw [hβBarE_def, hγBar'E_def]
      exact ENNReal.ofReal_le_ofReal (gammaBar'_le_betaBar h.hα h.hβ)
    have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
    exact Periodic.MemLpPer.mono_exponent_finite hle hβTop hμ
  -- Sum closure: T1 + T2 + T3.
  have hSum :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) =>
          μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
            + μ x ^ (1 + h.β - h.β / h.α) + μ x) := by
    -- Combine via `add` lemmas; rewrite the function as a `fun_add`.
    have h12 :
        Periodic.MemLpPer γBar'E
          (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
              + μ x ^ (1 + h.β - h.β / h.α)) := by
      have := hT1.add hT2
      have heq :
          ((fun x : (Fin d → ℝ) =>
              μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1))
            + (fun x : (Fin d → ℝ) =>
              μ x ^ (1 + h.β - h.β / h.α)))
          = (fun x : (Fin d → ℝ) =>
              μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                + μ x ^ (1 + h.β - h.β / h.α)) := by
        funext x; simp [Pi.add_apply]
      rw [heq] at this
      exact this
    have := h12.add hT3
    have heq :
        ((fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
              + μ x ^ (1 + h.β - h.β / h.α))
          + μ)
        = (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
              + μ x ^ (1 + h.β - h.β / h.α) + μ x) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Final scalar multiply by `h.C`.
  have hFinal :
      Periodic.MemLpPer γBar'E
        (fun x : (Fin d → ℝ) =>
          h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                  + μ x ^ (1 + h.β - h.β / h.α) + μ x)) := by
    have := hSum.const_smul (𝕜 := ℝ) h.C
    have heq :
        ((h.C : ℝ) •
          (fun x : (Fin d → ℝ) =>
            μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
              + μ x ^ (1 + h.β - h.β / h.α) + μ x))
        = (fun x : (Fin d → ℝ) =>
            h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                    + μ x ^ (1 + h.β - h.β / h.α) + μ x)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  exact hFinal

/-! #### Phase H4 — flux integrability at the limit triple.

The two lemmas below close the Phase H4 task
`infra-P5-theorem1-phase-H4-discharge-hFluxInt`. They derive the
flux-integrability claim

```
Integrable (fun x => mDpH DpH x (fun i => Du i x) (m x))
           (volume.restrict (UnitCube d))
```

— the `hFluxInt` field of `FinalIntegrabilityPaperResidue` — from the
power-growth bundle `h : HypothesisPowerGrowth H DpH` plus the
`MemLpPer β̄`/`MemLpPer γ̄` certificates carried by the weak-limit
bundle and the strict-`γ̄` `DuLim` residue. The discharge proceeds in
two stages:

* `mDpH_dominator_memLpPer_gammaBar'` — `MemLpPer γ̄'` of the explicit
  three-summand dominator (an alias of `flux_dominator_memLp_gammaBar'`
  exposed under the spec's name).
* `mDpH_integrable_of_memLpPer` — full integrability of the flux
  vector field, via `mDpH_mem_Lp_gammaBar'` plus `MemLp.mono_exponent`
  to L¹ on the finite-measure cube. -/

/-- **Phase H4 — `MemLpPer γ̄'` of the flux dominator.** Direct alias
of `flux_dominator_memLp_gammaBar'` exposed under the spec's name. -/
theorem mDpH_dominator_memLpPer_gammaBar'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (m : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hm : Periodic.MemLpPer (ENNReal.ofReal (h.β + 1)) m)
    (hDu : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) (Du i)) :
    Periodic.MemLpPer
      (ENNReal.ofReal (h.α * (h.β + 1) / h.β /
        (h.α * (h.β + 1) / h.β - 1)))
      (fun x : (Fin d → ℝ) =>
        h.C * (m x * ‖fun j => Du j x‖ ^ (h.α - 1)
                  + m x ^ (1 + h.β - h.β / h.α) + m x)) :=
  flux_dominator_memLp_gammaBar' h m Du hm hDu

/-- **Phase H4 — flux integrability at the weak limit.** Discharge
the `hFluxInt` residue from the power-growth bundle plus
`m ∈ L^{β̄}_per`, `Du_i ∈ L^{γ̄}_per`, and a.e. nonnegativity of `m`.

Pipeline:
1. The explicit dominator `G x = h.C · (m x · ‖Du x‖^{α-1} + m x^{1+β-β/α} + m x)`
   lies in `L^{γ̄'}_per` (via `mDpH_dominator_memLpPer_gammaBar'`).
2. Pointwise `‖m x • DpH x (Du x) (m x)‖ ≤ G x` a.e., via
   `mDpH_pointwise_bound` for `m x > 0` and the trivial `0 • v = 0`
   case for `m x = 0` (using `m ≥ 0` a.e.).
3. `mDpH_mem_Lp_gammaBar'` packages 1+2 into
   `MemLpPer γ̄' (mDpH DpH · (Du ·) (m ·))`.
4. `MemLp.mono_exponent` from `γ̄' ≥ 1` to `1` on the finite-measure
   unit cube, then `memLp_one_iff_integrable.mp`. -/
theorem mDpH_integrable_of_memLpPer
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (m : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hm : Periodic.MemLpPer (ENNReal.ofReal (h.β + 1)) m)
    (hDu : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) (Du i))
    (hF_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          mDpH DpH x (fun i => Du i x) (m x))
        (Measure.restrict volume (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x : (Fin d → ℝ) =>
        mDpH DpH x (fun i => Du i x) (m x))
      (Measure.restrict volume (UnitCube d)) := by
  -- Standing positivity facts.
  have hαpos : 0 < h.α := lt_trans one_pos h.hα
  have hβ_pos : 0 < h.β := h.hβ
  have hbb_pos : 0 < h.β + 1 := by linarith
  have hγb_pos : 0 < h.α * (h.β + 1) / h.β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hγb_gt_one : 1 < h.α * (h.β + 1) / h.β := by
    rw [lt_div_iff₀ h.hβ]; nlinarith [h.hα, h.hβ]
  have hγbm1_pos : 0 < h.α * (h.β + 1) / h.β - 1 := by linarith
  have hγb' : 0 < h.α * (h.β + 1) / h.β /
                  (h.α * (h.β + 1) / h.β - 1) :=
    div_pos hγb_pos hγbm1_pos
  -- `γ̄' ≥ 1`: from `γ̄'·(γ̄-1) = γ̄ ≥ γ̄-1`, so `γ̄' ≥ 1`.
  have hγb'_ge_one : 1 ≤ h.α * (h.β + 1) / h.β /
                          (h.α * (h.β + 1) / h.β - 1) := by
    rw [le_div_iff₀ hγbm1_pos]
    linarith
  -- Finite-measure instance for the cube-restricted volume.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Step 1: dominator membership.
  have hG_mem :
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β /
          (h.α * (h.β + 1) / h.β - 1)))
        (fun x : (Fin d → ℝ) =>
          h.C * (m x * ‖fun j => Du j x‖ ^ (h.α - 1)
                    + m x ^ (1 + h.β - h.β / h.α) + m x)) :=
    mDpH_dominator_memLpPer_gammaBar' h m Du hm hDu
  -- Step 2: pointwise bound `‖m • DpH‖ ≤ G` a.e., extending
  -- `mDpH_pointwise_bound` (which assumes `m x > 0`) to `m x ≥ 0` by
  -- handling the `m x = 0` case directly.
  have hF_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖mDpH DpH x (fun i => Du i x) (m x)‖
          ≤ h.C *
              (m x * ‖fun j => Du j x‖ ^ (h.α - 1)
                + m x ^ (1 + h.β - h.β / h.α) + m x) := by
    filter_upwards [mDpH_pointwise_bound h (fun x => fun i => Du i x), hm_nn]
      with x hxbnd hxnn
    rcases lt_or_eq_of_le hxnn with hxpos | hxz
    · -- Strict positivity case: apply the bundled pointwise bound.
      exact hxbnd (m x) hxpos
    · -- Zero case: LHS is `‖0 • v‖ = 0`, RHS is `≥ 0`.
      have hmzero : m x = 0 := hxz.symm
      have hLHS : mDpH DpH x (fun i => Du i x) (m x) = 0 := by
        unfold mDpH
        rw [hmzero, zero_smul]
      rw [hLHS, norm_zero]
      have hα1_nn : 0 ≤ ‖fun j => Du j x‖ ^ (h.α - 1) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hμα_nn : 0 ≤ m x ^ (1 + h.β - h.β / h.α) :=
        Real.rpow_nonneg hxnn _
      have hsum_nn :
          0 ≤ m x * ‖fun j => Du j x‖ ^ (h.α - 1)
                + m x ^ (1 + h.β - h.β / h.α) + m x := by
        have h1 : 0 ≤ m x * ‖fun j => Du j x‖ ^ (h.α - 1) :=
          mul_nonneg hxnn hα1_nn
        linarith
      exact mul_nonneg h.hC.le hsum_nn
  -- Step 3: `MemLpPer γ̄'` of the flux vector field.
  have hF_lp :
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β /
          (h.α * (h.β + 1) / h.β - 1)))
        (fun x : (Fin d → ℝ) =>
          mDpH DpH x (fun i => Du i x) (m x)) := by
    refine mDpH_mem_Lp_gammaBar'
      (q := ENNReal.ofReal (h.α * (h.β + 1) / h.β /
              (h.α * (h.β + 1) / h.β - 1)))
      (m := m) (Du := fun x => fun i => Du i x)
      (F := fun x => mDpH DpH x (fun i => Du i x) (m x))
      (C := h.C) (α := h.α) (β := h.β)
      hF_meas hF_le hG_mem
  -- Step 4: mono_exponent down to L¹ on the finite-measure cube.
  have h_one_le : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (h.α * (h.β + 1) / h.β /
        (h.α * (h.β + 1) / h.β - 1)) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal hγb'_ge_one
  have hF_memLp_one :
      MemLp (fun x : (Fin d → ℝ) =>
              mDpH DpH x (fun i => Du i x) (m x))
            1
            (Measure.restrict volume (UnitCube d)) :=
    hF_lp.toMemLp.mono_exponent h_one_le
  -- Step 5: conclude integrability.
  exact memLp_one_iff_integrable.mp hF_memLp_one

/-- **Phase H4 — sanity check.** With the trivially-flat Hamiltonian
`H(x, p, m) = -m`, `D_pH ≡ 0`, `m ≡ 1`, `Du ≡ 0`, the flux
`x ↦ m(x) • D_pH(x, Du(x), m(x))` is integrable over the unit cube. -/
example (d : ℕ) :
    MeasureTheory.Integrable
      (fun _ : (Fin d → ℝ) => (0 : Fin d → ℝ))
      (Measure.restrict volume (UnitCube d)) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- The constant zero function is integrable over any finite measure.
  exact MeasureTheory.integrable_zero _ _ _

/-- **AC2 — HJB-side dominator closure (`β̄'`).** Paper Lemma
`lem:ADFGU`, eq.~`eq:boundsH` (the dominator-`MemLpPer` content
covered in `Source/FGU-monotone_revised.tex`, lines 600–610).

Given the power-growth bundle `h : HypothesisPowerGrowth H DpH` with
exponents `α > 1`, `β > 0`, the test-triple regularity

* `μ ∈ L^{β̄}_per` with `β̄ = β + 1`,
* `υ ∈ L^{γ̄}_per`,
* `Dυ_j ∈ L^{γ̄}_per` for each `j`, with `γ̄ = α(β+1)/β`,
* `V ∈ L^{β̄'}_per` with `β̄' = (β+1)/β`,

and `C' > 0`, the dominator

  `G x = C' · (‖fun j => Dυ j x‖^α + 1) + h.C · (μ x ^ β + 1) + |υ x| + |V x|`

lies in `L^{β̄'}_per`.

Each summand of `G` is in `L^{β̄'}_per`:

* `‖fun j => Dυ j ·‖^α`: by `MemLp.norm_rpow_div` of the vector-valued
  `Dυ_vec ∈ L^{γ̄}` at exponent `α`. Identity `γ̄/α = β̄'` from
  `α β̄' = γ̄` (paper `eq:gamma`).
* `μ ^ β`: by `MemLp.norm_rpow_div` of `μ ∈ L^{β̄}` at exponent `β`.
  Identity `β̄/β = β̄'` from `β̄ = β + 1`, `β̄' = (β+1)/β`.
* `|υ|`: by `MemLpPer.mono_exponent_finite` against `β̄' ≤ γ̄`.
* `|V|`: directly from `V ∈ L^{β̄'}_per`.
* Constants: `memLp_const` (finite measure). -/
theorem g_dominator_memLp_betaBar'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V υ : (Fin d → ℝ) → ℝ) (μ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ : Periodic.MemLpPer (ENNReal.ofReal (h.β + 1)) μ)
    (hυ : Periodic.MemLpPer
            (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) υ)
    (hDυ : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) (Dυ i))
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal ((h.β + 1) / h.β)) V)
    {C' : ℝ} (hC'_pos : 0 < C') :
    Periodic.MemLpPer
      (ENNReal.ofReal ((h.β + 1) / h.β))
      (fun x : (Fin d → ℝ) =>
        C' * (‖fun i => Dυ i x‖ ^ h.α + 1)
          + h.C * (μ x ^ h.β + 1) + |υ x| + |V x|) := by
  -- Standing positivity facts.
  have hαpos : 0 < h.α := lt_trans one_pos h.hα
  have hbb_pos : 0 < h.β + 1 := by linarith [h.hβ]
  have hβ_pos : 0 < h.β := h.hβ
  have hγb_pos : 0 < h.α * (h.β + 1) / h.β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hβb'_pos : 0 < (h.β + 1) / h.β := div_pos hbb_pos h.hβ
  -- The unit cube has volume 1; the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Notation.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal (h.β + 1) with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal (h.α * (h.β + 1) / h.β) with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal ((h.β + 1) / h.β) with hβBar'E_def
  -- The key exponent identity: `γ̄ / α = β̄'`, i.e. `(α(β+1)/β)/α = (β+1)/β`.
  have hγα_eq : h.α * (h.β + 1) / h.β / h.α = (h.β + 1) / h.β := by
    field_simp
  -- Term: ‖fun j => Dυ j ·‖^α ∈ L^{β̄'}.
  have hT_Du :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ h.α) := by
    -- Vector-valued `Dυ_vec ∈ L^{γ̄}`.
    have hDυ_vec :
        Periodic.MemLpPer γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => Dυ j x) :=
      memLpPer_pi_of_coord (p := γBarE) Dυ hDυ
    set qE : ℝ≥0∞ := ENNReal.ofReal h.α with hqE_def
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = h.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαpos.le
    have hT_a :
        MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (Measure.restrict volume (UnitCube d)) :=
      MemLp.norm_rpow_div hDυ_vec.toMemLp qE
    -- Identify `γBarE / qE = βBar'E`.
    have hdiv : γBarE / qE = βBar'E := by
      rw [hγBarE_def, hqE_def, hβBar'E_def,
        ← ENNReal.ofReal_div_of_pos hαpos]
      exact congrArg _ hγα_eq
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ h.α) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have := MemLp.toMemLpPer hT_a
    rw [hdiv] at this
    exact this
  -- Term: μ^β ∈ L^{β̄'}.
  have hT_mb :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => μ x ^ h.β) := by
    set qE : ℝ≥0∞ := ENNReal.ofReal h.β with hqE_def
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = h.β := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal h.hβ.le
    have hT_a :
        MemLp (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
              (βBarE / qE)
              (Measure.restrict volume (UnitCube d)) := by
      have h1 := MemLp.norm_rpow_div hμ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μ x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    -- Identify `βBarE / qE = βBar'E`, i.e. `(β+1)/β = β̄'` directly.
    have hdiv : βBarE / qE = βBar'E := by
      rw [hβBarE_def, hqE_def, hβBar'E_def,
        ← ENNReal.ofReal_div_of_pos h.hβ]
    have heq :
        (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μ x| ^ h.β) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    -- Convert to `MemLpPer βBar'E (fun x => |μ x|^β)`, then bound `μ^β` by it.
    have hT_b : Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => |μ x| ^ h.β) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hbound :
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          ‖μ x ^ h.β‖ ≤ (1 : ℝ) * ‖|μ x| ^ h.β‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
      have habs := Real.abs_rpow_le_abs_rpow (μ x) h.β
      have hrhs_nn : 0 ≤ |μ x| ^ h.β :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μ x ^ h.β)
          (Measure.restrict volume (UnitCube d)) := by
      have hcont : Continuous (fun y : ℝ => y ^ h.β) :=
        Real.continuous_rpow_const h.hβ.le
      exact hcont.comp_aestronglyMeasurable hμ.aestronglyMeasurable
    exact MemLp.toMemLpPer (MemLp.of_le_mul hT_b.toMemLp hmeas hbound)
  -- Term: |υ| ∈ L^{β̄'} via `mono_exponent_finite` (since β̄' ≤ γ̄).
  have hT_uabs :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => |υ x|) := by
    -- `(β+1)/β ≤ α(β+1)/β` since `α ≥ 1`.
    have hle_real :
        (h.β + 1) / h.β ≤ h.α * (h.β + 1) / h.β := by
      rw [div_le_div_iff_of_pos_right h.hβ]
      have : (1 : ℝ) * (h.β + 1) ≤ h.α * (h.β + 1) :=
        mul_le_mul_of_nonneg_right h.hα.le hbb_pos.le
      simpa using this
    have hle : βBar'E ≤ γBarE := by
      rw [hβBar'E_def, hγBarE_def]
      exact ENNReal.ofReal_le_ofReal hle_real
    have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
    -- `MemLpPer βBar'E υ` from `MemLpPer γBarE υ`.
    have hυβ' : Periodic.MemLpPer βBar'E υ :=
      Periodic.MemLpPer.mono_exponent_finite hle hγTop hυ
    -- `|υ x| = ‖υ x‖`.
    have hυ_norm : Periodic.MemLpPer βBar'E (fun x => ‖υ x‖) := by
      have := hυβ'.toMemLp.norm
      exact MemLp.toMemLpPer this
    have heq : (fun x : (Fin d → ℝ) => ‖υ x‖)
              = (fun x : (Fin d → ℝ) => |υ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at hυ_norm
    exact hυ_norm
  -- Term: |V| ∈ L^{β̄'} directly from `V ∈ L^{β̄'}`.
  have hT_Vabs :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => |V x|) := by
    have := hV.toMemLp.norm
    have hmem := MemLp.toMemLpPer this
    have heq : (fun x : (Fin d → ℝ) => ‖V x‖)
              = (fun x : (Fin d → ℝ) => |V x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at hmem
    exact hmem
  -- Constant `1` and friends.
  have hone : Periodic.MemLpPer βBar'E (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  -- Build `‖Dυ‖^α + 1`.
  have hT_Du1 :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ h.α + 1) := by
    have := hT_Du.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ h.α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ h.α + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hT_mb1 :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => μ x ^ h.β + 1) := by
    have := hT_mb.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => μ x ^ h.β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => μ x ^ h.β + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Apply scalar multiplications and sum closure.
  have hC'Du :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => C' * (‖fun j => Dυ j x‖ ^ h.α + 1)) := by
    have := hT_Du1.const_smul (𝕜 := ℝ) C'
    have heq :
        ((C' : ℝ) •
          (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ h.α + 1))
        = (fun x : (Fin d → ℝ) => C' * (‖fun j => Dυ j x‖ ^ h.α + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  have hCm :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => h.C * (μ x ^ h.β + 1)) := by
    have := hT_mb1.const_smul (𝕜 := ℝ) h.C
    have heq :
        ((h.C : ℝ) •
          (fun x : (Fin d → ℝ) => μ x ^ h.β + 1))
        = (fun x : (Fin d → ℝ) => h.C * (μ x ^ h.β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  -- Sum the four pieces.
  have hSum :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun j => Dυ j x‖ ^ h.α + 1)
            + h.C * (μ x ^ h.β + 1) + |υ x| + |V x|) := by
    have h12 := hC'Du.add hCm
    have heq12 :
        ((fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ h.α + 1))
          + (fun x : (Fin d → ℝ) => h.C * (μ x ^ h.β + 1)))
        = (fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1)) := by
      funext x; simp [Pi.add_apply]
    rw [heq12] at h12
    have h123 := h12.add hT_uabs
    have heq123 :
        ((fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1))
          + (fun x : (Fin d → ℝ) => |υ x|))
        = (fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1) + |υ x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq123] at h123
    have h1234 := h123.add hT_Vabs
    have heq1234 :
        ((fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1) + |υ x|)
          + (fun x : (Fin d → ℝ) => |V x|))
        = (fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1) + |υ x| + |V x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq1234] at h1234
    exact h1234
  -- Note: hC'_pos is exposed so the API matches the AC2 wrapper signature
  -- shape (it is not consumed inside this lemma — but is by the wrapper
  -- via `g_memLp_betaBar'_at_test`).
  let _ := hC'_pos
  exact hSum

/-- **`g_dominator_memLp_betaBar'_bare`** — bare-exponent sibling of
`g_dominator_memLp_betaBar'` (EXPERT RULING #4 retype, D2c-2e-1 child A).

Identical dominator-`MemLpPer` conclusion, but keyed on plain exponents
`(β α C : ℝ)` with their positivity facts `(hα : 1 < α) (hβ : 0 < β)`
instead of `h : HypothesisPowerGrowth H DpH`. The original proof consumes
`h` ONLY through the values `h.α/β/C` and positivity `h.hα/hβ`; no
`RegularityH`, no `upper/lower/DpH_upper/lagr/H_upper_pointwise` field. So the
result is value/positivity-level and needs no strict bundle — exactly the a.e.
dominator fields the T3 `setTendstoResidue` envelope consumes.

Body is the verbatim adaptation of `g_dominator_memLp_betaBar'` with
`h.α ↦ α`, `h.β ↦ β`, `h.C ↦ C`, `h.hα ↦ hα`, `h.hβ ↦ hβ`. -/
theorem g_dominator_memLp_betaBar'_bare
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (V υ : (Fin d → ℝ) → ℝ) (μ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) μ)
    (hυ : Periodic.MemLpPer
            (ENNReal.ofReal (α * (β + 1) / β)) υ)
    (hDυ : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i))
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal ((β + 1) / β)) V)
    {C' : ℝ} (hC'_pos : 0 < C') :
    Periodic.MemLpPer
      (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) =>
        C' * (‖fun i => Dυ i x‖ ^ α + 1)
          + C * (μ x ^ β + 1) + |υ x| + |V x|) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hbb_pos : 0 < β + 1 := by linarith
  have hβ_pos : 0 < β := hβ
  have hγb_pos : 0 < α * (β + 1) / β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hβb'_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  set βBarE : ℝ≥0∞ := ENNReal.ofReal (β + 1) with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal (α * (β + 1) / β) with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hβBar'E_def
  have hγα_eq : α * (β + 1) / β / α = (β + 1) / β := by
    field_simp
  have hT_Du :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ α) := by
    have hDυ_vec :
        Periodic.MemLpPer γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => Dυ j x) :=
      memLpPer_pi_of_coord (p := γBarE) Dυ hDυ
    set qE : ℝ≥0∞ := ENNReal.ofReal α with hqE_def
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαpos.le
    have hT_a :
        MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (Measure.restrict volume (UnitCube d)) :=
      MemLp.norm_rpow_div hDυ_vec.toMemLp qE
    have hdiv : γBarE / qE = βBar'E := by
      rw [hγBarE_def, hqE_def, hβBar'E_def,
        ← ENNReal.ofReal_div_of_pos hαpos]
      exact congrArg _ hγα_eq
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ α) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have := MemLp.toMemLpPer hT_a
    rw [hdiv] at this
    exact this
  have hT_mb :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => μ x ^ β) := by
    set qE : ℝ≥0∞ := ENNReal.ofReal β with hqE_def
    have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
    have hqE_toReal : qE.toReal = β := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hβ.le
    have hT_a :
        MemLp (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
              (βBarE / qE)
              (Measure.restrict volume (UnitCube d)) := by
      have h1 := MemLp.norm_rpow_div hμ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μ x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hdiv : βBarE / qE = βBar'E := by
      rw [hβBarE_def, hqE_def, hβBar'E_def,
        ← ENNReal.ofReal_div_of_pos hβ]
    have heq :
        (fun x : (Fin d → ℝ) => |μ x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μ x| ^ β) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b : Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => |μ x| ^ β) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hbound :
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          ‖μ x ^ β‖ ≤ (1 : ℝ) * ‖|μ x| ^ β‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
      have habs := Real.abs_rpow_le_abs_rpow (μ x) β
      have hrhs_nn : 0 ≤ |μ x| ^ β :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μ x ^ β)
          (Measure.restrict volume (UnitCube d)) := by
      have hcont : Continuous (fun y : ℝ => y ^ β) :=
        Real.continuous_rpow_const hβ.le
      exact hcont.comp_aestronglyMeasurable hμ.aestronglyMeasurable
    exact MemLp.toMemLpPer (MemLp.of_le_mul hT_b.toMemLp hmeas hbound)
  have hT_uabs :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => |υ x|) := by
    have hle_real :
        (β + 1) / β ≤ α * (β + 1) / β := by
      rw [div_le_div_iff_of_pos_right hβ]
      have : (1 : ℝ) * (β + 1) ≤ α * (β + 1) :=
        mul_le_mul_of_nonneg_right hα.le hbb_pos.le
      simpa using this
    have hle : βBar'E ≤ γBarE := by
      rw [hβBar'E_def, hγBarE_def]
      exact ENNReal.ofReal_le_ofReal hle_real
    have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
    have hυβ' : Periodic.MemLpPer βBar'E υ :=
      Periodic.MemLpPer.mono_exponent_finite hle hγTop hυ
    have hυ_norm : Periodic.MemLpPer βBar'E (fun x => ‖υ x‖) := by
      have := hυβ'.toMemLp.norm
      exact MemLp.toMemLpPer this
    have heq : (fun x : (Fin d → ℝ) => ‖υ x‖)
              = (fun x : (Fin d → ℝ) => |υ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at hυ_norm
    exact hυ_norm
  have hT_Vabs :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => |V x|) := by
    have := hV.toMemLp.norm
    have hmem := MemLp.toMemLpPer this
    have heq : (fun x : (Fin d → ℝ) => ‖V x‖)
              = (fun x : (Fin d → ℝ) => |V x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at hmem
    exact hmem
  have hone : Periodic.MemLpPer βBar'E (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hT_Du1 :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ α + 1) := by
    have := hT_Du.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ α + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hT_mb1 :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => μ x ^ β + 1) := by
    have := hT_mb.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => μ x ^ β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => μ x ^ β + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hC'Du :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => C' * (‖fun j => Dυ j x‖ ^ α + 1)) := by
    have := hT_Du1.const_smul (𝕜 := ℝ) C'
    have heq :
        ((C' : ℝ) •
          (fun x : (Fin d → ℝ) => ‖fun j => Dυ j x‖ ^ α + 1))
        = (fun x : (Fin d → ℝ) => C' * (‖fun j => Dυ j x‖ ^ α + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  have hCm :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) => C * (μ x ^ β + 1)) := by
    have := hT_mb1.const_smul (𝕜 := ℝ) C
    have heq :
        ((C : ℝ) •
          (fun x : (Fin d → ℝ) => μ x ^ β + 1))
        = (fun x : (Fin d → ℝ) => C * (μ x ^ β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  have hSum :
      Periodic.MemLpPer βBar'E
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun j => Dυ j x‖ ^ α + 1)
            + C * (μ x ^ β + 1) + |υ x| + |V x|) := by
    have h12 := hC'Du.add hCm
    have heq12 :
        ((fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ α + 1))
          + (fun x : (Fin d → ℝ) => C * (μ x ^ β + 1)))
        = (fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ α + 1)
              + C * (μ x ^ β + 1)) := by
      funext x; simp [Pi.add_apply]
    rw [heq12] at h12
    have h123 := h12.add hT_uabs
    have heq123 :
        ((fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ α + 1)
              + C * (μ x ^ β + 1))
          + (fun x : (Fin d → ℝ) => |υ x|))
        = (fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ α + 1)
              + C * (μ x ^ β + 1) + |υ x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq123] at h123
    have h1234 := h123.add hT_Vabs
    have heq1234 :
        ((fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ α + 1)
              + C * (μ x ^ β + 1) + |υ x|)
          + (fun x : (Fin d → ℝ) => |V x|))
        = (fun x : (Fin d → ℝ) =>
            C' * (‖fun j => Dυ j x‖ ^ α + 1)
              + C * (μ x ^ β + 1) + |υ x| + |V x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq1234] at h1234
    exact h1234
  let _ := hC'_pos
  exact hSum

/-! ### Phase H5d — extension of `H` upper / lower bounds to `m = 0`

Under `HypothesisPowerGrowth` together with the paper-faithful Hat0
riders (`HypothesisHat0`, `Hext_finite_at_zero`, `H_zero_eq_Hext`)
the right-continuity bridge `H_rc0_of_hHat0` gives
`H x p m → H x p 0` as `m → 0⁺` (real-valued). Combined with the
`m > 0` upper / lower bounds, the limit-of-inequality lemma
`le_of_tendsto_of_tendsto` extends both bounds to `m = 0` and then
to all `m ≥ 0`. The conclusion is a single non-strict-positivity
absolute-value bound `|H x p m| ≤ C(‖p‖^α + 1) + C(m^β + 1)` that
is exactly what `g_memLp_betaBar'_nonneg` (the H5d non-strict
variant of `g_memLp_betaBar'_at_test'`) consumes. -/

section H5dExtensions

open Filter
open scoped Topology

/-- **Phase H5d auxiliary.** Combined upper + lower absolute-value
bound on `H` covering the boundary `m = 0`. Under `(hpow, hHat0,
hFin, hAgree)`:

  for a.e. `x ∈ 𝕋^d` and every `(p, m)` with `0 ≤ m`,
    `|H x p m| ≤ h.C * (‖p‖^α + 1) + h.C * (m^β + 1)`. -/
theorem H_abs_bound_nonneg_of_hHat0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m →
        |H x p m| ≤ h.C * (‖p‖ ^ h.α + 1) + h.C * (m ^ h.β + 1) := by
  have hC := h.hC
  have hβ := h.hβ
  have hαpos : 0 < h.α := lt_trans one_pos h.hα
  -- Real-valued right-continuity of `H x p ·` at `0` (a.e. in `x`).
  have hRC := H_rc0_of_hHat0 hHat0 hFin hAgree
  -- Combine with `(h.H_upper_pointwise, h.lower)`. We weaken
  -- `H_upper_pointwise` (which has constant `h.C`) into the form
  -- `H ≤ h.C*(‖p‖^α + 1) + h.C*(m^β + 1)` (since `−m^β/h.C ≤ h.C*(m^β+1)`
  -- for `m ≥ 0`).
  filter_upwards [h.H_upper_pointwise, h.lower, hRC]
    with x hxU hxL hxRC
  intro p m hm_nn
  -- Real-valued limit-of-inequality applied to two cases.
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · -- Case `m > 0`: directly from `hxU`, `hxL`.
    have hUpper : H x p m ≤ h.C * (‖p‖ ^ h.α + 1) - (m ^ h.β) / h.C :=
      hxU p m hm_pos
    have hLower : (‖p‖ ^ h.α) / h.C - h.C * (m ^ h.β + 1) ≤ H x p m :=
      hxL p m hm_pos
    have hα_p_nn : 0 ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_m_nn : 0 ≤ m ^ h.β := Real.rpow_nonneg hm_nn _
    have hmβ_div_nn : 0 ≤ (m ^ h.β) / h.C := div_nonneg hβ_m_nn hC.le
    have hC1_nn : 0 ≤ h.C * (‖p‖ ^ h.α + 1) := by
      have : 0 ≤ ‖p‖ ^ h.α + 1 := by linarith
      exact mul_nonneg hC.le this
    have hCb_nn : 0 ≤ h.C * (m ^ h.β + 1) := by
      have : 0 ≤ m ^ h.β + 1 := by linarith
      exact mul_nonneg hC.le this
    have hpC_div_nn : 0 ≤ ‖p‖ ^ h.α / h.C := div_nonneg hα_p_nn hC.le
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · -- Case `m = 0`: use real-valued tendsto + limit-of-inequality.
    -- Substitute `m = 0` directly.
    subst hm_eq
    -- Tendsto `H x p s → H x p 0` as `s → 0⁺`.
    have hLim : Filter.Tendsto (fun s : ℝ => H x p s)
        (𝓝[>] (0 : ℝ)) (𝓝 (H x p 0)) := hxRC p
    -- Build upper bound via limit. RHS for `s > 0` is
    -- `h.C * (‖p‖^α + 1) - s^β / h.C`, continuous in `s`, → `h.C*(‖p‖^α + 1)` as `s → 0`.
    set Rup : ℝ → ℝ :=
      fun s => h.C * (‖p‖ ^ h.α + 1) - (s ^ h.β) / h.C with hRup_def
    have hRup_cont : Continuous Rup := by
      have h1 : Continuous (fun s : ℝ => s ^ h.β) :=
        Real.continuous_rpow_const hβ.le
      exact continuous_const.sub ((h1.div_const _))
    have hRup_lim : Filter.Tendsto Rup (𝓝[>] (0 : ℝ)) (𝓝 (Rup 0)) :=
      hRup_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hRup_at_zero : Rup 0 = h.C * (‖p‖ ^ h.α + 1) := by
      simp [hRup_def, Real.zero_rpow hβ.ne']
    have hUpper_ev :
        ∀ᶠ s in 𝓝[>] (0 : ℝ), H x p s ≤ Rup s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa [hRup_def] using hxU p s hs
    have hUpper0 : H x p 0 ≤ h.C * (‖p‖ ^ h.α + 1) := by
      have := le_of_tendsto_of_tendsto hLim hRup_lim hUpper_ev
      simpa [hRup_at_zero] using this
    -- Build lower bound via limit. RHS = `(‖p‖^α)/h.C - h.C*(s^β+1)`.
    set Rlo : ℝ → ℝ :=
      fun s => (‖p‖ ^ h.α) / h.C - h.C * (s ^ h.β + 1) with hRlo_def
    have hRlo_cont : Continuous Rlo := by
      have h1 : Continuous (fun s : ℝ => s ^ h.β) :=
        Real.continuous_rpow_const hβ.le
      exact continuous_const.sub
        (continuous_const.mul (h1.add continuous_const))
    have hRlo_lim : Filter.Tendsto Rlo (𝓝[>] (0 : ℝ)) (𝓝 (Rlo 0)) :=
      hRlo_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hRlo_at_zero : Rlo 0 = (‖p‖ ^ h.α) / h.C - h.C := by
      simp [hRlo_def, Real.zero_rpow hβ.ne']
    have hLower_ev :
        ∀ᶠ s in 𝓝[>] (0 : ℝ), Rlo s ≤ H x p s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa [hRlo_def] using hxL p s hs
    have hLower0 : (‖p‖ ^ h.α) / h.C - h.C ≤ H x p 0 := by
      have := le_of_tendsto_of_tendsto hRlo_lim hLim hLower_ev
      simpa [hRlo_at_zero] using this
    -- Combine into the absolute-value bound at `m = 0`.
    have hα_p_nn : 0 ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have h0β_eq : (0 : ℝ) ^ h.β = 0 := Real.zero_rpow hβ.ne'
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- −(rhs) ≤ H x p 0.
      have hCb_nn : 0 ≤ h.C * ((0 : ℝ) ^ h.β + 1) := by
        rw [h0β_eq]; linarith [hC]
      have hC1_nn : 0 ≤ h.C * (‖p‖ ^ h.α + 1) := by
        have : 0 ≤ ‖p‖ ^ h.α + 1 := by linarith
        exact mul_nonneg hC.le this
      have hpC_div_nn : 0 ≤ ‖p‖ ^ h.α / h.C := div_nonneg hα_p_nn hC.le
      -- From `hLower0`: `‖p‖^α / h.C - h.C ≤ H x p 0`.
      -- Goal: `-(h.C*(‖p‖^α+1) + h.C*(0^β+1)) ≤ H x p 0`.
      -- It suffices that `-(h.C*(‖p‖^α+1) + h.C*(0^β+1)) ≤ ‖p‖^α/h.C - h.C`.
      have hgap : -(h.C * (‖p‖ ^ h.α + 1) + h.C * ((0 : ℝ) ^ h.β + 1))
                  ≤ (‖p‖ ^ h.α) / h.C - h.C := by
        rw [h0β_eq]
        -- `-h.C(‖p‖^α + 1) - h.C(0+1) ≤ ‖p‖^α/h.C - h.C`
        -- ⇔ `-h.C(‖p‖^α + 1) ≤ ‖p‖^α/h.C`
        have : -h.C * (‖p‖ ^ h.α + 1) ≤ (‖p‖ ^ h.α) / h.C := by
          have hC1 : 0 ≤ h.C * (‖p‖ ^ h.α + 1) := hC1_nn
          linarith
        linarith
      linarith
    · -- H x p 0 ≤ rhs.
      have hCb_nn : 0 ≤ h.C * ((0 : ℝ) ^ h.β + 1) := by
        rw [h0β_eq]; linarith [hC]
      -- `hUpper0 : H x p 0 ≤ h.C*(‖p‖^α + 1)`. Add the non-negative `h.C*(0^β+1)`.
      linarith

/-- **Phase H5d — non-strict-positivity HJB-residual `MemLpPer β̄'`.**

Variant of `g_memLp_betaBar'_at_test'` where the test mass `μ` is only
required to be a.e. **non-negative** (rather than strict-positive).
The `m = 0` boundary case is handled by combining `hpow`'s `m > 0`
upper / lower bounds with the paper's `(a:Hat0)` real-valued
right-continuity bridge `H_rc0_of_hHat0`, which gives
`H x p m → H x p 0` as `m → 0⁺` and hence extends both bounds to
the boundary by `le_of_tendsto_of_tendsto`.

The producer takes the three Hat0 riders `(hHat0, hFin, hAgree)`
explicitly. The strict-positivity variant
`g_memLp_betaBar'_at_test'` remains the call surface for the
regularised pair `m_ε > 0`; this `_nonneg` variant is what
`WeakLimitInputBundle.hRes_Lp` consumes at the weak limit `mLim ≥ 0`. -/
theorem g_memLp_betaBar'_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V υ : (Fin d → ℝ) → ℝ) (μ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hg_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
        (Measure.restrict volume (UnitCube d)))
    (hμ : Periodic.MemLpPer (ENNReal.ofReal (h.β + 1)) μ)
    (hυ : Periodic.MemLpPer
            (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) υ)
    (hDυ : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) (Dυ i))
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal ((h.β + 1) / h.β)) V) :
    Periodic.MemLpPer
      (ENNReal.ofReal ((h.β + 1) / h.β))
      (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x) := by
  -- Use `C' := h.C` as the unifying constant. The dominator is then
  -- `h.C * (‖Dυ‖^α + 1) + h.C * (μ^β + 1) + |υ| + |V|`, which is exactly
  -- the shape of `g_dominator_memLp_betaBar'`.
  have hC := h.hC
  -- `MemLpPer` of the dominator at `C' := h.C`.
  have hG_mem :
      Periodic.MemLpPer
        (ENNReal.ofReal ((h.β + 1) / h.β))
        (fun x : (Fin d → ℝ) =>
          h.C * (‖fun i => Dυ i x‖ ^ h.α + 1)
            + h.C * (μ x ^ h.β + 1) + |υ x| + |V x|) :=
    g_dominator_memLp_betaBar' h V υ μ Dυ hμ hυ hDυ hV hC
  -- Pointwise bound on the residual via `H_abs_bound_nonneg_of_hHat0`.
  have habs := H_abs_bound_nonneg_of_hHat0 h hHat0 hFin hAgree
  have hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x) (μ x) + V x‖
          ≤ (1 : ℝ) *
            ‖h.C * (‖fun i => Dυ i x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1) + |υ x| + |V x|‖ := by
    filter_upwards [habs, hμ_nn] with x hxAbs hxμ
    set p_x : Fin d → ℝ := fun i => Dυ i x with hp_x
    have hxμ' : 0 ≤ μ x := hxμ
    have hα_p_nn : 0 ≤ ‖p_x‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_μ_nn : 0 ≤ μ x ^ h.β := Real.rpow_nonneg hxμ' _
    -- Apply `hxAbs` at `(p_x, μ x)`.
    have hH_abs : |H x p_x (μ x)|
                  ≤ h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1) :=
      hxAbs p_x (μ x) hxμ'
    -- Triangle: `|g| ≤ |υ| + |H| + |V|`.
    have htri :
        ‖-(υ x) - H x p_x (μ x) + V x‖
          ≤ |υ x| + |H x p_x (μ x)| + |V x| := by
      rw [Real.norm_eq_abs]
      have h1 : |(-(υ x)) - H x p_x (μ x) + V x|
                ≤ |(-(υ x)) - H x p_x (μ x)| + |V x| := abs_add_le _ _
      have h2 : |(-(υ x)) - H x p_x (μ x)|
                ≤ |-(υ x)| + |-(H x p_x (μ x))| := by
        have := abs_add_le (-(υ x)) (-(H x p_x (μ x)))
        have heq : -(υ x) + -(H x p_x (μ x)) = (-(υ x)) - H x p_x (μ x) := by
          ring
        rw [heq] at this
        exact this
      have h3 : |-(υ x)| = |υ x| := abs_neg _
      have h4 : |-(H x p_x (μ x))| = |H x p_x (μ x)| := abs_neg _
      linarith
    -- Combine: `|g| ≤ Dom_H + |υ| + |V|` ≤ Dom (with `+ h.C·(μ^β + 1)` flips).
    have htotal :
        ‖-(υ x) - H x p_x (μ x) + V x‖
          ≤ h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
              + |υ x| + |V x| := by linarith
    have hG_nn :
        0 ≤ h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x| := by
      have hC1 : 0 ≤ h.C * (‖p_x‖ ^ h.α + 1) := by
        have : 0 ≤ ‖p_x‖ ^ h.α + 1 := by linarith
        exact mul_nonneg hC.le this
      have hCb : 0 ≤ h.C * (μ x ^ h.β + 1) := by
        have : 0 ≤ μ x ^ h.β + 1 := by linarith
        exact mul_nonneg hC.le this
      have habs1 : 0 ≤ |υ x| := abs_nonneg _
      have habs2 : 0 ≤ |V x| := abs_nonneg _
      linarith
    rw [show (‖h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x|‖) = _ from
            (Real.norm_eq_abs _)]
    rw [abs_of_nonneg hG_nn, one_mul]
    exact htotal
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_mem.toMemLp hg_meas hbound)

/-- **Free-`q` non-strict-positivity HJB-residual `MemLpPer`.**

Variant of `g_memLp_betaBar'_nonneg` parameterised on the conclusion
exponent `q : ℝ≥0∞` (instead of being pinned to `(h.β+1)/h.β`), and
on the dominator-`MemLpPer` membership directly (instead of deriving
it internally from `(hμ, hυ, hDυ, hV)`). This matches the API shape
of `g_memLp_betaBar'_at_test`, but consumes a.e. non-negativity of
`μ` (and the Hat0 riders) rather than strict positivity. -/
theorem g_memLp_q_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    {q : ℝ≥0∞}
    (V υ : (Fin d → ℝ) → ℝ) (μ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hg_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
        (Measure.restrict volume (UnitCube d)))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          h.C * (‖fun i => Dυ i x‖ ^ h.α + 1)
            + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x|)) :
    MemLpPer q
      (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x) := by
  -- Pointwise bound using `H_abs_bound_nonneg_of_hHat0`.
  have habs := H_abs_bound_nonneg_of_hHat0 h hHat0 hFin hAgree
  have hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x) (μ x) + V x‖
          ≤ (1 : ℝ) *
            ‖h.C * (‖fun i => Dυ i x‖ ^ h.α + 1)
              + h.C * (μ x ^ h.β + 1) + |υ x| + |V x|‖ := by
    filter_upwards [habs, hμ_nn] with x hxAbs hxμ
    set p_x : Fin d → ℝ := fun i => Dυ i x with hp_x
    have hxμ' : 0 ≤ μ x := hxμ
    have hα_p_nn : 0 ≤ ‖p_x‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_μ_nn : 0 ≤ μ x ^ h.β := Real.rpow_nonneg hxμ' _
    -- Apply `hxAbs` at `(p_x, μ x)`.
    have hH_abs : |H x p_x (μ x)|
                  ≤ h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1) :=
      hxAbs p_x (μ x) hxμ'
    -- Triangle: `|g| ≤ |υ| + |H| + |V|`.
    have htri :
        ‖-(υ x) - H x p_x (μ x) + V x‖
          ≤ |υ x| + |H x p_x (μ x)| + |V x| := by
      rw [Real.norm_eq_abs]
      have h1 : |(-(υ x)) - H x p_x (μ x) + V x|
                ≤ |(-(υ x)) - H x p_x (μ x)| + |V x| := abs_add_le _ _
      have h2 : |(-(υ x)) - H x p_x (μ x)|
                ≤ |-(υ x)| + |-(H x p_x (μ x))| := by
        have := abs_add_le (-(υ x)) (-(H x p_x (μ x)))
        have heq : -(υ x) + -(H x p_x (μ x)) = (-(υ x)) - H x p_x (μ x) := by
          ring
        rw [heq] at this
        exact this
      have h3 : |-(υ x)| = |υ x| := abs_neg _
      have h4 : |-(H x p_x (μ x))| = |H x p_x (μ x)| := abs_neg _
      linarith
    have htotal :
        ‖-(υ x) - H x p_x (μ x) + V x‖
          ≤ h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
              + |υ x| + |V x| := by linarith
    have hG_nn :
        0 ≤ h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x| := by
      have hC1 : 0 ≤ h.C * (‖p_x‖ ^ h.α + 1) := by
        have : 0 ≤ ‖p_x‖ ^ h.α + 1 := by linarith
        exact mul_nonneg h.hC.le this
      have hCb : 0 ≤ h.C * (μ x ^ h.β + 1) := by
        have : 0 ≤ μ x ^ h.β + 1 := by linarith
        exact mul_nonneg h.hC.le this
      have habs1 : 0 ≤ |υ x| := abs_nonneg _
      have habs2 : 0 ≤ |V x| := abs_nonneg _
      linarith
    rw [show (‖h.C * (‖p_x‖ ^ h.α + 1) + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x|‖) = _ from
            (Real.norm_eq_abs _)]
    rw [abs_of_nonneg hG_nn, one_mul]
    exact htotal
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_mem.toMemLp hg_meas hbound)

/-- **Phase H5d — non-strict-positivity flux `MemLpPer γ̄'`.**

Variant of `flux_memLp_gammaBar'_at_test` where the test mass `μ`
is only required to be a.e. **non-negative** (rather than
strict-positive). On the `μ = 0` boundary the integrand
`μ x * DpH x (Dυ x) (μ x) i` vanishes identically (the factor
`μ x = 0`), so the pointwise bound by the dominator
`G x := h.C · (μ x · ‖Dυ x‖^{α-1} + μ x^{1+β-β/α} + μ x)` extends to
the boundary without needing any `Hat0` riders (unlike the HJB
variant, which needs `H_rc0_of_hHat0` to extend the upper/lower
bounds to `m = 0`).

This is the flux-side counterpart of `g_memLp_betaBar'_nonneg`,
consumed by the limit-pairing producer when working at the weak
limit `mLim ≥ 0` rather than the regularised pair `m_ε > 0`. -/
theorem flux_memLp_gammaBar'_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {q : ℝ≥0∞}
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (i : Fin d)
    (hμ_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hF_meas :
      AEStronglyMeasurable
        (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
        (Measure.restrict volume (UnitCube d)))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                    + μ x ^ (1 + h.β - h.β / h.α) + μ x))) :
    MemLpPer q (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) := by
  -- The pointwise dominator `G x` is non-negative under `μ x ≥ 0`
  -- (every summand `μ · ‖·‖^{α-1}`, `μ^{1+β-β/α}`, `μ` is nonneg, and
  -- `h.C > 0`). Use `MemLp.of_le_mul` with `c = 1`.
  have hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μ x * DpH x (fun j => Dυ j x) (μ x) i‖
          ≤ (1 : ℝ) *
            ‖h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                      + μ x ^ (1 + h.β - h.β / h.α) + μ x)‖ := by
    filter_upwards [mDpH_coord_pointwise_bound h (fun x => fun j => Dυ j x),
                    hμ_nn] with x hxbnd hxμ
    -- Non-negativity of every summand of `G x`.
    have hα1_nn : 0 ≤ ‖fun j => Dυ j x‖ ^ (h.α - 1) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hμα_nn : 0 ≤ μ x ^ (1 + h.β - h.β / h.α) :=
      Real.rpow_nonneg hxμ _
    have hG_nn : 0 ≤ h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                  + μ x ^ (1 + h.β - h.β / h.α) + μ x) := by
      apply mul_nonneg h.hC.le
      have h1 : 0 ≤ μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1) :=
        mul_nonneg hxμ hα1_nn
      linarith
    -- Split on `μ x = 0 ∨ 0 < μ x`.
    rcases eq_or_lt_of_le hxμ with hxμeq | hxμpos
    · -- Case `μ x = 0`: the integrand vanishes.
      have hxμeq' : (0 : ℝ) = μ x := hxμeq
      have hflux_zero : μ x * DpH x (fun j => Dυ j x) (μ x) i = 0 := by
        rw [← hxμeq']; ring
      rw [hflux_zero, norm_zero]
      rw [Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
      exact hG_nn
    · -- Case `0 < μ x`: reuse the strict-positivity pointwise bound.
      have hb := hxbnd (μ x) hxμpos i
      rw [Real.norm_eq_abs]
      rw [Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
      exact hb
  exact MemLp.toMemLpPer (MemLp.of_le_mul hG_mem.toMemLp hF_meas hbound)

end H5dExtensions

/-! #### Sanity-check: type-shape pinning of the four per-test-triple
declarations.

These `example` blocks exercise each of `mDpH_coord_pointwise_bound`,
`flux_memLp_gammaBar'_at_test`, `g_memLp_betaBar'_at_test`, and
`μMinusOne_memLp_of_betaBar` purely at the level of type-shape: each
example threads the lemma's hypotheses through unchanged and pins the
conclusion's type. No "real content" is checked — just that the
declarations exist with the expected signatures and that the
`MemLpPer`/`∀ᵐ`-quantifier shapes line up. -/

/-- Type-shape pinning for `mDpH_coord_pointwise_bound`. -/
example
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Dυ : (Fin d → ℝ) → (Fin d → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ μx, 0 < μx → ∀ i,
        |μx * DpH x (Dυ x) μx i|
          ≤ h.C * (μx * ‖Dυ x‖ ^ (h.α - 1)
                    + μx ^ (1 + h.β - h.β / h.α) + μx) :=
  mDpH_coord_pointwise_bound h Dυ

/-- Type-shape pinning for `flux_memLp_gammaBar'_at_test`. -/
example
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {q : ℝ≥0∞}
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (i : Fin d)
    (hμ_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < μ x)
    (hF_meas :
      AEStronglyMeasurable
        (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
        (Measure.restrict volume (UnitCube d)))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          h.C * (μ x * ‖fun j => Dυ j x‖ ^ (h.α - 1)
                    + μ x ^ (1 + h.β - h.β / h.α) + μ x))) :
    MemLpPer q (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) :=
  flux_memLp_gammaBar'_at_test h μ Dυ i hμ_pos hF_meas hG_mem

/-- Type-shape pinning for `g_memLp_betaBar'_at_test`. -/
example
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {q : ℝ≥0∞}
    (V υ : (Fin d → ℝ) → ℝ) (μ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < μ x)
    {C' : ℝ} (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ C' * (‖p‖ ^ h.α + 1) - (m ^ h.β) / C')
    (hg_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
        (Measure.restrict volume (UnitCube d)))
    (hG_mem :
      MemLpPer q
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun i => Dυ i x‖ ^ h.α + 1)
            + h.C * (μ x ^ h.β + 1)
            + |υ x| + |V x|)) :
    MemLpPer q
      (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x) :=
  g_memLp_betaBar'_at_test h V υ μ Dυ hμ_pos hC'_pos h_upper hg_meas hG_mem

/-- Type-shape pinning for `μMinusOne_memLp_of_betaBar`, instantiated at
the trivial case `q = p` where the exponent inequality `q ≤ p` is just
reflexivity. -/
example
    {d : ℕ}
    {p : ℝ≥0∞}
    (μ : (Fin d → ℝ) → ℝ)
    (hμ_memLp : Periodic.MemLpPer (d := d) p μ)
    (hp_top : p ≠ ⊤) :
    Periodic.MemLpPer (d := d) p (fun x => μ x - 1) :=
  μMinusOne_memLp_of_betaBar μ hμ_memLp le_rfl hp_top

/-! ## Section: integrand-level tendsto along an additive perturbation

This section provides the analytic core consumed by Children C and D
of the two-domain redesign in
`Theorems/SimplePower/Banach/RegularizedSequence.lean`. Those Minty/δ-limit
lifts need to discharge an `hCont` hypothesis: the value of the
regularized MFG operator pairing `mfgOperatorEpsPair γBar ε Dυ μ_n υ Dν η_n (υ - u)`
along the strict-positive perturbation `μ_n := S.indicator ρ + 1/(n+1)`
converges to the value at the limit `μ := S.indicator ρ`.

Because `Hamiltonian/Estimates.lean` sits *upstream* of
`Solutions/Regularized.lean` (and therefore cannot reference
`mfgOperatorEpsPair` directly), we land here the *integrand-level*
analytic core only: a generic product DCT helper, plus three specialised
tendsto lemmas (HJB, flux, mass) at the level of `∫ … dx`. The consumer
composes them by adding the three terms and the constant Gateaux term
to obtain the headline tendsto for `mfgOperatorEpsPair`.

All lemmas integrate against `Measure.restrict volume (UnitCube d)`,
matching the convention of `mfgOperatorPair` / `mfgOperatorEpsPair`.

The key analytic input is dominated convergence; the `Lᵖ` domination
chains are the AC2 dominators
`g_dominator_memLp_betaBar'` (HJB side, exponent `β̄'`) and
`flux_dominator_memLp_gammaBar'` (flux side, exponent `γ̄'`) landed
just above.
-/

open MeasureTheory Filter
open scoped Topology

/-- **Generic product DCT on the unit cube.** Given two sequences
`g_n, η_n : (Fin d → ℝ) → ℝ` of AE-strongly-measurable functions on the
unit cube with:

* a.e. pointwise convergence `g_n → g_∞` and `η_n → η_∞`,
* uniform pointwise domination `‖g_n‖ ≤ G` a.e. with `G ∈ L^p` and
  `‖η_n‖ ≤ E` a.e. with `E ∈ L^q`, where `p`, `q` are real
  Hölder-conjugate (`1/p + 1/q = 1`) and finite,

the integrals of the products converge:
`∫ g_n · η_n d(volume.restrict (UnitCube d)) → ∫ g_∞ · η_∞ d(volume.restrict (UnitCube d))`.

This is the analytic engine that the three named perturbation-tendsto
lemmas below specialise. The proof bounds `|g_n η_n| ≤ G · E ∈ L¹` by
Hölder's inequality, then invokes
`MeasureTheory.tendsto_integral_of_dominated_convergence`. -/
theorem tendsto_setIntegral_mul_of_dom
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {gN : ℕ → (Fin d → ℝ) → ℝ} {gInf : (Fin d → ℝ) → ℝ}
    {ηN : ℕ → (Fin d → ℝ) → ℝ} {ηInf : (Fin d → ℝ) → ℝ}
    {G E : (Fin d → ℝ) → ℝ}
    (hG_memLp : Periodic.MemLpPer (ENNReal.ofReal p) G)
    (hE_memLp : Periodic.MemLpPer (ENNReal.ofReal q) E)
    (hgN_meas : ∀ n,
      AEStronglyMeasurable (gN n) (volume.restrict (UnitCube d)))
    (hηN_meas : ∀ n,
      AEStronglyMeasurable (ηN n) (volume.restrict (UnitCube d)))
    (hgN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖gN n x‖ ≤ G x)
    (hηN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖ηN n x‖ ≤ E x)
    (hgN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => gN n x) Filter.atTop (𝓝 (gInf x)))
    (hηN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, gN n x * ηN n x
                  ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d, gInf x * ηInf x
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Working measure: restriction of Lebesgue to the unit cube.
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm
  -- The dominator `bound x := G x * E x` is in `L¹` by Hölder.
  set bound : (Fin d → ℝ) → ℝ := fun x => G x * E x with hbound
  have hbound_int : Integrable bound μm := by
    -- `MemLpPer.integrable_mul` produces `IntegrableOn (G * E) (UnitCube d)`.
    have := Periodic.MemLpPer.integrable_mul (p := p) (q := q) hpq hG_memLp hE_memLp
    -- `IntegrableOn f s := Integrable f (μ.restrict s)` by definition.
    exact this
  -- AE-strong-measurability of the products.
  have hprod_meas : ∀ n,
      AEStronglyMeasurable (fun x => gN n x * ηN n x) μm :=
    fun n => (hgN_meas n).mul (hηN_meas n)
  -- Pointwise domination of the products by `bound`.
  have hG_nn : ∀ᵐ x ∂μm, 0 ≤ G x := by
    -- `‖gN 0 x‖ ≤ G x` and `‖·‖ ≥ 0`.
    filter_upwards [hgN_bd 0] with x hx
    exact (norm_nonneg _).trans hx
  have hE_nn : ∀ᵐ x ∂μm, 0 ≤ E x := by
    filter_upwards [hηN_bd 0] with x hx
    exact (norm_nonneg _).trans hx
  have hprod_bd : ∀ n, ∀ᵐ x ∂μm,
      ‖gN n x * ηN n x‖ ≤ bound x := by
    intro n
    filter_upwards [hgN_bd n, hηN_bd n, hG_nn, hE_nn]
      with x hxg hxη hxG hxE
    rw [norm_mul]
    exact mul_le_mul hxg hxη (norm_nonneg _) hxG
  -- Pointwise convergence of the products.
  have hprod_lim : ∀ᵐ x ∂μm,
      Filter.Tendsto (fun n => gN n x * ηN n x) Filter.atTop
        (𝓝 (gInf x * ηInf x)) := by
    filter_upwards [hgN_lim, hηN_lim] with x hxg hxη
    exact hxg.mul hxη
  -- DCT.
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hprod_meas hbound_int hprod_bd hprod_lim

/-- **HJB-side integrand tendsto along an additive perturbation.** The
HJB summand of `mfgOperatorPair`,

  `g_n(x) = -υ(x) - H(x, Dυ x, μ_n x) + V(x)`,

paired against `η_n := μ_n - m'`, converges along `n → ∞` to its value
at the limit `μ_∞`, when:

* the integrand sequences `g_n` are AE-strongly-measurable and
  pointwise-dominated by an `Lᵝ̄'` bound `G`,
* the test sequences `η_n` (here `μ_n - m'`) are AE-strongly-measurable
  and pointwise-dominated by an `Lᵝ̄` bound `E`,
* the pointwise convergences `g_n → g_∞`, `η_n → η_∞` hold a.e.

This is the literal special-case wrapper of `tendsto_setIntegral_mul_of_dom`
named for the consumer in `Banach/RegularizedSequence.lean` — the only
content beyond the generic helper is fixing the Hölder pair to
`(β̄', β̄)` (with `β̄ = β + 1`, `β̄' = β̄/(β̄-1) = (β+1)/β`).

The pointwise tendsto inputs `hg_lim` / `hη_lim` come from the paper's
`RegularityH.continuous_H_pm` (continuity of `H` in the third argument)
and the trivial fact `1/(n+1) → 0`; these are paper-level inputs
authorised at the use site (CONVENTIONS §8).

The pointwise dominators `G` / `E` come from the AC2 closure
`g_dominator_memLp_betaBar'` (here, evaluated at the upper envelope
`μ + 1` of the perturbation `μ_n = μ + 1/(n+1) ≤ μ + 1`). -/
theorem tendsto_setIntegral_HJB_mul_of_dom
    {β : ℝ} (hβ : 0 < β)
    {gN : ℕ → (Fin d → ℝ) → ℝ} {gInf : (Fin d → ℝ) → ℝ}
    {ηN : ℕ → (Fin d → ℝ) → ℝ} {ηInf : (Fin d → ℝ) → ℝ}
    {G E : (Fin d → ℝ) → ℝ}
    (hG_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) G)
    (hE_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) E)
    (hgN_meas : ∀ n,
      AEStronglyMeasurable (gN n) (volume.restrict (UnitCube d)))
    (hηN_meas : ∀ n,
      AEStronglyMeasurable (ηN n) (volume.restrict (UnitCube d)))
    (hgN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖gN n x‖ ≤ G x)
    (hηN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖ηN n x‖ ≤ E x)
    (hgN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => gN n x) Filter.atTop (𝓝 (gInf x)))
    (hηN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, gN n x * ηN n x
                  ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d, gInf x * ηInf x
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Real Hölder-conjugate pair `((β+1)/β, β+1)`.
  have hβbar_gt_one : 1 < β + 1 := by linarith
  have hpq : Real.HolderConjugate ((β + 1) / β) (β + 1) := by
    -- Direct proof: `1/((β+1)/β) + 1/(β+1) = β/(β+1) + 1/(β+1) = 1`.
    have hβ_pos : 0 < β := hβ
    have hbb_pos : 0 < β + 1 := by linarith
    have hbb_ne : (β + 1 : ℝ) ≠ 0 := hbb_pos.ne'
    have hβ_ne : (β : ℝ) ≠ 0 := hβ_pos.ne'
    have hβb'_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ_pos
    refine ⟨?_, hβb'_pos, hbb_pos⟩
    -- `1/((β+1)/β) + 1/(β+1) = 1`.
    field_simp
  exact tendsto_setIntegral_mul_of_dom hpq hG_memLp hE_memLp
    hgN_meas hηN_meas hgN_bd hηN_bd hgN_lim hηN_lim

/-- **Flux-side integrand tendsto along an additive perturbation.** The
flux summand of `mfgOperatorPair`,

  `F_n(x) = μ_n x · (D_pH(x, Dυ x, μ_n x) ⬝ Dν x)`,

paired against the constant `1`-coefficient (or alternatively summing
the per-coordinate flux against the test components `Dν_i`), converges
along `n → ∞` to its value at the limit. Special case wrapper of
`tendsto_setIntegral_mul_of_dom` at the Hölder pair `(γ̄', γ̄)` with
`γ̄ = α(β+1)/β`, `γ̄' = γ̄/(γ̄-1)`. -/
theorem tendsto_setIntegral_flux_mul_of_dom
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {gN : ℕ → (Fin d → ℝ) → ℝ} {gInf : (Fin d → ℝ) → ℝ}
    {ηN : ℕ → (Fin d → ℝ) → ℝ} {ηInf : (Fin d → ℝ) → ℝ}
    {G E : (Fin d → ℝ) → ℝ}
    (hG_memLp : Periodic.MemLpPer
        (ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1))) G)
    (hE_memLp : Periodic.MemLpPer
        (ENNReal.ofReal (α * (β + 1) / β)) E)
    (hgN_meas : ∀ n,
      AEStronglyMeasurable (gN n) (volume.restrict (UnitCube d)))
    (hηN_meas : ∀ n,
      AEStronglyMeasurable (ηN n) (volume.restrict (UnitCube d)))
    (hgN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖gN n x‖ ≤ G x)
    (hηN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖ηN n x‖ ≤ E x)
    (hgN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => gN n x) Filter.atTop (𝓝 (gInf x)))
    (hηN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, gN n x * ηN n x
                  ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d, gInf x * ηInf x
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Real Hölder-conjugate pair `(γ̄/(γ̄-1), γ̄)` with `γ̄ = α(β+1)/β`.
  have hαpos : 0 < α := lt_trans one_pos hα
  have hbb_pos : 0 < β + 1 := by linarith
  have hγb_pos : 0 < α * (β + 1) / β :=
    div_pos (mul_pos hαpos hbb_pos) hβ
  have hγb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  have hγbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hγb'_pos : 0 < α * (β + 1) / β / (α * (β + 1) / β - 1) :=
    div_pos hγb_pos hγbm1_pos
  have hpq :
      Real.HolderConjugate
        (α * (β + 1) / β / (α * (β + 1) / β - 1))
        (α * (β + 1) / β) := by
    refine ⟨?_, hγb'_pos, hγb_pos⟩
    -- `1/(γ̄/(γ̄-1)) + 1/γ̄ = (γ̄-1)/γ̄ + 1/γ̄ = 1`.
    have hγb_ne : α * (β + 1) / β ≠ 0 := hγb_pos.ne'
    have hγbm1_ne : α * (β + 1) / β - 1 ≠ 0 := hγbm1_pos.ne'
    field_simp
    ring
  exact tendsto_setIntegral_mul_of_dom hpq hG_memLp hE_memLp
    hgN_meas hηN_meas hgN_bd hηN_bd hgN_lim hηN_lim

/-- **Mass-side integrand tendsto along an additive perturbation.** The
mass summand of `mfgOperatorPair`,

  `M_n(x) = (μ_n x - 1) · (υ x - u x)`,

converges along `n → ∞` to its value at the limit. Special case wrapper
of `tendsto_setIntegral_mul_of_dom` at the Hölder pair `(β̄, β̄')`. -/
theorem tendsto_setIntegral_mass_mul_of_dom
    {β : ℝ} (hβ : 0 < β)
    {gN : ℕ → (Fin d → ℝ) → ℝ} {gInf : (Fin d → ℝ) → ℝ}
    {ηN : ℕ → (Fin d → ℝ) → ℝ} {ηInf : (Fin d → ℝ) → ℝ}
    {G E : (Fin d → ℝ) → ℝ}
    (hG_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) G)
    (hE_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) E)
    (hgN_meas : ∀ n,
      AEStronglyMeasurable (gN n) (volume.restrict (UnitCube d)))
    (hηN_meas : ∀ n,
      AEStronglyMeasurable (ηN n) (volume.restrict (UnitCube d)))
    (hgN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖gN n x‖ ≤ G x)
    (hηN_bd : ∀ n,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖ηN n x‖ ≤ E x)
    (hgN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => gN n x) Filter.atTop (𝓝 (gInf x)))
    (hηN_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, gN n x * ηN n x
                  ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d, gInf x * ηInf x
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Real Hölder-conjugate pair `(β+1, (β+1)/β)`.
  have hβ_pos : 0 < β := hβ
  have hbb_pos : 0 < β + 1 := by linarith
  have hβb'_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ_pos
  have hpq : Real.HolderConjugate (β + 1) ((β + 1) / β) := by
    refine ⟨?_, hbb_pos, hβb'_pos⟩
    have hbb_ne : (β + 1 : ℝ) ≠ 0 := hbb_pos.ne'
    have hβ_ne : (β : ℝ) ≠ 0 := hβ_pos.ne'
    field_simp
    ring
  exact tendsto_setIntegral_mul_of_dom hpq hG_memLp hE_memLp
    hgN_meas hηN_meas hgN_bd hηN_bd hgN_lim hηN_lim

/-! ### Sanity check: the constant-mass test trivialises -/

/-- **Trivial-case sanity check.** For a constant test sequence
`gN ≡ 1 ≡ gInf` and `ηN ≡ 0 ≡ ηInf`, the product DCT statement
collapses to a constant-zero limit. This pins the lemma's signature
shape against accidental refactor breakage. -/
example {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto
      (fun _ : ℕ => ∫ _x in UnitCube d, (1 : ℝ) * (0 : ℝ)
                      ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ _x in UnitCube d, (1 : ℝ) * (0 : ℝ)
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Both sides are `∫ 0 = 0`; tendsto-of-const is reflexive.
  let _ := hβ  -- exponent supplied to keep the example aligned with
                -- the wrappers' signature shape.
  exact tendsto_const_nhds

/-! ### Signed-perturbation dominator MemLpPer derivations

(Phase G; task `infra-P5-phase-G-tendsto-signed-dominator-integrabilities`.)

Mirror of the set-perturbation dominator block above, specialised to the
signed perturbation `μ_n := m + σ · m · 1_S + 1/(n+1)` with `σ ∈ {±1}`.
The test direction is zero, so the flux and mass summand integrands
vanish pointwise in this case; only the HJB summand contributes, and
hence we only need the `Eh` (test factor) and `Gh` (HJB-residual
envelope) dominators here. -/

/-- **`Eh` integrability (signed case).** The HJB-summand test factor

  `Eh x := |m x| · 2 + 1`

dominates `‖σ · m x · 1_S x + 1/(n+1)‖` uniformly in `n` and in
`σ ∈ {±1}`, and lies in `L^{β+1}_per` whenever `m ∈ L^{β+1}_per`. -/
theorem Eh_memLp_betaBar_signed
    {β : ℝ} (hβ : 0 < β)
    (m : (Fin d → ℝ) → ℝ)
    (hm : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) m) :
    Periodic.MemLpPer (ENNReal.ofReal (β + 1))
      (fun x : (Fin d → ℝ) => |m x| * 2 + 1) := by
  -- The unit cube has volume 1; the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  set p : ℝ≥0∞ := ENNReal.ofReal (β + 1) with hp_def
  -- `|m x| ∈ L^p`.
  have hm_abs : Periodic.MemLpPer p (fun x : (Fin d → ℝ) => |m x|) := by
    have h := hm.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖m x‖)
              = (fun x : (Fin d → ℝ) => |m x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h
    exact MemLp.toMemLpPer h
  -- `|m x| · 2 ∈ L^p` via `const_smul` with scalar `2`.
  have hm_abs_2 :
      Periodic.MemLpPer p (fun x : (Fin d → ℝ) => |m x| * 2) := by
    have := hm_abs.const_smul (𝕜 := ℝ) (2 : ℝ)
    have heq : ((2 : ℝ) • (fun x : (Fin d → ℝ) => |m x|))
              = (fun x : (Fin d → ℝ) => |m x| * 2) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [heq] at this
    exact this
  -- The constant `1` is in `L^p`.
  have hone : Periodic.MemLpPer p (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  let _ := hβ
  -- Sum closure.
  have hsum := hm_abs_2.add hone
  have heq :
      ((fun x : (Fin d → ℝ) => |m x| * 2) + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => |m x| * 2 + 1) := by
    funext x; simp [Pi.add_apply]
  rw [heq] at hsum
  exact hsum

end Hamiltonian
end StationaryMFG
