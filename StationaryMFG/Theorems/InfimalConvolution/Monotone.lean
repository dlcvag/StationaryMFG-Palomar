module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.InfimalConvolution.InfConv

@[expose] public section

/-!
# `lem:H.delta.monotone`: LL-monotonicity of `H^ε`

This module formalizes Lemma `lem:H.delta.monotone` of
Ferreira–Gomes–Üçer (`Source/FGU-monotone_revised.tex`, line 1754).

## Paper restatement (line 1754, equation `h-epsilon-mon`)

Under `HypothesisMonotone H DpH` and `HypothesisWeakGrowth H DpH`, for
every `ε > 0` the regularized Hamiltonian
`H^ε(x, p, m) := ⨅_q [H(x, p − q, m) + (1/ε) K(q)]` with its gradient
`D_pH^ε(x, p, m) := D_pH(x, p − q^ε(x, p, m), m)` satisfies the
Lasry–Lions monotonicity inequality `h-epsilon-mon` for a.e.~`x` and
all `(p_i, m_i)` with `m_i > 0`:
```
  (-H^ε(x, p_1, m_1) + H^ε(x, p_2, m_2)) · (m_1 − m_2)
    + (m_1 D_pH^ε(x, p_1, m_1) − m_2 D_pH^ε(x, p_2, m_2)) · (p_1 − p_2) ≥ 0.
```

## Paper proof (lines 1766–1777)

Substituting `eq:H-epsilon-formula` and `eq:DpH-epsilon-formula`, with
`q_i := q^ε(x, p_i, m_i)` and `G_i := DpH(x, p_i − q_i, m_i)`, the LHS
expands into three non-negative pieces:

1. The Lasry–Lions inequality for `H` at the **inner** points
   `(p_i − q_i, m_i)` (from `HypothesisMonotone.monotone`).
2. `m_1 · ((1/ε) K(q_2) − (1/ε) K(q_1) − G_1 · (q_2 − q_1)) ≥ 0`
   from the convex subgradient inequality
   `G_1 · (q − q_1) ≤ (1/ε)(K(q) − K(q_1))` at `q = q_2` (the first
   inclusion in `eq:inf-conv.diff-relation1`).
3. Symmetric term at index `2`, by the same inclusion with roles
   swapped.

Each is non-negative; the sum is non-negative.

## Lean strategy

Since `DpHdelta` is not packaged as a noncomputable function in this
project (it would require a Borel-measurable selector of the
minimizer), we follow the codebase pattern of `Hdelta_gradient_upper_bound`
and `mDpHdelta_hat0`: take an **arbitrary candidate**
`DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)` together with
per-`(x, p, m)` minimizer data and the optimality (subgradient)
inequality as explicit hypotheses, and produce a `HypothesisMonotone`
witness.

The algebraic content of the paper proof is fully verified.
-/

noncomputable section

namespace StationaryMFG
namespace InfimalConvolution

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped Topology

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ## Algebraic helpers -/

/-- Scalar multiplication distributes through `dotProduct` on the
left: `(σ • v) ⬝ w = σ * (v ⬝ w)`. Note that `σ • v` for `v : Fin d → ℝ`
unfolds pointwise to `fun i => σ * v i`. -/
private lemma euclideanDot_smul_left (σ : ℝ) (v w : Fin d → ℝ) :
    (σ • v) ⬝ w = σ * (v ⬝ w) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Bilinearity of `dotProduct` in the right slot: `v ⬝ (w₁ + w₂) = v ⬝ w₁ + v ⬝ w₂`. -/
private lemma euclideanDot_add_right (v w₁ w₂ : Fin d → ℝ) :
    v ⬝ (w₁ + w₂) = v ⬝ w₁ + v ⬝ w₂ := by
  unfold dotProduct
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.add_apply]; ring

/-- Bilinearity of `dotProduct` in the right slot under subtraction:
`v ⬝ (w₁ − w₂) = v ⬝ w₁ − v ⬝ w₂`. -/
private lemma euclideanDot_sub_right (v w₁ w₂ : Fin d → ℝ) :
    v ⬝ (w₁ - w₂) = v ⬝ w₁ - v ⬝ w₂ := by
  unfold dotProduct
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.sub_apply]; ring

/-- Bilinearity of `dotProduct` in the left slot under subtraction:
`(v₁ − v₂) ⬝ w = v₁ ⬝ w − v₂ ⬝ w`. -/
private lemma euclideanDot_sub_left (v₁ v₂ w : Fin d → ℝ) :
    (v₁ - v₂) ⬝ w = v₁ ⬝ w - v₂ ⬝ w := by
  unfold dotProduct
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.sub_apply]; ring

/-! ## Pointwise LL-monotonicity for `H^ε` -/

/-- **Paper `lem:H.delta.monotone`, pointwise algebraic content**
(line 1766–1777).

The pure algebraic step of the LL-monotonicity proof for `H^ε`: given

* `Hinner` — the LL inequality for `H` at the **inner** points
  `(p_i − q_i, m_i)` (the conclusion of `HypothesisMonotone.monotone`
  applied at `(p_1 − q_1, m_1)` and `(p_2 − q_2, m_2)`),
* `Hform_i` — the inf-conv formula
  `H^ε(x, p_i, m_i) = H(x, p_i − q_i, m_i) + (1/ε) K(q_i)`
  (eq. `eq:H-epsilon-formula`),
* `DpHε_form_i` — the gradient formula
  `DpHε(x, p_i, m_i) = DpH(x, p_i − q_i, m_i)`
  (eq. `eq:DpH-epsilon-formula`),
* `subgrad_1_at_2` — the subgradient inequality
  `DpH(x, p_1 − q_1, m_1) ⬝ (q_2 − q_1) ≤ (1/ε)(K(q_2) − K(q_1))`,
* `subgrad_2_at_1` — the symmetric inequality
  `DpH(x, p_2 − q_2, m_2) ⬝ (q_1 − q_2) ≤ (1/ε)(K(q_1) − K(q_2))`,

both of `m_1, m_2 > 0`, the LL inequality for `(H^ε, DpHε)` at
`((p_1, m_1), (p_2, m_2))` holds.

The proof: the LHS of the LL inequality for `H^ε` equals
`(LL inequality for H at inner points)`
` + m_1 · ((1/ε)(K(q_2) − K(q_1)) − DpH(p_1 − q_1) ⬝ (q_2 − q_1))`
` + m_2 · ((1/ε)(K(q_1) − K(q_2)) − DpH(p_2 − q_2) ⬝ (q_1 − q_2))`,
each of which is non-negative. -/
lemma Hdelta_monotone_pointwise
    {ε : ℝ}
    {Hε : (Fin d → ℝ) → ℝ → ℝ} -- H^ε(p, m) at fixed `x`
    {DpHε : (Fin d → ℝ) → ℝ → (Fin d → ℝ)} -- D_pH^ε(p, m) at fixed `x`
    {Hin : (Fin d → ℝ) → ℝ → ℝ} -- H(·, ·, m) at the inner argument
    {DpHin : (Fin d → ℝ) → ℝ → (Fin d → ℝ)} -- DpH(·, ·, m) at the inner argument
    {Kfun : (Fin d → ℝ) → ℝ} -- K
    (p₁ : Fin d → ℝ) (m₁ : ℝ) (p₂ : Fin d → ℝ) (m₂ : ℝ)
    (q₁ q₂ : Fin d → ℝ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (Hform₁ : Hε p₁ m₁ = Hin (p₁ - q₁) m₁ + (1 / ε) * Kfun q₁)
    (Hform₂ : Hε p₂ m₂ = Hin (p₂ - q₂) m₂ + (1 / ε) * Kfun q₂)
    (DpHε_form₁ : DpHε p₁ m₁ = DpHin (p₁ - q₁) m₁)
    (DpHε_form₂ : DpHε p₂ m₂ = DpHin (p₂ - q₂) m₂)
    (Hinner :
      0 ≤ (-Hin (p₁ - q₁) m₁ + Hin (p₂ - q₂) m₂) * (m₁ - m₂)
            + (m₁ • DpHin (p₁ - q₁) m₁ - m₂ • DpHin (p₂ - q₂) m₂) ⬝
                ((p₁ - q₁) - (p₂ - q₂)))
    (subgrad_1_at_2 :
      DpHin (p₁ - q₁) m₁ ⬝ (q₂ - q₁) ≤ (1 / ε) * (Kfun q₂ - Kfun q₁))
    (subgrad_2_at_1 :
      DpHin (p₂ - q₂) m₂ ⬝ (q₁ - q₂) ≤ (1 / ε) * (Kfun q₁ - Kfun q₂)) :
    0 ≤ (-Hε p₁ m₁ + Hε p₂ m₂) * (m₁ - m₂)
          + (m₁ • DpHε p₁ m₁ - m₂ • DpHε p₂ m₂) ⬝ (p₁ - p₂) := by
  -- Substitute the formulae for `H^ε` and `D_pH^ε`.
  rw [Hform₁, Hform₂, DpHε_form₁, DpHε_form₂]
  -- Abbreviate the inner quantities and dot products as named reals.
  set A₁ : ℝ := Hin (p₁ - q₁) m₁ with hA₁def
  set A₂ : ℝ := Hin (p₂ - q₂) m₂ with hA₂def
  set G₁ : Fin d → ℝ := DpHin (p₁ - q₁) m₁ with hG₁def
  set G₂ : Fin d → ℝ := DpHin (p₂ - q₂) m₂ with hG₂def
  set K₁ : ℝ := Kfun q₁ with hK₁def
  set K₂ : ℝ := Kfun q₂ with hK₂def
  -- Inner dot products as named reals.
  set d12 : ℝ := (m₁ • G₁ - m₂ • G₂) ⬝ ((p₁ - q₁) - (p₂ - q₂)) with hd12
  set s12 : ℝ := G₁ ⬝ (q₂ - q₁) with hs12def
  set s21 : ℝ := G₂ ⬝ (q₁ - q₂) with hs21def
  -- Key algebraic identity: `p₁ - p₂ = ((p₁ - q₁) - (p₂ - q₂)) + (q₁ - q₂)`.
  have hsplit : p₁ - p₂ = ((p₁ - q₁) - (p₂ - q₂)) + (q₁ - q₂) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  -- Expand the dot product along this split.
  have hexpand_p :
      (m₁ • G₁ - m₂ • G₂) ⬝ (p₁ - p₂)
        = d12 + (m₁ • G₁ - m₂ • G₂) ⬝ (q₁ - q₂) := by
    rw [hsplit, euclideanDot_add_right]
  -- Expand `(m₁ • G₁ - m₂ • G₂) ⬝ (q₁ - q₂) = m₁ * (G₁ ⬝ (q₁-q₂)) - m₂ * (G₂ ⬝ (q₁-q₂))`.
  have hbar :
      (m₁ • G₁ - m₂ • G₂) ⬝ (q₁ - q₂)
        = m₁ * (G₁ ⬝ (q₁ - q₂)) - m₂ * (G₂ ⬝ (q₁ - q₂)) := by
    rw [euclideanDot_sub_left]
    rw [euclideanDot_smul_left, euclideanDot_smul_left]
  -- Express `G₁ ⬝ (q₁ - q₂) = -s12` and `G₂ ⬝ (q₁ - q₂) = s21`.
  have hflip₁ : G₁ ⬝ (q₁ - q₂) = -s12 := by
    have hq : q₁ - q₂ = -(q₂ - q₁) := by
      ext i; simp only [Pi.sub_apply, Pi.neg_apply]; ring
    unfold dotProduct at *
    -- `∑ i, G₁ i * (q₁ - q₂) i = -∑ i, G₁ i * (q₂ - q₁) i`.
    have : ∀ i, G₁ i * (q₁ - q₂) i = -(G₁ i * (q₂ - q₁) i) := by
      intro i
      simp only [Pi.sub_apply]
      ring
    calc (∑ i, G₁ i * (q₁ - q₂) i)
        = ∑ i, -(G₁ i * (q₂ - q₁) i) := Finset.sum_congr rfl (fun i _ => this i)
      _ = -(∑ i, G₁ i * (q₂ - q₁) i) := by rw [← Finset.sum_neg_distrib]
      _ = -s12 := by rw [hs12def]
  have hflip₂ : G₂ ⬝ (q₁ - q₂) = s21 := by rfl
  -- Now substitute everything and close by `linarith`.
  -- Target: 0 ≤ (-(A₁ + 1/ε * K₁) + (A₂ + 1/ε * K₂)) * (m₁ - m₂)
  --           + (m₁ • G₁ - m₂ • G₂) ⬝ (p₁ - p₂)
  -- Goal numeric:
  --   0 ≤ (-A₁ + A₂) * (m₁ - m₂) + d12     -- = Hinner
  --     + m₁ * ((1/ε) * (K₂ - K₁) - s12)   -- piece2
  --     + m₂ * ((1/ε) * (K₁ - K₂) - s21)   -- piece3
  have hHinner_named : 0 ≤ (-A₁ + A₂) * (m₁ - m₂) + d12 := Hinner
  have hsub1 : s12 ≤ (1 / ε) * (K₂ - K₁) := subgrad_1_at_2
  have hsub2 : s21 ≤ (1 / ε) * (K₁ - K₂) := subgrad_2_at_1
  have piece2 : 0 ≤ m₁ * ((1 / ε) * (K₂ - K₁) - s12) :=
    mul_nonneg (le_of_lt hm₁) (by linarith)
  have piece3 : 0 ≤ m₂ * ((1 / ε) * (K₁ - K₂) - s21) :=
    mul_nonneg (le_of_lt hm₂) (by linarith)
  -- Rewrite the goal in terms of d12, s12, s21, A₁, A₂, K₁, K₂.
  rw [hexpand_p, hbar, hflip₁, hflip₂]
  -- The goal is now an algebraic identity in named reals.
  linarith [hHinner_named, piece2, piece3]

/-! ## Main result: `HypothesisMonotone` for `(Hdelta, DpHε)` -/

/-- **Carrier-generic LL-monotonicity producer** (paper `lem:H.delta.monotone`,
line 1754). Abstracts `Hdelta_monotone` over an arbitrary regularized
Hamiltonian carrier `Hε`. The only place the genuine `Hdelta` value enters
the proof is the inf-conv formula `hHform`; here that formula is restated for
the carrier `Hε` (valid on `{0<m}`, where every Theorem 3 consumer lives),
and a bridge `hHbridge : Hε x p m = Hdelta h ε x p m` on `{0<m}` reconciles
the carrier value with the genuine `Hdelta` value the algebraic core uses.

Both `Hε := Hdelta h ε` (with the trivial `rfl` bridge) and the junk-valued
`Hε := HdeltaPos h ε` (with `HdeltaPos_eq_Hdelta_of_pos` as the bridge) are
instances, so the `hMeasNeg`-free `HdeltaPos` carrier threads the downstream
Banach chain unchanged. The carrier is observably identical to `Hdelta` on
`{0<m}`, so the algebraic monotonicity identity is unaffected. -/
theorem Hepsilon_monotone_generic
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : HypothesisMonotone (d := d) H DpH)
    {ε : ℝ} (_hε : 0 < ε)
    (Hε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (qOf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) Hε DpHε)
    -- Bridge: the carrier equals the genuine `Hdelta` on the strict-positivity
    -- cone `{0<m}` (`rfl` for `Hdelta`, `HdeltaPos_eq_Hdelta_of_pos` for `HdeltaPos`).
    (hHbridge : ∀ x p m, 0 < m → Hε x p m = Hdelta h ε x p m)
    (hHform :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta h ε x p m
            = H x (p - qOf x p m) m + (1 / ε) * K h (qOf x p m))
    (hDpHε_form :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → DpHε x p m = DpH x (p - qOf x p m) m)
    (hSub :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → ∀ q : Fin d → ℝ,
          DpH x (p - qOf x p m) m ⬝ (q - qOf x p m)
            ≤ (1 / ε) * (K h q - K h (qOf x p m)))
    (hFtcSlice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          (DpHε x p m) ⬝ p - (Hε x p m - Hε x (0 : Fin d → ℝ) m)
            = ∫ t in (0 : ℝ)..1,
                ((DpHε x p m - DpHε x (t • p) m) ⬝ p)) :
    HypothesisMonotone (d := d) Hε DpHε :=
  { toRegularityH := hReg
    lagr_ftc_slice := hFtcSlice
    monotone := by
      filter_upwards [hMono.monotone, hHform, hDpHε_form, hSub]
        with x hxLL hxHform hxDpHε hxSub
      intro p₁ m₁ p₂ m₂ hm₁ hm₂
      -- Specialize the inner LL inequality at `(p_i - qOf …, m_i)`.
      have hInner :=
        hxLL (p₁ - qOf x p₁ m₁) m₁ (p₂ - qOf x p₂ m₂) m₂ hm₁ hm₂
      -- Reconcile the carrier value with the genuine `Hdelta` value on `{0<m}`.
      have hHf₁ : Hε x p₁ m₁
          = H x (p₁ - qOf x p₁ m₁) m₁ + (1 / ε) * K h (qOf x p₁ m₁) := by
        rw [hHbridge x p₁ m₁ hm₁]; exact hxHform p₁ m₁ hm₁
      have hHf₂ : Hε x p₂ m₂
          = H x (p₂ - qOf x p₂ m₂) m₂ + (1 / ε) * K h (qOf x p₂ m₂) := by
        rw [hHbridge x p₂ m₂ hm₂]; exact hxHform p₂ m₂ hm₂
      have hDf₁ := hxDpHε p₁ m₁ hm₁
      have hDf₂ := hxDpHε p₂ m₂ hm₂
      have hSub₁ := hxSub p₁ m₁ hm₁ (qOf x p₂ m₂)
      have hSub₂ := hxSub p₂ m₂ hm₂ (qOf x p₁ m₁)
      -- Invoke the pointwise algebraic lemma.
      exact Hdelta_monotone_pointwise (ε := ε)
        (Hε := fun p m => Hε x p m)
        (DpHε := fun p m => DpHε x p m)
        (Hin := fun s m => H x s m)
        (DpHin := fun s m => DpH x s m)
        (Kfun := fun q => K h q)
        p₁ m₁ p₂ m₂ (qOf x p₁ m₁) (qOf x p₂ m₂) hm₁ hm₂
        hHf₁ hHf₂ hDf₁ hDf₂ hInner hSub₁ hSub₂ }

/-- **Paper `lem:H.delta.monotone`** (line 1754, eq. `h-epsilon-mon`).

Under `HypothesisMonotone H DpH` and `HypothesisWeakGrowth H DpH`, for
every `ε > 0` and every candidate regularized gradient `DpHε` that
satisfies the inf-conv formula `eq:DpH-epsilon-formula` and the
subgradient inequality (first inclusion in `eq:inf-conv.diff-relation1`)
on the same a.e. set as `monotone` holds, the regularized pair
`(Hdelta h ε, DpHε)` satisfies the LL-monotonicity hypothesis.

The candidate `DpHε`, the per-`(x, p, m)` minimizer `qOf`, the formulae
`hHform`, `hDpHε_form`, and the subgradient inequality `hSub` are
passed as hypotheses, matching the codebase pattern of
`Hdelta_gradient_upper_bound` and `mDpHdelta_hat0` (which similarly
abstract over a candidate `DpHε`). The basic regularity fields of
`HypothesisMonotone` (extending `RegularityH`) are likewise passed in
through `hReg`. Thin wrapper around `Hepsilon_monotone_generic` at
`Hε := Hdelta h ε` with the trivial `rfl` bridge. -/
theorem Hdelta_monotone
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : HypothesisMonotone (d := d) H DpH)
    {ε : ℝ} (_hε : 0 < ε)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (qOf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) (Hdelta h ε) DpHε)
    (hHform :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta h ε x p m
            = H x (p - qOf x p m) m + (1 / ε) * K h (qOf x p m))
    (hDpHε_form :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → DpHε x p m = DpH x (p - qOf x p m) m)
    (hSub :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → ∀ q : Fin d → ℝ,
          DpH x (p - qOf x p m) m ⬝ (q - qOf x p m)
            ≤ (1 / ε) * (K h q - K h (qOf x p m)))
    -- Paper FTC-slice identity for the regularized pair `(Hδ, DpHε)`
    -- (`eq:DpHdelta.dotp.minusH`, derived as in `lem:A1+anyother`;
    -- tex line 1815). Mirrors `hHform`/`hDpHε_form`/`hSub`: it is the
    -- bridged form of the paper-proven slice identity, supplied at the
    -- producer interface (the regularized Hamiltonian's `D_pHε` is the
    -- `p`-gradient of `Hδ` along `[0, p]`).
    (hFtcSlice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          (DpHε x p m) ⬝ p - (Hdelta h ε x p m - Hdelta h ε x (0 : Fin d → ℝ) m)
            = ∫ t in (0 : ℝ)..1,
                ((DpHε x p m - DpHε x (t • p) m) ⬝ p)) :
    HypothesisMonotone (d := d) (Hdelta h ε) DpHε :=
  Hepsilon_monotone_generic (h := h) (hMono := hMono) (_hε := _hε)
    (Hε := Hdelta h ε) DpHε qOf hReg
    (fun _ _ _ _ => rfl) hHform hDpHε_form hSub hFtcSlice

/-! ## Unit-test sanity check

We verify the lemma signature at the trivially-zero Hamiltonian
`H ≡ 0`, `DpH ≡ 0`, with `qOf ≡ 0` and `DpHε ≡ 0`. Most hypotheses
collapse to `0 ≤ 0` or `0 = 0`. -/

/-- Unit test: `Hdelta_monotone` instantiates at the trivial choices
`H = 0`, `DpH = 0`, `DpHε = 0`, `qOf = 0`. The inf-conv formula and the
subgradient inequality both reduce to `0 ≤ 0` / `0 = 0`, and the
regularity bundle is the trivial one. -/
example
    (h : HypothesisWeakGrowth (d := d)
            (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)))
    (hMono : HypothesisMonotone (d := d)
              (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)))
    {ε : ℝ} (hε : 0 < ε)
    (hReg : RegularityH (d := d)
              (Hdelta h ε) (fun (_ _ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ)))
    (hHform :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta h ε x p m
            = (fun _ _ _ => (0 : ℝ)) x (p - (0 : Fin d → ℝ)) m
              + (1 / ε) * K h (0 : Fin d → ℝ)) :
    HypothesisMonotone (d := d)
      (Hdelta h ε)
      (fun (_ _ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ)) :=
  Hdelta_monotone h hMono hε
    (DpHε := fun (_ _ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ))
    (qOf := fun (_ _ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ))
    hReg
    hHform
    (Filter.Eventually.of_forall (fun _ _ _ _ => rfl))
    (Filter.Eventually.of_forall (by
      intro _ _ _ _ q
      -- LHS: `(fun _ _ _ => 0) x (p - 0) m ⬝ (q - 0) = 0 ⬝ q = 0`.
      -- RHS: `(1/ε) * (K h q - K h 0) = (1/ε) * (K h q - 0) ≥ 0`.
      have hK0 : K h (0 : Fin d → ℝ) = 0 := K_zero h
      have hKq : 0 ≤ K h q := K_nonneg h q
      have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt (one_div_pos.mpr hε)
      have : (0 : Fin d → ℝ) ⬝ (q - (0 : Fin d → ℝ)) = 0 :=
        euclideanDot_zero_left _
      rw [this, hK0]
      have hKq' : 0 ≤ (1 / ε) * (K h q - 0) := by
        have : 0 ≤ K h q - 0 := by linarith
        exact mul_nonneg hε_inv_nn this
      exact hKq'))
    -- `hFtcSlice`: both `Hδ x p m` and `Hδ x 0 m` equal `(1/ε) K(0) = 0`
    -- via `hHform`, and `DpHε ≡ 0`, so both sides reduce to `0`.
    (by
      filter_upwards [hHform] with x hx
      intro p m hm
      have hp := hx p m hm
      have h0 := hx (0 : Fin d → ℝ) m hm
      simp only [euclideanDot_zero_left, sub_zero] at hp h0 ⊢
      rw [hp, h0]
      simp)

end InfimalConvolution
end StationaryMFG
