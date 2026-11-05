module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.MuAux
public import StationaryMFG.Theorems.Congestion.MuIntegrability
public import StationaryMFG.Theorems.Congestion.MuRe
public import StationaryMFG.Theorems.Congestion.Domain
public import StationaryMFG.Theorems.Congestion.Existence
public import StationaryMFG.Solutions.Weak
public import StationaryMFG.Solutions.Strong

@[expose] public section

/-!
# Pointwise identity `(μ - m)·(-k + u + H(·, Du, μ) - V) = 0`

This module exposes the paper-named pointwise identity used in the
strong-implies-strong step of the congestion-growth argument
(`Source/FGU-monotone_revised.tex`, eq. `eq:mu-minus-m-formula`,
line 1437):

```
(μ(x) - m(x)) · (-k + u(x) + H(x, Du(x), μ(x)) - V(x)) = 0   for a.e. x.
```

Here `μ` is the auxiliary function `muAux` defined in
`StationaryMFG.Theorems.Congestion.MuAux`. The full proof — case
split on `μ(x) > m(x)` versus `μ(x) = m(x)`, with the strict case
using continuity-and-monotonicity of `H` in the third slot
(paper line 1439) — is carried out in `MuAux.muAux_product_identity`.
This module restates that result under the paper's name
`mu_minus_m_formula` so that downstream consumers of the congestion
strong-implies-strong argument can refer to it directly.

## Paper reference

`Source/FGU-monotone_revised.tex`, eq. `eq:mu-minus-m-formula`,
line 1437; supporting argument on line 1439.
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.Strong
open StationaryMFG.Solutions.MFG
open scoped ENNReal

variable {d : ℕ}

/-- **Pointwise identity** (paper eq. `eq:mu-minus-m-formula`, line 1437).

For almost every `x : 𝕋^d`, the auxiliary function `μ = muAux k m u V Du H`
satisfies

```
(μ(x) - m(x)) · (-k + u(x) + H(x, Du(x), μ(x)) - V(x)) = 0.
```

The proof (paper line 1439) proceeds by case split on the first
factor:

* if `μ(x) = m(x)`, the identity is trivial;
* if `μ(x) > m(x)`, then since the infimum is attained the HJB
  constraint `u + H(·, Du, μ) - V ≤ k` holds, and continuity of
  `H(x, Du x, ·)` rules out strict inequality (a strictly smaller
  candidate `μ(x) - ε > m(x)` would otherwise still lie in the
  constraint set, contradicting infimumness).

This is a thin restatement of `muAux_product_identity` from
`StationaryMFG.Theorems.Congestion.MuAux`. -/
theorem mu_minus_m_formula
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAux k m u V Du H x - m x) *
        (-k + u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x) = 0 :=
  muAux_product_identity hae_cont hae_ne hae_m_nn

/-! ## Step 1 of paper Lemma `lem:weak.is.strong` — HJB inequality
`eq:congest.HJleq0`

Paper `Source/FGU-monotone_revised.tex`, lines 1397, 1424–1470.

We formalise the conclusion that any pair `(m, u)` solving the
variational inequality `eq:weak.epsi.cong` (encoded by
`StationaryMFG.Solutions.Weak.IsWeakSolution`) automatically satisfies
the Hamilton–Jacobi inequality

```
u(x) + H(x, Du(x), m(x)) - V(x) ≤ 0   for a.e. x ∈ 𝕋^d.
```

The argument has three substantive ingredients (cf. paper lines 1429–1470):

1. **Per-`k` reduction (`weak_is_strong_HJB_le_at_k`).** Fix `k > 0` and
   let `μ := muAux k m u V Du H` be the auxiliary correction of paper
   `eq:mu-definition` (formalised in
   `StationaryMFG.Theorems.Congestion.MuAux`). Two analytical inputs
   are bundled as hypotheses (mirroring the pattern of
   `WellDefined.lean` and `MuIntegrability.lean`):

   * the *post-DCT* outcome of testing `eq:weak.epsi.cong` against the
     truncated pair `(μ_δ, u)` and sending `δ → 0⁺` — namely
     `∫ (u + H(·, Du, μ) - V)(μ - m) dx ≤ 0` (paper line 1467); and
   * the integrability `μ - m ∈ L¹_per`.

   Combined with the pointwise product identity
   `(μ - m)(-k + u + H(·, Du, μ) - V) = 0`
   (`muAux_product_identity`) and the constraint `μ ≥ m` (from the
   defining infimum), they force `k · ∫(μ - m) dx ≤ 0`, hence — since
   `k > 0` and `μ ≥ m` — `μ = m` a.e. Substituting in the constraint
   `u + H(·, Du, μ) - V ≤ k` yields the per-`k` bound.

2. **Limit `k → 0⁺` (`weak_is_strong_HJB_le`).** Apply
   `weak_is_strong_HJB_le_at_k` along the sequence `k_n := 1/(n+1)`.
   Intersect the resulting countable family of a.e. statements via
   `ae_all_iff`, then send `n → ∞` pointwise to obtain the desired
   inequality with `0` on the right-hand side.

The DCT/integrability hypothesis is delegated to the consumer (a future
task `infra-P5-mu-integrability-DCT` will discharge it from the uniform
`δ ≤ 1` envelopes already available in `MuIntegrability.lean`); the
present module focuses on the cleaner *combinatorial* step of going
from those analytical facts to the headline a.e. inequality. This
mirrors the modular policy adopted in `WellDefined.lean`. -/

/-- **Step 1 per-`k` HJB inequality.** Given the *post-DCT* and
integrability conclusions of paper line 1467 packaged as hypotheses,
together with the structural facts about `muAux` from
`MuAux.lean`, deduce `u + H(·, Du, m) - V ≤ k` a.e. on the unit cube.

Concretely (with `μ := muAux k m u V Du H`):

* `hk` — `k > 0` (paper line 1431).
* `hae_cont`, `hae_ne`, `hae_m_nn` — the standing hypotheses of
  `muAux_product_identity` (continuity of `H(x, Du x, ·)`,
  non-emptiness of the constraint set, non-negativity of `m`).
* `h_mu_ge_m` — `μ ≥ m` a.e. (a defining property of the infimum from
  `eq:mu-definition`; a direct consequence of `hae_ne`).
* `h_diff_int` — `μ - m ∈ L¹_per` (integrability of the difference).
* `h_DCT` — `∫(u + H(·, Du, μ) - V)(μ - m) dx ≤ 0` (the conclusion of
  paper eq. `eq:hjb-test-mu.delta` after DCT).
* `h_HJB_at_mu` — the defining HJB constraint `u + H(·, Du, μ) - V ≤ k`
  a.e. (paper line 1432, infimum-attained when the constraint set is
  closed and bounded below, formalised via `muAuxSet_isClosed`).

The conclusion `u + H(·, Du, m) - V ≤ k` (paper line 1470) follows
from `μ = m` a.e., which is the substantive content of the chain. -/
theorem weak_is_strong_HJB_le_at_k
    {k : ℝ} (hk : 0 < k)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (h_mu_ge_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        m x ≤ muAux k m u V Du H x)
    (h_diff_int :
      Integrable (fun x => muAux k m u V Du H x - m x)
        (volume.restrict (UnitCube d)))
    (h_DCT :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
            * (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0)
    (h_HJB_at_mu :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ k := by
  -- Set μ := muAux k m u V Du H for readability.
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  -- Step (a): the product identity (paper eq. `eq:mu-minus-m-formula`).
  have h_prod :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (μ x - m x) *
          (-k + u x + H x (fun i => Du i x) (μ x) - V x) = 0 :=
    muAux_product_identity (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) hae_cont hae_ne hae_m_nn
  -- Step (b): convert the product identity to
  --   `(u + H - V)(μ - m) = k (μ - m)` a.e.
  have h_prod_rewrite :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
          = k * (μ x - m x) := by
    filter_upwards [h_prod] with x hx
    -- `(μ - m)(-k + u + H - V) = 0` ⇒ either `μ = m` (both sides zero)
    -- or `u + H - V = k` (LHS = k(μ - m)).
    have : (μ x - m x) * (u x + H x (fun i => Du i x) (μ x) - V x)
              = (μ x - m x) * k := by
      have := hx
      nlinarith [hx]
    -- Re-shuffle.
    linarith [mul_comm (μ x - m x) (u x + H x (fun i => Du i x) (μ x) - V x),
               mul_comm (μ x - m x) k, this]
  -- Step (c): integrate the rewrite to get
  --   `∫ k (μ - m) ≤ 0`, i.e. `∫ (μ - m) ≤ 0`.
  have h_kint_le :
      ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_eq :
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
              * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ))
          = ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [h_prod_rewrite] with x hx
      exact hx
    rw [← h_eq]; exact h_DCT
  -- Step (d): factor `k` out and divide. Since `k > 0`, get `∫(μ - m) ≤ 0`.
  have h_int_le :
      ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_factor :
        ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ))
          = k * ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_const_mul (μ := volume.restrict (UnitCube d)) k _
    rw [h_factor] at h_kint_le
    -- `k > 0` and `k * I ≤ 0` ⇒ `I ≤ 0`.
    by_contra hpos
    have hpos' : 0 < ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) := lt_of_not_ge hpos
    have : 0 < k * ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) :=
      mul_pos hk hpos'
    linarith
  -- Step (e): combine `μ - m ≥ 0` a.e. and `∫(μ - m) ≤ 0` to get
  --   `μ - m = 0` a.e., i.e. `μ = m` a.e.
  have h_diff_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x - m x := by
    filter_upwards [h_mu_ge_m] with x hx; linarith
  -- The non-negative integrable function with non-positive integral is
  -- zero a.e.
  have h_int_eq :
      ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    have h_int_nn :
        0 ≤ ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) :=
      integral_nonneg_of_ae h_diff_nn
    linarith
  have h_mu_eq_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muAux k m u V Du H x = m x := by
    -- A non-negative integrable function with zero integral vanishes a.e.
    have h_diff_zero :
        (fun x => muAux k m u V Du H x - m x)
          =ᵐ[volume.restrict (UnitCube d)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_diff_nn h_diff_int).mp h_int_eq
    filter_upwards [h_diff_zero] with x hx
    have : muAux k m u V Du H x - m x = 0 := hx
    linarith
  -- Step (f): substitute `μ = m` in the constraint `u + H(·, Du, μ) - V ≤ k`.
  filter_upwards [h_mu_eq_m, h_HJB_at_mu] with x hxeq hx_le
  -- `μ x = m x`, so `H(x, Du x, μ x) = H(x, Du x, m x)`.
  have h_H_eq :
      H x (fun i => Du i x) (muAux k m u V Du H x)
        = H x (fun i => Du i x) (m x) := by rw [hxeq]
  -- Unfold the local `set` abbreviation `μ` to `muAux k m u V Du H` so the
  -- substitution lands.
  change u x + H x (fun i => Du i x) (m x) - V x ≤ k
  have hx_le' : u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k := hx_le
  linarith [h_H_eq]

/-- **Positive-witness sibling of `weak_is_strong_HJB_le_at_k`** (on `{0 < m x}`).

Same conclusion as `weak_is_strong_HJB_le_at_k`, but the full-`ℝ` continuity
hypothesis is replaced by on-`(0,∞)` continuity of `H(x, Du x, ·)` together with
a.e. strict positivity `0 < m x`. The only use of continuity is via the product
identity, here routed through `muAux_product_identity_of_m_pos`. The original is
kept untouched. -/
theorem weak_is_strong_HJB_le_at_k_of_m_pos
    {k : ℝ} (hk : 0 < k)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (h_mu_ge_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        m x ≤ muAux k m u V Du H x)
    (h_diff_int :
      Integrable (fun x => muAux k m u V Du H x - m x)
        (volume.restrict (UnitCube d)))
    (h_DCT :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
            * (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0)
    (h_HJB_at_mu :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ k := by
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  -- Step (a): the product identity on `{0 < m x}`.
  have h_prod :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (μ x - m x) *
          (-k + u x + H x (fun i => Du i x) (μ x) - V x) = 0 :=
    muAux_product_identity_of_m_pos (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) hae_cont hae_ne hae_m_pos
  -- Step (b): convert the product identity to `(u + H - V)(μ - m) = k (μ - m)`.
  have h_prod_rewrite :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
          = k * (μ x - m x) := by
    filter_upwards [h_prod] with x hx
    have : (μ x - m x) * (u x + H x (fun i => Du i x) (μ x) - V x)
              = (μ x - m x) * k := by
      nlinarith [hx]
    linarith [mul_comm (μ x - m x) (u x + H x (fun i => Du i x) (μ x) - V x),
               mul_comm (μ x - m x) k, this]
  -- Step (c): integrate the rewrite to get `∫ k (μ - m) ≤ 0`.
  have h_kint_le :
      ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_eq :
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
              * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ))
          = ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [h_prod_rewrite] with x hx
      exact hx
    rw [← h_eq]; exact h_DCT
  -- Step (d): divide by `k > 0` to get `∫(μ - m) ≤ 0`.
  have h_int_le :
      ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_factor :
        ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ))
          = k * ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_const_mul (μ := volume.restrict (UnitCube d)) k _
    rw [h_factor] at h_kint_le
    by_contra hpos
    have hpos' : 0 < ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) := lt_of_not_ge hpos
    have : 0 < k * ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) :=
      mul_pos hk hpos'
    linarith
  -- Step (e): `μ - m ≥ 0` a.e. and `∫(μ - m) ≤ 0` ⇒ `μ = m` a.e.
  have h_diff_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x - m x := by
    filter_upwards [h_mu_ge_m] with x hx; linarith
  have h_int_eq :
      ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    have h_int_nn :
        0 ≤ ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) :=
      integral_nonneg_of_ae h_diff_nn
    linarith
  have h_mu_eq_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muAux k m u V Du H x = m x := by
    have h_diff_zero :
        (fun x => muAux k m u V Du H x - m x)
          =ᵐ[volume.restrict (UnitCube d)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_diff_nn h_diff_int).mp h_int_eq
    filter_upwards [h_diff_zero] with x hx
    have : muAux k m u V Du H x - m x = 0 := hx
    linarith
  -- Step (f): substitute `μ = m` in the constraint.
  filter_upwards [h_mu_eq_m, h_HJB_at_mu] with x hxeq hx_le
  have h_H_eq :
      H x (fun i => Du i x) (muAux k m u V Du H x)
        = H x (fun i => Du i x) (m x) := by rw [hxeq]
  change u x + H x (fun i => Du i x) (m x) - V x ≤ k
  have hx_le' : u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k := hx_le
  linarith [h_H_eq]

/-- **Nonnegativity-witness sibling of `weak_is_strong_HJB_le_at_k`** (route (a),
paper lines 1417–1506).

Same conclusion as `weak_is_strong_HJB_le_at_k`, but the full-`ℝ` continuity
hypothesis is replaced by on-`(0,∞)` continuity of `H(x, Du x, ·)` together with
mere a.e. **non-negativity** `0 ≤ m x` (NOT strict `0 < m x`). The only use of
continuity is via the product identity, here routed through child-1's
`muAux_product_identity_of_m_nonneg_ae` (paper line 1437, the δ-truncation route).
The original `_pos` sibling and the base lemma are kept untouched.

This is the per-`k` foundation of route (a): the strict-positivity assumption on
`m`/`μ` is dropped, and the boundary set `{m x = 0}` is handled inside the
product identity (the `μ x = m x` case makes the first factor vanish; the
perturbation stays in `Ioi 0` since the perturbed point is `> m x ≥ 0`). -/
theorem weak_is_strong_HJB_le_at_k_of_m_nonneg
    {k : ℝ} (hk : 0 < k)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (h_mu_ge_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        m x ≤ muAux k m u V Du H x)
    (h_diff_int :
      Integrable (fun x => muAux k m u V Du H x - m x)
        (volume.restrict (UnitCube d)))
    (h_DCT :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
            * (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0)
    (h_HJB_at_mu :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ k := by
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  -- Step (a): the product identity from child-1 (only `0 ≤ m` + `Ioi 0` cont.).
  have h_prod :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (μ x - m x) *
          (-k + u x + H x (fun i => Du i x) (μ x) - V x) = 0 :=
    muAux_product_identity_of_m_nonneg_ae (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) hae_cont hae_ne hae_m_nn
  -- Step (b): convert to `(u + H - V)(μ - m) = k (μ - m)`.
  have h_prod_rewrite :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
          = k * (μ x - m x) := by
    filter_upwards [h_prod] with x hx
    have : (μ x - m x) * (u x + H x (fun i => Du i x) (μ x) - V x)
              = (μ x - m x) * k := by
      nlinarith [hx]
    linarith [mul_comm (μ x - m x) (u x + H x (fun i => Du i x) (μ x) - V x),
               mul_comm (μ x - m x) k, this]
  -- Step (c): integrate the rewrite to get `∫ k (μ - m) ≤ 0`.
  have h_kint_le :
      ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_eq :
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
              * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ))
          = ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [h_prod_rewrite] with x hx
      exact hx
    rw [← h_eq]; exact h_DCT
  -- Step (d): divide by `k > 0` to get `∫(μ - m) ≤ 0`.
  have h_int_le :
      ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_factor :
        ∫ x in UnitCube d, k * (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ))
          = k * ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_const_mul (μ := volume.restrict (UnitCube d)) k _
    rw [h_factor] at h_kint_le
    by_contra hpos
    have hpos' : 0 < ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) := lt_of_not_ge hpos
    have : 0 < k * ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) :=
      mul_pos hk hpos'
    linarith
  -- Step (e): `μ - m ≥ 0` a.e. and `∫(μ - m) ≤ 0` ⇒ `μ = m` a.e.
  have h_diff_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x - m x := by
    filter_upwards [h_mu_ge_m] with x hx; linarith
  have h_int_eq :
      ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    have h_int_nn :
        0 ≤ ∫ x in UnitCube d, (muAux k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) :=
      integral_nonneg_of_ae h_diff_nn
    linarith
  have h_mu_eq_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muAux k m u V Du H x = m x := by
    have h_diff_zero :
        (fun x => muAux k m u V Du H x - m x)
          =ᵐ[volume.restrict (UnitCube d)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_diff_nn h_diff_int).mp h_int_eq
    filter_upwards [h_diff_zero] with x hx
    have : muAux k m u V Du H x - m x = 0 := hx
    linarith
  -- Step (f): substitute `μ = m` in the constraint.
  filter_upwards [h_mu_eq_m, h_HJB_at_mu] with x hxeq hx_le
  have h_H_eq :
      H x (fun i => Du i x) (muAux k m u V Du H x)
        = H x (fun i => Du i x) (m x) := by rw [hxeq]
  change u x + H x (fun i => Du i x) (m x) - V x ≤ k
  have hx_le' : u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k := hx_le
  linarith [h_H_eq]

/-- **Step 1 of paper `lem:weak.is.strong`** (`eq:congest.HJleq0`,
paper line 1397).

Apply `weak_is_strong_HJB_le_at_k` along a sequence `k_n := 1/(n+1) > 0`
and intersect the a.e. statements: for every `n`,
`u + H(·, Du, m) - V ≤ 1/(n+1)` a.e., hence
`u + H(·, Du, m) - V ≤ 0` a.e.

The per-`k` analytical hypotheses are quantified over `k > 0` to keep
the headline statement uniform (paper line 1431 fixes an arbitrary
`k > 0` for the construction, and the conclusion is independent of `k`).
-/
theorem weak_is_strong_HJB_le
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h_perk :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          u x + H x (fun i => Du i x) (m x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- Build the sequence `k_n := 1/(n+1)`.
  set kSeq : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1) with hkSeqdef
  have hk_pos : ∀ n, 0 < kSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- For each n, get the a.e. statement at k_n.
  have h_each : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ kSeq n :=
    fun n => h_perk (kSeq n) (hk_pos n)
  -- Intersect over n via `ae_all_iff`.
  have h_all : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ n, u x + H x (fun i => Du i x) (m x) - V x ≤ kSeq n :=
    ae_all_iff.mpr h_each
  -- Pass to the limit n → ∞.
  filter_upwards [h_all] with x hx
  -- We have: for every n, `u + H - V ≤ 1/(n+1)`. Since `1/(n+1) → 0`,
  -- conclude `u + H - V ≤ 0`.
  have h_lim : Filter.Tendsto kSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The constant function `c := u x + H x (fun i => Du i x) (m x) - V x`
  -- is bounded above by `kSeq n` for every `n`, hence ≤ lim = 0.
  have h_const : Filter.Tendsto (fun _ : ℕ => u x + H x (fun i => Du i x) (m x) - V x)
      Filter.atTop (nhds (u x + H x (fun i => Du i x) (m x) - V x)) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' h_const h_lim hx

/-- **Step 1 assembler — per-`k` DCT family ⇒ HJB inequality at `0`.**

This is the connective tissue between `weak_is_strong_HJB_le_at_k`
(which discharges the per-`k` bound `u + H(·, Du, m) - V ≤ k` from the
DCT outcome and the structural `muAux` facts *at one fixed `k > 0`*) and
`weak_is_strong_HJB_le` (which sends `k → 0⁺` along `k_n = 1/(n+1)`).

The consumer supplies, **uniformly in `k > 0`**, the six structural
`muAux` hypotheses and the post-DCT integral inequality of paper
line 1467 (`h_DCT`). For each `k` we run `weak_is_strong_HJB_le_at_k`
to obtain `u + H(·, Du, m) - V ≤ k` a.e., then feed the resulting
`∀ k > 0`-family to `weak_is_strong_HJB_le` to get the headline
inequality with `0` on the right (paper `eq:congest.HJleq0`,
line 1397).

This is the final wiring of Step 1 of paper Lemma `lem:weak.is.strong`:
the `δ → 0` passage that produces each `h_DCT` is delivered by
`muAux_integral_tendsto` in the consumer, and the `muAux`-structural
hypotheses are the standing assumptions of `muAux_product_identity`
plus the infimum-attained constraint. No `sorry`, no oracle: both
constituents are proven theorems above. -/
theorem weak_is_strong_HJB_le_of_perk_DCT
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_mu_ge_m :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          m x ≤ muAux k m u V Du H x)
    (h_diff_int :
      ∀ k : ℝ, 0 < k →
        Integrable (fun x => muAux k m u V Du H x - m x)
          (volume.restrict (UnitCube d)))
    (h_DCT :
      ∀ k : ℝ, 0 < k →
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
              * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) ≤ 0)
    (h_HJB_at_mu :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- Per-`k` bound from `weak_is_strong_HJB_le_at_k`, then send `k → 0⁺`.
  refine weak_is_strong_HJB_le (V := V) (H := H) (Du := Du) (m := m) (u := u)
    (fun k hk => ?_)
  exact weak_is_strong_HJB_le_at_k hk hae_cont (hae_ne k hk) hae_m_nn
    (h_mu_ge_m k hk) (h_diff_int k hk) (h_DCT k hk) (h_HJB_at_mu k hk)

/-- **Positive-witness sibling of `weak_is_strong_HJB_le_of_perk_DCT`**
(on `{0 < m x}`). Same conclusion, but the full-`ℝ` continuity hypothesis is
replaced by on-`(0,∞)` continuity plus a.e. strict positivity `0 < m x`; the
per-`k` step is routed through `weak_is_strong_HJB_le_at_k_of_m_pos`. -/
theorem weak_is_strong_HJB_le_of_perk_DCT_of_m_pos
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_mu_ge_m :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          m x ≤ muAux k m u V Du H x)
    (h_diff_int :
      ∀ k : ℝ, 0 < k →
        Integrable (fun x => muAux k m u V Du H x - m x)
          (volume.restrict (UnitCube d)))
    (h_DCT :
      ∀ k : ℝ, 0 < k →
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
              * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) ≤ 0)
    (h_HJB_at_mu :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le (V := V) (H := H) (Du := Du) (m := m) (u := u)
    (fun k hk => ?_)
  exact weak_is_strong_HJB_le_at_k_of_m_pos hk hae_cont (hae_ne k hk) hae_m_pos
    (h_mu_ge_m k hk) (h_diff_int k hk) (h_DCT k hk) (h_HJB_at_mu k hk)

/-- **Nonnegativity-witness sibling of `weak_is_strong_HJB_le_of_perk_DCT`**
(route (a), paper lines 1417–1506). Same conclusion, but the full-`ℝ`
continuity hypothesis is replaced by on-`(0,∞)` continuity plus mere a.e.
**non-negativity** `0 ≤ m x`; the per-`k` step is routed through
`weak_is_strong_HJB_le_at_k_of_m_nonneg`. -/
theorem weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_mu_ge_m :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          m x ≤ muAux k m u V Du H x)
    (h_diff_int :
      ∀ k : ℝ, 0 < k →
        Integrable (fun x => muAux k m u V Du H x - m x)
          (volume.restrict (UnitCube d)))
    (h_DCT :
      ∀ k : ℝ, 0 < k →
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
              * (muAux k m u V Du H x - m x)
            ∂(volume : Measure (Fin d → ℝ)) ≤ 0)
    (h_HJB_at_mu :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le (V := V) (H := H) (Du := Du) (m := m) (u := u)
    (fun k hk => ?_)
  exact weak_is_strong_HJB_le_at_k_of_m_nonneg hk hae_cont (hae_ne k hk) hae_m_nn
    (h_mu_ge_m k hk) (h_diff_int k hk) (h_DCT k hk) (h_HJB_at_mu k hk)

/-! ## Regularity by-product (paper `eq:reg.pair.sol`, line 1407)

Paper `Source/FGU-monotone_revised.tex`, lines 1473–1474:

> Finally, we note that (eq:H-at-Du-mu.bounds) combined with `μ = m`
> yields (eq:reg.pair.sol).

I.e. once `μ = m` a.e. (the substantive content of
`paper:lem:weak.is.strong.a`, established inside
`weak_is_strong_HJB_le_at_k` above), the integrability conclusions
of `infra:P5-mu-integrability` for `μ`,

* `H(·, Du, μ) ∈ L^{β̄'}_per(𝕋^d)`,
* `|Du|^{α(1+τ/β)}/(μ^τ + 1) ∈ L^{β̄'}_per(𝕋^d)`,

transfer immediately to `m`, giving paper eq.~`eq:reg.pair.sol`:

* `H(·, Du, m) ∈ L^{β̄'}_per(𝕋^d)`,
* `|Du|^{α(1+τ/β)}/(m^τ + 1) ∈ L^{β̄'}_per(𝕋^d)`.

The proofs are one-line invocations of `MemLp.ae_eq` (Mathlib's
a.e.-equality transport for `MemLp`).

This regularity by-product is required as a prerequisite for
`infra:P5-mdelta-admissibility` in Step 3 of paper Lemma
`lem:weak.is.strong`.
-/

/-- **Paper `eq:reg.pair.sol` (line 1407), first clause** —
`H(·, Du, m) ∈ L^{β̄'}_per(𝕋^d)`.

Direct substitution of `μ = m` (a.e.) into the integrability
conclusion `MemLpPer β̄' (fun x => H x (Du x) (μ x))` produced by
`infra:P5-mu-integrability` (`muAux_H_mem_Lp`).

The hypothesis `h_mu_eq_m` packages the substantive
`paper:lem:weak.is.strong.a` content `μ = m` a.e., obtained inside
the proof of `weak_is_strong_HJB_le_at_k`. The hypothesis `hH_mu_mem`
is the conclusion of `muAux_H_mem_Lp`. -/
theorem weak_is_strong_regularity_H
    {betaBarPrime : ℝ≥0∞}
    {k : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h_mu_eq_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muAux k m u V Du H x = m x)
    (hH_mu_mem :
      MemLpPer (d := d) betaBarPrime
        (fun x => H x (fun i => Du i x) (muAux k m u V Du H x))) :
    MemLpPer (d := d) betaBarPrime
      (fun x => H x (fun i => Du i x) (m x)) := by
  -- A.e.-equality transports `MemLp`.
  have h_ae :
      (fun x => H x (fun i => Du i x) (muAux k m u V Du H x))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => H x (fun i => Du i x) (m x)) := by
    filter_upwards [h_mu_eq_m] with x hx
    simp [hx]
  exact MemLp.toMemLpPer ((MemLpPer.toMemLp hH_mu_mem).ae_eq h_ae)

/-- **Paper `eq:reg.pair.sol` (line 1407), second clause** —
`|Du|^{α(1+τ/β)}/(m^τ + 1) ∈ L^{β̄'}_per(𝕋^d)`.

Direct substitution of `μ = m` (a.e.) into the integrability
conclusion `MemLpPer β̄' (fun x => ‖Du x‖^{αt}/(μ^τ + 1))` produced
by `infra:P5-mu-integrability` (`muAux_integrability_quotient`). -/
theorem weak_is_strong_regularity_quotient
    {betaBarPrime : ℝ≥0∞}
    {α β τ : ℝ}
    {k : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h_mu_eq_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muAux k m u V Du H x = m x)
    (hQuot_mu_mem :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (muAux k m u V Du H x ^ τ + 1))) :
    MemLpPer (d := d) betaBarPrime
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
          (m x ^ τ + 1)) := by
  -- A.e.-equality transports `MemLp`.
  have h_ae :
      (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (muAux k m u V Du H x ^ τ + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x : Fin d → ℝ =>
            ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
              (m x ^ τ + 1)) := by
    filter_upwards [h_mu_eq_m] with x hx
    simp [hx]
  exact MemLp.toMemLpPer ((MemLpPer.toMemLp hQuot_mu_mem).ae_eq h_ae)

/-! ## Step 1, Sub-step A₀ — the DCT dominator's integrability
(`muAux_diff_integrable`)

Paper `Source/FGU-monotone_revised.tex`, line 1530: the dominated-convergence
passage `δ → 0⁺` needs an `L¹` dominator for the integrands
`(u + H(·, Du, max(μ, δ)) − V)(max(μ, δ) − m)`. The integrability of the
second-factor difference `μ − m` underwrites that dominator (the first factor
is bounded a.e. by `k + 1` along the truncation). We package the difference's
`L¹` membership as a standalone helper: it follows from `μ ∈ L^{β̄}_per` and
`m ∈ L^{β̄}_per` (with `β̄ ≥ 1`) by `MemLp.sub` and the finite-measure
Hölder inclusion `L^{β̄} ⊆ L¹`.

This also discharges the `h_diff_int` field of
`weak_is_strong_HJB_le_of_perk_DCT` once `μ = muAux k …`. -/

/-- **Step 1, Sub-step A₀ — `μ − m ∈ L¹_per`.**

If `μ` and `m` both lie in `L^{β̄}_per` with `1 ≤ β̄` (and `β̄ ≠ ⊤`), then
their difference is integrable on the unit cube. On the finite-measure cube,
`L^{β̄} ⊆ L¹` (Hölder inclusion), and `MemLp.sub` keeps the difference in
`L^{β̄}`; `MemLp.integrable` (at `p = 1`) closes the goal. -/
theorem muAux_diff_integrable
    {betaBar : ℝ≥0∞}
    (hβBar_one : 1 ≤ betaBar) (hβBar_top : betaBar ≠ ⊤)
    {μ m : (Fin d → ℝ) → ℝ}
    (hμ_Lp : MemLpPer (d := d) betaBar μ)
    (hm_Lp : MemLpPer (d := d) betaBar m) :
    Integrable (fun x => μ x - m x) (volume.restrict (UnitCube d)) := by
  -- `μ − m ∈ L^{β̄}_per` by `MemLp.sub`.
  have h_sub : MemLpPer (d := d) betaBar (fun x => μ x - m x) :=
    MemLp.toMemLpPer (hμ_Lp.toMemLp.sub hm_Lp.toMemLp)
  -- Hölder inclusion `L^{β̄} ⊆ L¹` on the finite-measure cube.
  have h_L1 : MemLpPer (d := d) 1 (fun x => μ x - m x) :=
    h_sub.mono_exponent_finite hβBar_one hβBar_top
  -- `MemLp` at `p = 1` is integrability.
  exact MeasureTheory.memLp_one_iff_integrable.mp h_L1.toMemLp

/-! ## Step 1, Sub-step A — `δ → 0` dominated-convergence limit
(`muAux_integral_tendsto`)

Paper `Source/FGU-monotone_revised.tex`, lines 1527–1533: the abstract
variational inequality is tested against the truncated density
`max(μ, δ)` for each `δ > 0`, yielding the per-`δ` integral inequality
```
∫ (u + H(·, Du, max(μ, δ)) − V)(max(μ, δ) − m) ≤ 0.
```
To pass to the limit `δ → 0⁺` we need the genuine analytical fact that
the per-`δ` integrals converge to the integral at `μ` itself.  Since
`μ ≥ 0`, for `δ_n → 0⁺` we have `max(μ x, δ_n) → μ x` pointwise; the
integrand then converges pointwise by continuity of `H(x, Du x, ·)`,
and Lebesgue dominated convergence (with an `L¹` dominator) delivers
convergence of the integrals.

This is the only genuinely analytic step in the `δ → 0` passage; the
surrounding VI/assembly wiring is delegated to the consumer in
`Existence.lean`. -/

/-- **Step 1, Sub-step A — the `δ → 0⁺` integral limit.**

Let `μ ≥ 0` a.e., let `δSeq` be a sequence of positive reals tending to
`0`, and write
```
gδ n x := (u x + H x (Du x) (max (μ x) (δSeq n)) − V x) · (max (μ x) (δSeq n) − m x),
gμ   x := (u x + H x (Du x) (μ x) − V x) · (μ x − m x).
```
Under continuity of `H(x, Du x, ·)`, measurability of each `gδ n`, and a
common integrable dominator `bound`, the integrals `∫ gδ n` converge to
`∫ gμ`.

The pointwise convergence `gδ n x → gμ x` is derived internally from
`max (μ x) (δSeq n) → μ x` (which holds because `δSeq → 0` and
`μ x ≥ 0`) and continuity of `H` in its third argument. -/
theorem muAux_integral_tendsto
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u μ : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x))
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x)‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
              * (max (μ x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (nhds
        (∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Pointwise convergence: `max (μ x) (δSeq n) → μ x` a.e., then propagate
  -- through `H` (continuous in the 3rd slot) and the algebraic combination.
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
              * (max (μ x) (δSeq n) - m x))
          Filter.atTop
          (nhds
            ((u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x))) := by
    filter_upwards [hμ_nn, hae_cont] with x hx_nn hx_cont
    -- `max (μ x) (δSeq n) → max (μ x) 0 = μ x` since `δSeq → 0` and `μ x ≥ 0`.
    have h_max_lim :
        Filter.Tendsto (fun n => max (μ x) (δSeq n)) Filter.atTop
          (nhds (μ x)) := by
      have h0 : max (μ x) (0 : ℝ) = μ x := max_eq_left hx_nn
      have := (tendsto_const_nhds (x := μ x)).max hδ_lim
      simpa [h0] using this
    -- Propagate through `H(x, Du x, ·)` (continuous), `u`, `V` (constants in n),
    -- and the second factor.
    have h_H_lim :
        Filter.Tendsto
          (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
          Filter.atTop (nhds (H x (fun i => Du i x) (μ x))) :=
      (hx_cont.tendsto (μ x)).comp h_max_lim
    have h_first :
        Filter.Tendsto
          (fun n => u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          Filter.atTop
          (nhds (u x + H x (fun i => Du i x) (μ x) - V x)) :=
      ((tendsto_const_nhds.add h_H_lim).sub tendsto_const_nhds)
    have h_second :
        Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
          (nhds (μ x - m x)) :=
      h_max_lim.sub tendsto_const_nhds
    exact h_first.mul h_second
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hmeas hbound_int hbound h_lim

/-- **Step 1, Sub-step A on `{0 < m x}` — positive-witness `δ → 0⁺` integral
limit.** Sibling of `muAux_integral_tendsto` (the original is kept untouched).

Here the full-ℝ continuity hypothesis is replaced by on-`(0,∞)` continuity of
`H(x, Du x, ·)` together with `0 < m x` and `m x ≤ μ x` a.e. On `{0 < m x}` the
limit point `μ x ≥ m x > 0` is interior to `Ioi 0`, and the truncation sequence
`max (μ x) (δSeq n) ≥ μ x > 0` stays in `Ioi 0`; so `ContinuousOn (Ioi 0)`
suffices for the pointwise `Tendsto` step driving dominated convergence. -/
theorem muAux_integral_tendsto_of_m_pos
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u μ : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)), m x ≤ μ x)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x))
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x)‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
              * (max (μ x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (nhds
        (∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Pointwise convergence on `{0 < m x}`: `max (μ x) (δSeq n) → μ x`, then
  -- propagate through `H` (continuous at the interior point `μ x ∈ Ioi 0`).
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
              * (max (μ x) (δSeq n) - m x))
          Filter.atTop
          (nhds
            ((u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x))) := by
    filter_upwards [hm_pos, hm_le_mu, hae_cont] with x hx_mpos hx_mle hx_cont
    -- `μ x ≥ m x > 0`, so `μ x` is interior to `Ioi 0`.
    have hμx_pos : (0 : ℝ) < μ x := lt_of_lt_of_le hx_mpos hx_mle
    have hμx_nn : (0 : ℝ) ≤ μ x := hμx_pos.le
    -- `max (μ x) (δSeq n) → max (μ x) 0 = μ x` since `δSeq → 0`.
    have h_max_lim :
        Filter.Tendsto (fun n => max (μ x) (δSeq n)) Filter.atTop
          (nhds (μ x)) := by
      have h0 : max (μ x) (0 : ℝ) = μ x := max_eq_left hμx_nn
      have := (tendsto_const_nhds (x := μ x)).max hδ_lim
      simpa [h0] using this
    -- Upgrade on-`Ioi 0` continuity to `ContinuousAt` at the interior `μ x`.
    have hμx_mem : μ x ∈ Set.Ioi (0 : ℝ) := hμx_pos
    have h_cont_at : ContinuousAt (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (μ x) :=
      (hx_cont (μ x) hμx_mem).continuousAt (isOpen_Ioi.mem_nhds hμx_mem)
    -- Propagate through `H(x, Du x, ·)`, `u`, `V`, and the second factor.
    have h_H_lim :
        Filter.Tendsto
          (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
          Filter.atTop (nhds (H x (fun i => Du i x) (μ x))) :=
      (h_cont_at.tendsto).comp h_max_lim
    have h_first :
        Filter.Tendsto
          (fun n => u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          Filter.atTop
          (nhds (u x + H x (fun i => Du i x) (μ x) - V x)) :=
      ((tendsto_const_nhds.add h_H_lim).sub tendsto_const_nhds)
    have h_second :
        Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
          (nhds (μ x - m x)) :=
      h_max_lim.sub tendsto_const_nhds
    exact h_first.mul h_second
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hmeas hbound_int hbound h_lim

/-- **Step 1, Sub-step A on `0 ≤ m x` — nonneg-witness `δ → 0⁺` integral limit.**
Sibling of `muAux_integral_tendsto`/`muAux_integral_tendsto_of_m_pos` (both kept
untouched), assuming only `0 ≤ m` (a.e.) and on-`(0,∞)` continuity of
`H(x, Du x, ·)`.

The pointwise `δ → 0⁺` limit driving dominated convergence is established by a
case split on the (a.e.-nonnegative) limit point `μ x`:

* If `0 < μ x` then `μ x` is interior to `Ioi 0` and `max (μ x) (δSeq n) → μ x`
  stays in `Ioi 0`, so on-`(0,∞)` continuity gives the limit exactly as in the
  positive-witness sibling.
* If `μ x = 0` then `0 ≤ m x ≤ μ x = 0` forces `m x = 0`, so the **target**
  integrand `(u + H(·,Du,0) − V)(0 − 0) = 0`, and the sequence integrand is
  `(u + H(·,Du,δSeq n) − V) · δSeq n`, whose first factor is bounded **uniformly
  in `n`** by `G1 x` (the `n`-independent envelope of the domination bound) while
  the second factor `δSeq n → 0`; hence the product `→ 0` by the squeeze. No
  continuity of `H` at the boundary `0` is used.

The uniform first-factor envelope is passed as `hf1_bd`; in the consumer it is
exactly the `|factor1| ≤ G1 x` estimate already produced for the dominator. -/
theorem muAux_integral_tendsto_of_m_nonneg
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u μ : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)), m x ≤ μ x)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (G1 : (Fin d → ℝ) → ℝ)
    (hf1_bd :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x)
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x))
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x)‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
              * (max (μ x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop
      (nhds
        (∫ x in UnitCube d,
            (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
            ∂(volume : Measure (Fin d → ℝ)))) := by
  -- Bundle the per-`n` first-factor bounds into a single a.e. statement.
  have hf1_all :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ n, |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x :=
    (ae_all_iff).mpr hf1_bd
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
              * (max (μ x) (δSeq n) - m x))
          Filter.atTop
          (nhds
            ((u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x))) := by
    filter_upwards [hm_nn, hμ_nn, hm_le_mu, hae_cont, hf1_all]
      with x hx_mnn hx_μnn hx_mle hx_cont hx_f1
    rcases eq_or_lt_of_le hx_μnn with hμ0 | hμpos
    · -- `μ x = 0` (so `m x = 0`): the target integrand vanishes, and the
      -- sequence is `first · δSeq n` with `|first| ≤ G1 x`, `δSeq n → 0`.
      have hμx0 : μ x = 0 := hμ0.symm
      have hmx0 : m x = 0 := le_antisymm (hμx0 ▸ hx_mle) hx_mnn
      -- Target value is `0`.
      have htarget0 :
          (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x) = 0 := by
        rw [hμx0, hmx0]; ring
      rw [htarget0]
      -- Second factor `max (μ x) (δSeq n) - m x = δSeq n` (since `μ x = m x = 0`
      -- and `δSeq n > 0` eventually; in fact `max 0 (δSeq n) = δSeq n` once
      -- `δSeq n ≥ 0`).  We prove the product `→ 0` by squeezing its absolute
      -- value between `0` and `G1 x · |δSeq n|`.
      have h_abs_le :
          ∀ n,
            |(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
                * (max (μ x) (δSeq n) - m x)|
              ≤ G1 x * |max (μ x) (δSeq n) - m x| := by
        intro n
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hx_f1 n) (abs_nonneg _)
      -- `max (μ x) (δSeq n) - m x → μ x - m x = 0`.
      have h_second :
          Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
            (nhds (μ x - m x)) := by
        have h0 : max (μ x) (0 : ℝ) = μ x := max_eq_left hx_μnn
        have hmax := (tendsto_const_nhds (x := μ x)).max hδ_lim
        rw [h0] at hmax
        exact hmax.sub tendsto_const_nhds
      have h_second0 :
          Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
            (nhds 0) := by
        have : μ x - m x = 0 := by rw [hμx0, hmx0]; ring
        rwa [this] at h_second
      -- `G1 x · |second| → G1 x · 0 = 0`.
      have h_upper :
          Filter.Tendsto
            (fun n => G1 x * |max (μ x) (δSeq n) - m x|) Filter.atTop (nhds 0) := by
        have habs : Filter.Tendsto (fun n => |max (μ x) (δSeq n) - m x|)
            Filter.atTop (nhds 0) := by
          have := (continuous_abs.tendsto (0 : ℝ)).comp h_second0
          simpa only [Function.comp_def, abs_zero] using this
        have := habs.const_mul (G1 x)
        simpa using this
      -- Squeeze the product to `0`.
      apply squeeze_zero_norm (fun n => ?_) h_upper
      simpa [Real.norm_eq_abs] using h_abs_le n
    · -- `0 < μ x`: interior limit point, on-`(0,∞)` continuity suffices.
      have hμx_pos : (0 : ℝ) < μ x := hμpos
      have hμx_nn : (0 : ℝ) ≤ μ x := hμx_pos.le
      have h_max_lim :
          Filter.Tendsto (fun n => max (μ x) (δSeq n)) Filter.atTop
            (nhds (μ x)) := by
        have h0 : max (μ x) (0 : ℝ) = μ x := max_eq_left hμx_nn
        have := (tendsto_const_nhds (x := μ x)).max hδ_lim
        simpa [h0] using this
      have hμx_mem : μ x ∈ Set.Ioi (0 : ℝ) := hμx_pos
      have h_cont_at : ContinuousAt (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (μ x) :=
        (hx_cont (μ x) hμx_mem).continuousAt (isOpen_Ioi.mem_nhds hμx_mem)
      have h_H_lim :
          Filter.Tendsto
            (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
            Filter.atTop (nhds (H x (fun i => Du i x) (μ x))) :=
        (h_cont_at.tendsto).comp h_max_lim
      have h_first :
          Filter.Tendsto
            (fun n => u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            Filter.atTop
            (nhds (u x + H x (fun i => Du i x) (μ x) - V x)) :=
        ((tendsto_const_nhds.add h_H_lim).sub tendsto_const_nhds)
      have h_second :
          Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
            (nhds (μ x - m x)) :=
        h_max_lim.sub tendsto_const_nhds
      exact h_first.mul h_second
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    bound hmeas hbound_int hbound h_lim

/-! ## Step 3 of paper Lemma `lem:weak.is.strong` — `m_δ`-admissibility
(`infra:P5-mdelta-admissibility`)

Paper `Source/FGU-monotone_revised.tex`, line 1527:

> We then set `m_δ := max{m, δ}` for `δ > 0` and observe that
> `(m_δ, u + φ) ∈ 𝓚` for arbitrary `φ ∈ C^∞(𝕋^d)` by
> `(eq:reg.pair.sol)` and because
> ```
> |Du + Dφ|^{αt} / (m_δ^τ + 1)
>   ≤ 2^{αt - 1} · (|Du|^{αt} / (m^τ + 1) + |Dφ|^{αt}).
> ```

The two ingredients of this membership claim are:

1. The **pointwise bound** on line 1528: a direct consequence of the
   convexity inequality `(a + b)^{αt} ≤ 2^{αt - 1}(a^{αt} + b^{αt})`
   for `αt ≥ 1` and `a, b ≥ 0`, together with `m_δ ≥ m` and
   `m^τ + 1 ≥ 1`. Formalised below as `mdelta_pointwise_bound`.

2. The **`MemLpPer` closure under domination** (Mathlib's
   `MemLp.mono'`): given that the RHS — which involves
   `|Du|^{αt}/(m^τ + 1) ∈ L^{β̄'}_per` (paper `eq:reg.pair.sol`,
   already formalised as `weak_is_strong_regularity_quotient`) and
   `|Dφ|^{αt} ∈ L^{β̄'}_per` (smooth periodic bounded ⇒ in any
   `L^p`) — is in `L^{β̄'}_per`, the LHS is too. -/

/-- **Convex `(a + b)^{αt} ≤ 2^{αt-1}(a^{αt} + b^{αt})`** for `a, b ≥ 0`
and `αt ≥ 1`. The real-valued counterpart of
`NNReal.rpow_add_le_mul_rpow_add_rpow`, lifted via `NNReal`. -/
private lemma rpow_add_le_two_pow_sub_one_mul_add
    {a b αt : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hαt : 1 ≤ αt) :
    (a + b) ^ αt ≤ (2 : ℝ) ^ (αt - 1) * (a ^ αt + b ^ αt) := by
  -- Lift to `NNReal` and use `NNReal.rpow_add_le_mul_rpow_add_rpow`.
  lift a to NNReal using ha with a' ha'
  lift b to NNReal using hb with b' hb'
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow a' b' hαt
  exact_mod_cast h

/-- **Pointwise bound from paper line 1528.** For `m ≥ 0`, `δ > 0`,
`τ ≥ 0`, `αt ≥ 1`, and arbitrary real vectors `a b : Fin d → ℝ`,
```
‖a + b‖^{αt} / (max(m, δ)^τ + 1)
  ≤ 2^{αt - 1} (‖a‖^{αt} / (m^τ + 1) + ‖b‖^{αt}).
```

In the application, `a = Du x`, `b = Dφ x`, and the `max(m, δ)` is the
truncation `m_δ`. The inequality is purely numerical: it does not
depend on periodicity. -/
theorem mdelta_pointwise_bound
    {m δ αt τ : ℝ} {a b : Fin d → ℝ}
    (hm : 0 ≤ m) (hδ : 0 < δ) (hτ : 0 ≤ τ) (hαt : 1 ≤ αt) :
    ‖a + b‖ ^ αt / ((max m δ) ^ τ + 1) ≤
      (2 : ℝ) ^ (αt - 1) *
        (‖a‖ ^ αt / (m ^ τ + 1) + ‖b‖ ^ αt) := by
  -- Step 1: `‖a + b‖^{αt} ≤ 2^{αt-1}(‖a‖^{αt} + ‖b‖^{αt})` via the
  -- triangle inequality `‖a + b‖ ≤ ‖a‖ + ‖b‖` followed by the convex
  -- inequality on the right (both sides nonnegative; `αt ≥ 1` makes
  -- `t ↦ t^{αt}` monotone on `[0, ∞)`).
  have hab_nn : 0 ≤ ‖a + b‖ := norm_nonneg _
  have ha_nn : 0 ≤ ‖a‖ := norm_nonneg _
  have hb_nn : 0 ≤ ‖b‖ := norm_nonneg _
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  have h_pow_le_sum :
      ‖a + b‖ ^ αt ≤ (‖a‖ + ‖b‖) ^ αt := by
    apply Real.rpow_le_rpow hab_nn htri (le_trans zero_le_one hαt)
  have h_sum_le :
      (‖a‖ + ‖b‖) ^ αt ≤
        (2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt + ‖b‖ ^ αt) :=
    rpow_add_le_two_pow_sub_one_mul_add ha_nn hb_nn hαt
  have h_top :
      ‖a + b‖ ^ αt ≤ (2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt + ‖b‖ ^ αt) :=
    le_trans h_pow_le_sum h_sum_le
  -- Step 2: bound the denominator. `m_δ = max(m, δ) ≥ m ≥ 0`, so
  -- `m_δ^τ ≥ m^τ` (for `τ ≥ 0`), hence `m_δ^τ + 1 ≥ m^τ + 1 > 0`.
  have hm_le_max : m ≤ max m δ := le_max_left _ _
  have hδ_le_max : δ ≤ max m δ := le_max_right _ _
  have hmax_pos : 0 < max m δ := lt_of_lt_of_le hδ hδ_le_max
  have hmax_nn : 0 ≤ max m δ := hmax_pos.le
  have hmτ_le : m ^ τ ≤ (max m δ) ^ τ :=
    Real.rpow_le_rpow hm hm_le_max hτ
  have hden_lhs_pos : 0 < (max m δ) ^ τ + 1 := by
    have : 0 ≤ (max m δ) ^ τ := Real.rpow_nonneg hmax_nn _
    linarith
  have hden_rhs_pos : 0 < m ^ τ + 1 := by
    have : 0 ≤ m ^ τ := Real.rpow_nonneg hm _
    linarith
  have hden_le : m ^ τ + 1 ≤ (max m δ) ^ τ + 1 := by linarith
  -- Step 3: from `‖a+b‖^{αt} ≤ K` and `(m_δ^τ+1) ≥ (m^τ+1) ≥ 1`, derive
  -- `‖a+b‖^{αt} / (m_δ^τ+1) ≤ K / (m^τ+1)` (so long as everything is
  -- nonnegative — which is the case since `αt ≥ 1` and the bases are
  -- nonnegative).
  have h_top_nn : 0 ≤ ‖a + b‖ ^ αt := Real.rpow_nonneg hab_nn _
  have hK_nn : 0 ≤ (2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt + ‖b‖ ^ αt) := by
    have h1 : 0 ≤ (2 : ℝ) ^ (αt - 1) := Real.rpow_nonneg (by norm_num) _
    have h2 : 0 ≤ ‖a‖ ^ αt := Real.rpow_nonneg ha_nn _
    have h3 : 0 ≤ ‖b‖ ^ αt := Real.rpow_nonneg hb_nn _
    have : 0 ≤ ‖a‖ ^ αt + ‖b‖ ^ αt := by linarith
    exact mul_nonneg h1 this
  -- Bound LHS by `K / (m^τ + 1)`.
  have h_div_le_first :
      ‖a + b‖ ^ αt / ((max m δ) ^ τ + 1) ≤
        ‖a + b‖ ^ αt / (m ^ τ + 1) := by
    apply div_le_div_of_nonneg_left h_top_nn hden_rhs_pos hden_le
  have h_num_le :
      ‖a + b‖ ^ αt / (m ^ τ + 1) ≤
        ((2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt + ‖b‖ ^ αt)) / (m ^ τ + 1) := by
    apply div_le_div_of_nonneg_right h_top hden_rhs_pos.le
  -- Combine and split the RHS.
  have h_combined :
      ‖a + b‖ ^ αt / ((max m δ) ^ τ + 1) ≤
        ((2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt + ‖b‖ ^ αt)) / (m ^ τ + 1) :=
    le_trans h_div_le_first h_num_le
  -- Step 4: split the RHS as
  --   `2^{αt-1} (‖a‖^{αt}/(m^τ+1)) + 2^{αt-1} (‖b‖^{αt}/(m^τ+1))`
  -- and dominate the second piece by `2^{αt-1} ‖b‖^{αt}` using
  -- `m^τ + 1 ≥ 1`.
  have hone_le_den : (1 : ℝ) ≤ m ^ τ + 1 := by
    have : 0 ≤ m ^ τ := Real.rpow_nonneg hm _
    linarith
  have htwo_pow_nn : 0 ≤ (2 : ℝ) ^ (αt - 1) := Real.rpow_nonneg (by norm_num) _
  have hb_pow_nn : 0 ≤ ‖b‖ ^ αt := Real.rpow_nonneg hb_nn _
  have h_b_div_le : ‖b‖ ^ αt / (m ^ τ + 1) ≤ ‖b‖ ^ αt := by
    rw [div_le_iff₀ hden_rhs_pos]
    nlinarith [hb_pow_nn, hone_le_den]
  have h_split :
      ((2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt + ‖b‖ ^ αt)) / (m ^ τ + 1)
        = (2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt / (m ^ τ + 1))
            + (2 : ℝ) ^ (αt - 1) * (‖b‖ ^ αt / (m ^ τ + 1)) := by
    field_simp
  rw [h_split] at h_combined
  -- Replace the second `‖b‖^{αt}/(m^τ+1)` by `‖b‖^{αt}`.
  have h_second_bound :
      (2 : ℝ) ^ (αt - 1) * (‖b‖ ^ αt / (m ^ τ + 1))
        ≤ (2 : ℝ) ^ (αt - 1) * ‖b‖ ^ αt :=
    mul_le_mul_of_nonneg_left h_b_div_le htwo_pow_nn
  have hRHS_eq :
      (2 : ℝ) ^ (αt - 1) *
        (‖a‖ ^ αt / (m ^ τ + 1) + ‖b‖ ^ αt)
        = (2 : ℝ) ^ (αt - 1) * (‖a‖ ^ αt / (m ^ τ + 1))
            + (2 : ℝ) ^ (αt - 1) * ‖b‖ ^ αt := by ring
  rw [hRHS_eq]
  linarith

/-! ### Helper: closure of `HasWeakDerivPer` under sum -/

/-- The weak partial derivative is additive: if `f₁` and `f₂` have weak
partial derivatives `g₁` and `g₂` respectively in direction `i`, and
both `f₁` and `f₂` are in `L¹_per` (so the IBP test integrals
decompose), then `f₁ + f₂` has weak partial derivative `g₁ + g₂`. -/
private lemma hasWeakDerivPer_add
    {i : Fin d} {f₁ f₂ g₁ g₂ : (Fin d → ℝ) → ℝ}
    (hf₁ : MemLpPer (d := d) 1 f₁) (hf₂ : MemLpPer (d := d) 1 f₂)
    (h₁ : HasWeakDerivPer i f₁ g₁) (h₂ : HasWeakDerivPer i f₂ g₂) :
    HasWeakDerivPer (d := d) i (fun x => f₁ x + f₂ x)
      (fun x => g₁ x + g₂ x) := by
  refine ⟨?_, ?_⟩
  · -- `MemLpPer 1 (g₁ + g₂)`: closure under sum.
    have hg₁ : MemLpPer (d := d) 1 g₁ := h₁.memLpPer
    have hg₂ : MemLpPer (d := d) 1 g₂ := h₂.memLpPer
    have hsum : MemLpPer (d := d) 1 (g₁ + g₂) := hg₁.add hg₂
    have heq : (fun x : Fin d → ℝ => g₁ x + g₂ x) = g₁ + g₂ := by
      funext x; rfl
    rw [heq]; exact hsum
  · intro φ
    -- Smooth `φ` and `∂_i φ` are bounded continuous; combined with `Lp`
    -- integrability of `f₁, f₂, g₁, g₂`, we get integrability of the
    -- factored products and apply linearity.
    have hφ_cont : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
    have hpartial_cont : Continuous
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) :=
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous
    -- Bound smooth `φ` and `∂_i φ` on the unit cube.
    have hbdd_on_cube : ∀ (k : (Fin d → ℝ) → ℝ), Continuous k →
        ∃ C, ∀ x ∈ UnitCube d, |k x| ≤ C := by
      intro k hcont
      have hcompact :
          IsCompact (Set.pi Set.univ
            (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
        isCompact_univ_pi (fun _ => isCompact_Icc)
      obtain ⟨C, hC⟩ := hcompact.bddAbove_image hcont.norm.continuousOn
      refine ⟨C, ?_⟩
      intro x hx; apply hC
      refine ⟨x, ?_, rfl⟩
      intro j _; exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))
    obtain ⟨C, hC⟩ := hbdd_on_cube _ hφ_cont
    obtain ⟨C', hC'⟩ := hbdd_on_cube _ hpartial_cont
    -- Build integrability of each product.
    have hf₁_int : Integrable f₁ (volume.restrict (UnitCube d)) :=
      (memLp_one_iff_integrable).1 hf₁
    have hf₂_int : Integrable f₂ (volume.restrict (UnitCube d)) :=
      (memLp_one_iff_integrable).1 hf₂
    have hg₁_int : Integrable g₁ (volume.restrict (UnitCube d)) :=
      (memLp_one_iff_integrable).1 h₁.memLpPer
    have hg₂_int : Integrable g₂ (volume.restrict (UnitCube d)) :=
      (memLp_one_iff_integrable).1 h₂.memLpPer
    -- Bounded-times-integrable on a finite-measure set.
    have hφ_bound :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ C := by
      refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx; rw [Real.norm_eq_abs]; exact hC x hx
    have hpartial_bound :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x‖ ≤ C' := by
      refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx; rw [Real.norm_eq_abs]; exact hC' x hx
    have hg₁φ_int : Integrable
        (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x)
        (volume.restrict (UnitCube d)) :=
      hg₁_int.mul_bdd hφ_cont.aestronglyMeasurable hφ_bound
    have hg₂φ_int : Integrable
        (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x)
        (volume.restrict (UnitCube d)) :=
      hg₂_int.mul_bdd hφ_cont.aestronglyMeasurable hφ_bound
    have hf₁_partial_int : Integrable
        (fun x => f₁ x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (volume.restrict (UnitCube d)) :=
      hf₁_int.mul_bdd hpartial_cont.aestronglyMeasurable hpartial_bound
    have hf₂_partial_int : Integrable
        (fun x => f₂ x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (volume.restrict (UnitCube d)) :=
      hf₂_int.mul_bdd hpartial_cont.aestronglyMeasurable hpartial_bound
    -- Now compute both sides via additivity.
    have hLHS_split :
        periodicIntegral (fun x => (g₁ x + g₂ x) *
            (φ : (Fin d → ℝ) → ℝ) x)
          = periodicIntegral (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x)
            + periodicIntegral (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) := by
      unfold periodicIntegral
      have heq : (fun x => (g₁ x + g₂ x) * (φ : (Fin d → ℝ) → ℝ) x)
          = (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x)
            + (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x; simp [Pi.add_apply]; ring
      rw [heq]
      exact integral_add hg₁φ_int hg₂φ_int
    have hRHS_split :
        periodicIntegral (fun x => (f₁ x + f₂ x) *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
          = periodicIntegral (fun x => f₁ x *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            + periodicIntegral (fun x => f₂ x *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      unfold periodicIntegral
      have heq :
          (fun x => (f₁ x + f₂ x) *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
            = (fun x => f₁ x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              + (fun x => f₂ x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) := by
        funext x; simp [Pi.add_apply]; ring
      rw [heq]
      exact integral_add hf₁_partial_int hf₂_partial_int
    rw [hLHS_split, hRHS_split]
    rw [h₁.integral_eq φ, h₂.integral_eq φ]
    ring

/-- **`m_δ`-admissibility** (paper `infra:P5-mdelta-admissibility`,
line 1527).

Given a pair `(m, u)` satisfying:

* `MemLpPer β̄ m` and `m ≥ 0` a.e. (the `L^{β̄}` and non-negativity
  parts of `(m, u) ∈ 𝓚`);
* `MemSobolevPer γ̄ u` with explicit weak-derivative witness `Du`;
* `MemLpPer 1 u` (so `u ∈ L¹_per`, used in the IBP additivity); this
  follows from `MemSobolevPer γ̄ u` and `1 ≤ γ̄` via `LpInclusion`,
  which is the standard paper assumption (`γ̄ > 1`);
* the regularity by-product `(eq:reg.pair.sol)` —
  `MemLpPer β̄' (|Du|^{αt}/(m^τ + 1))` —
  obtained from `weak_is_strong_regularity_quotient`;
* `MemLpPer β̄' (|Dφ|^{αt})`: smooth periodic ⇒ bounded ⇒ in any `L^p`
  on the finite-measure cube, but caller-supplied to avoid taking
  `αt ≥ 0` and the `‖·‖_∞`-bound machinery on hand.

A smooth periodic test function `φ` and any `δ > 0` with
`τ ≥ 0`, `αt ≥ 1`:

The truncated pair `(m_δ, u + φ)` belongs to `congestionDomainK`. -/
theorem mdelta_admissibility
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {α β τ : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (φ : SmoothPeriodic d)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    {δ : ℝ}
    (hδ : 0 < δ)
    (hτ : 0 ≤ τ)
    (hαt : 1 ≤ α * (1 + τ / β))
    (hm_Lp : MemLpPer (d := d) betaBar m)
    (hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_Sob : MemSobolevPer (d := d) gammaBar u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDφ_weak : ∀ i, HasWeakDerivPer (d := d) i (φ : (Fin d → ℝ) → ℝ) (Dφ i))
    (hQuot_m_mem :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (m x ^ τ + 1)))
    (hDφ_Lp :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => Dφ i x‖ ^ (α * (1 + τ / β)))) :
    ((fun x => max (m x) δ),
        (fun x => u x + (φ : (Fin d → ℝ) → ℝ) x)) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ := by
  -- Abbreviation.
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  -- For `MemLpPer` of constants we need finite-measure of the cube.
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Smooth `φ` is in `L¹_per` (continuous bounded on finite measure).
  have hφ_L1 : MemLpPer (d := d) 1 ((φ : (Fin d → ℝ) → ℝ)) :=
    (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ).1
  refine ⟨?mLp, ?uSob, ?lower, ?quot⟩
  · -- (1) `MemLpPer betaBar (fun x => max (m x) δ)`.
    -- Bound: `|max(m, δ)| ≤ |m| + δ` pointwise (for `δ > 0`,
    -- `m` real-valued). Actually, `max(m, δ) ≤ max(|m|, δ) ≤ |m| + δ`
    -- since both are nonneg (δ > 0 and |m| ≥ 0).
    have hmax_nn :
        ∀ x, 0 ≤ max (m x) δ := fun x =>
      le_trans hδ.le (le_max_right _ _)
    -- `max(m, δ) ≤ |m| + δ` pointwise, for `δ > 0`.
    have hbnd : ∀ x, |max (m x) δ| ≤ |m x| + δ := by
      intro x
      have h1 : max (m x) δ ≤ |m x| + δ := by
        rcases le_total (m x) δ with h | h
        · rw [max_eq_right h]
          have : 0 ≤ |m x| := abs_nonneg _
          linarith
        · rw [max_eq_left h]
          have habs : m x ≤ |m x| := le_abs_self _
          linarith
      have h2 : 0 ≤ max (m x) δ := hmax_nn x
      rw [abs_of_nonneg h2]
      exact h1
    -- The bounding function `|m| + δ` is in `L^{β̄}_per`.
    have h_abs_m : MemLpPer (d := d) betaBar (fun x => |m x|) := by
      -- `MemLp` of `|f|` follows from `MemLp` of `f` by the norm.
      have hae : (fun x => |m x|) =ᵐ[volume.restrict (UnitCube d)]
          (fun x => ‖m x‖) := by
        refine Filter.Eventually.of_forall ?_
        intro x
        simp only [Real.norm_eq_abs]
      have h_norm_m : MemLpPer (d := d) betaBar (fun x => ‖m x‖) :=
        MemLp.toMemLpPer (MeasureTheory.MemLp.norm hm_Lp.toMemLp)
      exact MemLp.toMemLpPer
        ((MemLpPer.toMemLp h_norm_m).ae_eq hae.symm)
    have h_const_δ : MemLpPer (d := d) betaBar (fun _ : Fin d → ℝ => δ) :=
      MemLp.toMemLpPer (memLp_const δ)
    have h_sum : MemLpPer (d := d) betaBar
        (fun x => |m x| + δ) := h_abs_m.add h_const_δ
    -- Apply `MemLp.mono'` (domination by a real-valued nonneg function).
    apply MemLp.toMemLpPer
    refine MemLp.mono' h_sum.toMemLp ?_ ?_
    · -- AE strong measurability of `max(m, δ)` via AEMeasurable.max.
      have hm_aem : AEMeasurable m
          (Measure.restrict volume (UnitCube d)) :=
        hm_Lp.aestronglyMeasurable.aemeasurable
      have hconst_aem : AEMeasurable
          (fun _ : Fin d → ℝ => δ)
          (Measure.restrict volume (UnitCube d)) :=
        aemeasurable_const
      exact (hm_aem.max hconst_aem).aestronglyMeasurable
    · refine Filter.Eventually.of_forall ?_
      intro x; exact hbnd x
  · -- (2) `MemSobolevPer gammaBar (u + φ)`.
    -- Witness derivatives: `Du i + Dφ i`.
    refine ⟨?_, ?_⟩
    · -- `MemLpPer gammaBar (u + φ)`.
      have hφ : MemLpPer (d := d) gammaBar ((φ : (Fin d → ℝ) → ℝ)) :=
        (MemSobolevPer.of_smoothPeriodic gammaBar φ).1
      have h_sum : MemLpPer (d := d) gammaBar
          (u + (fun x => (φ : (Fin d → ℝ) → ℝ) x)) :=
        hu_Sob.1.add hφ
      -- Coerce the lambda-form to the equality form.
      have heq :
          (fun x : Fin d → ℝ => u x + (φ : (Fin d → ℝ) → ℝ) x)
            = u + (fun x => (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x; rfl
      rw [heq]; exact h_sum
    · -- Weak derivatives: `Du i + Dφ i` via `hasWeakDerivPer_add`.
      refine ⟨fun i x => Du i x + Dφ i x, ?_⟩
      intro i
      exact hasWeakDerivPer_add (i := i) hu_L1 hφ_L1
        (hDu_weak i) (hDφ_weak i)
  · -- (3) Lower bound `δ ≤ max(m, δ)` a.e.
    refine ⟨δ, hδ, ?_⟩
    refine Filter.Eventually.of_forall ?_
    intro x; exact le_max_right _ _
  · -- (4) Weak-derivative witness `Du + Dφ` together with quotient
    -- integrability via the pointwise bound + `MemLp.mono'`.
    refine ⟨fun i x => Du i x + Dφ i x, ?_, ?_⟩
    · -- Weak-derivative witness for `u + φ`: same as in (2).
      intro i
      exact hasWeakDerivPer_add (i := i) hu_L1 hφ_L1
        (hDu_weak i) (hDφ_weak i)
    · -- Quotient integrability via the pointwise bound. We dominate
      -- `LHS x = ‖Du x + Dφ x‖^{αt} / ((max (m x) δ)^τ + 1)` by
      -- `RHS x := 2^{αt-1} (‖Du x‖^{αt}/(m x ^τ + 1) + ‖Dφ x‖^{αt})`,
      -- which is in `L^{β̄'}_per` by closure under sum / scalar
      -- multiplication.
      -- Build `RHS ∈ L^{β̄'}_per`.
      have htwo_pow_nn : 0 ≤ (2 : ℝ) ^ (αt - 1) :=
        Real.rpow_nonneg (by norm_num) _
      have hRHS_inner_mem :
          MemLpPer (d := d) betaBarPrime
            (fun x : Fin d → ℝ =>
              ‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)
                + ‖fun i => Dφ i x‖ ^ αt) := by
        -- Sum of two `L^{β̄'}_per` functions.
        have hsum := hQuot_m_mem.add hDφ_Lp
        -- Coerce to a lambda form.
        have heq :
            (fun x : Fin d → ℝ =>
              ‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)
                + ‖fun i => Dφ i x‖ ^ αt)
              = (fun x : Fin d → ℝ =>
                  ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
                    (m x ^ τ + 1))
                + (fun x : Fin d → ℝ =>
                  ‖fun i => Dφ i x‖ ^ (α * (1 + τ / β))) := by
          funext x; rfl
        rw [heq]; exact hsum
      have hRHS_mem :
          MemLpPer (d := d) betaBarPrime
            (fun x : Fin d → ℝ =>
              (2 : ℝ) ^ (αt - 1) *
                (‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)
                  + ‖fun i => Dφ i x‖ ^ αt)) := by
        -- `c • f ∈ L^p` for any constant `c`.
        have := hRHS_inner_mem.const_smul ((2 : ℝ) ^ (αt - 1))
        -- `c • f = fun x => c * f x` for real-valued `f`.
        have heq :
            ((2 : ℝ) ^ (αt - 1)) •
                (fun x : Fin d → ℝ =>
                  ‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)
                    + ‖fun i => Dφ i x‖ ^ αt)
              = (fun x : Fin d → ℝ =>
                  (2 : ℝ) ^ (αt - 1) *
                    (‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)
                      + ‖fun i => Dφ i x‖ ^ αt)) := by
          funext x; simp [Pi.smul_apply, smul_eq_mul]
        rw [heq] at this
        exact this
      -- Apply `MemLp.mono'`. Pointwise bound from `mdelta_pointwise_bound`.
      apply MemLp.toMemLpPer
      refine MemLp.mono' hRHS_mem.toMemLp ?_ ?_
      · -- AE strong measurability of LHS. Build it from the components.
        -- Du + Dφ is AE strongly measurable because both are.
        -- The norm is continuous, the rpow is continuous in the base for
        -- a fixed exponent (when base is nonneg), and `(m^τ+1)` is AE
        -- strongly measurable too.
        -- Construct `∀ᵐ x, LHS_aesm` via `aestronglyMeasurable_of_aeStronglyMeasurable_quotient`.
        -- Easier: use the fact that the LHS is AE-equal to a measurable
        -- function. Since the bound function `RHS` is AE strongly
        -- measurable and the LHS is bounded by `RHS` (so it doesn't
        -- blow up except a.e.), we instead just verify AE strong
        -- measurability directly. We do not have a clean way without
        -- the witness structure, so we use the standard composition:
        -- `‖fun i => (Du i x + Dφ i x)‖` is continuous in the vector,
        -- which is AE strongly measurable as a function of `x` since
        -- each component is. Combined with continuity of `t ↦ t^{αt}`
        -- (on `[0, ∞)`) and division by an AE-strongly-measurable
        -- positive function, we get AE strong measurability.
        -- For the formal step, we strip down to the measurability
        -- predicate already supported by `hRHS_mem.aestronglyMeasurable`
        -- via congruence: the LHS and RHS are different functions, but
        -- the AE strong measurability of LHS only depends on its
        -- formula, not the `RHS`. We construct it from `Du`, `Dφ`, `m`.
        -- Each `Du i` is AE strongly measurable (member of `L^1_per`).
        -- Likewise `Dφ i`. `m` is AE strongly measurable. Build up:
        -- AESM of LHS = (norm-of-vector-sum)^αt / ((max(m,δ))^τ + 1).
        -- We build it from the components using continuity for rpow
        -- and the standard closure operations.
        have hαt_nn : 0 ≤ αt := le_trans zero_le_one hαt
        have hcont_rpow_αt : Continuous (fun x : ℝ => x ^ αt) :=
          Real.continuous_rpow_const hαt_nn
        have hcont_rpow_τ : Continuous (fun x : ℝ => x ^ τ) :=
          Real.continuous_rpow_const hτ
        -- AEMeasurable building blocks (pointwise components via
        -- `aemeasurable_pi_iff`).
        have h_Du_aem : ∀ i, AEMeasurable (Du i)
            (volume.restrict (UnitCube d)) := fun i =>
          ((hDu_weak i).memLpPer.aestronglyMeasurable).aemeasurable
        have h_Dφ_aem : ∀ i, AEMeasurable (Dφ i)
            (volume.restrict (UnitCube d)) := fun i =>
          ((hDφ_weak i).memLpPer.aestronglyMeasurable).aemeasurable
        have h_sum_aem : ∀ i, AEMeasurable
            (fun x => Du i x + Dφ i x)
            (volume.restrict (UnitCube d)) :=
          fun i => (h_Du_aem i).add (h_Dφ_aem i)
        have h_vec_aem : AEMeasurable
            (fun x : Fin d → ℝ => fun i => Du i x + Dφ i x)
            (volume.restrict (UnitCube d)) :=
          aemeasurable_pi_iff.mpr h_sum_aem
        have h_vec_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ => fun i => Du i x + Dφ i x)
            (volume.restrict (UnitCube d)) :=
          h_vec_aem.aestronglyMeasurable
        -- `‖·‖` is continuous: pull it through.
        have h_norm_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ => ‖fun i => Du i x + Dφ i x‖)
            (volume.restrict (UnitCube d)) :=
          AEStronglyMeasurable.norm h_vec_aesm
        -- `^ αt` via continuous composition (AESM ∘ continuous = AESM).
        have h_rpow_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ => ‖fun i => Du i x + Dφ i x‖ ^ αt)
            (volume.restrict (UnitCube d)) :=
          hcont_rpow_αt.comp_aestronglyMeasurable h_norm_aesm
        -- Denominator AESM.
        have h_m_aesm : AEStronglyMeasurable m
            (volume.restrict (UnitCube d)) :=
          hm_Lp.aestronglyMeasurable
        have h_const_aesm : AEStronglyMeasurable
            (fun _ : Fin d → ℝ => δ)
            (volume.restrict (UnitCube d)) :=
          aestronglyMeasurable_const
        have h_m_aem : AEMeasurable m
            (volume.restrict (UnitCube d)) :=
          h_m_aesm.aemeasurable
        have h_const_aem : AEMeasurable
            (fun _ : Fin d → ℝ => δ)
            (volume.restrict (UnitCube d)) :=
          aemeasurable_const
        have h_max_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ => max (m x) δ)
            (volume.restrict (UnitCube d)) :=
          (h_m_aem.max h_const_aem).aestronglyMeasurable
        have h_mtau_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ => (max (m x) δ) ^ τ)
            (volume.restrict (UnitCube d)) :=
          hcont_rpow_τ.comp_aestronglyMeasurable h_max_aesm
        have h_one_aesm : AEStronglyMeasurable
            (fun _ : Fin d → ℝ => (1 : ℝ))
            (volume.restrict (UnitCube d)) :=
          aestronglyMeasurable_const
        have h_den_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ => (max (m x) δ) ^ τ + 1)
            (volume.restrict (UnitCube d)) :=
          AEStronglyMeasurable.add h_mtau_aesm h_one_aesm
        -- Division through AEMeasurable.
        have h_rpow_aem : AEMeasurable
            (fun x : Fin d → ℝ => ‖fun i => Du i x + Dφ i x‖ ^ αt)
            (volume.restrict (UnitCube d)) := h_rpow_aesm.aemeasurable
        have h_den_aem : AEMeasurable
            (fun x : Fin d → ℝ => (max (m x) δ) ^ τ + 1)
            (volume.restrict (UnitCube d)) := h_den_aesm.aemeasurable
        have h_div_aem : AEMeasurable
            (fun x : Fin d → ℝ =>
              ‖fun i => Du i x + Dφ i x‖ ^ αt /
                ((max (m x) δ) ^ τ + 1))
            (volume.restrict (UnitCube d)) :=
          h_rpow_aem.div h_den_aem
        exact h_div_aem.aestronglyMeasurable
      · -- AE pointwise bound. Combine `hm_nn` (almost everywhere `m ≥ 0`)
        -- with the deterministic `mdelta_pointwise_bound`.
        filter_upwards [hm_nn] with x hx
        -- `‖LHS x‖ ≤ RHS x`. Both sides are nonneg (LHS via rpow_nonneg,
        -- norm_nonneg; RHS via product of nonneg).
        have hLHS_nn :
            0 ≤ ‖fun i => Du i x + Dφ i x‖ ^ αt /
                ((max (m x) δ) ^ τ + 1) := by
          have h1 : 0 ≤ ‖fun i => Du i x + Dφ i x‖ ^ αt :=
            Real.rpow_nonneg (norm_nonneg _) _
          have h2 : 0 ≤ (max (m x) δ) ^ τ + 1 := by
            have : 0 ≤ (max (m x) δ) ^ τ :=
              Real.rpow_nonneg (le_trans hδ.le (le_max_right _ _)) _
            linarith
          exact div_nonneg h1 h2
        rw [Real.norm_eq_abs, abs_of_nonneg hLHS_nn]
        -- Apply the pointwise bound with `a = fun i => Du i x` and
        -- `b = fun i => Dφ i x`.
        have hbound :=
          mdelta_pointwise_bound (m := m x) (δ := δ) (αt := αt) (τ := τ)
            (a := fun i => Du i x) (b := fun i => Dφ i x)
            hx hδ hτ hαt
        -- `(fun i => Du i x) + (fun i => Dφ i x) = fun i => Du i x + Dφ i x`.
        have hadd_eq :
            ((fun i => Du i x) + (fun i => Dφ i x))
              = (fun i => Du i x + Dφ i x) := by
          funext i; rfl
        rw [hadd_eq] at hbound
        exact hbound

/-- **Generic density per-`δ` VI integral inequality** (Steps C–E glue,
density-agnostic core of `perdelta_vi_integral_le`).

This is the reusable core of `perdelta_vi_integral_le` with the concrete
density `muAux k m u V Du H` replaced by an *abstract* nonnegative density
`μ`.  The only `muAux`-specific facts the Steps C–E glue actually uses are
bundled here as three explicit hypotheses:

* `hμ_Lp : μ ∈ L^{β̄}_per` (Step A output);
* `hQuot_m_mem` : the quotient dominator `‖Du‖^{αt}/(μ^τ+1) ∈ L^{β̄'}_per`
  (Step B output);
* `hμ_nn : 0 ≤ μ` a.e.

Everything downstream (`mdelta_admissibility` at the test density
`ρ = max(μ, δ)`, the Banach lift `vδ`, the abstract VI at `vδ`, and the
a.e.-equality transport) is identical to `perdelta_vi_integral_le`.  Both
the `≤`/`muAux` side (`perdelta_vi_integral_le` and its siblings) and the
`≥`/`muRe` side (child D1b-i) instantiate this with their own density.  The
truncation `ρ = max(μ, δ)` (`δ > 0`) keeps the test density admissible in
`congestionBanachK` while `ρ → μ` as `δ → 0⁺`. -/
theorem perdelta_vi_integral_le_of_density
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ : (Fin d → ℝ) → ℝ}
    (hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ)
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)))
    (hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (μ x) δ) - V x)
          * (max (μ x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  simpa only [hρdef] using hgoal

/-- **Per-`δ` VI integral inequality for the `μ_re`/`≥` side** (child D1b-i,
paper `eq:congest.HJ0`, lines 1493–1507; the `≥`-direction analogue of
`perdelta_vi_integral_le`).

Instantiates the density-agnostic core `perdelta_vi_integral_le_of_density` at
the `μ_re` density `μ := muRe k m u V Du H`.  Despite the `≥`-side label, the
output integral is the same `≤ 0` shape: `μ_re = min(m, μ_re_inner) ≤ m`, and
the genuinely-needed `≤ 0` integral is the Banach test-pair VI (exactly the
`≤`/`muAux` side; `muRe_inequality` separately supplies the `≥`-direction
product bound that `weak_is_strong_HJB_ge_at_k` combines with this).  We reuse
the same `max(μ, δ)` upward clamp (`δ > 0`), which `→ μ_re` as `δ → 0⁺`.

Two of the three Steps-A/B certs are discharged internally:

* `hμ_nn : 0 ≤ μ_re` a.e. — from `muRe_nonneg_ae` (`0 ≤ m` + non-emptiness);
* `hμ_Lp : μ_re ∈ L^{β̄}_per` — from `0 ≤ μ_re ≤ m` (`muRe_le_m`) by
  `MemLp.mono'` against the `L^{β̄}` envelope `m`.

The remaining quotient-dominator cert `hQuot_muRe_mem`
(`‖Du‖^{αt}/(μ_re^τ + 1) ∈ L^{β̄'}_per`) is taken as a hypothesis parameter:
unlike the numerator, it is **not** obtainable by dropping the `μ_re^τ`
denominator (that would force `‖Du‖^{αt} ∈ L^{β̄'}`, which fails for `τ > 0`),
so it needs the `μ_re`-HJB-constraint analogue of
`muAux_quotient_dominator_memLp` (child D1b-i2). -/
theorem perdelta_vi_integral_le_of_muRe
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hμre_aesm :
      AEStronglyMeasurable (muRe k m u V Du H)
        (volume.restrict (UnitCube d)))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty)
    (hQuot_muRe_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (muRe k m u V Du H x ^ hcong.τ + 1)))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x
            + H x (fun i => Du i x) (max (muRe k m u V Du H x) δ) - V x)
          * (max (muRe k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muRe k m u V Du H with hμdef
  -- `0 ≤ μ_re` a.e. (`0 ≤ m` + non-emptiness of the inner constraint set).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    muRe_nonneg_ae hae_m_nn hae_ne
  -- `μ_re ∈ L^{β̄}_per`: dominated by the `L^{β̄}` envelope `m` since
  -- `0 ≤ μ_re ≤ m` a.e.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ := by
    have hbound :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖μ x‖ ≤ m x := by
      filter_upwards [hμ_nn] with x hx_nn
      have hle : μ x ≤ m x := by
        simpa [hμdef] using muRe_le_m k m u V Du H x
      rw [Real.norm_of_nonneg hx_nn]
      exact hle
    exact Periodic.memLpPer_iff_memLp.mpr
      (MemLp.mono' (Periodic.memLpPer_iff_memLp.mp hm_mem) hμre_aesm hbound)
  -- Instantiate the density-agnostic core at `μ := muRe k m u V Du H`.
  have h := perdelta_vi_integral_le_of_density (d := d) hmon hcong
    (m := m) (u := u) (V := V) (Du := Du) (μ := μ)
    hμ_Lp hQuot_muRe_mem hμ_nn hVmeas hV
    (ε := ε) (A := A) (K := K) (w := w)
    hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du hδ
  simpa only [hμdef] using h

set_option maxHeartbeats 1600000 in
/-- **`h_DCT` producer for the `≥`-side** (child D1b-iii, paper
`eq:congest.HJ0`, line 1398 — the `μ_re` analogue of
`h_DCT_producer_of_m_nonneg`).

Assembles the landed D1b pieces into the integral inequality that
`weak_is_strong_HJB_ge_at_k` consumes as its `h_DCT` field:

```
∫ (u + H(·, Du, μ_re) − V)·(μ_re − m) ≤ 0.
```

The proof runs the `δ → 0⁺` DCT engine `muRe_integral_tendsto` against the
clamped sequence `μδ n := max(μ_re, 1/(n+1))`, `mδ n := m`, taking
`le_of_tendsto` over the per-`n` VI inequalities supplied by
`perdelta_vi_integral_le_of_muRe`.  The first-factor envelope is the
`μ_re`-side analogue of `hf1_all`: at `μ_re x` the HJB constraint gives
`u + H(·, Du, μ_re) − V ≤ 0` (`muRe_bound_up`), antitonicity transports
the bound up to the clamp `ρ = max(μ_re x, δ) ≥ μ_re x`, and the
congestion lower bound supplies the matching lower envelope.  The
boundary `{μ_re x = 0}` is handled inside `muRe_integral_tendsto` via the
vanishing-prefactor squeeze (`hbdry : μ_re x = 0 ⇒ m x = 0` from
`muRe_le_m` + `m ≥ 0`).  No `Hext_finite_at_zero` / power-growth crutch /
`0 < m` rider. -/
theorem h_DCT_producer_muRe
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {k : ℝ} (hk : 0 < k)
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
        (muReSet k u V Du H x).Nonempty)
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
          * (muRe k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muRe k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- HJB null-measurability (boundary-free `_aesm` route). `V` is only
  -- a.e.-strongly-measurable, so build the sublevel set as a `NullMeasurableSet`
  -- of the a.e.-strongly-measurable HJB integrand.
  have hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ -k }
        (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hF_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ => u x + H x (fun i => Du i x) a - V x)
        (volume.restrict (UnitCube d)) :=
      (hu_meas.aestronglyMeasurable.add hHcomp.aestronglyMeasurable).sub hV_aesm
    exact hF_aesm.nullMeasurableSet_le aestronglyMeasurable_const
  -- A.e./`Ioi 0` analytic riders derived from `hmon`/`hcong`.
  have hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    have hg : Continuous (fun μ₀ : ℝ => ((fun i => Du i x), μ₀)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun μ₀ : ℝ => ((fun i => Du i x), μ₀))
        (Set.Ioi (0 : ℝ)) {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := fun μ₀ hμ₀ => hμ₀
    exact hx.comp hg.continuousOn hmaps
  have hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx (fun i => Du i x)
  -- `μ_re` is `AEMeasurable` (a.e.-on-`Ioi 0` route).
  have hμre_aem : AEMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muRe_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hae_m_nn
      hae_anti hae_cont hae_ne
  have hμre_aesm : AEStronglyMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) := hμre_aem.aestronglyMeasurable
  -- `0 ≤ μ_re` a.e.
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    muRe_nonneg_ae hae_m_nn hae_ne
  -- Boundary HJB-upper bound at `μ_re = 0` via (a:Hat0).
  have hae_HJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k := by
    filter_upwards [hae_anti, hae_ne, hHat0.exists_limit_at_zero, hAgree]
      with x hx_anti hx_ne hx_limit hx_agree hμle0
    have hwit := (muReInner_le_zero_iff_of_antitoneOn_Ioi hx_anti hx_ne).mp hμle0
    have hTendsto :
        Filter.Tendsto
          (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
      Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
    set b : ℝ := -k - u x + V x with hb_def
    by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
        (q : ℝ) = 0 ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k
    · obtain ⟨_, _, hq_eq0, _, _, hHJB_q⟩ := hzero
      rw [hq_eq0] at hHJB_q; exact hHJB_q
    · have hPointwise : ∀ ν : ℝ, 0 < ν →
          u x + H x (fun i => Du i x) ν - V x ≤ -k := by
        intro ν hν
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
        obtain ⟨q, hq_nn, hq_hi, hHJB_q⟩ := hwit n
        have hq_lt_ν : (q : ℝ) < ν := by
          have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
            simpa only [one_div] using hn
          exact lt_trans hq_hi h1
        have hq_pos : 0 < (q : ℝ) := by
          rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
          · exact absurd ⟨n, q, hq0.symm, hq_nn, hq_hi, hHJB_q⟩ hzero
          · exact hq_pos
        have hanti_le :
            H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
          hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
        linarith [hHJB_q]
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
          self_mem_nhdsWithin, fun ν hν => ?_⟩
        have := hPointwise ν hν
        have hle : H x (fun i => Du i x) ν ≤ b := by rw [hb_def]; linarith
        exact_mod_cast hle
      have hHext_le :
          Hamiltonian.H_at_zero H x (fun i => Du i x)
            ≤ ((b : ℝ) : WithTop ℝ) := le_of_tendsto hTendsto hEv
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
      have hraw_le :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        rw [hAgree_x]; exact hHext_le
      have hraw : H x (fun i => Du i x) 0 ≤ b := by exact_mod_cast hraw_le
      rw [hb_def] at hraw; linarith
  -- The quotient dominator rider (`hQuot_muRe_mem`) for the per-`δ` VI.
  have hQuot_muRe_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (muRe k m u V Du H x ^ hcong.τ + 1)) :=
    muRe_quotient_dominator_memLp hmon hcong hHat0 hAgree hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hae_m_nn hae_anti hae_cont h_step1 hae_ne
  -- Per-`n` variational inequality from `perdelta_vi_integral_le_of_muRe`.
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    intro n
    have h := perdelta_vi_integral_le_of_muRe hmon hcong hm_mem hμre_aesm
      hae_m_nn hae_ne hQuot_muRe_mem hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du
      hcoeWeak_Du (hδ_pos n)
    simpa only [hμdef] using h
  -- Lower congestion bound `-(C·(ρ^β+1)) ≤ H(·, ρ)` for `ρ > 0` (a.e.).
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1))
        * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ -(C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1))
            * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) - C * (ρ ^ β + 1)
            ≥ -(C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  -- `μ_re ∈ L^{β+1}` (dominated by `m` since `0 ≤ μ_re ≤ m`).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ := by
    have hbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖μ x‖ ≤ m x := by
      filter_upwards [hμ_nn] with x hx_nn
      have hle : μ x ≤ m x := by simpa [hμdef] using muRe_le_m k m u V Du H x
      rw [Real.norm_of_nonneg hx_nn]; exact hle
    have hm_mem' : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m := hm_mem
    exact Periodic.memLpPer_iff_memLp.mpr
      (MemLp.mono' (Periodic.memLpPer_iff_memLp.mp hm_mem') hμre_aesm hbnd)
  -- The upper HJB envelope at `μ_re`: `u + H(·, μ_re) − V ≤ 0` a.e. (`muRe_bound_up`).
  have hμ_bound_up : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (μ x) - V x ≤ 0 := by
    have := muRe_bound_up (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H)
      hk hae_cont hae_ne hae_HJB0 h_step1
    simpa only [hμdef] using this
  -- Envelope/dominator data, mirroring `h_DCT_producer_of_m_nonneg`.
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := (hu'.add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]; field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  -- Antitone-clamp transport `H(·, ρ) ≤ H(·, μ x)` for `0 ≤ μ x ≤ ρ`, `0 < ρ`
  -- (a.e.).  For `μ x > 0` this is `hae_anti`; for `μ x = 0` the right-limit
  -- `H(·, ν) → H(·, 0)` (a:Hat0) transports the antitone bound to the boundary.
  have hae_clamp : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ ρ : ℝ, μ x ≤ ρ → 0 < ρ →
        H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) := by
    filter_upwards [hμ_nn, hae_anti, hHat0.exists_limit_at_zero, hAgree]
      with x hxμ_nn hx_anti hx_limit hx_agree ρ hρ_ge hρ_pos
    rcases eq_or_lt_of_le hxμ_nn with hμ0 | hμpos
    · -- `μ x = 0`: antitone-to-0 via the right-limit.
      rw [← hμ0]
      have hTendsto :
          Filter.Tendsto
            (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
        Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
      -- `H(·, ρ) ≤ H(·, ν)` for `0 < ν < ρ`, then take `ν ↓ 0`.
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ρ : ℝ) : WithTop ℝ)
              ≤ ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr
          ⟨Set.Ioo (0 : ℝ) ρ, Ioo_mem_nhdsGT hρ_pos, fun ν hν => ?_⟩
        have hle : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) ν :=
          hx_anti hν.1 hρ_pos hν.2.le
        exact_mod_cast hle
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
      have hle_top :
          ((H x (fun i => Du i x) ρ : ℝ) : WithTop ℝ)
            ≤ Hamiltonian.H_at_zero H x (fun i => Du i x) :=
        ge_of_tendsto hTendsto hEv
      rw [← hAgree_x] at hle_top
      exact_mod_cast hle_top
    · -- `μ x > 0`: direct antitone on `Ioi 0`.
      exact hx_anti hμpos (lt_of_lt_of_le hμpos hρ_ge) hρ_ge
  -- The uniform-in-`n` first-factor bound `|u+H(max(μ,δ))−V| ≤ G1` (a.e.).
  have hf1_all : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    filter_upwards [hμ_nn, hH_lower, hμ_bound_up, hae_clamp]
      with x hxμ_nn hxH_lower hx_up hx_clamp
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]; apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    -- Antitonicity: `H(·, ρ) ≤ H(·, μ x)` (boundary-aware, `μ x ≤ ρ`, `0 < ρ`).
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      hx_clamp ρ hρ_ge_μ hρ_pos
    have hf1_upper : factor1 ≤ 0 := by
      rw [hf1def]; linarith [hx_up, hHanti_le]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    show |factor1| ≤ G1 x
    rw [hG1def, abs_le]
    refine ⟨hf1_lower, ?_⟩
    have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      positivity
    linarith [hf1_upper]
  -- The per-`n` integrand measurability (`hmeas`).
  have h_max_meas : ∀ n, AEMeasurable (fun x => max (μ x) (δSeq n))
      (volume.restrict (UnitCube d)) :=
    fun n => hμre_aem.max aemeasurable_const
  have h_Hmax_meas : ∀ n, AEMeasurable
      (fun x => H x (fun i => Du i x) (max (μ x) (δSeq n)))
      (volume.restrict (UnitCube d)) :=
    fun n => hmon.toRegularityH.measurable_H.comp_aemeasurable
      (aemeasurable_id.prodMk
        ((Measurable.of_eval hDu_meas).aemeasurable.prodMk (h_max_meas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      (((hu_meas.aestronglyMeasurable.add
            (AEMeasurable.aestronglyMeasurable (h_Hmax_meas n))).sub
          hV_aesm).mul
        ((AEMeasurable.aestronglyMeasurable (h_max_meas n)).sub
          hm_meas.aestronglyMeasurable))
  -- The domination `‖factor1·factor2‖ ≤ bound x`.
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    filter_upwards [hf1_all n, hμ_nn] with x hxf1 hxμ_nn
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]; apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n, hxμ_nn]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    have hf1_abs : |factor1| ≤ G1 x := hxf1
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        refine ⟨by linarith [hρ_ge_μ], by linarith [hρ_le]⟩
      linarith [hsplit, hρμ]
    have hG1_nonneg : 0 ≤ G1 x := by
      rw [hG1def]
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      positivity
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            exact mul_le_mul hf1_abs hf2_abs (abs_nonneg _) hG1_nonneg
      _ = bound x := by rw [hbounddef]
  -- The pointwise `δ → 0⁺` limit (full continuity of `H(x,Du x,·)` at `μ x`,
  -- including the boundary `μ x = 0` — no `hbdry` squeeze needed).
  have h_lim : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n =>
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x))
        Filter.atTop
        (nhds
          ((u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x))) := by
    filter_upwards [hμ_nn, hae_cont, hHat0.exists_limit_at_zero, hAgree]
      with x hxμ_nn hx_cont hx_limit hx_agree
    have h_max_lim :
        Filter.Tendsto (fun n => max (μ x) (δSeq n)) Filter.atTop (nhds (μ x)) := by
      have h0 : max (μ x) (0 : ℝ) = μ x := max_eq_left hxμ_nn
      have := (tendsto_const_nhds (x := μ x)).max hδ_lim
      simpa [h0] using this
    -- `H(·, max(μ,δ_n)) → H(·, μ)`: for `μ > 0` eventually constant; for
    -- `μ = 0`, `max(0,δ_n) = δ_n → 0⁺`, so the (a:Hat0) right-limit applies.
    have h_H_lim :
        Filter.Tendsto (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
          Filter.atTop (nhds (H x (fun i => Du i x) (μ x))) := by
      rcases eq_or_lt_of_le hxμ_nn with hμ0 | hμpos
      · -- `μ x = 0`: `max(0, δSeq n) = δSeq n`, right-limit via (a:Hat0).
        have hmax_eq : (fun n => max (μ x) (δSeq n)) = δSeq := by
          funext n; rw [← hμ0]; exact max_eq_right (hδ_pos n).le
        -- `WithTop`-valued right-limit to `H_at_zero`.
        have hTop :
            Filter.Tendsto
              (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
          Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
        -- Identify `H_at_zero = (H x (Du x) 0 : WithTop ℝ)` via `hAgree`.
        have hAgree_x :
            ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
              = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
          rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
        have hTop' :
            Filter.Tendsto
              (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ))) := by
          rw [hAgree_x]; exact hTop
        -- Pull back to a real-valued right-limit.
        have hReal :
            Filter.Tendsto (fun ν : ℝ => H x (fun i => Du i x) ν)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (H x (fun i => Du i x) 0)) :=
          (WithTop.isEmbedding_coe (ι := ℝ)).tendsto_nhds_iff.mpr hTop'
        -- `δSeq → 0` and `δSeq n ∈ Ioi 0`, so compose to the right-limit.
        have hδ_within :
            Filter.Tendsto δSeq Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ_lim
            (Filter.Eventually.of_forall (fun n => hδ_pos n))
        have hcomp := hReal.comp hδ_within
        have hfun_eq :
            (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
              = (fun n => H x (fun i => Du i x) (δSeq n)) := by
          funext n; rw [← hμ0]; rw [max_eq_right (hδ_pos n).le]
        rw [hfun_eq, ← hμ0]; exact hcomp
      · -- `μ x > 0`: `H(·, ·)` continuous at `μ x ∈ Ioi 0`.
        have hcontAt : ContinuousAt (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (μ x) :=
          (hx_cont _ hμpos).continuousAt (isOpen_Ioi.mem_nhds hμpos)
        exact hcontAt.tendsto.comp h_max_lim
    have h_first :
        Filter.Tendsto
          (fun n => u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          Filter.atTop (nhds (u x + H x (fun i => Du i x) (μ x) - V x)) :=
      ((tendsto_const_nhds.add h_H_lim).sub tendsto_const_nhds)
    have h_second :
        Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
          (nhds (μ x - m x)) := h_max_lim.sub tendsto_const_nhds
    exact h_first.mul h_second
  -- Assemble the DCT limit.
  have htendsto :
      Filter.Tendsto
        (fun n =>
          ∫ x in UnitCube d,
              (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
                * (max (μ x) (δSeq n) - m x)
              ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds
          (∫ x in UnitCube d,
              (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
              ∂(volume : Measure (Fin d → ℝ)))) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hmeas hbound_int hbound h_lim
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

/-- **Per-`δ` VI integral inequality** (paper `lem:weak.is.strong`,
Step 1, lines 1527–1533; Steps C–E glue).

Given the congestion witness context — abstract VI witness `w` whose
coercions realise the witness data `(m, u, V, Du)`, the abstract VI
`hVI`, the BB1 `Fact` pack, the HJB level `k`, and the standing
measurability / `MemLpPer` / continuity hypotheses consumed by
`muAux_mem_Lp_of_witnessData` / `muAux_quotient_dominator_memLp` — and
each `δ > 0`, produce

```
∫ (u + H(·, Du, max(muAux k m u V Du H, δ)) − V)·(max(muAux …, δ) − m) ≤ 0.
```

The proof glues:
* Step A/B: `muAux_mem_Lp_of_witnessData` and
  `muAux_quotient_dominator_memLp` (consumed, not re-derived);
* Step C: `mdelta_admissibility` at the zero test function (`φ = 0`),
  giving `(max(muAux, δ), u) ∈ congestionDomainK`;
* Step D: `mem_congestionBanachK_of_densityMemLp` with density
  `ρ = max(muAux, δ)`, producing a Banach lift `vδ` whose density slot
  is a.e. `ρ` and whose value/gradient slots equal `w.2`;
* Step E: `vi_integral_le_of_mem_witnessComponents` (`hAeq`/`hKeq` by
  `rfl`), followed by `MeasureTheory.integral_congr_ae` to rewrite the
  density slot `⇑vδ.1` to `max(muAux, δ)` in the integrand. -/
theorem perdelta_vi_integral_le
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    -- The abstract VI data, threaded as plain parameters exactly as in
    -- `vi_integral_le_of_mem_witnessComponents`. The caller instantiates
    -- `A`/`K` from the BB1 operator pack so `hAeq`/`hKeq` hold by `rfl`.
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    -- The witness coercions realise the witness data.
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    -- The witness weak-derivative relation (paper `Du = ∇u`).
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) δ) - V x)
          * (max (muAux k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  -- `1 ≤ α(1 + τ/β)`: from `1 < α` and `1 ≤ 1 + τ/β` (since `τ/β ≥ 0`).
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- Step A: `μ ∈ L^{β̄}_per`.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  -- Step B: the quotient dominator membership.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  -- `μ ≥ 0` a.e. on the cube (`muAux` = `sInf` of a set of nonneg values).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact le_csInf (h_ne_all x) (fun b hb => hb.1)
  -- `γBar = ofReal(α(β+1)/β)` is finite, and `1 ≤ γBar` is the BB1 Fact.
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  -- `MemLpPer γBar u` from the witness `u = ⇑w.2.1`.
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  -- `hu_L1 : MemLpPer 1 u` (Hölder inclusion on the finite cube).
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  -- `hDu_weak : ∀ i, HasWeakDerivPer i u (Du i)` (witness relation, rewritten).
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  -- `hu_Sob : MemSobolevPer γBar u`.
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  -- `hDφ_weak` for the zero test function (inlined; the Existence-private
  -- `congestion_hasWeakDerivPer_zero_zero` is not exported).
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  -- `hDφ_Lp`: `‖0‖^{αt} = 0`, so the function is `0 ∈ L^{β̄'}`.
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  -- Step C: `(ρ, u+0) ∈ congestionDomainK` via `mdelta_admissibility` (φ = 0).
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  -- Clean the value slot `u + 0 = u`.
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  -- `hdom`: `(ρ, ⇑w.2.1) ∈ congestionDomainK` (rewrite `u → ⇑w.2.1`).
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  -- `hρ_mem : MemLpPer (ofReal(β+1)) ρ` — the first conjunct of the
  -- `congestionDomainK` membership produced by `mdelta_admissibility`.
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  -- Step D: Banach lift `vδ` of the truncated density `ρ`.
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  -- Step E: the abstract VI integral inequality at `vδ`.
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  -- Step E (a.e. rewrite): the integrand a.e. equals the target integrand.
  -- Rewrite the witness coercions to `u`, `Du`, `m`, and `⇑vδ.1 → ρ`.
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  -- Conclude by transporting `hVI_vδ` along the a.e. equality of integrands.
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  -- Unfold `ρ = max(μ, δ)` and `μ = muAux …` to match the stated goal.
  simpa only [hρdef, hμdef] using hgoal

/-- **First-variation VI inequality at fixed `δ` and fixed test direction `φ`**
(paper `lem:weak.is.strong`, `eq:identity-congestion`, lines 1530–1556;
T2 phase6 BB VIid child-3).

Sibling of `perdelta_vi_integral_le` but with a **nonzero** smooth periodic
test direction `φ` and a positive scaling `t > 0`. Applies the abstract VI
`hVI` at the admissible perturbed pair
`(m_δ, u + t·φ, Du + t·∇φ) ∈ congestionBanachK` — where the density slot is the
δ-truncation `m_δ x = max (m x) δ` (`mPerDelta`) and the value/gradient slots
are the witness slots shifted by `t·φ` / `t·∇φ` — then unfolds the concrete
operator pairing `mfgOperatorEpsPair` via `congestionAepsiOpK_apply_of_mem` and
`mfgOperatorEpsPair_pairing_eq`, and divides by `t > 0`.

The conclusion is the **raw first-variation inequality at fixed `δ`** (paper
line 1534): the pairing integrand of `A_ε` at the perturbed pair against the
difference test direction `(m_δ − m, t·φ, t·∇φ)`, scaled by `1/t`. No limit is
taken here (`t → 0` is child-4, `δ → 0` is child-5).

The K-membership of the perturbed pair is assembled here (child-1 deferred it):
the density / value / gradient slots are realised as `Lp` lifts, the
`congestionDomainK` conjunct is supplied by `mdelta_admissibility` at the
smooth periodic test `t • φ` (whose ratio-integrability conjunct carries the
perturbed gradient `Du + t·∇φ`), and the weak-derivative conjunct by
`hasWeakDerivPer_add`. -/
theorem congestion_VI_firstvar_ineq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (φ : Periodic.SmoothPeriodic d)
    {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (1 / t) *
      ((∫ x in UnitCube d,
          (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              - H x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
              + V x) * (max (m x) δ - m x)
            + max (m x) δ
                * (DpH x
                    (fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    (max (m x) δ)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
            + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                * ((fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                    * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))) := by
  classical
  -- Standard exponent facts.
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The scaled smooth periodic test direction `ψ := t • φ`.
  set ψ : Periodic.SmoothPeriodic d := t • φ with hψdef
  have hψ_coe : (ψ : (Fin d → ℝ) → ℝ)
      = fun x => t * (φ : (Fin d → ℝ) → ℝ) x := by
    rw [hψdef]; funext x; rw [Periodic.SmoothPeriodic.coe_smul]; rfl
  -- The test gradient `Dψ i := ∂_i ψ`, with its scaled-`φ` profile.
  set Dψ : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (Periodic.SmoothPeriodic.partialDeriv i ψ : (Fin d → ℝ) → ℝ)
    with hDψdef
  -- `∂_i (t • φ) = t • ∂_i φ` pointwise (linearity of `fderiv`).
  have hDψ_coe : ∀ i, Dψ i
      = fun x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
          (Fin d → ℝ) → ℝ) x := by
    intro i
    rw [hDψdef]
    simp only [Periodic.SmoothPeriodic.coe_partialDeriv]
    funext x
    have hψφ : (ψ : (Fin d → ℝ) → ℝ) = t • (φ : (Fin d → ℝ) → ℝ) := by
      rw [hψ_coe]; funext y; simp [Pi.smul_apply]
    rw [hψφ, fderiv_const_smul (φ.smooth.differentiable (by simp) |>.differentiableAt)]
    simp [Pi.smul_apply]
  -- `ρ := m_δ = max(m, δ)`.
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (m x) δ with hρdef
  -- Abbreviations for the witness coercions (`= m, u, Du`).
  -- Weak-derivative facts for `u`, transported from the witness.
  have hu_L1' : MemLpPer (d := d) 1 (⇑w.2.1 : (Fin d → ℝ) → ℝ) := by
    have hu_Lp_γ :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          (⇑w.2.1 : (Fin d → ℝ) → ℝ) :=
      Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
    refine hu_Lp_γ.mono_exponent_finite ?_ ENNReal.ofReal_ne_top
    exact Fact.out
  -- `ψ`-side `L¹` / `Lp` and weak-derivative facts.
  have hψ_L1 : MemLpPer (d := d) 1 ((ψ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) ψ).1
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) :=
    ⟨Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1),
      ⟨fun i => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ), hcoeWeak_Du⟩⟩
  have hDψ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i ((ψ : (Fin d → ℝ) → ℝ)) (Dψ i) := by
    intro i
    rw [hDψdef]
    exact Periodic.HasWeakDerivPer.of_contDiff i ψ
  -- The `‖Dψ‖^{αt}` ratio-Lp datum: `ψ` smooth ⇒ `∂ᵢψ` continuous bounded ⇒
  -- `‖Dψ‖^{αt} ∈ L^{β̄'}` on the finite-measure cube.
  have hDψ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Dψ i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    -- `‖Dψ(x)‖` is bounded on the cube (each `Dψ i` is continuous), so the
    -- `αt`-power is bounded, hence in `L^{β̄'}`.
    set αt : ℝ := hcong.α * (1 + hcong.τ / hcong.β) with hαtdef
    have hαt_nn : 0 ≤ αt := le_trans (by norm_num) hαt
    have hcont : ∀ i, Continuous (Dψ i) := by
      intro i; rw [hDψdef]
      exact (Periodic.SmoothPeriodic.partialDeriv i ψ).smooth.continuous
    have hnorm_cont : Continuous (fun x : Fin d → ℝ => ‖fun i => Dψ i x‖) := by
      apply Continuous.norm
      apply continuous_pi
      intro i; exact hcont i
    -- Bound `‖Dψ(·)‖` on the closed cube.
    have hcompact :
        IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hnorm_cont.continuousOn
    -- The `αt`-power function is continuous, hence a.e.-strongly measurable.
    have hpow_cont : Continuous (fun x : Fin d → ℝ =>
        ‖fun i => Dψ i x‖ ^ αt) :=
      hnorm_cont.rpow_const (fun _ => Or.inr hαt_nn)
    refine MemLp.toMemLpPer ?_
    refine MeasureTheory.MemLp.of_bound hpow_cont.aestronglyMeasurable
      (C ^ αt) ?_
    refine (ae_restrict_iff' measurableSet_unitCube).2
      (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx_cube : x ∈ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro j _
      exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))
    have hnorm_le : ‖fun i => Dψ i x‖ ≤ C := hC ⟨x, hx_cube, rfl⟩
    have hnorm_nn : 0 ≤ ‖fun i => Dψ i x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnorm_nn _)]
    exact Real.rpow_le_rpow hnorm_nn hnorm_le hαt_nn
  -- Step C: `(m_δ, ⇑w.2.1 + ψ) ∈ congestionDomainK` via `mdelta_admissibility`.
  have hdomC :
      ((fun x => max ((⇑w.1 : (Fin d → ℝ) → ℝ) x) δ),
          (fun x => (⇑w.2.1 : (Fin d → ℝ) → ℝ) x
            + (ψ : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    refine mdelta_admissibility (d := d)
      (m := (⇑w.1 : (Fin d → ℝ) → ℝ)) (u := (⇑w.2.1 : (Fin d → ℝ) → ℝ))
      (Du := fun i => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
      ψ Dψ hδ hτ_nn hαt ?_ ?_ hu_Sob hu_L1' hcoeWeak_Du hDψ_weak ?_ ?_
    · rw [hw_m]; exact hm_mem
    · rw [hw_m]; exact hm_nn
    · -- ratio-Lp for the witness density `⇑w.1 = m`.
      have heq : (fun x : Fin d → ℝ =>
            ‖fun i => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x‖
              ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
              ((⇑w.1 : (Fin d → ℝ) → ℝ) x ^ hcong.τ + 1))
          = (fun x : Fin d → ℝ =>
              ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
                (m x ^ hcong.τ + 1)) := by
        funext x
        have hDu_pt : (fun i => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x)
            = (fun i => Du i x) := by funext i; rw [hw_Du i]
        rw [hDu_pt, hw_m]
      rw [heq]; exact hQuot_m_mem
    · exact hDψ_Lp
  -- Step D: build the perturbed Banach element `vt`.
  -- Value/gradient `Lp` lifts of `ψ` (at exponent `γBar`).
  have hψ_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        ((ψ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) ψ).1
  have hDψ_Lp_γ : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (Dψ i) := by
    intro i
    rw [hDψdef]
    exact (Periodic.MemSobolevPer.of_smoothPeriodic
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (Periodic.SmoothPeriodic.partialDeriv i ψ)).1
  -- Density `Lp` lift of `ρ`.
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := by
    have := hdomC.1
    rw [hw_m] at this; exact this
  -- The perturbed Banach element.
  set vt : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
    (hρ_mem.toMemLp.toLp,
     w.2.1 + (hψ_Lp_γ.toMemLp.toLp),
     fun i => w.2.2 i + ((hDψ_Lp_γ i).toMemLp.toLp)) with hvtdef
  -- a.e. slot profiles of `vt`.
  have hvt_dens : (⇑vt.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] ρ := by
    rw [hvtdef]; exact MeasureTheory.MemLp.coeFn_toLp hρ_mem.toMemLp
  have hvt_val : (⇑vt.2.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => (⇑w.2.1 : (Fin d → ℝ) → ℝ) x + (ψ : (Fin d → ℝ) → ℝ) x) := by
    have hval : vt.2.1 = w.2.1 + (hψ_Lp_γ.toMemLp.toLp) := rfl
    rw [hval]
    filter_upwards [MeasureTheory.Lp.coeFn_add w.2.1 (hψ_Lp_γ.toMemLp.toLp),
      MeasureTheory.MemLp.coeFn_toLp hψ_Lp_γ.toMemLp] with x hx_add hx_ψ
    rw [hx_add, Pi.add_apply, hx_ψ]
  have hvt_grad : ∀ i, (⇑(vt.2.2 i) : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x + Dψ i x) := by
    intro i
    have hgr : vt.2.2 i = w.2.2 i + ((hDψ_Lp_γ i).toMemLp.toLp) := rfl
    rw [hgr]
    filter_upwards [MeasureTheory.Lp.coeFn_add (w.2.2 i) ((hDψ_Lp_γ i).toMemLp.toLp),
      MeasureTheory.MemLp.coeFn_toLp (hDψ_Lp_γ i).toMemLp] with x hx_add hx_ψ
    rw [hx_add, Pi.add_apply, hx_ψ]
  -- `vt ∈ congestionBanachK`.
  have hvt_mem : vt ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ := by
    rw [mem_congestionBanachK_iff]
    refine ⟨?_, ?_⟩
    · -- Domain conjunct: transport `hdomC` along the a.e. slot profiles.
      have hdens_ae : (fun x => max ((⇑w.1 : (Fin d → ℝ) → ℝ) x) δ)
          =ᵐ[volume.restrict (UnitCube d)] (⇑vt.1 : (Fin d → ℝ) → ℝ) := by
        rw [hw_m]
        exact hvt_dens.symm
      have hval_ae :
          (fun x => (⇑w.2.1 : (Fin d → ℝ) → ℝ) x + (ψ : (Fin d → ℝ) → ℝ) x)
            =ᵐ[volume.restrict (UnitCube d)] (⇑vt.2.1 : (Fin d → ℝ) → ℝ) :=
        hvt_val.symm
      exact congestionDomainK_congr_ae hdomC hdens_ae hval_ae
    · -- Gradient conjunct: weak-deriv of `⇑vt.2.1` is `⇑(vt.2.2 i)`.
      intro i
      -- Weak-deriv of `u + ψ` is `Du i + Dψ i`.
      have hbase : Periodic.HasWeakDerivPer (d := d) i
          (fun x => (⇑w.2.1 : (Fin d → ℝ) → ℝ) x + (ψ : (Fin d → ℝ) → ℝ) x)
          (fun x => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x + Dψ i x) :=
        hasWeakDerivPer_add (i := i) hu_L1' hψ_L1 (hcoeWeak_Du i) (hDψ_weak i)
      -- `⇑(vt.2.2 i) ∈ L¹_per` (from `Lp` at `γBar` via Hölder inclusion).
      have hg'_mem : MemLpPer (d := d) 1 (⇑(vt.2.2 i) : (Fin d → ℝ) → ℝ) := by
        have hLpγ :
            MemLpPer (d := d)
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              (⇑(vt.2.2 i) : (Fin d → ℝ) → ℝ) :=
          Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (vt.2.2 i))
        exact hLpγ.mono_exponent_finite Fact.out ENNReal.ofReal_ne_top
      -- Transport across the a.e. slot profiles (both `f` and `g`).
      exact hbase.congr_ae_unitCube hvt_val.symm hg'_mem (hvt_grad i).symm
  -- Step E: abstract VI at `vt`, unfolded to the concrete pairing integrand.
  have hvt_K : vt ∈ K := by rw [hKeq]; exact hvt_mem
  have h_vi : 0 ≤ A vt (vt - w) := hVI vt hvt_K
  have h_op : A vt (vt - w)
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i x => (⇑(vt.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑vt.1) (⇑vt.2.1)
          (fun i => (⇑((vt - w).2.2 i) : (Fin d → ℝ) → ℝ))
          (⇑(vt - w).1) (⇑(vt - w).2.1) := by
    rw [hAeq]
    exact congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hvt_mem (vt - w)
  -- a.e. profiles of the primal slots and the difference test slots.
  have hμδ_ae : (⇑vt.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] ρ := hvt_dens
  have hυ_ae : (⇑vt.2.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [hvt_val] with x hx
    rw [hx, hw_u, hψ_coe]
  have hDυ_ae : ∀ i, (⇑(vt.2.2 i) : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => Du i x
        + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
            (Fin d → ℝ) → ℝ) x) := by
    intro i
    filter_upwards [hvt_grad i] with x hx
    rw [hx, hw_Du i, hDψ_coe i]
  have hqm_ae : (⇑(vt - w).1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => ρ x - m x) := by
    have hsub : (vt - w).1 = vt.1 - w.1 := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub vt.1 w.1, hvt_dens] with x hx hxρ
    rw [hx, Pi.sub_apply, hxρ, hw_m]
  have hqu_ae : (⇑(vt - w).2.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => t * (φ : (Fin d → ℝ) → ℝ) x) := by
    have hsub : (vt - w).2.1 = vt.2.1 - w.2.1 := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub vt.2.1 w.2.1, hvt_val] with x hx hxv
    rw [hx, Pi.sub_apply, hxv, hψ_coe]; ring
  have hqDu_ae : ∀ i, (⇑((vt - w).2.2 i) : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)]
      (fun x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
          (Fin d → ℝ) → ℝ) x) := by
    intro i
    have hsub : (vt - w).2.2 i = vt.2.2 i - w.2.2 i := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub (vt.2.2 i) (w.2.2 i),
      hvt_grad i] with x hx hxg
    rw [hx, Pi.sub_apply, hxg, hDψ_coe i]; ring
  -- Concrete bare profiles for the perturbed primal slots.
  set μδc : (Fin d → ℝ) → ℝ := ρ with hμδc
  set υc : (Fin d → ℝ) → ℝ :=
    fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x with hυc
  set Dυc : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => Du i x
      + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x
    with hDυc
  set ηc : (Fin d → ℝ) → ℝ := fun x => ρ x - m x with hηc
  set νc : (Fin d → ℝ) → ℝ :=
    fun x => t * (φ : (Fin d → ℝ) → ℝ) x with hνc
  set Dνc : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
        (Fin d → ℝ) → ℝ) x with hDνc
  -- Rewrite both primal and test slots in `h_op` to the concrete profiles.
  rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        (fun i x => (⇑(vt.2.2 i) : (Fin d → ℝ) → ℝ) x) Dυc
        (⇑vt.1) μδc (⇑vt.2.1) υc
        (fun i => (⇑((vt - w).2.2 i) : (Fin d → ℝ) → ℝ))
        (⇑(vt - w).1) (⇑(vt - w).2.1)
        (fun i => hDυ_ae i) hμδ_ae hυ_ae] at h_op
  rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        Dυc μδc υc
        (fun i => (⇑((vt - w).2.2 i) : (Fin d → ℝ) → ℝ)) Dνc
        (⇑(vt - w).1) ηc (⇑(vt - w).2.1) νc
        (fun i => hqDu_ae i) hqm_ae hqu_ae] at h_op
  -- The test triple `(ηc, νc, Dνc)` equals the difference `(μδc-m, υc-u, Dυc-Du)`.
  have hηc_eq : ηc = μδc - m := by funext x; rw [hηc, hμδc]; rfl
  have hνc_eq : νc = υc - u := by
    funext x; rw [hνc, hυc]; simp [Pi.sub_apply]
  have hDνc_eq : Dνc = (fun i x => Dυc i x - Du i x) := by
    funext i x; rw [hDνc, hDυc]; ring
  rw [hηc_eq, hνc_eq, hDνc_eq] at h_op
  -- Expand via the pairing identity.
  rw [mfgOperatorEpsPair_pairing_eq (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        Dυc Du μδc υc m u] at h_op
  -- Now `h_op` is exactly the pairing-eq RHS at the perturbed pair.
  rw [h_op] at h_vi
  -- Divide by `t > 0`: `0 ≤ I ⇒ 0 ≤ (1/t)·I`.
  have ht_inv_nn : 0 ≤ 1 / t := by positivity
  have hmul := mul_le_mul_of_nonneg_left h_vi ht_inv_nn
  rw [mul_zero] at hmul
  -- Unfold the abbreviations.  `μδc = ρ = max(m,δ)`, `υc`, `Dυc` are the bare
  -- perturbed primal slots; the test slots `Dυc - Du`, `υc - u` cancel
  -- pointwise to `t·∇φ`, `t·φ`.
  simp only [hμδc, hυc, hDυc, hρdef] at hmul
  -- Rewrite the two integrals of `hmul` to the displayed (cancelled) integrands.
  have hI1 :
      (∫ x in UnitCube d,
          (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              - H x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
              + V x) * (max (m x) δ - m x)
            + max (m x) δ
                * (DpH x
                    (fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    (max (m x) δ)
                  ⬝ (fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x - Du i x))
            + (max (m x) δ - 1)
                * (u x + t * (φ : (Fin d → ℝ) → ℝ) x - u x)
          ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d,
          (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              - H x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
              + V x) * (max (m x) δ - m x)
            + max (m x) δ
                * (DpH x
                    (fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    (max (m x) δ)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
            + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hcancel :
        (fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x - Du i x)
          = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
      funext i; ring
    simp only [hcancel]; ring
  have hI2 :
      (∫ x in UnitCube d,
          vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x - Du i x))
          + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                * (u x + t * (φ : (Fin d → ℝ) → ℝ) x - u x))
          ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d,
          vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
          + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                * (t * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hcancel :
        (fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x - Du i x)
          = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
      funext i; ring
    simp only [hcancel]; ring
  rw [hI1, hI2] at hmul
  exact hmul

/-- **Per-test-pair regularized weak VI (core, `hcong`-exponents).**

For an arbitrary admissible test pair `(μ, υ, Dυ)` lifted to the Banach domain
`congestionBanachK`, the abstract VI at the witness `w` gives
`0 ≤ A vT (vT - w)`; the on-domain operator identity
`congestionAepsiOpK_apply_of_mem` rewrites this to a `mfgOperatorEpsPair`
inequality at the lifted slots; two a.e.-congruences
(`mfgOperatorEpsPair_congr_ae_primal` for the primal `(Dυ, μ, υ)` slots,
`mfgOperatorEpsPair_congr_ae` for the test direction `(μ-m, υ-u, Dυ-Du)`) move
it to the bare-function shape.  Unlike `congestion_VI_firstvar_ineq`, the
off-diagonal flux / `(μ-1)·ν` / ε-Gateaux terms are **not** collapsed — the
full regularized operator is retained, as the general test pair has nonzero
value/gradient test direction.

This is the per-test-pair handle the parent `…-vIEps-remove` projects for
`hVIeps` (Gaps 1+2). -/
theorem congestion_vIEps_at_testPair
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ)
    (hυ_sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) υ)
    (hDυ_mem : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dυ i))
    (hDυ_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i))
    (hdom : (μ, υ) ∈ congestionDomainK (d := d)
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : m =ᵐ[volume.restrict (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ))
    (hw_u : u =ᵐ[volume.restrict (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (hw_Du : ∀ i,
      Du i =ᵐ[volume.restrict (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε Dυ μ υ
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
  classical
  -- Step A: lift the bare test pair to the Banach domain.
  obtain ⟨vT, hvT_dens, hvT_val, hvT_grad, hvT_mem⟩ :=
    congestionBanachLift_of_testData (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      hμ_mem hυ_sob hDυ_mem hDυ_weak hdom
  -- Step B: abstract VI at `vT`.
  have hvT_K : vT ∈ K := by rw [hKeq]; exact hvT_mem
  have h_vi : 0 ≤ A vT (vT - w) := hVI vT hvT_K
  -- Step C: on-domain operator identity.
  have h_op : A vT (vT - w)
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i x => (⇑(vT.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑vT.1) (⇑vT.2.1)
          (fun i => (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ))
          (⇑(vT - w).1) (⇑(vT - w).2.1) := by
    rw [hAeq]
    exact congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hvT_mem (vT - w)
  -- Step D: a.e. profiles of the test-direction slots (`vT - w`).
  have hqm_ae : (⇑(vT - w).1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] (μ - m) := by
    have hsub : (vT - w).1 = vT.1 - w.1 := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub vT.1 w.1, hvT_dens, hw_m]
      with x hx hxμ hxm
    rw [hx, Pi.sub_apply, hxμ, Pi.sub_apply, hxm]
  have hqu_ae : (⇑(vT - w).2.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
    have hsub : (vT - w).2.1 = vT.2.1 - w.2.1 := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub vT.2.1 w.2.1, hvT_val, hw_u]
      with x hx hxυ hxu
    rw [hx, Pi.sub_apply, hxυ, Pi.sub_apply, hxu]
  have hqDu_ae : ∀ i, (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
    intro i
    have hsub : (vT - w).2.2 i = vT.2.2 i - w.2.2 i := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub (vT.2.2 i) (w.2.2 i),
      hvT_grad i, hw_Du i] with x hx hxDυ hxDu
    rw [hx, Pi.sub_apply, hxDυ, hxDu]
  -- Step E: rewrite `h_op` to the bare test-pair shape via two a.e.-congruences.
  rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        (fun i x => (⇑(vT.2.2 i) : (Fin d → ℝ) → ℝ) x) Dυ
        (⇑vT.1) μ (⇑vT.2.1) υ
        (fun i => (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ))
        (⇑(vT - w).1) (⇑(vT - w).2.1)
        (fun i => hvT_grad i) hvT_dens hvT_val] at h_op
  rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        Dυ μ υ
        (fun i => (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ))
        (fun i x => Dυ i x - Du i x)
        (⇑(vT - w).1) (μ - m) (⇑(vT - w).2.1) (υ - u)
        (fun i => hqDu_ae i) hqm_ae hqu_ae] at h_op
  rw [h_op] at h_vi
  exact h_vi

/-- **Exponent-transported per-test-pair regularized weak VI.**

`subst`/`cast_eq`-collapse wrapper around `congestion_vIEps_at_testPair`, for the
abstract exponents `(αh, βh)` arising from `CongestionAprioriPowerData`'s
projections (`h.α`, `h.β`).  Mirrors the skeleton of
`weak_is_strong_HJB_le_of_witnessData_powTransport`. -/
theorem congestion_vIEps_at_testPair_powTransport
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) μ)
    (hυ_sob : MemSobolevPer (d := d) (ENNReal.ofReal (αh * (βh + 1) / βh)) υ)
    (hDυ_mem : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (αh * (βh + 1) / βh)) (Dυ i))
    (hDυ_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i))
    (hdom : (μ, υ) ∈ congestionDomainK (d := d)
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : m =ᵐ[volume.restrict (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ))
    (hw_u : u =ᵐ[volume.restrict (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (hw_Du : ∀ i,
      Du i =ᵐ[volume.restrict (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (αh * (βh + 1) / βh) ε Dυ μ υ
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
  subst hpowβ_eq
  subst hpowα_eq
  rw [cast_eq] at hAeq hKeq
  exact congestion_vIEps_at_testPair hmon hcong hμ_mem hυ_sob hDυ_mem hDυ_weak
    hdom hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du

/-- **Positive-witness per-`δ` VI integral sibling of `perdelta_vi_integral_le`**
(paper `lem:weak.is.strong`, Step 1, on the a.e. set `{0 < m x}`).

Identical conclusion to `perdelta_vi_integral_le`, but the standing full-`ℝ`
continuity `hcont` is weakened to `ContinuousOn (Ioi 0)`, at the cost of the
extra a.e. positivity witness `hm_pos : 0 < m x`. Steps A/B (the `μ ∈ L^{β̄}_per`
and quotient-dominator memberships) are routed through the positive-witness
siblings `muAux_mem_Lp_of_witnessData_pos` (child-A) and
`muAux_quotient_dominator_memLp_of_m_pos`; every other ingredient is reused
verbatim. The original is kept untouched. -/
theorem perdelta_vi_integral_le_of_m_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) δ) - V x)
          * (max (muAux k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- Step A (positive-witness): `μ ∈ L^{β̄}_per`.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_pos hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos h_anti h_cont h_ne_all
  -- Step B (positive-witness): the quotient dominator membership.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_pos hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos h_anti h_cont h_ne_all
  -- `μ ≥ 0` a.e. on the cube.
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact le_csInf (h_ne_all x) (fun b hb => hb.1)
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  simpa only [hρdef, hμdef] using hgoal

/-- **Nonnegative-witness per-`δ` VI integral sibling of `perdelta_vi_integral_le`**
(paper `lem:weak.is.strong`, Step 1, δ-truncation route, lines 1417–1506).

Identical conclusion to `perdelta_vi_integral_le`, with the standing full-`ℝ`
continuity `hcont` weakened to `ContinuousOn (Ioi 0)` and *no positivity witness
on `m`*. Steps A/B (the `μ ∈ L^{β̄}_per` and quotient-dominator memberships) route
through the nonneg-witness siblings `muAux_mem_Lp_of_witnessData_nonneg` and
`muAux_quotient_dominator_memLp_of_m_nonneg`; the `μ ≥ 0` a.e. fact is read off
non-emptiness (`le_csInf`); every other ingredient is reused verbatim. Strict
positivity enters only through the truncated test density `ρ = max(μ, δ)`,
`δ > 0`. The originals are kept untouched. -/
theorem perdelta_vi_integral_le_of_m_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) δ) - V x)
          * (max (muAux k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- Step A (nonneg-witness): `μ ∈ L^{β̄}_per`.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_nonneg hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  -- Step B (nonneg-witness): the quotient dominator membership.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_nonneg hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  -- `μ ≥ 0` a.e. on the cube.
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact le_csInf (h_ne_all x) (fun b hb => hb.1)
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  simpa only [hρdef, hμdef] using hgoal

/-- **a.e.-rider sibling of `perdelta_vi_integral_le_of_m_pos`** (child-F).

Identical conclusion, but the pointwise closed-`Ici 0` antitonicity/continuity
and pointwise nonemptiness are dropped in favour of the a.e.-on-`Ioi 0`
antitonicity `hae_anti` (with `hcont`/`hne`/`hm_pos` already a.e.). Steps A/B
route through the a.e.-rider siblings `muAux_mem_Lp_of_witnessData_pos'` and
`muAux_quotient_dominator_memLp_of_m_pos'`; the `μ ≥ 0` a.e. fact is supplied by
the unconditional `muAux_nonneg`. Everything else is reused verbatim. -/
theorem perdelta_vi_integral_le_of_m_pos'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) δ) - V x)
          * (max (muAux k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- Step A (a.e.-rider): `μ ∈ L^{β̄}_per`.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_pos' hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  -- Step B (a.e.-rider): the quotient dominator membership.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_pos' hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  -- `μ ≥ 0` everywhere (unconditional).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  simpa only [hρdef, hμdef] using hgoal

/-- **`AEStronglyMeasurable V` sibling of `perdelta_vi_integral_le_of_m_pos'`**
(child-G).

Identical to the primed version, but `V` is only `AEStronglyMeasurable` (`hV_aesm`,
which coincides with the `hVmeas` already threaded into the VI machinery). Steps A/B
route through the `_aesm` siblings `muAux_mem_Lp_of_witnessData_pos_aesm` and
`muAux_quotient_dominator_memLp_of_m_pos_aesm`. The `_pos'` original is kept
untouched. -/
theorem perdelta_vi_integral_le_of_m_pos_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) δ) - V x)
          * (max (muAux k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- Step A (`_aesm`): `μ ∈ L^{β̄}_per`.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_pos_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  -- Step B (`_aesm`): the quotient dominator membership.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_pos_aesm hmon hcong hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  -- `μ ≥ 0` everywhere (unconditional).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  simpa only [hρdef, hμdef] using hgoal

/-- **Nonneg-`aesm` sibling of `perdelta_vi_integral_le_of_m_pos_aesm`**
(child-D2b, the δ-truncation route; paper `lem:weak.is.strong`, Step 1).

Identical conclusion (the per-`δ` truncated variational inequality), with the
`_pos_aesm` version's `hm_pos` replaced by `hm_nn : 0 ≤ m x` a.e. and the
boundary-free producers swapped in: Step A uses
`muAux_mem_Lp_of_witnessData_nonneg_aesm`, Step B uses the (a:Hat0)
quotient-dominator `muAux_quotient_dominator_memLp_of_m_nonneg_aesm` (so the
`{μ=0}` boundary routes through `Hext`/`H_at_zero`, finiteness DERIVED from the
HJB bound, NOT `Hext_finite_at_zero`). No `0<m`, no Ici-0 continuity. The
`_pos_aesm` original is kept untouched. -/
theorem perdelta_vi_integral_le_of_m_nonneg_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) δ) - V x)
          * (max (muAux k m u V Du H x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- Step A (nonneg `_aesm`): `μ ∈ L^{β̄}_per`.
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_nonneg_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti
  -- Step B (nonneg `_aesm`): the quotient dominator membership ((a:Hat0) boundary).
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_nonneg_aesm hmon hcong hHat0 hAgree
      hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti
  -- `μ ≥ 0` everywhere (unconditional).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  have hγBar_ne :
      ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hγBar_ge_one :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    Fact.out
  have hu_Lp_γ :
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    hw_u ▸ Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp w.2.1)
  have hu_L1 : MemLpPer (d := d) 1 u :=
    hu_Lp_γ.mono_exponent_finite hγBar_ge_one hγBar_ne
  have hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have h := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at h
    exact h
  have hu_Sob :
      MemSobolevPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
    ⟨hu_Lp_γ, ⟨Du, hDu_weak⟩⟩
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdomC0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ_nn hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_m_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdomC0
  have hdom :
      (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
    rw [hρdef, hw_u]; exact hdomC0
  have hρ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) ρ := hdom.1
  obtain ⟨vδ, hvδ_slot, hvδ_dens, hvδ_mem⟩ :=
    mem_congestionBanachK_of_densityMemLp (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
      w hρ_mem hdom hcoeWeak_Du
  have hu_eq : vδ.2.1 = w.2.1 := congrArg Prod.fst hvδ_slot
  have hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i := fun i => by
    rw [show vδ.2.2 = w.2.2 from congrArg Prod.snd hvδ_slot]
  have hVI_vδ :
      ∫ x in UnitCube d,
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    vi_integral_le_of_mem_witnessComponents (d := d) hmon hcong
      hVmeas hV (ε := ε) (A := A) (K := K) (w := w)
      hAeq hKeq hVI hvδ_mem hu_eq hDu_eq
  have h_integrand_ae :
      (fun x =>
          ((w.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((vδ.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
            * ((vδ.1 : (Fin d → ℝ) → ℝ) x
                - (w.1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x =>
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)) := by
    filter_upwards [hvδ_dens] with x hx
    have hDu_pt : (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x) := by funext i; rw [hw_Du i]
    rw [hw_u, hw_m, hDu_pt, hx]
  have hgoal :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (ρ x) - V x) * (ρ x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    rw [← MeasureTheory.integral_congr_ae h_integrand_ae]
    exact hVI_vδ
  simpa only [hρdef, hμdef] using hgoal

/-- **Step 1, Sub-step A — the `δ → 0⁺` DCT passage producing `h_DCT k`**
(paper `lem:weak.is.strong`, Step 1, lines 1467, 1527–1533).

For each fixed `k > 0`, the per-`δ` variational inequality
`perdelta_vi_integral_le` holds for every `δ > 0`. Specialising to the
sequence `δSeq n := 1/(n+1) → 0⁺`, the per-`n` integrand of
`muAux_integral_tendsto` (at `μ := muAux k …`) matches the conclusion of
`perdelta_vi_integral_le` *exactly*. The DCT limit (delivered by
`muAux_integral_tendsto`) sends each such integral to the integral at
`μ = muAux k …`, and `le_of_tendsto` of the eventually-`≤ 0` sequence
yields the `h_DCT k` inequality

```
∫ (u + H(·, Du, muAux k …) − V)·(muAux k … − m) ≤ 0,
```

which is exactly the fourth hypothesis (`h_DCT k hk`) of
`weak_is_strong_HJB_le_of_perk_DCT`.

The two dominated-convergence bookkeeping inputs — measurability of the
per-`n` integrand (`hmeas`) and the common integrable dominator
(`bound`, `hbound_int`, `hbound`) — are threaded as hypotheses; they are
discharged in the sibling sub-tasks `child2b-iii-a-hmeas` and
`child2b-iii-b-hbound` from the standing measurability of `muAux` and the
Hamiltonian lower bound `eq:assH.lower.congestion`. The genuine analytic
content (pointwise `max(μ, δ_n) → μ` plus DCT) lives in
`muAux_integral_tendsto`, and the per-`n` `≤ 0` inequalities are the
materially-consumed output of `perdelta_vi_integral_le`. -/
theorem h_DCT_producer
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  -- The truncation sequence `δSeq n := 1/(n+1) → 0⁺`.
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- Per-`n` variational inequality from `perdelta_vi_integral_le`.
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) (δSeq n)) - V x)
            * (max (muAux k m u V Du H x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    fun n => perdelta_vi_integral_le hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du (hδ_pos n)
  -- `μ = muAux k …` is nonnegative a.e. (its `csInf` set is of nonneg values).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall (fun x => le_csInf (h_ne_all x) (fun b hb => hb.1))
  -- Discharge the per-`n` integrand measurability (`hmeas`) from the standing
  -- measurability hypotheses, via the level-set identity for `muAux`.
  have hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ | u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    exact ((hu_meas.add hHcomp).sub hV_meas) measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  have h_max_meas : ∀ n,
      Measurable (fun x => max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) :=
    fun n => h_mu_meas.max measurable_const
  have h_Hmax_meas : ∀ n, Measurable
      (fun x =>
        H x (fun i => Du i x) (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)))) :=
    fun n => hmon.toRegularityH.measurable_H.comp
      (measurable_id.prodMk
        ((Measurable.of_eval hDu_meas).prodMk (h_max_meas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x)
            (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) - V x)
          * (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      ((hu_meas.add (h_Hmax_meas n)).sub hV_meas).aestronglyMeasurable.mul
        ((h_max_meas n).sub hm_meas).aestronglyMeasurable
  -- ====================================================================
  -- Discharge the integrable dominator (`bound`, `hbound_int`, `hbound`)
  -- from the standing hypotheses (`child2b-iii-b-hbound`), specialised to
  -- `δSeq n = 1/(n+1) ∈ (0,1]`.
  -- ====================================================================
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  -- `μ ∈ L^{β+1}` (paper `eq:mu-bound`).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ :=
    muAux_mem_Lp_of_witnessData hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  -- The two Hölder factors of the dominator.
  -- `G1 x = |k| + ‖u x‖ + ‖V x‖ + C·((‖μ x‖ + 1)^β + 1)` in `L^{(β+1)/β}`.
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  -- `F2 x = ‖μ x - m x‖ + 1` in `L^{β+1}`.
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  -- `(‖μ x‖ + 1)^β ∈ L^{(β+1)/β}`: the `β`-power of `‖μ‖ + 1 ∈ L^{β+1}`.
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  -- `G1 ∈ L^{(β+1)/β}`.
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hk : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : Fin d → ℝ => |k|) := MemLpPer.const _
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := ((hk.add hu').add hV').add hCpow
    exact this
  -- `F2 ∈ L^{β+1}`.
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  -- Hölder conjugates `((β+1)/β, β+1)`.
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]
      field_simp
  -- The dominator and its integrability via Hölder.
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  -- Per-`n` pointwise domination `‖gδ_n‖ ≤ bound`.
  -- The Hamiltonian congestion lower bound `H x p ρ ≥ -C(ρ^β + 1)` (ρ > 0),
  -- dropping the nonnegative first term of `hcong.lower`.
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hτ1 : (0 : ℝ) < ρ ^ hcong.τ + 1 := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ - (C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β)))
            - C * (ρ ^ β + 1) ≥ - (C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hμ_nn, h_anti |> Filter.Eventually.of_forall,
      hH_lower] with x hxμ_nn _ hxH_lower
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    -- `factor1 = u x + H x (Du x) ρ - V x`.
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    -- Upper bound `factor1 ≤ k` via the `csInf`-attained constraint.
    have hμ_constraint :
        u x + H x (fun i => Du i x) (μ x) - V x ≤ k := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn (h_cont x)
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      have h_inf_mem : sInf (muAuxSet k m u V Du H x)
          ∈ muAuxSet k m u V Du H x :=
        h_closed.csInf_mem (h_ne_all x) h_bdd
      have hcon := h_inf_mem.2.2
      have hμx : μ x = sInf (muAuxSet k m u V Du H x) := by
        rw [hμdef, muAux_def]
      rw [hμx]
      exact hcon
    -- On-`Ici 0` antitonicity, applied at `μ x ≤ ρ` (both in `[0, ∞)`).
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      h_anti x (Set.mem_Ici.mpr hxμ_nn) (Set.mem_Ici.mpr hρ_pos.le) hρ_ge_μ
    have hf1_upper : factor1 ≤ k := by
      rw [hf1def]; linarith [hμ_constraint, hHanti_le]
    -- Lower bound `factor1 ≥ -‖u x‖ - ‖V x‖ - C((‖μ x‖ + 1)^β + 1)`.
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    -- `‖factor1‖ ≤ G1 x`.
    have hG1_nonneg : 0 ≤ |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      have h2 : 0 ≤ |k| := abs_nonneg k
      positivity
    have hf1_abs : |factor1| ≤ G1 x := by
      rw [hG1def, abs_le]
      constructor
      · have hkabs : -(|k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1))
            ≤ -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) := by
          have : 0 ≤ |k| := abs_nonneg k
          linarith
        exact le_trans hkabs hf1_lower
      · have hk_le : k ≤ |k| := le_abs_self k
        have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
          have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
          positivity
        linarith [hf1_upper, hk_le]
    -- `‖factor2‖ ≤ F2 x`.
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hρ_ge_μ]
        · linarith [hρ_le]
      linarith [hsplit, hρμ]
    -- Combine.
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            apply mul_le_mul hf1_abs hf2_abs (abs_nonneg _)
            rw [hG1def]; exact hG1_nonneg
      _ = bound x := by rw [hbounddef]
  -- The genuine `δ → 0⁺` DCT limit at `μ = muAux k …`.
  have htendsto :=
    muAux_integral_tendsto (m := m) (u := u) (V := V) (H := H) (Du := Du)
      (μ := μ) (δSeq := δSeq) hδ_lim hμ_nn hcont
      bound hbound_int hmeas hbound
  -- Close: the limit of an eventually-`≤ 0` sequence is `≤ 0`.
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

/-- **Positive-witness sibling of `h_DCT_producer`** (on `{0 < m x}`).

Same post-DCT integral conclusion as `h_DCT_producer`, but the full-`ℝ`
continuity hypothesis is replaced by on-`(0,∞)` continuity of `H(x, Du x, ·)`
together with a.e. strict positivity `0 < m x`. The three deep helpers that
consume continuity — the per-`δ` VI inequality, the `μ ∈ L^{β̄}` envelope, and
the `δ → 0⁺` DCT passage — are routed through their `_of_m_pos` siblings
(`perdelta_vi_integral_le_of_m_pos`, `muAux_mem_Lp_of_witnessData_pos`,
`muAux_integral_tendsto_of_m_pos`). The on-`Ici 0` pointwise antitonicity /
continuity facts (`h_anti`, `h_cont`) are still supplied as standing hypotheses;
they only feed the bound estimate (which already restricts to `μ x ≥ 0`) and
the `muAux` measurability, not the limit passage. The original is kept
untouched. -/
theorem h_DCT_producer_of_m_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  -- The truncation sequence `δSeq n := 1/(n+1) → 0⁺`.
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- Per-`n` variational inequality from `perdelta_vi_integral_le_of_m_pos`.
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) (δSeq n)) - V x)
            * (max (muAux k m u V Du H x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    fun n => perdelta_vi_integral_le_of_m_pos hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos h_anti h_cont h_ne_all
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du (hδ_pos n)
  -- `μ = muAux k …` is nonnegative a.e. (its `csInf` set is of nonneg values).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall (fun x => le_csInf (h_ne_all x) (fun b hb => hb.1))
  -- `m x ≤ μ x` everywhere (every element of the constraint set dominates `m x`).
  have hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall
      (fun x => le_csInf (h_ne_all x) (fun b hb => hb.2.1))
  -- Discharge the per-`n` integrand measurability (`hmeas`).
  have hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ | u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    exact ((hu_meas.add hHcomp).sub hV_meas) measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  have h_max_meas : ∀ n,
      Measurable (fun x => max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) :=
    fun n => h_mu_meas.max measurable_const
  have h_Hmax_meas : ∀ n, Measurable
      (fun x =>
        H x (fun i => Du i x) (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)))) :=
    fun n => hmon.toRegularityH.measurable_H.comp
      (measurable_id.prodMk
        ((Measurable.of_eval hDu_meas).prodMk (h_max_meas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x)
            (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) - V x)
          * (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      ((hu_meas.add (h_Hmax_meas n)).sub hV_meas).aestronglyMeasurable.mul
        ((h_max_meas n).sub hm_meas).aestronglyMeasurable
  -- The integrable dominator (`bound`, `hbound_int`, `hbound`).
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  -- `μ ∈ L^{β+1}` (positive-witness envelope).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_pos hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos h_anti h_cont h_ne_all
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hk : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : Fin d → ℝ => |k|) := MemLpPer.const _
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := ((hk.add hu').add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]
      field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hτ1 : (0 : ℝ) < ρ ^ hcong.τ + 1 := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ - (C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β)))
            - C * (ρ ^ β + 1) ≥ - (C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hμ_nn, h_anti |> Filter.Eventually.of_forall,
      hH_lower] with x hxμ_nn _ hxH_lower
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    have hμ_constraint :
        u x + H x (fun i => Du i x) (μ x) - V x ≤ k := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn (h_cont x)
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      have h_inf_mem : sInf (muAuxSet k m u V Du H x)
          ∈ muAuxSet k m u V Du H x :=
        h_closed.csInf_mem (h_ne_all x) h_bdd
      have hcon := h_inf_mem.2.2
      have hμx : μ x = sInf (muAuxSet k m u V Du H x) := by
        rw [hμdef, muAux_def]
      rw [hμx]
      exact hcon
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      h_anti x (Set.mem_Ici.mpr hxμ_nn) (Set.mem_Ici.mpr hρ_pos.le) hρ_ge_μ
    have hf1_upper : factor1 ≤ k := by
      rw [hf1def]; linarith [hμ_constraint, hHanti_le]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    have hG1_nonneg : 0 ≤ |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      have h2 : 0 ≤ |k| := abs_nonneg k
      positivity
    have hf1_abs : |factor1| ≤ G1 x := by
      rw [hG1def, abs_le]
      constructor
      · have hkabs : -(|k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1))
            ≤ -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) := by
          have : 0 ≤ |k| := abs_nonneg k
          linarith
        exact le_trans hkabs hf1_lower
      · have hk_le : k ≤ |k| := le_abs_self k
        have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
          have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
          positivity
        linarith [hf1_upper, hk_le]
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hρ_ge_μ]
        · linarith [hρ_le]
      linarith [hsplit, hρμ]
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            apply mul_le_mul hf1_abs hf2_abs (abs_nonneg _)
            rw [hG1def]; exact hG1_nonneg
      _ = bound x := by rw [hbounddef]
  -- The genuine `δ → 0⁺` DCT limit at `μ = muAux k …` (positive-witness).
  have htendsto :=
    muAux_integral_tendsto_of_m_pos (m := m) (u := u) (V := V) (H := H) (Du := Du)
      (μ := μ) (δSeq := δSeq) hδ_lim hm_pos hm_le_mu hcont
      bound hbound_int hmeas hbound
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

/-- **Shared `δ → 0⁺` DCT engine** (paper `lem:weak.is.strong`, Step 1,
δ-truncation route, lines 1417–1506).

Factored out of `h_DCT_producer_of_m_nonneg` (iter-1108, task P6a0c): given the
per-`δ` family of truncated integral inequalities
`hperdelta : ∀ n, ∫ (u + H(Du, max(μ,δ)) − V)·(max(μ,δ) − m) ≤ 0`
(at the auxiliary density `μ = muAux k m u V Du H`), the `δ → 0⁺` dominated
convergence passage (`muAux_integral_tendsto_of_m_nonneg`) produces the limit
integral inequality `∫ (u + H(Du, μ) − V)·(μ − m) ≤ 0`.

This isolates the DCT machinery (envelope/dominator construction +
`muAux_integral_tendsto_of_m_nonneg`) so that BOTH the cone-VI route
(`h_DCT_producer_of_m_nonneg`, supplying `hperdelta` via
`perdelta_vi_integral_le_of_m_nonneg`) AND the periodic-VI route
(`h_DCT_of_abstractPeriodicVI`, supplying `hperdelta` via
`congestionLimitVI_integral_le_of_abstract_at_periodicDensity` at the periodic
truncated test pair) reuse the same `δ → 0` engine. The body is the post-`hperdelta`
tail of the original producer verbatim; only the analytic inputs are taken as
hypotheses (no Banach/cone data). -/
theorem h_DCT_of_perdelta
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
    (hm_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hperdelta : ∀ n : ℕ,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x)
              (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) - V x)
            * (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1)) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall (fun x => le_csInf (h_ne_all x) (fun b hb => hb.1))
  have hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall
      (fun x => le_csInf (h_ne_all x) (fun b hb => hb.2.1))
  have hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ | u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    exact ((hu_meas.add hHcomp).sub hV_meas) measurableSet_Iic
  have h_mu_meas : Measurable (muAux k m u V Du H) :=
    muAux_measurable_of_Ici0 hm_meas hHJB_meas h_anti h_cont h_ne_all
  have h_max_meas : ∀ n,
      Measurable (fun x => max (muAux k m u V Du H x) (δSeq n)) :=
    fun n => h_mu_meas.max measurable_const
  have h_Hmax_meas : ∀ n, Measurable
      (fun x =>
        H x (fun i => Du i x) (max (muAux k m u V Du H x) (δSeq n))) :=
    fun n => hmon.toRegularityH.measurable_H.comp
      (measurable_id.prodMk
        ((Measurable.of_eval hDu_meas).prodMk (h_max_meas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x)
            (max (muAux k m u V Du H x) (δSeq n)) - V x)
          * (max (muAux k m u V Du H x) (δSeq n) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      ((hu_meas.add (h_Hmax_meas n)).sub hV_meas).aestronglyMeasurable.mul
        ((h_max_meas n).sub hm_meas).aestronglyMeasurable
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  -- `μ ∈ L^{β+1}` (nonneg-witness envelope).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_nonneg hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hk : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : Fin d → ℝ => |k|) := MemLpPer.const _
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := ((hk.add hu').add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]
      field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hτ1 : (0 : ℝ) < ρ ^ hcong.τ + 1 := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ - (C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β)))
            - C * (ρ ^ β + 1) ≥ - (C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  have hf1_all : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hμ_nn, h_anti |> Filter.Eventually.of_forall,
      hH_lower] with x hxμ_nn _ hxH_lower
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    have hμ_constraint :
        u x + H x (fun i => Du i x) (μ x) - V x ≤ k := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn (h_cont x)
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      have h_inf_mem : sInf (muAuxSet k m u V Du H x)
          ∈ muAuxSet k m u V Du H x :=
        h_closed.csInf_mem (h_ne_all x) h_bdd
      have hcon := h_inf_mem.2.2
      have hμx : μ x = sInf (muAuxSet k m u V Du H x) := by
        rw [hμdef, muAux_def]
      rw [hμx]
      exact hcon
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      h_anti x (Set.mem_Ici.mpr hxμ_nn) (Set.mem_Ici.mpr hρ_pos.le) hρ_ge_μ
    have hf1_upper : factor1 ≤ k := by
      rw [hf1def]; linarith [hμ_constraint, hHanti_le]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    show |factor1| ≤ G1 x
    rw [hG1def, abs_le]
    constructor
    · have hkabs : -(|k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1))
          ≤ -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) := by
        have : 0 ≤ |k| := abs_nonneg k
        linarith
      exact le_trans hkabs hf1_lower
    · have hk_le : k ≤ |k| := le_abs_self k
      have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
        have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
        positivity
      linarith [hf1_upper, hk_le]
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hf1_all n, hμ_nn] with x hxf1 hxμ_nn
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n, hxμ_nn]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    have hf1_abs : |factor1| ≤ G1 x := hxf1
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hρ_ge_μ]
        · linarith [hρ_le]
      linarith [hsplit, hρμ]
    have hG1_nonneg : 0 ≤ G1 x := by
      rw [hG1def]
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      have h2 : 0 ≤ |k| := abs_nonneg k
      positivity
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            apply mul_le_mul hf1_abs hf2_abs (abs_nonneg _) hG1_nonneg
      _ = bound x := by rw [hbounddef]
  have htendsto :=
    muAux_integral_tendsto_of_m_nonneg (m := m) (u := u) (V := V) (H := H) (Du := Du)
      (μ := μ) (δSeq := δSeq) hδ_lim hm_nn hμ_nn hm_le_mu hcont
      G1 hf1_all bound hbound_int hmeas hbound
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

/-- **Nonnegative-witness sibling of `h_DCT_producer`** (paper `lem:weak.is.strong`,
Step 1, δ-truncation route, lines 1417–1506).

Same post-DCT integral conclusion as `h_DCT_producer`, with the full-`ℝ`
continuity weakened to on-`(0,∞)` continuity of `H(x, Du x, ·)` and *no positivity
witness on `m`*. The per-`δ` VI and `μ ∈ L^{β̄}` envelope route through the
nonneg-witness siblings (`perdelta_vi_integral_le_of_m_nonneg`,
`muAux_mem_Lp_of_witnessData_nonneg`). The `δ → 0⁺` passage uses
`muAux_integral_tendsto_of_m_nonneg`, whose pointwise limit is established by a
case split on the limit point `μ x ≥ 0`: on `{0 < μ x}` continuity on `Ioi 0`
suffices, while on `{μ x = 0}` (forcing `m x = 0`) the **target integrand
vanishes** and the sequence integrand `→ 0` because the first factor is bounded
uniformly in `δ` by `G1 x` and the second factor `δSeq n → 0`. The uniform
first-factor bound `hf1_all` is the same `|factor1| ≤ G1 x` estimate already
produced for the dominator. The original is kept untouched.

Refactored (iter-1108, P6a0c): the post-`hperdelta` body is now the shared
`h_DCT_of_perdelta` engine; this producer only supplies `hperdelta` via the
cone-VI `perdelta_vi_integral_le_of_m_nonneg`. -/
theorem h_DCT_producer_of_m_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
    (hm_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  -- Per-`n` truncated VI from the cone-VI `perdelta_vi_integral_le_of_m_nonneg`.
  have hperdelta : ∀ n : ℕ,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x)
              (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) - V x)
            * (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1)) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    intro n
    have hδ_pos : (0 : ℝ) < (1 : ℝ) / (↑n + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
      exact div_pos one_pos this
    exact perdelta_vi_integral_le_of_m_nonneg hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du hδ_pos
  -- The shared `δ → 0⁺` DCT engine.
  exact h_DCT_of_perdelta hmon hcong hm_meas hu_meas hV_meas hDu_meas
    hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn h_anti h_cont h_ne_all hperdelta

/-- **a.e.-rider sibling of `h_DCT_producer_of_m_pos`** (child-F).

Identical conclusion, but the pointwise closed-`Ici 0` antitonicity/continuity
and pointwise nonemptiness are dropped in favour of the a.e.-on-`Ioi 0`
antitonicity `hae_anti`. The per-`δ` VI and the `μ ∈ L^{β̄}` envelope route
through the a.e.-rider siblings `perdelta_vi_integral_le_of_m_pos'` and
`muAux_mem_Lp_of_witnessData_pos'`; `μ`-measurability is `AEMeasurable` (via
`muAux_measurable_of_Ioi0_of_m_pos`); the per-`n` integrand is therefore
assembled at the `AEStronglyMeasurable` level. The bound estimate, instead of
the pointwise `Ici 0` data, uses `muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos`
and the a.e.-on-`Ioi 0` antitonicity on the a.e. set `{0 < m x}` (where
`μ x ≥ m x > 0`). -/
theorem h_DCT_producer_of_m_pos'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- Per-`n` variational inequality from `perdelta_vi_integral_le_of_m_pos'`.
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) (δSeq n)) - V x)
            * (max (muAux k m u V Du H x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    fun n => perdelta_vi_integral_le_of_m_pos' hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du (hδ_pos n)
  -- `μ = muAux k …` is nonnegative everywhere (unconditional).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  -- `m x ≤ μ x` a.e. (every element of the constraint set dominates `m x`).
  have hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x ≤ muAux k m u V Du H x := by
    filter_upwards [hne] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  -- Discharge the per-`n` integrand measurability (`hmeas`).
  have hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ | u x + H x (fun i => Du i x) a - V x ≤ k } := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    exact ((hu_meas.add hHcomp).sub hV_meas) measurableSet_Iic
  -- `μ` is `AEMeasurable` (a.e.-on-`Ioi 0` route).
  have h_mu_aemeas : AEMeasurable (muAux k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muAux_measurable_of_Ioi0_of_m_pos hm_meas hHJB_meas hm_pos hae_anti hcont hne
  have h_max_aemeas : ∀ n,
      AEMeasurable (fun x => max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)))
        (volume.restrict (UnitCube d)) :=
    fun n => h_mu_aemeas.max aemeasurable_const
  have h_Hmax_aemeas : ∀ n, AEMeasurable
      (fun x =>
        H x (fun i => Du i x) (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))))
      (volume.restrict (UnitCube d)) :=
    fun n => hmon.toRegularityH.measurable_H.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk
        ((Measurable.of_eval hDu_meas).aemeasurable.prodMk (h_max_aemeas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x)
            (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) - V x)
          * (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      ((hu_meas.aemeasurable.add (h_Hmax_aemeas n)).sub
          hV_meas.aemeasurable).aestronglyMeasurable.mul
        ((h_max_aemeas n).sub hm_meas.aemeasurable).aestronglyMeasurable
  -- The integrable dominator (`bound`, `hbound_int`, `hbound`).
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  -- `μ ∈ L^{β+1}` (a.e.-rider envelope).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_pos' hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hk : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : Fin d → ℝ => |k|) := MemLpPer.const _
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := ((hk.add hu').add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]
      field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hτ1 : (0 : ℝ) < ρ ^ hcong.τ + 1 := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ - (C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β)))
            - C * (ρ ^ β + 1) ≥ - (C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hμ_nn, hae_anti, hH_lower, hm_pos, hne, hcont]
      with x hxμ_nn hx_anti hxH_lower hx_mpos hx_ne hx_cont
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    -- `μ x ≥ m x > 0` on the a.e. set `{0 < m x}`.
    have hμx_pos : 0 < μ x :=
      lt_of_lt_of_le hx_mpos (le_csInf hx_ne (fun b hb => hb.2.1))
    have hμ_constraint :
        u x + H x (fun i => Du i x) (μ x) - V x ≤ k := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hx_mpos hx_cont
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      have h_inf_mem : sInf (muAuxSet k m u V Du H x)
          ∈ muAuxSet k m u V Du H x :=
        h_closed.csInf_mem hx_ne h_bdd
      have hcon := h_inf_mem.2.2
      have hμx : μ x = sInf (muAuxSet k m u V Du H x) := by
        rw [hμdef, muAux_def]
      rw [hμx]
      exact hcon
    -- On-`Ioi 0` antitonicity, applied at `μ x ≤ ρ` (both in `(0, ∞)`).
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      hx_anti (Set.mem_Ioi.mpr hμx_pos) (Set.mem_Ioi.mpr hρ_pos) hρ_ge_μ
    have hf1_upper : factor1 ≤ k := by
      rw [hf1def]; linarith [hμ_constraint, hHanti_le]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    have hG1_nonneg : 0 ≤ |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      have h2 : 0 ≤ |k| := abs_nonneg k
      positivity
    have hf1_abs : |factor1| ≤ G1 x := by
      rw [hG1def, abs_le]
      constructor
      · have hkabs : -(|k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1))
            ≤ -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) := by
          have : 0 ≤ |k| := abs_nonneg k
          linarith
        exact le_trans hkabs hf1_lower
      · have hk_le : k ≤ |k| := le_abs_self k
        have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
          have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
          positivity
        linarith [hf1_upper, hk_le]
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hρ_ge_μ]
        · linarith [hρ_le]
      linarith [hsplit, hρμ]
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            apply mul_le_mul hf1_abs hf2_abs (abs_nonneg _)
            rw [hG1def]; exact hG1_nonneg
      _ = bound x := by rw [hbounddef]
  -- The genuine `δ → 0⁺` DCT limit at `μ = muAux k …` (positive-witness).
  have htendsto :=
    muAux_integral_tendsto_of_m_pos (m := m) (u := u) (V := V) (H := H) (Du := Du)
      (μ := μ) (δSeq := δSeq) hδ_lim hm_pos hm_le_mu hcont
      bound hbound_int hmeas hbound
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

/-- **`AEStronglyMeasurable V` sibling of `h_DCT_producer_of_m_pos'`** (child-G).

Identical to the primed version, but `V` is only `AEStronglyMeasurable` (`hV_aesm`).
The HJB sublevel set is `NullMeasurableSet`; per-`n` measurability and the
quotient-dominator membership route through the `_aesm` siblings. The `_pos'`
original is kept untouched. -/
theorem h_DCT_producer_of_m_pos_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- Per-`n` variational inequality from `perdelta_vi_integral_le_of_m_pos_aesm`.
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) (δSeq n)) - V x)
            * (max (muAux k m u V Du H x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    fun n => perdelta_vi_integral_le_of_m_pos_aesm hmon hcong hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du (hδ_pos n)
  -- `μ = muAux k …` is nonnegative everywhere (unconditional).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  -- `m x ≤ μ x` a.e. (every element of the constraint set dominates `m x`).
  have hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x ≤ muAux k m u V Du H x := by
    filter_upwards [hne] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  -- Discharge the per-`n` integrand measurability (`hmeas`).
  have hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k }
        (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        AEMeasurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x)
          (volume.restrict (UnitCube d)) :=
      ((hu_meas.add hHcomp).aemeasurable).sub hV_aesm.aemeasurable
    exact hfun.nullMeasurableSet_preimage measurableSet_Iic
  -- `μ` is `AEMeasurable` (a.e.-on-`Ioi 0` route, `_aesm`).
  have h_mu_aemeas : AEMeasurable (muAux k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muAux_measurable_of_Ioi0_of_m_pos_aesm hm_meas hHJB_nmeas hm_pos hae_anti
      hcont hne
  have h_max_aemeas : ∀ n,
      AEMeasurable (fun x => max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)))
        (volume.restrict (UnitCube d)) :=
    fun n => h_mu_aemeas.max aemeasurable_const
  have h_Hmax_aemeas : ∀ n, AEMeasurable
      (fun x =>
        H x (fun i => Du i x) (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))))
      (volume.restrict (UnitCube d)) :=
    fun n => hmon.toRegularityH.measurable_H.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk
        ((Measurable.of_eval hDu_meas).aemeasurable.prodMk (h_max_aemeas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x)
            (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) - V x)
          * (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      ((hu_meas.aemeasurable.add (h_Hmax_aemeas n)).sub
          hVmeas.aemeasurable).aestronglyMeasurable.mul
        ((h_max_aemeas n).sub hm_meas.aemeasurable).aestronglyMeasurable
  -- The integrable dominator (`bound`, `hbound_int`, `hbound`).
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  -- `μ ∈ L^{β+1}` (`_aesm` envelope).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_pos_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_pos hae_anti
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hk : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : Fin d → ℝ => |k|) := MemLpPer.const _
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := ((hk.add hu').add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]
      field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hτ1 : (0 : ℝ) < ρ ^ hcong.τ + 1 := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ - (C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β)))
            - C * (ρ ^ β + 1) ≥ - (C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hμ_nn, hae_anti, hH_lower, hm_pos, hne, hcont]
      with x hxμ_nn hx_anti hxH_lower hx_mpos hx_ne hx_cont
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    -- `μ x ≥ m x > 0` on the a.e. set `{0 < m x}`.
    have hμx_pos : 0 < μ x :=
      lt_of_lt_of_le hx_mpos (le_csInf hx_ne (fun b hb => hb.2.1))
    have hμ_constraint :
        u x + H x (fun i => Du i x) (μ x) - V x ≤ k := by
      have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
        muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hx_mpos hx_cont
      have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
        muAuxSet_bddBelow k m u V Du H x
      have h_inf_mem : sInf (muAuxSet k m u V Du H x)
          ∈ muAuxSet k m u V Du H x :=
        h_closed.csInf_mem hx_ne h_bdd
      have hcon := h_inf_mem.2.2
      have hμx : μ x = sInf (muAuxSet k m u V Du H x) := by
        rw [hμdef, muAux_def]
      rw [hμx]
      exact hcon
    -- On-`Ioi 0` antitonicity, applied at `μ x ≤ ρ` (both in `(0, ∞)`).
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      hx_anti (Set.mem_Ioi.mpr hμx_pos) (Set.mem_Ioi.mpr hρ_pos) hρ_ge_μ
    have hf1_upper : factor1 ≤ k := by
      rw [hf1def]; linarith [hμ_constraint, hHanti_le]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    have hG1_nonneg : 0 ≤ |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      have h2 : 0 ≤ |k| := abs_nonneg k
      positivity
    have hf1_abs : |factor1| ≤ G1 x := by
      rw [hG1def, abs_le]
      constructor
      · have hkabs : -(|k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1))
            ≤ -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) := by
          have : 0 ≤ |k| := abs_nonneg k
          linarith
        exact le_trans hkabs hf1_lower
      · have hk_le : k ≤ |k| := le_abs_self k
        have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
          have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
          positivity
        linarith [hf1_upper, hk_le]
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hρ_ge_μ]
        · linarith [hρ_le]
      linarith [hsplit, hρμ]
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            apply mul_le_mul hf1_abs hf2_abs (abs_nonneg _)
            rw [hG1def]; exact hG1_nonneg
      _ = bound x := by rw [hbounddef]
  -- The genuine `δ → 0⁺` DCT limit at `μ = muAux k …` (positive-witness).
  have htendsto :=
    muAux_integral_tendsto_of_m_pos (m := m) (u := u) (V := V) (H := H) (Du := Du)
      (μ := μ) (δSeq := δSeq) hδ_lim hm_pos hm_le_mu hcont
      bound hbound_int hmeas hbound
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

set_option maxHeartbeats 1600000 in
/-- **`δ → 0⁺` DCT engine from per-`δ` inequalities (nonneg `aesm` route)**
(paper `lem:weak.is.strong`, Step 1).

This is the `Ioi 0` / a.e. + `(a:Hat0)`-boundary sibling of `h_DCT_of_perdelta`:
it takes the per-`δ` integral inequalities `hperdelta` (at `δ = 1/(n+1)`) as a
hypothesis and runs the genuine `δ → 0⁺` dominated-convergence passage to the
limit `h_DCT k` inequality, using ONLY the a.e./`Ioi 0` data
(`hcont`, `hae_anti`, `hne`, `hm_nn`) plus the paper-faithful boundary device
`hHat0`/`hAgree` — NO closed-`Ici 0` / `∀ x` boundary hypotheses. The Lp envelope
is `muAux_mem_Lp_of_witnessData_nonneg_aesm`, the measurability is
`muAux_measurable_of_Ioi0_of_m_nonneg_aesm`, and the DCT limit is
`muAux_integral_tendsto_of_m_nonneg`. The first-factor upper bound
`|u + H(ρ) − V| ≤ k` for the truncation `ρ = max(μ,δ_n) > 0` is derived from the
boundary-free level-set lemma at `a = ρ`, with the `{μ=0}` branch routed through
`Hext`/`H_at_zero` (the `(a:Hat0)` device). This engine body is shared verbatim
with `h_DCT_producer_of_m_nonneg_aesm` (which only differs by supplying
`hperdelta` from the Banach VI rather than the abstract limit VI). -/
theorem h_DCT_of_perdelta_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hperdelta : ∀ n : ℕ,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x)
              (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) - V x)
            * (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1)) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- `μ = muAux k …` is nonnegative everywhere (unconditional).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muAux k m u V Du H x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  -- `m x ≤ μ x` a.e. (every element of the constraint set dominates `m x`).
  have hm_le_mu : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x ≤ muAux k m u V Du H x := by
    filter_upwards [hne] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  -- Discharge the per-`n` integrand measurability (`hmeas`).
  have hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k }
        (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hfun :
        AEMeasurable (fun x : Fin d → ℝ =>
          u x + H x (fun i => Du i x) a - V x)
          (volume.restrict (UnitCube d)) :=
      ((hu_meas.add hHcomp).aemeasurable).sub hV_aesm.aemeasurable
    exact hfun.nullMeasurableSet_preimage measurableSet_Iic
  have h_mu_aemeas : AEMeasurable (muAux k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muAux_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hm_nn hae_anti
      hcont hne
  have h_max_aemeas : ∀ n,
      AEMeasurable (fun x => max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)))
        (volume.restrict (UnitCube d)) :=
    fun n => h_mu_aemeas.max aemeasurable_const
  have h_Hmax_aemeas : ∀ n, AEMeasurable
      (fun x =>
        H x (fun i => Du i x) (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))))
      (volume.restrict (UnitCube d)) :=
    fun n => hmon.toRegularityH.measurable_H.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk
        ((Measurable.of_eval hDu_meas).aemeasurable.prodMk (h_max_aemeas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x)
            (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1))) - V x)
          * (max (muAux k m u V Du H x) (1 / ((n : ℝ) + 1)) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      ((hu_meas.aemeasurable.add (h_Hmax_aemeas n)).sub
          hV_aesm.aemeasurable).aestronglyMeasurable.mul
        ((h_max_aemeas n).sub hm_meas.aemeasurable).aestronglyMeasurable
  -- The integrable dominator (`bound`, `hbound_int`, `hbound`).
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  -- `μ ∈ L^{β+1}` (nonneg `_aesm` envelope).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_nonneg_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hk : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : Fin d → ℝ => |k|) := MemLpPer.const _
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := ((hk.add hu').add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]
      field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hτ1 : (0 : ℝ) < ρ ^ hcong.τ + 1 := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ - (C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1)) * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β)))
            - C * (ρ ^ β + 1) ≥ - (C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  -- The combined first-factor bound (`|factor1| ≤ G1`) and the product
  -- dominator (`‖factor1·factor2‖ ≤ bound`). The first-factor *upper* bound
  -- `factor1 ≤ k` for the truncation `ρ = max(μ,δ_n) > 0` is derived from the
  -- boundary-free level-set lemma at `a = ρ`, with the `{μ=0}` branch routed
  -- through `Hext`/`H_at_zero` (the (a:Hat0) device).
  have hcombined : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x ∧
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    filter_upwards [hμ_nn, hae_anti, hH_lower, hm_nn, hne, hcont,
        hHat0.exists_limit_at_zero, hAgree]
      with x hxμ_nn hx_anti hxH_lower hx_mnn hx_ne hx_cont hx_limit hx_agree
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hμx_nn : 0 ≤ μ x := muAux_nonneg x
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]
      apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    set b : ℝ := k - u x + V x with hb_def
    -- `H x (Du x) ρ ≤ b`, hence `factor1 ≤ k`.  Level-set lemma at `a = ρ`:
    -- `μ ≤ ρ ↔ m ≤ ρ ∧ (HJB(ρ) ≤ k ∨ μ ≤ 0)`.  Since `μ ≤ ρ`, the disjunction
    -- holds; the `μ ≤ 0` (= 0) branch routes through `Hext`.
    have hHρ_le_b : H x (fun i => Du i x) ρ ≤ b := by
      have hiff :=
        muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg
          (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H) (x := x)
          (a := ρ) hx_mnn hρ_pos.le hx_cont hx_anti hx_ne
      rcases (hiff.mp hρ_ge_μ).2 with hHJB | hμle0
      · -- `HJB(ρ) ≤ k`.
        rw [hb_def]; linarith
      · -- `μ ≤ 0`, i.e. `μ = 0`: route the boundary value through `Hext`.
        have hwit := (muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg
          (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H) (x := x)
          hx_mnn hx_anti hx_ne).mp hμle0
        -- `H(ν) ≤ b` for every `ν > 0` (uniform positive bound).  We split on
        -- whether some admissible witness equals `0`.
        have hPointwise : ∀ ν : ℝ, 0 < ν → H x (fun i => Du i x) ν ≤ b := by
          intro ν hν
          by_cases hzero : ∃ p : ℕ, ∃ q : ℚ,
              (q : ℝ) = 0 ∧ m x ≤ (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧
                (q : ℝ) < 1 / ((p : ℝ) + 1) ∧
                u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ k
          · -- Case A: a `q = 0` witness ⇒ raw `H(0) ≤ b`.  Since `H` is antitone
            -- on `Ioi 0` and `H(·) → H_at_zero = (H(0):WithTop)` along `𝓝[>]0`,
            -- `H(ν) ≤ H(0) ≤ b` for every `ν > 0`.
            obtain ⟨_, _, hq_eq0, _, _, _, hHJB_q⟩ := hzero
            have hH0_le_b : H x (fun i => Du i x) (0 : ℝ) ≤ b := by
              have : u x + H x (fun i => Du i x) (0 : ℝ) - V x ≤ k := by
                rw [← hq_eq0]; exact hHJB_q
              rw [hb_def]; linarith
            -- `H(·) → H_at_zero` along `𝓝[>]0`.
            have hTendsto :
                Filter.Tendsto
                  (fun s : ℝ => ((H x (fun i => Du i x) s : ℝ) : WithTop ℝ))
                  (nhdsWithin 0 (Set.Ioi 0))
                  (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
              Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
            -- Eventually along `𝓝[>]0`, `s < ν`, so `H(ν) ≤ H(s)` by antitone.
            have hEv :
                ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                  ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ)
                    ≤ ((H x (fun i => Du i x) s : ℝ) : WithTop ℝ) := by
              refine Filter.eventually_iff_exists_mem.mpr
                ⟨Set.Ioo (0 : ℝ) ν, ?_, fun s hs => ?_⟩
              · exact Ioo_mem_nhdsGT hν
              · have hs_pos : 0 < s := hs.1
                have hs_lt : s < ν := hs.2
                have hanti_le :
                    H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) s :=
                  hx_anti hs_pos hν hs_lt.le
                exact_mod_cast hanti_le
            -- `(H(ν):WithTop) ≤ H_at_zero`.
            have hHν_le_at0 :
                ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ)
                  ≤ Hamiltonian.H_at_zero H x (fun i => Du i x) :=
              ge_of_tendsto hTendsto hEv
            -- `H_at_zero = (H(0):WithTop)` (agreement) and `H(0) ≤ b`.
            have hAgree_x :
                ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
                  = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
              rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
            have hraw_le :
                ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ)
                  ≤ ((b : ℝ) : WithTop ℝ) := by
              refine le_trans hHν_le_at0 ?_
              rw [← hAgree_x]
              exact_mod_cast hH0_le_b
            exact_mod_cast hraw_le
          · -- Case B: every witness is positive ⇒ pick admissible `0 < q < ν`,
            -- antitone gives `H(ν) ≤ H(q) ≤ b`.
            obtain ⟨j, hj⟩ := exists_nat_one_div_lt hν
            obtain ⟨q, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ := hwit j
            have hq_lt_ν : (q : ℝ) < ν := by
              have h1 : (1 : ℝ) / ((j : ℝ) + 1) < ν := by
                simpa only [one_div] using hj
              exact lt_trans hq_hi h1
            have hq_pos : 0 < (q : ℝ) := by
              rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
              · exact absurd
                  ⟨j, q, hq0.symm, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ hzero
              · exact hq_pos
            have hHq : H x (fun i => Du i x) (q : ℝ) ≤ b := by
              rw [hb_def]; linarith [hHJB_q]
            have hanti_le :
                H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
              hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
            exact le_trans hanti_le hHq
        exact hPointwise ρ hρ_pos
    have hf1_upper : factor1 ≤ k := by
      rw [hf1def]; linarith [hHρ_le_b]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    have hG1_nonneg : 0 ≤ |k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      have h2 : 0 ≤ |k| := abs_nonneg k
      positivity
    have hf1_abs : |factor1| ≤ G1 x := by
      rw [hG1def, abs_le]
      constructor
      · have hkabs : -(|k| + ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1))
            ≤ -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) := by
          have : 0 ≤ |k| := abs_nonneg k
          linarith
        exact le_trans hkabs hf1_lower
      · have hk_le : k ≤ |k| := le_abs_self k
        have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
          have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
          positivity
        linarith [hf1_upper, hk_le]
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hρ_ge_μ]
        · linarith [hρ_le]
      linarith [hsplit, hρμ]
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    refine ⟨hf1_abs, ?_⟩
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            apply mul_le_mul hf1_abs hf2_abs (abs_nonneg _)
            rw [hG1def]; exact hG1_nonneg
      _ = bound x := by rw [hbounddef]
  have hf1_bd : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x :=
    fun n => (hcombined n).mono (fun _ h => h.1)
  have hbound : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x :=
    fun n => (hcombined n).mono (fun _ h => h.2)
  -- The genuine `δ → 0⁺` DCT limit at `μ = muAux k …` (nonneg route).
  have htendsto :=
    muAux_integral_tendsto_of_m_nonneg (m := m) (u := u) (V := V) (H := H) (Du := Du)
      (μ := μ) (δSeq := δSeq) hδ_lim hm_nn hμ_nn hm_le_mu hcont
      G1 hf1_bd bound hbound_int hmeas hbound
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

set_option maxHeartbeats 1600000 in
/-- **Nonneg-`aesm` sibling of `h_DCT_producer_of_m_pos_aesm`**
(child-D2b, the `δ → 0⁺` DCT passage; paper `lem:weak.is.strong`, Step 1).

Identical conclusion (the `h_DCT k` inequality), with the `_pos_aesm` version's
`hm_pos` replaced by `hm_nn` a.e., the per-`δ` VI supplied by
`perdelta_vi_integral_le_of_m_nonneg_aesm`, the Lp envelope by
`muAux_mem_Lp_of_witnessData_nonneg_aesm`, the measurability by
`muAux_measurable_of_Ioi0_of_m_nonneg_aesm`, and the DCT limit by
`muAux_integral_tendsto_of_m_nonneg`. The first-factor bound `|u+H(ρ)−V| ≤ k`
(needed both for `G1` and the dominator) is derived for the truncation
`ρ = max(μ,δ_n) > 0` from the boundary-free level-set lemma at `a = ρ`, with the
`{μ=0}` branch routed through `Hext`/`H_at_zero` (the (a:Hat0) device, finiteness
DERIVED from the HJB bound), NOT through `0<m`. The `_pos_aesm` original is kept
untouched. -/
theorem h_DCT_producer_of_m_nonneg_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
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
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- Per-`n` variational inequality from `perdelta_vi_integral_le_of_m_nonneg_aesm`.
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (muAux k m u V Du H x) (δSeq n)) - V x)
            * (max (muAux k m u V Du H x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    fun n => perdelta_vi_integral_le_of_m_nonneg_aesm hmon hcong hHat0 hAgree
      hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du (hδ_pos n)
  -- Delegate the entire `δ → 0⁺` DCT passage to the shared engine
  -- `h_DCT_of_perdelta_aesm`, supplying `hperdelta` from the Banach VI above.
  exact h_DCT_of_perdelta_aesm hmon hcong hHat0 hAgree hm_meas hu_meas hV_aesm
    hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti hperdelta

/-! ## Step 3 of paper Lemma `lem:weak.is.strong` — limit of the
`m_δ`-tested transport equation (`eq:transport-test-m.delta`)

Paper `Source/FGU-monotone_revised.tex`, lines 1530–1554.

The strategy of paper Step 3 is:

1. By `mdelta_admissibility` (`infra:P5-mdelta-admissibility`), the
   truncated pair `(m_δ, u + φ)` lies in `𝓚` for every `δ > 0` and
   every smooth test `φ`.
2. Test `eq:weak.epsi.cong` against `(m_δ, u + φ)`. After
   rearrangement and use of the lower bound
   `H(x, p, m_δ) ≥ -C(m_δ^β + 1)` from
   `Hamiltonian.lower_congestion_of_alternative` (applied to `m_δ > 0`),
   one obtains for every admissible `δ`:

   ```
   ∫ [(m_δ − 1)φ + m_δ · D_pH(x, Du+Dφ, m_δ)·Dφ] dx
     + ε-Gateaux terms
     ≥ ∫ (u + φ − C(m_δ^β + 1) − V)(m_δ − m) dx.
   ```
3. The integrability of all terms is uniform in `δ ∈ (0,1]` thanks to
   `eq:assH.DpH.upper.congestion` (i.e.
   `Hamiltonian.mDpH_mem_Lp_gammaBar'_congestion`) and the trivial
   bound `m_δ ≤ m + 1`. Hence dominated convergence applies along any
   sequence `δ_n → 0⁺`. As `m_δ → m` a.e., the RHS limit is `0`
   (since the multiplier `m_δ − m → 0` a.e.).
4. Conclude `eq:transport-test-m.delta` (paper line 1546) — the
   variational inequality with the same LHS evaluated at the limit
   `(m, u+φ)` and `0` on the right.

Following the modular policy adopted in `WellDefined.lean`,
`MuIntegrability.lean`, and `weak_is_strong_HJB_le_at_k` above, the
present module formalises only the **combinatorial step** that goes
from the post-DCT inputs to the headline limit inequality. The DCT
manipulations themselves (showing the LHS sequence converges and the
RHS sequence converges to `0`) are bundled as hypotheses on the
caller — discharged elsewhere in the project from the standing
integrability bounds in `Hamiltonian.Congestion`. -/

/-- **Limit of the `m_δ`-tested transport variational inequality**
(paper `eq:transport-test-m.delta`, line 1546).

Combinatorial step of paper Step 3. Inputs:

* `δSeq : ℕ → ℝ` — a positive sequence with `δSeq n → 0` and
  `δSeq n ≤ 1` (so that the uniform-`δ ≤ 1` integrability bounds
  `eq:assH.DpH.upper.congestion` apply for every `n`).
* `LHS, RHS : ℕ → ℝ` — the (real) values of the LHS and RHS integrals
  of paper line 1538, with `m` replaced by `m_{δSeq n}` and the
  Hamiltonian lower bound applied (so the RHS is the
  `(u + φ − C(m_δ^β + 1) − V)(m_δ − m)` integral).
* `LHSlim : ℝ` — the limit value of `LHS n` as `n → ∞`.
* `h_VI_at_mdelta` — the per-`n` variational inequality
  `LHS n ≥ RHS n` from paper line 1538 (after applying
  `lower_congestion_of_alternative`).
* `h_LHS_tendsto` — `LHS n → LHSlim` (post-DCT input bundling
  `eq:assH.DpH.upper.congestion`).
* `h_RHS_tendsto` — `RHS n → 0` (post-DCT input; the multiplier
  `m_δ − m → 0` a.e. and the integrand is uniformly dominated).

Conclusion: `LHSlim ≥ 0`, i.e. paper `eq:transport-test-m.delta`.

The proof is a one-line application of `le_of_tendsto_of_tendsto'`:
the limit of a non-negative sequence is non-negative, where the
sequence is `LHS n − RHS n ≥ 0`. -/
theorem transport_mdelta_limit
    {δSeq : ℕ → ℝ}
    (_hδ_pos : ∀ n, 0 < δSeq n)
    (_hδ_le_one : ∀ n, δSeq n ≤ 1)
    (_hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    {LHS RHS : ℕ → ℝ} {LHSlim : ℝ}
    (h_VI_at_mdelta : ∀ n, RHS n ≤ LHS n)
    (h_LHS_tendsto : Filter.Tendsto LHS Filter.atTop (nhds LHSlim))
    (h_RHS_tendsto : Filter.Tendsto RHS Filter.atTop (nhds (0 : ℝ))) :
    0 ≤ LHSlim :=
  le_of_tendsto_of_tendsto' h_RHS_tendsto h_LHS_tendsto h_VI_at_mdelta

/-- **Concrete packaging of `transport_mdelta_limit`** at the
integral form of paper line 1546.

Given:

* a smooth test `φ` and its weak gradient `Dφ`,
* the data `(m, u, Du, V, H, DpH, ε, γ̄, β, C)` of the standing
  congestion model,
* a sequence `δSeq → 0⁺` with `δSeq n ≤ 1`,
* the per-`n` variational inequality (paper line 1538): for every `n`,

  ```
  ∫ [(m_{δ_n}-1)φ + m_{δ_n}·D_pH(x, Du+Dφ, m_{δ_n})·Dφ] dx
    + ∫ [ε·|Du+Dφ|^{γ̄-2}(Du+Dφ)·Dφ + ε·|u+φ|^{γ̄-2}(u+φ)·φ] dx
    ≥ ∫ (u + φ − C(m_{δ_n}^β + 1) − V)(m_{δ_n} − m) dx,
  ```
* DCT outputs:
  * the LHS converges to its `m`-evaluated counterpart
    (paper line 1548–1551);
  * the RHS converges to `0` (since `m_δ − m → 0` a.e. with uniform
    dominator).

Conclusion: paper `eq:transport-test-m.delta` —

```
∫ [(m-1)φ + m·D_pH(x, Du+Dφ, m)·Dφ] dx
  + ∫ [ε·|Du+Dφ|^{γ̄-2}(Du+Dφ)·Dφ + ε·|u+φ|^{γ̄-2}(u+φ)·φ] dx ≥ 0.
```
-/
theorem transport_mdelta_limit_concrete
    {V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar β C : ℝ}
    (φ Dφ_φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    {δSeq : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    -- Per-`n` variational inequality, lower-bounded form (paper line 1538).
    (h_VI_at_mdelta : ∀ n,
      (∫ x in UnitCube d,
          (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
            * (max (m x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)))
      ≤
      (∫ x in UnitCube d,
          (max (m x) (δSeq n) - 1) * φ x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))))
    -- Limit of the LHS (DCT, paper line 1545).
    (h_LHS_tendsto :
      Filter.Tendsto
        (fun n =>
          (∫ x in UnitCube d,
              (max (m x) (δSeq n) - 1) * φ x
                + max (m x) (δSeq n)
                  * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                      ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))
        Filter.atTop
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + m x
                  * (DpH x (fun i => Du i x + Dφ i x) (m x)
                      ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))))
    -- Limit of the RHS to `0` (DCT; `m_δ − m → 0` a.e.).
    (h_RHS_tendsto :
      Filter.Tendsto
        (fun n =>
          ∫ x in UnitCube d,
            (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
              * (max (m x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds (0 : ℝ))) :
    0 ≤
      (∫ x in UnitCube d,
          (m x - 1) * φ x
            + m x
              * (DpH x (fun i => Du i x + Dφ i x) (m x)
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))) := by
  -- Suppress unused-variable warnings for parameters retained for
  -- documentation / call-site consistency with paper line 1538.
  let _ := Dφ_φ
  exact transport_mdelta_limit
    (δSeq := δSeq) hδ_pos hδ_le_one hδ_tendsto
    (LHS := fun n =>
      (∫ x in UnitCube d,
          (max (m x) (δSeq n) - 1) * φ x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))))
    (RHS := fun n =>
      ∫ x in UnitCube d,
        (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
          * (max (m x) (δSeq n) - m x)
        ∂(volume : Measure (Fin d → ℝ)))
    h_VI_at_mdelta h_LHS_tendsto h_RHS_tendsto

/-- **`J`-extension sibling of `transport_mdelta_limit_concrete`** (T2 phase6 BB
VIid child-5a-ii-β, connector J-reshape).

Identical packaging of `transport_mdelta_limit`, but the limit-density flux
integrand is the paper-faithful closed-half-line extension `J(x, p, m) ⬝ Dφ`
(hypothesis `(a:mDpHat0)`) in place of the product `m·D_pH(x, p, m)·Dφ`. At the
boundary `{m x = 0}` the product vanishes regardless of `D_pH`, but the honest
`δ → 0` flux limit is `J(x, p, 0) ⬝ Dφ`, which need not vanish; threading `J`
keeps the connector chain honest at the Browder–Minty witness.

The `δ`-sequence VI `h_VI_at_mdelta` still carries the product `m_δ·D_pH` (true
for `m_δ ≥ δ > 0`); only the **limit** integrand (and conclusion) moves to `J`.
The generic backend `transport_mdelta_limit` is limit-target-agnostic, so the
proof closes unchanged. -/
theorem transport_mdelta_limit_concrete_J
    {V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar β C : ℝ}
    (φ Dφ_φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    {δSeq : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (h_VI_at_mdelta : ∀ n,
      (∫ x in UnitCube d,
          (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
            * (max (m x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)))
      ≤
      (∫ x in UnitCube d,
          (max (m x) (δSeq n) - 1) * φ x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))))
    -- Limit of the LHS, with the `J`-extension flux integrand.
    (h_LHS_tendsto :
      Filter.Tendsto
        (fun n =>
          (∫ x in UnitCube d,
              (max (m x) (δSeq n) - 1) * φ x
                + max (m x) (δSeq n)
                  * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                      ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))
        Filter.atTop
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + (J x (fun i => Du i x + Dφ i x) (m x)
                    ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))))
    (h_RHS_tendsto :
      Filter.Tendsto
        (fun n =>
          ∫ x in UnitCube d,
            (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
              * (max (m x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds (0 : ℝ))) :
    0 ≤
      (∫ x in UnitCube d,
          (m x - 1) * φ x
            + (J x (fun i => Du i x + Dφ i x) (m x)
                ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))) := by
  let _ := Dφ_φ
  exact transport_mdelta_limit
    (δSeq := δSeq) hδ_pos hδ_le_one hδ_tendsto
    (LHS := fun n =>
      (∫ x in UnitCube d,
          (max (m x) (δSeq n) - 1) * φ x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))))
    (RHS := fun n =>
      ∫ x in UnitCube d,
        (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
          * (max (m x) (δSeq n) - m x)
        ∂(volume : Measure (Fin d → ℝ)))
    h_VI_at_mdelta h_LHS_tendsto h_RHS_tendsto

/-! ## Step 3 of paper Lemma `lem:weak.is.strong` — first-order
variation `ι(t) = 0` (paper lines 1556–1565)

Paper `Source/FGU-monotone_revised.tex`, lines 1556–1565. After
establishing `eq:transport-test-m.delta` (paper line 1546) for
arbitrary smooth `φ`, the paper substitutes `φ ↦ tφ` for `t ≠ 0`
in the integral inequality and divides by `t`. The resulting
expression is denoted `ι(t)`:

```
ι(t) = ∫ [(m − 1)φ + m·D_pH(x, Du + tDφ, m)·Dφ] dx
     + ∫ [ε·|Du + tDφ|^{γ̄−2}(Du + tDφ)·Dφ
            + ε·|u + tφ|^{γ̄−2}(u + tφ)·φ] dx.
```

Sign argument: dividing the inequality `LHS_{tφ} ≥ 0` by `t > 0`
preserves the sign, giving `ι(t) ≥ 0`; dividing by `t < 0`
reverses it, giving `ι(t) ≤ 0`. By `(a:mDpHat0)` and the upper
bound `Hamiltonian.upper_bound_congestiongrowth`, the integrand
is continuous in `t` for a.e. `x` with a uniform `|t| ≤ 1`
integrable dominator. Hence Lebesgue's DCT gives `ι` continuous
at `0`. Combining `ι(0⁺) ≥ 0` and `ι(0⁻) ≤ 0` with continuity at
`0` forces `ι(0) = 0`. This is `eq:congest.transport`.

Following the modular pattern of `transport_mdelta_limit`, the
combinatorial sign-and-limit step is isolated below from the DCT
manipulations, which are bundled as a `Tendsto` hypothesis. -/

/-- **First-order variation `ι(t) = 0` (paper line 1565).**

Combinatorial step of paper Step 3, second half. Inputs:

* `ι : ℝ → ℝ` — the function obtained by replacing `φ ↦ tφ` in
  paper `eq:transport-test-m.delta` and dividing by `t ≠ 0`
  (paper line 1556 definition, packaged opaquely here).
* `ι0 : ℝ` — the value of the integrand at `t = 0` (i.e. paper
  `eq:congest.transport`'s LHS).
* `h_pos` — `ι(t) ≥ 0` for `t > 0` (paper line 1565, dividing the
  inequality at `tφ` by positive `t`).
* `h_neg` — `ι(t) ≤ 0` for `t < 0` (paper line 1565, dividing by
  negative `t` flips the sign).
* `h_lim` — `Tendsto ι (𝓝 0) (𝓝 ι0)` (post-DCT continuity at
  `t = 0`, from `(a:mDpHat0)` and uniform `|t| ≤ 1` domination).

Conclusion: `ι0 = 0`, i.e. paper `eq:congest.transport`. -/
theorem iota_firstorder_zero
    {ι : ℝ → ℝ} {ι0 : ℝ}
    (h_pos : ∀ t, 0 < t → 0 ≤ ι t)
    (h_neg : ∀ t, t < 0 → ι t ≤ 0)
    (h_lim : Filter.Tendsto ι (nhds (0 : ℝ)) (nhds ι0)) :
    ι0 = 0 := by
  -- Build a sequence `tPos n := 1/(n+1) > 0` tending to 0.
  set tPos : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1) with htPosdef
  have h_tPos_pos : ∀ n, 0 < tPos n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  have h_tPos_to_zero :
      Filter.Tendsto tPos Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- And `tNeg n := -1/(n+1) < 0` tending to 0.
  set tNeg : ℕ → ℝ := fun n => -((1 : ℝ) / (n + 1)) with htNegdef
  have h_tNeg_neg : ∀ n, tNeg n < 0 := by
    intro n; exact neg_lt_zero.mpr (h_tPos_pos n)
  have h_tNeg_to_zero :
      Filter.Tendsto tNeg Filter.atTop (nhds (0 : ℝ)) := by
    have h : Filter.Tendsto (fun n => -(tPos n)) Filter.atTop
        (nhds (-(0 : ℝ))) := h_tPos_to_zero.neg
    have heq : (fun n => -(tPos n)) = tNeg := by
      funext n; rfl
    rw [heq, neg_zero] at h
    exact h
  -- Composing with `h_lim`: `ι ∘ tPos → ι0` and `ι ∘ tNeg → ι0`.
  have h_iota_tPos :
      Filter.Tendsto (fun n => ι (tPos n)) Filter.atTop (nhds ι0) :=
    h_lim.comp h_tPos_to_zero
  have h_iota_tNeg :
      Filter.Tendsto (fun n => ι (tNeg n)) Filter.atTop (nhds ι0) :=
    h_lim.comp h_tNeg_to_zero
  -- From the right: `ι (tPos n) ≥ 0` for all `n`, hence `ι0 ≥ 0`.
  have h_ι0_nn : 0 ≤ ι0 :=
    ge_of_tendsto' h_iota_tPos (fun n => h_pos (tPos n) (h_tPos_pos n))
  -- From the left: `ι (tNeg n) ≤ 0` for all `n`, hence `ι0 ≤ 0`.
  have h_ι0_np : ι0 ≤ 0 :=
    le_of_tendsto' h_iota_tNeg (fun n => h_neg (tNeg n) (h_tNeg_neg n))
  linarith

/-! ### child-4d (b): a.e. `t`-continuity at `0` of the DCT integrands

The two analytic-continuity inputs `hcontA`/`hcontB` of
`iota_firstorder_h_lim_dct` are discharged here. The `ε`-Gateaux integrand
`FB` is continuous in `t` on all of `ℝ` (for `1 < γ̄`) by the signed-power
continuity machinery (`continuous_vecSignedRpow` / `continuous_signedRpow`),
with **no** positivity required. The flux integrand `FA` hits the `{m = 0}`
boundary, where `RegularityH.continuous_DpH_pm` is only available on `Ioi 0`;
this is handled by the **`m`-prefactor-vanishing case split** (MEMORY
`hcoeHJB_le_positive_witness_route`): on `{0 < m x}` the section
`t ↦ m x · D_pH(x, Du+t∇φ, m x) · ∇φ` is continuous (the fixed mass slot
`m x > 0` stays in `Ioi 0`), while on `{m x = 0}` the prefactor `m x = 0`
kills the flux term, leaving the `t`-constant `(m x − 1)·φ x`. No
`Hext_finite_at_zero`, no power-growth crutch, no raw `m = 0` continuity. -/

/-- **Pointwise `t`-continuity of the `ε`-Gateaux integrand `FB`** (child-4d
piece b). For `1 < γ̄`, the map
`t ↦ ε·|Du+t∇φ|^{γ̄−2}(Du+t∇φ)·∇φ + ε·|u+tφ|^{γ̄−2}(u+tφ)·φ` is continuous
on all of `ℝ` for every fixed `x` — no positivity needed, since
`vecAbsPowMinusTwo γ̄ v * (v ⬝ w) = vecSignedRpow γ̄ v ⬝ w` (and the scalar
analogue) and the signed-power maps are continuous for `1 < γ̄`. -/
theorem iota_FB_integrand_continuous
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ} (hγ : 1 < γBar)
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) :
    Continuous (fun t : ℝ =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x)) := by
  -- Vector part: `ε·(vecAbsPowMinusTwo γBar v_t * (v_t ⬝ w)) = ε·(vecSignedRpow γBar v_t ⬝ w)`.
  have hvec : Continuous (fun t : ℝ =>
      ε * (vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x)))) := by
    have hrw : (fun t : ℝ =>
        vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x)))
        = (fun t : ℝ =>
            vecSignedRpow γBar (fun i => Du i x + t * Dφ i x)
              ⬝ (fun i => Dφ i x)) := by
      funext t
      set v : Fin d → ℝ := fun i => Du i x + t * Dφ i x with hv
      set w : Fin d → ℝ := fun i => Dφ i x with hw
      show vecAbsPowMinusTwo γBar v * (v ⬝ w) = vecSignedRpow γBar v ⬝ w
      unfold euclideanDot vecSignedRpow
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    refine continuous_const.mul ?_
    rw [hrw]
    unfold euclideanDot
    refine continuous_finset_sum _ (fun i _ => ?_)
    have hvcont : Continuous (fun t : ℝ => (fun i => Du i x + t * Dφ i x)) := by
      refine continuous_pi (fun j => ?_)
      exact continuous_const.add (continuous_id.mul continuous_const)
    have hcoord : Continuous (fun t : ℝ =>
        vecSignedRpow γBar (fun i => Du i x + t * Dφ i x) i) :=
      (continuous_apply i).comp ((continuous_vecSignedRpow hγ).comp hvcont)
    exact hcoord.mul continuous_const
  -- Scalar part: `ε·(absPowMinusTwo γBar s_t * (s_t * φ x)) = ε·(signedRpow γBar s_t * φ x)`.
  have hsc : Continuous (fun t : ℝ =>
      ε * (absPowMinusTwo γBar (u x + t * φ x)
          * ((u x + t * φ x) * φ x))) := by
    have hrw : (fun t : ℝ =>
        absPowMinusTwo γBar (u x + t * φ x)
          * ((u x + t * φ x) * φ x))
        = (fun t : ℝ => signedRpow γBar (u x + t * φ x) * φ x) := by
      funext t
      show absPowMinusTwo γBar (u x + t * φ x) * ((u x + t * φ x) * φ x)
          = signedRpow γBar (u x + t * φ x) * φ x
      unfold signedRpow; ring
    refine continuous_const.mul ?_
    rw [hrw]
    refine Continuous.mul ?_ continuous_const
    have hscont : Continuous (fun t : ℝ => u x + t * φ x) :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact (continuous_signedRpow hγ).comp hscont
  -- Combine, matching the goal's `ε * A * B + ε * C * D` shape.
  have : (fun t : ℝ =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x))
      = (fun t : ℝ =>
          ε * (vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
              * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x)))
            + ε * (absPowMinusTwo γBar (u x + t * φ x)
                * ((u x + t * φ x) * φ x))) := by
    funext t; ring
  rw [this]
  exact hvec.add hsc

/-- **a.e. `t`-continuity at `0` of the flux integrand `FA`** (child-4d
piece b, the `{m = 0}` boundary crux). On `{0 < m x}` the section
`t ↦ (m x − 1)·φ x + m x · D_pH(x, Du+t∇φ, m x) · ∇φ` is continuous because
the mass slot `m x > 0` stays in `Ioi 0` where `D_pH(x, ·, ·)` is continuous
(`RegularityH.continuous_DpH_pm`). On `{m x = 0}` the prefactor `m x = 0`
annihilates the flux term, leaving the `t`-constant `(m x − 1)·φ x`. Hence
the limit `t → 0` of `FA t x` is `FA 0 x` for a.e. `x` (using `0 ≤ m` a.e.).

The conclusion is stated in the exact `hcontA` shape of
`iota_firstorder_h_lim_dct`. -/
theorem iota_FA_continuous_at_zero_ae
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m : (Fin d → ℝ) → ℝ}
    (hDpH_cont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
        {pm | 0 < pm.2})
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun t : ℝ =>
          (m x - 1) * φ x
            + m x * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x)))
        (nhds (0 : ℝ))
        (nhds
          ((m x - 1) * φ x
            + m x * (DpH x (fun i => Du i x + (0 : ℝ) * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x)))) := by
  filter_upwards [hDpH_cont, hm_nn] with x hDpHx hmx
  -- The map `t ↦ FA t x` evaluated at the limit point `0`.
  rcases eq_or_lt_of_le hmx with hm0 | hmpos
  · -- `m x = 0`: the flux term vanishes, `FA t x = (m x − 1)·φ x` is `t`-const.
    have hzero : (fun t : ℝ =>
        (m x - 1) * φ x
          + m x * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
              ⬝ (fun i => Dφ i x)))
        = (fun _ : ℝ => (m x - 1) * φ x) := by
      funext t; rw [← hm0]; ring
    rw [hzero]
    have : (m x - 1) * φ x
        + m x * (DpH x (fun i => Du i x + (0 : ℝ) * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x))
        = (m x - 1) * φ x := by rw [← hm0]; ring
    rw [this]
    exact tendsto_const_nhds
  · -- `0 < m x`: continuity from `continuous_DpH_pm` on `Ioi 0`.
    -- `t ↦ (Du+t∇φ, m x)` is continuous into `{0 < ·.2}` (mass slot fixed).
    have hpath : Continuous
        (fun t : ℝ => ((fun i => Du i x + t * Dφ i x), m x) :
          ℝ → (Fin d → ℝ) × ℝ) := by
      refine Continuous.prodMk ?_ continuous_const
      refine continuous_pi (fun j => ?_)
      exact continuous_const.add (continuous_id.mul continuous_const)
    -- Membership of the path in the open set `{pm | 0 < pm.2}` for all `t`.
    have hmem : ∀ t : ℝ, ((fun i => Du i x + t * Dφ i x), m x)
        ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := fun t => hmpos
    -- Continuity of `t ↦ DpH x (Du+t∇φ) (m x)` via `ContinuousOn.comp_continuous`.
    have hDpH_path : Continuous
        (fun t : ℝ => DpH x (fun i => Du i x + t * Dφ i x) (m x)) := by
      have := hDpHx.comp_continuous hpath hmem
      exact this
    -- The dot product with `∇φ` and the affine `(m x −1)·φ + m x · (·)`.
    have hdot : Continuous
        (fun t : ℝ => DpH x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x)) := by
      unfold euclideanDot
      refine continuous_finset_sum _ (fun i _ => ?_)
      exact ((continuous_apply i).comp hDpH_path).mul continuous_const
    have hcont : Continuous
        (fun t : ℝ =>
          (m x - 1) * φ x
            + m x * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x))) :=
      continuous_const.add (continuous_const.mul hdot)
    exact hcont.tendsto 0

/-- **t → 0 DCT for the paper-correct first-variation family** (T2 phase6
BB VIid **child-4c**; paper `eq:identity-congestion`, line 1565, last
sentence).

This discharges the `h_lim` hypothesis of `iota_firstorder_zero_concrete`
for the **paper-correct** family `ι(t)` at the limit density `m` (the one
produced by child-4b's `δ → 0` passage, with the `t`-factor already cancelled
against the squeeze's `1/t`):

```
ι(t) = ∫ [(m−1)φ + m·D_pH(x, Du+t∇φ, m)·Dφ] dx
     + ∫ [ε·|Du+t∇φ|^{γ̄−2}(Du+t∇φ)·Dφ + ε·|u+tφ|^{γ̄−2}(u+tφ)·φ] dx.
```

The DCT machinery (`tendsto_integral_filter_of_dominated_convergence` along
`𝓝 0`) is run genuinely here; its three analytic inputs are bundled as
hypotheses, exactly as the established `δ → 0` DCT lemmas
(`muAux_integral_tendsto`, `transport_mdelta_limit_of_L1`) bundle their
dominators / `L¹` data:

* **a.e. `t`-continuity at `0`** of each integrand (`hcontA`, `hcontB`) —
  continuity of `D_pH(x, ·, m)` and the ε-functionals in the perturbed
  momentum `Du + t∇φ` / value `u + tφ`. On `{0 < m x}` this is the
  on-`Ioi 0` momentum-slot continuity of `RegularityH.continuous_DpH_pm`
  (the positive-witness route); the ε-terms are continuous away from the
  origin of their argument.
* **uniform `|t| ≤ 1` integrable dominators** `gA`, `gB` (`hgA_int`,
  `hgB_int`, `hboundA`, `hboundB`) — from
  `CongestionGrowthCore.mDpH_mem_Lp_gammaBar'_congestion`
  bounding `m·|D_pH(x, Du+t∇φ, m)|` by an `L¹` function uniform in
  `t ∈ [−1, 1]` (since `‖Du+t∇φ‖ ≤ ‖Du‖ + ‖∇φ‖`), plus the ε-term bounds.
* **a.e.-strong-measurability** `hmeasA`, `hmeasB` of the per-`t` integrands.

The output `h_lim` feeds `iota_firstorder_zero_concrete` directly. -/
theorem iota_firstorder_h_lim_dct
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    -- The two per-`t` integrands.
    (FA : ℝ → (Fin d → ℝ) → ℝ)
    (FB : ℝ → (Fin d → ℝ) → ℝ)
    (hFAdef : ∀ t, FA t = fun x =>
      (m x - 1) * φ x
        + m x * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x)))
    (hFBdef : ∀ t, FB t = fun x =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x))
    -- a.e. `t`-continuity at `0`.
    (hcontA : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FA t x) (nhds (0 : ℝ)) (nhds (FA 0 x)))
    (hcontB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FB t x) (nhds (0 : ℝ)) (nhds (FB 0 x)))
    -- uniform `|t| ≤ 1` integrable dominators.
    (gA gB : (Fin d → ℝ) → ℝ)
    (hgA_int : Integrable gA (volume.restrict (UnitCube d)))
    (hgB_int : Integrable gB (volume.restrict (UnitCube d)))
    (hboundA : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FA t x‖ ≤ gA x)
    (hboundB : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FB t x‖ ≤ gB x)
    -- a.e.-strong-measurability of the per-`t` integrands.
    (hmeasA : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FA t) (volume.restrict (UnitCube d)))
    (hmeasB : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FB t) (volume.restrict (UnitCube d))) :
    Filter.Tendsto
      (fun t =>
        (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))))
      (nhds (0 : ℝ))
      (nhds
        ((∫ x in UnitCube d,
            (m x - 1) * φ x
              + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
            ∂(volume : Measure (Fin d → ℝ))))) := by
  -- DCT along `𝓝 0` for the first integrand `FA`, target `∫ FA 0`.
  have hA :
      Filter.Tendsto
        (fun t => ∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
        (nhds (0 : ℝ))
        (nhds (∫ x in UnitCube d, FA 0 x ∂(volume : Measure (Fin d → ℝ)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      gA hmeasA hboundA hgA_int hcontA
  -- DCT along `𝓝 0` for the second integrand `FB`, target `∫ FB 0`.
  have hB :
      Filter.Tendsto
        (fun t => ∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ)))
        (nhds (0 : ℝ))
        (nhds (∫ x in UnitCube d, FB 0 x ∂(volume : Measure (Fin d → ℝ)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      gB hmeasB hboundB hgB_int hcontB
  -- Identify the `t = 0` limits with the `eq:congest.transport` LHS.
  have hFA0 :
      (∫ x in UnitCube d, FA 0 x ∂(volume : Measure (Fin d → ℝ)))
        = ∫ x in UnitCube d,
            (m x - 1) * φ x
              + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [hFAdef 0]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    have : (fun i => Du i x + (0 : ℝ) * Dφ i x) = (fun i => Du i x) := by
      funext i; ring
    rw [this]
  have hFB0 :
      (∫ x in UnitCube d, FB 0 x ∂(volume : Measure (Fin d → ℝ)))
        = ∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [hFBdef 0]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    have hv : (fun i => Du i x + (0 : ℝ) * Dφ i x) = (fun i => Du i x) := by
      funext i; ring
    rw [hv]
    have hs : u x + (0 : ℝ) * φ x = u x := by ring
    rw [hs]
  rw [hFA0] at hA
  rw [hFB0] at hB
  exact hA.add hB

/-- **a.e. `t`-continuity at `0` of the `J`-extension flux integrand `FA`**
(T2 phase6 BB VIid **child-5b**, part (b); paper `eq:congest.transport`,
the `t → 0` boundary continuity in the `J`-stated DCT).

The `J`-form sibling of `iota_FA_continuous_at_zero_ae`. The flux integrand is
now `FA t x = (m x − 1)·φ x + J(x, Du+t∇φ, m x) ⬝ ∇φ`, the paper's
closed-half-line extension. Continuity in `t` at `0` for a.e. `x` is **uniform
across the `{m = 0}` boundary**: the joint continuity hypothesis
`(a:mDpHat0).continuous_J` gives `ContinuousOn (p, m) ↦ J(x, p, m)` on
`{(p, m) | 0 ≤ m}`, and at the witness `0 ≤ m x` a.e. (`hm_nn`), so the section
`t ↦ J(x, Du+t∇φ, m x)` (mass slot fixed in `{0 ≤ ·}`) is continuous — **no**
`m x > 0` / positive-witness route needed here, the extension carries the honest
`m = 0` value `J(x, Du, 0)⬝∇φ`.

Conclusion in the exact `hcontA` shape of `iota_firstorder_h_lim_dct_J`. -/
theorem iota_FA_continuous_at_zero_ae_J
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m : (Fin d → ℝ) → ℝ}
    (hcont_J : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => J x pm.1 pm.2)
        {pm | 0 ≤ pm.2})
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun t : ℝ =>
          (m x - 1) * φ x
            + (J x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x)))
        (nhds (0 : ℝ))
        (nhds
          ((m x - 1) * φ x
            + (J x (fun i => Du i x + (0 : ℝ) * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x)))) := by
  let _ := DpH
  filter_upwards [hcont_J, hm_nn] with x hJx hmx
  -- The path `t ↦ (Du+t∇φ, m x)` stays in `{0 ≤ ·.2}` (mass slot fixed `≥ 0`).
  have hpath : Continuous
      (fun t : ℝ => ((fun i => Du i x + t * Dφ i x), m x) :
        ℝ → (Fin d → ℝ) × ℝ) := by
    refine Continuous.prodMk ?_ continuous_const
    refine continuous_pi (fun j => ?_)
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hmem : ∀ t : ℝ, ((fun i => Du i x + t * Dφ i x), m x)
      ∈ {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} := fun t => hmx
  -- Continuity of `t ↦ J(x, Du+t∇φ, m x)` via `ContinuousOn.comp_continuous`.
  have hJ_path : Continuous
      (fun t : ℝ => J x (fun i => Du i x + t * Dφ i x) (m x)) :=
    hJx.comp_continuous hpath hmem
  -- The dot product with `∇φ` and the affine `(m x −1)·φ + (·)`.
  have hdot : Continuous
      (fun t : ℝ => J x (fun i => Du i x + t * Dφ i x) (m x)
          ⬝ (fun i => Dφ i x)) := by
    unfold euclideanDot
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact ((continuous_apply i).comp hJ_path).mul continuous_const
  have hcont : Continuous
      (fun t : ℝ =>
        (m x - 1) * φ x
          + (J x (fun i => Du i x + t * Dφ i x) (m x)
              ⬝ (fun i => Dφ i x))) :=
    continuous_const.add hdot
  exact hcont.tendsto 0

/-- **a.e. `t`-continuity at `0` of the `ε`-Gateaux integrand `FB`**
(T2 phase6 BB VIid **child-5b**, part (b)).

Pointwise (hence a.e.) repackaging of `iota_FB_integrand_continuous`: for
`1 < γ̄` the section `t ↦ FB t x` is continuous on all of `ℝ`, so it tends to
`FB 0 x` as `t → 0`. Conclusion in the exact `hcontB` shape of
`iota_firstorder_h_lim_dct_J`. -/
theorem iota_FB_continuous_at_zero_ae
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ} (hγ : 1 < γBar)
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun t : ℝ =>
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
              * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x + t * φ x)
                * ((u x + t * φ x) * φ x))
        (nhds (0 : ℝ))
        (nhds
          (ε * vecAbsPowMinusTwo γBar (fun i => Du i x + (0 : ℝ) * Dφ i x)
              * ((fun i => Du i x + (0 : ℝ) * Dφ i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x + (0 : ℝ) * φ x)
                * ((u x + (0 : ℝ) * φ x) * φ x))) := by
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact (iota_FB_integrand_continuous (Du := Du) (u := u) (ε := ε)
    (γBar := γBar) hγ φ Dφ x).tendsto 0

/-- **`J`-extension sibling of `iota_firstorder_h_lim_dct`** (T2 phase6 BB VIid
child-5a-ii-β, connector J-reshape).

Same `t → 0` DCT continuity, but the flux integrand `FA t` carries the
paper-faithful extension `J(x, Du+t∇φ, m) ⬝ ∇φ` in place of the product
`m·D_pH(x, Du+t∇φ, m)·∇φ`; the `t = 0` limit is `(m−1)φ + J(x, Du, m)⬝∇φ`. The
DCT backend `tendsto_integral_filter_of_dominated_convergence` is target-agnostic,
so the proof is the original verbatim with `FA` reshaped onto `J`. The dominator
`gA` now controls `‖J(x, Du+t∇φ, m)⬝∇φ‖` uniformly in `|t| ≤ 1` (from the flux
`L^{γ̄'}` envelope, via `J = m·D_pH` on `{0<m}` and the bundled `(a:mDpHat0)` data
on `{m = 0}`). -/
theorem iota_firstorder_h_lim_dct_J
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (FA : ℝ → (Fin d → ℝ) → ℝ)
    (FB : ℝ → (Fin d → ℝ) → ℝ)
    (hFAdef : ∀ t, FA t = fun x =>
      (m x - 1) * φ x
        + (J x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x)))
    (hFBdef : ∀ t, FB t = fun x =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x))
    (hcontA : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FA t x) (nhds (0 : ℝ)) (nhds (FA 0 x)))
    (hcontB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FB t x) (nhds (0 : ℝ)) (nhds (FB 0 x)))
    (gA gB : (Fin d → ℝ) → ℝ)
    (hgA_int : Integrable gA (volume.restrict (UnitCube d)))
    (hgB_int : Integrable gB (volume.restrict (UnitCube d)))
    (hboundA : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FA t x‖ ≤ gA x)
    (hboundB : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FB t x‖ ≤ gB x)
    (hmeasA : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FA t) (volume.restrict (UnitCube d)))
    (hmeasB : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FB t) (volume.restrict (UnitCube d))) :
    Filter.Tendsto
      (fun t =>
        (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))))
      (nhds (0 : ℝ))
      (nhds
        ((∫ x in UnitCube d,
            (m x - 1) * φ x
              + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
            ∂(volume : Measure (Fin d → ℝ))))) := by
  let _ := DpH
  have hA :
      Filter.Tendsto
        (fun t => ∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
        (nhds (0 : ℝ))
        (nhds (∫ x in UnitCube d, FA 0 x ∂(volume : Measure (Fin d → ℝ)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      gA hmeasA hboundA hgA_int hcontA
  have hB :
      Filter.Tendsto
        (fun t => ∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ)))
        (nhds (0 : ℝ))
        (nhds (∫ x in UnitCube d, FB 0 x ∂(volume : Measure (Fin d → ℝ)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      gB hmeasB hboundB hgB_int hcontB
  have hFA0 :
      (∫ x in UnitCube d, FA 0 x ∂(volume : Measure (Fin d → ℝ)))
        = ∫ x in UnitCube d,
            (m x - 1) * φ x
              + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [hFAdef 0]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    have : (fun i => Du i x + (0 : ℝ) * Dφ i x) = (fun i => Du i x) := by
      funext i; ring
    rw [this]
  have hFB0 :
      (∫ x in UnitCube d, FB 0 x ∂(volume : Measure (Fin d → ℝ)))
        = ∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [hFBdef 0]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    have hv : (fun i => Du i x + (0 : ℝ) * Dφ i x) = (fun i => Du i x) := by
      funext i; ring
    rw [hv]
    have hs : u x + (0 : ℝ) * φ x = u x := by ring
    rw [hs]
  rw [hFA0] at hA
  rw [hFB0] at hB
  exact hA.add hB

/-- **Concrete packaging of `iota_firstorder_zero`** at the
integral form of paper `eq:congest.transport` (line 1546 with the
`t = 0` test value).

Given:

* a smooth test `φ` and its weak gradient `Dφ`,
* the data `(m, u, Du, V, DpH, ε, γ̄)` of the standing congestion
  model,
* the function `ι : ℝ → ℝ` defined by the paper's formula at
  parameter `t` (line 1557),
* `h_pos`, `h_neg` from dividing `eq:transport-test-m.delta`
  applied to `tφ` by `t > 0` and `t < 0` respectively (paper line
  1565), and
* `h_lim` continuity of `ι` at `0`, from DCT against the uniform
  `|t| ≤ 1` dominator (paper line 1565, last sentence) — discharged
  by `iota_firstorder_h_lim_dct` above.

Conclusion: `ι(0) = 0`, where `ι(0)` is the LHS of paper
`eq:congest.transport` evaluated at `t = 0`:

```
ι(0) = ∫ [(m − 1)φ + m·D_pH(x, Du, m)·Dφ] dx
     + ∫ [ε·|Du|^{γ̄−2}·Du·Dφ + ε·|u|^{γ̄−2}·u·φ] dx.
```

This is the desired transport equation `eq:congest.transport`. -/
theorem iota_firstorder_zero_concrete
    {_V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (ι : ℝ → ℝ)
    (h_pos : ∀ t, 0 < t → 0 ≤ ι t)
    (h_neg : ∀ t, t < 0 → ι t ≤ 0)
    (h_lim :
      Filter.Tendsto ι (nhds (0 : ℝ))
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + m x
                  * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
              ∂(volume : Measure (Fin d → ℝ)))))) :
    (∫ x in UnitCube d,
        (m x - 1) * φ x
          + m x
            * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
        ∂(volume : Measure (Fin d → ℝ))) = 0 :=
  iota_firstorder_zero (ι := ι) h_pos h_neg h_lim

/-- **`J`-extension sibling of `iota_firstorder_zero_concrete`** (T2 phase6 BB
VIid child-5a-ii-β, connector J-reshape).

Same combinatorial `ι(0) = 0` packaging, but the first-variation flux integrand
at `t = 0` is the paper-faithful extension `J(x, Du, m) ⬝ Dφ` instead of the
product `m·D_pH(x, Du, m)·Dφ`. The squeeze backend `iota_firstorder_zero` is
limit-target-agnostic, so the proof is unchanged. -/
theorem iota_firstorder_zero_concrete_J
    {_V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (ι : ℝ → ℝ)
    (h_pos : ∀ t, 0 < t → 0 ≤ ι t)
    (h_neg : ∀ t, t < 0 → ι t ≤ 0)
    (h_lim :
      Filter.Tendsto ι (nhds (0 : ℝ))
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
              ∂(volume : Measure (Fin d → ℝ)))))) :
    (∫ x in UnitCube d,
        (m x - 1) * φ x
          + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
        ∂(volume : Measure (Fin d → ℝ))) = 0 :=
  iota_firstorder_zero (ι := ι) h_pos h_neg h_lim

/-- **±tφ wiring + final `eq:congest.transport` assembly** (T2 phase6 BB VIid
**child-4d-C**; paper `eq:congest.transport`, line 1546 at `t = 0`).

The clean final composition. For the standing congestion data `(m, u, Du, DpH,
ε, γ̄)` and a fixed smooth test `φ` with weak gradient `Dφ`, this assembles the
per-`φ` transport identity from:

* `h_dir` — the per-direction limit-density inequality, in the *exact*
  conclusion shape of the landed `transport_mdelta_limit_of_L1` applied at the
  test direction `(t·φ, t·∇φ)`:
  ```
  0 ≤ ∫[(m−1)(tφ) + m·D_pH(x, Du+t∇φ, m)·(t∇φ)]
      + ∫[ε·|Du+t∇φ|^{γ̄−2}(Du+t∇φ)·(t∇φ) + ε·|u+tφ|^{γ̄−2}(u+tφ)·(tφ)].
  ```
  Because every occurrence of the test in the `transport_mdelta_limit_of_L1`
  conclusion is `t·φ` or `t·∇φ`, the RHS factors as `t · ι(t)` where `ι(t)` is
  the paper-correct first-variation family at the limit density (the
  `iota_firstorder_h_lim_dct` integrands `FA t`, `FB t` with the `t`-factor
  cancelled). The `1/t` cancellation then gives both sign halves of the
  squeeze.
* `h_lim` — the DCT continuity at `t = 0`, produced by
  `iota_firstorder_h_lim_dct` (child-4c) from child-4d's `hcontA`/`hcontB` and
  child-4d-A's `gA`/`gB` dominators; in the exact `Tendsto` shape
  `iota_firstorder_zero_concrete` consumes.

The two sign halves:
* `t > 0`: `0 ≤ t·ι(t)` gives `0 ≤ ι(t)`;
* `t < 0`: `0 ≤ t·ι(t)` gives `ι(t) ≤ 0`.

`iota_firstorder_zero_concrete` then forces `ι(0) = 0`, i.e. the transport
equation `eq:congest.transport` at `φ`. -/
theorem iota_transport_smooth_assembled
    {_V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (FA FB : ℝ → (Fin d → ℝ) → ℝ)
    (hFAdef : ∀ t, FA t = fun x =>
      (m x - 1) * φ x
        + m x * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x)))
    (hFBdef : ∀ t, FB t = fun x =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x))
    -- The per-direction limit-density inequality: the conclusion of
    -- `transport_mdelta_limit_of_L1` at the test direction `(t·φ, t·∇φ)`.
    (h_dir : ∀ t : ℝ,
      0 ≤
        (∫ x in UnitCube d,
            (m x - 1) * (t * φ x)
              + m x
                * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
                    ⬝ (fun i => t * Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
              * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
            + ε * absPowMinusTwo γBar (u x + t * φ x)
                * ((u x + t * φ x) * (t * φ x))
            ∂(volume : Measure (Fin d → ℝ))))
    -- DCT continuity at `t = 0` (from `iota_firstorder_h_lim_dct`).
    (h_lim :
      Filter.Tendsto
        (fun t =>
          (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
            + (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))))
        (nhds (0 : ℝ))
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
              ∂(volume : Measure (Fin d → ℝ)))))) :
    (∫ x in UnitCube d,
        (m x - 1) * φ x
          + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  -- Abbreviate the paper-correct first-variation family `ι t = ∫ FA t + ∫ FB t`.
  set ι : ℝ → ℝ := fun t =>
    (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))) with hιdef
  -- `t`-pull-out: the transport conclusion at `(tφ, t∇φ)` equals `t · ι t`.
  have h_pull : ∀ t : ℝ,
      (∫ x in UnitCube d,
          (m x - 1) * (t * φ x)
            + m x
              * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
                  ⬝ (fun i => t * Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
            * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
          + ε * absPowMinusTwo γBar (u x + t * φ x)
              * ((u x + t * φ x) * (t * φ x))
          ∂(volume : Measure (Fin d → ℝ)))
        = t * ι t := by
    intro t
    -- First integral: pointwise integrand `= t * FA t x`.
    have hA : (∫ x in UnitCube d,
          (m x - 1) * (t * φ x)
            + m x
              * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
                  ⬝ (fun i => t * Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
        = t * (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ))) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      rw [hFAdef t]
      -- `D_pH(...) ⬝ (t • ∇φ) = t * (D_pH(...) ⬝ ∇φ)`.
      have hdot :
          (DpH x (fun i => Du i x + t * Dφ i x) (m x) ⬝ (fun i => t * Dφ i x))
            = t * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x)) := by
        unfold euclideanDot
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      simp only []
      rw [hdot]; ring
    -- Second integral: pointwise integrand `= t * FB t x`.
    have hB : (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
            * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
          + ε * absPowMinusTwo γBar (u x + t * φ x)
              * ((u x + t * φ x) * (t * φ x))
          ∂(volume : Measure (Fin d → ℝ)))
        = t * (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      rw [hFBdef t]
      -- `(Du+t∇φ) ⬝ (t • ∇φ) = t * ((Du+t∇φ) ⬝ ∇φ)`.
      have hdot :
          ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
            = t * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x)) := by
        unfold euclideanDot
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      simp only []
      rw [hdot]; ring
    rw [hA, hB, hιdef]; ring
  -- Sign halves of the squeeze from `h_dir` via `h_pull`.
  have h_tι_nn : ∀ t : ℝ, 0 ≤ t * ι t := by
    intro t; rw [← h_pull t]; exact h_dir t
  have h_pos : ∀ t, 0 < t → 0 ≤ ι t := by
    intro t ht
    have := h_tι_nn t
    exact nonneg_of_mul_nonneg_right this ht
  have h_neg : ∀ t, t < 0 → ι t ≤ 0 := by
    intro t ht
    have hmul := h_tι_nn t
    nlinarith [hmul, ht]
  -- Close via the concrete first-order-variation combinator.
  exact iota_firstorder_zero_concrete (_V := _V) (DpH := DpH) (Du := Du)
    (m := m) (u := u) (ε := ε) (γBar := γBar) φ Dφ ι h_pos h_neg h_lim

/-- **`J`-extension sibling of `iota_transport_smooth_assembled`** (T2 phase6 BB
VIid child-5a-ii-β, connector J-reshape — the deliverable of this task).

Assembles the per-`φ` transport identity `eq:congest.transport` with the
paper-faithful extension flux `J(x, Du, m) ⬝ ∇φ` in place of the product
`m·D_pH(x, Du, m)·∇φ`. Its inputs are the `J`-stated outputs of the connector
chain:

* `h_dir` — the per-direction limit-density inequality, the conclusion shape of
  `transport_mdelta_limit_of_L1_J` at `(t·φ, t·∇φ)`, whose flux is
  `J(x, Du+t∇φ, m) ⬝ (t∇φ)`. Every test occurrence is `t·φ`/`t·∇φ`, so the RHS
  factors as `t · ι(t)` with `ι` the `J`-stated first-variation family
  (`iota_firstorder_h_lim_dct_J` integrands `FA t`, `FB t`, `t`-factor cancelled).
* `h_lim` — DCT continuity at `t = 0`, from `iota_firstorder_h_lim_dct_J`.

The `t`-pull-out `hdot` is a dot-product scaling, identical for `J`; the squeeze
closes via `iota_firstorder_zero_concrete_J`. No `0 < m`, no power-growth crutch:
the `J` extension carries the honest `{m = 0}` boundary value. -/
theorem iota_transport_smooth_assembled_J
    {_V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (FA FB : ℝ → (Fin d → ℝ) → ℝ)
    (hFAdef : ∀ t, FA t = fun x =>
      (m x - 1) * φ x
        + (J x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x)))
    (hFBdef : ∀ t, FB t = fun x =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x))
    (h_dir : ∀ t : ℝ,
      0 ≤
        (∫ x in UnitCube d,
            (m x - 1) * (t * φ x)
              + (J x (fun i => Du i x + t * Dφ i x) (m x)
                  ⬝ (fun i => t * Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
              * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
            + ε * absPowMinusTwo γBar (u x + t * φ x)
                * ((u x + t * φ x) * (t * φ x))
            ∂(volume : Measure (Fin d → ℝ))))
    (h_lim :
      Filter.Tendsto
        (fun t =>
          (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
            + (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))))
        (nhds (0 : ℝ))
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
              ∂(volume : Measure (Fin d → ℝ)))))) :
    (∫ x in UnitCube d,
        (m x - 1) * φ x
          + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  let _ := DpH
  set ι : ℝ → ℝ := fun t =>
    (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))) with hιdef
  have h_pull : ∀ t : ℝ,
      (∫ x in UnitCube d,
          (m x - 1) * (t * φ x)
            + (J x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => t * Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
            * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
          + ε * absPowMinusTwo γBar (u x + t * φ x)
              * ((u x + t * φ x) * (t * φ x))
          ∂(volume : Measure (Fin d → ℝ)))
        = t * ι t := by
    intro t
    have hA : (∫ x in UnitCube d,
          (m x - 1) * (t * φ x)
            + (J x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => t * Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
        = t * (∫ x in UnitCube d, FA t x ∂(volume : Measure (Fin d → ℝ))) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      rw [hFAdef t]
      have hdot :
          (J x (fun i => Du i x + t * Dφ i x) (m x) ⬝ (fun i => t * Dφ i x))
            = t * (J x (fun i => Du i x + t * Dφ i x) (m x)
                ⬝ (fun i => Dφ i x)) := by
        unfold euclideanDot
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      simp only []
      rw [hdot]; ring
    have hB : (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
            * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
          + ε * absPowMinusTwo γBar (u x + t * φ x)
              * ((u x + t * φ x) * (t * φ x))
          ∂(volume : Measure (Fin d → ℝ)))
        = t * (∫ x in UnitCube d, FB t x ∂(volume : Measure (Fin d → ℝ))) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      rw [hFBdef t]
      have hdot :
          ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => t * Dφ i x))
            = t * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x)) := by
        unfold euclideanDot
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      simp only []
      rw [hdot]; ring
    rw [hA, hB, hιdef]; ring
  have h_tι_nn : ∀ t : ℝ, 0 ≤ t * ι t := by
    intro t; rw [← h_pull t]; exact h_dir t
  have h_pos : ∀ t, 0 < t → 0 ≤ ι t := by
    intro t ht
    have := h_tι_nn t
    exact nonneg_of_mul_nonneg_right this ht
  have h_neg : ∀ t, t < 0 → ι t ≤ 0 := by
    intro t ht
    have hmul := h_tι_nn t
    nlinarith [hmul, ht]
  exact iota_firstorder_zero_concrete_J (_V := _V) (DpH := DpH) (J := J) (Du := Du)
    (m := m) (u := u) (ε := ε) (γBar := γBar) φ Dφ ι h_pos h_neg h_lim

/-! ## Step 3 of paper Lemma `lem:weak.is.strong` — the `t → 0`
first-variation passage at fixed `δ` (paper lines 1556–1565)

T2 phase6 BB VIid **child-4**. After child-3
(`congestion_VI_firstvar_ineq`) supplies, for fixed `δ > 0` and every
smooth periodic test direction `φ`, the inequality

```
0 ≤ (1/t) · BigInt_φ(t)   for all t > 0,
```

the paper substitutes `φ ↦ ±φ` and divides by `±t`. The function

```
ι_δ(φ, t) := (1/t) · BigInt_φ(t)
```

(the explicit `congestionIotaFamily` below — the raw first-variation
pairing of `A_ε` at the perturbed pair `(m_δ, u + t·φ)` against the
difference direction `(m_δ − m, t·φ, t·∇φ)`, scaled by `1/t`) satisfies
the **odd symmetry** `ι_δ(φ, t) = − ι_δ(−φ, −t)` because every
occurrence of the test in `BigInt` is `t·φ` or `t·∇φ`, which is invariant
under `(φ, t) ↦ (−φ, −t)`.

Consequently child-3 gives both halves of the squeeze:

* `ι_δ(φ, t) ≥ 0` for `t > 0` (child-3 at `φ`, `t`);
* `ι_δ(φ, t) ≤ 0` for `t < 0` (child-3 at `−φ`, `−t > 0`, then the odd
  symmetry).

Given the DCT limit `ι_δ(φ, ·) → ι0` at `t = 0` (continuity of the
integrand in `t` at `t = 0` with a uniform `|t| ≤ 1` integrable
dominator, paper line 1565 — bundled as a hypothesis, exactly as
`transport_mdelta_limit` and `iota_firstorder_zero` bundle their DCT
outputs), the squeeze combinator `iota_firstorder_zero` forces `ι0 = 0`.
This is the fixed-`δ` first-variation identity `eq:identity-congestion`. -/

/-- **The first-variation `ι`-family at fixed `δ`** (paper line 1557).

`congestionIotaFamily H DpH V m u Du ε δ φ t` is the raw first-variation
pairing of `A_ε` at the perturbed pair `(m_δ, u + t·φ, Du + t·∇φ)`
against the difference direction `(m_δ − m, t·φ, t·∇φ)`, scaled by `1/t`
— i.e. the right-hand side of the conclusion of
`congestion_VI_firstvar_ineq` (child-3), packaged as a function of `t`.

The defining feature exploited downstream is the **odd symmetry**
`congestionIotaFamily … φ t = − congestionIotaFamily … (−φ) (−t)`
(`congestionIotaFamily_neg_neg`): every occurrence of the test is `t·φ`
or `t·∇φ`, invariant under `(φ, t) ↦ (−φ, −t)`, while the prefactor
`1/t` is odd. -/
noncomputable def congestionIotaFamily
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (V m u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (ε γEps δ : ℝ)
    (φ : Periodic.SmoothPeriodic d) (t : ℝ) : ℝ :=
  (1 / t) *
    ((∫ x in UnitCube d,
        (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            - H x
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (max (m x) δ)
            + V x) * (max (m x) δ - m x)
          + max (m x) δ
              * (DpH x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ)))
      + ε * (∫ x in UnitCube d,
            vecAbsPowMinusTwo γEps
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
            + absPowMinusTwo γEps
                (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                  * (t * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))))

end Congestion
end StationaryMFG
end
