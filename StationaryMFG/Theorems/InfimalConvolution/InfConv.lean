module

public import StationaryMFG.Theorems.InfimalConvolution.Kernel

@[expose] public section

/-!
# Regularized Hamiltonian `H^ε` (a.k.a. `Hdelta`) via infimal convolution

This file introduces the §6 regularized Hamiltonian
`H^ε(x, p, m) := ⨅ q, H(x, p − q, m) + (1/ε) K(q)`
defined at paper line 1624 (`eq:defHdelta`,
`Source/FGU-monotone_revised.tex`).

`K(q) = ‖q‖ + ‖q‖^α` is the kernel from `Kernel.lean`. Strict
convexity of `K`, attainment of the infimum, and the formulae for
`D_p H^ε` are treated in separate (downstream) tasks; here we provide
only the definition together with three first-order properties:

* `Hdelta_le_H_self` — the regularization decreases `H` (test `q = 0`).
* `Hdelta_lower_bound` — `Hdelta` is bounded below by the unpenalized
  inf `⨅ q, H(x, p − q, m)`.
* `Hdelta_antitone_eps` — `Hdelta H ε x p m` is antitone in `ε > 0`:
  larger `ε` ⇒ smaller penalty `1/ε` ⇒ smaller integrand ⇒ smaller inf.

Each of these requires a `BddBelow` hypothesis on the family
`q ↦ H(x, p − q, m)`, since we work with `ciInf` (conditionally
complete inf on `ℝ`).
-/

namespace StationaryMFG
namespace InfimalConvolution

open StationaryMFG.Hamiltonian
open scoped Topology

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The §6 regularized Hamiltonian via infimal convolution with the
kernel `K`. Paper line 1624 (`eq:defHdelta`):
`H^ε(x, p, m) := ⨅ q, H(x, p − q, m) + (1/ε) K(q)`. -/
noncomputable def Hdelta (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) (m : ℝ) : ℝ :=
  ⨅ q : Fin d → ℝ, H x (p - q) m + (1 / ε) * K h q

lemma Hdelta_def (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) (m : ℝ) :
    Hdelta h ε x p m
      = ⨅ q : Fin d → ℝ, H x (p - q) m + (1 / ε) * K h q := rfl

/-! ### Bounded-below auxiliary

`ciInf_le` requires the family to be `BddBelow`. From a `BddBelow`
hypothesis on `q ↦ H(x, p − q, m)` we deduce `BddBelow` for the
penalized family, since the penalty `(1/ε) K q ≥ 0`. -/

private lemma bddBelow_penalized
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m + (1 / ε) * K h q) := by
  obtain ⟨L, hL⟩ := hBdd
  refine ⟨L, ?_⟩
  rintro y ⟨q, rfl⟩
  have hLq : L ≤ H x (p - q) m := hL ⟨q, rfl⟩
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hKq_nn : 0 ≤ K h q := K_nonneg h q
  have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg (le_of_lt hε_inv_pos) hKq_nn
  linarith

/-! ### `Hdelta ≤ H` (test `q = 0`) -/

/-- **Paper line 1624 corollary.** Testing `q = 0` in the infimum
gives `Hdelta H ε x p m ≤ H x p m`. -/
lemma Hdelta_le_H_self
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (x p : Fin d → ℝ) (m : ℝ)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    Hdelta h ε x p m ≤ H x p m := by
  unfold Hdelta
  -- Apply ciInf_le at q = 0; integrand becomes H x p m + 0.
  have hbdd := bddBelow_penalized h hε hBdd
  have hle :
      (⨅ q : Fin d → ℝ, H x (p - q) m + (1 / ε) * K h q)
        ≤ H x (p - 0) m + (1 / ε) * K h (0 : Fin d → ℝ) :=
    ciInf_le hbdd 0
  have hK0 : K h (0 : Fin d → ℝ) = 0 := K_zero h
  rw [hK0, mul_zero, add_zero, sub_zero] at hle
  exact hle

/-! ### Lower bound by the unpenalized inf -/

/-- **Lower bound:** `Hdelta H ε x p m ≥ ⨅ q, H(x, p − q, m)`.
The penalty `(1/ε) K q` is nonnegative, so dropping it can only
decrease each integrand value, and hence the infimum. -/
lemma Hdelta_lower_bound
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (x p : Fin d → ℝ) (m : ℝ)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    (⨅ q : Fin d → ℝ, H x (p - q) m) ≤ Hdelta h ε x p m := by
  unfold Hdelta
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  -- Pointwise: H x (p - q) m ≤ H x (p - q) m + (1/ε) * K h q.
  refine le_ciInf ?_
  intro q
  -- ⨅ ≤ H x (p - q) m, then add nonneg.
  have h₁ : (⨅ r : Fin d → ℝ, H x (p - r) m) ≤ H x (p - q) m :=
    ciInf_le hBdd q
  have hKq_nn : 0 ≤ K h q := K_nonneg h q
  have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg (le_of_lt hε_inv_pos) hKq_nn
  linarith

/-! ### Antitonicity in `ε` -/

/-- **Antitonicity in `ε`.** If `0 < ε₁ ≤ ε₂` then
`Hdelta H ε₁ x p m ≥ Hdelta H ε₂ x p m`, because the penalty
coefficient `1/ε` is *larger* at `ε₁`, making each integrand larger
and hence the infimum larger. -/
lemma Hdelta_antitone_eps
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hle : ε₁ ≤ ε₂)
    (x p : Fin d → ℝ) (m : ℝ)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    Hdelta h ε₂ x p m ≤ Hdelta h ε₁ x p m := by
  unfold Hdelta
  -- 1/ε₂ ≤ 1/ε₁ since 0 < ε₁ ≤ ε₂.
  have hinv : 1 / ε₂ ≤ 1 / ε₁ := by
    rw [one_div, one_div]
    exact inv_anti₀ hε₁ hle
  -- Bounded-below witness for ε₂'s family, used by `ciInf_le`.
  have hbdd₂ := bddBelow_penalized h hε₂ hBdd
  -- Pointwise inequality of integrands and the iInf-mono pattern.
  refine le_ciInf ?_
  intro q
  -- Bound ⨅ at ε₂ by the integrand at ε₂.
  have h_le_int₂ :
      (⨅ r : Fin d → ℝ, H x (p - r) m + (1 / ε₂) * K h r)
        ≤ H x (p - q) m + (1 / ε₂) * K h q :=
    ciInf_le hbdd₂ q
  -- Pointwise (1/ε₂) * K q ≤ (1/ε₁) * K q.
  have hKq_nn : 0 ≤ K h q := K_nonneg h q
  have hpen :
      (1 / ε₂) * K h q ≤ (1 / ε₁) * K h q :=
    mul_le_mul_of_nonneg_right hinv hKq_nn
  linarith

/-! ### Lower bound at the minimizer

Paper line 1796, equation `H-inf-conv-lower`. When the infimum
defining `Hdelta` is attained at some point `qStar`, we can combine
the kernel lower bound `K h q ≥ ‖q‖^α`, the bound `1/ε ≥ 1` for
`0 < ε ≤ 1`, and the weak-growth lower bound on `H` to derive

  `Hdelta h ε x p m ≥ ‖qStar‖^α + ‖p - qStar‖^α / h.C - h.C * (m^β + 1)`.

The attainment certificate `hqStar` and the per-point lower bound
`hLower` are passed as explicit hypotheses; this avoids any
dependence on strict convexity of `K` (needed for constructing
`qStar`) and on the `∀ᵐ x` quantification of `HypothesisWeakGrowth.lower`. -/

/-- **Paper line 1796 (`H-inf-conv-lower`).** Assuming the infimum
defining `Hdelta` is attained at `qStar`, and that the per-point
weak-growth lower bound holds at `(x, p - qStar, m)`, we have

  `Hdelta h ε x p m ≥ ‖qStar‖^α + ‖p - qStar‖^α / h.C - h.C * (m^β + 1)`.

This is the shared intermediate bound used in
`paper:prop:boundsHepsilon.b` and `paper:prop:boundsHepsilon.c`. -/
lemma Hdelta_lower_bound_via_minimizer
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x p : Fin d → ℝ} {m : ℝ} (qStar : Fin d → ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m) :
    ‖qStar‖ ^ h.α + ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1)
      ≤ Hdelta h ε x p m := by
  -- Step 1: rewrite Hdelta using the attainment certificate.
  rw [hqStar]
  -- Step 2: Kernel lower bound K h qStar ≥ ‖qStar‖^α.
  have hK_ge : ‖qStar‖ ^ h.α ≤ K h qStar := K_ge_rpow h qStar
  -- Step 3: 1/ε ≥ 1 since 0 < ε ≤ 1.
  have h_inv_ge_one : (1 : ℝ) ≤ 1 / ε := one_le_one_div hε hε1
  -- Step 4: `‖qStar‖^α ≥ 0` so `(1/ε) * K h qStar ≥ 1 * ‖qStar‖^α = ‖qStar‖^α`.
  have hqStar_α_nn : 0 ≤ ‖qStar‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have h_K_nn : 0 ≤ K h qStar := K_nonneg h qStar
  -- (1/ε) * K h qStar ≥ 1 * K h qStar = K h qStar ≥ ‖qStar‖^α.
  have h_inv_mul_K_ge :
      ‖qStar‖ ^ h.α ≤ (1 / ε) * K h qStar := by
    have h_one_mul : 1 * K h qStar ≤ (1 / ε) * K h qStar :=
      mul_le_mul_of_nonneg_right h_inv_ge_one h_K_nn
    have h_K_ge_rpow' : ‖qStar‖ ^ h.α ≤ K h qStar := hK_ge
    linarith
  -- Combine with hLower:
  -- H x (p - qStar) m + (1/ε) * K h qStar
  --   ≥ (‖p - qStar‖^α / h.C - h.C * (m^β + 1)) + ‖qStar‖^α.
  linarith

/-! ### `ε`-dependent upper bound on `H^ε`

Paper line 1784, eq. `eq:H-epsilon.upper`:

  `H^ε(x, p, m) ≤ C_ε ‖p‖^α − m^β / C + C`,

for `0 < ε ≤ 1` and `m > 0`. The paper proof (lines 1791–1793):
test `q = p` in the inf-conv definition, then absorb the linear
term `(1/ε) ‖p‖` into `(1/ε) ‖p‖^α` by Young's inequality and bound
`H(x, 0, m)` by `eq:assH.upper.weak`.

Following the local-hypothesis pattern of
`Hdelta_lower_bound_via_minimizer`, we pass the per-point upper bound
`H x 0 m ≤ -m^β/C + C` as an explicit hypothesis (the user can
obtain it by `filter_upwards` on `h.upper` for `a.e. x`). -/

/-- **Paper Proposition `prop:boundsHepsilon.a` (line 1784,
eq. `eq:H-epsilon.upper`).** Under `HypothesisWeakGrowth`, for
`0 < ε ≤ 1` and `m > 0`, the regularized Hamiltonian admits the
`ε`-dependent upper bound

  `H^ε(x, p, m) ≤ (2/ε) ‖p‖^α − m^β / C + (1/ε + C)`.

The per-point upper bound `hUpper` at `(x, 0, m)` is passed as an
explicit hypothesis (obtainable from `h.upper` via `filter_upwards`
for a.e. `x`), matching the per-point pattern of
`Hdelta_lower_bound_via_minimizer`. The `BddBelow` witness `hBdd`
discharges the `ciInf_le` side-condition. -/
lemma Hdelta_upper_bound
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1)
    {x p : Fin d → ℝ} {m : ℝ} (_hm : 0 < m)
    (hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    Hdelta h ε x p m
      ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α
          - (m ^ h.β) / h.C + (K_sup_const (d := d) h / ε + h.C) := by
  -- Step 1: test q = p in the inf-conv definition.
  unfold Hdelta
  have hbdd := bddBelow_penalized h hε hBdd
  have h_inf_le :
      (⨅ q : Fin d → ℝ, H x (p - q) m + (1 / ε) * K h q)
        ≤ H x (p - p) m + (1 / ε) * K h p :=
    ciInf_le hbdd p
  -- Simplify `p - p = 0`.
  rw [sub_self] at h_inf_le
  -- Step 2: bound the kernel `K h p ≤ K_sup_const * (‖p‖^α + 1)`.
  have hKp_bound : K h p ≤ K_sup_const (d := d) h * (‖p‖ ^ h.α + 1) :=
    K_le_sup_polynomial h p
  set Cd : ℝ := K_sup_const (d := d) h with hCd_def
  have hCd_nn : 0 ≤ Cd := K_sup_const_nonneg h
  -- Step 3: multiply by `1/ε > 0`.
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
  have h_mul_K :
      (1 / ε) * K h p ≤ (1 / ε) * (Cd * (‖p‖ ^ h.α + 1)) :=
    mul_le_mul_of_nonneg_left hKp_bound hε_inv_nn
  -- Distribute: (1/ε)*(Cd * (‖p‖^α + 1)) = (Cd/ε) * ‖p‖^α + Cd/ε.
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have h_distrib :
      (1 / ε) * (Cd * (‖p‖ ^ h.α + 1)) = (Cd / ε) * ‖p‖ ^ h.α + Cd / ε := by
    field_simp
  rw [h_distrib] at h_mul_K
  -- Step 4: combine with `hUpper`.
  have h_combined :
      H x 0 m + (1 / ε) * K h p
        ≤ (Cd / ε) * ‖p‖ ^ h.α - (m ^ h.β) / h.C + (Cd / ε + h.C) := by
    have hsum :
        H x 0 m + (1 / ε) * K h p
          ≤ (-(m ^ h.β) / h.C + h.C) + ((Cd / ε) * ‖p‖ ^ h.α + Cd / ε) :=
      add_le_add hUpper h_mul_K
    have hrw :
        (-(m ^ h.β) / h.C + h.C) + ((Cd / ε) * ‖p‖ ^ h.α + Cd / ε)
          = (Cd / ε) * ‖p‖ ^ h.α - (m ^ h.β) / h.C + (Cd / ε + h.C) := by
      ring
    rw [hrw] at hsum
    exact hsum
  exact le_trans h_inf_le h_combined

/-! ### ε-uniform lower bound on `H^ε` (paper `prop:boundsHepsilon.c`)

Paper line 1786, eq. `eq:H-epsilon.lower.uniform`:

  `H^ε(x, p, m) ≥ (1/C') ‖p‖^α − C' (m^β + 1)`,

with `C'` independent of `ε` (we take `C' := 2^α · (h.C + 1)`). The
paper proof (lines 1811-1813) starts from the minimizer-based lower
bound `Hdelta_lower_bound_via_minimizer`,

  `Hdelta h ε x p m ≥ ‖q*‖^α + ‖p − q*‖^α / h.C − h.C · (m^β + 1)`,

then uses the elementary inequality
`max{‖q*‖, ‖p − q*‖} ≥ ‖p‖/2` (triangle inequality) to conclude. -/

/-- **Paper Proposition `prop:boundsHepsilon.c` (line 1786,
eq. `eq:H-epsilon.lower.uniform`).** Under `HypothesisWeakGrowth`, for
`0 < ε ≤ 1`, the regularized Hamiltonian admits the *ε-uniform* lower
bound

  `Hdelta h ε x p m ≥ ‖p‖^α / (2^α · (h.C + 1)) − (2^α · (h.C + 1)) · (m^β + 1)`.

The constant `C' := 2^α · (h.C + 1)` is independent of `ε`, matching
the paper. The attainment certificate `hqStar` at `qStar`, the
per-point weak-growth lower bound `hLower`, and the sign witness
`hmβ : 0 ≤ m ^ h.β + 1` (a consequence of `0 < m`, `0 < β` in the
paper, making `m^β ≥ 0`) are passed as explicit hypotheses, following
the pattern of `Hdelta_lower_bound_via_minimizer`. -/
lemma Hdelta_lower_bound_uniform
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x p : Fin d → ℝ} {m : ℝ} (qStar : Fin d → ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m)
    (hmβ : 0 ≤ m ^ h.β + 1) :
    ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1))
        - ((2 : ℝ) ^ h.α * (h.C + 1)) * (m ^ h.β + 1)
      ≤ Hdelta h ε x p m := by
  -- Step 1: invoke the minimizer-based lower bound.
  have h_min :
      ‖qStar‖ ^ h.α + ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1)
        ≤ Hdelta h ε x p m :=
    Hdelta_lower_bound_via_minimizer h hε hε1 qStar hqStar hLower
  -- Step 2: set up positivity facts.
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_nn : 0 ≤ h.α := le_of_lt hα_pos
  have hC_pos : 0 < h.C := h.hC
  have hC1_pos : 0 < h.C + 1 := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have h2α_pos : (0 : ℝ) < (2 : ℝ) ^ h.α := Real.rpow_pos_of_pos h2_pos _
  have h2α_nn : (0 : ℝ) ≤ (2 : ℝ) ^ h.α := le_of_lt h2α_pos
  have hCprime_pos : (0 : ℝ) < (2 : ℝ) ^ h.α * (h.C + 1) :=
    mul_pos h2α_pos hC1_pos
  have hp_nn : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
  have hq_nn : (0 : ℝ) ≤ ‖qStar‖ := norm_nonneg _
  have hr_nn : (0 : ℝ) ≤ ‖p - qStar‖ := norm_nonneg _
  have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg hp_nn _
  have hqα_nn : (0 : ℝ) ≤ ‖qStar‖ ^ h.α := Real.rpow_nonneg hq_nn _
  have hrα_nn : (0 : ℝ) ≤ ‖p - qStar‖ ^ h.α := Real.rpow_nonneg hr_nn _
  -- Step 3: triangle inequality `‖p‖ ≤ ‖qStar‖ + ‖p - qStar‖`.
  have h_tri : ‖p‖ ≤ ‖qStar‖ + ‖p - qStar‖ := by
    have : p = qStar + (p - qStar) := by ring
    calc ‖p‖ = ‖qStar + (p - qStar)‖ := by rw [← this]
      _ ≤ ‖qStar‖ + ‖p - qStar‖ := norm_add_le _ _
  -- Step 4: `‖p‖/2 ≤ max ‖qStar‖ ‖p - qStar‖`.
  have h_half_le_max : ‖p‖ / 2 ≤ max ‖qStar‖ ‖p - qStar‖ := by
    have h_sum_le : ‖qStar‖ + ‖p - qStar‖ ≤ 2 * max ‖qStar‖ ‖p - qStar‖ := by
      have h1 : ‖qStar‖ ≤ max ‖qStar‖ ‖p - qStar‖ := le_max_left _ _
      have h2 : ‖p - qStar‖ ≤ max ‖qStar‖ ‖p - qStar‖ := le_max_right _ _
      linarith
    have : ‖p‖ ≤ 2 * max ‖qStar‖ ‖p - qStar‖ := le_trans h_tri h_sum_le
    linarith
  -- Step 5: the key bound `‖p‖^α / (2^α (C+1)) ≤ ‖qStar‖^α + ‖p - qStar‖^α / C`.
  have h_key :
      ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1))
        ≤ ‖qStar‖ ^ h.α + ‖p - qStar‖ ^ h.α / h.C := by
    -- `(‖p‖/2)^α = ‖p‖^α / 2^α`.
    have h_pow_half : (‖p‖ / 2) ^ h.α = ‖p‖ ^ h.α / (2 : ℝ) ^ h.α := by
      rw [Real.div_rpow hp_nn h2_nn]
    -- Case-split on which of ‖qStar‖, ‖p-qStar‖ realises the max.
    rcases le_or_gt ‖p - qStar‖ ‖qStar‖ with hmax | hmax
    · -- `max = ‖qStar‖`, so `‖p‖/2 ≤ ‖qStar‖`.
      have hmax_eq : max ‖qStar‖ ‖p - qStar‖ = ‖qStar‖ := max_eq_left hmax
      rw [hmax_eq] at h_half_le_max
      -- `(‖p‖/2)^α ≤ ‖qStar‖^α` by `Real.rpow_le_rpow`.
      have h_half_nn : (0 : ℝ) ≤ ‖p‖ / 2 := by linarith
      have h_pow_le : (‖p‖ / 2) ^ h.α ≤ ‖qStar‖ ^ h.α :=
        Real.rpow_le_rpow h_half_nn h_half_le_max hα_nn
      rw [h_pow_half] at h_pow_le
      -- `‖p‖^α / (2^α(C+1)) ≤ ‖p‖^α / 2^α` since `C+1 ≥ 1`.
      have h_one_le_C1 : (1 : ℝ) ≤ h.C + 1 := by linarith
      have h_2α_le_prod : (2 : ℝ) ^ h.α ≤ (2 : ℝ) ^ h.α * (h.C + 1) := by
        have := mul_le_mul_of_nonneg_left h_one_le_C1 h2α_nn
        simpa using this
      have h_div_le : ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1))
                       ≤ ‖p‖ ^ h.α / (2 : ℝ) ^ h.α :=
        div_le_div_of_nonneg_left hpα_nn h2α_pos h_2α_le_prod
      have h_chain : ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1)) ≤ ‖qStar‖ ^ h.α :=
        le_trans h_div_le h_pow_le
      -- Add the nonneg `‖p - qStar‖^α / h.C`.
      have h_rα_div_nn : 0 ≤ ‖p - qStar‖ ^ h.α / h.C :=
        div_nonneg hrα_nn (le_of_lt hC_pos)
      linarith
    · -- `max = ‖p - qStar‖`, so `‖p‖/2 ≤ ‖p - qStar‖`.
      have hmax' : ‖qStar‖ ≤ ‖p - qStar‖ := le_of_lt hmax
      have hmax_eq : max ‖qStar‖ ‖p - qStar‖ = ‖p - qStar‖ := max_eq_right hmax'
      rw [hmax_eq] at h_half_le_max
      have h_half_nn : (0 : ℝ) ≤ ‖p‖ / 2 := by linarith
      have h_pow_le : (‖p‖ / 2) ^ h.α ≤ ‖p - qStar‖ ^ h.α :=
        Real.rpow_le_rpow h_half_nn h_half_le_max hα_nn
      rw [h_pow_half] at h_pow_le
      -- Divide by `h.C` on both sides.
      have h_div_pow_le :
          ‖p‖ ^ h.α / (2 : ℝ) ^ h.α / h.C
            ≤ ‖p - qStar‖ ^ h.α / h.C :=
        div_le_div_of_nonneg_right h_pow_le (le_of_lt hC_pos)
      -- Simplify LHS: `‖p‖^α / 2^α / C = ‖p‖^α / (2^α · C)`.
      have h_div_simp :
          ‖p‖ ^ h.α / (2 : ℝ) ^ h.α / h.C
            = ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * h.C) := by
        field_simp
      rw [h_div_simp] at h_div_pow_le
      -- Now `‖p‖^α / (2^α(C+1)) ≤ ‖p‖^α / (2^α C)` since `C ≤ C+1`.
      have hC_le_C1 : h.C ≤ h.C + 1 := by linarith
      have h_2αC_pos : (0 : ℝ) < (2 : ℝ) ^ h.α * h.C := mul_pos h2α_pos hC_pos
      have h_2αC_le : (2 : ℝ) ^ h.α * h.C ≤ (2 : ℝ) ^ h.α * (h.C + 1) :=
        mul_le_mul_of_nonneg_left hC_le_C1 h2α_nn
      have h_div_le :
          ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1))
            ≤ ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * h.C) :=
        div_le_div_of_nonneg_left hpα_nn h_2αC_pos h_2αC_le
      have h_chain :
          ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1)) ≤ ‖p - qStar‖ ^ h.α / h.C :=
        le_trans h_div_le h_div_pow_le
      linarith
  -- Step 6: bound `h.C * (m^β + 1) ≤ C' * (m^β + 1)` since `h.C ≤ C'`.
  -- `C' = 2^α · (h.C + 1) ≥ 1 · h.C = h.C` since `2^α ≥ 1` and `C+1 ≥ C`.
  have h_one_le_2α : (1 : ℝ) ≤ (2 : ℝ) ^ h.α := by
    have h1 : (1 : ℝ) ^ h.α ≤ (2 : ℝ) ^ h.α :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hα_nn
    simpa using h1
  have hC_le_Cp : h.C ≤ (2 : ℝ) ^ h.α * (h.C + 1) := by
    have hC_le_C1 : h.C ≤ h.C + 1 := by linarith
    calc h.C ≤ h.C + 1 := hC_le_C1
      _ = 1 * (h.C + 1) := by ring
      _ ≤ (2 : ℝ) ^ h.α * (h.C + 1) :=
        mul_le_mul_of_nonneg_right h_one_le_2α (le_of_lt hC1_pos)
  -- Step 7: `h.C * (m^β + 1) ≤ C' * (m^β + 1)` since `h.C ≤ C'` and `m^β + 1 ≥ 0`.
  have h_mass : h.C * (m ^ h.β + 1) ≤ ((2 : ℝ) ^ h.α * (h.C + 1)) * (m ^ h.β + 1) :=
    mul_le_mul_of_nonneg_right hC_le_Cp hmβ
  -- Step 8: chain inequalities.
  -- From h_key: ‖p‖^α / C' ≤ ‖qStar‖^α + ‖p - qStar‖^α / h.C.
  -- From h_mass: -C' (m^β+1) ≤ -h.C (m^β+1).
  -- Add: ‖p‖^α/C' - C'(m^β+1) ≤ ‖qStar‖^α + ‖p-qStar‖^α/h.C - h.C(m^β+1)
  --                          ≤ Hdelta h ε x p m by h_min.
  linarith

/-- Unit test: `Hdelta` is well-defined and the trivial
`q = 0` upper bound holds, here exercised at the constant Hamiltonian
`H x p m = 0` (which is bounded below by `0`). -/
example (h : HypothesisWeakGrowth (d := d) (fun _ _ _ => (0 : ℝ)) DpH)
    {ε : ℝ} (hε : 0 < ε) (x p : Fin d → ℝ) (m : ℝ) :
    Hdelta h ε x p m ≤ (fun _ _ _ => (0 : ℝ)) x p m := by
  refine Hdelta_le_H_self h hε x p m ?_
  refine ⟨0, ?_⟩
  rintro y ⟨q, rfl⟩
  exact le_refl _

/-- Unit test: antitonicity in `ε` at the same constant Hamiltonian. -/
example (h : HypothesisWeakGrowth (d := d) (fun _ _ _ => (0 : ℝ)) DpH)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hle : ε₁ ≤ ε₂)
    (x p : Fin d → ℝ) (m : ℝ) :
    Hdelta h ε₂ x p m ≤ Hdelta h ε₁ x p m := by
  refine Hdelta_antitone_eps h hε₁ hε₂ hle x p m ?_
  refine ⟨0, ?_⟩
  rintro y ⟨q, rfl⟩
  exact le_refl _

/-- Unit test for `Hdelta_lower_bound_via_minimizer`. The attainment
certificate and the per-point weak-growth lower bound are passed as
`sorry`-stubs (allowed by the task spec since this is an example
exercising the lemma's signature, not its proof). -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x p qStar : Fin d → ℝ) (m : ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m) :
    ‖qStar‖ ^ h.α + ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1)
      ≤ Hdelta h ε x p m :=
  Hdelta_lower_bound_via_minimizer h hε hε1 qStar hqStar hLower

/-- Unit test for `Hdelta_upper_bound`. The per-point upper bound and
the `BddBelow` witness are passed; we simply check that the lemma's
signature delivers the claimed inequality (with the dimension/exponent
constant `K_sup_const h`). -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m)
    (hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    Hdelta h ε x p m
      ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α
          - (m ^ h.β) / h.C + (K_sup_const (d := d) h / ε + h.C) :=
  Hdelta_upper_bound h hε hε1 hm hUpper hBdd

/-- Unit test for `Hdelta_lower_bound_uniform`. The attainment
certificate, the per-point weak-growth lower bound, and the sign
witness on `m^β + 1` are passed; the lemma's signature delivers the
ε-uniform lower bound. -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x p qStar : Fin d → ℝ) (m : ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m)
    (hmβ : 0 ≤ m ^ h.β + 1) :
    ‖p‖ ^ h.α / ((2 : ℝ) ^ h.α * (h.C + 1))
        - ((2 : ℝ) ^ h.α * (h.C + 1)) * (m ^ h.β + 1)
      ≤ Hdelta h ε x p m :=
  Hdelta_lower_bound_uniform h hε hε1 qStar hqStar hLower hmβ

/-! ### ε-independent Lagrangian lower bound for `H^ε`
(paper `prop:boundsHepsilon.d`)

Paper line 1787, eq. `eq:DpHdelta.dotp.minusH`:

  `D_pH^ε(x, p, m) ⬝ p − H^ε(x, p, m) ≥ m^β / C − C`,

for `0 < ε ≤ 1`, `m > 0`, and a.e. `x`. The constant `C` matches the
bundle's `h.C`, so the bound is *ε-independent*.

The paper proof (lines 1815-1817) only uses convexity of
`p ↦ H^ε(x, p, m)` (no minimizer uniqueness or strict convexity of `K`):

1. Subgradient inequality at the origin gives
   `D_pH^ε(x, p, m) ⬝ p − H^ε(x, p, m) ≥ −H^ε(x, 0, m)`.
2. `Hdelta_le_H_self` at `p = 0` combined with `h.upper` gives
   `H^ε(x, 0, m) ≤ −m^β / C + C`, hence
   `−H^ε(x, 0, m) ≥ m^β / C − C`.

Following the local-hypothesis pattern of
`Hdelta_lower_bound_via_minimizer`, the convex-at-zero inequality is
passed as an explicit hypothesis. -/

/-- **Paper Proposition `prop:boundsHepsilon.d` (line 1787,
eq. `eq:DpHdelta.dotp.minusH`).** Under `HypothesisWeakGrowth`, for
`0 < ε ≤ 1` and `m > 0`, the regularized Hamiltonian satisfies the
*ε-independent* Lagrangian lower bound

  `DpHε(x, p, m) ⬝ p − H^ε(x, p, m) ≥ m^β / h.C − h.C`.

The convex-at-zero inequality for `H^ε` (which follows from convexity of
`p ↦ H^ε(x, p, m)` evaluated at the origin) is passed as an explicit
hypothesis `hCx`, mirroring `Hamiltonian.lagrangian_lower_bound`. The
per-point upper bound `hUp` at `(x, 0, m)` and the `BddBelow` witness
`hBdd` for the family `q ↦ H(x, -q, m)` (needed by `Hdelta_le_H_self`
at `p = 0`) discharge the side conditions.

No `qStar`, no strict convexity of `K`, and no minimizer uniqueness are
used — the proof is pure convex algebra. -/
lemma Hdelta_lagrangian_lower_bound
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m : ℝ} (_hm : 0 < m)
    (hCx :
      Hdelta h ε x p m - (DpHε x p m) ⬝ p ≤ Hdelta h ε x 0 m)
    (hUp : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m)) :
    (m ^ h.β) / h.C - h.C ≤ (DpHε x p m) ⬝ p - Hdelta h ε x p m := by
  -- Step 1: `Hdelta_le_H_self` at `p = 0` gives `H^ε(x, 0, m) ≤ H(x, 0, m)`.
  have h_self : Hdelta h ε x 0 m ≤ H x (0 : Fin d → ℝ) m :=
    Hdelta_le_H_self h hε x 0 m hBdd
  -- Step 2: chain with `hUp` to get `H^ε(x, 0, m) ≤ -m^β/C + C`.
  have h_zero_le : Hdelta h ε x 0 m ≤ -(m ^ h.β) / h.C + h.C :=
    h_self.trans hUp
  -- Step 3: convexity at `0` says
  -- `Hdelta h ε x p m − DpHε(x, p, m) ⬝ p ≤ Hdelta h ε x 0 m`.
  -- Chain with `h_zero_le`.
  have h_chain :
      Hdelta h ε x p m - (DpHε x p m) ⬝ p ≤ -(m ^ h.β) / h.C + h.C :=
    hCx.trans h_zero_le
  -- Step 4: algebraic rearrangement.
  have hrw : -(m ^ h.β) / h.C = -((m ^ h.β) / h.C) := by ring
  linarith [h_chain, hrw]

/-- Unit test for `Hdelta_lagrangian_lower_bound`. The convex-at-zero
inequality and the per-point upper bound are passed as inputs; the
lemma's signature delivers the ε-independent Lagrangian lower bound. -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m)
    (hCx :
      Hdelta h ε x p m - (DpHε x p m) ⬝ p ≤ Hdelta h ε x 0 m)
    (hUp : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m)) :
    (m ^ h.β) / h.C - h.C ≤ (DpHε x p m) ⬝ p - Hdelta h ε x p m :=
  Hdelta_lagrangian_lower_bound h hε hε1 DpHε hm hCx hUp hBdd

/-! ### Existence of the inf-conv minimizer `q^ε`

Paper line 1630 (`Source/FGU-monotone_revised.tex`): the infimum
defining `H^ε(x, p, m) = inf_q H(x, p − q, m) + (1/ε) K(q)` is attained
by a compactness argument. The objective is coercive
(`K(q) ≥ ‖q‖^α → ∞`) and bounded below
(`H(x, p − q, m) ≥ ‖p − q‖^α/h.C − h.C(m^β + 1)`); together with
continuity these guarantee a minimum on any closed ball that contains
a sublevel set, hence a global minimum.

This produces the *existence* of a minimizer only. Uniqueness is
deferred to a separate task (and is not needed for the Lagrangian
lower bound, Bound .b, .c, or .d). -/

/-- Auxiliary: under the per-point lower bound on `H x · m`,
the family `q ↦ H x (p - q) m + (1/ε) K h q` is bounded below by the
explicit constant `-h.C * (m^β + 1)`. -/
private lemma bddBelow_objective
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m) :
    BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m + (1 / ε) * K h q) := by
  refine ⟨-(h.C * (m ^ h.β + 1)), ?_⟩
  rintro y ⟨q, rfl⟩
  have hLow := hLower q
  have hC_pos : 0 < h.C := h.hC
  have hpα_nn : 0 ≤ ‖p - q‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hdiv_nn : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
    div_nonneg hpα_nn (le_of_lt hC_pos)
  have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt (one_div_pos.mpr hε)
  have hK_nn : 0 ≤ K h q := K_nonneg h q
  have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
  linarith

/-- **Paper line 1630.** Existence of the inf-conv minimizer `q*` for
`Hdelta H ε x p m`: assuming per-point continuity of `H x · m` and the
per-point weak-growth lower bound, there exists `q*` with
`H x (p - q*) m + (1/ε) K h q* = Hdelta H ε x p m`.

The per-point hypotheses `hCont` and `hLower` are obtainable from
`h.continuous_H_pm` and `h.lower` respectively (after `filter_upwards`
for a.e. `x`). -/
lemma qStar_exists
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m) :
    ∃ q : Fin d → ℝ,
      H x (p - q) m + (1 / ε) * K h q = Hdelta h ε x p m := by
  classical
  -- The objective function.
  set F : (Fin d → ℝ) → ℝ := fun q => H x (p - q) m + (1 / ε) * K h q with hFdef
  -- BddBelow witness.
  have hBddF : BddBelow (Set.range F) := bddBelow_objective h hε hLower
  -- F is continuous: H x (p - ·) m continuous (given) + K continuous.
  have hF_cont : Continuous F := by
    refine hCont.add ?_
    exact continuous_const.mul (K_continuous h)
  -- Positivity facts.
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_ge_one : (1 : ℝ) ≤ h.α := le_of_lt h.hα
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hC_pos : 0 < h.C := h.hC
  -- Step: lower bound F(q) ≥ -h.C*(m^β + 1) + (1/ε) * ‖q‖^α.
  have hF_lower :
      ∀ q : Fin d → ℝ, -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α ≤ F q := by
    intro q
    have hLow := hLower q
    have hpα_nn : 0 ≤ ‖p - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hK_ge : ‖q‖ ^ h.α ≤ K h q := K_ge_rpow h q
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have h_mul : (1 / ε) * ‖q‖ ^ h.α ≤ (1 / ε) * K h q :=
      mul_le_mul_of_nonneg_left hK_ge hε_inv_nn
    -- F q = H x (p - q) m + (1/ε) K h q
    --     ≥ (‖p-q‖^α/C - C(m^β+1)) + (1/ε) ‖q‖^α
    --     ≥ -C(m^β+1) + (1/ε) ‖q‖^α  (dropping the nonneg term).
    change -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
        ≤ H x (p - q) m + (1 / ε) * K h q
    linarith
  -- Define the threshold M := F(0) + h.C * (m^β + 1).
  set M : ℝ := F 0 + h.C * (m ^ h.β + 1) with hMdef
  -- Choose R := max 1 (ε * M + 1) so that R ≥ 1 and ‖q‖ > R ⇒ ‖q‖^α > ε*M.
  set R : ℝ := max 1 (ε * M + 1) with hRdef
  have hR_ge_one : (1 : ℝ) ≤ R := le_max_left _ _
  have hR_ge_εM_one : ε * M + 1 ≤ R := le_max_right _ _
  have hR_nn : 0 ≤ R := le_trans zero_le_one hR_ge_one
  -- The closed ball is compact (Fin d → ℝ is a ProperSpace).
  set B : Set (Fin d → ℝ) := Metric.closedBall 0 R with hBdef
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_nonempty : B.Nonempty := ⟨0, by
    simp [hBdef, Metric.mem_closedBall, hR_nn]⟩
  -- Apply IsCompact.exists_isMinOn.
  obtain ⟨q', hq'B, hq'min⟩ :=
    hB_compact.exists_isMinOn hB_nonempty hF_cont.continuousOn
  -- Goal: F q' = ⨅ q, F q. Show F q' is a lower bound and ciInf ≤ F q'.
  refine ⟨q', ?_⟩
  -- Show: F q' = Hdelta h ε x p m = ⨅ q, F q.
  unfold Hdelta
  -- It suffices to show F q' ≤ F q for all q (global min), then ciInf = F q'.
  have h_global :
      ∀ q : Fin d → ℝ, F q' ≤ F q := by
    intro q
    by_cases hq_in : q ∈ B
    · -- q in the ball: use IsMinOn.
      exact hq'min hq_in
    · -- q not in the ball: ‖q‖ > R.
      have hq_norm : R < ‖q‖ := by
        rw [hBdef, Metric.mem_closedBall, dist_zero_right] at hq_in
        exact lt_of_not_ge hq_in
      have hq_ge_one : (1 : ℝ) ≤ ‖q‖ := le_trans hR_ge_one (le_of_lt hq_norm)
      have hq_pos : (0 : ℝ) < ‖q‖ := lt_of_lt_of_le zero_lt_one hq_ge_one
      -- ‖q‖^α ≥ ‖q‖^1 = ‖q‖.
      have h_rpow_mono : ‖q‖ ^ (1 : ℝ) ≤ ‖q‖ ^ h.α :=
        Real.rpow_le_rpow_of_exponent_le hq_ge_one hα_ge_one
      have h_rpow_one : ‖q‖ ^ (1 : ℝ) = ‖q‖ := Real.rpow_one _
      have hq_α_ge : ‖q‖ ≤ ‖q‖ ^ h.α := by
        have := h_rpow_mono
        rw [h_rpow_one] at this
        exact this
      -- Now F q ≥ -C(m^β+1) + (1/ε) ‖q‖^α ≥ -C(m^β+1) + (1/ε) ‖q‖.
      have h_pen_ge : (1 / ε) * ‖q‖ ≤ (1 / ε) * ‖q‖ ^ h.α :=
        mul_le_mul_of_nonneg_left hq_α_ge (le_of_lt hε_inv_pos)
      have hF_q_low :
          -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ≤ F q := by
        have h1 := hF_lower q
        linarith
      -- We need F q' ≤ F q. We know q' ∈ B, so 0 ∈ B (since R ≥ 0). By IsMinOn:
      -- F q' ≤ F 0.
      have h0_in_B : (0 : Fin d → ℝ) ∈ B := by
        simp [hBdef, Metric.mem_closedBall, hR_nn]
      have hF_q'_le_F0 : F q' ≤ F 0 := hq'min h0_in_B
      -- Need: F 0 ≤ F q. Use: (1/ε) * ‖q‖ ≥ (1/ε) * R ≥ (1/ε) * (ε * M + 1) = M + 1/ε.
      -- So F q ≥ -C(m^β+1) + M + 1/ε = F 0 + 1/ε > F 0.
      have h_eps_q : (1 / ε) * (ε * M + 1) ≤ (1 / ε) * ‖q‖ := by
        have hq_ge_εM1 : ε * M + 1 ≤ ‖q‖ := le_trans hR_ge_εM_one (le_of_lt hq_norm)
        exact mul_le_mul_of_nonneg_left hq_ge_εM1 (le_of_lt hε_inv_pos)
      -- (1/ε) * (ε * M + 1) = M + 1/ε.
      have h_eps_simp : (1 / ε) * (ε * M + 1) = M + 1 / ε := by
        field_simp
      rw [h_eps_simp] at h_eps_q
      -- Now: F q ≥ -C(m^β+1) + (M + 1/ε) = -C(m^β+1) + F 0 + C(m^β+1) + 1/ε
      --           = F 0 + 1/ε.
      have hM_unfold : M = F 0 + h.C * (m ^ h.β + 1) := hMdef
      have hF_q_ge_F0 : F 0 + 1 / ε ≤ F q := by
        have hcomb :
            -(h.C * (m ^ h.β + 1)) + (M + 1 / ε) ≤ F q := by
          have := hF_q_low
          linarith
        rw [hM_unfold] at hcomb
        linarith
      have hε_inv_pos' : (0 : ℝ) < 1 / ε := hε_inv_pos
      linarith
  -- Conclude: F q' = ⨅ q, F q.
  -- (a) ⨅ ≤ F q' (use ciInf_le).
  have h_inf_le : (⨅ q : Fin d → ℝ, F q) ≤ F q' := ciInf_le hBddF q'
  -- (b) F q' ≤ ⨅ (use le_ciInf with the global-min bound).
  have h_le_inf : F q' ≤ (⨅ q : Fin d → ℝ, F q) :=
    le_ciInf h_global
  -- Antisymm gives F q' = ⨅ q, F q.
  have h_eq : F q' = ⨅ q : Fin d → ℝ, F q := le_antisymm h_le_inf h_inf_le
  -- Unfold F definitionally.
  change H x (p - q') m + (1 / ε) * K h q' = ⨅ q : Fin d → ℝ, H x (p - q) m + (1 / ε) * K h q
  exact h_eq

/-- The inf-conv minimizer, chosen via `Classical.choose` from
`qStar_exists`. Noncomputable since the minimizer is not in general
unique without strict convexity of `K`. -/
noncomputable def qStar
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m) :
    Fin d → ℝ :=
  Classical.choose (qStar_exists h hε hCont hLower)

/-- **Attainment certificate.** `qStar h hε hCont hLower` realizes the
infimum defining `Hdelta`. -/
lemma qStar_spec
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m) :
    H x (p - qStar h hε hCont hLower) m
        + (1 / ε) * K h (qStar h hε hCont hLower)
      = Hdelta h ε x p m :=
  Classical.choose_spec (qStar_exists h hε hCont hLower)

/-- Unit test: `qStar_spec` produces an attainment certificate, which
plugs into `Hdelta_lower_bound_via_minimizer`. -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m) :
    let qS := qStar h hε hCont hLower
    Hdelta h ε x p m = H x (p - qS) m + (1 / ε) * K h qS := by
  simp only
  exact (qStar_spec h hε hCont hLower).symm

/-! ### Bound on `‖q^ε‖^α` (paper line 1802)

Combining the per-minimizer lower bound on `H^ε` (line 1796) with the
`ε`-dependent upper bound (line 1784), the paper derives

  `‖q^ε‖^α ≤ C_ε ‖p‖^α + C m^β + C`  (line 1802),

which after taking the α-th root becomes `eq:q-epsilon-estimate`. We
provide the `‖q^ε‖^α` form directly — the α-th root step is unnecessary
when we feed the bound into the gradient estimate
`‖D_pH^ε‖ ≤ (1/ε)(1 + α‖q^ε‖^{α−1})` via `R^{(α−1)/α}`. -/

/-- **Paper line 1802.** Subtracting `Hdelta_lower_bound_via_minimizer`
from `Hdelta_upper_bound` and dropping the nonneg term
`‖p − q^ε‖^α / h.C` yields the `‖q^ε‖^α` bound:

  `‖q^ε‖^α ≤ (2/ε) ‖p‖^α + h.C (m^β + 1) + (1/ε + h.C)`.

The minimizer's attainment certificate `hqStar`, the per-point
weak-growth lower bound at `(x, p − q^ε, m)`, the per-point upper
bound at `(x, 0, m)`, and the `BddBelow` witness for the H family are
passed as inputs, matching the per-point pattern used elsewhere in
this file. -/
lemma qStar_alpha_norm_bound
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) (qStar : Fin d → ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m)
    (hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    ‖qStar‖ ^ h.α
      ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α
          + h.C * (m ^ h.β + 1) + (K_sup_const (d := d) h / ε + h.C) := by
  -- Combine the minimizer-based lower bound and the ε-dependent upper bound.
  have h_low :
      ‖qStar‖ ^ h.α + ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1)
        ≤ Hdelta h ε x p m :=
    Hdelta_lower_bound_via_minimizer h hε hε1 qStar hqStar hLower
  have h_up :
      Hdelta h ε x p m
        ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α
            - (m ^ h.β) / h.C + (K_sup_const (d := d) h / ε + h.C) :=
    Hdelta_upper_bound h hε hε1 hm hUpper hBdd
  -- Drop nonneg term `‖p - qStar‖^α / h.C ≥ 0`.
  have hC_pos : 0 < h.C := h.hC
  have hrα_nn : 0 ≤ ‖p - qStar‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hdiv_nn : 0 ≤ ‖p - qStar‖ ^ h.α / h.C :=
    div_nonneg hrα_nn (le_of_lt hC_pos)
  have hchain :
      ‖qStar‖ ^ h.α + ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1)
        ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α
            - (m ^ h.β) / h.C + (K_sup_const (d := d) h / ε + h.C) :=
    h_low.trans h_up
  have hmβ_nn : 0 ≤ m ^ h.β := Real.rpow_nonneg (le_of_lt hm) _
  have h_mβ_div_nn : 0 ≤ (m ^ h.β) / h.C := div_nonneg hmβ_nn (le_of_lt hC_pos)
  linarith

/-! ### Gradient upper bound on `H^ε` (paper line 1785, eq. `eq:DpHdelta.upper`)

Paper line 1808:

  `|D_pH^ε(x, p, m)| ≤ (1/ε) (1 + α |q^ε|^{α−1})`,

obtained from `eq:DpH-epsilon-formula` together with the first
inclusion of `eq:inf-conv.diff-relation1`. Substituting
`eq:q-epsilon-estimate` (equivalently, the α-th root of
`qStar_alpha_norm_bound`) yields `eq:DpHdelta.upper`.

We avoid taking the α-th root by working with
`‖q*‖^{α−1} = (‖q*‖^α)^{(α−1)/α}` via `Real.rpow_le_rpow` directly on
the `‖q*‖^α` bound. The result is a single explicit upper bound on
`‖D_pH^ε‖` whose right-hand side depends polynomially on `‖p‖^α`,
`m^β`, and `1/ε`, matching the paper. -/

/-- **Paper Proposition `prop:boundsHepsilon.b` (line 1785,
eq. `eq:DpHdelta.upper`).** Under `HypothesisWeakGrowth`, for
`0 < ε ≤ 1` and `m > 0`, the regularized Hamiltonian's gradient
admits the `ε`-dependent upper bound

  `‖D_pH^ε(x, p, m)‖ ≤ (1/ε) · (1 + h.α · R^{(h.α − 1) / h.α})`

where `R = (2/ε)·‖p‖^h.α + h.C·(m^h.β + 1) + (1/ε + h.C)` is the
upper bound on `‖q^ε‖^h.α` provided by `qStar_alpha_norm_bound`.

We expose this in `R^{(α−1)/α}` form (rather than expanded as
`‖p‖^{α−1} + m^{β-β/α} + 1`) because the latter further requires
subadditivity of `t ↦ t^r` for `0 < r ≤ 1`. The `R^{(α−1)/α}` form
captures all the paper's content; downstream users can specialize
further as needed.

The hypothesis `hDpHε_via_qStar` packages the paper formula
`|D_pH^ε(x,p,m)| ≤ (1/ε)(1 + α·|q^ε|^{α-1})` (line 1808), which the
paper derives from `eq:DpH-epsilon-formula` and the first inclusion of
`eq:inf-conv.diff-relation1`; we pass it as input pending separate
formalization of those identities (see `paper:lem:inf-conv-props.iii`). -/
lemma Hdelta_gradient_upper_bound
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) (qStar : Fin d → ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m)
    (hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m))
    (hDpHε_via_qStar :
      ‖DpHε x p m‖ ≤ (1 / ε) * (1 + h.α * (Real.sqrt d) ^ (h.α - 1)
        * ‖qStar‖ ^ (h.α - 1))) :
    ‖DpHε x p m‖
      ≤ (1 / ε) *
        (1 + h.α * (Real.sqrt d) ^ (h.α - 1) *
          ((K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α + h.C * (m ^ h.β + 1)
              + (K_sup_const (d := d) h / ε + h.C))
            ^ ((h.α - 1) / h.α)) := by
  -- The Euclidean kernel `K` carries a dimension factor `dFac := (√d)^{α−1}`
  -- on the `‖q^ε‖`-side (paper line 1808, Euclidean form).
  set dFac : ℝ := (Real.sqrt d) ^ (h.α - 1) with hdFac_def
  have hdFac_nn : 0 ≤ dFac := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  -- Step 1: `qStar_alpha_norm_bound` gives the bound on `‖qStar‖^α`.
  have h_qbnd :
      ‖qStar‖ ^ h.α
        ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α + h.C * (m ^ h.β + 1)
            + (K_sup_const (d := d) h / ε + h.C) :=
    qStar_alpha_norm_bound h hε hε1 hm qStar hqStar hLower hUpper hBdd
  -- Step 2: positivity facts.
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_nn : 0 ≤ h.α := le_of_lt hα_pos
  have hα_m1_nn : 0 ≤ h.α - 1 := by linarith [h.hα]
  have hα_m1_div_α_nn : 0 ≤ (h.α - 1) / h.α := div_nonneg hα_m1_nn hα_nn
  have hq_nn : 0 ≤ ‖qStar‖ := norm_nonneg _
  have hqα_nn : 0 ≤ ‖qStar‖ ^ h.α := Real.rpow_nonneg hq_nn _
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
  -- Step 3: `‖qStar‖^(α-1) = (‖qStar‖^α)^((α-1)/α)`.
  -- Use `Real.rpow_mul`: `‖qStar‖^(α * ((α-1)/α)) = (‖qStar‖^α)^((α-1)/α)`.
  have hα_ne : h.α ≠ 0 := ne_of_gt hα_pos
  have h_exp_eq : h.α * ((h.α - 1) / h.α) = h.α - 1 := by
    field_simp
  have h_qα_pow :
      ‖qStar‖ ^ (h.α - 1) = (‖qStar‖ ^ h.α) ^ ((h.α - 1) / h.α) := by
    have hmul : (‖qStar‖ ^ h.α) ^ ((h.α - 1) / h.α)
                  = ‖qStar‖ ^ (h.α * ((h.α - 1) / h.α)) :=
      (Real.rpow_mul hq_nn h.α ((h.α - 1) / h.α)).symm
    rw [hmul, h_exp_eq]
  -- Step 4: monotonicity of `t ↦ t^((α-1)/α)`.
  set Cd : ℝ := K_sup_const (d := d) h with hCd_def
  have hCd_nn : 0 ≤ Cd := K_sup_const_nonneg h
  set R : ℝ := (Cd / ε) * ‖p‖ ^ h.α + h.C * (m ^ h.β + 1) + (Cd / ε + h.C)
    with hRdef
  have h_qα_le_R : ‖qStar‖ ^ h.α ≤ R := h_qbnd
  have h_qpow_le :
      (‖qStar‖ ^ h.α) ^ ((h.α - 1) / h.α)
        ≤ R ^ ((h.α - 1) / h.α) :=
    Real.rpow_le_rpow hqα_nn h_qα_le_R hα_m1_div_α_nn
  rw [← h_qα_pow] at h_qpow_le
  have hαR_nn : 0 ≤ h.α * ‖qStar‖ ^ (h.α - 1) := by
    have hqp_nn : 0 ≤ ‖qStar‖ ^ (h.α - 1) := Real.rpow_nonneg hq_nn _
    exact mul_nonneg hα_nn hqp_nn
  have hαR'_nn : 0 ≤ h.α * R ^ ((h.α - 1) / h.α) := by
    have hRpow_nn : 0 ≤ R ^ ((h.α - 1) / h.α) := by
      have hC_pos : 0 < h.C := h.hC
      have hCdε_nn : 0 ≤ Cd / ε := div_nonneg hCd_nn (le_of_lt hε)
      have hpα_nn : 0 ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
      have hmβ_nn : 0 ≤ m ^ h.β := Real.rpow_nonneg (le_of_lt hm) _
      have hC_nn : 0 ≤ h.C := le_of_lt hC_pos
      have h_term1_nn : 0 ≤ (Cd / ε) * ‖p‖ ^ h.α := mul_nonneg hCdε_nn hpα_nn
      have h_term2_nn : 0 ≤ h.C * (m ^ h.β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have h_term3_nn : 0 ≤ Cd / ε + h.C := by linarith
      have hR_nn : 0 ≤ R := by
        change 0 ≤ (Cd / ε) * ‖p‖ ^ h.α + h.C * (m ^ h.β + 1) + (Cd / ε + h.C)
        linarith
      exact Real.rpow_nonneg hR_nn _
    exact mul_nonneg hα_nn hRpow_nn
  have hαdFac_nn : 0 ≤ h.α * dFac := mul_nonneg hα_nn hdFac_nn
  have h_α_mul_le :
      h.α * dFac * ‖qStar‖ ^ (h.α - 1) ≤ h.α * dFac * R ^ ((h.α - 1) / h.α) :=
    mul_le_mul_of_nonneg_left h_qpow_le hαdFac_nn
  have h_inside_le :
      1 + h.α * dFac * ‖qStar‖ ^ (h.α - 1)
        ≤ 1 + h.α * dFac * R ^ ((h.α - 1) / h.α) := by
    linarith
  have h_outer_le :
      (1 / ε) * (1 + h.α * dFac * ‖qStar‖ ^ (h.α - 1))
        ≤ (1 / ε) * (1 + h.α * dFac * R ^ ((h.α - 1) / h.α)) :=
    mul_le_mul_of_nonneg_left h_inside_le hε_inv_nn
  -- Final chain: ‖DpHε‖ ≤ (1/ε)(1 + α·dFac·‖qStar‖^(α-1))
  --                       ≤ (1/ε)(1 + α·dFac·R^((α-1)/α)).
  exact le_trans hDpHε_via_qStar h_outer_le

/-- Unit test for `qStar_alpha_norm_bound`. -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) (qStar : Fin d → ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m)
    (hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m)) :
    ‖qStar‖ ^ h.α
      ≤ (K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α
          + h.C * (m ^ h.β + 1) + (K_sup_const (d := d) h / ε + h.C) :=
  qStar_alpha_norm_bound h hε hε1 hm qStar hqStar hLower hUpper hBdd

/-- Unit test for `Hdelta_gradient_upper_bound`. -/
example (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) (qStar : Fin d → ℝ)
    (hqStar : Hdelta h ε x p m = H x (p - qStar) m + (1 / ε) * K h qStar)
    (hLower :
      ‖p - qStar‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - qStar) m)
    (hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C)
    (hBdd : BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m))
    (hDpHε_via_qStar :
      ‖DpHε x p m‖ ≤ (1 / ε) * (1 + h.α * (Real.sqrt d) ^ (h.α - 1)
        * ‖qStar‖ ^ (h.α - 1))) :
    ‖DpHε x p m‖
      ≤ (1 / ε) *
        (1 + h.α * (Real.sqrt d) ^ (h.α - 1) *
          ((K_sup_const (d := d) h / ε) * ‖p‖ ^ h.α + h.C * (m ^ h.β + 1)
              + (K_sup_const (d := d) h / ε + h.C))
            ^ ((h.α - 1) / h.α)) :=
  Hdelta_gradient_upper_bound h hε hε1 DpHε hm qStar hqStar hLower hUpper
    hBdd hDpHε_via_qStar

/-! ### Continuity of the minimizer map `q^ε` in `(p, m)`
(paper `lem:inf-conv-props`, item (i))

Paper lines 1639, 1646–1659 of `Source/FGU-monotone_revised.tex`:
under the standing hypotheses of `thm:main-weak.power.growth`, for
a.e. `x` the map `(p, m) ↦ q^ε(x, p, m)` is continuous.

The paper's proof (by contradiction; lines 1646–1659) uses the
**uniqueness** of the minimizer in its closing step. Strict convexity
of `K`, which is the standard route to that uniqueness, is documented
as blocked under `infra-P6-kernel-K-strictly-convex` (the sup-norm
blocker). We therefore package the continuity statement as a
conditional lemma `qStar_continuous_of_unique` taking the
uniqueness hypothesis as an explicit input. The downstream
strict-convexity / uniqueness task will discharge this hypothesis.

The proof is a direct transcription of the paper's contradiction
argument, with sequential continuity on the metric space
`(Fin d → ℝ) × ℝ` replacing the informal "let `(p_k, m_k) →
(p_0, m_0)`". Coercivity (from `K_ge_rpow` + `hLowerAll`) plus
continuity of the objective `F` gives boundedness, hence a convergent
subsequence; passing to the limit in the minimizer inequality and
applying uniqueness identifies the limit with `qOf (p_0, m_0)`. -/

/-- **Paper `lem:inf-conv-props` item (i), lines 1639, 1646–1659.**
Continuity of the inf-conv minimizer in `(p, m)`, conditional on a
uniqueness hypothesis.

Inputs (all per-fixed-`x`):
* `hCont3` — joint continuity of `(q, p, m) ↦ H x (p − q) m`
  (a strengthening of the per-`(p, m)` continuity used in
  `qStar_exists`),
* `hLowerAll` — the per-`x` slice of the weak-growth lower bound,
* `qOf` — a function `(Fin d → ℝ) × ℝ → Fin d → ℝ` such that
* `qOfMin` — `qOf pm` realises the infimum defining
  `Hdelta h ε x pm.1 pm.2`,
* `hUniq` — that minimiser is unique.

Conclusion: `qOf` is continuous on `(Fin d → ℝ) × ℝ`. -/
lemma qStar_continuous_of_unique
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (hCont3 : Continuous
        (fun (qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          H x (qpm.2.1 - qpm.1) qpm.2.2))
    (hLowerAll : ∀ p q : Fin d → ℝ, ∀ m : ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (qOf : (Fin d → ℝ) × ℝ → Fin d → ℝ)
    (qOfMin : ∀ pm : (Fin d → ℝ) × ℝ,
      H x (pm.1 - qOf pm) pm.2 + (1 / ε) * K h (qOf pm)
        = Hdelta h ε x pm.1 pm.2)
    (hUniq : ∀ pm : (Fin d → ℝ) × ℝ, ∀ q : Fin d → ℝ,
      H x (pm.1 - q) pm.2 + (1 / ε) * K h q = Hdelta h ε x pm.1 pm.2
        → q = qOf pm) :
    Continuous qOf := by
  classical
  -- The full objective F : (q, (p, m)) ↦ H x (p − q) m + (1/ε) K h q.
  set F : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ) → ℝ :=
    fun u => H x (u.2.1 - u.1) u.2.2 + (1 / ε) * K h u.1 with hFdef
  -- F is continuous.
  have hF_cont : Continuous F := by
    refine hCont3.add ?_
    exact continuous_const.mul ((K_continuous h).comp continuous_fst)
  -- Positivity facts.
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_ge_one : (1 : ℝ) ≤ h.α := le_of_lt h.hα
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hC_pos : 0 < h.C := h.hC
  -- F-lower: F(q, (p, m)) ≥ -C(m^β+1) + (1/ε) ‖q‖^α.
  have hF_lower :
      ∀ q p : Fin d → ℝ, ∀ m : ℝ,
        -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
          ≤ F (q, (p, m)) := by
    intro q p m
    have hLow := hLowerAll p q m
    have hpα_nn : 0 ≤ ‖p - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hK_ge : ‖q‖ ^ h.α ≤ K h q := K_ge_rpow h q
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have h_mul : (1 / ε) * ‖q‖ ^ h.α ≤ (1 / ε) * K h q :=
      mul_le_mul_of_nonneg_left hK_ge hε_inv_nn
    change -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
        ≤ H x (p - q) m + (1 / ε) * K h q
    linarith
  -- Reduce to sequential continuity: it suffices to show that for any
  -- sequence (p_k, m_k) → (p_0, m_0) we have qOf (p_k, m_k) → qOf (p_0, m_0).
  refine continuous_iff_seqContinuous.mpr ?_
  intro pmSeq pm0 hpmSeq
  -- Unpack notation.
  set q₀ : Fin d → ℝ := qOf pm0 with hq₀
  set qSeq : ℕ → Fin d → ℝ := fun k => qOf (pmSeq k) with hqSeq
  -- The minimiser inequality, repackaged in F-notation.
  have hF_cmp : ∀ k, F (qSeq k, pmSeq k) ≤ F (q₀, pmSeq k) := by
    intro k
    -- F(qSeq k, pmSeq k) = Hdelta h ε x (pmSeq k).1 (pmSeq k).2.
    have hLHS : F (qSeq k, pmSeq k) = Hdelta h ε x (pmSeq k).1 (pmSeq k).2 := by
      change H x ((pmSeq k).1 - qSeq k) (pmSeq k).2 + (1 / ε) * K h (qSeq k)
             = Hdelta h ε x (pmSeq k).1 (pmSeq k).2
      simpa [qSeq] using qOfMin (pmSeq k)
    -- BddBelow for ciInf_le.
    have hBdd_k :
        BddBelow (Set.range
          fun q : Fin d → ℝ =>
            H x ((pmSeq k).1 - q) (pmSeq k).2 + (1 / ε) * K h q) := by
      refine ⟨-(h.C * ((pmSeq k).2 ^ h.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowerAll (pmSeq k).1 q (pmSeq k).2
      have hpα_nn : 0 ≤ ‖(pmSeq k).1 - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖(pmSeq k).1 - q‖ ^ h.α / h.C :=
        div_nonneg hpα_nn (le_of_lt hC_pos)
      have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
      have hK_nn : 0 ≤ K h (q) := K_nonneg h q
      have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
      linarith
    have hRHS_ge :
        Hdelta h ε x (pmSeq k).1 (pmSeq k).2 ≤ F (q₀, pmSeq k) := by
      change Hdelta h ε x (pmSeq k).1 (pmSeq k).2
          ≤ H x ((pmSeq k).1 - q₀) (pmSeq k).2 + (1 / ε) * K h q₀
      unfold Hdelta
      exact ciInf_le hBdd_k q₀
    rw [hLHS]; exact hRHS_ge
  -- RHS converges: F(q₀, pmSeq k) → F(q₀, pm0).
  have hRHS_tend : Filter.Tendsto (fun k => F (q₀, pmSeq k)) Filter.atTop
      (𝓝 (F (q₀, pm0))) := by
    have hCont_q₀ : Continuous (fun pm : (Fin d → ℝ) × ℝ => F (q₀, pm)) :=
      hF_cont.comp (Continuous.prodMk continuous_const continuous_id)
    exact (hCont_q₀.tendsto pm0).comp hpmSeq
  -- A convergent real sequence has bounded range.
  -- Strategy: pick Mup s.t. eventually |F(q₀, pmSeq k) - F(q₀, pm0)| < 1; then
  -- on the eventually-set, |F(q₀, pmSeq k)| ≤ |F(q₀, pm0)| + 1, and on the
  -- (finite) complement we take the max.
  obtain ⟨Mup, hMup⟩ : ∃ Mup : ℝ, ∀ k, F (q₀, pmSeq k) ≤ Mup := by
    have hbdd := hRHS_tend.bddAbove_range
    rcases hbdd with ⟨Mup, hMup⟩
    refine ⟨Mup, ?_⟩
    intro k
    exact hMup ⟨k, rfl⟩
  -- Coercivity gives a uniform norm bound on qSeq.
  -- F(qSeq k, pmSeq k) ≤ F(q₀, pmSeq k) ≤ Mup, and
  -- F(qSeq k, pmSeq k) ≥ -C(m_k^β+1) + (1/ε) ‖qSeq k‖^α.
  -- Since `m_k → m₀`, the lower constant is bounded by some `Lconst`.
  -- We also need `m_k^β` bounded — use continuity of `· ^ h.β` on a
  -- neighborhood of `m₀`. Alternatively: by `Tendsto` of `pmSeq` we have
  -- `(fun k => h.C * ((pmSeq k).2 ^ h.β + 1))` convergent, hence bounded.
  have hβ_pos : 0 ≤ h.β := le_of_lt h.hβ
  -- We avoid `Real.rpow` continuity issues by noting that the LHS of the
  -- F-lower bound viewed as a function of `k` is a continuous function of
  -- `pmSeq k`, hence convergent, hence bounded.
  -- Explicitly: the sequence `n ↦ h.C * ((pmSeq n).2 ^ h.β + 1)` is bounded
  -- since `pmSeq n → pm0`. Let `Lconst` be such a bound.
  obtain ⟨Lconst, hLconst⟩ : ∃ Lconst : ℝ,
      ∀ k, h.C * ((pmSeq k).2 ^ h.β + 1) ≤ Lconst := by
    -- (pmSeq k).2 → pm0.2 in ℝ; and t ↦ t^h.β is continuous on (0,∞).
    -- Since `pm0.2` may be ≤ 0, we instead just observe: the sequence
    -- `(pmSeq k).2` is bounded (converges in ℝ), and `Real.rpow` is bounded
    -- on bounded sets. Use Bornology.IsBounded.range_of_tendsto.
    have hm_tend : Filter.Tendsto (fun k => (pmSeq k).2) Filter.atTop (𝓝 pm0.2) :=
      (continuous_snd.tendsto pm0).comp hpmSeq
    -- This implies the sequence `fun k => (pmSeq k).2 ^ h.β` is bounded
    -- only if `· ^ h.β` is continuous at `pm0.2`. To avoid that subtlety,
    -- we instead use a coarser bound on `(pmSeq k).2 ^ h.β`. But this is
    -- hard without continuity. Easier path: bound directly.
    -- Approach: pick a closed ball around `pm0.2` containing all but
    -- finitely many `(pmSeq k).2`; bound `t ^ h.β` on a closed interval.
    -- For simplicity, we instead bound directly: since `F(q₀, pmSeq k) ≤ Mup`
    -- and `F(q₀, pmSeq k) = H x (pmSeq k.1 - q₀) (pmSeq k.2) + (1/ε) K h q₀`,
    -- and `H` is continuous (`hCont3`), the sequence
    -- `H x (pmSeq k.1 - q₀) (pmSeq k.2)` converges, hence is bounded.
    -- We don't actually need to bound `m^β` separately; the cleaner approach
    -- is to bound `F (qSeq k, pmSeq k)` from below by ANY constant. We use
    -- the fact that `F (qSeq k, pmSeq k) ≥ H x (...) (...) + 0` and that
    -- H restricted to a compact set in (p, m) (via convergence of pmSeq) is
    -- bounded. Better: use `BddBelow` from `hLowerAll` applied directly to
    -- the COMPACT set traced out by pmSeq.
    -- Easiest concrete approach: the sequence `k ↦ (pmSeq k).2 ^ h.β` is
    -- bounded because `Real.rpow` is continuous on `ℝ × {h.β}`. But that
    -- requires the base ≥ 0. We split: if `(pmSeq k).2 ≥ 0`, then
    -- `(pmSeq k).2 ^ h.β = Real.rpow ...` is continuous; else use the
    -- convention `Real.rpow_def_of_neg`. We sidestep this entirely.
    -- ACTUAL SIMPLE APPROACH: We use a different lower bound for F that
    -- does not depend on `m^β`. From `F (qSeq k, pmSeq k) = Hdelta...`
    -- and Hdelta `≤ F(0, pmSeq k)` (testing q = 0 in the infimum), we get
    -- `F (qSeq k, pmSeq k) ≤ F(0, pmSeq k) = H x (pmSeq k.1) (pmSeq k.2) +
    -- (1/ε) K h 0 = H x (pmSeq k.1) (pmSeq k.2) + 0`.
    -- The RHS is continuous in pmSeq k and so bounded.
    -- BUT we need a LOWER bound for F. The cleanest lower bound is via K:
    -- `F (qSeq k, pmSeq k) ≥ (1/ε) K h (qSeq k) + L_H` where L_H is a
    -- (joint) lower bound on H. But hCont3 alone doesn't give that.
    -- Tactical compromise: we use hLowerAll, but bound m^β via a max over a
    -- closed interval containing the sequence and pm0.2. Concretely:
    -- since pmSeq → pm0, the sequence `(pmSeq k).2` lives in a closed
    -- bounded interval [pm0.2 - 1, pm0.2 + 1] except for finitely many k.
    -- On that compact interval, `t ↦ Real.rpow t h.β` is continuous (it's
    -- the function we're worried about); for `t < 0` we use the convention.
    -- Implementation: invoke `Continuous.bddAbove_range` on `(pmSeq k).2 ^ h.β`.
    -- The function `t ↦ t ^ h.β` is continuous on ℝ in Mathlib as
    -- `Real.continuous_rpow_const` (provided h.β ≥ 0; we have h.β > 0).
    have hrpow_cont : Continuous (fun t : ℝ => t ^ h.β) :=
      Real.continuous_rpow_const hβ_pos
    have htβ_tend : Filter.Tendsto (fun k => (pmSeq k).2 ^ h.β) Filter.atTop
        (𝓝 (pm0.2 ^ h.β)) := (hrpow_cont.tendsto _).comp hm_tend
    have hbdd_mβ := htβ_tend.bddAbove_range
    rcases hbdd_mβ with ⟨Mβ, hMβ⟩
    refine ⟨h.C * (Mβ + 1), ?_⟩
    intro k
    have hmβk_le : (pmSeq k).2 ^ h.β ≤ Mβ := hMβ ⟨k, rfl⟩
    have hC_nn : 0 ≤ h.C := le_of_lt hC_pos
    nlinarith [hC_nn, hmβk_le]
  -- Combine: (1/ε) ‖qSeq k‖^α ≤ Mup + Lconst.
  -- F (qSeq k, pmSeq k) ≤ Mup; F (qSeq k, pmSeq k) ≥ -Lconst + (1/ε)‖qSeq k‖^α.
  have hqα_bnd : ∀ k, (1 / ε) * ‖qSeq k‖ ^ h.α ≤ Mup + Lconst := by
    intro k
    have hcmp := hF_cmp k
    have hRHS_le_Mup : F (q₀, pmSeq k) ≤ Mup := hMup k
    have hLHS_le_Mup : F (qSeq k, pmSeq k) ≤ Mup := le_trans hcmp hRHS_le_Mup
    have hLowF := hF_lower (qSeq k) (pmSeq k).1 (pmSeq k).2
    -- F(qSeq k, pmSeq k) = ... but the F-lower uses the unsplit form. We
    -- align by `Prod.mk` of `(pmSeq k).1, (pmSeq k).2`.
    have heq : F (qSeq k, (pmSeq k).1, (pmSeq k).2) = F (qSeq k, pmSeq k) := by
      congr 1
    rw [heq] at hLowF
    have hLconst_k : h.C * ((pmSeq k).2 ^ h.β + 1) ≤ Lconst := hLconst k
    linarith
  -- Hence ‖qSeq k‖^α ≤ ε * (Mup + Lconst), and so ‖qSeq k‖ ≤ R for some R.
  set Mqα : ℝ := ε * (Mup + Lconst) with hMqα
  have hqα_bnd' : ∀ k, ‖qSeq k‖ ^ h.α ≤ Mqα := by
    intro k
    have := hqα_bnd k
    have hε_inv_ne : (1 / ε) ≠ 0 := ne_of_gt hε_inv_pos
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    -- (1/ε) * x ≤ Mup + Lconst  ⇒  x ≤ ε * (Mup + Lconst)
    have hx_eq : (1 / ε) * ‖qSeq k‖ ^ h.α = ‖qSeq k‖ ^ h.α / ε := by
      field_simp
    rw [hx_eq] at this
    -- ‖qSeq k‖^α / ε ≤ Mup + Lconst  ⇒  ‖qSeq k‖^α ≤ ε * (Mup + Lconst)
    have := (div_le_iff₀ hε).mp this
    -- `this : ‖qSeq k‖ ^ h.α ≤ (Mup + Lconst) * ε`; Mqα = ε * (Mup + Lconst).
    rw [hMqα]; linarith
  -- Choose R = max 1 (Mqα^(1/α)). We want ‖qSeq k‖ ≤ R for all k.
  -- Bypass rpow gymnastics: pick R = max 1 (Mqα + 1) and show
  -- ‖qSeq k‖ ≤ R using ‖q‖ ≤ max 1 ‖q‖^α + 1 (a trivial slack bound).
  -- Trick: since α ≥ 1, t ≥ 0 ⇒ t ≤ t^α + 1 (when t ≥ 1, t ≤ t^α; when
  -- t ≤ 1, t ≤ 1 ≤ t^α + 1).
  have hnorm_le_rpow_plus_one : ∀ t : ℝ, 0 ≤ t → t ≤ t ^ h.α + 1 := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · -- t ≤ 1, t^α ≥ 0, so t ≤ 1 ≤ t^α + 1.
      have : 0 ≤ t ^ h.α := Real.rpow_nonneg ht _
      linarith
    · -- t > 1, so t^α ≥ t^1 = t.
      have ht1' : 1 < t := lt_of_not_ge ht1
      have ht_ge_one : (1 : ℝ) ≤ t := le_of_lt ht1'
      have h_rpow_one : t ^ (1 : ℝ) = t := Real.rpow_one _
      have hmono : t ^ (1 : ℝ) ≤ t ^ h.α :=
        Real.rpow_le_rpow_of_exponent_le ht_ge_one hα_ge_one
      rw [h_rpow_one] at hmono
      linarith
  have hqSeq_norm_bnd : ∀ k, ‖qSeq k‖ ≤ Mqα + 1 := by
    intro k
    have hnn : 0 ≤ ‖qSeq k‖ := norm_nonneg _
    have h1 := hnorm_le_rpow_plus_one (‖qSeq k‖) hnn
    have h2 := hqα_bnd' k
    linarith
  -- The qSeq lives in the closed ball B(0, Mqα + 1), which is compact.
  set R : ℝ := Mqα + 1 with hRdef
  set B : Set (Fin d → ℝ) := Metric.closedBall 0 R with hBdef
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hqSeq_in_B : ∀ k, qSeq k ∈ B := by
    intro k
    rw [hBdef, Metric.mem_closedBall, dist_zero_right]
    exact hqSeq_norm_bnd k
  -- BddBelow at pm0 for use below.
  have hBdd0 :
      BddBelow (Set.range
        fun q : Fin d → ℝ =>
          H x (pm0.1 - q) pm0.2 + (1 / ε) * K h q) := by
    refine ⟨-(h.C * (pm0.2 ^ h.β + 1)), ?_⟩
    rintro y ⟨q, rfl⟩
    have hLow := hLowerAll pm0.1 q pm0.2
    have hpα_nn : 0 ≤ ‖pm0.1 - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖pm0.1 - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have hK_nn : 0 ≤ K h (q) := K_nonneg h q
    have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
    linarith
  -- F(q₀, pm0) = Hdelta h ε x pm0.1 pm0.2.
  have hF_q₀_eq :
      F (q₀, pm0) = Hdelta h ε x pm0.1 pm0.2 := by
    change H x (pm0.1 - q₀) pm0.2 + (1 / ε) * K h q₀
         = Hdelta h ε x pm0.1 pm0.2
    simpa [q₀] using qOfMin pm0
  -- Strategy via `tendsto_of_subseq_tendsto`: every subsequence
  -- `ns : ℕ → ℕ` (with `Tendsto ns atTop atTop`) has a further
  -- subsequence `ms : ℕ → ℕ` making `qSeq ∘ ns ∘ ms` converge to q₀.
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
  -- (qSeq ∘ ns) is in B; extract a further convergent subsequence.
  have hcomp_in_B : ∀ k, (qSeq ∘ ns) k ∈ B := fun k => hqSeq_in_B (ns k)
  obtain ⟨q_star, hq_star_B, ψ, hψ_mono, hsubseq_tend⟩ :=
    hB_compact.tendsto_subseq hcomp_in_B
  -- Now `(qSeq ∘ ns) ∘ ψ → q_star`. We will show q_star = q₀.
  -- pmSeq ∘ (ns ∘ ψ) → pm0 (since pmSeq → pm0 and ns ∘ ψ → ∞).
  have hψ_tendsto : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
    hψ_mono.tendsto_atTop
  have hns_psi_tendsto : Filter.Tendsto (fun k => ns (ψ k)) Filter.atTop Filter.atTop :=
    hns.comp hψ_tendsto
  have hpmSeq_subseq :
      Filter.Tendsto (fun k => pmSeq (ns (ψ k))) Filter.atTop (𝓝 pm0) :=
    hpmSeq.comp hns_psi_tendsto
  -- LHS = F(qSeq ∘ ns ∘ ψ, pmSeq ∘ ns ∘ ψ) → F(q_star, pm0).
  have hF_lhs_tend :
      Filter.Tendsto
        (fun k => F (qSeq (ns (ψ k)), pmSeq (ns (ψ k)))) Filter.atTop
        (𝓝 (F (q_star, pm0))) := by
    have hpair_tend :
        Filter.Tendsto
          (fun k => (qSeq (ns (ψ k)), pmSeq (ns (ψ k)))) Filter.atTop
          (𝓝 (q_star, pm0)) :=
      Filter.Tendsto.prodMk_nhds hsubseq_tend hpmSeq_subseq
    exact (hF_cont.tendsto _).comp hpair_tend
  -- RHS = F(q₀, pmSeq ∘ ns ∘ ψ) → F(q₀, pm0).
  have hF_rhs_tend :
      Filter.Tendsto (fun k => F (q₀, pmSeq (ns (ψ k)))) Filter.atTop
        (𝓝 (F (q₀, pm0))) := by
    have hCont_q₀ : Continuous (fun pm : (Fin d → ℝ) × ℝ => F (q₀, pm)) :=
      hF_cont.comp (Continuous.prodMk continuous_const continuous_id)
    exact (hCont_q₀.tendsto pm0).comp hpmSeq_subseq
  -- Pass to limit in hF_cmp.
  have hLim_le :
      F (q_star, pm0) ≤ F (q₀, pm0) := by
    refine le_of_tendsto_of_tendsto hF_lhs_tend hF_rhs_tend ?_
    refine Filter.Eventually.of_forall (fun k => ?_)
    exact hF_cmp (ns (ψ k))
  -- F(q_star, pm0) ≥ Hdelta (the inf).
  have hF_qstar_ge :
      Hdelta h ε x pm0.1 pm0.2 ≤ F (q_star, pm0) := by
    change Hdelta h ε x pm0.1 pm0.2
        ≤ H x (pm0.1 - q_star) pm0.2 + (1 / ε) * K h q_star
    unfold Hdelta
    exact ciInf_le hBdd0 q_star
  -- F(q_star, pm0) = Hdelta h ε x pm0.1 pm0.2.
  have hF_qstar_eq : F (q_star, pm0) = Hdelta h ε x pm0.1 pm0.2 := by
    have h1 : F (q_star, pm0) ≤ Hdelta h ε x pm0.1 pm0.2 := by
      rw [← hF_q₀_eq]; exact hLim_le
    exact le_antisymm h1 hF_qstar_ge
  -- Apply uniqueness: q_star = qOf pm0 = q₀.
  have hq_star_eq_q₀ : q_star = q₀ := by
    have huniq := hUniq pm0 q_star
    have hF_unfold : H x (pm0.1 - q_star) pm0.2 + (1 / ε) * K h q_star
        = Hdelta h ε x pm0.1 pm0.2 := hF_qstar_eq
    exact huniq hF_unfold
  -- Produce the subsequence `ψ` and the convergence to q₀.
  refine ⟨ψ, ?_⟩
  rw [hq_star_eq_q₀] at hsubseq_tend
  -- hsubseq_tend : Tendsto ((qSeq ∘ ns) ∘ ψ) atTop (𝓝 q₀).
  exact hsubseq_tend

/-- **`{0<m}` variant of `qStar_continuous_of_unique`.**
Continuity of the inf-conv minimizer `qOf` *on the positive-`m` region*
`{pm | 0 < pm.2}`, from `{0<m}`-restricted riders.

This is the form that the regularity bundle actually needs (paper
`prop:boundsHepsilon`: continuity of `H^ε` on `ℝ^d × ℝ⁺`) and the form
that the paper-faithful data (`convexOn_H_p`, `hasFDerivAt_H_p`,
`HypothesisWeakGrowth.lower`) can deliver — all of which hold only for
`m > 0`.

Inputs (all per-fixed-`x`):
* `hCont3` — joint continuity of `(q, p, m) ↦ H x (p − q) m` (global; this
  is downstream of `RegularityH.continuous_H_pm` restricted to `{m>0}`,
  but as a function of `(q,p,m)` it is continuous wherever `m>0`; we take
  it as the global continuity input since the consumer only ever evaluates
  at `m>0`),
* `hLowerAll` — the per-`x` weak-growth lower bound, for `0 < m`,
* `qOfMin`/`hUniq` — minimiser realisation / uniqueness, for `0 < m`.

Conclusion: `ContinuousOn qOf {pm | 0 < pm.2}`.

The proof reduces (via openness of `{m>0}` and
`Filter.tendsto_iff_seq_tendsto` on the countably-generated filter
`𝓝[{m>0}] pm0`) to: for every sequence `pmSeq → pm0` eventually in
`{m>0}` with `pm0 ∈ {m>0}`, `qOf (pmSeq k) → qOf pm0`. Passing to a tail
where all terms satisfy `0 < (pmSeq k).2`, the contradiction argument of
`qStar_continuous_of_unique` goes through verbatim, now invoking the
riders only at the positive-`m` points it visits. -/
lemma qStar_continuousOn_pos_of_unique
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (hCont3 : Continuous
        (fun (qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          H x (qpm.2.1 - qpm.1) qpm.2.2))
    (hLowerAll : ∀ p q : Fin d → ℝ, ∀ m : ℝ, 0 < m →
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (qOf : (Fin d → ℝ) × ℝ → Fin d → ℝ)
    (qOfMin : ∀ pm : (Fin d → ℝ) × ℝ, 0 < pm.2 →
      H x (pm.1 - qOf pm) pm.2 + (1 / ε) * K h (qOf pm)
        = Hdelta h ε x pm.1 pm.2)
    (hUniq : ∀ pm : (Fin d → ℝ) × ℝ, 0 < pm.2 → ∀ q : Fin d → ℝ,
      H x (pm.1 - q) pm.2 + (1 / ε) * K h q = Hdelta h ε x pm.1 pm.2
        → q = qOf pm) :
    ContinuousOn qOf {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
  classical
  set S : Set ((Fin d → ℝ) × ℝ) := {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} with hSdef
  -- `S` is open.
  have hS_open : IsOpen S := by
    have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
    exact this.preimage continuous_snd
  -- The full objective `F : (q, (p, m)) ↦ H x (p − q) m + (1/ε) K h q`.
  set F : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ) → ℝ :=
    fun u => H x (u.2.1 - u.1) u.2.2 + (1 / ε) * K h u.1 with hFdef
  have hF_cont : Continuous F := by
    refine hCont3.add ?_
    exact continuous_const.mul ((K_continuous h).comp continuous_fst)
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_ge_one : (1 : ℝ) ≤ h.α := le_of_lt h.hα
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 ≤ h.β := le_of_lt h.hβ
  -- Reduce to `ContinuousWithinAt` at each `pm0 ∈ S`, then to a tendsto
  -- statement on the (countably generated) within-filter `𝓝[S] pm0`.
  intro pm0 hpm0
  -- Membership: `0 < pm0.2`.
  have hm0_pos : (0 : ℝ) < pm0.2 := hpm0
  -- It suffices to show `Tendsto qOf (𝓝[S] pm0) (𝓝 (qOf pm0))`.
  rw [ContinuousWithinAt]
  -- Sequential criterion on the countably generated filter `𝓝[S] pm0`.
  rw [Filter.tendsto_iff_seq_tendsto]
  intro pmSeq hpmSeq_within
  -- Decompose into convergence + eventual membership.
  rw [tendsto_nhdsWithin_iff] at hpmSeq_within
  obtain ⟨hpmSeq, hpmSeq_mem⟩ := hpmSeq_within
  -- Pass to a tail where all terms are in `S`.
  rw [Filter.eventually_atTop] at hpmSeq_mem
  obtain ⟨N, hN⟩ := hpmSeq_mem
  -- It suffices to prove convergence of the shifted (tail) sequence.
  -- `qOf ∘ pmSeq` and its tail share a tail, so they have the same limit.
  rw [show ((fun pm => qOf pm) ∘ pmSeq) = (fun k => qOf (pmSeq k)) from rfl]
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun k => qOf (pmSeq k)) N]
  -- Goal: `Tendsto (fun k => qOf (pmSeq (k + N))) atTop (𝓝 (qOf pm0))`.
  -- Now work with the tail sequence; all its terms are in `S`.
  set qSeq : ℕ → Fin d → ℝ := fun k => qOf (pmSeq (k + N)) with hqSeq
  set pmS : ℕ → (Fin d → ℝ) × ℝ := fun k => pmSeq (k + N) with hpmS
  have hpmS_pos : ∀ k, 0 < (pmS k).2 := fun k => hN (k + N) (Nat.le_add_left N k)
  have hpmS_tend : Filter.Tendsto pmS Filter.atTop (𝓝 pm0) :=
    hpmSeq.comp (Filter.tendsto_add_atTop_nat N)
  set q₀ : Fin d → ℝ := qOf pm0 with hq₀
  -- The minimiser inequality, repackaged in F-notation (at positive-`m` points).
  have hF_cmp : ∀ k, F (qSeq k, pmS k) ≤ F (q₀, pmS k) := by
    intro k
    have hLHS : F (qSeq k, pmS k) = Hdelta h ε x (pmS k).1 (pmS k).2 := by
      change H x ((pmS k).1 - qSeq k) (pmS k).2 + (1 / ε) * K h (qSeq k)
             = Hdelta h ε x (pmS k).1 (pmS k).2
      simpa [qSeq, hpmS] using qOfMin (pmS k) (hpmS_pos k)
    have hBdd_k :
        BddBelow (Set.range
          fun q : Fin d → ℝ =>
            H x ((pmS k).1 - q) (pmS k).2 + (1 / ε) * K h q) := by
      refine ⟨-(h.C * ((pmS k).2 ^ h.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowerAll (pmS k).1 q (pmS k).2 (hpmS_pos k)
      have hpα_nn : 0 ≤ ‖(pmS k).1 - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖(pmS k).1 - q‖ ^ h.α / h.C :=
        div_nonneg hpα_nn (le_of_lt hC_pos)
      have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
      have hK_nn : 0 ≤ K h (q) := K_nonneg h q
      have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
      linarith
    have hRHS_ge :
        Hdelta h ε x (pmS k).1 (pmS k).2 ≤ F (q₀, pmS k) := by
      change Hdelta h ε x (pmS k).1 (pmS k).2
          ≤ H x ((pmS k).1 - q₀) (pmS k).2 + (1 / ε) * K h q₀
      unfold Hdelta
      exact ciInf_le hBdd_k q₀
    rw [hLHS]; exact hRHS_ge
  -- RHS converges.
  have hRHS_tend : Filter.Tendsto (fun k => F (q₀, pmS k)) Filter.atTop
      (𝓝 (F (q₀, pm0))) := by
    have hCont_q₀ : Continuous (fun pm : (Fin d → ℝ) × ℝ => F (q₀, pm)) :=
      hF_cont.comp (Continuous.prodMk continuous_const continuous_id)
    exact (hCont_q₀.tendsto pm0).comp hpmS_tend
  -- Upper bound on RHS values.
  obtain ⟨Mup, hMup⟩ : ∃ Mup : ℝ, ∀ k, F (q₀, pmS k) ≤ Mup := by
    have hbdd := hRHS_tend.bddAbove_range
    rcases hbdd with ⟨Mup, hMup⟩
    exact ⟨Mup, fun k => hMup ⟨k, rfl⟩⟩
  -- Bound on the `m^β` term.
  obtain ⟨Lconst, hLconst⟩ : ∃ Lconst : ℝ,
      ∀ k, h.C * ((pmS k).2 ^ h.β + 1) ≤ Lconst := by
    have hm_tend : Filter.Tendsto (fun k => (pmS k).2) Filter.atTop (𝓝 pm0.2) :=
      (continuous_snd.tendsto pm0).comp hpmS_tend
    have hrpow_cont : Continuous (fun t : ℝ => t ^ h.β) :=
      Real.continuous_rpow_const hβ_pos
    have htβ_tend : Filter.Tendsto (fun k => (pmS k).2 ^ h.β) Filter.atTop
        (𝓝 (pm0.2 ^ h.β)) := (hrpow_cont.tendsto _).comp hm_tend
    have hbdd_mβ := htβ_tend.bddAbove_range
    rcases hbdd_mβ with ⟨Mβ, hMβ⟩
    refine ⟨h.C * (Mβ + 1), ?_⟩
    intro k
    have hmβk_le : (pmS k).2 ^ h.β ≤ Mβ := hMβ ⟨k, rfl⟩
    have hC_nn : 0 ≤ h.C := le_of_lt hC_pos
    nlinarith [hC_nn, hmβk_le]
  -- F-lower bound.
  have hF_lower :
      ∀ q p : Fin d → ℝ, ∀ m : ℝ, 0 < m →
        -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
          ≤ F (q, (p, m)) := by
    intro q p m hm
    have hLow := hLowerAll p q m hm
    have hpα_nn : 0 ≤ ‖p - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hK_ge : ‖q‖ ^ h.α ≤ K h q := K_ge_rpow h q
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have h_mul : (1 / ε) * ‖q‖ ^ h.α ≤ (1 / ε) * K h q :=
      mul_le_mul_of_nonneg_left hK_ge hε_inv_nn
    change -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
        ≤ H x (p - q) m + (1 / ε) * K h q
    linarith
  -- Uniform `α`-norm bound on qSeq.
  have hqα_bnd : ∀ k, (1 / ε) * ‖qSeq k‖ ^ h.α ≤ Mup + Lconst := by
    intro k
    have hcmp := hF_cmp k
    have hRHS_le_Mup : F (q₀, pmS k) ≤ Mup := hMup k
    have hLHS_le_Mup : F (qSeq k, pmS k) ≤ Mup := le_trans hcmp hRHS_le_Mup
    have hLowF := hF_lower (qSeq k) (pmS k).1 (pmS k).2 (hpmS_pos k)
    have heq : F (qSeq k, (pmS k).1, (pmS k).2) = F (qSeq k, pmS k) := by
      congr 1
    rw [heq] at hLowF
    have hLconst_k : h.C * ((pmS k).2 ^ h.β + 1) ≤ Lconst := hLconst k
    linarith
  set Mqα : ℝ := ε * (Mup + Lconst) with hMqα
  have hqα_bnd' : ∀ k, ‖qSeq k‖ ^ h.α ≤ Mqα := by
    intro k
    have := hqα_bnd k
    have hx_eq : (1 / ε) * ‖qSeq k‖ ^ h.α = ‖qSeq k‖ ^ h.α / ε := by field_simp
    rw [hx_eq] at this
    have := (div_le_iff₀ hε).mp this
    rw [hMqα]; linarith
  have hnorm_le_rpow_plus_one : ∀ t : ℝ, 0 ≤ t → t ≤ t ^ h.α + 1 := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have : 0 ≤ t ^ h.α := Real.rpow_nonneg ht _
      linarith
    · have ht1' : 1 < t := lt_of_not_ge ht1
      have ht_ge_one : (1 : ℝ) ≤ t := le_of_lt ht1'
      have h_rpow_one : t ^ (1 : ℝ) = t := Real.rpow_one _
      have hmono : t ^ (1 : ℝ) ≤ t ^ h.α :=
        Real.rpow_le_rpow_of_exponent_le ht_ge_one hα_ge_one
      rw [h_rpow_one] at hmono
      linarith
  have hqSeq_norm_bnd : ∀ k, ‖qSeq k‖ ≤ Mqα + 1 := by
    intro k
    have hnn : 0 ≤ ‖qSeq k‖ := norm_nonneg _
    have h1 := hnorm_le_rpow_plus_one (‖qSeq k‖) hnn
    have h2 := hqα_bnd' k
    linarith
  set R : ℝ := Mqα + 1 with hRdef
  set B : Set (Fin d → ℝ) := Metric.closedBall 0 R with hBdef
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hqSeq_in_B : ∀ k, qSeq k ∈ B := by
    intro k
    rw [hBdef, Metric.mem_closedBall, dist_zero_right]
    exact hqSeq_norm_bnd k
  -- BddBelow at pm0 (positive `m`).
  have hBdd0 :
      BddBelow (Set.range
        fun q : Fin d → ℝ =>
          H x (pm0.1 - q) pm0.2 + (1 / ε) * K h q) := by
    refine ⟨-(h.C * (pm0.2 ^ h.β + 1)), ?_⟩
    rintro y ⟨q, rfl⟩
    have hLow := hLowerAll pm0.1 q pm0.2 hm0_pos
    have hpα_nn : 0 ≤ ‖pm0.1 - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖pm0.1 - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have hK_nn : 0 ≤ K h (q) := K_nonneg h q
    have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
    linarith
  have hF_q₀_eq : F (q₀, pm0) = Hdelta h ε x pm0.1 pm0.2 := by
    change H x (pm0.1 - q₀) pm0.2 + (1 / ε) * K h q₀
         = Hdelta h ε x pm0.1 pm0.2
    simpa [q₀] using qOfMin pm0 hm0_pos
  -- Subsequence argument.
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hcomp_in_B : ∀ k, (qSeq ∘ ns) k ∈ B := fun k => hqSeq_in_B (ns k)
  obtain ⟨q_star, hq_star_B, ψ, hψ_mono, hsubseq_tend⟩ :=
    hB_compact.tendsto_subseq hcomp_in_B
  have hψ_tendsto : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
    hψ_mono.tendsto_atTop
  have hns_psi_tendsto :
      Filter.Tendsto (fun k => ns (ψ k)) Filter.atTop Filter.atTop :=
    hns.comp hψ_tendsto
  have hpmS_subseq :
      Filter.Tendsto (fun k => pmS (ns (ψ k))) Filter.atTop (𝓝 pm0) :=
    hpmS_tend.comp hns_psi_tendsto
  have hF_lhs_tend :
      Filter.Tendsto
        (fun k => F (qSeq (ns (ψ k)), pmS (ns (ψ k)))) Filter.atTop
        (𝓝 (F (q_star, pm0))) := by
    have hpair_tend :
        Filter.Tendsto
          (fun k => (qSeq (ns (ψ k)), pmS (ns (ψ k)))) Filter.atTop
          (𝓝 (q_star, pm0)) :=
      Filter.Tendsto.prodMk_nhds hsubseq_tend hpmS_subseq
    exact (hF_cont.tendsto _).comp hpair_tend
  have hF_rhs_tend :
      Filter.Tendsto (fun k => F (q₀, pmS (ns (ψ k)))) Filter.atTop
        (𝓝 (F (q₀, pm0))) := by
    have hCont_q₀ : Continuous (fun pm : (Fin d → ℝ) × ℝ => F (q₀, pm)) :=
      hF_cont.comp (Continuous.prodMk continuous_const continuous_id)
    exact (hCont_q₀.tendsto pm0).comp hpmS_subseq
  have hLim_le : F (q_star, pm0) ≤ F (q₀, pm0) := by
    refine le_of_tendsto_of_tendsto hF_lhs_tend hF_rhs_tend ?_
    refine Filter.Eventually.of_forall (fun k => ?_)
    exact hF_cmp (ns (ψ k))
  have hF_qstar_ge : Hdelta h ε x pm0.1 pm0.2 ≤ F (q_star, pm0) := by
    change Hdelta h ε x pm0.1 pm0.2
        ≤ H x (pm0.1 - q_star) pm0.2 + (1 / ε) * K h q_star
    unfold Hdelta
    exact ciInf_le hBdd0 q_star
  have hF_qstar_eq : F (q_star, pm0) = Hdelta h ε x pm0.1 pm0.2 := by
    have h1 : F (q_star, pm0) ≤ Hdelta h ε x pm0.1 pm0.2 := by
      rw [← hF_q₀_eq]; exact hLim_le
    exact le_antisymm h1 hF_qstar_ge
  have hq_star_eq_q₀ : q_star = q₀ := by
    have huniq := hUniq pm0 hm0_pos q_star
    have hF_unfold : H x (pm0.1 - q_star) pm0.2 + (1 / ε) * K h q_star
        = Hdelta h ε x pm0.1 pm0.2 := hF_qstar_eq
    exact huniq hF_unfold
  refine ⟨ψ, ?_⟩
  rw [hq_star_eq_q₀] at hsubseq_tend
  exact hsubseq_tend

/-- **Slice-continuity variant of `qStar_continuousOn_pos_of_unique`.**
Identical conclusion `ContinuousOn qOf {pm | 0 < pm.2}`, but the continuity
input is the `{m>0}`-restricted form

  `ContinuousOn (fun qpm => H x (qpm.2.1 − qpm.1) qpm.2.2) {qpm | 0 < qpm.2.2}`,

NOT global joint continuity in `(q,p,m)`. This is exactly what
`RegularityH.continuous_H_pm` supplies (continuity of `H(x,·,·)` only on the
positive-mass slice `{0 < m}`), composed with the continuous coordinate map
`(q,p,m) ↦ (p−q, m)`.

The proof mirrors `qStar_continuousOn_pos_of_unique` verbatim; the only
difference is that the objective `F : (q,(p,m)) ↦ H x (p−q) m + (1/ε) K h q`
is now only `ContinuousOn` the open set `T := {u | 0 < u.2.2}`. Since `T` is
open and *every* point at which `F` is evaluated in a limit (the limit point
`pm0`, all sequence tails `pmS k`, the limit `q_star`) has positive
`m`-coordinate, we recover `ContinuousAt F u` at each such `u ∈ T` and the
argument goes through unchanged. -/
lemma qStar_continuousOn_pos_of_unique_slice
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (hCont3 : ContinuousOn
        (fun (qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
          H x (qpm.2.1 - qpm.1) qpm.2.2)
        {qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < qpm.2.2})
    (hLowerAll : ∀ p q : Fin d → ℝ, ∀ m : ℝ, 0 < m →
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (qOf : (Fin d → ℝ) × ℝ → Fin d → ℝ)
    (qOfMin : ∀ pm : (Fin d → ℝ) × ℝ, 0 < pm.2 →
      H x (pm.1 - qOf pm) pm.2 + (1 / ε) * K h (qOf pm)
        = Hdelta h ε x pm.1 pm.2)
    (hUniq : ∀ pm : (Fin d → ℝ) × ℝ, 0 < pm.2 → ∀ q : Fin d → ℝ,
      H x (pm.1 - q) pm.2 + (1 / ε) * K h q = Hdelta h ε x pm.1 pm.2
        → q = qOf pm) :
    ContinuousOn qOf {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
  classical
  set S : Set ((Fin d → ℝ) × ℝ) := {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} with hSdef
  have hS_open : IsOpen S := by
    have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
    exact this.preimage continuous_snd
  -- The open "positive-mass" set in the `(q,(p,m))` space.
  set T : Set ((Fin d → ℝ) × ((Fin d → ℝ) × ℝ)) :=
    {u : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ) | 0 < u.2.2} with hTdef
  have hT_open : IsOpen T := by
    have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
    exact this.preimage (continuous_snd.comp continuous_snd)
  -- The full objective `F`.
  set F : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ) → ℝ :=
    fun u => H x (u.2.1 - u.1) u.2.2 + (1 / ε) * K h u.1 with hFdef
  -- `F` is continuous on `T` (the kernel term is globally continuous; the
  -- `H` term is the `hCont3` slice precomposed with the continuous projection
  -- `u ↦ (u.1, u.2.1, u.2.2)`).
  have hF_contOn : ContinuousOn F T := by
    refine ContinuousOn.add ?_ ?_
    · -- `u ↦ H x (u.2.1 - u.1) u.2.2`.
      have hmap : ContinuousOn
          (fun u : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ) =>
            ((u.1, u.2.1, u.2.2) : (Fin d → ℝ) × (Fin d → ℝ) × ℝ))
          T := by
        fun_prop
      have hmaps : Set.MapsTo
          (fun u : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ) =>
            ((u.1, u.2.1, u.2.2) : (Fin d → ℝ) × (Fin d → ℝ) × ℝ))
          T {qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < qpm.2.2} := by
        intro u hu; exact hu
      have hcomp := hCont3.comp hmap hmaps
      exact hcomp
    · exact (continuous_const.mul ((K_continuous h).comp continuous_fst)).continuousOn
  -- Upgrade to `ContinuousAt` at any point of the open set `T`.
  have hF_contAt : ∀ u : (Fin d → ℝ) × ((Fin d → ℝ) × ℝ), u ∈ T →
      ContinuousAt F u := fun u hu =>
    (hF_contOn u hu).continuousAt (hT_open.mem_nhds hu)
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_ge_one : (1 : ℝ) ≤ h.α := le_of_lt h.hα
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 ≤ h.β := le_of_lt h.hβ
  intro pm0 hpm0
  have hm0_pos : (0 : ℝ) < pm0.2 := hpm0
  rw [ContinuousWithinAt]
  rw [Filter.tendsto_iff_seq_tendsto]
  intro pmSeq hpmSeq_within
  rw [tendsto_nhdsWithin_iff] at hpmSeq_within
  obtain ⟨hpmSeq, hpmSeq_mem⟩ := hpmSeq_within
  rw [Filter.eventually_atTop] at hpmSeq_mem
  obtain ⟨N, hN⟩ := hpmSeq_mem
  rw [show ((fun pm => qOf pm) ∘ pmSeq) = (fun k => qOf (pmSeq k)) from rfl]
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun k => qOf (pmSeq k)) N]
  set qSeq : ℕ → Fin d → ℝ := fun k => qOf (pmSeq (k + N)) with hqSeq
  set pmS : ℕ → (Fin d → ℝ) × ℝ := fun k => pmSeq (k + N) with hpmS
  have hpmS_pos : ∀ k, 0 < (pmS k).2 := fun k => hN (k + N) (Nat.le_add_left N k)
  have hpmS_tend : Filter.Tendsto pmS Filter.atTop (𝓝 pm0) :=
    hpmSeq.comp (Filter.tendsto_add_atTop_nat N)
  set q₀ : Fin d → ℝ := qOf pm0 with hq₀
  -- `(q, pmS k) ∈ T` for any `q`; and `(q, pm0) ∈ T`.
  have hT_pmS : ∀ (q : Fin d → ℝ) (k : ℕ), (q, pmS k) ∈ T := fun q k => hpmS_pos k
  have hT_pm0 : ∀ q : Fin d → ℝ, (q, pm0) ∈ T := fun q => hm0_pos
  have hF_cmp : ∀ k, F (qSeq k, pmS k) ≤ F (q₀, pmS k) := by
    intro k
    have hLHS : F (qSeq k, pmS k) = Hdelta h ε x (pmS k).1 (pmS k).2 := by
      change H x ((pmS k).1 - qSeq k) (pmS k).2 + (1 / ε) * K h (qSeq k)
             = Hdelta h ε x (pmS k).1 (pmS k).2
      simpa [qSeq, hpmS] using qOfMin (pmS k) (hpmS_pos k)
    have hBdd_k :
        BddBelow (Set.range
          fun q : Fin d → ℝ =>
            H x ((pmS k).1 - q) (pmS k).2 + (1 / ε) * K h q) := by
      refine ⟨-(h.C * ((pmS k).2 ^ h.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowerAll (pmS k).1 q (pmS k).2 (hpmS_pos k)
      have hpα_nn : 0 ≤ ‖(pmS k).1 - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖(pmS k).1 - q‖ ^ h.α / h.C :=
        div_nonneg hpα_nn (le_of_lt hC_pos)
      have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
      have hK_nn : 0 ≤ K h (q) := K_nonneg h q
      have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
      linarith
    have hRHS_ge :
        Hdelta h ε x (pmS k).1 (pmS k).2 ≤ F (q₀, pmS k) := by
      change Hdelta h ε x (pmS k).1 (pmS k).2
          ≤ H x ((pmS k).1 - q₀) (pmS k).2 + (1 / ε) * K h q₀
      unfold Hdelta
      exact ciInf_le hBdd_k q₀
    rw [hLHS]; exact hRHS_ge
  have hRHS_tend : Filter.Tendsto (fun k => F (q₀, pmS k)) Filter.atTop
      (𝓝 (F (q₀, pm0))) := by
    have hpair_tend : Filter.Tendsto (fun k => (q₀, pmS k)) Filter.atTop
        (𝓝 (q₀, pm0)) := Filter.Tendsto.prodMk_nhds tendsto_const_nhds hpmS_tend
    exact (hF_contAt (q₀, pm0) (hT_pm0 q₀)).tendsto.comp hpair_tend
  obtain ⟨Mup, hMup⟩ : ∃ Mup : ℝ, ∀ k, F (q₀, pmS k) ≤ Mup := by
    have hbdd := hRHS_tend.bddAbove_range
    rcases hbdd with ⟨Mup, hMup⟩
    exact ⟨Mup, fun k => hMup ⟨k, rfl⟩⟩
  obtain ⟨Lconst, hLconst⟩ : ∃ Lconst : ℝ,
      ∀ k, h.C * ((pmS k).2 ^ h.β + 1) ≤ Lconst := by
    have hm_tend : Filter.Tendsto (fun k => (pmS k).2) Filter.atTop (𝓝 pm0.2) :=
      (continuous_snd.tendsto pm0).comp hpmS_tend
    have hrpow_cont : Continuous (fun t : ℝ => t ^ h.β) :=
      Real.continuous_rpow_const hβ_pos
    have htβ_tend : Filter.Tendsto (fun k => (pmS k).2 ^ h.β) Filter.atTop
        (𝓝 (pm0.2 ^ h.β)) := (hrpow_cont.tendsto _).comp hm_tend
    have hbdd_mβ := htβ_tend.bddAbove_range
    rcases hbdd_mβ with ⟨Mβ, hMβ⟩
    refine ⟨h.C * (Mβ + 1), ?_⟩
    intro k
    have hmβk_le : (pmS k).2 ^ h.β ≤ Mβ := hMβ ⟨k, rfl⟩
    have hC_nn : 0 ≤ h.C := le_of_lt hC_pos
    nlinarith [hC_nn, hmβk_le]
  have hF_lower :
      ∀ q p : Fin d → ℝ, ∀ m : ℝ, 0 < m →
        -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
          ≤ F (q, (p, m)) := by
    intro q p m hm
    have hLow := hLowerAll p q m hm
    have hpα_nn : 0 ≤ ‖p - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hK_ge : ‖q‖ ^ h.α ≤ K h q := K_ge_rpow h q
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have h_mul : (1 / ε) * ‖q‖ ^ h.α ≤ (1 / ε) * K h q :=
      mul_le_mul_of_nonneg_left hK_ge hε_inv_nn
    change -(h.C * (m ^ h.β + 1)) + (1 / ε) * ‖q‖ ^ h.α
        ≤ H x (p - q) m + (1 / ε) * K h q
    linarith
  have hqα_bnd : ∀ k, (1 / ε) * ‖qSeq k‖ ^ h.α ≤ Mup + Lconst := by
    intro k
    have hcmp := hF_cmp k
    have hRHS_le_Mup : F (q₀, pmS k) ≤ Mup := hMup k
    have hLHS_le_Mup : F (qSeq k, pmS k) ≤ Mup := le_trans hcmp hRHS_le_Mup
    have hLowF := hF_lower (qSeq k) (pmS k).1 (pmS k).2 (hpmS_pos k)
    have heq : F (qSeq k, (pmS k).1, (pmS k).2) = F (qSeq k, pmS k) := by
      congr 1
    rw [heq] at hLowF
    have hLconst_k : h.C * ((pmS k).2 ^ h.β + 1) ≤ Lconst := hLconst k
    linarith
  set Mqα : ℝ := ε * (Mup + Lconst) with hMqα
  have hqα_bnd' : ∀ k, ‖qSeq k‖ ^ h.α ≤ Mqα := by
    intro k
    have := hqα_bnd k
    have hx_eq : (1 / ε) * ‖qSeq k‖ ^ h.α = ‖qSeq k‖ ^ h.α / ε := by field_simp
    rw [hx_eq] at this
    have := (div_le_iff₀ hε).mp this
    rw [hMqα]; linarith
  have hnorm_le_rpow_plus_one : ∀ t : ℝ, 0 ≤ t → t ≤ t ^ h.α + 1 := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have : 0 ≤ t ^ h.α := Real.rpow_nonneg ht _
      linarith
    · have ht1' : 1 < t := lt_of_not_ge ht1
      have ht_ge_one : (1 : ℝ) ≤ t := le_of_lt ht1'
      have h_rpow_one : t ^ (1 : ℝ) = t := Real.rpow_one _
      have hmono : t ^ (1 : ℝ) ≤ t ^ h.α :=
        Real.rpow_le_rpow_of_exponent_le ht_ge_one hα_ge_one
      rw [h_rpow_one] at hmono
      linarith
  have hqSeq_norm_bnd : ∀ k, ‖qSeq k‖ ≤ Mqα + 1 := by
    intro k
    have hnn : 0 ≤ ‖qSeq k‖ := norm_nonneg _
    have h1 := hnorm_le_rpow_plus_one (‖qSeq k‖) hnn
    have h2 := hqα_bnd' k
    linarith
  set R : ℝ := Mqα + 1 with hRdef
  set B : Set (Fin d → ℝ) := Metric.closedBall 0 R with hBdef
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hqSeq_in_B : ∀ k, qSeq k ∈ B := by
    intro k
    rw [hBdef, Metric.mem_closedBall, dist_zero_right]
    exact hqSeq_norm_bnd k
  have hBdd0 :
      BddBelow (Set.range
        fun q : Fin d → ℝ =>
          H x (pm0.1 - q) pm0.2 + (1 / ε) * K h q) := by
    refine ⟨-(h.C * (pm0.2 ^ h.β + 1)), ?_⟩
    rintro y ⟨q, rfl⟩
    have hLow := hLowerAll pm0.1 q pm0.2 hm0_pos
    have hpα_nn : 0 ≤ ‖pm0.1 - q‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖pm0.1 - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have hK_nn : 0 ≤ K h (q) := K_nonneg h q
    have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
    linarith
  have hF_q₀_eq : F (q₀, pm0) = Hdelta h ε x pm0.1 pm0.2 := by
    change H x (pm0.1 - q₀) pm0.2 + (1 / ε) * K h q₀
         = Hdelta h ε x pm0.1 pm0.2
    simpa [q₀] using qOfMin pm0 hm0_pos
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hcomp_in_B : ∀ k, (qSeq ∘ ns) k ∈ B := fun k => hqSeq_in_B (ns k)
  obtain ⟨q_star, hq_star_B, ψ, hψ_mono, hsubseq_tend⟩ :=
    hB_compact.tendsto_subseq hcomp_in_B
  have hψ_tendsto : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
    hψ_mono.tendsto_atTop
  have hns_psi_tendsto :
      Filter.Tendsto (fun k => ns (ψ k)) Filter.atTop Filter.atTop :=
    hns.comp hψ_tendsto
  have hpmS_subseq :
      Filter.Tendsto (fun k => pmS (ns (ψ k))) Filter.atTop (𝓝 pm0) :=
    hpmS_tend.comp hns_psi_tendsto
  have hF_lhs_tend :
      Filter.Tendsto
        (fun k => F (qSeq (ns (ψ k)), pmS (ns (ψ k)))) Filter.atTop
        (𝓝 (F (q_star, pm0))) := by
    have hpair_tend :
        Filter.Tendsto
          (fun k => (qSeq (ns (ψ k)), pmS (ns (ψ k)))) Filter.atTop
          (𝓝 (q_star, pm0)) :=
      Filter.Tendsto.prodMk_nhds hsubseq_tend hpmS_subseq
    exact (hF_contAt (q_star, pm0) (hT_pm0 q_star)).tendsto.comp hpair_tend
  have hF_rhs_tend :
      Filter.Tendsto (fun k => F (q₀, pmS (ns (ψ k)))) Filter.atTop
        (𝓝 (F (q₀, pm0))) := by
    have hpair_tend : Filter.Tendsto (fun k => (q₀, pmS (ns (ψ k)))) Filter.atTop
        (𝓝 (q₀, pm0)) := Filter.Tendsto.prodMk_nhds tendsto_const_nhds hpmS_subseq
    exact (hF_contAt (q₀, pm0) (hT_pm0 q₀)).tendsto.comp hpair_tend
  have hLim_le : F (q_star, pm0) ≤ F (q₀, pm0) := by
    refine le_of_tendsto_of_tendsto hF_lhs_tend hF_rhs_tend ?_
    refine Filter.Eventually.of_forall (fun k => ?_)
    exact hF_cmp (ns (ψ k))
  have hF_qstar_ge : Hdelta h ε x pm0.1 pm0.2 ≤ F (q_star, pm0) := by
    change Hdelta h ε x pm0.1 pm0.2
        ≤ H x (pm0.1 - q_star) pm0.2 + (1 / ε) * K h q_star
    unfold Hdelta
    exact ciInf_le hBdd0 q_star
  have hF_qstar_eq : F (q_star, pm0) = Hdelta h ε x pm0.1 pm0.2 := by
    have h1 : F (q_star, pm0) ≤ Hdelta h ε x pm0.1 pm0.2 := by
      rw [← hF_q₀_eq]; exact hLim_le
    exact le_antisymm h1 hF_qstar_ge
  have hq_star_eq_q₀ : q_star = q₀ := by
    have huniq := hUniq pm0 hm0_pos q_star
    have hF_unfold : H x (pm0.1 - q_star) pm0.2 + (1 / ε) * K h q_star
        = Hdelta h ε x pm0.1 pm0.2 := hF_qstar_eq
    exact huniq hF_unfold
  refine ⟨ψ, ?_⟩
  rw [hq_star_eq_q₀] at hsubseq_tend
  exact hsubseq_tend

/-- Unit test for `qStar_continuous_of_unique` — degenerate but sorry-free.
We package the trivial case `H ≡ 0`, `qOf ≡ 0` (the unique minimizer
when the only term is the kernel penalty, which has its minimum at
`q = 0` by `K_zero` + `K_nonneg`). -/
example (h : HypothesisWeakGrowth (d := d) (fun _ _ _ => (0 : ℝ)) DpH)
    {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (hLowerAll : ∀ p q : Fin d → ℝ, ∀ m : ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ (0 : ℝ))
    (qOf : (Fin d → ℝ) × ℝ → Fin d → ℝ)
    (qOfMin : ∀ pm : (Fin d → ℝ) × ℝ,
      (0 : ℝ) + (1 / ε) * K h (qOf pm)
        = Hdelta h ε x pm.1 pm.2)
    (hUniq : ∀ pm : (Fin d → ℝ) × ℝ, ∀ q : Fin d → ℝ,
      (0 : ℝ) + (1 / ε) * K h q = Hdelta h ε x pm.1 pm.2 → q = qOf pm) :
    Continuous qOf :=
  qStar_continuous_of_unique (H := fun _ _ _ => 0) h hε
    (by exact continuous_const) hLowerAll qOf qOfMin hUniq

/-! ### `(a:Hat0)` and `(a:mDpHat0)` extension witnesses for `H^ε`

Paper line 1821 (`Source/FGU-monotone_revised.tex`), after
`prop:boundsHepsilon`:

> Note that Lemma `lem:H.delta.monotone` and Proposition
> `prop:boundsHepsilon` ensure the existence of the extended functions
> `H^ε : 𝕋^d × ℝ^d × ℝ⁺_0 → ℝ` and `mD_pH^ε : 𝕋^d × ℝ^d × ℝ⁺_0 → ℝ^d`
> as in `(a:Hat0)` and `(a:mDpHat0)`. Moreover,
> `(p, m) ↦ H^ε(x, p, m)` is continuous on `ℝ^d × ℝ⁺_0`.

The two constructors below package this statement: given suitable
continuity / norm-bound inputs (the per-`x` extensions of paper
`prop:boundsHepsilon.a` and `.c`), they produce
`HypothesisHat0 (Hdelta h ε)` and
`HypothesismDpHat0 DpHε (mDpHε)` respectively.

The signatures mirror the existing API pattern in this file
(`qStar_continuous_of_unique`, `Hdelta_lagrangian_lower_bound`, …),
which takes per-`x` hypotheses as explicit inputs rather than
extracting them from a single bundled assumption. -/

/-! #### Boundary right-continuity of `H` at `m = 0⁺` from the BASE bundle `hH0`

The expert-directed D2b-0 route proves genuine `Hdelta` right-continuity at
`m = 0⁺` toward the LITERAL value `Hdelta … x p 0` from the base boundary
bundle `hH0 : HypothesisHZeroExtension H` (the same T1/T2-accepted base-`H`
paper-clarification rider), NOT from a closed-cone joint-continuity rider on
`H` and NOT from minimizer uniqueness alone.

The first building block, `H_rc0_of_hH0`, recovers real-valued slice
right-continuity of `H` itself at `m = 0⁺`. It is the `Hext_finite_at_zero`-free
specialisation of `H_rc0_of_hHat0`: the finiteness rider is FREE here because
`hAgree` identifies `Hext H x p 0` with the coercion of the real `H x p 0`,
which is never `⊤`. -/

/-- **Slice right-continuity of `H` at `m = 0⁺` from `hH0` alone.**
For a.e. `x` and every `p`, `m ↦ H x p m` tends to `H x p 0` as `m → 0⁺`.

The finiteness of the extended boundary value `Hext H x p 0` is supplied for
free by the agreement field `hAgree` of `hH0`: it equals the coercion of the
real number `H x p 0`, hence is `≠ ⊤`. This is the `hH0`-only specialisation
of `H_rc0_of_hHat0` (Assumptions.lean), threading the BASE bundle, NOT a
regularized-Hamiltonian boundary fact. -/
theorem H_rc0_of_hH0
    (hH0 : StationaryMFG.Hamiltonian.HypothesisHZeroExtension (d := d) H) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)) := by
  -- The finiteness rider `Hext_finite_at_zero H` follows from `hAgree`:
  -- `Hext H x p 0 = ((H x p 0 : ℝ) : WithTop ℝ) ≠ ⊤`.
  have hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H := by
    filter_upwards [hH0.hAgree] with x hxAgree p
    rw [← hxAgree p]
    exact WithTop.coe_ne_top
  exact StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hH0.hHat0 hFin hH0.hAgree

/-! #### `Hdelta_boundary_limsup` — the limsup half of `Hdelta` rc0

For every fixed competitor `q`, the inf-conv value `Hdelta h ε x p m` is
`≤ H x (p − q) m + (1/ε) K q` (`ciInf_le`), and the right-hand side tends to
`H x (p − q) 0 + (1/ε) K q` as `m → 0⁺` (by `H_rc0_of_hH0` applied at the
fixed point `p − q`, plus the constant penalty). This is the per-competitor
upper-control that, together with the (split-out) liminf, assembles `Hdelta`
rc0. We expose it in eventual-bound + `Tendsto` form to avoid the
conditionally-complete-lattice `limsup` cobounded side-goals. -/

/-- **Per-competitor limsup control for `Hdelta` at `m = 0⁺`.**
Fix a competitor `q`. Then:
* eventually as `m → 0⁺`, `Hdelta h ε x p m ≤ H x (p − q) m + (1/ε) K q`
  (testing `q` in the infimum, using `BddBelow` along `m → 0⁺`); and
* `m ↦ H x (p − q) m + (1/ε) K q` tends to `H x (p − q) 0 + (1/ε) K q`
  (slice rc0 of `H` at `p − q` plus a constant).

These two facts are returned together, packaging the limsup half of the
boundary analysis (paper `lem:inf-conv-props`, the `m = 0` Hat0 convention).
The `hBdd` hypothesis is the per-`m` bounded-belowness of the inf-conv family
along `m → 0⁺`; it is supplied by the weak-growth coercivity at the consuming
site. -/
theorem Hdelta_boundary_limsup
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (x p : Fin d → ℝ) (q : Fin d → ℝ)
    (hH_rc0 : Filter.Tendsto (fun m : ℝ => H x (p - q) m) (𝓝[>] (0 : ℝ))
      (𝓝 (H x (p - q) 0)))
    (hBdd : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      BddBelow (Set.range fun q' : Fin d → ℝ => H x (p - q') m)) :
    (∀ᶠ m in 𝓝[>] (0 : ℝ),
        Hdelta h ε x p m ≤ H x (p - q) m + (1 / ε) * K h q)
      ∧ Filter.Tendsto (fun m : ℝ => H x (p - q) m + (1 / ε) * K h q)
          (𝓝[>] (0 : ℝ)) (𝓝 (H x (p - q) 0 + (1 / ε) * K h q)) := by
  refine ⟨?_, ?_⟩
  · -- Eventual upper bound by testing `q` in the infimum.
    filter_upwards [hBdd] with m hBddm
    have hbdd := bddBelow_penalized h hε hBddm
    have hle :
        (⨅ q' : Fin d → ℝ, H x (p - q') m + (1 / ε) * K h q')
          ≤ H x (p - q) m + (1 / ε) * K h q :=
      ciInf_le hbdd q
    exact hle
  · -- The competitor value tends to the boundary competitor value.
    have hconst : Filter.Tendsto (fun _ : ℝ => (1 / ε) * K h q)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / ε) * K h q)) := tendsto_const_nhds
    exact hH_rc0.add hconst

/-- **Paper line 1821 (`(a:Hat0)` for `H^ε`).** Given that for a.e. `x`
and every `p`, the section `m ↦ Hdelta h ε x p m` is right-continuous
at `m = 0` (with limit `Hdelta h ε x p 0`), the regularized Hamiltonian
`Hdelta h ε` satisfies hypothesis `(a:Hat0)`.

The limit value is taken to be `Hdelta h ε x p 0`, which is defined
since `Hdelta` is defined on all of `ℝ` in its `m`-argument (the
infimum is taken over `q : Fin d → ℝ` and `H` is given on `m ∈ ℝ`).

The per-`x` continuity hypothesis `hRC` is downstream of
`prop:boundsHepsilon.a`/`.c` (the bounds on `H^ε`) together with
joint continuity of `H` and `K`; obtaining a sorry-free derivation
of `hRC` from `HypothesisWeakGrowth` alone is the subject of a
follow-up task (it requires the uniqueness of `q^ε` which has the
sup-norm blocker, see `infra-P6-kernel-K-strictly-convex`). -/
theorem Hdelta_hat0
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (_hε : 0 < ε)
    (hRC : ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => Hdelta h ε x p m)
          (𝓝[>] (0 : ℝ)) (𝓝 (Hdelta h ε x p 0))) :
    StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) (Hdelta h ε) := by
  refine { exists_limit_at_zero := ?_ }
  filter_upwards [hRC] with x hxRC p
  refine ⟨((Hdelta h ε x p 0 : ℝ) : WithTop ℝ), ?_⟩
  -- The `WithTop ℝ`-valued lift of a right-continuous real-valued map
  -- is again right-continuous, by composition with `WithTop.continuous_coe`.
  have hcoe : Filter.Tendsto (fun r : ℝ => ((r : ℝ) : WithTop ℝ))
      (𝓝 (Hdelta h ε x p 0)) (𝓝 ((Hdelta h ε x p 0 : ℝ) : WithTop ℝ)) :=
    (WithTop.continuous_coe).tendsto _
  exact hcoe.comp (hxRC p)

/-- Unit test: under a constant choice for which the right-hand limit
is trivially given by `Hdelta h ε x p 0`, `Hdelta_hat0` reproduces a
`HypothesisHat0` witness. We feed an explicit per-`x` continuity input
to exercise the constructor. -/
example
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hRC : ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => Hdelta h ε x p m)
          (𝓝[>] (0 : ℝ)) (𝓝 (Hdelta h ε x p 0))) :
    StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) (Hdelta h ε) :=
  Hdelta_hat0 h hε hRC

/-! #### `(a:mDpHat0)` for a candidate regularized gradient `D_pH^ε`

Following the pattern of `HypothesisPowerGrowth.toMDpHat0`
(`StationaryMFG/Hamiltonian/Assumptions.lean` lines 1987–2088), we
build a `HypothesismDpHat0` witness for an arbitrary candidate
`D_pH^ε` together with its canonical `J`-extension
`J(x, p, m) := m • D_pH^ε(x, p, m)` (which equals zero at `m = 0`).

The inputs are:
* per-`x` continuity of `(p, m) ↦ D_pH^ε(x, p, m)` on
  `{(p, m) | 0 < pm.2}` (paper line 1821: continuity on
  `ℝ^d × ℝ⁺`);
* a per-`x` norm bound
  `‖D_pH^ε(x, p, m)‖ ≤ Bnd(x, p, m)` valid for `m > 0`, where
  `Bnd` is continuous on `{(p, m) | 0 ≤ pm.2}` and locally bounded
  near `m = 0` (paper `prop:boundsHepsilon.b`, line 1785,
  `eq:DpHdelta.upper`); we accept any such dominator as a
  per-`x` hypothesis. -/

/-- **Paper line 1821 (`(a:mDpHat0)` for `H^ε`).** Given a candidate
regularized gradient `DpHε`, jointly continuous in `(p, m)` on
`ℝ^d × ℝ⁺` for a.e. `x`, together with a per-`x` norm dominator
`Bnd(p, m)` continuous on `ℝ^d × ℝ⁺_0`, we obtain the `(a:mDpHat0)`
extension for `DpHε` with `J(x, p, m) := m • DpHε x p m` (which is
`0` at `m = 0`).

Adapted from `HypothesisPowerGrowth.toMDpHat0` (Assumptions.lean,
1987–2088). -/
theorem mDpHdelta_hat0
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Bnd : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (hCont : ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpHε x pm.1 pm.2)
        {pm | 0 < pm.2})
    (hBndCont : ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => Bnd x pm.1 pm.2)
        {pm | 0 ≤ pm.2})
    (hBnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ, ∀ m : ℝ, 0 < m → ‖DpHε x p m‖ ≤ Bnd x p m)
    (hMeas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        DpHε xpm.1 xpm.2.1 xpm.2.2)) :
    StationaryMFG.Hamiltonian.HypothesismDpHat0 (d := d) DpHε
      (fun x p m => if 0 < m then m • DpHε x p m else (0 : Fin d → ℝ)) := by
  refine
    { J_of_pos := ?_
      tendsto_at_zero := ?_
      continuous_J := ?_
      measurable_J := ?_
      J_zero_at_zero := Filter.Eventually.of_forall fun _ _ => by simp }
  · -- `J(x, p, m) = m • DpHε x p m` on `m > 0` by definition.
    intro x p m hm
    simp [hm]
  · -- For a.e. x, all p: `m • DpHε x p m → J(x, p, 0) = 0` as `m → 0⁺`.
    filter_upwards [hCont, hBndCont, hBnd] with x hxC hxBC hxB p
    -- The target: `J(x, p, 0) = 0`.
    have hJ0 : (if (0 : ℝ) < 0 then (0 : ℝ) • DpHε x p 0
                else (0 : Fin d → ℝ)) = (0 : Fin d → ℝ) := by
      simp
    rw [hJ0]
    -- Bound `‖m • DpHε x p m‖` by `m * Bnd x p m` for `m > 0`.
    refine squeeze_zero_norm' (a := fun m : ℝ => m * Bnd x p m) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with m hm
      have hm_pos : 0 < m := hm
      have hbound := hxB p m hm_pos
      -- `‖m • DpHε‖ = |m| * ‖DpHε‖ ≤ m * Bnd` (since m > 0).
      have hnorm_smul : ‖m • DpHε x p m‖ = |m| * ‖DpHε x p m‖ := by
        simp [norm_smul]
      have habsm : |m| = m := abs_of_pos hm_pos
      rw [hnorm_smul, habsm]
      have hm_nn : 0 ≤ m := le_of_lt hm_pos
      exact mul_le_mul_of_nonneg_left hbound hm_nn
    · -- `m * Bnd x p m → 0 * Bnd x p 0 = 0` as `m → 0⁺`.
      have hBnd_tend : Filter.Tendsto (fun m : ℝ => Bnd x p m)
          (𝓝[>] (0 : ℝ)) (𝓝 (Bnd x p 0)) := by
        -- `Bnd` is continuous on `{(p, m) | 0 ≤ m}` (a.e. `x`); the
        -- single-`m` section through `p` reaches `(p, 0)`, which is
        -- in this set.
        have h0_in : ((p, 0) : (Fin d → ℝ) × ℝ) ∈ {pm | (0 : ℝ) ≤ pm.2} := by
          change (0 : ℝ) ≤ (p, (0 : ℝ)).2
          simp
        have hcW := hxBC (p, (0 : ℝ)) h0_in
        -- ContinuousWithinAt of the joint map at (p, 0) within {m ≥ 0}.
        -- Convert to single-`m` `Tendsto` at `0⁺`.
        have hpair : Filter.Tendsto (fun m : ℝ => (p, m))
            (𝓝[>] 0) (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (p, (0 : ℝ))) := by
          refine Filter.tendsto_inf.mpr ⟨?_, ?_⟩
          · refine Filter.Tendsto.prodMk_nhds tendsto_const_nhds ?_
            exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
          · refine Filter.tendsto_principal.mpr ?_
            filter_upwards [self_mem_nhdsWithin] with m hm
            change (0 : ℝ) ≤ (p, m).2
            exact le_of_lt hm
        exact hcW.tendsto.comp hpair
      have hm_tend : Filter.Tendsto (fun m : ℝ => m) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      have hprod := hm_tend.mul hBnd_tend
      simpa using hprod
  · -- For a.e. x, joint continuity of `J` on `{(p, m) | 0 ≤ pm.2}`.
    filter_upwards [hCont, hBndCont, hBnd] with x hxC hxBC hxB
    intro pm hpm
    have hpm2 : (0 : ℝ) ≤ pm.2 := hpm
    rcases lt_or_eq_of_le hpm2 with hpos | hzero
    · -- `pm.2 > 0`. `J` agrees with `m • DpHε` on an open nbhd of `pm`.
      have hopen : {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} ∈ 𝓝 pm := by
        have : IsOpen {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} :=
          isOpen_lt continuous_const continuous_snd
        exact this.mem_nhds hpos
      -- `m • DpHε` is continuous at `pm` (using `hxC`).
      have hcontDpH : ContinuousAt
          (fun pm : (Fin d → ℝ) × ℝ => DpHε x pm.1 pm.2) pm :=
        hxC.continuousAt hopen
      have hcontm : ContinuousAt (fun pm : (Fin d → ℝ) × ℝ => pm.2) pm :=
        continuous_snd.continuousAt
      have hsmul_cont : ContinuousAt
          (fun pm : (Fin d → ℝ) × ℝ => pm.2 • DpHε x pm.1 pm.2) pm :=
        hcontm.smul hcontDpH
      -- The function `J` defined by `if 0 < m then m • DpHε else 0`
      -- agrees with `pm ↦ pm.2 • DpHε ...` on the open set `{m > 0}`.
      have hJagree :
          (fun pm : (Fin d → ℝ) × ℝ =>
              if 0 < pm.2 then pm.2 • DpHε x pm.1 pm.2 else (0 : Fin d → ℝ))
            =ᶠ[𝓝 pm]
            (fun pm : (Fin d → ℝ) × ℝ => pm.2 • DpHε x pm.1 pm.2) := by
        filter_upwards [hopen] with q hq
        have hq2 : 0 < q.2 := hq
        simp [hq2]
      refine ((hsmul_cont.congr hJagree.symm)).continuousWithinAt
    · -- `pm.2 = 0`. Show `J → 0 = J(x, pm.1, 0)` within `{m ≥ 0}`.
      have hpm_eq : pm = (pm.1, 0) := by
        ext
        · rfl
        · simpa using hzero.symm
      rw [hpm_eq]
      -- `J(x, pm.1, 0) = 0` (by definition).
      have hJ0val :
          (if (0 : ℝ) < (pm.1, (0 : ℝ)).2
              then (pm.1, (0 : ℝ)).2 • DpHε x (pm.1, (0 : ℝ)).1 (pm.1, (0 : ℝ)).2
              else (0 : Fin d → ℝ))
            = (0 : Fin d → ℝ) := by
        simp
      rw [ContinuousWithinAt, hJ0val]
      -- Need: `Tendsto J (𝓝[{m ≥ 0}] (pm.1, 0)) (𝓝 0)`.
      -- Use squeeze: `‖J(q)‖ ≤ q.2 * Bnd x q.1 q.2` on `{m ≥ 0}`.
      refine squeeze_zero_norm' (a := fun q : (Fin d → ℝ) × ℝ =>
        q.2 * Bnd x q.1 q.2) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with q hq
        have hq2 : 0 ≤ q.2 := hq
        rcases lt_or_eq_of_le hq2 with hq_pos | hq_zero
        · have hbound := hxB q.1 q.2 hq_pos
          have hJpos :
              (if 0 < q.2 then q.2 • DpHε x q.1 q.2 else (0 : Fin d → ℝ))
                = q.2 • DpHε x q.1 q.2 := by
            simp [hq_pos]
          rw [hJpos]
          have hnorm_smul : ‖q.2 • DpHε x q.1 q.2‖ = |q.2| * ‖DpHε x q.1 q.2‖ := by
            simp [norm_smul]
          have habsq2 : |q.2| = q.2 := abs_of_pos hq_pos
          rw [hnorm_smul, habsq2]
          exact mul_le_mul_of_nonneg_left hbound (le_of_lt hq_pos)
        · -- q.2 = 0: LHS = 0, RHS = 0.
          have hq2eq : q.2 = 0 := hq_zero.symm
          simp [hq2eq]
      · -- Dominator `q.2 * Bnd x q.1 q.2` tends to `0 * Bnd x pm.1 0 = 0`.
        have h0_in : ((pm.1, (0 : ℝ)) : (Fin d → ℝ) × ℝ) ∈ {pm | (0 : ℝ) ≤ pm.2} := by
          change (0 : ℝ) ≤ (0 : ℝ); exact le_refl _
        have hBnd_tend : Filter.Tendsto
            (fun q : (Fin d → ℝ) × ℝ => Bnd x q.1 q.2)
            (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (pm.1, (0 : ℝ)))
            (𝓝 (Bnd x pm.1 0)) :=
          (hxBC (pm.1, (0 : ℝ)) h0_in).tendsto
        have hm_tend : Filter.Tendsto
            (fun q : (Fin d → ℝ) × ℝ => q.2)
            (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (pm.1, (0 : ℝ)))
            (𝓝 0) := by
          have hcont : Continuous (fun q : (Fin d → ℝ) × ℝ => q.2) := continuous_snd
          have hcAt : Filter.Tendsto (fun q : (Fin d → ℝ) × ℝ => q.2)
              (𝓝 ((pm.1, (0 : ℝ)) : (Fin d → ℝ) × ℝ)) (𝓝 0) := by
            have := hcont.tendsto ((pm.1, (0 : ℝ)) : (Fin d → ℝ) × ℝ)
            simpa using this
          exact hcAt.mono_left nhdsWithin_le_nhds
        have hprod := hm_tend.mul hBnd_tend
        simpa using hprod
  · -- `measurable_J`: the extension is
    -- `fun (x,p,m) => if 0 < m then m • DpHε x p m else 0`, measurable by
    -- `Measurable.ite` using joint measurability of `DpHε` (`hMeas`).
    show Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        if 0 < xpm.2.2 then xpm.2.2 • DpHε xpm.1 xpm.2.1 xpm.2.2
        else (0 : Fin d → ℝ))
    have hset : MeasurableSet
        {xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < xpm.2.2} :=
      measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)
    refine Measurable.ite hset ?_ measurable_const
    exact (measurable_snd.comp measurable_snd).smul hMeas

/-- Unit test for `mDpHdelta_hat0`: the trivial gradient `DpHε ≡ 0` and
trivial dominator `Bnd ≡ 0` produce a `HypothesismDpHat0` witness. -/
example :
    StationaryMFG.Hamiltonian.HypothesismDpHat0 (d := d)
      (fun (_ _ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ))
      (fun (_ _ : Fin d → ℝ) (m : ℝ) =>
        if 0 < m then m • (0 : Fin d → ℝ) else (0 : Fin d → ℝ)) :=
  mDpHdelta_hat0 (d := d)
    (fun _ _ _ => (0 : Fin d → ℝ))
    (fun _ _ _ => (0 : ℝ))
    (Filter.Eventually.of_forall (fun _ => continuousOn_const))
    (Filter.Eventually.of_forall (fun _ => continuousOn_const))
    (Filter.Eventually.of_forall (fun _ _ _ _ => by simp))
    measurable_const

end InfimalConvolution
end StationaryMFG
