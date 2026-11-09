module

public import StationaryMFG.Hamiltonian.Assumptions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Ray

@[expose] public section

/-!
# Inf-conv kernel `K`

This file introduces the regularization kernel
`K(q) := ‖q‖ + ‖q‖ ^ α` used in §6.0 of
Ferreira–Gomes–Üçer, *Solving Mean-Field Games with Monotonicity
Methods in Banach Spaces* (`Source/FGU-monotone_revised.tex`,
line 1622, equation preceding `eq:defHdelta`).

`α := h.α` is the momentum-growth exponent (`1 < α`) supplied by
`HypothesisWeakGrowth`. The kernel `K` is the Yosida-style penalty
used in the inf-conv regularization

  `H_δ(x, p, m) = ⨅ q, H x (p - q) m + (1/ε) K q`.

We prove the basic properties consumed throughout Phase 6:

* `K_nonneg`, `K_zero`,
* `K_continuous`,
* `K_ge_rpow` (the coercive lower bound `‖q‖^α ≤ K q`).

## Euclidean-norm view of `K`

In the paper, `|·|` is the **Euclidean norm** on `ℝ^d`. Mathlib's
default norm on `Fin d → ℝ` is the sup-norm, which is not strictly
convex. To recover the paper's strict-convexity statement
(line 1622) without rewriting the entire project, we set up a
**local** Euclidean-norm bridge inside this file:

* `toEucl : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)` — type-level
  identity, switching the norm instance from sup-norm to L².
* `K_euclidean : EuclideanSpace ℝ (Fin d) → ℝ`,
  `K_euclidean v := ‖v‖ + ‖v‖ ^ h.α` (now `‖·‖` is the Euclidean
  norm).
* `K_euclidean_strictlyConvex` — the paper's strict-convexity claim,
  in its proper Euclidean setting.

Splicing `K_euclidean` into the rest of the inf-conv pipeline
(redefining `K` to use `K_euclidean ∘ toEucl`, and rewiring the
downstream `Hdelta_*` bounds and `Stabilization.lean` to the
Euclidean norm) is deferred to a separate task — it is a non-trivial
refactor since several upper-bound proofs depend on the precise form
`K h p = ‖p‖_sup + ‖p‖_sup^α`.
-/

namespace StationaryMFG
namespace InfimalConvolution

open Filter Topology
open StationaryMFG.Hamiltonian

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ### Local Euclidean-norm bridge

The §6.0 kernel `K` is defined in terms of the Euclidean (L²) norm on
`ℝ^d` (paper line 1622). Since Mathlib's default norm on
`Fin d → ℝ` is the sup-norm, we set up a **local** Euclidean-norm
bridge: `toEucl : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)` is the
type-level identity, switching the norm instance from sup-norm to
L². The Euclidean form is essential to prove strict convexity of `K`
(which the sup-norm fails). -/

/-- The canonical inclusion `Fin d → ℝ ↪ EuclideanSpace ℝ (Fin d)`.
Underlying function is the identity; the codomain carries the
Euclidean (L²) norm rather than the sup-norm. -/
noncomputable def toEucl (q : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 q

@[simp] lemma toEucl_apply (q : Fin d → ℝ) (i : Fin d) :
    (toEucl q) i = q i := rfl

@[simp] lemma toEucl_zero : toEucl (0 : Fin d → ℝ) = 0 := rfl

@[simp] lemma toEucl_add (q q' : Fin d → ℝ) :
    toEucl (q + q') = toEucl q + toEucl q' := rfl

@[simp] lemma toEucl_smul (a : ℝ) (q : Fin d → ℝ) :
    toEucl (a • q) = a • toEucl q := rfl

lemma toEucl_injective : Function.Injective (toEucl (d := d)) :=
  fun _ _ h => WithLp.toLp_injective 2 h

/-- The Euclidean norm of `toEucl q` equals `√(∑ q_i^2)`. -/
lemma norm_toEucl_sq (q : Fin d → ℝ) :
    ‖toEucl q‖ ^ 2 = ∑ i, (q i) ^ 2 := by
  have := EuclideanSpace.real_norm_sq_eq (toEucl q)
  simpa [toEucl_apply] using this

/-- Sup-norm is at most Euclidean norm on `Fin d → ℝ`. -/
lemma sup_norm_le_eucl_norm (q : Fin d → ℝ) :
    ‖q‖ ≤ ‖toEucl q‖ := by
  classical
  have h_eucl_nn : 0 ≤ ‖toEucl q‖ := norm_nonneg _
  rw [pi_norm_le_iff_of_nonneg h_eucl_nn]
  intro i
  have h_each : (q i) ^ 2 ≤ ‖toEucl q‖ ^ 2 := by
    rw [norm_toEucl_sq]
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        (0 : ℝ) ≤ (q j) ^ 2 := fun _ _ => sq_nonneg _
    exact Finset.single_le_sum hnonneg (Finset.mem_univ i)
  have hqi_abs : |q i| ^ 2 = (q i) ^ 2 := sq_abs _
  have h_qi_abs_sq : |q i| ^ 2 ≤ ‖toEucl q‖ ^ 2 := by
    rw [hqi_abs]; exact h_each
  have h_qi_abs_nn : (0 : ℝ) ≤ |q i| := abs_nonneg _
  have : |q i| ≤ ‖toEucl q‖ :=
    abs_le_of_sq_le_sq' (by
      simpa [abs_of_nonneg h_qi_abs_nn, abs_of_nonneg h_eucl_nn]
        using h_qi_abs_sq) h_eucl_nn |>.2
  simpa [Real.norm_eq_abs] using this

/-- Euclidean norm is at most `√d` times the sup-norm. -/
lemma eucl_norm_le_sqrt_d_sup_norm (q : Fin d → ℝ) :
    ‖toEucl q‖ ≤ Real.sqrt d * ‖q‖ := by
  classical
  have h_eucl_nn : 0 ≤ ‖toEucl q‖ := norm_nonneg _
  have h_sup_nn : 0 ≤ ‖q‖ := norm_nonneg _
  have h_d_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
  have h_sqrtd_nn : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h_rhs_nn : (0 : ℝ) ≤ Real.sqrt d * ‖q‖ := mul_nonneg h_sqrtd_nn h_sup_nn
  -- Square both sides: ‖toEucl q‖^2 = ∑ q_i^2 ≤ d * ‖q‖^2 = (√d * ‖q‖)^2.
  have h_sq_le : ‖toEucl q‖ ^ 2 ≤ (Real.sqrt d * ‖q‖) ^ 2 := by
    rw [norm_toEucl_sq]
    have h_each : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        (q i) ^ 2 ≤ ‖q‖ ^ 2 := by
      intro i _
      have hqi : |q i| ≤ ‖q‖ := by
        have := norm_le_pi_norm q i
        simpa [Real.norm_eq_abs] using this
      have hqi_sq : (q i) ^ 2 = |q i| ^ 2 := (sq_abs _).symm
      rw [hqi_sq]
      exact pow_le_pow_left₀ (abs_nonneg _) hqi 2
    have h_sum_le : (∑ i, (q i) ^ 2) ≤ ∑ _ : Fin d, ‖q‖ ^ 2 :=
      Finset.sum_le_sum h_each
    have h_card :
        (∑ _ : Fin d, ‖q‖ ^ 2) = (d : ℝ) * ‖q‖ ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_mul_eq : (Real.sqrt d * ‖q‖) ^ 2 = (d : ℝ) * ‖q‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h_d_nn]
    rw [h_mul_eq]
    linarith
  -- From the squared inequality, recover the unsquared one via sqrt monotonicity.
  have h_sqrt_le :
      Real.sqrt (‖toEucl q‖ ^ 2) ≤ Real.sqrt ((Real.sqrt d * ‖q‖) ^ 2) :=
    Real.sqrt_le_sqrt h_sq_le
  rw [Real.sqrt_sq h_eucl_nn, Real.sqrt_sq h_rhs_nn] at h_sqrt_le
  exact h_sqrt_le

/-- The §6.0 regularization kernel `K(q) = ‖q‖_eucl + ‖q‖_eucl ^ α`
where `‖·‖_eucl` is the Euclidean (L²) norm on `ℝ^d` (paper line 1622)
and `α = h.α` is the weak-growth exponent (`α > 1`). The Euclidean
norm is used (rather than the sup-norm) because strict convexity of
`K` requires it (`K_strictlyConvex`). -/
noncomputable def K (h : HypothesisWeakGrowth (d := d) H DpH)
    (q : Fin d → ℝ) : ℝ :=
  ‖toEucl q‖ + ‖toEucl q‖ ^ h.α

lemma K_nonneg (h : HypothesisWeakGrowth (d := d) H DpH) (q : Fin d → ℝ) :
    0 ≤ K h q := by
  unfold K
  exact add_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

lemma K_zero (h : HypothesisWeakGrowth (d := d) H DpH) :
    K h (0 : Fin d → ℝ) = 0 := by
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_ne : h.α ≠ 0 := ne_of_gt hα_pos
  change ‖toEucl (0 : Fin d → ℝ)‖ + ‖toEucl (0 : Fin d → ℝ)‖ ^ h.α = 0
  rw [toEucl_zero]
  simp [Real.zero_rpow hα_ne]

lemma toEucl_continuous : Continuous (toEucl (d := d)) :=
  (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap.continuous_of_finiteDimensional

lemma K_continuous (h : HypothesisWeakGrowth (d := d) H DpH) :
    Continuous (K h) := by
  have hα_nonneg : 0 ≤ h.α := le_of_lt (lt_trans zero_lt_one h.hα)
  have hcont_norm : Continuous fun q : Fin d → ℝ => ‖toEucl q‖ :=
    continuous_norm.comp toEucl_continuous
  have hcont_rpow : Continuous fun q : Fin d → ℝ => ‖toEucl q‖ ^ h.α :=
    hcont_norm.rpow_const (fun _ => Or.inr hα_nonneg)
  exact hcont_norm.add hcont_rpow

/-- Direct Euclidean-norm form: `‖toEucl q‖ ^ α ≤ K h q`. -/
lemma K_ge_rpow_eucl (h : HypothesisWeakGrowth (d := d) H DpH) (q : Fin d → ℝ) :
    ‖toEucl q‖ ^ h.α ≤ K h q := by
  unfold K
  have hnorm : 0 ≤ ‖toEucl q‖ := norm_nonneg _
  linarith

/-- Sup-norm form (legacy compatibility): `‖q‖ ^ α ≤ K h q`. Derived
from the Euclidean form via `sup_norm_le_eucl_norm`. -/
lemma K_ge_rpow (h : HypothesisWeakGrowth (d := d) H DpH) (q : Fin d → ℝ) :
    ‖q‖ ^ h.α ≤ K h q := by
  have hα_nn : 0 ≤ h.α := le_of_lt (lt_trans zero_lt_one h.hα)
  have h_step1 : ‖q‖ ^ h.α ≤ ‖toEucl q‖ ^ h.α :=
    Real.rpow_le_rpow (norm_nonneg _) (sup_norm_le_eucl_norm q) hα_nn
  exact h_step1.trans (K_ge_rpow_eucl h q)

/-! ### Subdifferential of `K` at the origin

Paper line 1925 (Remark `\label{observation}`): since `α > 1`, the
subdifferential `δK(0)` equals the (closed) dual unit ball.

Mathlib (on the pinned toolchain) does not expose a generic
`HasSubgradientAt` predicate, and our ambient norm on `Fin d → ℝ` is the
sup norm — so we phrase the subgradient condition self-contained, with
the canonical pairing `⟨v, y⟩ := ∑ i, v i * y i`. The "dual unit ball"
is then `{v | ∀ y, ⟨v, y⟩ ≤ ‖y‖}`, and we prove

  `HasSubgradientAt (K h) 0 v ↔ ∀ y, ∑ i, v i * y i ≤ ‖y‖`. -/

/-- Subgradient of a real-valued function on `Fin d → ℝ` at a point,
phrased with the canonical bilinear pairing `⟨v, y⟩ = ∑ i, v i * y i`.
This is the convex-analysis subgradient (no smoothness assumed). -/
def HasSubgradientAt
    (f : (Fin d → ℝ) → ℝ) (x v : Fin d → ℝ) : Prop :=
  ∀ y : Fin d → ℝ, f x + ∑ i, v i * (y i - x i) ≤ f y

lemma hasSubgradientAt_iff_zero
    {f : (Fin d → ℝ) → ℝ} {v : Fin d → ℝ} :
    HasSubgradientAt f 0 v ↔
      ∀ y : Fin d → ℝ, f 0 + ∑ i, v i * y i ≤ f y := by
  unfold HasSubgradientAt
  refine ⟨fun H y => ?_, fun H y => ?_⟩
  · simpa using H y
  · simpa using H y

/-- **Paper observation (line 1925).** For `α > 1`, the subgradient
of `K(q) = ‖toEucl q‖ + ‖toEucl q‖^α` at the origin equals the
(Euclidean) closed dual unit ball, characterised here as
`{v | ∀ y, ∑ i, v i * y i ≤ ‖toEucl y‖}`. -/
theorem K_subdiff_zero (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : Fin d → ℝ) :
    HasSubgradientAt (K h) 0 v ↔
      ∀ y : Fin d → ℝ, ∑ i, v i * y i ≤ ‖toEucl y‖ := by
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_sub_pos : 0 < h.α - 1 := sub_pos.mpr h.hα
  rw [hasSubgradientAt_iff_zero]
  constructor
  · -- Forward direction: scale `y ↦ t • y`, divide by `t`, take `t → 0⁺`.
    intro Hsub y
    -- Standard pairing on `Fin d → ℝ`.
    set ip : ℝ := ∑ i, v i * y i with hip
    -- For all `t > 0`: `t * ‖toEucl y‖ + t^α * ‖toEucl y‖^α ≥ t * ip`.
    have h_ineq_t : ∀ t : ℝ, 0 < t →
        t * ip ≤ t * ‖toEucl y‖ + t ^ h.α * ‖toEucl y‖ ^ h.α := by
      intro t ht
      have ht_nonneg : (0 : ℝ) ≤ t := le_of_lt ht
      have hKt : K h (t • y) = t * ‖toEucl y‖ + t ^ h.α * ‖toEucl y‖ ^ h.α := by
        unfold K
        have hns : ‖toEucl (t • y)‖ = t * ‖toEucl y‖ := by
          rw [toEucl_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        rw [hns]
        congr 1
        rw [Real.mul_rpow ht_nonneg (norm_nonneg _)]
      have hKzero : K h (0 : Fin d → ℝ) = 0 := K_zero h
      have hHsub_ty := Hsub (t • y)
      -- `∑ i, v i * (t • y) i = t * ip`.
      have hpair : (∑ i, v i * (t • y) i) = t * ip := by
        simp [hip, Finset.mul_sum, mul_left_comm, smul_eq_mul]
      rw [hpair, hKzero, zero_add, hKt] at hHsub_ty
      exact hHsub_ty
    -- Show `ip ≤ ‖toEucl y‖`. Suppose for contradiction `‖toEucl y‖ < ip`.
    by_contra hcon
    have hcon : ‖toEucl y‖ < ip := lt_of_not_ge hcon
    -- Pick `t > 0` so small that `t^{α-1} * ‖toEucl y‖^α < ip - ‖toEucl y‖`.
    have hδ : 0 < ip - ‖toEucl y‖ := sub_pos.mpr hcon
    -- Case `‖toEucl y‖ = 0` is contradictory: then `y = 0`, so `ip = 0`.
    rcases (norm_nonneg (toEucl y)).lt_or_eq with hpos | hzero
    · -- `‖toEucl y‖ > 0`.
      set δ : ℝ := ip - ‖toEucl y‖ with hδdef
      have hyα_pos : 0 < ‖toEucl y‖ ^ h.α := Real.rpow_pos_of_pos hpos _
      -- Define `t := (δ / (2 * ‖toEucl y‖^α))^(1/(α-1))`.
      set t : ℝ := (δ / (2 * ‖toEucl y‖ ^ h.α)) ^ (1 / (h.α - 1)) with htdef
      have h2yα_pos : 0 < 2 * ‖toEucl y‖ ^ h.α := by positivity
      have hbase_pos : 0 < δ / (2 * ‖toEucl y‖ ^ h.α) := by positivity
      have ht_pos : 0 < t := Real.rpow_pos_of_pos hbase_pos _
      -- `t^(α-1) = δ / (2 * ‖toEucl y‖^α)` because `(α-1) * (1/(α-1)) = 1`.
      have ht_alpha_sub_one :
          t ^ (h.α - 1) = δ / (2 * ‖toEucl y‖ ^ h.α) := by
        rw [htdef, ← Real.rpow_mul (le_of_lt hbase_pos)]
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hα_sub_pos), Real.rpow_one]
      -- Use the inequality at `t`.
      have hineq := h_ineq_t t ht_pos
      -- `t^α = t * t^(α-1)` so `t^α * ‖toEucl y‖^α = t * (t^(α-1) * ‖toEucl y‖^α)`.
      have htα_eq : t ^ h.α = t * t ^ (h.α - 1) := by
        have hα_split : h.α = 1 + (h.α - 1) := by ring
        conv_lhs => rw [hα_split]
        rw [Real.rpow_add ht_pos, Real.rpow_one]
      -- So `t * ip ≤ t * ‖toEucl y‖ + t * (t^(α-1) * ‖toEucl y‖^α)`.
      have hineq2 :
          t * ip ≤ t * ‖toEucl y‖ + t * (t ^ (h.α - 1) * ‖toEucl y‖ ^ h.α) := by
        rw [htα_eq, mul_assoc] at hineq
        exact hineq
      -- Cancel `t > 0`: `ip ≤ ‖toEucl y‖ + t^(α-1) * ‖toEucl y‖^α`.
      have hineq3 : ip ≤ ‖toEucl y‖ + t ^ (h.α - 1) * ‖toEucl y‖ ^ h.α := by
        have hineq2' : t * ip ≤ t * (‖toEucl y‖ + t ^ (h.α - 1) * ‖toEucl y‖ ^ h.α) := by
          rw [mul_add]; exact hineq2
        exact le_of_mul_le_mul_left hineq2' ht_pos
      rw [ht_alpha_sub_one] at hineq3
      -- `δ / (2 * ‖toEucl y‖^α) * ‖toEucl y‖^α = δ / 2`.
      have hsimp :
          δ / (2 * ‖toEucl y‖ ^ h.α) * ‖toEucl y‖ ^ h.α = δ / 2 := by
        field_simp
      rw [hsimp] at hineq3
      -- `ip ≤ ‖toEucl y‖ + δ / 2`, but `ip = ‖toEucl y‖ + δ`, so `δ ≤ δ / 2`, contradiction.
      have : ip = ‖toEucl y‖ + δ := by simp [hδdef]
      linarith
    · -- `‖toEucl y‖ = 0`. Then `toEucl y = 0`, so `y = 0`, so `ip = 0`.
      have hte_eq : toEucl y = 0 := by
        have : ‖toEucl y‖ = 0 := hzero.symm
        exact norm_eq_zero.mp this
      have hy_eq : y = 0 := toEucl_injective (by rw [hte_eq, toEucl_zero])
      have : ip = 0 := by simp [hip, hy_eq]
      linarith
  · -- Backward direction: trivial chain
    -- `ip ≤ ‖toEucl y‖ ≤ ‖toEucl y‖ + ‖toEucl y‖^α = K h y`.
    intro Hdual y
    have hKy : K h y = ‖toEucl y‖ + ‖toEucl y‖ ^ h.α := rfl
    have hy_alpha_nn : 0 ≤ ‖toEucl y‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hKzero : K h (0 : Fin d → ℝ) = 0 := K_zero h
    rw [hKzero, hKy, zero_add]
    have h1 : ∑ i, v i * y i ≤ ‖toEucl y‖ := Hdual y
    linarith

/-- **Sufficient condition for sup-norm subgradient.** If the
pairing-vs-sup-norm bound `∀ y, ∑ i, v i * y i ≤ ‖y‖` holds, then `v`
is a subgradient of `K h` at `0`. (The dual ball with respect to the
sup-norm is contained in the dual ball with respect to the Euclidean
norm, because `‖y‖_sup ≤ ‖toEucl y‖`.) Used in `Stabilization.lean` to
upgrade the elementary sup-norm pairing bound to the Euclidean
subdifferential. -/
lemma K_subdiff_zero_of_sup_bound
    (h : HypothesisWeakGrowth (d := d) H DpH) {v : Fin d → ℝ}
    (Hbnd : ∀ y : Fin d → ℝ, ∑ i, v i * y i ≤ ‖y‖) :
    HasSubgradientAt (K h) 0 v := by
  rw [K_subdiff_zero]
  intro y
  exact (Hbnd y).trans (sup_norm_le_eucl_norm y)

/-! ### General base-point subgradient norm bound

The `q = 0` versions above characterise `∂K(0)` as the dual unit ball.
For the inf-conv gradient estimate we need the bound at a **general**
base point `q₀`: every subgradient `v ∈ ∂K(q₀)` satisfies the Euclidean
norm bound `‖toEucl v‖_e ≤ 1 + α‖toEucl q₀‖_e^(α−1)`. This is the
genuine content behind paper line 1808
(`eq:inf-conv.diff-relation1`, `|D_pH^ε| ≤ (1/ε)(1 + α|q^ε|^{α−1})`),
since `K` is C¹ on `{q ≠ 0}` with `‖∇K(q)‖_e = 1 + α‖q‖_e^{α−1}`.

We do not differentiate `K`; instead we run a scaling/limit
contradiction (mirroring the forward direction of `K_subdiff_zero`):
test the subgradient inequality along the direction `v` at scale `t`,
use the Euclidean triangle inequality and the convex-slope bound
`b^α − a^α ≤ α b^{α−1}(b − a)`, then push `t → 0⁺`. -/

/-- **Convex-slope (gradient) inequality for `t ↦ t^α`.** For `α ≥ 1`
and `0 ≤ a ≤ b`, `b ^ α − a ^ α ≤ α * b ^ (α − 1) * (b − a)`.
Derived from Bernoulli's inequality
(`one_add_mul_self_le_rpow_one_add`). -/
lemma rpow_sub_rpow_le_slope {α a b : ℝ} (hα : 1 ≤ α)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ α - a ^ α ≤ α * b ^ (α - 1) * (b - a) := by
  rcases eq_or_lt_of_le (ha.trans hab) with hb0 | hbpos
  · -- `b = 0`, hence `a = 0`.
    have hb : b = 0 := hb0.symm
    have ha0 : a = 0 := le_antisymm (hb ▸ hab) ha
    have hα_pos : 0 < α := lt_of_lt_of_le zero_lt_one hα
    simp [hb, ha0, Real.zero_rpow (ne_of_gt hα_pos)]
  · -- `0 < b`.
    -- Bernoulli with `s := (a - b)/b ∈ [-1, 0]`, `p := α`:
    -- `1 + α * (a - b)/b ≤ (1 + (a - b)/b) ^ α = (a / b) ^ α`.
    set s : ℝ := (a - b) / b with hs_def
    have hb_ne : b ≠ 0 := ne_of_gt hbpos
    have hs_ge : -1 ≤ s := by
      rw [hs_def, le_div_iff₀ hbpos]
      have : -b ≤ a - b := by linarith
      linarith
    have hbern := one_add_mul_self_le_rpow_one_add hs_ge hα
    -- `1 + s = a / b`.
    have h1s : 1 + s = a / b := by
      rw [hs_def]; field_simp; ring
    rw [h1s] at hbern
    -- `(a / b) ^ α = a ^ α / b ^ α` (both nonneg).
    have hab_nn : 0 ≤ a / b := div_nonneg ha (le_of_lt hbpos)
    have hpow_div : (a / b) ^ α = a ^ α / b ^ α := by
      rw [Real.div_rpow ha (le_of_lt hbpos)]
    rw [hpow_div] at hbern
    -- Multiply Bernoulli `1 + α * s ≤ a^α / b^α` by `b^α > 0`.
    have hbα_pos : 0 < b ^ α := Real.rpow_pos_of_pos hbpos _
    have hmul := mul_le_mul_of_nonneg_left hbern (le_of_lt hbα_pos)
    -- LHS: `b^α * (1 + α*s) = b^α + α * b^α * s`.
    -- RHS: `b^α * (a^α / b^α) = a^α`.
    have hrhs : b ^ α * (a ^ α / b ^ α) = a ^ α := by
      field_simp
    rw [hrhs] at hmul
    -- `b^α * s = b^(α-1) * (a - b)` since `b^α / b = b^(α-1)`.
    have hbα_split : b ^ α = b ^ (α - 1) * b := by
      have heq : α = (α - 1) + 1 := by ring
      conv_lhs => rw [heq]
      rw [Real.rpow_add hbpos, Real.rpow_one]
    have hbαs : b ^ α * s = b ^ (α - 1) * (a - b) := by
      rw [hbα_split, hs_def]
      field_simp
    -- From `b^α + α * (b^α * s) ≤ a^α` rearrange.
    have hmul2 : b ^ α + α * (b ^ α * s) ≤ a ^ α := by
      calc b ^ α + α * (b ^ α * s)
          = b ^ α * (1 + α * s) := by ring
        _ ≤ a ^ α := hmul
    rw [hbαs] at hmul2
    nlinarith [hmul2]

/-- **General base-point subgradient norm bound (Euclidean).** If
`v ∈ ∂K(q₀)` (in the convex-analysis sense `HasSubgradientAt`), then
the Euclidean norm of `v` is bounded by `1 + α‖q₀‖_e^{α−1}`. This is
the paper's line-1808 estimate, in its native Euclidean form. -/
theorem K_subdiff_norm_le
    (h : HypothesisWeakGrowth (d := d) H DpH) {q₀ v : Fin d → ℝ}
    (hsub : HasSubgradientAt (K h) q₀ v) :
    ‖toEucl v‖ ≤ 1 + h.α * ‖toEucl q₀‖ ^ (h.α - 1) := by
  classical
  set α : ℝ := h.α with hαdef
  have hα_gt_one : 1 < α := h.hα
  have hα_one_le : 1 ≤ α := le_of_lt hα_gt_one
  have hα_sub_nn : 0 ≤ α - 1 := by linarith
  set N : ℝ := ‖toEucl v‖ with hNdef
  set a : ℝ := ‖toEucl q₀‖ with hadef
  have hN_nn : 0 ≤ N := norm_nonneg _
  have ha_nn : 0 ≤ a := norm_nonneg _
  -- Target RHS.
  set RHS : ℝ := 1 + α * a ^ (α - 1) with hRHSdef
  have haα_nn : 0 ≤ a ^ (α - 1) := Real.rpow_nonneg ha_nn _
  have hRHS_nn : 0 ≤ RHS := by
    have : 0 ≤ α * a ^ (α - 1) :=
      mul_nonneg (le_of_lt (lt_trans zero_lt_one hα_gt_one)) haα_nn
    rw [hRHSdef]; linarith
  by_contra hcon
  push_neg at hcon  -- `RHS < N`
  -- `N > 0` since `RHS ≥ 0`.
  have hN_pos : 0 < N := lt_of_le_of_lt hRHS_nn hcon
  -- `v ⬝ v = N^2`.
  have hvv : v ⬝ v = N ^ 2 := by
    rw [hNdef]
    rw [norm_toEucl_sq]
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [sq]
  -- For each `t > 0`, the subgradient inequality at `y = q₀ + t • v`
  -- gives `t * (v ⬝ v) ≤ K(q₀ + t•v) - K(q₀)`.
  have hsub_t : ∀ t : ℝ, 0 < t →
      t * N ^ 2 ≤ K h (q₀ + t • v) - K h q₀ := by
    intro t ht
    have hsy := hsub (q₀ + t • v)
    -- `∑ i, v i * ((q₀ + t•v) i - q₀ i) = t * (v ⬝ v)`.
    have hpair : (∑ i, v i * ((q₀ + t • v) i - q₀ i)) = t * (v ⬝ v) := by
      unfold dotProduct
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpair, hvv] at hsy
    linarith [hsy]
  -- Bound `K(q₀ + t•v) - K(q₀)` from above for `t > 0`.
  -- `‖toEucl(q₀ + t•v)‖ ≤ a + t*N`.
  have hKt_bnd : ∀ t : ℝ, 0 < t →
      K h (q₀ + t • v) - K h q₀ ≤ t * N + α * (a + t * N) ^ (α - 1) * (t * N) := by
    intro t ht
    set b : ℝ := ‖toEucl (q₀ + t • v)‖ with hbdef
    have hb_nn : 0 ≤ b := norm_nonneg _
    -- `b ≤ a + t * N`.
    have htN_nn : 0 ≤ t * N := mul_nonneg (le_of_lt ht) hN_nn
    have hatN_nn : 0 ≤ a + t * N := by linarith
    have hb_le : b ≤ a + t * N := by
      have htri : ‖toEucl (q₀ + t • v)‖ ≤ ‖toEucl q₀‖ + ‖toEucl (t • v)‖ := by
        rw [toEucl_add]; exact norm_add_le _ _
      have hsmul : ‖toEucl (t • v)‖ = t * N := by
        rw [toEucl_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      rw [hbdef]; rw [hsmul] at htri; rw [hadef]; linarith [htri]
    -- `K(q₀ + t•v) = b + b^α`, `K(q₀) = a + a^α`.
    have hKy : K h (q₀ + t • v) = b + b ^ α := rfl
    have hKx : K h q₀ = a + a ^ α := rfl
    rw [hKy, hKx]
    -- Norm part: `b - a ≤ t*N`.
    have hnorm_part : b - a ≤ t * N := by linarith [hb_le]
    -- rpow part: `b^α - a^α ≤ α * (a + t*N)^(α-1) * (t*N)`.
    have hslope_term : 0 ≤ α * (a + t * N) ^ (α - 1) * (t * N) := by
      have h1 : 0 ≤ α := le_of_lt (lt_trans zero_lt_one hα_gt_one)
      have h2 : 0 ≤ (a + t * N) ^ (α - 1) := Real.rpow_nonneg hatN_nn _
      positivity
    have hrpow_part : b ^ α - a ^ α ≤ α * (a + t * N) ^ (α - 1) * (t * N) := by
      rcases le_or_gt b a with hba | hab
      · -- `b ≤ a`, so `b^α ≤ a^α`, difference `≤ 0`.
        have : b ^ α ≤ a ^ α :=
          Real.rpow_le_rpow hb_nn hba (le_of_lt (lt_trans zero_lt_one hα_gt_one))
        linarith [hslope_term]
      · -- `a < b`: slope at `b`, then bound `b^(α-1) ≤ (a+tN)^(α-1)` and `b-a ≤ tN`.
        have hslope := rpow_sub_rpow_le_slope hα_one_le ha_nn (le_of_lt hab)
        have hbα1_le : b ^ (α - 1) ≤ (a + t * N) ^ (α - 1) :=
          Real.rpow_le_rpow hb_nn hb_le hα_sub_nn
        have hba_nn : 0 ≤ b - a := by linarith
        have hα_nn : 0 ≤ α := le_of_lt (lt_trans zero_lt_one hα_gt_one)
        -- `α * b^(α-1) * (b-a) ≤ α * (a+tN)^(α-1) * (tN)`.
        have hstep1 : α * b ^ (α - 1) * (b - a)
            ≤ α * (a + t * N) ^ (α - 1) * (b - a) := by
          apply mul_le_mul_of_nonneg_right _ hba_nn
          exact mul_le_mul_of_nonneg_left hbα1_le hα_nn
        have hstep2 : α * (a + t * N) ^ (α - 1) * (b - a)
            ≤ α * (a + t * N) ^ (α - 1) * (t * N) := by
          apply mul_le_mul_of_nonneg_left hnorm_part
          have h2 : 0 ≤ (a + t * N) ^ (α - 1) := Real.rpow_nonneg hatN_nn _
          positivity
        linarith [hslope, hstep1, hstep2]
    linarith [hnorm_part, hrpow_part]
  -- Combine: for `t > 0`, `t*N² ≤ t*N + α(a+tN)^(α-1)(t*N)`.
  have hcombined : ∀ t : ℝ, 0 < t →
      N ≤ 1 + α * (a + t * N) ^ (α - 1) := by
    intro t ht
    have h1 := hsub_t t ht
    have h2 := hKt_bnd t ht
    have htN_pos : 0 < t * N := mul_pos ht hN_pos
    -- `t*N² ≤ t*N + α(a+tN)^(α-1)(t*N) = (t*N) * (1 + α(a+tN)^(α-1))`.
    have h3 : t * N ^ 2 ≤ (t * N) * (1 + α * (a + t * N) ^ (α - 1)) := by
      have : t * N + α * (a + t * N) ^ (α - 1) * (t * N)
          = (t * N) * (1 + α * (a + t * N) ^ (α - 1)) := by ring
      linarith [h1, h2, this]
    -- LHS `t*N² = (t*N)*N`.
    have hlhs : t * N ^ 2 = (t * N) * N := by ring
    rw [hlhs] at h3
    exact le_of_mul_le_mul_left h3 htN_pos
  -- Now take `t → 0⁺`. Use continuity of `t ↦ α(a + t*N)^(α-1)` at `0`.
  -- `g(0) = α * a^(α-1)`, and `RHS = 1 + g(0) < N`. Find `t` with `g(t) < N - 1`.
  set g : ℝ → ℝ := fun t => α * (a + t * N) ^ (α - 1) with hg_def
  have hg_cont : ContinuousAt g 0 := by
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.rpow_const
    · exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
    · exact Or.inr hα_sub_nn
  have hg0 : g 0 = α * a ^ (α - 1) := by simp [hg_def]
  -- `δ := N - RHS > 0`.
  have hδ_pos : 0 < N - RHS := by linarith [hcon]
  -- continuity: ∃ neighbourhood of 0 where `|g t - g 0| < δ`.
  have hbnd : ∀ᶠ t in nhds (0 : ℝ), |g t - g 0| < N - RHS := by
    have := hg_cont.tendsto
    have hmem : Set.Ioo (g 0 - (N - RHS)) (g 0 + (N - RHS)) ∈ nhds (g 0) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have := this hmem
    filter_upwards [this] with t htmem
    simp only [Set.mem_preimage, Set.mem_Ioo] at htmem
    rw [abs_lt]; constructor <;> linarith [htmem.1, htmem.2]
  -- Extract a positive `t` from the eventually statement.
  have hbnd' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), |g t - g 0| < N - RHS :=
    hbnd.filter_mono nhdsWithin_le_nhds
  have hpos_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < t :=
    eventually_mem_nhdsWithin.mono (fun t ht => ht)
  obtain ⟨t, htg, htpos⟩ := (hbnd'.and hpos_ev).exists
  -- For this `t`: `g t < g 0 + (N - RHS) = N - 1`.
  have hgt_lt : g t < N - 1 := by
    have h1 : g t - g 0 < N - RHS := (abs_lt.mp htg).2
    rw [hg0] at h1
    -- `RHS = 1 + α a^(α-1)`, so `N - RHS = N - 1 - α a^(α-1)`.
    rw [hRHSdef] at h1
    linarith [h1]
  -- But `hcombined t htpos : N ≤ 1 + g t`, contradiction.
  have hcomb := hcombined t htpos
  have : N ≤ 1 + g t := by rw [hg_def]; exact hcomb
  linarith [hgt_lt, this]

/-! ### Strict convexity on the Euclidean side

The paper's strict-convexity claim (line 1622) lives naturally on
`EuclideanSpace ℝ (Fin d)`. We prove it there
(`K_euclidean_strictlyConvex`), then transport via the linear
bijection `toEucl` to land on `Fin d → ℝ` as `K_strictlyConvex`. -/

/-- The paper's `K` realised on `EuclideanSpace ℝ (Fin d)`:
`K_euclidean v := ‖v‖_eucl + ‖v‖_eucl ^ α`. This is the *correct*
setting for the paper's strict-convexity claim — the inner-product
structure makes the norm strictly convex modulo same-ray. -/
noncomputable def K_euclidean (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖v‖ + ‖v‖ ^ h.α

@[simp] lemma K_euclidean_def
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : EuclideanSpace ℝ (Fin d)) :
    K_euclidean h v = ‖v‖ + ‖v‖ ^ h.α := rfl

/-! ### Strict convexity of `K_euclidean` (paper line 1622) -/

/-- Auxiliary: the map `r ↦ r ^ α` is strictly convex on `Ici 0` for
`α > 1`. -/
private lemma rpow_strictConvexOn (α : ℝ) (hα : 1 < α) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun r : ℝ => r ^ α) :=
  strictConvexOn_rpow hα

/-- Auxiliary: the map `r ↦ r ^ α` is convex on `Ici 0` for `α ≥ 1`. -/
private lemma rpow_convexOn (α : ℝ) (hα : 1 ≤ α) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun r : ℝ => r ^ α) :=
  convexOn_rpow hα

/-- Strict convexity of `‖·‖ ^ α` on `EuclideanSpace ℝ (Fin d)` for
`α > 1`. The proof splits on whether the two points are on the same
ray; in either case strict convexity follows from a combination of
the strict convexity of `r ↦ r^α` on `[0, ∞)` and the strict
convexity of the Euclidean norm modulo same-ray. -/
private lemma normPow_strictConvexOn_euclidean
    (h : HypothesisWeakGrowth (d := d) H DpH) :
    StrictConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
      (fun v => ‖v‖ ^ h.α) := by
  have hα_gt_one : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_gt_one
  have hα_nonneg : 0 ≤ h.α := le_of_lt hα_pos
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  -- Beta-reduce the goal.
  change ‖a • x + b • y‖ ^ h.α < a • ‖x‖ ^ h.α + b • ‖y‖ ^ h.α
  by_cases hsame : SameRay ℝ x y
  · -- Same ray, but `x ≠ y`. Then `‖x‖ ≠ ‖y‖`.
    have hnorm_ne : ‖x‖ ≠ ‖y‖ := by
      intro heq
      exact hxy (hsame.eq_of_norm_eq heq)
    have hsame_ab : SameRay ℝ (a • x) (b • y) :=
      (hsame.nonneg_smul_left ha.le).nonneg_smul_right hb.le
    have hnorm_eq : ‖a • x + b • y‖ = a * ‖x‖ + b * ‖y‖ := by
      have := hsame_ab.norm_add
      simp [norm_smul, Real.norm_of_nonneg ha.le,
            Real.norm_of_nonneg hb.le] at this
      linarith
    rw [hnorm_eq]
    have hx_nn : ‖x‖ ∈ Set.Ici (0 : ℝ) := norm_nonneg _
    have hy_nn : ‖y‖ ∈ Set.Ici (0 : ℝ) := norm_nonneg _
    have hsc := (rpow_strictConvexOn h.α hα_gt_one).2
      hx_nn hy_nn hnorm_ne ha hb hab
    simpa [smul_eq_mul] using hsc
  · -- Not same ray.
    have hsame_ab : ¬ SameRay ℝ (a • x) (b • y) := by
      intro hab_same
      apply hsame
      have ha_ne : a ≠ 0 := ne_of_gt ha
      have hb_ne : b ≠ 0 := ne_of_gt hb
      have := hab_same.nonneg_smul_left (a := a⁻¹) (inv_nonneg.mpr ha.le)
      have := this.nonneg_smul_right (a := b⁻¹) (inv_nonneg.mpr hb.le)
      rw [smul_smul, smul_smul, inv_mul_cancel₀ ha_ne, inv_mul_cancel₀ hb_ne,
          one_smul, one_smul] at this
      exact this
    have h_sup_strict : ‖a • x + b • y‖ < a * ‖x‖ + b * ‖y‖ := by
      have h_strict := norm_add_lt_of_not_sameRay hsame_ab
      have hax : ‖a • x‖ = a * ‖x‖ := by
        rw [norm_smul, Real.norm_of_nonneg ha.le]
      have hby : ‖b • y‖ = b * ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hb.le]
      linarith
    have h_n_nn : 0 ≤ ‖a • x + b • y‖ := norm_nonneg _
    have h_step1 : ‖a • x + b • y‖ ^ h.α < (a * ‖x‖ + b * ‖y‖) ^ h.α :=
      Real.rpow_lt_rpow h_n_nn h_sup_strict hα_pos
    have h_step2 : (a * ‖x‖ + b * ‖y‖) ^ h.α ≤
        a * ‖x‖ ^ h.α + b * ‖y‖ ^ h.α := by
      have hh := (rpow_convexOn h.α hα_gt_one.le).2
        (x := ‖x‖) (norm_nonneg _) (y := ‖y‖) (norm_nonneg _)
        ha.le hb.le hab
      simpa [smul_eq_mul] using hh
    have hfinal : ‖a • x + b • y‖ ^ h.α < a * ‖x‖ ^ h.α + b * ‖y‖ ^ h.α :=
      lt_of_lt_of_le h_step1 h_step2
    simpa [smul_eq_mul] using hfinal

/-- **Paper line 1622, Euclidean form.** Strict convexity of
`K_euclidean(v) = ‖v‖ + ‖v‖^α` on `EuclideanSpace ℝ (Fin d)` for
`α > 1`. The paper-faithful kernel uses the Euclidean (L²) norm. -/
theorem K_euclidean_strictlyConvex (h : HypothesisWeakGrowth (d := d) H DpH) :
    StrictConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
      (K_euclidean h) := by
  -- `K_euclidean = (‖·‖) + (‖·‖^α)`; the first is convex, the
  -- second is strictly convex.
  have h_norm_convex :
      ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) norm :=
    convexOn_univ_norm
  have h_rpow_strict := normPow_strictConvexOn_euclidean (h := h)
  -- Strict + convex = strict (sum order).
  have hsum := h_rpow_strict.add_convexOn h_norm_convex
  -- Massage the sum form: `(‖·‖^α) + ‖·‖ = ‖·‖ + ‖·‖^α`.
  convert hsum using 1
  ext v
  simp [K_euclidean, add_comm]

/-- The function `K_euclidean ∘ toEucl : (Fin d → ℝ) → ℝ`. This is the
paper-faithful kernel viewed on the sup-norm carrier `Fin d → ℝ`: it
agrees with `K` only on the formula, but uses the Euclidean norm
internally. -/
noncomputable def K_paper (h : HypothesisWeakGrowth (d := d) H DpH)
    (q : Fin d → ℝ) : ℝ :=
  K_euclidean h (toEucl q)

@[simp] lemma K_paper_def
    (h : HypothesisWeakGrowth (d := d) H DpH) (q : Fin d → ℝ) :
    K_paper h q = ‖toEucl q‖ + ‖toEucl q‖ ^ h.α := rfl

/-- The paper-faithful kernel `K_paper := K_euclidean ∘ toEucl` is
**strictly convex** on `(Fin d → ℝ)`. This is the paper's line-1622
claim, transported via the linear bijection `toEucl`. -/
theorem K_paper_strictlyConvex (h : HypothesisWeakGrowth (d := d) H DpH) :
    StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (K_paper h) := by
  have h_eucl := K_euclidean_strictlyConvex (h := h)
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have h_te_ne : toEucl x ≠ toEucl y := fun heq => hxy (toEucl_injective heq)
  have h_strict := h_eucl.2 (Set.mem_univ (toEucl x)) (Set.mem_univ (toEucl y))
    h_te_ne ha hb hab
  have h_lin : toEucl (a • x + b • y) = a • toEucl x + b • toEucl y := by
    simp [toEucl_add, toEucl_smul]
  change K_euclidean h (toEucl (a • x + b • y))
    < a • K_euclidean h (toEucl x) + b • K_euclidean h (toEucl y)
  rw [h_lin]
  exact h_strict

/-- **`K` equals `K_paper`** — `K` is now defined via the Euclidean
norm, matching `K_paper := K_euclidean ∘ toEucl` definitionally. -/
lemma K_eq_K_paper (h : HypothesisWeakGrowth (d := d) H DpH) :
    K h = K_paper h := rfl

/-- **Paper line 1622, sup-norm carrier form.** Strict convexity of
the `K` kernel on `Fin d → ℝ`, transported from the Euclidean form via
`toEucl`. The Euclidean norm inside `K` is what makes this work — the
sup-norm form `‖q‖_sup + ‖q‖_sup^α` would *not* be strictly convex. -/
theorem K_strictlyConvex (h : HypothesisWeakGrowth (d := d) H DpH) :
    StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (K h) := by
  rw [K_eq_K_paper]
  exact K_paper_strictlyConvex h

/-! ### Sup-norm polynomial upper bound on `K`

The Euclidean version of `K` is bounded above by a `(d,α)`-dependent
polynomial in the sup-norm. This is used in `InfConv.lean` to derive
upper bounds on `Hdelta` from `K h p`. -/

/-- Young-style helper: for `1 ≤ α` and `t ≥ 0`, we have
`t ≤ t^α + 1`. (Same as in `InfConv.lean`, replicated here to avoid
circularity.) -/
private lemma kernel_norm_le_rpow_add_one
    {α t : ℝ} (hα : 1 ≤ α) (ht : 0 ≤ t) :
    t ≤ t ^ α + 1 := by
  rcases lt_or_ge t 1 with ht1 | ht1
  · have hpow_nn : 0 ≤ t ^ α := Real.rpow_nonneg ht _
    linarith
  · have ht_ge_one : 1 ≤ t := ht1
    have hmono : t ^ (1 : ℝ) ≤ t ^ α :=
      Real.rpow_le_rpow_of_exponent_le ht_ge_one hα
    have hrpow_one : t ^ (1 : ℝ) = t := Real.rpow_one t
    have hmono' : t ≤ t ^ α := by
      calc t = t ^ (1 : ℝ) := hrpow_one.symm
        _ ≤ t ^ α := hmono
    have h_step : t ^ α ≤ t ^ α + 1 := by linarith
    exact le_trans hmono' h_step

/-- The dimension/exponent-dependent constant `Cα,d := √d^α + √d + 1`
appearing in the sup-norm upper bound on `K`. Hard-coded as a real
constant (not unfolded). -/
noncomputable def K_sup_const (h : HypothesisWeakGrowth (d := d) H DpH) : ℝ :=
  (Real.sqrt d) ^ h.α + Real.sqrt d + 1

lemma K_sup_const_nonneg (h : HypothesisWeakGrowth (d := d) H DpH) :
    0 ≤ K_sup_const (d := d) h := by
  unfold K_sup_const
  have h1 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (Real.sqrt d) ^ h.α := Real.rpow_nonneg h1 _
  linarith

/-- **Sup-norm polynomial bound.** Bounds `K h p` by a constant times
`‖p‖_sup^α` plus a constant. Concretely:
`K h p ≤ (√d^α + √d) * ‖p‖^α + (√d + 1)` — bounded by
`K_sup_const h * (‖p‖^α + 1)`. -/
lemma K_le_sup_polynomial (h : HypothesisWeakGrowth (d := d) H DpH)
    (p : Fin d → ℝ) :
    K h p ≤ K_sup_const (d := d) h * (‖p‖ ^ h.α + 1) := by
  unfold K K_sup_const
  have hα_ge_one : (1 : ℝ) ≤ h.α := le_of_lt h.hα
  have hα_nn : (0 : ℝ) ≤ h.α := le_of_lt (lt_trans zero_lt_one h.hα)
  have hp_nn : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
  have hsqrtd_nn : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsqrtd_α_nn : (0 : ℝ) ≤ (Real.sqrt d) ^ h.α := Real.rpow_nonneg hsqrtd_nn _
  -- `‖toEucl p‖ ≤ √d * ‖p‖`.
  have h_eucl_le : ‖toEucl p‖ ≤ Real.sqrt d * ‖p‖ := eucl_norm_le_sqrt_d_sup_norm p
  have h_eucl_nn : (0 : ℝ) ≤ ‖toEucl p‖ := norm_nonneg _
  -- `‖toEucl p‖^α ≤ (√d * ‖p‖)^α = (√d)^α * ‖p‖^α`.
  have h_eucl_α_le : ‖toEucl p‖ ^ h.α ≤ (Real.sqrt d) ^ h.α * ‖p‖ ^ h.α := by
    have step1 : ‖toEucl p‖ ^ h.α ≤ (Real.sqrt d * ‖p‖) ^ h.α :=
      Real.rpow_le_rpow h_eucl_nn h_eucl_le hα_nn
    have step2 : (Real.sqrt d * ‖p‖) ^ h.α =
        (Real.sqrt d) ^ h.α * ‖p‖ ^ h.α :=
      Real.mul_rpow hsqrtd_nn hp_nn
    rw [step2] at step1
    exact step1
  -- `‖toEucl p‖ ≤ √d * ‖p‖ ≤ √d * (‖p‖^α + 1)` by Young.
  have h_young : ‖p‖ ≤ ‖p‖ ^ h.α + 1 :=
    kernel_norm_le_rpow_add_one hα_ge_one hp_nn
  have h_eucl_le_young : ‖toEucl p‖ ≤ Real.sqrt d * (‖p‖ ^ h.α + 1) := by
    have := mul_le_mul_of_nonneg_left h_young hsqrtd_nn
    exact h_eucl_le.trans this
  -- Combine: K = ‖toEucl p‖ + ‖toEucl p‖^α
  --   ≤ √d * (‖p‖^α + 1) + (√d)^α * ‖p‖^α
  --   ≤ (√d^α + √d) * ‖p‖^α + √d
  --   ≤ (√d^α + √d + 1) * (‖p‖^α + 1).
  have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg hp_nn _
  nlinarith [h_eucl_le_young, h_eucl_α_le, hpα_nn, hsqrtd_nn, hsqrtd_α_nn]

/-! ### Legendre transform `K̂` of `K`

Paper: `Source/FGU-monotone_revised.tex` line 1668 — the Fenchel
conjugate

  `K̂(v) := sup_q { q ⬝ v - K(q) }`,

with `q ⬝ v := ∑ i, q i * v i`. The basic convex-analysis properties
land here; smoothness of `K̂` (paper line 1670) is deferred to a
separate task once strict convexity of `K` is in. -/

/-- The pairing `q ⬝ v` is bounded by `d · ‖q‖ · ‖v‖`. With the
sup-norm on `Fin d → ℝ`, each term `q i * v i ≤ ‖q‖ * ‖v‖`, and there
are `d` summands. -/
private lemma euclideanDot_le_card_mul_norm
    (q v : Fin d → ℝ) :
    q ⬝ v ≤ d * ‖q‖ * ‖v‖ := by
  unfold dotProduct
  have h_each : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      q i * v i ≤ ‖q‖ * ‖v‖ := by
    intro i _
    have h1 : q i * v i ≤ |q i * v i| := le_abs_self _
    have h2 : |q i * v i| = |q i| * |v i| := abs_mul _ _
    have hqi : |q i| ≤ ‖q‖ := by
      have := norm_le_pi_norm q i
      simpa [Real.norm_eq_abs] using this
    have hvi : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      simpa [Real.norm_eq_abs] using this
    have hqi_nn : 0 ≤ |q i| := abs_nonneg _
    have hv_nn : 0 ≤ ‖v‖ := norm_nonneg _
    calc q i * v i ≤ |q i * v i| := h1
      _ = |q i| * |v i| := h2
      _ ≤ ‖q‖ * |v i| := by
            exact mul_le_mul_of_nonneg_right hqi (abs_nonneg _)
      _ ≤ ‖q‖ * ‖v‖ :=
            mul_le_mul_of_nonneg_left hvi (norm_nonneg _)
  have h_sum :
      (∑ i, q i * v i) ≤ ∑ _ : Fin d, ‖q‖ * ‖v‖ :=
    Finset.sum_le_sum h_each
  have h_card :
      (∑ _ : Fin d, ‖q‖ * ‖v‖) = (d : ℝ) * (‖q‖ * ‖v‖) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc (∑ i, q i * v i) ≤ ∑ _ : Fin d, ‖q‖ * ‖v‖ := h_sum
    _ = (d : ℝ) * (‖q‖ * ‖v‖) := h_card
    _ = (d : ℝ) * ‖q‖ * ‖v‖ := by ring

/-- The Legendre transform (Fenchel conjugate) of `K`:
`K̂(v) := sup_q { q ⬝ v - K(q) }`, paper line 1668–1669. -/
noncomputable def Khat (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : Fin d → ℝ) : ℝ :=
  ⨆ q : Fin d → ℝ, q ⬝ v - K h q

/-- The set of values `q ⬝ v - K h q` is bounded above. Combine
`q ⬝ v ≤ d ‖q‖ ‖v‖` with the coercive lower bound `‖q‖^α ≤ K h q`,
then split on `‖q‖ ≤ R` versus `‖q‖ > R` for a suitable threshold
`R := max ((d ‖v‖ + 1)^{1/(α-1)}) 1`. -/
lemma Khat_bddAbove (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : Fin d → ℝ) :
    BddAbove (Set.range fun q : Fin d → ℝ => q ⬝ v - K h q) := by
  classical
  set α : ℝ := h.α with hαdef
  have hα_gt_one : 1 < α := h.hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_sub_one_pos : 0 < α - 1 := sub_pos.mpr hα_gt_one
  set M : ℝ := (d : ℝ) * ‖v‖ with hMdef
  have hM_nn : 0 ≤ M := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
    exact mul_nonneg hd (norm_nonneg _)
  -- Threshold `R := max ((M+1)^(1/(α-1))) 1`.
  have hM1_pos : 0 < M + 1 := by linarith
  set R : ℝ := max ((M + 1) ^ (1 / (α - 1))) 1 with hRdef
  have hR_ge_one : 1 ≤ R := le_max_right _ _
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
  -- The bound `B := M * R`, the goal is to show `f q ≤ B` for all q.
  set B : ℝ := M * R with hBdef
  refine ⟨B, ?_⟩
  rintro y ⟨q, rfl⟩
  -- We have `q ⬝ v ≤ M * ‖q‖` and `K h q ≥ ‖q‖^α`.
  have hpair : q ⬝ v ≤ M * ‖q‖ := by
    have := euclideanDot_le_card_mul_norm (d := d) q v
    -- `(d : ℝ) * ‖q‖ * ‖v‖ = M * ‖q‖`.
    have hrw : (d : ℝ) * ‖q‖ * ‖v‖ = M * ‖q‖ := by
      simp [hMdef]; ring
    linarith [hrw]
  have hK_ge : ‖q‖ ^ α ≤ K h q := K_ge_rpow h q
  have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
  -- Case split on ‖q‖ ≤ R versus ‖q‖ > R.
  by_cases hcase : ‖q‖ ≤ R
  · -- For ‖q‖ ≤ R: use `q ⬝ v ≤ M * ‖q‖ ≤ M * R = B`, and
    -- `K h q ≥ ‖q‖^α ≥ 0`, so `q ⬝ v - K h q ≤ M * R = B`.
    have hKq_nn : 0 ≤ K h q := K_nonneg h q
    have h1 : M * ‖q‖ ≤ M * R := mul_le_mul_of_nonneg_left hcase hM_nn
    linarith
  · -- For ‖q‖ > R ≥ 1: ‖q‖^(α-1) ≥ R^(α-1) ≥ ((M+1)^(1/(α-1)))^(α-1) = M+1,
    -- so ‖q‖^α = ‖q‖^(α-1) * ‖q‖ ≥ (M+1) * ‖q‖ = M*‖q‖ + ‖q‖.
    -- Thus q ⬝ v - K h q ≤ M*‖q‖ - ‖q‖^α ≤ -‖q‖ ≤ 0 ≤ B (since M, R ≥ 0).
    have hcase : R < ‖q‖ := lt_of_not_ge hcase
    have hq_pos : 0 < ‖q‖ := lt_of_lt_of_le hR_pos (le_of_lt hcase)
    -- ‖q‖^(α-1) ≥ R^(α-1).
    have h_rpow_le_R :
        R ^ (α - 1) ≤ ‖q‖ ^ (α - 1) :=
      Real.rpow_le_rpow (le_of_lt hR_pos) (le_of_lt hcase) (le_of_lt hα_sub_one_pos)
    -- R^(α-1) ≥ ((M+1)^(1/(α-1)))^(α-1) = M + 1.
    have hbase_pos : 0 < (M + 1) ^ (1 / (α - 1)) :=
      Real.rpow_pos_of_pos hM1_pos _
    have h_M1_le_Rpow : M + 1 ≤ R ^ (α - 1) := by
      have h_left :
          ((M + 1) ^ (1 / (α - 1))) ≤ R := le_max_left _ _
      have hstep :
          ((M + 1) ^ (1 / (α - 1))) ^ (α - 1) ≤ R ^ (α - 1) :=
        Real.rpow_le_rpow (le_of_lt hbase_pos) h_left (le_of_lt hα_sub_one_pos)
      -- Simplify `((M+1)^(1/(α-1)))^(α-1) = (M+1)`.
      have hsimp :
          ((M + 1) ^ (1 / (α - 1))) ^ (α - 1) = M + 1 := by
        rw [← Real.rpow_mul (le_of_lt hM1_pos)]
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hα_sub_one_pos), Real.rpow_one]
      linarith
    -- ‖q‖^(α-1) ≥ M + 1.
    have h_pow_ge : M + 1 ≤ ‖q‖ ^ (α - 1) :=
      le_trans h_M1_le_Rpow h_rpow_le_R
    -- ‖q‖^α = ‖q‖^(α-1) * ‖q‖ ≥ (M + 1) * ‖q‖ = M * ‖q‖ + ‖q‖.
    have hα_split : α = (α - 1) + 1 := by ring
    have hpow_eq : ‖q‖ ^ α = ‖q‖ ^ (α - 1) * ‖q‖ := by
      conv_lhs => rw [hα_split]
      rw [Real.rpow_add hq_pos, Real.rpow_one]
    have h_normα_ge : (M + 1) * ‖q‖ ≤ ‖q‖ ^ α := by
      rw [hpow_eq]
      exact mul_le_mul_of_nonneg_right h_pow_ge hq_nn
    -- q ⬝ v - K h q ≤ M*‖q‖ - ‖q‖^α ≤ M*‖q‖ - (M+1)*‖q‖ = -‖q‖ ≤ 0.
    have h_le_zero : q ⬝ v - K h q ≤ 0 := by
      have : q ⬝ v - K h q ≤ M * ‖q‖ - ‖q‖ ^ α := by linarith
      have hneg : M * ‖q‖ - ‖q‖ ^ α ≤ -‖q‖ := by
        have : M * ‖q‖ - (M + 1) * ‖q‖ = -‖q‖ := by ring
        linarith
      have : q ⬝ v - K h q ≤ -‖q‖ := le_trans ‹_› hneg
      linarith
    have hB_nn : 0 ≤ B := by
      have : 0 ≤ M * R := mul_nonneg hM_nn (le_of_lt hR_pos)
      simpa [hBdef] using this
    linarith

/-- The auxiliary slice `v ↦ q ⬝ v - K h q` is continuous (it is
affine in `v`). -/
private lemma slice_continuous
    (h : HypothesisWeakGrowth (d := d) H DpH) (q : Fin d → ℝ) :
    Continuous (fun v : Fin d → ℝ => q ⬝ v - K h q) := by
  -- `q ⬝ v` is `∑ i, q i * v i`, continuous in `v`. Subtract a constant.
  have h_dot : Continuous (fun v : Fin d → ℝ => q ⬝ v) := by
    unfold dotProduct
    refine continuous_finset_sum _ ?_
    intro i _
    exact (continuous_const).mul (continuous_apply i)
  exact h_dot.sub continuous_const

/-- **Convexity of `K̂`.** Each slice `v ↦ q ⬝ v - K h q` is affine,
hence convex; the pointwise iSup of convex functions is convex. -/
theorem Khat_convex (h : HypothesisWeakGrowth (d := d) H DpH) :
    ConvexOn ℝ Set.univ (Khat h) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  -- Goal: Khat h (a • v + b • w) ≤ a • Khat h v + b • Khat h w.
  -- Using ciSup_le, reduce to showing each slice value at `a•v + b•w` is
  -- ≤ a * Khat h v + b * Khat h w.
  apply ciSup_le
  intro q
  -- The pairing is bilinear, so q ⬝ (a•v + b•w) = a*(q⬝v) + b*(q⬝w).
  have hpair :
      q ⬝ (a • v + b • w) = a * (q ⬝ v) + b * (q ⬝ w) := by
    unfold dotProduct
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> · apply Finset.sum_congr rfl; intro i _; ring
  -- Rewrite K h q with `a + b = 1`: K h q = (a + b) * K h q = a*Kq + b*Kq.
  have hKq_decomp : K h q = a * K h q + b * K h q := by
    have : (a + b) * K h q = a * K h q + b * K h q := by ring
    have : (1 : ℝ) * K h q = a * K h q + b * K h q := by
      rw [← hab]; ring
    linarith
  -- Bound each piece by Khat at `v` and `w` respectively.
  have hsliceV : q ⬝ v - K h q ≤ Khat h v := by
    apply le_ciSup (Khat_bddAbove h v) q
  have hsliceW : q ⬝ w - K h q ≤ Khat h w := by
    apply le_ciSup (Khat_bddAbove h w) q
  -- Combine.
  have hmul_v : a * (q ⬝ v - K h q) ≤ a * Khat h v :=
    mul_le_mul_of_nonneg_left hsliceV ha
  have hmul_w : b * (q ⬝ w - K h q) ≤ b * Khat h w :=
    mul_le_mul_of_nonneg_left hsliceW hb
  -- Goal: q ⬝ (a • v + b • w) - K h q ≤ a • Khat h v + b • Khat h w.
  -- The smul on ℝ is multiplication.
  change q ⬝ (a • v + b • w) - K h q ≤ a • Khat h v + b • Khat h w
  rw [hpair, hKq_decomp]
  have hgoal :
      (a * (q ⬝ v) + b * (q ⬝ w)) - (a * K h q + b * K h q)
        = a * (q ⬝ v - K h q) + b * (q ⬝ w - K h q) := by ring
  rw [hgoal]
  simp only [smul_eq_mul]
  linarith

/-- **Lower semicontinuity of `K̂`.** Each slice `v ↦ q ⬝ v - K h q`
is continuous (affine), and the pointwise iSup of continuous (hence
LSC) functions is LSC. We use Mathlib's `lowerSemicontinuous_ciSup`,
applying `Khat_bddAbove` to discharge the `BddAbove` hypothesis. -/
theorem Khat_lsc (h : HypothesisWeakGrowth (d := d) H DpH) :
    LowerSemicontinuous (Khat h) := by
  unfold Khat
  apply lowerSemicontinuous_ciSup
  · intro v
    exact Khat_bddAbove h v
  · intro q
    exact (slice_continuous h q).lowerSemicontinuous

/-! ### Existence and uniqueness of the `K̂` argmax (`DKhat`)

We define `DKhat h v` as the **unique maximiser** of
`q ↦ q ⬝ v - K h q`. Existence follows from coercivity of `K`
(the supremand is `≤ 0` outside a large closed ball) plus
compactness of closed balls in `Fin d → ℝ` (finite-dimensional /
proper). Uniqueness follows from strict convexity of `K`
(`K_strictlyConvex`).

`DKhat` is consumed by the C¹ regularity of `K̂` (paper line 1670)
via the semi-explicit formula `q^ε = p - (M^ε_{x,m})^{-1}(p)`
(`paper:lem:inf-conv-props.ii`). Continuity and differentiability
of `DKhat` / `K̂` are deferred to sibling tasks
`infra-P6-Khat-C1-B-DKhat-continuous` and
`infra-P6-Khat-C1-C-Khat-differentiable`. -/

/-- The supremand of `K̂`: `f_v(q) := q ⬝ v - K h q`. -/
noncomputable def palomar_Kernel_Khat_supremand
    (h : HypothesisWeakGrowth (d := d) H DpH) (v q : Fin d → ℝ) : ℝ :=
  q ⬝ v - K h q

/-- For `‖q‖` greater than the threshold `R` of `Khat_bddAbove`, the
supremand is `≤ 0`. The proof reuses the coercive-tail estimate from
`Khat_bddAbove`. -/
private lemma Khat_supremand_nonpos_of_large_norm
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ q : Fin d → ℝ, R < ‖q‖ → palomar_Kernel_Khat_supremand h v q ≤ 0 := by
  classical
  set α : ℝ := h.α with hαdef
  have hα_gt_one : 1 < α := h.hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_sub_one_pos : 0 < α - 1 := sub_pos.mpr hα_gt_one
  set M : ℝ := (d : ℝ) * ‖v‖ with hMdef
  have hM_nn : 0 ≤ M := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
    exact mul_nonneg hd (norm_nonneg _)
  have hM1_pos : 0 < M + 1 := by linarith
  set R : ℝ := max ((M + 1) ^ (1 / (α - 1))) 1 with hRdef
  have hR_ge_one : 1 ≤ R := le_max_right _ _
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
  refine ⟨R, hR_pos, ?_⟩
  intro q hcase
  -- Re-derive the inequality `q ⬝ v - K h q ≤ -‖q‖ ≤ 0` from
  -- `Khat_bddAbove`'s `R < ‖q‖` branch.
  have hpair : q ⬝ v ≤ M * ‖q‖ := by
    have hbnd := euclideanDot_le_card_mul_norm (d := d) q v
    have hrw : (d : ℝ) * ‖q‖ * ‖v‖ = M * ‖q‖ := by
      simp [hMdef]; ring
    linarith [hrw]
  have hK_ge : ‖q‖ ^ α ≤ K h q := K_ge_rpow h q
  have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
  have hq_pos : 0 < ‖q‖ := lt_of_lt_of_le hR_pos (le_of_lt hcase)
  have h_rpow_le_R : R ^ (α - 1) ≤ ‖q‖ ^ (α - 1) :=
    Real.rpow_le_rpow (le_of_lt hR_pos) (le_of_lt hcase) (le_of_lt hα_sub_one_pos)
  have hbase_pos : 0 < (M + 1) ^ (1 / (α - 1)) :=
    Real.rpow_pos_of_pos hM1_pos _
  have h_M1_le_Rpow : M + 1 ≤ R ^ (α - 1) := by
    have h_left : ((M + 1) ^ (1 / (α - 1))) ≤ R := le_max_left _ _
    have hstep :
        ((M + 1) ^ (1 / (α - 1))) ^ (α - 1) ≤ R ^ (α - 1) :=
      Real.rpow_le_rpow (le_of_lt hbase_pos) h_left (le_of_lt hα_sub_one_pos)
    have hsimp : ((M + 1) ^ (1 / (α - 1))) ^ (α - 1) = M + 1 := by
      rw [← Real.rpow_mul (le_of_lt hM1_pos)]
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hα_sub_one_pos), Real.rpow_one]
    linarith
  have h_pow_ge : M + 1 ≤ ‖q‖ ^ (α - 1) :=
    le_trans h_M1_le_Rpow h_rpow_le_R
  have hα_split : α = (α - 1) + 1 := by ring
  have hpow_eq : ‖q‖ ^ α = ‖q‖ ^ (α - 1) * ‖q‖ := by
    conv_lhs => rw [hα_split]
    rw [Real.rpow_add hq_pos, Real.rpow_one]
  have h_normα_ge : (M + 1) * ‖q‖ ≤ ‖q‖ ^ α := by
    rw [hpow_eq]
    exact mul_le_mul_of_nonneg_right h_pow_ge hq_nn
  -- palomar_Kernel_Khat_supremand h v q = q ⬝ v - K h q ≤ M*‖q‖ - ‖q‖^α ≤ -‖q‖ ≤ 0.
  unfold palomar_Kernel_Khat_supremand
  have h1 : q ⬝ v - K h q ≤ M * ‖q‖ - ‖q‖ ^ α := by linarith
  have hneg : M * ‖q‖ - ‖q‖ ^ α ≤ -‖q‖ := by
    have : M * ‖q‖ - (M + 1) * ‖q‖ = -‖q‖ := by ring
    linarith
  linarith

/-- The supremand `palomar_Kernel_Khat_supremand h v` is continuous in `q`
(affine + a continuous penalty). -/
private lemma Khat_supremand_continuous
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    Continuous (palomar_Kernel_Khat_supremand h v) := by
  unfold palomar_Kernel_Khat_supremand
  have h_dot : Continuous (fun q : Fin d → ℝ => q ⬝ v) := by
    unfold dotProduct
    refine continuous_finset_sum _ ?_
    intro i _
    exact (continuous_apply i).mul continuous_const
  exact h_dot.sub (K_continuous h)

/-- **Existence of the `K̂` argmax.** For every `v`, there exists a
`q₀` realising the supremum `Khat h v = sup_q (q ⬝ v - K h q)`.
The argument: outside a large closed ball, the supremand is
non-positive (and equals `0` at `q = 0`); on the ball it attains
its max by compactness + continuity. -/
theorem Khat_isMaxOn_exists
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    ∃ q₀ : Fin d → ℝ, IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ q₀ := by
  classical
  obtain ⟨R, hR_pos, hR_tail⟩ := Khat_supremand_nonpos_of_large_norm h v
  -- Closed ball is compact in the proper space `Fin d → ℝ`.
  have h_compact : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
    isCompact_closedBall (0 : Fin d → ℝ) R
  have h_ne : (Metric.closedBall (0 : Fin d → ℝ) R).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (le_of_lt hR_pos)⟩
  have h_cont_on : ContinuousOn (palomar_Kernel_Khat_supremand h v)
      (Metric.closedBall (0 : Fin d → ℝ) R) :=
    (Khat_supremand_continuous h v).continuousOn
  obtain ⟨q₀, hq₀_mem, hq₀_max⟩ :=
    h_compact.exists_isMaxOn h_ne h_cont_on
  refine ⟨q₀, ?_⟩
  -- Extend the max from the closed ball to `Set.univ`.
  intro q _hq
  by_cases hcase : ‖q‖ ≤ R
  · -- `q ∈ closedBall 0 R`.
    have : q ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hcase
    exact hq₀_max this
  · -- `‖q‖ > R`: supremand at q is ≤ 0, and supremand at q₀ ≥ supremand at 0 = 0.
    have hq_R : R < ‖q‖ := lt_of_not_ge hcase
    have h_q_le : palomar_Kernel_Khat_supremand h v q ≤ 0 := hR_tail q hq_R
    have h_zero_mem : (0 : Fin d → ℝ) ∈ Metric.closedBall (0 : Fin d → ℝ) R :=
      Metric.mem_closedBall_self (le_of_lt hR_pos)
    have h_zero_val : palomar_Kernel_Khat_supremand h v 0 = 0 := by
      unfold palomar_Kernel_Khat_supremand dotProduct
      simp [K_zero h]
    have h_q₀_ge_zero : 0 ≤ palomar_Kernel_Khat_supremand h v q₀ := by
      have h_zero_le : palomar_Kernel_Khat_supremand h v 0 ≤ palomar_Kernel_Khat_supremand h v q₀ :=
        hq₀_max h_zero_mem
      linarith [h_zero_le, h_zero_val]
    -- Goal: `q ∈ {x | palomar_Kernel_Khat_supremand h v x ≤ palomar_Kernel_Khat_supremand h v q₀}`.
    -- We have `q-val ≤ 0 ≤ q₀-val`.
    change palomar_Kernel_Khat_supremand h v q ≤ palomar_Kernel_Khat_supremand h v q₀
    linarith

/-- **The argmax `DKhat`.** Defined as a (Classical) choice of the
maximiser of `q ↦ q ⬝ v - K h q`. By `K_strictlyConvex`, this
choice is in fact unique (`DKhat_unique`). -/
noncomputable def DKhat (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : Fin d → ℝ) : Fin d → ℝ :=
  Classical.choose (Khat_isMaxOn_exists h v)

/-- The defining property of `DKhat`: it is a maximiser of the
supremand `q ↦ q ⬝ v - K h q`. -/
theorem DKhat_isMaxOn (h : HypothesisWeakGrowth (d := d) H DpH)
    (v : Fin d → ℝ) :
    IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ (DKhat h v) :=
  Classical.choose_spec (Khat_isMaxOn_exists h v)

/-- For every `q`, `q ⬝ v - K h q ≤ (DKhat h v) ⬝ v - K h (DKhat h v)`.
This is the unfolded form of `DKhat_isMaxOn`. -/
lemma DKhat_le_supremand
    (h : HypothesisWeakGrowth (d := d) H DpH) (v q : Fin d → ℝ) :
    q ⬝ v - K h q ≤ DKhat h v ⬝ v - K h (DKhat h v) :=
  DKhat_isMaxOn h v (Set.mem_univ q)

/-- **Strict convexity of the negated supremand.** The function
`q ↦ K h q - q ⬝ v` is strictly convex on `Set.univ`, because it is
the sum of a strictly convex function (`K`) and a linear (hence
convex) function `q ↦ -(q ⬝ v)`. This is the key tool for
uniqueness of `DKhat`. -/
private lemma negSupremand_strictConvexOn
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q => K h q - q ⬝ v) := by
  -- `(K h) + (q ↦ -(q ⬝ v)) = (q ↦ K h q - q ⬝ v)` modulo a sign.
  have hK_sc := K_strictlyConvex h
  -- `q ↦ -(q ⬝ v)` is linear, hence convex on `univ`.
  have h_lin_convex :
      ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (fun q => -(q ⬝ v)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _hab
    -- The function `q ↦ -(q ⬝ v)` is linear, hence we have equality
    -- (not just `≤`). Reduce to a pointwise computation.
    change -((a • x + b • y) ⬝ v) ≤ a • -(x ⬝ v) + b • -(y ⬝ v)
    unfold dotProduct
    simp only [smul_eq_mul]
    -- Both sides as a sum over `i`.
    have hkey : ∀ i : Fin d,
        -((a • x + b • y) i * v i) =
          a * -(x i * v i) + b * -(y i * v i) := by
      intro i
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h_eq :
        -∑ i, (a • x + b • y) i * v i =
          a * -∑ i, x i * v i + b * -∑ i, y i * v i := by
      rw [← Finset.sum_neg_distrib]
      have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hkey i)
      rw [this]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    linarith
  -- Strict + convex = strict.
  have hsum := hK_sc.add_convexOn h_lin_convex
  -- Massage form: `K h q + -(q ⬝ v) = K h q - q ⬝ v`.
  have hext : (fun q : Fin d → ℝ => K h q - q ⬝ v) =
      fun q : Fin d → ℝ => K h q + -(q ⬝ v) := by
    funext q; ring
  rw [hext]
  exact hsum

/-- **Uniqueness of `DKhat`.** If `q₁` and `q₂` both maximise
`q ↦ q ⬝ v - K h q`, they are equal. The proof: `q ↦ K h q - q ⬝ v`
is strictly convex (`negSupremand_strictConvexOn`), and `IsMaxOn`
of `f` is `IsMinOn` of `-f`. Apply `StrictConvexOn.eq_of_isMinOn`. -/
theorem DKhat_unique
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ)
    {q₁ q₂ : Fin d → ℝ}
    (hq₁ : IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ q₁)
    (hq₂ : IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ q₂) :
    q₁ = q₂ := by
  -- Reframe: `IsMaxOn (palomar_Kernel_Khat_supremand h v) = IsMinOn (fun q => K h q - q ⬝ v)`.
  have h_neg : ∀ q, -(palomar_Kernel_Khat_supremand h v q) = K h q - q ⬝ v := by
    intro q
    unfold palomar_Kernel_Khat_supremand
    ring
  have hq₁_min : IsMinOn (fun q => K h q - q ⬝ v) Set.univ q₁ := by
    intro q _
    change K h q₁ - q₁ ⬝ v ≤ K h q - q ⬝ v
    have hh : palomar_Kernel_Khat_supremand h v q ≤ palomar_Kernel_Khat_supremand h v q₁ :=
      hq₁ (Set.mem_univ q)
    unfold palomar_Kernel_Khat_supremand at hh
    linarith
  have hq₂_min : IsMinOn (fun q => K h q - q ⬝ v) Set.univ q₂ := by
    intro q _
    change K h q₂ - q₂ ⬝ v ≤ K h q - q ⬝ v
    have hh : palomar_Kernel_Khat_supremand h v q ≤ palomar_Kernel_Khat_supremand h v q₂ :=
      hq₂ (Set.mem_univ q)
    unfold palomar_Kernel_Khat_supremand at hh
    linarith
  exact (negSupremand_strictConvexOn h v).eq_of_isMinOn
    hq₁_min hq₂_min (Set.mem_univ _) (Set.mem_univ _)

/-- **Public uniqueness lemma for the supremand.** If `q` satisfies the
pointwise inequality `∀ r, r ⬝ v − K h r ≤ q ⬝ v − K h q`
(i.e. `q` is a maximiser of the supremand
`r ↦ r ⬝ v − K h r`), then `q = DKhat h v`. This is the externally
usable form of `DKhat_unique`, which is internally stated with the
private `palomar_Kernel_Khat_supremand` alias. -/
theorem DKhat_eq_of_isMaxOn
    (h : HypothesisWeakGrowth (d := d) H DpH) (v q : Fin d → ℝ)
    (hq : ∀ r : Fin d → ℝ, r ⬝ v - K h r ≤ q ⬝ v - K h q) :
    q = DKhat h v := by
  -- Recast `hq` as `IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ q`.
  have hq_max : IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ q := by
    intro r _
    -- `palomar_Kernel_Khat_supremand h v r = r ⬝ v − K h r` definitionally.
    change r ⬝ v - K h r ≤ q ⬝ v - K h q
    exact hq r
  -- Apply uniqueness against the `DKhat_isMaxOn` certificate.
  exact DKhat_unique h v hq_max (DKhat_isMaxOn h v)

/-- **Headline identity.** `K̂(v)` equals the supremand value at the
unique argmax `DKhat h v`. -/
theorem Khat_eq_at_DKhat
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    Khat h v = DKhat h v ⬝ v - K h (DKhat h v) := by
  unfold Khat
  apply le_antisymm
  · -- `⨆ q, (q ⬝ v - K h q) ≤ DKhat h v ⬝ v - K h (DKhat h v)`.
    apply ciSup_le
    intro q
    exact DKhat_le_supremand h v q
  · -- `DKhat h v ⬝ v - K h (DKhat h v) ≤ ⨆ q, (q ⬝ v - K h q)`.
    exact le_ciSup (Khat_bddAbove h v) (DKhat h v)

/-! ### Continuity of `DKhat`

The Legendre transform's gradient `DKhat` is continuous. We follow
the standard argmax-USC argument: any sequence `v_n → v` produces
a bounded sequence `q_n := DKhat h v_n` (boundedness from coercivity
of `K`), and any convergent subsequence of `q_n` must converge to
`DKhat h v` by uniqueness of the argmax. Hence `q_n → DKhat h v`.

Paper reference: `Source/FGU-monotone_revised.tex` lines 1646–1659. -/

/-- **A-priori bound on `DKhat`.** If `‖v‖ ≤ V`, then
`‖DKhat h v‖ ≤ max 1 ((d·V+1)^{1/(α-1)})`. The argument:
- `0 ≤ DKhat h v ⬝ v − K h (DKhat h v)` (since `0` is a candidate
  for the supremum, and `K h 0 = 0`).
- Hence `K h (DKhat h v) ≤ DKhat h v ⬝ v ≤ d·‖DKhat h v‖·‖v‖`.
- Combined with `‖DKhat h v‖^α ≤ K h (DKhat h v)`, get
  `‖DKhat h v‖^α ≤ d·‖DKhat h v‖·V`, i.e.
  `‖DKhat h v‖^{α-1} ≤ d·V` (when `‖DKhat h v‖ > 1`). -/
lemma DKhat_norm_bound
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    ‖DKhat h v‖ ≤ max 1 (((d : ℝ) * ‖v‖ + 1) ^ (1 / (h.α - 1))) := by
  classical
  set α : ℝ := h.α with hαdef
  have hα_gt_one : 1 < α := h.hα
  have hα_sub_one_pos : 0 < α - 1 := sub_pos.mpr hα_gt_one
  set V : ℝ := ‖v‖ with hVdef
  have hV_nn : 0 ≤ V := norm_nonneg _
  set q : Fin d → ℝ := DKhat h v with hqdef
  -- Compare with `q' = 0`: at `q' = 0`, the supremand is `0 - K h 0 = 0`.
  have h_zero_le : (0 : ℝ) ≤ q ⬝ v - K h q := by
    have h0 : (0 : Fin d → ℝ) ⬝ v - K h (0 : Fin d → ℝ) ≤ q ⬝ v - K h q := by
      have := DKhat_le_supremand h v 0
      simpa [hqdef] using this
    have hK0 : K h (0 : Fin d → ℝ) = 0 := K_zero h
    have hd0 : (0 : Fin d → ℝ) ⬝ v = 0 := by simp
    linarith [h0, hK0, hd0]
  -- Hence `K h q ≤ q ⬝ v`.
  have hKq_le_dot : K h q ≤ q ⬝ v := by linarith
  -- `q ⬝ v ≤ d · ‖q‖ · V`.
  have hdot_bnd : q ⬝ v ≤ (d : ℝ) * ‖q‖ * V := by
    have := euclideanDot_le_card_mul_norm (d := d) q v
    simpa [hVdef] using this
  -- Combine.
  have hKq_bnd : K h q ≤ (d : ℝ) * ‖q‖ * V := le_trans hKq_le_dot hdot_bnd
  -- Coercive lower bound `‖q‖^α ≤ K h q`.
  have hKq_ge : ‖q‖ ^ α ≤ K h q := K_ge_rpow h q
  -- Hence `‖q‖^α ≤ d · ‖q‖ · V`.
  have hqα_le : ‖q‖ ^ α ≤ (d : ℝ) * ‖q‖ * V := le_trans hKq_ge hKq_bnd
  -- Now case-split on `‖q‖ ≤ 1` vs `‖q‖ > 1`.
  by_cases hq1 : ‖q‖ ≤ 1
  · exact le_trans hq1 (le_max_left _ _)
  · push_neg at hq1
    -- ‖q‖ > 1 > 0.
    have hq_pos : 0 < ‖q‖ := lt_trans zero_lt_one hq1
    have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
    -- Express `‖q‖^α = ‖q‖^(α-1) · ‖q‖`.
    have hα_split : α = (α - 1) + 1 := by ring
    have hpow_eq : ‖q‖ ^ α = ‖q‖ ^ (α - 1) * ‖q‖ := by
      conv_lhs => rw [hα_split]
      rw [Real.rpow_add hq_pos, Real.rpow_one]
    rw [hpow_eq] at hqα_le
    -- Divide both sides by `‖q‖` (positive):
    have hqα_le2 : ‖q‖ ^ (α - 1) ≤ (d : ℝ) * V := by
      have hmul : ‖q‖ ^ (α - 1) * ‖q‖ ≤ (d : ℝ) * V * ‖q‖ := by
        calc ‖q‖ ^ (α - 1) * ‖q‖
            ≤ (d : ℝ) * ‖q‖ * V := hqα_le
          _ = (d : ℝ) * V * ‖q‖ := by ring
      exact le_of_mul_le_mul_right hmul hq_pos
    -- Bound by ((d V) + 1) (just a slight padding so we can take roots safely).
    have hbnd_lt : ‖q‖ ^ (α - 1) ≤ (d : ℝ) * V + 1 := by linarith
    -- Take `(α-1)`-th root.
    have hdV_nn : 0 ≤ (d : ℝ) * V :=
      mul_nonneg (by exact_mod_cast (Nat.zero_le d)) hV_nn
    have hbase_nn : 0 ≤ (d : ℝ) * V + 1 := by linarith
    have hbase_pos : 0 < (d : ℝ) * V + 1 := by linarith
    -- Goal: ‖q‖ ≤ ((d V) + 1)^(1/(α-1)) ≤ max 1 ...
    refine le_trans ?_ (le_max_right _ _)
    -- We have ‖q‖^(α-1) ≤ ((d V) + 1). Raise both to 1/(α-1).
    have h_inv_pos : 0 < 1 / (α - 1) := by
      apply one_div_pos.mpr hα_sub_one_pos
    have h_rpow_step :
        (‖q‖ ^ (α - 1)) ^ (1 / (α - 1)) ≤ ((d : ℝ) * V + 1) ^ (1 / (α - 1)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq_nn _) hbnd_lt (le_of_lt h_inv_pos)
    have hlhs : (‖q‖ ^ (α - 1)) ^ (1 / (α - 1)) = ‖q‖ := by
      rw [← Real.rpow_mul hq_nn]
      rw [mul_one_div, div_self (ne_of_gt hα_sub_one_pos), Real.rpow_one]
    rw [hlhs] at h_rpow_step
    exact h_rpow_step

/-- The Euclidean dot product is jointly continuous on `(Fin d → ℝ) × (Fin d → ℝ)`. -/
private lemma euclideanDot_continuous_pair (d : ℕ) :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 ⬝ p.2) := by
  change Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
    ∑ i : Fin d, p.1 i * p.2 i)
  refine continuous_finset_sum _ ?_
  intro i _
  exact ((continuous_apply i).comp continuous_fst).mul
    ((continuous_apply i).comp continuous_snd)

/-- **Continuity of `DKhat`.** Standard argmax-USC argument.

Given `v_n → v`, the sequence `q_n := DKhat h v_n` is bounded by
`DKhat_norm_bound` (since `(v_n)` is bounded as a convergent
sequence). Bolzano–Weierstrass gives a convergent subsequence
`q_{n_k} → q*`. Passing to limits in the maximiser inequality
`q ⬝ v_{n_k} − K h q ≤ q_{n_k} ⬝ v_{n_k} − K h q_{n_k}` shows
that `q*` is also a maximiser at `v`. Uniqueness (`DKhat_unique`)
forces `q* = DKhat h v`. Hence every subsequence has a sub-subseq
converging to `DKhat h v`, which (by `tendsto_of_subseq_tendsto`)
forces the whole sequence to converge. -/
theorem DKhat_continuous (h : HypothesisWeakGrowth (d := d) H DpH) :
    Continuous (DKhat h) := by
  classical
  rw [continuous_iff_seqContinuous]
  intro v_seq v hv_lim
  -- Goal: `Tendsto (fun n => DKhat h (v_seq n)) atTop (𝓝 (DKhat h v))`.
  apply tendsto_of_subseq_tendsto
  intro ns hns_lim
  -- `v_seq ∘ ns → v`.
  have hvns_lim : Filter.Tendsto (fun n => v_seq (ns n)) Filter.atTop
      (𝓝 v) := hv_lim.comp hns_lim
  -- `(v_seq ∘ ns)` is bounded — convergent in a metric space.
  -- Specifically, eventually in any closed ball `closedBall v 1`.
  -- We need a uniform bound `V` for `‖v_seq (ns n)‖` for all `n`.
  -- Use: every convergent sequence in a metric space is bounded
  -- (`Bornology.IsBounded.range_of_tendsto` or just construct V explicitly).
  -- We bound the *q_n*'s using `DKhat_norm_bound`. For this we need
  -- the range of `‖v_seq ∘ ns‖` to be bounded.
  have hVns_bound : ∃ V : ℝ, ∀ n, ‖v_seq (ns n)‖ ≤ V := by
    -- `‖v_seq (ns n)‖ → ‖v‖`.
    have hnorm_lim : Filter.Tendsto (fun n => ‖v_seq (ns n)‖) Filter.atTop
        (𝓝 ‖v‖) := (continuous_norm.tendsto v).comp hvns_lim
    -- Hence eventually within distance 1 of `‖v‖`.
    have hbdd : Filter.Tendsto (fun n => ‖v_seq (ns n)‖) Filter.atTop
        (𝓝 ‖v‖) := hnorm_lim
    -- Use bornology lemma: image of tendsto is bounded.
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hbdd) 1 (by norm_num)
    -- For n ≥ N, `|‖v_seq (ns n)‖ - ‖v‖| < 1`, so `‖v_seq (ns n)‖ ≤ ‖v‖ + 1`.
    -- For n < N, take the max.
    set vals : ℕ → ℝ := fun n => ‖v_seq (ns n)‖
    -- Build V = max (‖v‖ + 1) (max of vals 0, ..., vals (N-1)).
    have h_after : ∀ n, N ≤ n → vals n ≤ ‖v‖ + 1 := by
      intro n hn
      have := hN n hn
      have habs : |vals n - ‖v‖| < 1 := by
        rwa [Real.dist_eq] at this
      have : vals n - ‖v‖ < 1 := lt_of_le_of_lt (le_abs_self _) habs
      linarith
    -- Pick max over the first N values + (‖v‖ + 1).
    classical
    by_cases hN0 : N = 0
    · refine ⟨‖v‖ + 1, ?_⟩
      intro n
      exact h_after n (by rw [hN0]; exact Nat.zero_le _)
    · -- The finite set `{0, 1, ..., N-1}` is nonempty.
      have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      let M := (Finset.range N).sup' (Finset.nonempty_range_iff.mpr hN0) vals
      refine ⟨max M (‖v‖ + 1), ?_⟩
      intro n
      by_cases hn : n < N
      · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
        have hle : vals n ≤ M :=
          Finset.le_sup' (f := vals) hmem
        exact le_trans hle (le_max_left _ _)
      · push_neg at hn
        exact le_trans (h_after n hn) (le_max_right _ _)
  obtain ⟨V, hV⟩ := hVns_bound
  -- Concrete upper bound `R` for `‖DKhat h (v_seq (ns n))‖`.
  set α : ℝ := h.α with hαdef
  have hα_gt_one : 1 < α := h.hα
  have hα_sub_one_pos : 0 < α - 1 := sub_pos.mpr hα_gt_one
  -- For any `v` with `‖v‖ ≤ V`, `‖DKhat h v‖ ≤ R := max 1 ((d·V+1)^(1/(α-1)))`.
  set R : ℝ := max 1 (((d : ℝ) * V + 1) ^ (1 / (α - 1))) with hRdef
  -- We need V ≥ 0 implied by `hV` (since `‖v_seq (ns 0)‖ ≤ V`).
  have hV_nn : 0 ≤ V := le_trans (norm_nonneg _) (hV 0)
  -- For each n, `‖DKhat h (v_seq (ns n))‖ ≤ R`.
  have hqbnd : ∀ n, ‖DKhat h (v_seq (ns n))‖ ≤ R := by
    intro n
    have h_b := DKhat_norm_bound h (v_seq (ns n))
    -- h_b: ‖DKhat ..‖ ≤ max 1 ((d · ‖v_seq (ns n)‖ + 1)^(1/(α-1))).
    -- The RHS is monotone in `‖v_seq (ns n)‖`. Use `hV n`.
    refine le_trans h_b ?_
    -- max 1 (a^(1/(α-1))) ≤ max 1 (b^(1/(α-1))) when a ≤ b, a, b ≥ 0.
    have ha_nn : 0 ≤ (d : ℝ) * ‖v_seq (ns n)‖ + 1 := by
      have : 0 ≤ (d : ℝ) * ‖v_seq (ns n)‖ :=
        mul_nonneg (by exact_mod_cast (Nat.zero_le d)) (norm_nonneg _)
      linarith
    have hle : (d : ℝ) * ‖v_seq (ns n)‖ + 1 ≤ (d : ℝ) * V + 1 := by
      have hdle : (d : ℝ) * ‖v_seq (ns n)‖ ≤ (d : ℝ) * V :=
        mul_le_mul_of_nonneg_left (hV n) (by exact_mod_cast (Nat.zero_le d))
      linarith
    have h_inv_nn : 0 ≤ 1 / (α - 1) :=
      le_of_lt (one_div_pos.mpr hα_sub_one_pos)
    have h_rpow_mono :
        ((d : ℝ) * ‖v_seq (ns n)‖ + 1) ^ (1 / (α - 1)) ≤
          ((d : ℝ) * V + 1) ^ (1 / (α - 1)) :=
      Real.rpow_le_rpow ha_nn hle h_inv_nn
    exact max_le_max le_rfl h_rpow_mono
  -- The sequence `q ns n := DKhat h (v_seq (ns n))` lies in the closed ball
  -- `closedBall 0 R`. Apply BW.
  set q_seq : ℕ → (Fin d → ℝ) := fun n => DKhat h (v_seq (ns n))
  have hR_nn : 0 ≤ R := le_trans (norm_nonneg (q_seq 0)) (hqbnd 0)
  have hq_in : ∀ n, q_seq n ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hqbnd n
  have h_isBdd : Bornology.IsBounded (Metric.closedBall (0 : Fin d → ℝ) R) :=
    Metric.isBounded_closedBall
  obtain ⟨q_star, _hq_star_mem, φ, hφ_mono, hφ_lim⟩ :=
    tendsto_subseq_of_bounded h_isBdd hq_in
  -- We have `q_seq ∘ φ → q_star` and `v_seq ∘ ns ∘ φ → v`.
  refine ⟨φ, ?_⟩
  -- Goal: `Tendsto ((fun n => DKhat h (v_seq (ns n))) ∘ φ) atTop (𝓝 (DKhat h v))`.
  -- Show `q_star = DKhat h v` by uniqueness.
  -- First the limits we need.
  have hv_subsub : Filter.Tendsto (fun n => v_seq (ns (φ n))) Filter.atTop
      (𝓝 v) := hvns_lim.comp hφ_mono.tendsto_atTop
  have hq_subsub : Filter.Tendsto (fun n => q_seq (φ n)) Filter.atTop
      (𝓝 q_star) := hφ_lim
  -- For each q' : Fin d → ℝ: `q' ⬝ v_n - K h q' ≤ q_n ⬝ v_n - K h q_n`.
  have h_max : IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ q_star := by
    intro q' _hq'mem
    -- Goal: `palomar_Kernel_Khat_supremand h v q' ≤ palomar_Kernel_Khat_supremand h v q_star`.
    change q' ⬝ v - K h q' ≤ q_star ⬝ v - K h q_star
    -- Define LHS_n = q' ⬝ v_seq (ns (φ n)) - K h q'.
    -- Define RHS_n = q_seq (φ n) ⬝ v_seq (ns (φ n)) - K h (q_seq (φ n)).
    -- Then LHS_n → q' ⬝ v - K h q' and RHS_n → q_star ⬝ v - K h q_star.
    have h_step : ∀ n,
        q' ⬝ v_seq (ns (φ n)) - K h q' ≤
          q_seq (φ n) ⬝ v_seq (ns (φ n)) - K h (q_seq (φ n)) := by
      intro n
      have := DKhat_le_supremand h (v_seq (ns (φ n))) q'
      simpa [q_seq] using this
    -- Limit of LHS_n.
    have h_dot_lhs : Filter.Tendsto
        (fun n => q' ⬝ v_seq (ns (φ n))) Filter.atTop (𝓝 (q' ⬝ v)) := by
      -- `v ↦ q' ⬝ v` is continuous.
      have : Continuous (fun w : Fin d → ℝ => q' ⬝ w) := by
        unfold dotProduct
        refine continuous_finset_sum _ ?_
        intro i _
        exact continuous_const.mul (continuous_apply i)
      exact (this.tendsto v).comp hv_subsub
    have h_lhs_lim : Filter.Tendsto
        (fun n => q' ⬝ v_seq (ns (φ n)) - K h q') Filter.atTop
        (𝓝 (q' ⬝ v - K h q')) :=
      h_dot_lhs.sub tendsto_const_nhds
    -- Limit of RHS_n.
    -- Build the dot product limit via the joint-continuous dot.
    have h_pair_lim : Filter.Tendsto
        (fun n => (q_seq (φ n), v_seq (ns (φ n)))) Filter.atTop
        (𝓝 (q_star, v)) := hq_subsub.prodMk_nhds hv_subsub
    have h_dot_rhs : Filter.Tendsto
        (fun n => q_seq (φ n) ⬝ v_seq (ns (φ n))) Filter.atTop
        (𝓝 (q_star ⬝ v)) :=
      ((euclideanDot_continuous_pair d).tendsto (q_star, v)).comp h_pair_lim
    have h_K_rhs : Filter.Tendsto
        (fun n => K h (q_seq (φ n))) Filter.atTop (𝓝 (K h q_star)) :=
      ((K_continuous h).tendsto q_star).comp hq_subsub
    have h_rhs_lim : Filter.Tendsto
        (fun n => q_seq (φ n) ⬝ v_seq (ns (φ n)) - K h (q_seq (φ n)))
        Filter.atTop (𝓝 (q_star ⬝ v - K h q_star)) :=
      h_dot_rhs.sub h_K_rhs
    -- Pass to limit in the inequality.
    exact le_of_tendsto_of_tendsto' h_lhs_lim h_rhs_lim h_step
  -- Uniqueness: `q_star = DKhat h v`.
  have hq_star_eq : q_star = DKhat h v :=
    DKhat_unique h v h_max (DKhat_isMaxOn h v)
  -- Conclude.
  rw [hq_star_eq] at hφ_lim
  -- Goal restated: convergence of the sub-sub-sequence to DKhat h v.
  exact hφ_lim

/-! ### Differentiability of `K̂` (envelope theorem)

Paper reference: `Source/FGU-monotone_revised.tex` line 1670 — `K̂` is
`C¹` with `∇K̂(v) = DKhat h v`. This is the classical
**Fenchel envelope theorem**: when the supremum
`Khat(v) = sup_q (q ⬝ v - K(q))` is attained at a unique maximiser
`DKhat(v)`, then `Khat` is Fréchet-differentiable at `v` with
derivative the linear functional `w ↦ DKhat(v) ⬝ w`.

The proof uses the two-sided supremand inequality

  `DKhat(v) ⬝ (w - v) ≤ Khat(w) - Khat(v) ≤ DKhat(w) ⬝ (w - v)`,

combined with continuity of `DKhat` (`DKhat_continuous`) to bound the
error term `r(w) := Khat(w) - Khat(v) - DKhat(v) ⬝ (w - v)` by
`d * ‖DKhat(w) - DKhat(v)‖ * ‖w - v‖`, which is `o(‖w - v‖)`. -/

/-- Absolute-value form of `euclideanDot_le_card_mul_norm`:
`|q ⬝ v| ≤ d * ‖q‖ * ‖v‖`. Apply the one-sided bound to both `q`
and `-q`. -/
lemma abs_euclideanDot_le_card_mul_norm
    (q v : Fin d → ℝ) :
    |q ⬝ v| ≤ d * ‖q‖ * ‖v‖ := by
  have h_pos : q ⬝ v ≤ d * ‖q‖ * ‖v‖ :=
    euclideanDot_le_card_mul_norm (d := d) q v
  -- Apply to `-q`: `(-q) ⬝ v = -(q ⬝ v) ≤ d * ‖-q‖ * ‖v‖ = d * ‖q‖ * ‖v‖`.
  have h_neg' : (-q) ⬝ v ≤ d * ‖-q‖ * ‖v‖ :=
    euclideanDot_le_card_mul_norm (d := d) (-q) v
  have h_neg_dot : (-q) ⬝ v = -(q ⬝ v) := by
    unfold dotProduct
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.neg_apply, neg_mul]
  have h_neg_norm : ‖-q‖ = ‖q‖ := norm_neg q
  rw [h_neg_dot, h_neg_norm] at h_neg'
  have h_neg_bound : -(q ⬝ v) ≤ d * ‖q‖ * ‖v‖ := h_neg'
  exact abs_le.mpr ⟨by linarith, h_pos⟩

/-- **Lower bound** (envelope step 1). For any `v, w`:
`DKhat h v ⬝ (w - v) ≤ Khat h w - Khat h v`.

Reason: `DKhat h v` is a candidate for the supremum defining
`Khat h w`, so `DKhat(v) ⬝ w - K(DKhat(v)) ≤ Khat(w)`. Subtract
the headline identity `Khat(v) = DKhat(v) ⬝ v - K(DKhat(v))`. -/
lemma Khat_sub_ge_dot
    (h : HypothesisWeakGrowth (d := d) H DpH) (v w : Fin d → ℝ) :
    DKhat h v ⬝ (w - v) ≤ Khat h w - Khat h v := by
  -- `DKhat h v ⬝ w - K h (DKhat h v) ≤ Khat h w` since it is a candidate.
  have h_candidate : DKhat h v ⬝ w - K h (DKhat h v) ≤ Khat h w := by
    unfold Khat
    exact le_ciSup (Khat_bddAbove h w) (DKhat h v)
  -- `Khat h v = DKhat h v ⬝ v - K h (DKhat h v)`.
  have h_eq : Khat h v = DKhat h v ⬝ v - K h (DKhat h v) :=
    Khat_eq_at_DKhat h v
  -- Compute `DKhat h v ⬝ (w - v) = DKhat h v ⬝ w - DKhat h v ⬝ v`.
  have h_lin : DKhat h v ⬝ (w - v) = DKhat h v ⬝ w - DKhat h v ⬝ v := by
    unfold dotProduct
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.sub_apply]
    ring
  linarith

/-- **Upper bound** (envelope step 2). For any `v, w`:
`Khat h w - Khat h v ≤ DKhat h w ⬝ (w - v)`.

Reason: by symmetry, `DKhat h w` is a candidate for the supremum
defining `Khat h v`, so `DKhat(w) ⬝ v - K(DKhat(w)) ≤ Khat(v)`.
Combined with `Khat(w) = DKhat(w) ⬝ w - K(DKhat(w))`. -/
lemma Khat_sub_le_dot
    (h : HypothesisWeakGrowth (d := d) H DpH) (v w : Fin d → ℝ) :
    Khat h w - Khat h v ≤ DKhat h w ⬝ (w - v) := by
  -- `Khat h w = DKhat h w ⬝ w - K h (DKhat h w)`.
  have h_eq_w : Khat h w = DKhat h w ⬝ w - K h (DKhat h w) :=
    Khat_eq_at_DKhat h w
  -- `DKhat h w ⬝ v - K h (DKhat h w) ≤ Khat h v` since it is a candidate.
  have h_candidate : DKhat h w ⬝ v - K h (DKhat h w) ≤ Khat h v := by
    unfold Khat
    exact le_ciSup (Khat_bddAbove h v) (DKhat h w)
  have h_lin : DKhat h w ⬝ (w - v) = DKhat h w ⬝ w - DKhat h w ⬝ v := by
    unfold dotProduct
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.sub_apply]
    ring
  linarith

/-- The linear functional `w ↦ q ⬝ w` packaged as a continuous linear
map `(Fin d → ℝ) →L[ℝ] ℝ`. Used to express the Fréchet derivative of
`Khat`. -/
noncomputable def dotCLM (q : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => q ⬝ w
      map_add' := by
        intro x y
        unfold dotProduct
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp [Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        unfold dotProduct
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [Pi.smul_apply, smul_eq_mul]
        ring }
    (d * ‖q‖)
    (by
      intro x
      have hbnd := abs_euclideanDot_le_card_mul_norm (d := d) q x
      simpa [Real.norm_eq_abs] using hbnd)

@[simp] lemma dotCLM_apply (q w : Fin d → ℝ) :
    dotCLM q w = q ⬝ w := rfl

/-- **Envelope theorem**: `Khat` is Fréchet-differentiable at every
`v`, with derivative the linear functional `w ↦ DKhat h v ⬝ w`.

Paper reference: `Source/FGU-monotone_revised.tex` line 1670. The
proof squeezes the error
`r(w) := Khat(w) - Khat(v) - DKhat(v) ⬝ (w - v)` between `0` (from
`Khat_sub_ge_dot`) and `(DKhat(w) - DKhat(v)) ⬝ (w - v)` (from
`Khat_sub_le_dot` minus the lower bound), then uses continuity of
`DKhat` and `|q ⬝ u| ≤ d ‖q‖ ‖u‖` to conclude `r(w) = o(‖w - v‖)`. -/
theorem Khat_hasFDerivAt
    (h : HypothesisWeakGrowth (d := d) H DpH) (v : Fin d → ℝ) :
    HasFDerivAt (Khat h) (dotCLM (DKhat h v)) v := by
  rw [hasFDerivAt_iff_tendsto]
  -- Goal: Tendsto (fun w => ‖w - v‖⁻¹ * ‖Khat h w - Khat h v - DKhat h v ⬝ (w - v)‖)
  --       (𝓝 v) (𝓝 0).
  -- Strategy: bound the inside by `d * ‖DKhat h w - DKhat h v‖`, which → 0.
  -- Then apply squeeze theorem.
  -- Define `g w := d * ‖DKhat h w - DKhat h v‖`.
  set g : (Fin d → ℝ) → ℝ := fun w => (d : ℝ) * ‖DKhat h w - DKhat h v‖ with hg_def
  have hg_tendsto : Filter.Tendsto g (𝓝 v) (𝓝 0) := by
    have h_cont_diff : Continuous (fun w : (Fin d → ℝ) => DKhat h w - DKhat h v) :=
      (DKhat_continuous h).sub continuous_const
    have h_norm : Continuous (fun w : (Fin d → ℝ) =>
        ‖DKhat h w - DKhat h v‖) := continuous_norm.comp h_cont_diff
    have h_mul : Continuous g := continuous_const.mul h_norm
    have h_at_v : g v = 0 := by
      simp [g, sub_self, norm_zero, mul_zero]
    have := h_mul.tendsto v
    rw [h_at_v] at this
    exact this
  -- The bound: `‖w - v‖⁻¹ * ‖r(w)‖ ≤ g w` when `w ≠ v`, and
  -- `‖w - v‖⁻¹ * ‖r(w)‖ = 0` when `w = v` (the inverse becomes 0 and r = 0).
  -- Use squeeze with nonneg LHS and `g` as upper bound.
  apply squeeze_zero (g := fun w => g w)
  · intro w
    positivity
  · intro w
    -- Need: ‖w - v‖⁻¹ * ‖Khat h w - Khat h v - dotCLM (DKhat h v) (w - v)‖ ≤ g w.
    by_cases hwv : w = v
    · -- w = v: LHS = 0 since the inside is 0.
      subst hwv
      simp [dotCLM_apply, sub_self, euclideanDot_zero_right, g]
    · -- w ≠ v: use the squeeze.
      have hwv_ne : w - v ≠ 0 := sub_ne_zero.mpr hwv
      have h_norm_pos : 0 < ‖w - v‖ := norm_pos_iff.mpr hwv_ne
      -- From the two envelope bounds:
      have h_lower : (0 : ℝ) ≤
          Khat h w - Khat h v - DKhat h v ⬝ (w - v) := by
        have := Khat_sub_ge_dot h v w
        linarith
      -- DKhat h w ⬝ (w - v) - DKhat h v ⬝ (w - v) = (DKhat h w - DKhat h v) ⬝ (w - v).
      have h_lin :
          DKhat h w ⬝ (w - v) - DKhat h v ⬝ (w - v) =
            (DKhat h w - DKhat h v) ⬝ (w - v) := by
        unfold dotProduct
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp [Pi.sub_apply]
        ring
      have h_upper :
          Khat h w - Khat h v - DKhat h v ⬝ (w - v) ≤
            (DKhat h w - DKhat h v) ⬝ (w - v) := by
        have hsub := Khat_sub_le_dot h v w
        linarith
      -- |r| ≤ |(DKhat h w - DKhat h v) ⬝ (w - v)| ≤ d * ‖DKhat h w - DKhat h v‖ * ‖w - v‖.
      have h_abs_r :
          |Khat h w - Khat h v - DKhat h v ⬝ (w - v)| ≤
            (d : ℝ) * ‖DKhat h w - DKhat h v‖ * ‖w - v‖ := by
        have h_abs_le_diff :
            |Khat h w - Khat h v - DKhat h v ⬝ (w - v)| ≤
              |(DKhat h w - DKhat h v) ⬝ (w - v)| := by
          rw [abs_of_nonneg h_lower]
          exact le_trans h_upper (le_abs_self _)
        have h_dot_bnd :=
          abs_euclideanDot_le_card_mul_norm (d := d) (DKhat h w - DKhat h v) (w - v)
        linarith
      -- Massage the LHS to expose `Khat h w - Khat h v - DKhat h v ⬝ (w - v)`.
      have h_inside :
          Khat h w - Khat h v - dotCLM (DKhat h v) (w - v) =
            Khat h w - Khat h v - DKhat h v ⬝ (w - v) := by
        simp [dotCLM_apply]
      rw [h_inside, Real.norm_eq_abs]
      change ‖w - v‖⁻¹ *
          |Khat h w - Khat h v - DKhat h v ⬝ (w - v)| ≤ g w
      change ‖w - v‖⁻¹ *
          |Khat h w - Khat h v - DKhat h v ⬝ (w - v)|
        ≤ (d : ℝ) * ‖DKhat h w - DKhat h v‖
      rw [inv_mul_le_iff₀ h_norm_pos]
      linarith [h_abs_r]
  · exact hg_tendsto

/-- **`K̂` is differentiable everywhere** (paper line 1670). -/
theorem Khat_differentiable
    (h : HypothesisWeakGrowth (d := d) H DpH) :
    Differentiable ℝ (Khat h) :=
  fun v => (Khat_hasFDerivAt h v).differentiableAt

/-! ### Unit tests -/

example (h : HypothesisWeakGrowth (d := d) H DpH) :
    K h (0 : Fin d → ℝ) = 0 := K_zero h

example (h : HypothesisWeakGrowth (d := d) H DpH) (q : Fin d → ℝ) :
    ‖q‖ ^ h.α ≤ K h q := K_ge_rpow h q

example (h : HypothesisWeakGrowth (d := d) H DpH) :
    HasSubgradientAt (K h) 0 (0 : Fin d → ℝ) := by
  rw [K_subdiff_zero]
  intro y
  simp [norm_nonneg]

/-- Unit test (`d = 1`): `K̂` is convex. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) :
    ConvexOn ℝ Set.univ (Khat h) := Khat_convex h

/-- Unit test (`d = 1`): `K̂` is lower semicontinuous. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) :
    LowerSemicontinuous (Khat h) := Khat_lsc h

/-- Unit test (`d = 1`): `DKhat` is a maximiser. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) (v : Fin 1 → ℝ) :
    IsMaxOn (palomar_Kernel_Khat_supremand h v) Set.univ (DKhat h v) :=
  DKhat_isMaxOn h v

/-- Unit test (`d = 1`): the headline identity at `v = 0`. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) (v : Fin 1 → ℝ) :
    Khat h v = DKhat h v ⬝ v - K h (DKhat h v) := Khat_eq_at_DKhat h v

/-- Unit test (`d = 1`): `DKhat` is continuous. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) :
    Continuous (DKhat h) := DKhat_continuous h

/-- Unit test (`d = 1`): `K̂` is differentiable everywhere. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) :
    Differentiable ℝ (Khat h) := Khat_differentiable h

/-- Unit test (`d = 1`): the Fréchet derivative of `K̂` at `v` is the
linear functional `w ↦ DKhat h v ⬝ w`. -/
example {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁) (v : Fin 1 → ℝ) :
    HasFDerivAt (Khat h) (dotCLM (DKhat h v)) v :=
  Khat_hasFDerivAt h v

/-- Unit test (`d = 2`): strict convexity of `K_paper` at two
distinct points. -/
example
    (h : HypothesisWeakGrowth (d := 2)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin 2 → ℝ))) :
    K_paper h ((1 / 2 : ℝ) • (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
        + (1 / 2 : ℝ) • (fun _ : Fin 2 => (1 : ℝ)))
      <
    (1 / 2 : ℝ) * K_paper h (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
      + (1 / 2 : ℝ) * K_paper h (fun _ : Fin 2 => (1 : ℝ)) := by
  set x : Fin 2 → ℝ := fun i => if i = 0 then (1 : ℝ) else 0
  set y : Fin 2 → ℝ := fun _ => (1 : ℝ)
  have hxy : x ≠ y := by
    intro h_eq
    have h1 : x 1 = y 1 := by rw [h_eq]
    have hx1 : x 1 = 0 := by simp [x]
    have hy1 : y 1 = 1 := by simp [y]
    rw [hx1, hy1] at h1
    exact zero_ne_one h1
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hab : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have h_sc := K_paper_strictlyConvex h
  have h_strict :=
    h_sc.2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab
  simpa [smul_eq_mul] using h_strict

end InfimalConvolution
end StationaryMFG
