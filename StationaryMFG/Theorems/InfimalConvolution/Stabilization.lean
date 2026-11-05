module

public import StationaryMFG.Theorems.InfimalConvolution.Kernel
public import StationaryMFG.Theorems.InfimalConvolution.InfConv

@[expose] public section

/-!
# Stabilization of `H^ε` and `D_pH^ε` for small `ε`

Paper Remark `observation` (`Source/FGU-monotone_revised.tex`, lines
1923–1941). Since `α > 1`, the subdifferential `∂K(0)` equals the
closed (dual) unit ball. Hence, given a bound `‖D_pH(x, p, m)‖ < M`,
there is a threshold `ε₀ = ε₀(M) > 0` such that for all `ε < ε₀`,

  `D_pH(x, p, m) ∈ (1/ε) · ∂K(0)`.

By uniqueness of the minimizer `q^ε(x, p, m)` in the first inclusion
of `eq:inf-conv.diff-relation1`, the value `q = 0` also satisfies that
inclusion, so it must coincide with `q^ε(x, p, m)`. Consequently,
using the formulae

  `H^ε(x, p, m) = H(x, p − q^ε, m) + (1/ε) K(q^ε)`     (eq:H-epsilon-formula)
  `D_pH^ε(x, p, m) = D_pH(x, p − q^ε, m)`                (eq:DpH-epsilon-formula)

and `K(0) = 0` from `Kernel.lean`, we conclude

  `H^ε(x, p, m) = H(x, p, m)`,    `D_pH^ε(x, p, m) = D_pH(x, p, m)`.

This file packages the observation as a sequence of three lemmas
(`qEpsilon_eq_zero_of_DpH_small`, `Hepsilon_eq_H_of_DpH_small`,
`DpHepsilon_eq_DpH_of_DpH_small`) plus the explicit threshold
`eps0 d M := 1 / (d * M + 1)`. The minimizer `q^ε`, the `H^ε`,
and the `D_pH^ε` are accepted as parameters together with their
defining formulae and the uniqueness hypothesis, matching the
abstract style used elsewhere in `InfimalConvolution/`.
-/

namespace StationaryMFG
namespace InfimalConvolution
namespace Stabilization

open StationaryMFG.Hamiltonian
open StationaryMFG.InfimalConvolution
open StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ### Threshold `ε₀(M)`

`ε₀(M) := 1 / (d · M + 1)`. The `+1` keeps the threshold strictly
positive for `M = 0` and avoids a division-by-zero edge case; for
`M > 0` the choice still satisfies `d · M · ε₀(M) < 1`, which is the
sufficient condition needed to put `ε · D_pH(x, p, m)` into the
subdifferential `∂K(0)` (the dual unit ball). -/

/-- The stabilization threshold `ε₀(M) := 1 / (d * M + 1)`. Depends
only on the ambient dimension `d` and the upper bound `M` on
`‖D_pH(x, p, m)‖`. -/
noncomputable def eps0 (d : ℕ) (M : ℝ) : ℝ := 1 / ((d : ℝ) * M + 1)

/-- `ε₀(M)` is positive (assuming `M ≥ 0`). -/
lemma eps0_pos {d : ℕ} {M : ℝ} (hM : 0 ≤ M) : 0 < eps0 d M := by
  unfold eps0
  have hd : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
  have h_denom_pos : 0 < (d : ℝ) * M + 1 := by
    have : 0 ≤ (d : ℝ) * M := mul_nonneg hd hM
    linarith
  exact one_div_pos.mpr h_denom_pos

/-! ### Key step: `ε • D_pH(x, p, m) ∈ ∂K(0)`

Combining `K_subdiff_zero` (the subdifferential characterization at
the origin) with the elementary pairing bound
`∑ i, v i * y i ≤ d · ‖v‖ · ‖y‖` for the sup-norm on `Fin d → ℝ`,
we get that `‖DpHval‖ < M` and `0 < ε < ε₀(M)` together imply
`HasSubgradientAt (K h) 0 (ε • DpHval)`. -/

/-- Elementary pairing bound: with the sup-norm on `Fin d → ℝ`,
`∑ i, v i * y i ≤ d · ‖v‖ · ‖y‖`. -/
private lemma pairing_le_sup_norm
    (v y : Fin d → ℝ) :
    ∑ i, v i * y i ≤ (d : ℝ) * ‖v‖ * ‖y‖ := by
  classical
  have h_each : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      v i * y i ≤ ‖v‖ * ‖y‖ := by
    intro i _
    have h1 : v i * y i ≤ |v i * y i| := le_abs_self _
    have h2 : |v i * y i| = |v i| * |y i| := abs_mul _ _
    have hvi : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      simpa [Real.norm_eq_abs] using this
    have hyi : |y i| ≤ ‖y‖ := by
      have := norm_le_pi_norm y i
      simpa [Real.norm_eq_abs] using this
    calc v i * y i ≤ |v i * y i| := h1
      _ = |v i| * |y i| := h2
      _ ≤ ‖v‖ * |y i| := by
            exact mul_le_mul_of_nonneg_right hvi (abs_nonneg _)
      _ ≤ ‖v‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_left hyi (norm_nonneg _)
  have h_sum :
      (∑ i, v i * y i) ≤ ∑ _ : Fin d, ‖v‖ * ‖y‖ :=
    Finset.sum_le_sum h_each
  have h_card :
      (∑ _ : Fin d, ‖v‖ * ‖y‖) = (d : ℝ) * (‖v‖ * ‖y‖) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc (∑ i, v i * y i)
        ≤ ∑ _ : Fin d, ‖v‖ * ‖y‖ := h_sum
    _ = (d : ℝ) * (‖v‖ * ‖y‖) := h_card
    _ = (d : ℝ) * ‖v‖ * ‖y‖ := by ring

/-- **Key inclusion.** If `‖DpHval‖ < M` and `0 < ε < ε₀(M)`, then
`ε • DpHval` lies in the subdifferential of `K h` at the origin:

  `HasSubgradientAt (K h) 0 (ε • DpHval)`.

Equivalently, `DpHval ∈ (1/ε) · ∂K(0)`. -/
lemma DpH_in_subdiff_zero
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (DpHval : Fin d → ℝ)
    {M ε : ℝ} (hM : 0 ≤ M) (hbnd : ‖DpHval‖ < M)
    (hε_pos : 0 < ε) (hε_lt : ε < eps0 d M) :
    HasSubgradientAt (K h) 0 (ε • DpHval) := by
  classical
  -- Reduce to the dual-pairing characterization at 0 (sup-norm form).
  -- We prove the sup-norm bound first and then upgrade via
  -- `K_subdiff_zero_of_sup_bound` (sup-norm ⇒ Euclidean dual ball).
  refine K_subdiff_zero_of_sup_bound h ?_
  intro y
  -- Goal: ∑ i, (ε • DpHval) i * y i ≤ ‖y‖.
  -- Simplify `(ε • DpHval) i = ε * DpHval i` and pull the constant out of the sum.
  have h_pair_eq :
      (∑ i, (ε • DpHval) i * y i) = ε * (∑ i, DpHval i * y i) := by
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [h_pair_eq]
  -- Bound `∑ i, DpHval i * y i ≤ d * ‖DpHval‖ * ‖y‖`.
  have h_dot_bound : (∑ i, DpHval i * y i) ≤ (d : ℝ) * ‖DpHval‖ * ‖y‖ :=
    pairing_le_sup_norm DpHval y
  -- Convert the threshold into the working inequality `d * M * ε ≤ 1` (strictly).
  have hε_nn : 0 ≤ ε := le_of_lt hε_pos
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
  have hDpH_nn : (0 : ℝ) ≤ ‖DpHval‖ := norm_nonneg _
  have hy_nn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have hdM_nn : (0 : ℝ) ≤ (d : ℝ) * M := mul_nonneg hd_nn hM
  have h_denom_pos : 0 < (d : ℝ) * M + 1 := by linarith
  -- From hε_lt : ε < 1 / (d * M + 1), conclude ε * (d * M + 1) < 1.
  have h_eps_denom : ε * ((d : ℝ) * M + 1) < 1 := by
    have hlt : ε < 1 / ((d : ℝ) * M + 1) := by
      simpa [eps0] using hε_lt
    have hmul : ε * ((d : ℝ) * M + 1) < (1 / ((d : ℝ) * M + 1)) * ((d : ℝ) * M + 1) :=
      mul_lt_mul_of_pos_right hlt h_denom_pos
    have h_cancel : (1 / ((d : ℝ) * M + 1)) * ((d : ℝ) * M + 1) = 1 := by
      field_simp
    linarith
  -- Hence ε * d * M ≤ ε * d * M + ε = ε * (d * M + 1) - 0 = ... ≤ 1 - ε. So ε * d * M < 1.
  have h_εdM_lt : ε * ((d : ℝ) * M) < 1 := by
    have h_split : ε * ((d : ℝ) * M + 1) = ε * ((d : ℝ) * M) + ε := by ring
    rw [h_split] at h_eps_denom
    linarith
  -- Combine: ε * (∑ i, DpHval i * y i)
  --        ≤ ε * (d * ‖DpHval‖ * ‖y‖)
  --        ≤ ε * (d * M * ‖y‖)        (since ‖DpHval‖ < M and ε * d ≥ 0)
  --        = (ε * d * M) * ‖y‖
  --        < 1 * ‖y‖ = ‖y‖.
  -- Step 1: ε * (∑ ...) ≤ ε * (d * ‖DpHval‖ * ‖y‖).
  have h1 : ε * (∑ i, DpHval i * y i) ≤ ε * ((d : ℝ) * ‖DpHval‖ * ‖y‖) :=
    mul_le_mul_of_nonneg_left h_dot_bound hε_nn
  -- Step 2: `d * ‖DpHval‖ * ‖y‖ ≤ d * M * ‖y‖`, using ‖DpHval‖ ≤ M (from <).
  have h_DpH_le_M : ‖DpHval‖ ≤ M := le_of_lt hbnd
  have h_d_DpH_le : (d : ℝ) * ‖DpHval‖ ≤ (d : ℝ) * M :=
    mul_le_mul_of_nonneg_left h_DpH_le_M hd_nn
  have h2 : (d : ℝ) * ‖DpHval‖ * ‖y‖ ≤ (d : ℝ) * M * ‖y‖ :=
    mul_le_mul_of_nonneg_right h_d_DpH_le hy_nn
  have h2' : ε * ((d : ℝ) * ‖DpHval‖ * ‖y‖) ≤ ε * ((d : ℝ) * M * ‖y‖) :=
    mul_le_mul_of_nonneg_left h2 hε_nn
  -- Step 3: ε * (d * M * ‖y‖) = (ε * (d * M)) * ‖y‖.
  have h_assoc : ε * ((d : ℝ) * M * ‖y‖) = (ε * ((d : ℝ) * M)) * ‖y‖ := by ring
  -- Step 4: (ε * d * M) * ‖y‖ ≤ 1 * ‖y‖ since ε * d * M < 1 and ‖y‖ ≥ 0.
  have h4 : (ε * ((d : ℝ) * M)) * ‖y‖ ≤ 1 * ‖y‖ :=
    mul_le_mul_of_nonneg_right (le_of_lt h_εdM_lt) hy_nn
  -- Chain.
  calc ε * (∑ i, DpHval i * y i)
        ≤ ε * ((d : ℝ) * ‖DpHval‖ * ‖y‖) := h1
    _ ≤ ε * ((d : ℝ) * M * ‖y‖) := h2'
    _ = (ε * ((d : ℝ) * M)) * ‖y‖ := h_assoc
    _ ≤ 1 * ‖y‖ := h4
    _ = ‖y‖ := one_mul _

/-! ### Stabilization at the abstract level

We accept as parameters:
- `qOf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)`, the inf-conv
  minimizer `q^ε`.
- `Hε`, `DpHε` : the regularized Hamiltonian and its gradient.
- Hypotheses encoding the paper's first inclusion in
  `eq:inf-conv.diff-relation1` and its uniqueness, together with the
  formulae `eq:H-epsilon-formula` and `eq:DpH-epsilon-formula`.

This avoids committing to a particular construction of `q^ε`
(strict convexity of `K` is the standard route, deferred to a
separate task) and keeps the observation self-contained. -/

/-- **Step 1: stabilization of `q^ε`.** Under `‖D_pH(x, p, m)‖ < M`
and `0 < ε < ε₀(M)`, and assuming the uniqueness of `q^ε(x, p, m)`
as the value `q` satisfying

  `HasSubgradientAt (K h) q (ε • D_pH(x, p − q, m))`,

we have `q^ε(x, p, m) = 0`. (The candidate `q = 0` satisfies the
inclusion at `q = 0` by `DpH_in_subdiff_zero`; uniqueness forces it
to coincide with the actual minimizer.) -/
theorem qEpsilon_eq_zero_of_DpH_small
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qOf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m : ℝ}
    {M ε : ℝ} (hM : 0 ≤ M) (hbnd : ‖DpH x p m‖ < M)
    (hε_pos : 0 < ε) (hε_lt : ε < eps0 d M)
    (hUniq : ∀ q : Fin d → ℝ,
      HasSubgradientAt (K h) q (ε • DpH x (p - q) m) → q = qOf x p m) :
    qOf x p m = 0 := by
  -- `q = 0` satisfies the inclusion since `p - 0 = p` and
  -- `ε • D_pH(x, p, m) ∈ ∂K(0)` by `DpH_in_subdiff_zero`.
  have hSub : HasSubgradientAt (K h) (0 : Fin d → ℝ) (ε • DpH x p m) :=
    DpH_in_subdiff_zero h (DpH x p m) hM hbnd hε_pos hε_lt
  -- Adjust the argument so it has the shape expected by `hUniq`.
  have hSub' :
      HasSubgradientAt (K h) (0 : Fin d → ℝ)
        (ε • DpH x (p - (0 : Fin d → ℝ)) m) := by
    have hp : p - (0 : Fin d → ℝ) = p := sub_zero _
    simpa [hp] using hSub
  -- Uniqueness forces `q = 0` to coincide with `qOf x p m`; we
  -- conclude `qOf x p m = 0` by symmetry.
  exact (hUniq 0 hSub').symm

/-- **Step 2: stabilization of `H^ε`.** Given the formula
`H^ε(x, p, m) = H(x, p − q^ε, m) + (1/ε) K(q^ε)` and the smallness
conclusion `q^ε(x, p, m) = 0`, we conclude `H^ε(x, p, m) = H(x, p, m)`. -/
theorem Hepsilon_eq_H_of_DpH_small
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (Hε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (qOf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m ε : ℝ}
    (hFormula : Hε x p m = H x (p - qOf x p m) m + (1 / ε) * K h (qOf x p m))
    (hqZero : qOf x p m = 0) :
    Hε x p m = H x p m := by
  rw [hFormula, hqZero, K_zero h]
  simp

/-- **Step 3: stabilization of `D_pH^ε`.** Given the formula
`D_pH^ε(x, p, m) = D_pH(x, p − q^ε, m)` (`eq:DpH-epsilon-formula`)
and the smallness conclusion `q^ε(x, p, m) = 0`, we conclude
`D_pH^ε(x, p, m) = D_pH(x, p, m)`. -/
theorem DpHepsilon_eq_DpH_of_DpH_small
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (qOf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {x p : Fin d → ℝ} {m : ℝ}
    (hFormula : DpHε x p m = DpH x (p - qOf x p m) m)
    (hqZero : qOf x p m = 0) :
    DpHε x p m = DpH x p m := by
  rw [hFormula, hqZero, sub_zero]

/-! ### Family-level stabilization producer (Theorem 3, arrow A4)

The pointwise stabilization identities (`qEpsilon_eq_zero_of_DpH_small`,
`Hepsilon_eq_H_of_DpH_small`, `DpHepsilon_eq_DpH_of_DpH_small`) are here
lifted to a **family-level** statement over the unit cube, as needed by the
Theorem 3 limit-passage step (`eq:existweaksol.delta`, paper line
1968). Given a test pair `(μ, Dυ)` and a *uniform* a.e. bound
`‖D_pH(x, Dυ(x), μ(x))‖ < M` on the cube — which the paper obtains
from `HypothesisWeakGrowth.DpH_upper` together with `μ, Dυ ∈ L^∞_per`
— the same threshold `ε₀ = ε₀(M)` works for almost every `x`
simultaneously. Hence for every `0 < ε < ε₀` the two stabilization
identities hold *pointwise a.e.* on `UnitCube d`:

  `H^ε(x, Dυ(x), μ(x)) = H(x, Dυ(x), μ(x))`,
  `D_pH^ε(x, Dυ(x), μ(x)) = D_pH(x, Dυ(x), μ(x))`.

This is the genuine A4 deliverable for the T3 public-signature drain.

The minimizer `qOf`, the regularized objects `Hε`/`DpHε`, and their
defining formulae + the subgradient uniqueness are accepted as
parameters family-wise (one instance per `x`), matching the abstract
style of the pointwise stabilization lemmas: this is exactly the data the
Phase 6 cascade (`Properties.qEpsilon_*`, `InfConv.qStar`, the
`eq_of_isMinOn` uniqueness) produces at each point. No strict
positivity of `μ` is required for the identity itself; the essinf
admissibility of the test pair lives in the `def:weak` test space,
not here. -/

/-- **Family-level stabilization** (paper Remark `observation`, lines
1923–1941; `eq:existweaksol.delta`, line 1968), Theorem 3 arrow A4.

Given:
* `h : HypothesisWeakGrowth H DpH`;
* a test pair `μ : (Fin d → ℝ) → ℝ`, `Dυ : Fin d → (Fin d → ℝ) → ℝ`;
* abstract `qOf`, `Hε`, `DpHε`;
* a uniform bound `M ≥ 0` with the a.e. estimate
  `‖D_pH(x, Dυ(x), μ(x))‖ < M` on `UnitCube d`;
* the family-wise subgradient uniqueness of `q^ε` at each `x`;
* the family-wise formulae `eq:H-epsilon-formula` and
  `eq:DpH-epsilon-formula` at each `x`,

there is a threshold `ε₀ = ε₀(M) > 0` such that for every
`0 < ε < ε₀`, both stabilization identities hold pointwise a.e. on
the cube. The uniqueness/formula data are quantified over `ε` so the
*same* `ε₀` serves the whole interval `(0, ε₀)`. -/
theorem stabilization_uniform_of_DpH_small
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (qOf : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Hε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpHε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖DpH x (fun i => Dυ i x) (μ x)‖ < M)
    (hUniq : ∀ ε, 0 < ε → ∀ x : Fin d → ℝ,
      ∀ q : Fin d → ℝ,
        HasSubgradientAt (K h) q
            (ε • DpH x ((fun i => Dυ i x) - q) (μ x)) →
          q = qOf ε x (fun i => Dυ i x) (μ x))
    (hHFormula : ∀ ε, 0 < ε → ∀ x : Fin d → ℝ,
      Hε ε x (fun i => Dυ i x) (μ x)
        = H x ((fun i => Dυ i x) - qOf ε x (fun i => Dυ i x) (μ x)) (μ x)
          + (1 / ε) * K h (qOf ε x (fun i => Dυ i x) (μ x)))
    (hDpHFormula : ∀ ε, 0 < ε → ∀ x : Fin d → ℝ,
      DpHε ε x (fun i => Dυ i x) (μ x)
        = DpH x ((fun i => Dυ i x) - qOf ε x (fun i => Dυ i x) (μ x)) (μ x)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
           Hε ε x (fun i => Dυ i x) (μ x) = H x (fun i => Dυ i x) (μ x))
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
           DpHε ε x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x)) := by
  refine ⟨eps0 d M, eps0_pos hM, ?_⟩
  intro ε hε_pos hε_lt
  constructor
  · -- `H^ε = H` a.e.: at each `x` with `‖D_pH‖ < M`, the pointwise
    -- stabilization gives `q^ε = 0`, hence the H-formula collapses.
    filter_upwards [hbnd] with x hx
    have hq0 : qOf ε x (fun i => Dυ i x) (μ x) = 0 :=
      qEpsilon_eq_zero_of_DpH_small h (qOf ε)
        (x := x) (p := fun i => Dυ i x) (m := μ x)
        hM hx hε_pos hε_lt (hUniq ε hε_pos x)
    exact Hepsilon_eq_H_of_DpH_small h (Hε ε) (qOf ε)
      (x := x) (p := fun i => Dυ i x) (m := μ x) (ε := ε)
      (hHFormula ε hε_pos x) hq0
  · -- `D_pH^ε = D_pH` a.e.: same `q^ε = 0` collapses the DpH-formula.
    filter_upwards [hbnd] with x hx
    have hq0 : qOf ε x (fun i => Dυ i x) (μ x) = 0 :=
      qEpsilon_eq_zero_of_DpH_small h (qOf ε)
        (x := x) (p := fun i => Dυ i x) (m := μ x)
        hM hx hε_pos hε_lt (hUniq ε hε_pos x)
    exact DpHepsilon_eq_DpH_of_DpH_small (DpH := DpH) (DpHε ε) (qOf ε)
      (x := x) (p := fun i => Dυ i x) (m := μ x)
      (hDpHFormula ε hε_pos x) hq0

/-! ### T3 internalization layer — canonical `ε`-sequence + internal
`hstab` producer (D6a)

The Theorem-3 public-signature drain (Path-B, D6) replaces the
public binders `εseq`/`hεpos`/`hεto0`/`hstab` of the closed entry
points by *internal* canonical data. This section provides:

* `T3.canonicalEpsSeq n := 1/(n+1)` — the canonical regularising
  sequence, with positivity and `→ 0` proofs (so `εseq`/`hεpos`/`hεto0`
  need no longer be threaded as public binders).

The per-test-pair A4 stabilisation term in the `∃ ε₀, ∀ e < ε₀` shape
consumed by the closed keystone is produced (downstream) from
`stabilization_uniform_of_DpH_small` applied to the Phase-6 cascade
outputs (`qOf`/`M`/`hbnd`/`hUniq`/`hHFormula`/`hDpHFormula`).

No `εseq`/`hstab`/`*Pack`/`*Inputs`/`*Oracle` binder, no
`HypothesisPowerGrowth`/`RegularityH`/`HdeltaPos`/`qE` appears in the
producers below: those data are the *outputs*, and the only structural
hypothesis consumed is `HypothesisWeakGrowth` (paper `onH.weakgrowth`)
together with paper-side per-test-pair `L^∞` bound + uniqueness/formula
data. -/

namespace T3

open Filter Topology

/-- **Canonical regularising `ε`-sequence** for Theorem 3:
`ε_n := 1/(n+1)`. The `+1` avoids a division-by-zero at `n = 0`. This
is the internal replacement for the previously-public `εseq` binder of
the closed T3 entry points. -/
noncomputable def canonicalEpsSeq : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)

@[simp]
lemma canonicalEpsSeq_apply (n : ℕ) :
    canonicalEpsSeq n = 1 / (n + 1 : ℝ) := rfl

/-- The canonical sequence is strictly positive. -/
lemma canonicalEpsSeq_pos : ∀ n, 0 < canonicalEpsSeq n := by
  intro n
  simp only [canonicalEpsSeq_apply]
  positivity

/-- The canonical sequence tends to `0` along `atTop`. -/
lemma canonicalEpsSeq_tendsto :
    Tendsto canonicalEpsSeq atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The canonical sequence is bounded by `1`: `1/(n+1) ≤ 1` since `1 ≤ n+1`.
Feeds the `hε_le1 : ∀ n, εseq n ≤ 1` slot of the closed T3 entry point (the
family is only evaluated on the paper regularization regime `0 < ε ≤ 1`). -/
lemma canonicalEpsSeq_le_one : ∀ n, canonicalEpsSeq n ≤ 1 := by
  intro n
  simp only [canonicalEpsSeq_apply]
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

end T3

/-! ### Unit tests -/

/-- Positivity of the threshold for `M = 0`. -/
example : 0 < eps0 d (0 : ℝ) := eps0_pos (le_refl 0)

/-- For `M = 1` and `d = 1`, `eps0 1 1 = 1/2`. -/
example : eps0 1 (1 : ℝ) = 1 / 2 := by
  unfold eps0; norm_num

end Stabilization
end InfimalConvolution
end StationaryMFG
