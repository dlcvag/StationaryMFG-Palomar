module

public import StationaryMFG.Periodic.Mollifier
public import StationaryMFG.Periodic.TestFunctions
public import StationaryMFG.Periodic.WeakDerivative

@[expose] public section

/-!
# d-dim periodisation of `bumpKernel`

For `0 < ε < 1/2` and a base point `x₀ : Fin d → ℝ`, this module defines

```
bumpKernelPer d ε hε hε' x₀ s := ∑' k : Fin d → ℤ,
  bumpKernel d ε hε (x₀ - s + (fun i => (k i : ℝ)))
```

and proves:

* `bumpKernelPer_eq_single` — single-term collapse: for any `s`, only the
  rounding `k = roundVec (s - x₀)` (coordinatewise nearest integer) gives
  a nonzero summand.
* `bumpKernelPer_periodic` — periodicity in `s` via lattice shift.
* `bumpKernelPer_contDiff` — smoothness via local agreement with a single
  smooth translate of `bumpKernel`.
* `bumpKernelPer_asSmoothPeriodic` — `SmoothPeriodic d` packaging.
* `bumpKernelPer_fderiv_eq` — partial-derivative formula in the form
  `fderiv ℝ (bumpKernelPer …) s = fderiv ℝ (single translate) s` locally.

This is the d-dim lift of the 1D construction in
`StationaryMFG.Periodic.Mollifier1D` (`periodicMollifier1D`).

-- Adapted from LpSpaces.Mollification (whole-space version) via the
-- 1D `Mollifier1D.lean` template; re-derived here on `Fin d → ℝ`.
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Set Filter Function
open scoped ContDiff Topology

variable {d : ℕ}

/-! ### Coordinatewise rounding -/

/-- Coordinatewise nearest-integer map on `Fin d → ℝ`. -/
noncomputable def roundVec (v : Fin d → ℝ) : Fin d → ℤ :=
  fun i => round (v i)

@[simp] lemma roundVec_apply (v : Fin d → ℝ) (i : Fin d) :
    roundVec v i = round (v i) := rfl

/-- For each coordinate, `|v i - roundVec v i| ≤ 1/2`. -/
lemma abs_sub_roundVec_le (v : Fin d → ℝ) (i : Fin d) :
    |v i - (roundVec v i : ℝ)| ≤ 1 / 2 := by
  simpa [roundVec_apply] using abs_sub_round (v i)

/-! ### When the kernel translate is zero -/

/-- If `0 < ε < 1/2`, then for any `v : Fin d → ℝ` and any
`k : Fin d → ℤ` with `k ≠ roundVec v`, the translate
`bumpKernel ε (v - k_ℝ) = 0`. The proof: some coordinate `i` has
`k i ≠ round (v i)`, and triangle inequality plus `|v i - round (v i)| ≤ 1/2`
forces `|v i - k i| ≥ 1/2 ≥ ε` so the bump factor in coordinate `i` vanishes. -/
lemma bumpKernel_translate_eq_zero_of_ne_roundVec
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (v : Fin d → ℝ)
    {k : Fin d → ℤ} (hk : k ≠ roundVec v) :
    bumpKernel d ε hε (v - fun i => (k i : ℝ)) = 0 := by
  -- Find the coordinate where `k` differs.
  have hexists : ∃ i, k i ≠ roundVec v i := by
    by_contra hall
    apply hk
    funext i
    exact not_not.mp (fun h => hall ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hexists
  -- Show `|v i - k i| ≥ ε`, which kills the i-th factor.
  refine bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨i, ?_⟩
  -- Compute the i-th coordinate of `v - k_ℝ`.
  have hcoord : (v - fun j => (k j : ℝ)) i = v i - (k i : ℝ) := by
    simp [Pi.sub_apply]
  rw [hcoord]
  -- Triangle: |round (v i) - k i| ≤ |v i - k i| + |v i - round (v i)|.
  have hround : |v i - (round (v i) : ℝ)| ≤ 1 / 2 := abs_sub_round (v i)
  have hne_int : (round (v i) - k i : ℤ) ≠ 0 := by
    intro h
    apply hi
    have : roundVec v i = k i := by
      simp [roundVec_apply, sub_eq_zero.mp h]
    exact this.symm
  have h_one_le : (1 : ℤ) ≤ |round (v i) - k i| := Int.one_le_abs hne_int
  have h_one_le_real : (1 : ℝ) ≤ |((round (v i) : ℝ) - (k i : ℝ))| := by
    have hcast : ((round (v i) - k i : ℤ) : ℝ)
        = (round (v i) : ℝ) - (k i : ℝ) := by push_cast; ring
    have : (1 : ℝ) ≤ ((|round (v i) - k i| : ℤ) : ℝ) := by exact_mod_cast h_one_le
    rwa [Int.cast_abs, hcast] at this
  -- Triangle inequality.
  have htri :
      |((round (v i) : ℝ) - (k i : ℝ))| ≤ |v i - (k i : ℝ)| + |v i - (round (v i) : ℝ)| := by
    calc |((round (v i) : ℝ) - (k i : ℝ))|
        = |((round (v i) : ℝ) - v i) + (v i - (k i : ℝ))| := by ring_nf
      _ ≤ |((round (v i) : ℝ) - v i)| + |v i - (k i : ℝ)| := abs_add_le _ _
      _ = |v i - (round (v i) : ℝ)| + |v i - (k i : ℝ)| := by rw [abs_sub_comm]
      _ = |v i - (k i : ℝ)| + |v i - (round (v i) : ℝ)| := by ring
  linarith

/-! ### The d-dim periodisation -/

set_option linter.unusedVariables false in
/-- The d-dim periodisation of `bumpKernel d ε hε` translated by `x₀`:
`bumpKernelPer d ε hε hε' x₀ s := ∑' k : Fin d → ℤ, bumpKernel d ε hε (x₀ - s + k_ℝ)`.

The hypothesis `hε' : ε < 1 / 2` is part of the signature so all downstream
lemmas (collapse, smoothness, periodicity) can be invoked without re-stating
the constraint; it is not used inside the bare tsum definition. -/
noncomputable def bumpKernelPer (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ : Fin d → ℝ) : (Fin d → ℝ) → ℝ :=
  fun s => ∑' k : Fin d → ℤ,
    bumpKernel d ε hε (x₀ - s + fun i => (k i : ℝ))

lemma bumpKernelPer_apply (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ s : Fin d → ℝ) :
    bumpKernelPer d ε hε hε' x₀ s =
      ∑' k : Fin d → ℤ,
        bumpKernel d ε hε (x₀ - s + fun i => (k i : ℝ)) := rfl

/-! ### Single-term collapse -/

/-- For `ε < 1/2`, the periodisation collapses to the single nonzero
translate at `k = roundVec (s - x₀)`. -/
lemma bumpKernelPer_eq_single (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ s : Fin d → ℝ) :
    bumpKernelPer d ε hε hε' x₀ s =
      bumpKernel d ε hε
        (x₀ - s + fun i => ((roundVec (s - x₀)) i : ℝ)) := by
  rw [bumpKernelPer_apply]
  refine tsum_eq_single (roundVec (s - x₀)) ?_
  intro k hk
  -- We need `k ≠ roundVec (-(x₀ - s)) = roundVec (s - x₀)`. The argument
  -- of `bumpKernel_translate_eq_zero_of_ne_roundVec` for vanishing is
  -- `v := -(x₀ - s)` since `bumpKernel ε (v - k_ℝ) = bumpKernel ε (x₀ - s + k_ℝ)`?
  -- Easier: rewrite the translate as `v - k_ℝ` with `v = x₀ - s + k_ℝ + k_ℝ`?
  -- Direct route: apply the zero-lemma at `v := x₀ - s + 2·k_ℝ` and shift?
  -- Cleanest: show the i-th coordinate has |·| ≥ ε directly.
  -- Use `bumpKernel_eq_zero_of_exists_abs_ge`.
  -- We have hk : k ≠ roundVec (s - x₀), find a coordinate.
  have hexists : ∃ i, k i ≠ roundVec (s - x₀) i := by
    by_contra hall
    apply hk
    funext i
    exact not_not.mp (fun h => hall ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hexists
  refine bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨i, ?_⟩
  -- The i-th coord of `x₀ - s + k_ℝ` is `x₀ i - s i + k i = -((s - x₀) i - k i)`.
  have hcoord :
      (x₀ - s + fun j => (k j : ℝ)) i = (x₀ i - s i) + (k i : ℝ) := by
    simp [Pi.add_apply, Pi.sub_apply]
  rw [hcoord]
  -- Reduce to bound on `(s - x₀) i - k i` since
  -- `|(x₀ i - s i) + k i| = |(s - x₀) i - k i|`.
  have habs_eq : |(x₀ i - s i) + (k i : ℝ)| = |(s - x₀) i - (k i : ℝ)| := by
    have heq2 : (x₀ i - s i) + (k i : ℝ) = -((s - x₀) i - (k i : ℝ)) := by
      change (x₀ i - s i) + (k i : ℝ) = -((s i - x₀ i) - (k i : ℝ))
      ring
    rw [heq2]; exact abs_neg _
  rw [habs_eq]
  -- Now the standard triangle argument.
  have hround : |(s - x₀) i - (round ((s - x₀) i) : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have hne_int : (round ((s - x₀) i) - k i : ℤ) ≠ 0 := by
    intro h
    apply hi
    have hroundeq : round ((s - x₀) i) = k i := sub_eq_zero.mp h
    -- Goal is `k i = roundVec (s - x₀) i`; unfolds to `k i = round ((s - x₀) i)`.
    exact hroundeq.symm
  have h_one_le : (1 : ℤ) ≤ |round ((s - x₀) i) - k i| := Int.one_le_abs hne_int
  have h_one_le_real :
      (1 : ℝ) ≤ |((round ((s - x₀) i) : ℝ) - (k i : ℝ))| := by
    have hcast : ((round ((s - x₀) i) - k i : ℤ) : ℝ)
        = (round ((s - x₀) i) : ℝ) - (k i : ℝ) := by push_cast; ring
    have : (1 : ℝ) ≤ ((|round ((s - x₀) i) - k i| : ℤ) : ℝ) := by exact_mod_cast h_one_le
    rwa [Int.cast_abs, hcast] at this
  have htri :
      |((round ((s - x₀) i) : ℝ) - (k i : ℝ))| ≤
        |(s - x₀) i - (k i : ℝ)| + |(s - x₀) i - (round ((s - x₀) i) : ℝ)| := by
    calc |((round ((s - x₀) i) : ℝ) - (k i : ℝ))|
        = |((round ((s - x₀) i) : ℝ) - (s - x₀) i) + ((s - x₀) i - (k i : ℝ))| := by
          ring_nf
      _ ≤ |((round ((s - x₀) i) : ℝ) - (s - x₀) i)| + |(s - x₀) i - (k i : ℝ)| :=
          abs_add_le _ _
      _ = |(s - x₀) i - (round ((s - x₀) i) : ℝ)| + |(s - x₀) i - (k i : ℝ)| := by
          rw [abs_sub_comm]
      _ = |(s - x₀) i - (k i : ℝ)| + |(s - x₀) i - (round ((s - x₀) i) : ℝ)| := by ring
  linarith

/-! ### Local agreement with a single smooth translate -/

/-- The single-translate branch of `bumpKernelPer` at base `s₀`:
the smooth function `s ↦ bumpKernel d ε hε (x₀ - s + roundVec(s₀ - x₀))`. -/
noncomputable def singleBranch (ε : ℝ) (hε : 0 < ε)
    (x₀ s₀ : Fin d → ℝ) : (Fin d → ℝ) → ℝ :=
  fun s => bumpKernel d ε hε
    (x₀ - s + fun i => ((roundVec (s₀ - x₀)) i : ℝ))

lemma singleBranch_contDiff (ε : ℝ) (hε : 0 < ε)
    (x₀ s₀ : Fin d → ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞)) (singleBranch ε hε x₀ s₀) := by
  unfold singleBranch
  have hshift : ContDiff ℝ ((⊤ : ℕ∞))
      (fun s : Fin d → ℝ => x₀ - s + fun i => ((roundVec (s₀ - x₀)) i : ℝ)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞)) (fun s : Fin d → ℝ => x₀ - s) :=
      contDiff_const.sub contDiff_id
    exact h1.add contDiff_const
  exact (bumpKernel_contDiff d ε hε).comp hshift

/-- Locally near `s₀`, the periodisation equals the single-translate
branch indexed by `roundVec (s₀ - x₀)`. -/
lemma bumpKernelPer_eventuallyEq_singleBranch
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ s₀ : Fin d → ℝ) :
    bumpKernelPer d ε hε hε' x₀ =ᶠ[𝓝 s₀] singleBranch ε hε x₀ s₀ := by
  -- Choose `δ := (1/2 - ε) / 2 > 0`. On a small ball of radius `δ`
  -- around `s₀`, every `s` has `roundVec (s - x₀) = roundVec (s₀ - x₀)`.
  set δ : ℝ := (1 / 2 - ε) / 2 with hδdef
  have hδpos : 0 < δ := by
    have : 0 < 1/2 - ε := by linarith
    change 0 < (1 / 2 - ε) / 2; linarith
  -- Open ball in sup metric is enough; we'll use coordinatewise
  -- pointwise neighborhoods.
  have hball_open : IsOpen
      ({s : Fin d → ℝ | ∀ i, |s i - s₀ i| < δ}) := by
    -- This is the intersection of preimages of open balls under coord proj.
    have : ({s : Fin d → ℝ | ∀ i, |s i - s₀ i| < δ})
        = ⋂ i : Fin d, {s : Fin d → ℝ | |s i - s₀ i| < δ} := by
      ext s; simp [Set.mem_iInter]
    rw [this]
    refine isOpen_iInter_of_finite (fun i => ?_)
    -- preimage under continuous `s ↦ s i - s₀ i` of open set `|·| < δ`.
    have hcont : Continuous (fun s : Fin d → ℝ => s i - s₀ i) :=
      (continuous_apply i).sub continuous_const
    exact isOpen_lt (continuous_abs.comp hcont) continuous_const
  have hmem : s₀ ∈ {s : Fin d → ℝ | ∀ i, |s i - s₀ i| < δ} := by
    intro i; simpa using hδpos
  refine eventuallyEq_of_mem (hball_open.mem_nhds hmem) ?_
  intro s hs
  -- Goal: `bumpKernelPer ... s = singleBranch ε hε x₀ s₀ s`.
  show bumpKernelPer d ε hε hε' x₀ s = singleBranch ε hε x₀ s₀ s
  rw [bumpKernelPer_apply]
  -- Collapse the tsum to the term `k = roundVec (s₀ - x₀)`.
  refine tsum_eq_single (roundVec (s₀ - x₀)) ?_
  intro k hk
  -- For every coord, |s_i - s₀_i| < δ. Need to show: bumpKernel(...)= 0,
  -- i.e. some coordinate of `x₀ - s + k_ℝ` has |·| ≥ ε.
  -- We pick the coord where `k i ≠ roundVec (s₀ - x₀) i`.
  have hexists : ∃ i, k i ≠ roundVec (s₀ - x₀) i := by
    by_contra hall
    apply hk
    funext i
    exact not_not.mp (fun h => hall ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hexists
  refine bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨i, ?_⟩
  have hcoord :
      (x₀ - s + fun j => (k j : ℝ)) i = (x₀ i - s i) + (k i : ℝ) := by
    simp [Pi.add_apply, Pi.sub_apply]
  rw [hcoord]
  -- Set up: |x₀ i - s i + k i|.
  -- Since |round((s₀ - x₀) i) - k i| ≥ 1, |s₀ - x₀)_i - round(.)| ≤ 1/2,
  -- |s_i - s₀_i| < δ, the triangle gives the bound.
  have hne_int : (round ((s₀ - x₀) i) - k i : ℤ) ≠ 0 := by
    intro h
    apply hi
    have hroundeq : round ((s₀ - x₀) i) = k i := sub_eq_zero.mp h
    exact hroundeq.symm
  have h_one_le : (1 : ℤ) ≤ |round ((s₀ - x₀) i) - k i| := Int.one_le_abs hne_int
  have h_one_le_real :
      (1 : ℝ) ≤ |((round ((s₀ - x₀) i) : ℝ) - (k i : ℝ))| := by
    have hcast : ((round ((s₀ - x₀) i) - k i : ℤ) : ℝ)
        = (round ((s₀ - x₀) i) : ℝ) - (k i : ℝ) := by push_cast; ring
    have : (1 : ℝ) ≤ ((|round ((s₀ - x₀) i) - k i| : ℤ) : ℝ) := by exact_mod_cast h_one_le
    rwa [Int.cast_abs, hcast] at this
  have hround_s0 : |(s₀ - x₀) i - (round ((s₀ - x₀) i) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have hclose : |s i - s₀ i| < δ := hs i
  -- Triangle: |round((s₀-x₀)_i) - k_i| ≤ |round - (s₀-x₀)_i| + |(s₀-x₀)_i - (s-x₀)_i|
  --                                       + |(s - x₀)_i - k_i|
  --   ≤ 1/2 + |s₀_i - s_i| + |x₀_i - s_i + k_i|
  -- Hence |x₀_i - s_i + k_i| ≥ 1 - 1/2 - δ = 1/2 - δ ≥ ε.
  -- Let A := |(x₀ i - s i) + (k i : ℝ)|. We want A ≥ ε.
  -- Note: (x₀ i - s i) + k i = -((s - x₀) i - k i), so |·| = |(s - x₀) i - k i|.
  have habs_eq :
      |(x₀ i - s i) + (k i : ℝ)| = |(s - x₀) i - (k i : ℝ)| := by
    have heq2 : (x₀ i - s i) + (k i : ℝ) = -((s - x₀) i - (k i : ℝ)) := by
      change (x₀ i - s i) + (k i : ℝ) = -((s i - x₀ i) - (k i : ℝ))
      ring
    rw [heq2]; exact abs_neg _
  rw [habs_eq]
  -- Triangle:
  -- |round - k| ≤ |round - (s₀-x₀)_i| + |(s₀-x₀)_i - (s-x₀)_i| + |(s-x₀)_i - k|
  have hsxi : (s₀ - x₀) i - (s - x₀) i = s₀ i - s i := by
    change (s₀ i - x₀ i) - (s i - x₀ i) = s₀ i - s i
    ring
  have habs_diff : |(s₀ - x₀) i - (s - x₀) i| = |s₀ i - s i| := by rw [hsxi]
  have habs_diff_swap : |s₀ i - s i| = |s i - s₀ i| := abs_sub_comm _ _
  have htri :
      |((round ((s₀ - x₀) i) : ℝ) - (k i : ℝ))| ≤
        |(s₀ - x₀) i - (round ((s₀ - x₀) i) : ℝ)|
          + |(s₀ - x₀) i - (s - x₀) i|
          + |(s - x₀) i - (k i : ℝ)| := by
    calc |((round ((s₀ - x₀) i) : ℝ) - (k i : ℝ))|
        = |((round ((s₀ - x₀) i) : ℝ) - (s₀ - x₀) i)
            + ((s₀ - x₀) i - (s - x₀) i)
            + ((s - x₀) i - (k i : ℝ))| := by ring_nf
      _ ≤ |((round ((s₀ - x₀) i) : ℝ) - (s₀ - x₀) i)
            + ((s₀ - x₀) i - (s - x₀) i)|
            + |(s - x₀) i - (k i : ℝ)| := abs_add_le _ _
      _ ≤ |((round ((s₀ - x₀) i) : ℝ) - (s₀ - x₀) i)|
            + |((s₀ - x₀) i - (s - x₀) i)|
            + |(s - x₀) i - (k i : ℝ)| := by
            have := abs_add_le ((round ((s₀ - x₀) i) : ℝ) - (s₀ - x₀) i)
              ((s₀ - x₀) i - (s - x₀) i)
            linarith
      _ = |(s₀ - x₀) i - (round ((s₀ - x₀) i) : ℝ)|
            + |(s₀ - x₀) i - (s - x₀) i|
            + |(s - x₀) i - (k i : ℝ)| := by
            rw [abs_sub_comm ((round ((s₀ - x₀) i) : ℝ)) ((s₀ - x₀) i)]
  -- δ = (1/2 - ε)/2, so 1 - 1/2 - δ = 1/2 - δ = 1/2 - (1/2-ε)/2 = (1+ε)/2 - ε/something.
  have hδeq : (1 : ℝ) / 2 - δ = ε + δ := by
    change (1 : ℝ) / 2 - (1 / 2 - ε) / 2 = ε + (1 / 2 - ε) / 2
    ring
  -- combine
  have hgoal : ε ≤ |(s - x₀) i - (k i : ℝ)| := by
    have h1 : |(s₀ - x₀) i - (s - x₀) i| < δ := by
      rw [habs_diff, habs_diff_swap]; exact hclose
    nlinarith [htri, h_one_le_real, hround_s0, h1, hδpos]
  exact hgoal

/-! ### Smoothness -/

/-- For `0 < ε < 1/2`, `bumpKernelPer d ε hε hε' x₀` is `C^∞`. -/
lemma bumpKernelPer_contDiff (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ : Fin d → ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞)) (bumpKernelPer d ε hε hε' x₀) := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  exact (singleBranch_contDiff ε hε x₀ s₀).contDiffAt.congr_of_eventuallyEq
    (bumpKernelPer_eventuallyEq_singleBranch ε hε hε' x₀ s₀)

/-! ### Periodicity -/

/-- For any periodic translation `n : Fin d → ℤ` of `s`, the
periodisation is invariant. -/
lemma bumpKernelPer_periodic (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ : Fin d → ℝ) :
    IsPeriodic (bumpKernelPer d ε hε hε' x₀) := by
  intro n s
  rw [bumpKernelPer_apply, bumpKernelPer_apply]
  -- Reindex `k ↦ k - n` (i.e. add n to the index of summation)
  -- so that `x₀ - (s + n) + k = x₀ - s + (k - n)`.
  -- Equivalently, replace `k = k' - n` for the LHS, mapping `k' = k + n`.
  let e : (Fin d → ℤ) ≃ (Fin d → ℤ) :=
    { toFun := fun k => k - n
      invFun := fun k => k + n
      left_inv := fun k => by ext i; simp
      right_inv := fun k => by ext i; simp }
  have heq := e.tsum_eq
    (f := fun k : Fin d → ℤ =>
      bumpKernel d ε hε
        (x₀ - s + fun i => ((k i : ℝ))))
  -- heq : ∑' k, f (e k) = ∑' k, f k. Need to massage LHS.
  -- LHS: ∑' k, bumpKernel ε (x₀ - (s + n) + k_ℝ).
  -- Apply the change of variable k ↦ k - n: that's e.
  have hkey : ∀ k : Fin d → ℤ,
      bumpKernel d ε hε (x₀ - (s + fun i => (n i : ℝ))
          + fun i => (k i : ℝ))
        = bumpKernel d ε hε
            (x₀ - s + fun i => ((e k) i : ℝ)) := by
    intro k
    congr 1
    ext i
    change x₀ i - (s i + (n i : ℝ)) + (k i : ℝ)
        = x₀ i - s i + ((e k) i : ℝ)
    have hek : (e k) i = k i - n i := rfl
    rw [hek]
    push_cast
    ring
  calc (∑' k : Fin d → ℤ,
          bumpKernel d ε hε
            (x₀ - (s + fun i => (n i : ℝ)) + fun i => (k i : ℝ)))
      = ∑' k : Fin d → ℤ,
          bumpKernel d ε hε
            (x₀ - s + fun i => ((e k) i : ℝ)) := tsum_congr hkey
    _ = ∑' k : Fin d → ℤ,
          bumpKernel d ε hε
            (x₀ - s + fun i => ((k i) : ℝ)) := heq

/-! ### `SmoothPeriodic` packaging -/

/-- Package `bumpKernelPer` as a `SmoothPeriodic d`. -/
noncomputable def bumpKernelPer_asSmoothPeriodic
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (x₀ : Fin d → ℝ) :
    SmoothPeriodic d where
  toFun    := bumpKernelPer d ε hε hε' x₀
  smooth   := bumpKernelPer_contDiff ε hε hε' x₀
  periodic := bumpKernelPer_periodic ε hε hε' x₀

@[simp] lemma coe_bumpKernelPer_asSmoothPeriodic
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (x₀ : Fin d → ℝ) :
    ((bumpKernelPer_asSmoothPeriodic (d := d) ε hε hε' x₀
        : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = bumpKernelPer d ε hε hε' x₀ := rfl

/-! ### Partial-derivative formula -/

/-- The Frechet derivative of `bumpKernelPer` at `s₀` agrees with the
Frechet derivative of the local single-translate branch at `s₀`. -/
lemma bumpKernelPer_fderiv_eq
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ s₀ : Fin d → ℝ) :
    fderiv ℝ (bumpKernelPer d ε hε hε' x₀) s₀ =
      fderiv ℝ (singleBranch ε hε x₀ s₀) s₀ :=
  Filter.EventuallyEq.fderiv_eq
    (bumpKernelPer_eventuallyEq_singleBranch ε hε hε' x₀ s₀)

/-- The partial derivative in coordinate `i` of the periodisation at
`s₀` equals the partial derivative of the single-translate branch
indexed by `roundVec (s₀ - x₀)`. -/
lemma bumpKernelPer_partialDeriv_eq
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x₀ s₀ : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (bumpKernelPer d ε hε hε' x₀) s₀ (Pi.basisFun ℝ (Fin d) i)
      = fderiv ℝ (singleBranch ε hε x₀ s₀) s₀ (Pi.basisFun ℝ (Fin d) i) := by
  rw [bumpKernelPer_fderiv_eq]

/-! ### Sample example -/

example (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (x₀ : Fin 2 → ℝ) :
    ∃ φ : SmoothPeriodic 2,
      (φ : (Fin 2 → ℝ) → ℝ) = bumpKernelPer 2 ε hε hε' x₀ :=
  ⟨bumpKernelPer_asSmoothPeriodic ε hε hε' x₀, rfl⟩

/-! ## IBP-on-convolution: `(∂_i B) ⋆ f = B ⋆ g_i`

We prove the IBP identity needed for the W^{1,p}-density argument:
the convolution of the partial derivative of the bump kernel with a periodic
function `f` equals the convolution of the bump kernel with the weak
derivative `g_i`. The proof relies on the periodisation `bumpKernelPer`
defined above and the IBP test-function identity
`HasWeakDerivPer.integral_eq`.

**Strategy.** Both sides reduce to unit-cube integrals against
`bumpKernelPer` and its `s`-derivative via the fundamental-domain
decomposition `∫_{ℝ^d} G = ∑' k, ∫_{UnitCube} G(s + k_ℝ)` and the
collapse-to-single-term identity `bumpKernelPer_eq_single`. The IBP step
is one application of `HasWeakDerivPer.integral_eq` against the test
function `bumpKernelPer_asSmoothPeriodic ε hε hε' x`.
-/

section IBP

variable {d : ℕ}

open MeasureTheory Set Function Filter
open scoped ContDiff Topology ENNReal

/-- The convolution `(K ⋆ f) x` written as an integral over `s` of
`K(x - s) * f(s)`. This is `convolution_eq_swap` specialised to
`L = lsmul ℝ ℝ` for real-valued functions. -/
private lemma convolution_eq_integral_swap
    (K f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    MeasureTheory.convolution K f (ContinuousLinearMap.lsmul ℝ ℝ)
        (volume : Measure (Fin d → ℝ)) x =
      ∫ s, K (x - s) * f s ∂(volume : Measure (Fin d → ℝ)) := by
  rw [MeasureTheory.convolution_eq_swap]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The integrand `s ↦ K(x - s) * f(s)` for a continuous compactly-supported
`K` and locally-integrable `f` is integrable over ℝ^d. Obtained via
`HasCompactSupport.convolutionExists_left` and `integrable_swap`. -/
private lemma integrable_kernel_translate
    (K : (Fin d → ℝ) → ℝ) (hK_cont : Continuous K)
    (hK_supp : HasCompactSupport K)
    {f : (Fin d → ℝ) → ℝ} (hf_loc : LocallyIntegrable f volume)
    (x : Fin d → ℝ) :
    Integrable (fun s : Fin d → ℝ =>
        K (x - s) * f s) (volume : Measure (Fin d → ℝ)) := by
  have hConv : ConvolutionExistsAt K f x
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Fin d → ℝ)) :=
    hK_supp.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hK_cont hf_loc x
  have hSwap := hConv.integrable_swap
  -- `hSwap : Integrable (fun s => lsmul ℝ ℝ (K (x - s)) (f s))`.
  refine hSwap.congr ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-! The pointwise tsum `s ↦ ∑' k : Fin d → ℤ, K(x - s + k_ℝ)` evaluated.
For the bump kernel with `ε < 1/2`, this collapses to a single nonzero
term — but we state the lemma generically. The key abstract identity used
below is the change of summation index inside an integer-lattice
fundamental-domain integral. -/

/-- **Key change-of-variable identity.** For continuous compactly-supported
`K` and periodic locally-integrable `f`, the convolution-style integral
`∫_{ℝ^d} K(x - s) · f(s) ds` decomposes into the sum-over-lattice of
unit-cube integrals of translated kernels times `f` (no swap of sum/integral
yet). -/
private lemma integral_kernel_translate_eq_tsum_unitCube
    (K : (Fin d → ℝ) → ℝ) (hK_cont : Continuous K)
    (hK_supp : HasCompactSupport K)
    {f : (Fin d → ℝ) → ℝ} (hf_per : IsPeriodic f)
    (hf_loc : LocallyIntegrable f volume) (x : Fin d → ℝ) :
    ∫ s, K (x - s) * f s ∂(volume : Measure (Fin d → ℝ)) =
      ∑' k : ZLatGroup d,
        ∫ s in UnitCube d, K (x - s - (k : Fin d → ℝ)) * f s
          ∂(volume : Measure (Fin d → ℝ)) := by
  have hint : Integrable (fun s : Fin d → ℝ => K (x - s) * f s) volume :=
    integrable_kernel_translate K hK_cont hK_supp hf_loc x
  -- Use `integral_eq_tsum''` on the unit-cube fundamental domain.
  rw [unitCube_isAddFundamentalDomain.integral_eq_tsum''
      (fun s => K (x - s) * f s) hint]
  refine tsum_congr (fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  -- Goal: K(x - (k +ᵥ s)) * f(k +ᵥ s) = K(x - s - k_ℝ) * f s.
  have hper : f ((k : Fin d → ℝ) +ᵥ s) = f s :=
    isPeriodic_toZLatGroup_invariant hf_per k s
  change K (x - ((k : Fin d → ℝ) + s)) * f ((k : Fin d → ℝ) +ᵥ s)
      = K (x - s - (k : Fin d → ℝ)) * f s
  rw [hper]
  congr 1
  abel

/-- The tsum-of-unit-cube-integrals can be reindexed `k ↦ -k`, since the
lattice `ZLatGroup d` is closed under negation and the family is a
formal tsum (the `Equiv.neg` reindexing is shape-preserving). -/
private lemma tsum_unitCube_reindex_neg
    (K : (Fin d → ℝ) → ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (∑' k : ZLatGroup d,
        ∫ s in UnitCube d, K (x - s - (k : Fin d → ℝ)) * f s
          ∂(volume : Measure (Fin d → ℝ))) =
      ∑' k : ZLatGroup d,
        ∫ s in UnitCube d, K (x - s + (k : Fin d → ℝ)) * f s
          ∂(volume : Measure (Fin d → ℝ)) := by
  -- Use `Equiv.neg (ZLatGroup d) : (ZLatGroup d) ≃ (ZLatGroup d)`.
  rw [← (Equiv.neg (ZLatGroup d)).tsum_eq
        (f := fun k : ZLatGroup d =>
          ∫ s in UnitCube d, K (x - s - (k : Fin d → ℝ)) * f s
            ∂(volume : Measure (Fin d → ℝ)))]
  refine tsum_congr (fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  -- `(Equiv.neg _ k : Fin d → ℝ) = -(k : Fin d → ℝ)`.
  have hcoe : ((Equiv.neg (ZLatGroup d) k : ZLatGroup d) : Fin d → ℝ)
      = -(k : Fin d → ℝ) := rfl
  change K (x - s - ((Equiv.neg (ZLatGroup d) k : ZLatGroup d) : Fin d → ℝ)) * f s
      = K (x - s + (k : Fin d → ℝ)) * f s
  rw [hcoe]
  congr 2
  abel

/-- The lintegral version of the fundamental-domain decomposition for
`s ↦ ‖K(x - s) f s‖ₑ`. Used to certify summability for `integral_tsum`.

Relaxed (infra-P5-T10): the hypotheses on `K` and `f` are not used in the
proof body; kept as `AEStronglyMeasurable` for API uniformity. -/
private lemma lintegral_kernel_translate_eq_tsum_unitCube
    (K : (Fin d → ℝ) → ℝ)
    (_hK_meas : MeasureTheory.AEStronglyMeasurable K
      (volume : Measure (Fin d → ℝ)))
    {f : (Fin d → ℝ) → ℝ}
    (_hf_meas : MeasureTheory.AEStronglyMeasurable f
      (volume : Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (x : Fin d → ℝ) :
    ∫⁻ s, ‖K (x - s) * f s‖ₑ ∂(volume : Measure (Fin d → ℝ)) =
      ∑' k : ZLatGroup d,
        ∫⁻ s in UnitCube d, ‖K (x - s + (k : Fin d → ℝ)) * f s‖ₑ
          ∂(volume : Measure (Fin d → ℝ)) := by
  -- Step 1: apply `lintegral_eq_tsum''` for the fundamental domain.
  rw [unitCube_isAddFundamentalDomain.lintegral_eq_tsum''
        (fun s => ‖K (x - s) * f s‖ₑ)]
  -- Step 2: rewrite each summand using periodicity of `f` and reindex `k → -k`.
  rw [← (Equiv.neg (ZLatGroup d)).tsum_eq
        (f := fun k : ZLatGroup d =>
          ∫⁻ s in UnitCube d, ‖K (x - s + (k : Fin d → ℝ)) * f s‖ₑ
            ∂(volume : Measure (Fin d → ℝ)))]
  refine tsum_congr (fun k => ?_)
  refine setLIntegral_congr_fun measurableSet_unitCube
    (fun s _ => ?_)
  have hper : f ((k : Fin d → ℝ) +ᵥ s) = f s :=
    isPeriodic_toZLatGroup_invariant hf_per k s
  have hcoe : ((Equiv.neg (ZLatGroup d) k : ZLatGroup d) : Fin d → ℝ)
      = -(k : Fin d → ℝ) := rfl
  change ‖K (x - ((k : Fin d → ℝ) + s)) * f ((k : Fin d → ℝ) +ᵥ s)‖ₑ
      = ‖K (x - s + ((Equiv.neg (ZLatGroup d) k : ZLatGroup d) : Fin d → ℝ)) * f s‖ₑ
  rw [hper, hcoe]
  have heq : x - ((k : Fin d → ℝ) + s) = x - s + -(k : Fin d → ℝ) := by abel
  rw [heq]

/-- The summability check needed for `integral_tsum`: under continuous
compactly-supported `K` and periodic locally-integrable `f`, the tsum
of unit-cube `lintegral`-norms is finite.

Relaxed (infra-P5-T10): `f` only needs `AEStronglyMeasurable` (used
internally only as forwarded API hypothesis). -/
private lemma tsum_lintegral_kernel_translate_lt_top
    (K : (Fin d → ℝ) → ℝ) (hK_cont : Continuous K)
    (hK_supp : HasCompactSupport K)
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (volume : Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : LocallyIntegrable f volume) (x : Fin d → ℝ) :
    (∑' k : ZLatGroup d,
        ∫⁻ s in UnitCube d, ‖K (x - s + (k : Fin d → ℝ)) * f s‖ₑ
          ∂(volume : Measure (Fin d → ℝ))) ≠ (⊤ : ℝ≥0∞) := by
  -- Identify the tsum with the ℝ^d-lintegral of `‖K(x-·) * f‖`.
  rw [← lintegral_kernel_translate_eq_tsum_unitCube K
        hK_cont.aestronglyMeasurable
        hf_meas hf_per x]
  -- The ℝ^d-lintegral is the `enorm` of the integral of an integrable
  -- function, hence finite.
  have hint : Integrable (fun s : Fin d → ℝ => K (x - s) * f s) volume :=
    integrable_kernel_translate K hK_cont hK_supp hf_loc x
  exact hint.2.ne

/-- **Headline reduction lemma.** For continuous compactly-supported `K`
and periodic locally-integrable `f`, the convolution `(K ⋆ f)(x)` equals
the unit-cube integral of `(s ↦ ∑' k, K(x - s + k_ℝ)) · f(s)`.

Relaxed (infra-P5-T10): `f` only needs `AEStronglyMeasurable f volume`
(used at line ~635 to certify integrability for `integral_tsum`). -/
private lemma convolution_eq_unitCube_integral_tsum
    (K : (Fin d → ℝ) → ℝ) (hK_cont : Continuous K)
    (hK_supp : HasCompactSupport K)
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (volume : Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : LocallyIntegrable f volume) (x : Fin d → ℝ) :
    MeasureTheory.convolution K f (ContinuousLinearMap.lsmul ℝ ℝ)
        (volume : Measure (Fin d → ℝ)) x =
      ∫ s in UnitCube d,
          (∑' k : ZLatGroup d, K (x - s + (k : Fin d → ℝ))) * f s
        ∂(volume : Measure (Fin d → ℝ)) := by
  -- LHS via `convolution_eq_swap`.
  rw [convolution_eq_integral_swap K f x]
  -- LHS = `∑' k, ∫_{UnitCube} K(x - s - k_ℝ) f s` (fundamental domain).
  rw [integral_kernel_translate_eq_tsum_unitCube K hK_cont hK_supp hf_per hf_loc x]
  -- Reindex k → -k.
  rw [tsum_unitCube_reindex_neg K f x]
  -- Now swap tsum and integral.
  have hae_meas : ∀ k : ZLatGroup d, AEStronglyMeasurable
      (fun s : Fin d → ℝ => K (x - s + (k : Fin d → ℝ)) * f s)
      ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)) := by
    intro k
    have hcont : Continuous
        (fun s : Fin d → ℝ => K (x - s + (k : Fin d → ℝ))) :=
      hK_cont.comp ((continuous_const.sub continuous_id).add continuous_const)
    refine (hcont.aestronglyMeasurable.mul ?_)
    exact hf_meas.restrict
  have hsum_finite :=
    tsum_lintegral_kernel_translate_lt_top K hK_cont hK_supp hf_meas hf_per hf_loc x
  have hswap := MeasureTheory.integral_tsum (μ :=
      ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)))
    (f := fun (k : ZLatGroup d) (s : Fin d → ℝ) =>
      K (x - s + (k : Fin d → ℝ)) * f s)
    hae_meas hsum_finite
  -- `hswap : ∫_{UnitCube} ∑' k, ... = ∑' k, ∫_{UnitCube} ...`.
  rw [← hswap]
  -- Now pull `f s` out of the tsum.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  change (∑' k : ZLatGroup d, K (x - s + (k : Fin d → ℝ)) * f s)
      = (∑' k : ZLatGroup d, K (x - s + (k : Fin d → ℝ))) * f s
  rw [tsum_mul_right]

/-! ### Identification: tsum-over-`ZLatGroup` = `bumpKernelPer`

Both tsums have at most one nonzero term (by `ε < 1/2`), so we collapse
both to a single value via `tsum_eq_single`.
-/

/-- For `ε < 1/2`, the tsum over `ZLatGroup d` of bump-kernel translates
collapses to a single nonzero term. The unique witness is the lattice
element with real-coordinates equal to `roundVec (s - x)`. -/
private lemma tsum_zlatgroup_bumpKernel_eq_bumpKernelPer
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (x s : Fin d → ℝ) :
    (∑' k : ZLatGroup d, bumpKernel d ε hε (x - s + (k : Fin d → ℝ)))
      = bumpKernelPer d ε hε hε' x s := by
  -- Step 1: rewrite `bumpKernelPer` to its single-term collapse.
  rw [bumpKernelPer_eq_single ε hε hε' x s]
  -- Step 2: identify the unique nonzero term in the ZLatGroup tsum.
  -- The witness is `intToZLat (roundVec (s - x))`.
  set rv : Fin d → ℝ := fun i => ((roundVec (s - x)) i : ℝ) with hrv_def
  have hrvLat : rv ∈ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) :
      Submodule ℤ (Fin d → ℝ)) := by
    -- `rv = ∑ i, (roundVec (s - x)) i • Pi.basisFun ℝ (Fin d) i`.
    have hsum : rv = ∑ i : Fin d,
        (roundVec (s - x)) i • (Pi.basisFun ℝ (Fin d) i : Fin d → ℝ) := by
      funext j
      simp only [hrv_def, Finset.sum_apply]
      classical
      rw [Finset.sum_eq_single j]
      · simp [Pi.basisFun_apply]
      · intro i _ hij
        simp [Pi.basisFun_apply, Pi.single_apply, hij.symm]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    refine Submodule.smul_of_tower_mem _ _ ?_
    exact Submodule.subset_span ⟨i, rfl⟩
  set vrv : ZLatGroup d := ⟨rv, hrvLat⟩ with hvrv_def
  refine tsum_eq_single vrv ?_ |>.trans ?_
  · -- For `k ≠ vrv`, the term is zero. Need to show: `(k : Fin d → ℝ) ≠ rv`,
    -- so some coordinate differs from the rounding, then bump vanishes.
    intro k hk
    -- `(k : Fin d → ℝ) ≠ rv`.
    have hne : (k : Fin d → ℝ) ≠ rv := fun h => hk (Subtype.ext h)
    -- Find a coordinate where they differ.
    have hexists : ∃ i, (k : Fin d → ℝ) i ≠ rv i := by
      by_contra hall
      apply hne
      funext i
      exact not_not.mp (fun h => hall ⟨i, h⟩)
    obtain ⟨i, hi⟩ := hexists
    -- For this `i`, the `i`-th coord of `x - s + k_ℝ` has |·| ≥ ε.
    refine bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨i, ?_⟩
    have hcoord : (x - s + (k : Fin d → ℝ)) i = (x i - s i) + (k : Fin d → ℝ) i := by
      simp [Pi.add_apply, Pi.sub_apply]
    rw [hcoord]
    -- Now reduce to bound on `(s - x) i - (k : ...) i`.
    have habs_eq : |(x i - s i) + (k : Fin d → ℝ) i|
        = |(s - x) i - (k : Fin d → ℝ) i| := by
      have heq2 : (x i - s i) + (k : Fin d → ℝ) i
          = -((s - x) i - (k : Fin d → ℝ) i) := by
        change (x i - s i) + (k : Fin d → ℝ) i
            = -((s i - x i) - (k : Fin d → ℝ) i)
        ring
      rw [heq2]; exact abs_neg _
    rw [habs_eq]
    -- We have `|(k : Fin d → ℝ) i - rv i| ≥ 1` because they're integers and
    -- different; combined with `|s_i - x_i - rv_i| ≤ 1/2`.
    -- Actually we need: the integer `(k : Fin d → ℝ) i` differs from `rv i = round((s-x) i)`.
    -- But how do we know `(k : ℝ) i` is an integer? From the membership hypothesis.
    have hkint : ∃ m : ℤ, (k : Fin d → ℝ) i = (m : ℝ) := by
      have hkmem := k.2
      have hrepr := ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ
        (k : Fin d → ℝ)).mp hkmem i
      rcases hrepr with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have h2 : (Pi.basisFun ℝ (Fin d)).repr (k : Fin d → ℝ) i = (k : Fin d → ℝ) i := by
        simp
      rw [← h2, ← hm]
      simp [algebraMap_int_eq, eq_intCast]
    obtain ⟨m, hm⟩ := hkint
    have hrv_i : rv i = (((roundVec (s - x)) i : ℤ) : ℝ) := by simp [hrv_def]
    -- `m ≠ roundVec (s - x) i` because `(k : ...) i ≠ rv i`.
    have hmne : m ≠ (roundVec (s - x)) i := by
      intro hmeq
      apply hi
      rw [hm, hrv_i]
      exact_mod_cast hmeq
    -- Triangle: `|round((s-x)_i) - m| ≤ |(s-x)_i - m| + |(s-x)_i - round((s-x)_i)|`
    have hround : |(s - x) i - ((roundVec (s - x)) i : ℝ)| ≤ 1 / 2 := by
      simpa using abs_sub_round ((s - x) i)
    have h_one_le : (1 : ℤ) ≤ |((roundVec (s - x)) i) - m| :=
      Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmne))
    have h_one_le_real :
        (1 : ℝ) ≤ |(((roundVec (s - x)) i : ℝ)) - (m : ℝ)| := by
      have hcast :
          (((((roundVec (s - x)) i) - m : ℤ) : ℝ)
            = (((roundVec (s - x)) i : ℝ)) - (m : ℝ)) := by push_cast; ring
      have : (1 : ℝ) ≤ ((|((roundVec (s - x)) i) - m| : ℤ) : ℝ) := by
        exact_mod_cast h_one_le
      rwa [Int.cast_abs, hcast] at this
    have htri :
        |(((roundVec (s - x)) i : ℝ)) - (m : ℝ)| ≤
          |(s - x) i - (m : ℝ)| + |(s - x) i - (((roundVec (s - x)) i : ℝ))| := by
      calc |(((roundVec (s - x)) i : ℝ)) - (m : ℝ)|
          = |((((roundVec (s - x)) i : ℝ)) - (s - x) i) + ((s - x) i - (m : ℝ))| := by
            ring_nf
        _ ≤ |((((roundVec (s - x)) i : ℝ)) - (s - x) i)| + |(s - x) i - (m : ℝ)| :=
            abs_add_le _ _
        _ = |(s - x) i - (((roundVec (s - x)) i : ℝ))| + |(s - x) i - (m : ℝ)| := by
            rw [abs_sub_comm]
        _ = |(s - x) i - (m : ℝ)| + |(s - x) i - (((roundVec (s - x)) i : ℝ))| := by
            ring
    rw [hm]
    linarith
  · -- The remaining single-term equals the same form as the right-hand side.
    show bumpKernel d ε hε (x - s + (vrv : Fin d → ℝ))
        = bumpKernel d ε hε
          (x - s + fun i => ((roundVec (s - x)) i : ℝ))
    rfl

/-! ### Partial-kernel single-term collapse

The partial kernel `partialKernel d ε hε i` has support inside the same
closed box `[-ε, ε]^d` as the bump kernel itself, since outside that box
the bump kernel is zero on a neighborhood and the Frechet derivative
vanishes there. We record the consequence: for `ε < 1/2`, the lattice tsum
of `partialKernel` translates collapses to a single term.
-/

/-- The partial kernel vanishes outside the open box `(-ε, ε)^d`: for any
`t` with some coordinate `|t i| > ε`, `partialKernel d ε hε i t = 0`. -/
private lemma partialKernel_eq_zero_of_exists_abs_gt
    (ε : ℝ) (hε : 0 < ε) (i : Fin d) {t : Fin d → ℝ}
    (ht : ∃ j, ε < |t j|) :
    partialKernel d ε hε i t = 0 := by
  -- The bump kernel vanishes on a neighborhood of `t`, so its derivative is 0.
  obtain ⟨j, hj⟩ := ht
  -- Choose `δ := |t j| - ε > 0` so a small ball around `t` still has `|· j| > ε`.
  set δ : ℝ := |t j| - ε with hδ_def
  have hδpos : 0 < δ := by simpa [hδ_def] using sub_pos.mpr hj
  -- On the ball `{u : ∀ k, |u k - t k| < δ}` the bump kernel is zero.
  have hball_open : IsOpen
      ({u : Fin d → ℝ | ∀ k, |u k - t k| < δ}) := by
    have heq : ({u : Fin d → ℝ | ∀ k, |u k - t k| < δ})
        = ⋂ k : Fin d, {u : Fin d → ℝ | |u k - t k| < δ} := by
      ext u; simp [Set.mem_iInter]
    rw [heq]
    refine isOpen_iInter_of_finite (fun k => ?_)
    have hcont : Continuous (fun u : Fin d → ℝ => u k - t k) :=
      (continuous_apply k).sub continuous_const
    exact isOpen_lt (continuous_abs.comp hcont) continuous_const
  have hmem : t ∈ {u : Fin d → ℝ | ∀ k, |u k - t k| < δ} := by
    intro k; simpa using hδpos
  have hzero_on_nbhd : (fun u => bumpKernel d ε hε u) =ᶠ[𝓝 t] 0 := by
    refine eventuallyEq_of_mem (hball_open.mem_nhds hmem) ?_
    intro u hu
    refine bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨j, ?_⟩
    have huj : |u j - t j| < δ := hu j
    -- |u j| ≥ |t j| - |u j - t j| > |t j| - δ = ε.
    have : ε ≤ |u j| := by
      have hgt : ε < |u j| := by
        have htri : |t j| - |u j - t j| ≤ |u j| := by
          have h1 : |t j| ≤ |u j| + |u j - t j| := by
            have := abs_add_le (u j) (t j - u j)
            simp at this
            calc |t j| = |u j + (t j - u j)| := by ring_nf
              _ ≤ |u j| + |t j - u j| := abs_add_le _ _
              _ = |u j| + |u j - t j| := by rw [abs_sub_comm]
          linarith
        have h2 : |t j| - δ < |u j| := by linarith
        have hsimp : |t j| - δ = ε := by
          show |t j| - (|t j| - ε) = ε; ring
        rw [hsimp] at h2; exact h2
      exact le_of_lt hgt
    exact this
  -- `fderiv` of an eventually-zero function is zero.
  have hfderiv : fderiv ℝ (bumpKernel d ε hε) t = 0 := by
    have hconst : fderiv ℝ (fun _ : Fin d → ℝ => (0 : ℝ)) t = 0 :=
      fderiv_const_apply (0 : ℝ)
    rw [← hconst]
    exact Filter.EventuallyEq.fderiv_eq hzero_on_nbhd
  show fderiv ℝ (bumpKernel d ε hε) t (Pi.basisFun ℝ (Fin d) i) = 0
  rw [hfderiv]
  rfl

/-- For `ε < 1/2`, the tsum over `ZLatGroup d` of `partialKernel d ε hε i`
translates collapses to the single nonzero term at the lattice element
matching `roundVec (s - x)`. -/
private lemma tsum_zlatgroup_partialKernel_eq_single
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (i : Fin d) (x s : Fin d → ℝ) :
    (∑' k : ZLatGroup d, partialKernel d ε hε i (x - s + (k : Fin d → ℝ)))
      = partialKernel d ε hε i
          (x - s + fun j => ((roundVec (s - x)) j : ℝ)) := by
  -- Same structure as the bump-kernel collapse, but using
  -- `partialKernel_eq_zero_of_exists_abs_gt` for the kill.
  set rv : Fin d → ℝ := fun i => ((roundVec (s - x)) i : ℝ) with hrv_def
  have hrvLat : rv ∈ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) :
      Submodule ℤ (Fin d → ℝ)) := by
    have hsum : rv = ∑ i : Fin d,
        (roundVec (s - x)) i • (Pi.basisFun ℝ (Fin d) i : Fin d → ℝ) := by
      funext j
      simp only [hrv_def, Finset.sum_apply]
      classical
      rw [Finset.sum_eq_single j]
      · simp [Pi.basisFun_apply]
      · intro i _ hij
        simp [Pi.basisFun_apply, Pi.single_apply, hij.symm]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    refine Submodule.smul_of_tower_mem _ _ ?_
    exact Submodule.subset_span ⟨i, rfl⟩
  set vrv : ZLatGroup d := ⟨rv, hrvLat⟩ with hvrv_def
  refine tsum_eq_single vrv ?_ |>.trans ?_
  · intro k hk
    have hne : (k : Fin d → ℝ) ≠ rv := fun h => hk (Subtype.ext h)
    have hexists : ∃ i, (k : Fin d → ℝ) i ≠ rv i := by
      by_contra hall
      apply hne
      funext i
      exact not_not.mp (fun h => hall ⟨i, h⟩)
    obtain ⟨ic, hic⟩ := hexists
    refine partialKernel_eq_zero_of_exists_abs_gt ε hε i ⟨ic, ?_⟩
    have hcoord : (x - s + (k : Fin d → ℝ)) ic
        = (x ic - s ic) + (k : Fin d → ℝ) ic := by
      simp [Pi.add_apply, Pi.sub_apply]
    rw [hcoord]
    -- Now the same arithmetic as for bumpKernel above: |·| > ε.
    have habs_eq : |(x ic - s ic) + (k : Fin d → ℝ) ic|
        = |(s - x) ic - (k : Fin d → ℝ) ic| := by
      have heq2 : (x ic - s ic) + (k : Fin d → ℝ) ic
          = -((s - x) ic - (k : Fin d → ℝ) ic) := by
        change (x ic - s ic) + (k : Fin d → ℝ) ic
            = -((s ic - x ic) - (k : Fin d → ℝ) ic)
        ring
      rw [heq2]; exact abs_neg _
    rw [habs_eq]
    have hkint : ∃ m : ℤ, (k : Fin d → ℝ) ic = (m : ℝ) := by
      have hkmem := k.2
      have hrepr := ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ
        (k : Fin d → ℝ)).mp hkmem ic
      rcases hrepr with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have h2 : (Pi.basisFun ℝ (Fin d)).repr (k : Fin d → ℝ) ic = (k : Fin d → ℝ) ic := by
        simp
      rw [← h2, ← hm]
      simp [algebraMap_int_eq, eq_intCast]
    obtain ⟨m, hm⟩ := hkint
    have hrv_i : rv ic = (((roundVec (s - x)) ic : ℤ) : ℝ) := by simp [hrv_def]
    have hmne : m ≠ (roundVec (s - x)) ic := by
      intro hmeq
      apply hic
      rw [hm, hrv_i]
      exact_mod_cast hmeq
    have hround : |(s - x) ic - ((roundVec (s - x)) ic : ℝ)| ≤ 1 / 2 := by
      simpa using abs_sub_round ((s - x) ic)
    have h_one_le : (1 : ℤ) ≤ |((roundVec (s - x)) ic) - m| :=
      Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmne))
    have h_one_le_real :
        (1 : ℝ) ≤ |(((roundVec (s - x)) ic : ℝ)) - (m : ℝ)| := by
      have hcast :
          (((((roundVec (s - x)) ic) - m : ℤ) : ℝ)
            = (((roundVec (s - x)) ic : ℝ)) - (m : ℝ)) := by push_cast; ring
      have : (1 : ℝ) ≤ ((|((roundVec (s - x)) ic) - m| : ℤ) : ℝ) := by
        exact_mod_cast h_one_le
      rwa [Int.cast_abs, hcast] at this
    have htri :
        |(((roundVec (s - x)) ic : ℝ)) - (m : ℝ)| ≤
          |(s - x) ic - (m : ℝ)|
            + |(s - x) ic - (((roundVec (s - x)) ic : ℝ))| := by
      calc |(((roundVec (s - x)) ic : ℝ)) - (m : ℝ)|
          = |((((roundVec (s - x)) ic : ℝ)) - (s - x) ic)
                + ((s - x) ic - (m : ℝ))| := by ring_nf
        _ ≤ |((((roundVec (s - x)) ic : ℝ)) - (s - x) ic)|
              + |(s - x) ic - (m : ℝ)| := abs_add_le _ _
        _ = |(s - x) ic - (((roundVec (s - x)) ic : ℝ))|
              + |(s - x) ic - (m : ℝ)| := by rw [abs_sub_comm]
        _ = |(s - x) ic - (m : ℝ)|
              + |(s - x) ic - (((roundVec (s - x)) ic : ℝ))| := by ring
    rw [hm]
    -- Need strict |·| > ε. We have ≥ 1/2 > ε from triangle.
    -- 1 ≤ |...| ≤ |(s-x)_ic - m| + 1/2, so |(s-x)_ic - m| ≥ 1/2 > ε.
    have hstrict : ε < 1 / 2 := hε'
    nlinarith
  · -- Single-term match.
    show partialKernel d ε hε i (x - s + (vrv : Fin d → ℝ))
        = partialKernel d ε hε i
            (x - s + fun j => ((roundVec (s - x)) j : ℝ))
    rfl

/-! ### Partial-derivative of `bumpKernelPer` via chain rule -/

/-- The partial derivative in `s_i` of `bumpKernelPer x` at `s` equals
`-partialKernel d ε hε i (x - s + roundVec(s - x)_ℝ)`, by chain rule on the
local single-translate branch. -/
private lemma bumpKernelPer_partialDeriv_apply
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (i : Fin d) (x s : Fin d → ℝ) :
    fderiv ℝ (bumpKernelPer d ε hε hε' x) s (Pi.basisFun ℝ (Fin d) i)
      = - partialKernel d ε hε i
          (x - s + fun j => ((roundVec (s - x)) j : ℝ)) := by
  -- Use `bumpKernelPer_partialDeriv_eq` to switch to the single branch.
  rw [bumpKernelPer_partialDeriv_eq]
  -- Now compute fderiv of `singleBranch ε hε x s` at `s` evaluated at `e_i`.
  -- `singleBranch ε hε x s = fun u => B(x - u + roundVec(s - x)_ℝ)`.
  set c : Fin d → ℝ := fun j => ((roundVec (s - x)) j : ℝ) with hc_def
  -- The function `singleBranch ε hε x s` equals `B ∘ (fun u => x - u + c)`.
  have hcomp : singleBranch ε hε x s = (bumpKernel d ε hε) ∘
      (fun u : Fin d → ℝ => x - u + c) := rfl
  rw [hcomp]
  -- Chain rule.
  have h_inner : HasFDerivAt (fun u : Fin d → ℝ => x - u + c)
      (-(ContinuousLinearMap.id ℝ (Fin d → ℝ))) s := by
    have h1 : HasFDerivAt (fun u : Fin d → ℝ => x - u)
        (-(ContinuousLinearMap.id ℝ (Fin d → ℝ))) s := by
      have := (hasFDerivAt_id s (𝕜 := ℝ)).const_sub x
      simpa using this
    have := h1.add_const c
    simpa using this
  have h_outer : HasFDerivAt (bumpKernel d ε hε)
      (fderiv ℝ (bumpKernel d ε hε) (x - s + c)) (x - s + c) := by
    have hdiff : Differentiable ℝ (bumpKernel d ε hε) := by
      have := (bumpKernel_contDiff d ε hε)
      exact this.differentiable (by decide)
    exact (hdiff (x - s + c)).hasFDerivAt
  have hcomp_deriv := h_outer.comp s h_inner
  rw [hcomp_deriv.fderiv]
  -- Goal: `(fderiv B (x-s+c)).comp (-id) e_i = -partialKernel d ε hε i (x-s+c)`.
  show ((fderiv ℝ (bumpKernel d ε hε) (x - s + c)).comp
      (-(ContinuousLinearMap.id ℝ (Fin d → ℝ)))) (Pi.basisFun ℝ (Fin d) i)
      = - partialKernel d ε hε i (x - s + c)
  simp [partialKernel_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]

/-! ### Headline IBP-on-convolution identity -/

/-- **Headline theorem.** For periodic locally-integrable `f` with weak
derivative `g_i` (i.e. `HasWeakDerivPer i f g_i`) and periodic
locally-integrable `g_i`, and any `0 < ε < 1/2`,

`((partialKernel d ε hε i) ⋆ f)(x) = (bumpKernel d ε hε ⋆ g_i)(x)`

pointwise for every `x : Fin d → ℝ`. The proof reduces both convolutions
to unit-cube integrals against `bumpKernelPer x` (or its `s`-derivative),
then applies `HasWeakDerivPer.integral_eq` once. -/
theorem convolution_partialKernel_eq_convolution_weakDeriv
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) (i : Fin d)
    {f g_i : (Fin d → ℝ) → ℝ}
    -- Relaxed (infra-P5-T10): `Measurable` → `AEStronglyMeasurable`.
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (volume : Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : LocallyIntegrable f volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g_i
      (volume : Measure (Fin d → ℝ)))
    (hg_per : IsPeriodic g_i)
    (hg_loc : LocallyIntegrable g_i volume)
    (hweak : HasWeakDerivPer i f g_i) (x : Fin d → ℝ) :
    MeasureTheory.convolution (partialKernel d ε hε i) f
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Fin d → ℝ)) x =
      MeasureTheory.convolution (bumpKernel d ε hε) g_i
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Fin d → ℝ)) x := by
  -- Step 1: Express RHS = `(B ⋆ g_i)(x)` as cube-integral against `bumpKernelPer`.
  have hRHS :
      MeasureTheory.convolution (bumpKernel d ε hε) g_i
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
        ∫ s in UnitCube d, bumpKernelPer d ε hε hε' x s * g_i s
          ∂(volume : Measure (Fin d → ℝ)) := by
    rw [convolution_eq_unitCube_integral_tsum (bumpKernel d ε hε)
        (bumpKernel_contDiff d ε hε).continuous
        (bumpKernel_hasCompactSupport d ε hε) hg_meas hg_per hg_loc x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    change (∑' k : ZLatGroup d, bumpKernel d ε hε (x - s + (k : Fin d → ℝ))) * g_i s
        = bumpKernelPer d ε hε hε' x s * g_i s
    rw [tsum_zlatgroup_bumpKernel_eq_bumpKernelPer ε hε hε' x s]
  -- Step 2: Express LHS = `((∂_i B) ⋆ f)(x)` as cube-integral against
  -- `(s ↦ ∑' k, partialKernel(x - s + k_ℝ))`, which by single-collapse
  -- equals `partialKernel(x - s + roundVec_ℝ) = -∂_{s_i}(bumpKernelPer x)(s)`.
  have hLHS :
      MeasureTheory.convolution (partialKernel d ε hε i) f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
        ∫ s in UnitCube d,
            (- fderiv ℝ (bumpKernelPer d ε hε hε' x) s
              (Pi.basisFun ℝ (Fin d) i)) * f s
          ∂(volume : Measure (Fin d → ℝ)) := by
    rw [convolution_eq_unitCube_integral_tsum (partialKernel d ε hε i)
        (partialKernel_continuous d ε hε i)
        (partialKernel_hasCompactSupport d ε hε i) hf_meas hf_per hf_loc x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    change (∑' k : ZLatGroup d, partialKernel d ε hε i (x - s + (k : Fin d → ℝ))) * f s
        = (- fderiv ℝ (bumpKernelPer d ε hε hε' x) s
            (Pi.basisFun ℝ (Fin d) i)) * f s
    rw [tsum_zlatgroup_partialKernel_eq_single ε hε hε' i x s,
        bumpKernelPer_partialDeriv_apply ε hε hε' i x s]
    ring
  -- Step 3: Apply `HasWeakDerivPer.integral_eq` against
  -- `bumpKernelPer_asSmoothPeriodic ε hε hε' x`.
  set φ : SmoothPeriodic d := bumpKernelPer_asSmoothPeriodic ε hε hε' x with hφ_def
  have hibp := hweak.integral_eq φ
  rw [hLHS, hRHS]
  -- `(φ : (Fin d → ℝ) → ℝ) = bumpKernelPer d ε hε hε' x` definitionally.
  -- `(SmoothPeriodic.partialDeriv i φ : ...) s = fderiv (bumpKernelPer x) s (e_i)`
  -- definitionally too (by `coe_partialDeriv`).
  -- So `hibp : ∫_{cube} g_i · bumpKernelPer x = -∫_{cube} f · ∂_{s_i}(bumpKernelPer x)`.
  unfold periodicIntegral at hibp
  -- Massage to commute multiplications and signs.
  have hcomm1 : ∀ s, bumpKernelPer d ε hε hε' x s * g_i s
      = g_i s * bumpKernelPer d ε hε hε' x s := fun s => by ring
  have hcomm2 : ∀ s,
      (- fderiv ℝ (bumpKernelPer d ε hε hε' x) s (Pi.basisFun ℝ (Fin d) i)) * f s
        = -(f s * fderiv ℝ (bumpKernelPer d ε hε hε' x) s
            (Pi.basisFun ℝ (Fin d) i)) := fun s => by ring
  rw [show (fun s : Fin d → ℝ =>
        bumpKernelPer d ε hε hε' x s * g_i s)
      = (fun s => g_i s * bumpKernelPer d ε hε hε' x s) from funext hcomm1]
  rw [show (fun s : Fin d → ℝ =>
        (- fderiv ℝ (bumpKernelPer d ε hε hε' x) s (Pi.basisFun ℝ (Fin d) i)) * f s)
      = (fun s => -(f s *
          fderiv ℝ (bumpKernelPer d ε hε hε' x) s (Pi.basisFun ℝ (Fin d) i))) from
    funext hcomm2]
  rw [MeasureTheory.integral_neg]
  -- Now goal: -∫_{cube} f · ∂_{s_i}(bumpKernelPer x) = ∫_{cube} g_i · bumpKernelPer x.
  -- Use `hibp` (essentially definitional).
  change -(∫ s in UnitCube d,
        f s * fderiv ℝ (bumpKernelPer d ε hε hε' x) s (Pi.basisFun ℝ (Fin d) i))
      = ∫ s in UnitCube d, g_i s * bumpKernelPer d ε hε hε' x s
  -- `hibp` reads:
  -- `∫_{cube} g_i s * (φ : ...) s = -∫_{cube} f s * (SmoothPeriodic.partialDeriv i φ : ...) s`.
  -- Coercions are definitional.
  have hibp_simp :
      ∫ s in UnitCube d, g_i s * bumpKernelPer d ε hε hε' x s =
        -∫ s in UnitCube d, f s *
          fderiv ℝ (bumpKernelPer d ε hε hε' x) s (Pi.basisFun ℝ (Fin d) i) := hibp
  linarith [hibp_simp]

end IBP

end Periodic
end StationaryMFG
