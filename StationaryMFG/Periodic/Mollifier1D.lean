module

public import StationaryMFG.Basic

@[expose] public section

/-!
# 1D periodic mollifier

This file constructs a 1-dimensional periodic mollifier
`periodicMollifier1D : ℝ → ℝ → ℝ`, parametrised by a "width" `ε > 0`.
For each `0 < ε < 1/2`, the function `periodicMollifier1D ε` is smooth
(in the `ℕ∞` sense), non-negative, and periodic of period `1`. It is the
1D ingredient used to build the multidimensional periodic mollifier on
`(Fin d → ℝ) → ℝ` in the sibling file `Mollifier.lean` (forthcoming,
task `infra:P1-mollifier-tensor`).

The construction is the periodisation of a smooth bump of width `ε` on
`ℝ`:

`periodicMollifier1D ε x := ∑' k : ℤ, palomar_Mollifier1D_B(x - k)`

where `palomar_Mollifier1D_B := bump.normed volume` for a `ContDiffBump (0 : ℝ)` with
`rIn = ε/2, rOut = ε`. For `ε < 1/2`, the support of `palomar_Mollifier1D_B` lies in
`(-ε, ε) ⊂ (-1/2, 1/2)`, so the integer translates of `palomar_Mollifier1D_B` have disjoint
supports and at most one term in the sum is nonzero at any given point.
This makes the `tsum` automatically well-defined and reducible to a
single bump value.

The integral identity `∫_{[0,1)} periodicMollifier1D ε = 1` is proved
in the dependent task `infra:P1-mollifier-1D-integral`.

-- Adapted from LpSpaces.Mollification (which uses a non-periodic
-- `ContDiffBump.normed` in its convolution argument; here we periodise
-- that same kernel).
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Set Filter Function
open scoped ContDiff Topology

/-! ### The base 1D bump -/

/-- A `ContDiffBump` centred at `0 : ℝ` with `rIn = ε/2` and `rOut = ε`. -/
noncomputable def palomar_Mollifier1D_baseBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The normalised base bump `B_ε : ℝ → ℝ`: smooth, non-negative,
supported in `(-ε, ε)`, with `∫ B_ε = 1`. -/
noncomputable def palomar_Mollifier1D_B (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ :=
  (palomar_Mollifier1D_baseBump ε hε).normed (volume : Measure ℝ)

private lemma B_nonneg (ε : ℝ) (hε : 0 < ε) (x : ℝ) : 0 ≤ palomar_Mollifier1D_B ε hε x :=
  (palomar_Mollifier1D_baseBump ε hε).nonneg_normed x

private lemma B_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞)) (palomar_Mollifier1D_B ε hε) :=
  (palomar_Mollifier1D_baseBump ε hε).contDiff_normed

/-- Support of the normalised base bump: the open ball of radius `ε`. -/
private lemma B_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (palomar_Mollifier1D_B ε hε) = Metric.ball (0 : ℝ) ε :=
  (palomar_Mollifier1D_baseBump ε hε).support_normed_eq

/-- The normalised base bump vanishes outside `(-ε, ε)`. -/
private lemma B_eq_zero_of_abs_ge (ε : ℝ) (hε : 0 < ε) {x : ℝ} (hx : ε ≤ |x|) :
    palomar_Mollifier1D_B ε hε x = 0 := by
  by_contra hne
  have hxsupp : x ∈ Function.support (palomar_Mollifier1D_B ε hε) := hne
  rw [B_support] at hxsupp
  have hxlt : |x| < ε := by
    have hd : dist x (0 : ℝ) < ε := hxsupp
    simpa [Real.dist_eq] using hd
  exact (not_lt.mpr hx) hxlt

/-! ### Different lattice points are far apart -/

/-- For `ε < 1/2`, every translate of `palomar_Mollifier1D_B` by a non-rounding integer is zero. -/
private lemma B_translate_eq_zero_of_ne_round (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < 1 / 2) {x : ℝ} {k : ℤ} (hk : k ≠ round x) :
    palomar_Mollifier1D_B ε hε (x - (k : ℝ)) = 0 := by
  apply B_eq_zero_of_abs_ge ε hε
  -- |x - k| ≥ |round x - k| - |x - round x| ≥ 1 - 1/2 = 1/2 > ε.
  have h1 : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
  have h2 : (round x - k : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  have h3 : (1 : ℤ) ≤ |round x - k| := Int.one_le_abs h2
  have h4 : (1 : ℝ) ≤ |((round x : ℝ) - (k : ℝ))| := by
    have hcast : ((round x - k : ℤ) : ℝ) = (round x : ℝ) - (k : ℝ) := by
      push_cast; ring
    have : (1 : ℝ) ≤ ((|round x - k| : ℤ) : ℝ) := by exact_mod_cast h3
    rwa [Int.cast_abs, hcast] at this
  -- Triangle: |round x - k| ≤ |x - k| + |x - round x|.
  have htri : |((round x : ℝ) - (k : ℝ))| ≤ |x - (k : ℝ)| + |x - (round x : ℝ)| := by
    calc |((round x : ℝ) - (k : ℝ))|
        = |((round x : ℝ) - x) + (x - (k : ℝ))| := by ring_nf
      _ ≤ |((round x : ℝ) - x)| + |x - (k : ℝ)| := abs_add_le _ _
      _ = |x - (round x : ℝ)| + |x - (k : ℝ)| := by rw [abs_sub_comm]
      _ = |x - (k : ℝ)| + |x - (round x : ℝ)| := by ring
  linarith

/-! ### Single-term collapse of the tsum -/

/-- For `ε < 1/2`, the `ℤ`-indexed family `k ↦ palomar_Mollifier1D_B(x - k)` has at most one
nonzero term and `tsum` collapses to it. -/
private lemma tsum_B_translates_eq (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (x : ℝ) :
    ∑' k : ℤ, palomar_Mollifier1D_B ε hε (x - (k : ℝ)) = palomar_Mollifier1D_B ε hε (x - (round x : ℝ)) := by
  refine tsum_eq_single (round x) ?_
  intro k hk
  exact B_translate_eq_zero_of_ne_round ε hε hε' hk

/-! ### The 1D periodic mollifier -/

/-- The 1D periodic mollifier of width `ε`: the periodisation of
`B_ε` along the integer lattice. We define it for all real `ε`, returning
`0` when `ε ≤ 0` so the function is total; the meaningful regime is
`0 < ε < 1/2`. -/
noncomputable def periodicMollifier1D (ε : ℝ) (x : ℝ) : ℝ :=
  if hε : 0 < ε then ∑' k : ℤ, palomar_Mollifier1D_B ε hε (x - (k : ℝ)) else 0

/-- Unfolding for the meaningful `ε > 0` case. -/
lemma periodicMollifier1D_eq_tsum (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    periodicMollifier1D ε x = ∑' k : ℤ, palomar_Mollifier1D_B ε hε (x - (k : ℝ)) := by
  unfold periodicMollifier1D; rw [dif_pos hε]

/-- For `0 < ε < 1/2`, the mollifier collapses to a single bump value. -/
lemma periodicMollifier1D_eq_single (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x : ℝ) : periodicMollifier1D ε x = palomar_Mollifier1D_B ε hε (x - (round x : ℝ)) := by
  rw [periodicMollifier1D_eq_tsum ε hε x, tsum_B_translates_eq ε hε hε']

/-! ### Non-negativity -/

/-- The 1D periodic mollifier is everywhere non-negative. -/
lemma periodicMollifier1D_nonneg (ε : ℝ) (x : ℝ) : 0 ≤ periodicMollifier1D ε x := by
  unfold periodicMollifier1D
  split_ifs with h
  · exact tsum_nonneg (fun _ => B_nonneg ε h _)
  · exact le_rfl

/-! ### Periodicity -/

/-- The 1D periodic mollifier is periodic with period `1`. -/
lemma periodicMollifier1D_periodic (ε : ℝ) :
    Function.Periodic (periodicMollifier1D ε) 1 := by
  intro x
  unfold periodicMollifier1D
  split_ifs with h
  · -- Reindex `k ↦ k + 1`: an additive equivalence on `ℤ`.
    have key : ∀ k : ℤ, palomar_Mollifier1D_B ε h ((x + 1) - (((Equiv.addRight (1 : ℤ)) k : ℤ) : ℝ)) =
        palomar_Mollifier1D_B ε h (x - (k : ℝ)) := by
      intro k
      congr 1
      change (x + 1) - ((k + 1 : ℤ) : ℝ) = x - (k : ℝ)
      push_cast; ring
    have heq := (Equiv.addRight (1 : ℤ)).tsum_eq
      (f := fun k : ℤ => palomar_Mollifier1D_B ε h ((x + 1) - (k : ℝ)))
    -- heq : ∑' k, palomar_Mollifier1D_B ε h ((x+1) - ↑((Equiv.addRight 1) k)) = ∑' k, palomar_Mollifier1D_B ε h ((x+1) - ↑k)
    rw [← heq]
    exact tsum_congr key
  · rfl

/-! ### Smoothness via local agreement with a single bump translate -/

/-- For `0 < ε < 1/2` and any `x₀ : ℝ`, there is a neighborhood of `x₀`
on which the mollifier equals the single bump translate
`palomar_Mollifier1D_B(· - round x₀)`. -/
private lemma periodicMollifier1D_eventuallyEq_single
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (x₀ : ℝ) :
    periodicMollifier1D ε =ᶠ[𝓝 x₀]
      (fun x => palomar_Mollifier1D_B ε hε (x - (round x₀ : ℝ))) := by
  -- Choose `δ := (1/2 - ε) / 2 > 0`.
  set δ : ℝ := (1 / 2 - ε) / 2 with hδdef
  have hδpos : 0 < δ := by
    have hpos : 0 < 1/2 - ε := by linarith
    change 0 < (1 / 2 - ε) / 2; linarith
  have hopen : IsOpen (Set.Ioo (x₀ - δ) (x₀ + δ)) := isOpen_Ioo
  have hmem : x₀ ∈ Set.Ioo (x₀ - δ) (x₀ + δ) := by
    refine ⟨?_, ?_⟩ <;> linarith
  refine eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
  intro x hx
  -- Goal: `periodicMollifier1D ε x = palomar_Mollifier1D_B ε hε (x - round x₀)`.
  change periodicMollifier1D ε x = palomar_Mollifier1D_B ε hε (x - (round x₀ : ℝ))
  rw [periodicMollifier1D_eq_tsum ε hε x]
  apply tsum_eq_single (round x₀)
  intro k hk
  -- Need: `palomar_Mollifier1D_B ε hε (x - k) = 0`. We show |x - k| ≥ ε.
  apply B_eq_zero_of_abs_ge ε hε
  have hkint : (round x₀ - k : ℤ) ≠ 0 := sub_ne_zero.mpr (by intro h; exact hk h.symm)
  have h_diff_one : (1 : ℝ) ≤ |((round x₀ : ℝ) - (k : ℝ))| := by
    have hint : ((round x₀ - k : ℤ) : ℝ) = (round x₀ : ℝ) - (k : ℝ) := by
      push_cast; ring
    have h3 : (1 : ℤ) ≤ |round x₀ - k| := Int.one_le_abs hkint
    have : (1 : ℝ) ≤ ((|round x₀ - k| : ℤ) : ℝ) := by exact_mod_cast h3
    rwa [Int.cast_abs, hint] at this
  have hxx0 : |x - x₀| < δ := by
    obtain ⟨h1, h2⟩ := hx
    rw [abs_sub_lt_iff]
    refine ⟨by linarith, by linarith⟩
  have hround : |x₀ - (round x₀ : ℝ)| ≤ 1 / 2 := abs_sub_round x₀
  -- Triangle: |round x₀ - k| ≤ |x - k| + |x - x₀| + |x₀ - round x₀|.
  have htri :
      |((round x₀ : ℝ) - (k : ℝ))| ≤ |x - (k : ℝ)| + |x - x₀| + |x₀ - (round x₀ : ℝ)| := by
    have step1 :
        ((round x₀ : ℝ) - (k : ℝ)) =
          ((round x₀ : ℝ) - x₀) + (x₀ - x) + (x - (k : ℝ)) := by ring
    have step2 :
        |((round x₀ : ℝ) - x₀) + (x₀ - x) + (x - (k : ℝ))| ≤
          |((round x₀ : ℝ) - x₀)| + |x₀ - x| + |x - (k : ℝ)| := by
      have a1 := abs_add_le (((round x₀ : ℝ) - x₀) + (x₀ - x)) (x - (k : ℝ))
      have a2 := abs_add_le ((round x₀ : ℝ) - x₀) (x₀ - x)
      linarith
    calc |((round x₀ : ℝ) - (k : ℝ))|
        = |((round x₀ : ℝ) - x₀) + (x₀ - x) + (x - (k : ℝ))| := by rw [step1]
      _ ≤ |((round x₀ : ℝ) - x₀)| + |x₀ - x| + |x - (k : ℝ)| := step2
      _ = |x₀ - (round x₀ : ℝ)| + |x - x₀| + |x - (k : ℝ)| := by
          rw [abs_sub_comm ((round x₀ : ℝ)) x₀, abs_sub_comm x₀ x]
      _ = |x - (k : ℝ)| + |x - x₀| + |x₀ - (round x₀ : ℝ)| := by ring
  -- |x - k| ≥ 1 - δ - 1/2 = 1/2 - δ; need ≥ ε.
  have hbig : |x - (k : ℝ)| ≥ 1 - δ - 1 / 2 := by linarith
  have heq : 1 - δ - 1 / 2 = 1/2 - δ := by ring
  have hgoal : ε ≤ 1 / 2 - δ := by
    -- ε ≤ 1/2 - δ
    have : δ = (1 / 2 - ε) / 2 := rfl
    linarith
  linarith [hbig, heq.le, heq.symm.le]

/-- The 1D periodic mollifier is `C^∞` (in the `ℕ∞` sense) for `0 < ε < 1/2`. -/
lemma periodicMollifier1D_contDiff_of_lt_half (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ContDiff ℝ ((⊤ : ℕ∞)) (periodicMollifier1D ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  -- The function `palomar_Mollifier1D_B(· - round x₀)` is smooth (translation of a smooth function).
  have hshift_diff : ContDiff ℝ ((⊤ : ℕ∞))
      (fun x : ℝ => x - (round x₀ : ℝ)) :=
    contDiff_id.sub contDiff_const
  have hshift : ContDiff ℝ ((⊤ : ℕ∞))
      (fun x : ℝ => palomar_Mollifier1D_B ε hε (x - (round x₀ : ℝ))) :=
    (B_contDiff ε hε).comp hshift_diff
  -- Locally, the mollifier equals this shift.
  exact (hshift.contDiffAt).congr_of_eventuallyEq
    (periodicMollifier1D_eventuallyEq_single ε hε hε' x₀)

/-! ### Integral of the mollifier over the unit interval -/

/-- The base bump `B_ε` is continuous. -/
private lemma B_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (palomar_Mollifier1D_B ε hε) :=
  (palomar_Mollifier1D_baseBump ε hε).continuous_normed

/-- The base bump `B_ε` is integrable on `ℝ` (volume measure). -/
private lemma B_integrable (ε : ℝ) (hε : 0 < ε) :
    MeasureTheory.Integrable (palomar_Mollifier1D_B ε hε) (MeasureTheory.volume) :=
  (palomar_Mollifier1D_baseBump ε hε).integrable_normed

/-- The base bump `B_ε` integrates to `1` on `ℝ`. -/
private lemma B_integral (ε : ℝ) (hε : 0 < ε) :
    ∫ x, palomar_Mollifier1D_B ε hε x = 1 :=
  (palomar_Mollifier1D_baseBump ε hε).integral_normed

/-- For `0 < ε < 1/2`, the support of `B_ε` is contained in `Ioc (-1/2) (1/2)`. -/
private lemma B_support_subset (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    Function.support (palomar_Mollifier1D_B ε hε) ⊆ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
  intro x hx
  rw [B_support] at hx
  have habs : |x| < ε := by
    have : dist x (0 : ℝ) < ε := hx
    simpa [Real.dist_eq] using this
  have hbnd : |x| < 1 / 2 := lt_trans habs hε'
  have h1 : -(1 / 2 : ℝ) < x := by
    have := (abs_lt.mp hbnd).1; linarith
  have h2 : x < (1 / 2 : ℝ) := (abs_lt.mp hbnd).2
  exact ⟨h1, h2.le⟩

/-- On `Ico 0 (1/2)`, the periodic mollifier equals `B_ε` itself
(because `round x = 0` there). -/
private lemma periodicMollifier1D_eqOn_Ico_zero_half
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    Set.EqOn (periodicMollifier1D ε) (palomar_Mollifier1D_B ε hε) (Set.Ico (0 : ℝ) (1 / 2)) := by
  intro x hx
  have hround : round x = 0 := by
    rw [round_eq_zero_iff]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [periodicMollifier1D_eq_single ε hε hε' x, hround]
  simp

/-- On `Ico (1/2) 1`, the periodic mollifier equals `B_ε(· - 1)`
(because `round x = 1` there). -/
private lemma periodicMollifier1D_eqOn_Ico_half_one
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    Set.EqOn (periodicMollifier1D ε) (fun x => palomar_Mollifier1D_B ε hε (x - 1))
      (Set.Ico ((1 / 2 : ℝ)) 1) := by
  intro x hx
  have hround : round x = 1 := by
    rw [round_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; linarith [hx.1]
    · push_cast; linarith [hx.2]
  rw [periodicMollifier1D_eq_single ε hε hε' x, hround]
  push_cast; rfl

/-- The 1D periodic mollifier integrates to `1` over the unit interval `[0,1)`. -/
theorem integral_periodicMollifier1D (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∫ x in Set.Ico (0:ℝ) 1, periodicMollifier1D ε x = 1 := by
  -- Step 1: convert to interval integral on `(0, 1]`.
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have h0half : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- Convert the LHS to `∫ x in (0:ℝ)..1, periodicMollifier1D ε x`.
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le h01]
  -- Continuity / integrability of the mollifier on intervals.
  have hcont : Continuous (periodicMollifier1D ε) :=
    (periodicMollifier1D_contDiff_of_lt_half ε hε hε').continuous
  -- Step 2: split at `1/2`.
  have hII1 : IntervalIntegrable (periodicMollifier1D ε) MeasureTheory.volume 0 (1/2) :=
    hcont.intervalIntegrable _ _
  have hII2 : IntervalIntegrable (periodicMollifier1D ε) MeasureTheory.volume (1/2) 1 :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hII1 hII2]
  -- Step 3: substitute on each piece.
  -- First piece: `∫ x in 0..1/2, periodicMollifier1D ε x = ∫ x in 0..1/2, palomar_Mollifier1D_B ε hε x`.
  have hpiece1 :
      ∫ x in (0:ℝ)..(1/2), periodicMollifier1D ε x =
      ∫ x in (0:ℝ)..(1/2), palomar_Mollifier1D_B ε hε x := by
    rw [intervalIntegral.integral_of_le h0half, intervalIntegral.integral_of_le h0half,
        ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ico
      (periodicMollifier1D_eqOn_Ico_zero_half ε hε hε')
  -- Second piece: `∫ x in 1/2..1, periodicMollifier1D ε x = ∫ x in 1/2..1, palomar_Mollifier1D_B ε hε (x - 1)`.
  have hpiece2 :
      ∫ x in (1/2:ℝ)..1, periodicMollifier1D ε x =
      ∫ x in (1/2:ℝ)..1, palomar_Mollifier1D_B ε hε (x - 1) := by
    rw [intervalIntegral.integral_of_le hhalf1, intervalIntegral.integral_of_le hhalf1,
        ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ico
      (periodicMollifier1D_eqOn_Ico_half_one ε hε hε')
  rw [hpiece1, hpiece2]
  -- Step 4: translate the second integral.
  have htrans :
      ∫ x in (1/2:ℝ)..1, palomar_Mollifier1D_B ε hε (x - 1) =
      ∫ x in (-(1/2):ℝ)..0, palomar_Mollifier1D_B ε hε x := by
    have := intervalIntegral.integral_comp_sub_right (a := (1/2:ℝ)) (b := 1)
      (f := palomar_Mollifier1D_B ε hε) (d := 1)
    -- `∫ x in 1/2..1, palomar_Mollifier1D_B (x - 1) = ∫ x in 1/2 - 1..1 - 1, palomar_Mollifier1D_B x`.
    convert this using 2 <;> norm_num
  rw [htrans]
  -- Step 5: combine to `∫ x in -1/2..1/2, palomar_Mollifier1D_B`.
  have hI3 : IntervalIntegrable (palomar_Mollifier1D_B ε hε) MeasureTheory.volume 0 (1/2) :=
    (B_continuous ε hε).intervalIntegrable _ _
  have hI4 : IntervalIntegrable (palomar_Mollifier1D_B ε hε) MeasureTheory.volume (-(1/2)) 0 :=
    (B_continuous ε hε).intervalIntegrable _ _
  rw [add_comm,
      intervalIntegral.integral_add_adjacent_intervals hI4 hI3]
  -- Step 6: extend to full integral using support of palomar_Mollifier1D_B.
  have hsupp : Function.support (palomar_Mollifier1D_B ε hε) ⊆ Set.Ioc (-(1/2 : ℝ)) (1/2) :=
    B_support_subset ε hε hε'
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  -- Step 7: conclude.
  exact B_integral ε hε

/-! ### Sample example -/

example (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ContDiff ℝ ((⊤ : ℕ∞)) (periodicMollifier1D ε) ∧
    Function.Periodic (periodicMollifier1D ε) 1 ∧
    (∀ x, 0 ≤ periodicMollifier1D ε x) :=
  ⟨periodicMollifier1D_contDiff_of_lt_half ε hε hε',
   periodicMollifier1D_periodic ε,
   periodicMollifier1D_nonneg ε⟩

end Periodic
end StationaryMFG
