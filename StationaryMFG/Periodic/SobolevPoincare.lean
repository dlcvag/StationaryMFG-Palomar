module

public import StationaryMFG.Periodic.Poincare
public import StationaryMFG.Periodic.LpInclusion

@[expose] public section

/-!
# Periodic Sobolev–Poincaré inequality on the unit cube

This module is the splice point for the W^{1,p} extension of the periodic
Poincaré–Wirtinger inequality. The headline target is the bound

```
lpNormPer p (f − periodicMean f) ≤ C(d) · Σ_i lpNormPer p (g i)
```

for `f : (Fin d → ℝ) → ℝ` with `MemSobolevPer p f` and weak-derivative
family `g`, paraphrased from `Source/FGU-monotone_revised.tex`
(eq. `eq:poincare-torus`, line 1245).

The argument decomposes into:

1. *Smooth case with `L^p` RHS*
   (`infra:P1-poincare-smooth-LpRHS-direct`, target of a sibling task)
   — a `path-telescope + weighted-power-mean` argument.
2. *Density extension* (`infra:P1-poincare-port-DeGiorgi-W1p-density`,
   target of a sibling task) — uses `SmoothPeriodic.denseInSobolevPer`
   from `Periodic/Sobolev.lean` and the Jensen-for-averages lemma
   `eLpNorm_const_average_le` provided here.

This module ships the *domain-agnostic* Jensen lemma adapted from
DeGiorgi's `SobolevPoincare.lean`, plus its specialisation to the
cube-restricted Lebesgue measure that the periodic toolkit uses.

Adapted from `DeGiorgi.SobolevPoincare` (whole-space version);
the Jensen lemma is genuinely domain-agnostic so we keep its statement
as is.
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ### Jensen's inequality for `eLpNorm` of averages

For `1 ≤ p < ∞`, an integrable `f`, and a finite measure `μ`, the
constant function equal to the `μ`-average of `f` has `Lᵖ(μ)` norm at
most that of `f` itself. This is the standard "average is `Lᵖ`-bounded
by the function" Jensen inequality, expressed at the `eLpNorm`/`ℝ≥0∞`
level so that it integrates cleanly with the rest of the Mathlib
measure-theory API.

Adapted from `DeGiorgi.SobolevPoincare.eLpNorm_const_average_le`
(whole-space version); the proof is genuinely domain-agnostic so we keep
it on a generic `IsFiniteMeasure`.
-/

/-- **Jensen's inequality for `eLpNorm` of averages.** For `1 ≤ p < ∞`,
an integrable function `f`, and a finite measure `μ`, the `Lᵖ(μ)` norm
of the constant function equal to the `μ`-average of `f` is at most
the `Lᵖ(μ)` norm of `f`:

```
eLpNorm (fun _ => ⨍ x, f x ∂μ) p μ ≤ eLpNorm f p μ.
```

Adapted from `DeGiorgi.SobolevPoincare` (whole-space version). -/
theorem eLpNorm_const_average_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : α → ℝ} (hf : Integrable f μ) :
    eLpNorm (fun _ => ⨍ x, f x ∂μ) p μ ≤ eLpNorm f p μ := by
  let _ := hp_top
  -- Trivial case: μ = 0
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp [eLpNorm_measure_zero]
  have hμ_ne : μ Set.univ ≠ 0 := by rwa [ne_eq, Measure.measure_univ_eq_zero]
  have hμ_top : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  have hp_ne : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  -- Key step: bound the enorm of the average by `(μ univ)⁻¹ * eLpNorm f 1`.
  have h_avg_enorm_le :
      ‖⨍ x, f x ∂μ‖ₑ ≤ (μ Set.univ)⁻¹ * eLpNorm f 1 μ := by
    have h_avg_bound : ‖⨍ x, f x ∂μ‖ ≤
        (μ.real Set.univ)⁻¹ * (eLpNorm f 1 μ).toReal := by
      simp only [average_eq]
      calc ‖(μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ‖
          ≤ ‖(μ.real Set.univ)⁻¹‖ * ‖∫ x, f x ∂μ‖ := norm_smul_le _ _
        _ = (μ.real Set.univ)⁻¹ * ‖∫ x, f x ∂μ‖ := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
        _ ≤ (μ.real Set.univ)⁻¹ * (eLpNorm f 1 μ).toReal := by
            gcongr
            calc ‖∫ x, f x ∂μ‖
                ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
              _ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal :=
                  integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable
              _ = (eLpNorm f 1 μ).toReal := by rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    -- Convert ℝ bound to ENNReal.
    have h_inv_eq : ENNReal.ofReal (μ.real Set.univ)⁻¹ = (μ Set.univ)⁻¹ := by
      rw [measureReal_def, ENNReal.ofReal_inv_of_pos
            (ENNReal.toReal_pos hμ_ne hμ_top),
        ENNReal.ofReal_toReal hμ_top]
    calc ‖⨍ x, f x ∂μ‖ₑ
        ≤ ENNReal.ofReal ((μ.real Set.univ)⁻¹ * (eLpNorm f 1 μ).toReal) := by
          simp only [Real.enorm_eq_ofReal_abs, ← Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal h_avg_bound
      _ = ENNReal.ofReal (μ.real Set.univ)⁻¹ *
            ENNReal.ofReal (eLpNorm f 1 μ).toReal :=
          ENNReal.ofReal_mul (inv_nonneg.mpr measureReal_nonneg)
      _ ≤ (μ Set.univ)⁻¹ * eLpNorm f 1 μ := by
          rw [h_inv_eq]; gcongr; exact ENNReal.ofReal_toReal_le
  set exp := 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal with hexp_def
  have h_holder : eLpNorm f 1 μ ≤
      eLpNorm f p μ * μ Set.univ ^ exp :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  have hexp_simp : exp + 1 / p.toReal = 1 := by
    simp [hexp_def, show (1 : ℝ≥0∞).toReal = 1 from ENNReal.toReal_one]
  calc eLpNorm (fun _ => ⨍ x, f x ∂μ) p μ
      = ‖⨍ x, f x ∂μ‖ₑ * μ Set.univ ^ (1 / p.toReal) := eLpNorm_const _ hp_ne hμ
    _ ≤ ((μ Set.univ)⁻¹ * eLpNorm f 1 μ) * μ Set.univ ^ (1 / p.toReal) := by
        gcongr
    _ ≤ ((μ Set.univ)⁻¹ * (eLpNorm f p μ * μ Set.univ ^ exp)) *
          μ Set.univ ^ (1 / p.toReal) := by gcongr
    _ = eLpNorm f p μ * ((μ Set.univ)⁻¹ * (μ Set.univ ^ exp *
          μ Set.univ ^ (1 / p.toReal))) := by ring
    _ = eLpNorm f p μ * ((μ Set.univ)⁻¹ * μ Set.univ ^ (exp + 1 / p.toReal)) := by
        congr 2; exact (ENNReal.rpow_add exp (1 / p.toReal) hμ_ne hμ_top).symm
    _ = eLpNorm f p μ * ((μ Set.univ)⁻¹ * μ Set.univ ^ (1 : ℝ)) := by
        rw [hexp_simp]
    _ = eLpNorm f p μ * ((μ Set.univ)⁻¹ * μ Set.univ) := by
        rw [ENNReal.rpow_one]
    _ = eLpNorm f p μ := by rw [ENNReal.inv_mul_cancel hμ_ne hμ_top, mul_one]

/-! ### Periodic specialisation: average over the unit cube -/

/-- **Cube-restricted Jensen.** For `1 ≤ p < ∞` and `f : (Fin d → ℝ) → ℝ`
integrable on the unit cube, the constant function equal to
`periodicMean f` has `eLpNormPer p`-norm at most `eLpNormPer p f`. This
is the periodic specialisation of `eLpNorm_const_average_le`: with
`μ = volume.restrict (UnitCube d)`, `μ univ = 1`, so the average
coincides with the integral. -/
theorem eLpNormPer_const_periodicMean_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f (UnitCube d)) :
    eLpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean f) ≤
      eLpNormPer (d := d) p f := by
  -- Set up the cube-restricted measure as a finite measure.
  haveI hμ_fin :
      IsFiniteMeasure (Measure.restrict
        (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  -- The cube-restricted measure has `univ`-measure equal to `1`.
  have hμuniv :
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact volume_unitCube
  -- Identify `periodicMean f` with the average over the cube. Because
  -- the cube has volume `1`, the average equals the integral.
  have hpm_eq :
      periodicMean f =
        ⨍ x, f x ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
    unfold periodicMean periodicIntegral
    rw [average_eq]
    have hreal : (Measure.restrict (volume : Measure (Fin d → ℝ))
          (UnitCube d)).real Set.univ = 1 := by
      rw [Measure.real, hμuniv]
      simp
    rw [hreal]
    simp
  -- Apply the generic Jensen lemma at `μ = volume.restrict (UnitCube d)`.
  have hkey :=
    eLpNorm_const_average_le
      (μ := Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
      (p := p) hp hp_top (f := f) hf
  -- Rewrite the LHS via `hpm_eq`.
  unfold eLpNormPer
  rw [hpm_eq]
  exact hkey

/-! ### Sample examples -/

/-- Sanity check: with `f = const c` on the cube, `periodicMean f = c`,
both `eLpNormPer p (const (periodicMean f))` and `eLpNormPer p f` reduce
to the `eLpNormPer` of `const c`, and the inequality is `≤` by `le_refl`. -/
example {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) (c : ℝ) :
    eLpNormPer (d := d) p
      (fun _ : Fin d → ℝ =>
        periodicMean (fun _ : Fin d → ℝ => c)) ≤
      eLpNormPer (d := d) p (fun _ : Fin d → ℝ => c) := by
  -- `IntegrableOn (const c) (UnitCube d)` since the cube has finite measure.
  have hvol : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  exact eLpNormPer_const_periodicMean_le (d := d) (p := p) hp hp_top
    (f := fun _ : Fin d → ℝ => c) (integrableOn_const hvol)

/-! ### `L^p`-RHS smooth-case Poincaré–Wirtinger on the unit cube

This section delivers the smooth-case Poincaré–Wirtinger inequality with
the gradient appearing under an `L^p` norm rather than a uniform `L^∞`
bound:

```
lpNormPer p (φ - periodicMean φ)
    ≤ poincareWirtingerConstant d · ∑ i, lpNormPer p (∂_i φ).
```

It mirrors `DeGiorgi.Poincare.poincare_smooth_unitBall` (whole-space +
restrict argument), simplified for the torus: the cube has volume `1`,
so the prefactors collapse, and we do not need a Riesz-potential
representation — the existing path-telescope of
`Periodic/Poincare.lean` suffices.

The strategy is:

1. *Pointwise integrand bound.* Use the slice Wirtinger
   inequality `wirtinger1D_axis_smoothPeriodic` to bound each step of
   the telescoping path by an integral of the relevant partial
   derivative; sum to get
   `|φ(x) - φ(y)| ≤ ∑_k ∫₀¹ |∂_⟨k,_⟩φ (...)| dτ`.

2. *Take the `L^p` norm.* Combine with `cube has volume 1` to express
   `φ(x) - periodicMean φ = ∫_y (φ(x) - φ(y)) dy`; the pointwise
   integrand bound therefore yields a Minkowski-type bound in `x`.

The pointwise bounds in step 1 are domain-agnostic and are recorded
here as `pointwise_step_integral_bound` and
`pointwise_diff_integral_bound`.
-/

open Function in
/-- **Pointwise step bound (integral form).** Each step of the
telescoping path between two points contributes a slice integral of the
relevant partial derivative. For `φ : SmoothPeriodic d`, base points
`x, y ∈ UnitCube d`, and `k < d`,

```
|φ(pathPoint x y (k+1)) − φ(pathPoint x y k)|
    ≤ ∫₀¹ |(∂_⟨k,_⟩ φ) (update (pathPoint x y k) ⟨k, hk⟩ τ)| dτ.
```

This is `wirtinger1D_axis_smoothPeriodic` applied to the slice base
point `pathPoint x y k`, where the two endpoints differ exactly in
coordinate `⟨k, hk⟩`. -/
lemma pointwise_step_integral_bound (φ : SmoothPeriodic d)
    {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d)
    {k : ℕ} (hk : k < d) :
    |(φ : (Fin d → ℝ) → ℝ) (pathPoint x y (k + 1))
        - (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k)|
      ≤ ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv ⟨k, hk⟩ φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (Function.update (pathPoint x y k) ⟨k, hk⟩ τ)| := by
  -- Identify both endpoints with `update`s of `pathPoint x y k`.
  set i : Fin d := ⟨k, hk⟩ with hidef
  set z : Fin d → ℝ := pathPoint x y k with hzdef
  have hsucc : pathPoint x y (k + 1) = Function.update z i (y i) :=
    pathPoint_succ hk
  have hzi : z i = x i := by
    change pathPoint x y k i = x i
    have hcoord : (i : ℕ) = k := rfl
    unfold pathPoint
    simp [hcoord]
  have hzeq : z = Function.update z i (x i) := by
    funext j
    by_cases hji : j = i
    · subst hji; simp [hzi]
    · simp [Function.update_of_ne hji]
  -- Membership of `x i, y i` in `[0,1]`.
  have hxmem : x i ∈ Set.Icc (0 : ℝ) 1 := by
    have := (mem_unitCube_iff.mp hx) i
    exact ⟨this.1, le_of_lt this.2⟩
  have hymem : y i ∈ Set.Icc (0 : ℝ) 1 := by
    have := (mem_unitCube_iff.mp hy) i
    exact ⟨this.1, le_of_lt this.2⟩
  -- Apply the slice Wirtinger inequality.
  have hslice :
      |(φ : (Fin d → ℝ) → ℝ) (Function.update z i (y i))
          - (φ : (Fin d → ℝ) → ℝ) (Function.update z i (x i))|
        ≤ ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) (Function.update z i τ)| :=
    wirtinger1D_axis_smoothPeriodic φ z i hxmem hymem
  -- Rewrite both endpoints using `hsucc` and `hzeq`.
  have hkrew : (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k)
      = (φ : (Fin d → ℝ) → ℝ) (Function.update z i (x i)) := by
    rw [show pathPoint x y k = Function.update z i (x i) from hzeq]
  have hk1rew : (φ : (Fin d → ℝ) → ℝ) (pathPoint x y (k + 1))
      = (φ : (Fin d → ℝ) → ℝ) (Function.update z i (y i)) := by
    rw [hsucc]
  rw [hkrew, hk1rew]
  exact hslice

/-- **Pointwise telescoping bound (integral form, `Fin d` indexing).**
The full coordinate-by-coordinate telescope, summing the per-axis slice
integrals of `pointwise_step_integral_bound` over `i : Fin d`. For
`φ : SmoothPeriodic d` and `x, y ∈ UnitCube d`,

```
|φ(x) − φ(y)|
    ≤ ∑ i, ∫₀¹ |(∂_i φ) (update (pathPoint x y (i : ℕ)) i τ)| dτ.
```

This bound — pointwise in `(x, y)`, with the gradient appearing under
an integral on the right — is the starting point of the `L^p`-RHS
Poincaré–Wirtinger argument. -/
lemma pointwise_diff_integral_bound_fin (φ : SmoothPeriodic d)
    {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d) :
    |(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y|
      ≤ ∑ i : Fin d,
          ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)
              (Function.update (pathPoint x y (i : ℕ)) i τ)| := by
  -- Telescope `φ(y) − φ(x) = ∑_{k<d} (φ(P_{k+1}) − φ(P_k))`
  -- where `P_k = pathPoint x y k`, then triangle + per-step bound + re-index.
  set f : ℕ → ℝ := fun k => (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k) with hf_def
  -- Auxiliary ℕ-indexed function `gℕ k := if k < d then g_⟨k,_⟩ else 0`,
  -- defined for all `k : ℕ` so we don't need to thread `k < d` through
  -- the sum. Inside `Finset.range d`, the `else` branch is never taken.
  classical
  set gℕ : ℕ → ℝ :=
    fun k =>
      if hk : k < d then
        ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv ⟨k, hk⟩ φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
            (Function.update (pathPoint x y k) ⟨k, hk⟩ τ)|
      else 0
    with hgℕ_def
  have htel : ∀ m : ℕ, f m - f 0 =
      ∑ k ∈ Finset.range m, (f (k + 1) - f k) := by
    intro m
    induction m with
    | zero => simp
    | succ p ihp =>
      rw [Finset.sum_range_succ, ← ihp]; ring
  have hsum : f d - f 0 = ∑ k ∈ Finset.range d, (f (k + 1) - f k) := htel d
  have hfd : f d = (φ : (Fin d → ℝ) → ℝ) y := by
    change (φ : (Fin d → ℝ) → ℝ) (pathPoint x y d) = _
    rw [pathPoint_card]
  have hf0 : f 0 = (φ : (Fin d → ℝ) → ℝ) x := by
    change (φ : (Fin d → ℝ) → ℝ) (pathPoint x y 0) = _
    rw [pathPoint_zero]
  have htele :
      (φ : (Fin d → ℝ) → ℝ) y - (φ : (Fin d → ℝ) → ℝ) x =
        ∑ k ∈ Finset.range d, (f (k + 1) - f k) := by
    rw [← hfd, ← hf0]; exact hsum
  -- Per-step integral bound, expressed via `gℕ`.
  have hkbnd : ∀ k ∈ Finset.range d, |f (k + 1) - f k| ≤ gℕ k := by
    intro k hk
    have hkd : k < d := Finset.mem_range.mp hk
    have hstep := pointwise_step_integral_bound φ hx hy hkd
    -- Unfold `gℕ k = ...` (positive branch).
    have hgℕ_pos : gℕ k =
        ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv ⟨k, hkd⟩ φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
            (Function.update (pathPoint x y k) ⟨k, hkd⟩ τ)| := by
      simp [gℕ, hkd]
    rw [hgℕ_pos]
    exact hstep
  -- Triangle inequality, then sum bound.
  have habs : |(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y|
        = |(φ : (Fin d → ℝ) → ℝ) y - (φ : (Fin d → ℝ) → ℝ) x| := by
    rw [abs_sub_comm]
  rw [habs, htele]
  -- The sum `∑_{k ∈ range d} gℕ k` is exactly `∑_{i : Fin d} g i` after
  -- re-indexing via `Fin.sum_univ_eq_sum_range`. We first equate
  -- `gℕ ↑i` with the slice integral at `i`, then apply the re-indexing.
  have hgℕ_eq : ∀ i : Fin d,
      gℕ (i : ℕ) =
        ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
            (Function.update (pathPoint x y (i : ℕ)) i τ)| := by
    intro i
    have hi : (i : ℕ) < d := i.isLt
    -- `⟨(i : ℕ), hi⟩ = i` (definitionally, but record explicitly).
    have hi_eq : (⟨(i : ℕ), hi⟩ : Fin d) = i := Fin.ext rfl
    simp [gℕ, hi, hi_eq]
  have hreindex :
      (∑ i : Fin d,
          ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)
              (Function.update (pathPoint x y (i : ℕ)) i τ)|)
        = ∑ k ∈ Finset.range d, gℕ k := by
    rw [show (∑ i : Fin d,
            ∫ τ in (0 : ℝ)..1,
              |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ)
                (Function.update (pathPoint x y (i : ℕ)) i τ)|)
          = ∑ i : Fin d, gℕ (i : ℕ) from
        Finset.sum_congr rfl (fun i _ => (hgℕ_eq i).symm)]
    exact Fin.sum_univ_eq_sum_range gℕ d
  calc |∑ k ∈ Finset.range d, (f (k + 1) - f k)|
      ≤ ∑ k ∈ Finset.range d, |f (k + 1) - f k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range d, gℕ k := Finset.sum_le_sum hkbnd
    _ = ∑ i : Fin d,
          ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)
              (Function.update (pathPoint x y (i : ℕ)) i τ)| := hreindex.symm

/-- Sanity-check `example`: for the constant smooth-periodic function
`φ = const c`, the partial derivatives vanish, so each axis slice
integral is `0`, and the pointwise telescoping integral bound reduces
to `0 ≤ 0`. -/
example (c : ℝ) {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d) :
    |((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
        - ((SmoothPeriodic.const c : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) y|
      ≤ ∑ i : Fin d,
          ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
                SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
              (Function.update (pathPoint x y (i : ℕ)) i τ)| :=
  pointwise_diff_integral_bound_fin (SmoothPeriodic.const c) hx hy

/-! ### Geometry-normalised axis-mix map and pushforward bridge

The pointwise telescope above leaves us with integrands of the form
`g (Function.update (pathPoint x y k) k τ)`. This is awkward for
Fubini-type reductions because it nests `update` on top of `pathPoint`.
The combinator `axisMix` below packages exactly the same point with a
Lean-friendly definition: coordinates strictly below `k` come from `y`,
the coordinate at `k` is `τ`, and coordinates strictly above `k` come
from `x`. A bridge lemma equates the two forms so existing pointwise
helpers transfer without re-proof.

The `axisMix_map_cubeMeasure` identity (the measure of the cube is the
pushforward of `(cube × cube) × [0,1]` along `axisMix`) reduces the
two-step (path + slice) Fubini argument needed by the `L^p`-RHS smooth
Poincaré–Wirtinger inequality to a one-line `lintegral_map`. We deliver
the identity here as a class hypothesis (`AxisMixMeasureHypothesis`)
together with the `lintegral_map`-based corollary; the discharge of the
hypothesis is left to the follow-up task
`infra:P1-axisMix-pushforward-prove`.
-/

/-- Geometry-normalised axis-mix map: combine `y` (axes below `k`),
`τ` (axis `k`), and `x` (axes above `k`) into a single point in
`Fin d → ℝ`. Definitionally simpler than
`Function.update (pathPoint x y k) k τ`. -/
def axisMix (k : Fin d) (x y : Fin d → ℝ) (τ : ℝ) : Fin d → ℝ :=
  fun j => if j < k then y j else if j = k then τ else x j

@[simp] lemma axisMix_lt (k j : Fin d) (h : j < k)
    (x y : Fin d → ℝ) (τ : ℝ) : axisMix k x y τ j = y j := by
  simp [axisMix, h]

@[simp] lemma axisMix_eq (k : Fin d) (x y : Fin d → ℝ) (τ : ℝ) :
    axisMix k x y τ k = τ := by
  simp [axisMix]

@[simp] lemma axisMix_gt (k j : Fin d) (h : k < j)
    (x y : Fin d → ℝ) (τ : ℝ) : axisMix k x y τ j = x j := by
  have hnot : ¬ j < k := not_lt.mpr h.le
  have hneq : j ≠ k := (ne_of_gt h)
  simp [axisMix, hnot, hneq]

/-- Bridge: `axisMix k x y τ` agrees with the older
`Function.update (pathPoint x y k) k τ`. The two forms differ only in
how the coordinate at `k` is overwritten — `pathPoint x y k` puts
`x k` there, then `update` replaces it with `τ`; `axisMix` writes `τ`
directly. Coordinates `j ≠ k` are determined by the same `j < k`
test in both. -/
lemma axisMix_eq_update_pathPoint (k : Fin d) (x y : Fin d → ℝ) (τ : ℝ) :
    axisMix k x y τ = Function.update (pathPoint x y (k : ℕ)) k τ := by
  funext j
  classical
  by_cases hjk : j = k
  · subst hjk
    simp [axisMix]
  · -- Off-diagonal: split on `j < k` vs `k < j`.
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · have hjk_nat : (j : ℕ) < (k : ℕ) := hlt
      simp [axisMix, hlt, hjk, pathPoint, hjk_nat]
    · have hjk_nat : ¬ (j : ℕ) < (k : ℕ) := not_lt.mpr (le_of_lt hgt)
      have hnot : ¬ j < k := not_lt.mpr (le_of_lt hgt)
      simp [axisMix, hnot, hjk, pathPoint, hjk_nat]

/-- Measurability of the axis-mix map as a function of `((x, y), τ)`.
We check measurability coordinate-by-coordinate: each output coordinate
is one of `y j`, `τ`, or `x j`, which are coordinate projections from
the input triple. -/
lemma measurable_axisMix (k : Fin d) :
    Measurable
      (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
        axisMix k q.1.1 q.1.2 q.2) := by
  classical
  apply Measurable.of_eval
  intro j
  unfold axisMix
  by_cases hlt : j < k
  · simp only [hlt, if_true]
    -- The coordinate-`j` output is `y j`, projection of `q.1.2`.
    have hy : Measurable
        (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ => q.1.2 j) :=
      ((measurable_pi_apply j).comp measurable_snd).comp measurable_fst
    exact hy
  · by_cases heq : j = k
    · subst heq
      simp only [hlt, if_false, if_true]
      exact measurable_snd
    · simp only [hlt, heq, if_false]
      have hx : Measurable
          (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ => q.1.1 j) :=
        ((measurable_pi_apply j).comp measurable_fst).comp measurable_fst
      exact hx

/-! ### Measure abbreviations -/

/-- The "torus measure" — Lebesgue measure on `Fin d → ℝ` restricted to
the (half-open) unit cube. Total mass `1`. -/
noncomputable def cubeMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  (volume : Measure (Fin d → ℝ)).restrict (UnitCube d)

/-- Lebesgue measure on `ℝ` restricted to the unit interval `[0,1]`.
Used as the `τ`-factor of the axis-triple measure. -/
noncomputable def unitIntervalMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)

/-- The product measure on `((Fin d → ℝ) × (Fin d → ℝ)) × ℝ` used as the
domain of the axis-mix Fubini reduction: two cube factors and one unit
interval factor. -/
noncomputable def axisTripleMeasure (d : ℕ) :
    Measure (((Fin d → ℝ) × (Fin d → ℝ)) × ℝ) :=
  ((cubeMeasure d).prod (cubeMeasure d)).prod unitIntervalMeasure

instance : IsFiniteMeasure (cubeMeasure d) := by
  unfold cubeMeasure
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    volume_unitCube]
  exact ENNReal.one_lt_top

instance : SigmaFinite (cubeMeasure d) := by infer_instance

instance : IsFiniteMeasure (unitIntervalMeasure) := by
  unfold unitIntervalMeasure
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]
  simp

instance : SigmaFinite unitIntervalMeasure := by infer_instance

/-! ### Pushforward identity (hypothesis class) and Fubini consequence

Per the expert plan, the *only* hard step in the axis-mix toolkit is the
identity that pushing the product `((cube × cube) × [0,1])` measure
forward along `axisMix k` recovers the cube measure. We expose this as
a typeclass hypothesis `AxisMixMeasureHypothesis`; the discharge of the
hypothesis is the subject of the follow-up task
`infra:P1-axisMix-pushforward-prove`. The Fubini-style consequence
`lintegral_axisMix_eq_cube_of_hyp` then follows from `lintegral_map` in
a single step.
-/

/-- The headline pushforward identity, packaged as a typeclass so the
discharge is decoupled from downstream consumers (smooth `L^p`-RHS
Poincaré–Wirtinger). The instance asserts that, for every dimension
`d` and axis `k : Fin d`, mapping the axis-triple measure forward by
`axisMix` recovers the cube measure. The follow-up task
`infra:P1-axisMix-pushforward-prove` will provide the proof; until then
downstream lemmas take `[AxisMixMeasureHypothesis]` as a hypothesis
class. -/
class AxisMixMeasureHypothesis : Prop where
  /-- The pushforward of `axisTripleMeasure d` under
  `axisMix k` agrees with `cubeMeasure d`. -/
  axisMix_map_cubeMeasure : ∀ {d : ℕ} (k : Fin d),
    Measure.map
        (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
          axisMix k q.1.1 q.1.2 q.2)
        (axisTripleMeasure d)
      = cubeMeasure d

/-! ### Discharge of `AxisMixMeasureHypothesis`

The pushforward identity is proved by identifying both sides with the
`Fin d`-indexed product `Measure.pi (fun _ => unitIntervalMeasure)` via
`Measure.pi_eq` (rectangle extensionality). The cube side uses
`restrict_pi_pi`; the pushforward side decomposes the preimage of a
rectangle along the `j < k`/`j = k`/`j > k` trichotomy.
-/

/-- **Cube measure as a product.** The cube measure is the `Fin d`-fold
product of the unit-interval measure. Proof via `Measure.pi_eq`,
followed by `restrict_pi_pi` to identify the two factor structures. -/
lemma cubeMeasure_eq_pi (d : ℕ) :
    cubeMeasure d = Measure.pi (fun _ : Fin d => unitIntervalMeasure) := by
  -- `cubeMeasure d = (Measure.pi fun _ => volume).restrict (Set.pi univ fun _ => Ico 0 1)`.
  unfold cubeMeasure UnitCube unitIntervalMeasure
  rw [show (volume : Measure (Fin d → ℝ))
        = Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) from
        volume_pi (α := fun _ : Fin d => ℝ)]
  rw [Measure.restrict_pi_pi]
  -- Now both sides are `Measure.pi`s of restricted volumes; replace `Ico 0 1` by `Icc 0 1`.
  congr 1
  funext _
  exact restrict_Ico_eq_restrict_Icc

/-- The unit-interval measure is finite (mass `1`). -/
lemma unitIntervalMeasure_univ : unitIntervalMeasure Set.univ = 1 := by
  unfold unitIntervalMeasure
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  simp

/-- Auxiliary: the set `{x : Fin d → ℝ | ∀ j, P j → x j ∈ s j}`
equals the product `Set.pi Set.univ (fun j => if P j then s j else Set.univ)`. -/
private lemma forall_imp_mem_eq_pi {d : ℕ} (P : Fin d → Prop) [DecidablePred P]
    (s : Fin d → Set ℝ) :
    {x : Fin d → ℝ | ∀ j, P j → x j ∈ s j}
      = Set.pi Set.univ (fun j => if P j then s j else Set.univ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
  constructor
  · intro h j
    by_cases hj : P j
    · simp [hj, h j hj]
    · simp [hj]
  · intro h j hj
    have := h j
    simpa [hj] using this

/-- Computing the pushforward measure on rectangles: the preimage
of `Set.pi univ s` under `axisMix k` is itself a measurable rectangle. -/
private lemma axisMix_preimage_pi {d : ℕ} (k : Fin d) (s : Fin d → Set ℝ) :
    (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
        axisMix k q.1.1 q.1.2 q.2) ⁻¹' (Set.pi Set.univ s)
      = (Set.pi Set.univ (fun j => if k < j then s j else Set.univ)
            ×ˢ Set.pi Set.univ (fun j => if j < k then s j else Set.univ))
          ×ˢ s k := by
  classical
  ext ⟨⟨x, y⟩, τ⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff,
    Set.mem_prod]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      by_cases hj : k < j
      · simp only [hj, if_true]
        have := h j
        rwa [axisMix_gt k j hj] at this
      · simp [hj]
    · intro j
      by_cases hj : j < k
      · simp only [hj, if_true]
        have := h j
        rwa [axisMix_lt k j hj] at this
      · simp [hj]
    · have := h k
      rwa [axisMix_eq] at this
  · rintro ⟨⟨hx, hy⟩, hτ⟩ j
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · have hyj := hy j
      rw [if_pos hjk] at hyj
      rw [axisMix_lt k j hjk]
      exact hyj
    · subst hjk
      rw [axisMix_eq]
      exact hτ
    · have hxj := hx j
      rw [if_pos hjk] at hxj
      rw [axisMix_gt k j hjk]
      exact hxj

/-- Discharging the typeclass hypothesis: the pushforward of the
axis-triple measure under `axisMix k` equals the cube measure. -/
theorem axisMix_map_cubeMeasure_proved {d : ℕ} (k : Fin d) :
    Measure.map
        (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
          axisMix k q.1.1 q.1.2 q.2)
        (axisTripleMeasure d)
      = cubeMeasure d := by
  classical
  -- Reduce both sides to `Measure.pi (fun _ => unitIntervalMeasure)`.
  rw [cubeMeasure_eq_pi]
  symm
  -- Identify `Measure.pi (fun _ => unitIntervalMeasure)` as the unique measure
  -- agreeing with the pushforward on measurable rectangles.
  refine Measure.pi_eq (fun s hs => ?_)
  -- Evaluate the pushforward on a rectangle `Set.pi univ s`.
  set fmix : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ → (Fin d → ℝ) :=
    fun q => axisMix k q.1.1 q.1.2 q.2 with hfmix
  have hmeas_fmix : Measurable fmix := measurable_axisMix k
  have hms : MeasurableSet (Set.pi (Set.univ : Set (Fin d)) s) :=
    MeasurableSet.univ_pi hs
  rw [Measure.map_apply hmeas_fmix hms]
  -- Preimage as a product rectangle.
  rw [axisMix_preimage_pi k s]
  -- Decompose the axis-triple measure.
  unfold axisTripleMeasure
  rw [Measure.prod_prod, Measure.prod_prod]
  -- Each cube factor is a `Measure.pi`, evaluate via `pi_pi`.
  rw [cubeMeasure_eq_pi]
  have hAx : ∀ j : Fin d, MeasurableSet (if k < j then s j else (Set.univ : Set ℝ)) := by
    intro j
    by_cases hj : k < j
    · simp [hj, hs j]
    · simp [hj]
  have hAy : ∀ j : Fin d, MeasurableSet (if j < k then s j else (Set.univ : Set ℝ)) := by
    intro j
    by_cases hj : j < k
    · simp [hj, hs j]
    · simp [hj]
  rw [Measure.pi_pi, Measure.pi_pi]
  -- Now collect the three product factors back into a single product over `Fin d`.
  -- Goal:
  --   (∏ j, μ_I (if k < j then s j else univ))
  --     * (∏ j, μ_I (if j < k then s j else univ))
  --     * μ_I (s k)
  --     = ∏ j, μ_I (s j)
  -- Strategy: pull each `if`-form into `if k < j then μ_I (s j) else 1` etc.,
  -- then collapse the two products via `Finset.prod_mul_distrib`, and finally
  -- recognise the trichotomy.
  have hgt : (∏ j : Fin d, unitIntervalMeasure (if k < j then s j else Set.univ))
      = ∏ j : Fin d, (if k < j then unitIntervalMeasure (s j) else 1) := by
    refine Finset.prod_congr rfl ?_
    intro j _
    by_cases hj : k < j
    · simp [hj]
    · simp [hj, unitIntervalMeasure_univ]
  have hlt : (∏ j : Fin d, unitIntervalMeasure (if j < k then s j else Set.univ))
      = ∏ j : Fin d, (if j < k then unitIntervalMeasure (s j) else 1) := by
    refine Finset.prod_congr rfl ?_
    intro j _
    by_cases hj : j < k
    · simp [hj]
    · simp [hj, unitIntervalMeasure_univ]
  rw [hgt, hlt]
  -- Combine the two indicator products into one via prod_mul_distrib.
  rw [← Finset.prod_mul_distrib]
  -- Each factor now is `(if k < j then μ_I (s j) else 1) * (if j < k then μ_I (s j) else 1)`.
  -- This equals `if j ≠ k then μ_I (s j) else 1` (by trichotomy).
  have hcomb : ∀ j : Fin d,
      ((if k < j then unitIntervalMeasure (s j) else 1)
          * (if j < k then unitIntervalMeasure (s j) else 1))
        = (if j ≠ k then unitIntervalMeasure (s j) else 1) := by
    intro j
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · have hk1 : ¬ k < j := not_lt.mpr hjk.le
      have hk2 : j ≠ k := ne_of_lt hjk
      simp [hjk, hk1, hk2]
    · subst hjk
      simp
    · have hk1 : ¬ j < k := not_lt.mpr hjk.le
      have hk2 : j ≠ k := (ne_of_gt hjk)
      simp [hjk, hk1, hk2]
  have hcomb' :
      (∏ j : Fin d, (if k < j then unitIntervalMeasure (s j) else 1)
          * (if j < k then unitIntervalMeasure (s j) else 1))
        = ∏ j : Fin d, (if j ≠ k then unitIntervalMeasure (s j) else 1) :=
    Finset.prod_congr rfl (fun j _ => hcomb j)
  rw [hcomb']
  -- Finally: separate out the j = k factor explicitly.
  -- ∏ j, (if j ≠ k then μ_I (s j) else 1) * μ_I (s k) = ∏ j, μ_I (s j).
  have hfinal :
      (∏ j : Fin d, (if j ≠ k then unitIntervalMeasure (s j) else 1))
        * unitIntervalMeasure (s k)
      = ∏ j : Fin d, unitIntervalMeasure (s j) := by
    -- Rewrite the LHS product as prod over j ≠ k of μ_I (s j).
    have hk_mem : k ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ k
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin d))
          (fun j => unitIntervalMeasure (s j)) hk_mem]
    congr 1
    -- Show ∏ over univ of (if j ≠ k then μ_I (s j) else 1) = ∏ over erase k of μ_I (s j).
    rw [show (Finset.univ.erase k : Finset (Fin d))
          = Finset.univ.filter (fun j => j ≠ k) by
        ext j; simp [eq_comm]]
    rw [Finset.prod_filter]
  exact hfinal

instance : AxisMixMeasureHypothesis where
  axisMix_map_cubeMeasure := fun {d} k => axisMix_map_cubeMeasure_proved (d := d) k

/-- Re-export the hypothesis as a plain lemma for ergonomic `rw` use. -/
lemma axisMix_map_cubeMeasure_of_hyp [AxisMixMeasureHypothesis]
    (k : Fin d) :
    Measure.map
        (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
          axisMix k q.1.1 q.1.2 q.2)
        (axisTripleMeasure d)
      = cubeMeasure d :=
  AxisMixMeasureHypothesis.axisMix_map_cubeMeasure k

/-- **Fubini-style consequence of the pushforward.** Once the
pushforward identity holds, integrating any measurable
`G : (Fin d → ℝ) → ℝ≥0∞` against the cube measure equals integrating
`G ∘ axisMix k` against the axis-triple measure. The proof is one
`lintegral_map` away from the pushforward identity. -/
theorem lintegral_axisMix_eq_cube_of_hyp [AxisMixMeasureHypothesis]
    (k : Fin d) (G : (Fin d → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ q, G (axisMix k q.1.1 q.1.2 q.2) ∂(axisTripleMeasure d)
      = ∫⁻ z, G z ∂(cubeMeasure d) := by
  have hmap := axisMix_map_cubeMeasure_of_hyp (d := d) k
  have hlm : ∫⁻ z, G z
      ∂Measure.map (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
            axisMix k q.1.1 q.1.2 q.2) (axisTripleMeasure d)
        = ∫⁻ q, G (axisMix k q.1.1 q.1.2 q.2) ∂(axisTripleMeasure d) :=
    lintegral_map hG (measurable_axisMix k)
  -- Combine: rewrite the LHS' measure to `cubeMeasure d` using `hmap`.
  rw [← hmap]
  exact hlm.symm

/-- Sanity check: with `G = 1` the constant integrand, both sides
collapse to `cubeMeasure d Set.univ * 1 = 1 * 1 = 1` (cube has total
mass `1`) on the right, and to the integral of `1` against the
axis-triple measure on the left. The Fubini identity gives equality. -/
example [AxisMixMeasureHypothesis] (k : Fin d) :
    ∫⁻ _ : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ, (1 : ℝ≥0∞)
        ∂(axisTripleMeasure d)
      = ∫⁻ _ : Fin d → ℝ, (1 : ℝ≥0∞) ∂(cubeMeasure d) := by
  have h := lintegral_axisMix_eq_cube_of_hyp (d := d) k
    (fun _ => (1 : ℝ≥0∞)) measurable_const
  simpa using h

/-! ### Smooth-case `L^p`-RHS Poincaré–Wirtinger inequality

We prove the headline `poincareWirtinger_smooth_LpRHS`:

```
lpNormPer p (φ - periodicMean φ) ≤ d · ∑ i, lpNormPer p (∂_iφ).
```

The argument combines:

* the pointwise telescoping integral bound `pointwise_diff_integral_bound_fin`,
* Jensen on the unit-mass cube and unit interval to interchange the
  power and the integral,
* the power-mean inequality for the finite sum over `Fin d`,
* the axis-mix pushforward identity `lintegral_axisMix_eq_cube_of_hyp`
  to identify the iterated integral with the cube integral of the
  partial derivative.

All steps are carried out at the `ℝ≥0∞` level (Lebesgue integrals); the
real-valued `lpNormPer` form follows by `.toReal`.
-/

/-- Pointwise telescoping bound rewritten in `axisMix` form. The
underlying inequality is `pointwise_diff_integral_bound_fin`; the only
change is the rewrite of `Function.update (pathPoint x y k) k τ` to
`axisMix k x y τ` via `axisMix_eq_update_pathPoint`. -/
lemma pointwise_diff_axisMix_bound (φ : SmoothPeriodic d)
    {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d) :
    |(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y|
      ≤ ∑ i : Fin d,
          ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)| := by
  have hbase := pointwise_diff_integral_bound_fin φ hx hy
  -- Rewrite each summand using `axisMix_eq_update_pathPoint`.
  have hrw : (∑ i : Fin d,
      ∫ τ in (0 : ℝ)..1,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)
          (Function.update (pathPoint x y (i : ℕ)) i τ)|) =
      ∑ i : Fin d,
          ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)| := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    rw [axisMix_eq_update_pathPoint]
  rw [hrw] at hbase
  exact hbase

/-- Measurability of the partial-derivative enorm-composed-with-axisMix
function as a map of `q`. -/
private lemma measurable_partialDeriv_axisMix_enorm (φ : SmoothPeriodic d)
    (k : Fin d) :
    Measurable
      (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
        ‖((SmoothPeriodic.partialDeriv k φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (axisMix k q.1.1 q.1.2 q.2)‖ₑ) := by
  have hcont : Continuous ((SmoothPeriodic.partialDeriv k φ :
      SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
    (SmoothPeriodic.partialDeriv k φ).smooth.continuous
  have hmeas_g : Measurable ((SmoothPeriodic.partialDeriv k φ :
      SmoothPeriodic d) : (Fin d → ℝ) → ℝ) := hcont.measurable
  have hmeas_mix := measurable_axisMix (d := d) k
  exact (hmeas_g.comp hmeas_mix).enorm

/-- Measurability of `‖∂_kφ‖ₑ`. -/
private lemma measurable_partialDeriv_enorm (φ : SmoothPeriodic d) (k : Fin d) :
    Measurable
      (fun z : Fin d → ℝ =>
        ‖((SmoothPeriodic.partialDeriv k φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) z‖ₑ) := by
  have hcont : Continuous ((SmoothPeriodic.partialDeriv k φ :
      SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
    (SmoothPeriodic.partialDeriv k φ).smooth.continuous
  exact hcont.measurable.enorm

/-- **Headline lintegral pushforward identity for the `p`-th power of
the partial derivative.** Combine `lintegral_axisMix_eq_cube_of_hyp`
with `G(z) := ‖∂_kφ z‖ₑ ^ q` to get
```
∫⁻_{x,y,τ} ‖∂_kφ(axisMix k x y τ)‖ₑ^q
    = ∫⁻_z ‖∂_kφ z‖ₑ^q d(cube).
```
-/
lemma lintegral_axisMix_partialDeriv_pow [AxisMixMeasureHypothesis]
    (φ : SmoothPeriodic d) (k : Fin d) (q : ℝ) :
    ∫⁻ qry, ‖((SmoothPeriodic.partialDeriv k φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (axisMix k qry.1.1 qry.1.2 qry.2)‖ₑ ^ q
          ∂(axisTripleMeasure d)
      = ∫⁻ z, ‖((SmoothPeriodic.partialDeriv k φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d) := by
  have hG : Measurable
      (fun z : Fin d → ℝ =>
        ‖((SmoothPeriodic.partialDeriv k φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) z‖ₑ ^ q) :=
    (measurable_partialDeriv_enorm φ k).pow_const q
  exact lintegral_axisMix_eq_cube_of_hyp (d := d) k _ hG

/-! ### `L^1`-RHS smooth Poincaré–Wirtinger on the unit cube

Combining the pointwise telescoping bound (`pointwise_diff_axisMix_bound`),
the cube-restricted average identity for the mean, and the axis-mix
pushforward (`lintegral_axisMix_partialDeriv_pow`), we obtain the
Lebesgue-integral form of the Poincaré–Wirtinger inequality on the unit
cube for `p = 1`:

```
∫⁻_x ‖φ x − periodicMean φ‖ₑ d(cube)
    ≤ ∑_i ∫⁻_z ‖∂_iφ z‖ₑ d(cube).
```

This `p = 1` instance is the "easy" case of the `L^p`-RHS smooth-case
Poincaré–Wirtinger inequality: no Jensen-on-the-cube and no power-mean
inequality is needed. It is the headline for the density extension at
`p = 1`. The general `p > 1` case is left to a follow-up
(`infra:P1-poincare-smooth-LpRHS-pgeneral`); the additional pieces
required there are Jensen on a probability measure and the
power-mean inequality for finite sums, both already in Mathlib. -/

/-- Continuity of `axisMix i x y` as a function of `τ` (only the
`i`-th coordinate depends on `τ`). -/
private lemma continuous_axisMix_τ (i : Fin d) (x y : Fin d → ℝ) :
    Continuous (fun τ : ℝ => axisMix i x y τ) := by
  refine continuous_pi ?_
  intro j
  unfold axisMix
  by_cases hlt : j < i
  · simp only [hlt, if_true]; exact continuous_const
  · by_cases heq : j = i
    · subst heq; simp only [hlt, if_false, if_true]; exact continuous_id
    · simp only [hlt, heq, if_false]; exact continuous_const

/-- Convert the per-axis interval-integral of `|∂_iφ ∘ axisMix|` (an
`ℝ`-valued non-negative integral) to a Lebesgue integral of the enorm
on the unit interval `[0,1]`:
```
ENNReal.ofReal (∫₀¹ |g (axisMix i x y τ)| dτ)
    = ∫⁻_τ ∈ [0,1], ‖g (axisMix i x y τ)‖ₑ.
```
-/
private lemma intervalIntegral_abs_partialDeriv_axisMix_eq
    (φ : SmoothPeriodic d) (i : Fin d) (x y : Fin d → ℝ) :
    ENNReal.ofReal
        (∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (axisMix i x y τ)|) =
      ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
          ∂(volume : Measure ℝ) := by
  set h : ℝ → ℝ := fun τ => ((SmoothPeriodic.partialDeriv i φ :
      SmoothPeriodic d) : (Fin d → ℝ) → ℝ) (axisMix i x y τ) with hh_def
  have hcont : Continuous h := by
    have hc1 : Continuous ((SmoothPeriodic.partialDeriv i φ :
        SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous
    exact hc1.comp (continuous_axisMix_τ i x y)
  have habs_nn : ∀ τ : ℝ, 0 ≤ |h τ| := fun _ => abs_nonneg _
  have hint_Ioc :
      IntegrableOn (fun τ : ℝ => |h τ|) (Set.Ioc (0 : ℝ) 1)
        (volume : Measure ℝ) := by
    have hIcc :
        IntegrableOn (fun τ : ℝ => |h τ|) (Set.Icc (0 : ℝ) 1)
          (volume : Measure ℝ) :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont.abs.continuousOn
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  -- Rewrite intervalIntegral as setIntegral on `Ioc`.
  have hint_eq :
      ∫ τ in (0 : ℝ)..1, |h τ| = ∫ τ in Set.Ioc (0 : ℝ) 1, |h τ| := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hint_eq]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_Ioc
    (MeasureTheory.ae_of_all _ habs_nn)]
  -- Replace `Ioc` by `Icc` (NoAtoms in Lebesgue measure).
  rw [restrict_Ioc_eq_restrict_Icc]
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards with τ
  rw [Real.enorm_eq_ofReal_abs]

/-! ### `L^1`-RHS smooth Poincaré–Wirtinger on the unit cube (lintegral form)

Combining the pointwise telescoping bound
(`pointwise_diff_axisMix_bound`), Jensen on the unit-mass cube, and the
axis-mix pushforward (`lintegral_axisMix_eq_cube_of_hyp`), we obtain the
Lebesgue-integral form of the Poincaré–Wirtinger inequality on the unit
cube for `p = 1`:

```
∫⁻_x ‖φ x − periodicMean φ‖ₑ d(cube)
    ≤ ∑_i ∫⁻_z ‖∂_iφ z‖ₑ d(cube).
```

This `p = 1` instance is the "easy" case of the `L^p`-RHS smooth-case
Poincaré–Wirtinger inequality: no Jensen-on-the-cube and no power-mean
inequality is needed beyond the trivial `p = 1` Jensen which
`enorm_integral_le_lintegral_enorm` provides directly.

The general `p > 1` case is left to a follow-up; it requires Jensen
for general `p` on a probability measure and the power-mean
inequality for finite sums. -/

/-- The pointwise telescoping enorm bound, packaged at the
`ℝ≥0∞` level: for `(x, y) ∈ cube × cube`,
```
‖φ x − φ y‖ₑ ≤ ∑_i ∫⁻_τ ∈ Icc, ‖∂_iφ(axisMix i x y τ)‖ₑ d(volume_τ).
```
-/
private lemma pointwise_diff_lintegral_bound
    (φ : SmoothPeriodic d) {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d) :
    ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ≤
      ∑ i : Fin d,
        ∫⁻ τ in Set.Icc (0 : ℝ) 1,
          ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
            ∂(volume : Measure ℝ) := by
  classical
  have hbd := pointwise_diff_axisMix_bound (d := d) φ hx hy
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)| := by
    intro i _
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)
  have h1 :
      ENNReal.ofReal
          |(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y| ≤
        ENNReal.ofReal
          (∑ i : Fin d,
            ∫ τ in (0 : ℝ)..1,
              |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) (axisMix i x y τ)|) :=
    ENNReal.ofReal_le_ofReal hbd
  rw [Real.enorm_eq_ofReal_abs]
  rw [ENNReal.ofReal_sum_of_nonneg hnn] at h1
  refine h1.trans (Finset.sum_le_sum (fun i _ => ?_))
  exact (intervalIntegral_abs_partialDeriv_axisMix_eq φ i x y).le

/-- The Lebesgue-integral form of the `L^1`-RHS smooth Poincaré–Wirtinger
inequality on the unit cube. The constant is `1` (sharp for `p = 1`). -/
theorem eLpNormPer_one_sub_periodicMean_le [AxisMixMeasureHypothesis]
    (φ : SmoothPeriodic d) :
    ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x
              - periodicMean (φ : (Fin d → ℝ) → ℝ)‖ₑ ∂(cubeMeasure d)
      ≤ ∑ i : Fin d,
          ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ∂(cubeMeasure d) := by
  classical
  have hφ_cont : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
  have hμ_finite : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have hφ_int : IntegrableOn ((φ : (Fin d → ℝ) → ℝ)) (UnitCube d) := by
    have hcompact :
        IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : UnitCube d ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro y hy i _
      have := (mem_unitCube_iff.mp hy) i
      exact ⟨this.1, le_of_lt this.2⟩
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image hφ_cont.norm.continuousOn
    refine Measure.integrableOn_of_bounded hμ_finite hφ_cont.aestronglyMeasurable
      (M := M) ?_
    refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
    refine MeasureTheory.ae_of_all _ (fun y hy => ?_)
    exact hM (Set.mem_image_of_mem _ (hsub hy))
  -- Step (1): pointwise bound `‖φ x − ⨏ φ‖ₑ ≤ ∫⁻_y ‖φ x − φ y‖ₑ d(cube_y)`.
  have hpt_x : ∀ x ∈ UnitCube d,
      ‖(φ : (Fin d → ℝ) → ℝ) x
          - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ≤
        ∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ
          ∂(cubeMeasure d) := by
    intro x hx
    have hconst_int :
        IntegrableOn (fun _ : Fin d → ℝ => (φ : (Fin d → ℝ) → ℝ) x)
          (UnitCube d) := integrableOn_const hμ_finite
    have hsub :
        (∫ y in UnitCube d,
            ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y)) =
          (∫ _ in UnitCube d, (φ : (Fin d → ℝ) → ℝ) x) -
            ∫ y in UnitCube d, (φ : (Fin d → ℝ) → ℝ) y :=
      MeasureTheory.integral_sub hconst_int hφ_int
    have hvol : (∫ _ in UnitCube d, (φ : (Fin d → ℝ) → ℝ) x) =
        (φ : (Fin d → ℝ) → ℝ) x := by
      rw [setIntegral_const, measureReal_def, volume_unitCube]
      simp
    have hmean_eq :
        periodicMean ((φ : (Fin d → ℝ) → ℝ)) =
          ∫ y in UnitCube d, (φ : (Fin d → ℝ) → ℝ) y := rfl
    have hdiff_eq :
        (φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ)) =
          ∫ y in UnitCube d,
            ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y) := by
      rw [hsub, hvol, hmean_eq]
    rw [hdiff_eq]
    show _ ≤ ∫⁻ y, _ ∂(volume.restrict (UnitCube d))
    exact MeasureTheory.enorm_integral_le_lintegral_enorm _
  -- Step (2): integrate `hpt_x` and apply the pointwise telescope inside.
  have hstep_a :
      ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ
          ∂(cubeMeasure d)
        ≤ ∫⁻ x,
            (∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ
              ∂(cubeMeasure d))
              ∂(cubeMeasure d) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro x hx
    show _ ≤ ∫⁻ y, _ ∂(volume.restrict (UnitCube d))
    exact hpt_x x hx
  have hstep_b :
      ∫⁻ x,
          (∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ
            ∂(cubeMeasure d))
            ∂(cubeMeasure d)
        ≤ ∫⁻ x, ∫⁻ y,
            (∑ i : Fin d,
              ∫⁻ τ in Set.Icc (0 : ℝ) 1,
                ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
                  ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro x hx
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro y hy
    exact pointwise_diff_lintegral_bound (d := d) φ hx hy
  have h1 :
      ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ
          ∂(cubeMeasure d)
        ≤ ∫⁻ x, ∫⁻ y,
            (∑ i : Fin d,
              ∫⁻ τ in Set.Icc (0 : ℝ) 1,
                ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
                  ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) :=
    hstep_a.trans hstep_b
  -- Step (3): pull the finite sum out of the iterated lintegrals and identify
  -- each term via Fubini and the axis-mix pushforward.
  set F : Fin d → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ≥0∞ :=
    fun i x y τ =>
      ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
    with hF_def
  have hF_meas : ∀ i : Fin d, Measurable
      (fun q : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ => F i q.1.1 q.1.2 q.2) :=
    measurable_partialDeriv_axisMix_enorm φ
  -- Joint measurability of `(xy, τ) ↦ indicator(Icc, τ) * F i xy.1 xy.2 τ`.
  have hindic_full : ∀ i : Fin d, Measurable
      (fun p : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
        (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) p.2 *
          F i p.1.1 p.1.2 p.2) := by
    intro i
    apply Measurable.mul
    · exact (Measurable.indicator measurable_const measurableSet_Icc).comp
        measurable_snd
    · exact hF_meas i
  -- Pointwise rewrite of the τ-restrict integral as a τ-integral with indicator.
  have hint_eq : ∀ i : Fin d, ∀ x y : Fin d → ℝ,
      ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ) =
        ∫⁻ τ, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) τ *
          F i x y τ ∂(volume : Measure ℝ) := by
    intro i x y
    rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
    refine MeasureTheory.lintegral_congr (fun τ => ?_)
    by_cases hτ : τ ∈ Set.Icc (0 : ℝ) 1
    · simp [Set.indicator_of_mem hτ]
    · simp [Set.indicator_of_notMem hτ]
  -- Joint measurability of `(x, y) ↦ ∫⁻ τ in Icc, F i x y τ`.
  have hjoint_xy : ∀ i : Fin d, Measurable
      (fun xy : (Fin d → ℝ) × (Fin d → ℝ) =>
        ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i xy.1 xy.2 τ ∂(volume : Measure ℝ)) := by
    intro i
    simp_rw [hint_eq i]
    exact Measurable.lintegral_prod_right (hindic_full i)
  -- Identify each iterated integral with the product integral over `axisTriple`.
  have hfubini : ∀ i : Fin d,
      ∫⁻ x, ∫⁻ y, (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d) ∂(cubeMeasure d)
        = ∫⁻ q, F i q.1.1 q.1.2 q.2 ∂(axisTripleMeasure d) := by
    intro i
    unfold axisTripleMeasure unitIntervalMeasure
    rw [MeasureTheory.lintegral_prod _ (hF_meas i).aemeasurable]
    rw [MeasureTheory.lintegral_prod]
    exact (hjoint_xy i).aemeasurable
  -- Pushforward identity.
  have hpush : ∀ i : Fin d,
      ∫⁻ q, F i q.1.1 q.1.2 q.2 ∂(axisTripleMeasure d) =
        ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) z‖ₑ ∂(cubeMeasure d) := by
    intro i
    exact lintegral_axisMix_eq_cube_of_hyp (d := d) i _
      (measurable_partialDeriv_enorm φ i)
  -- Pull the sum past `∫⁻_y` (each fixed `x`).
  have hsum_meas_y : ∀ x : Fin d → ℝ, ∀ i : Fin d,
      AEMeasurable
        (fun y : Fin d → ℝ =>
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
        (cubeMeasure d) := by
    intro x i
    -- Compose the joint `(x, y) ↦ ...` with `y ↦ (x, y)`.
    have hcomp : Measurable (fun y : Fin d → ℝ => (x, y)) :=
      measurable_const.prodMk measurable_id
    exact ((hjoint_xy i).comp hcomp).aemeasurable
  have hpull_y : ∀ x : Fin d → ℝ,
      ∫⁻ y, (∑ i : Fin d,
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d) =
        ∑ i : Fin d, ∫⁻ y,
            (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) := by
    intro x
    rw [MeasureTheory.lintegral_finset_sum']
    intro i _
    exact hsum_meas_y x i
  -- Pull the sum past `∫⁻_x`.
  have hsum_meas_x : ∀ i : Fin d,
      AEMeasurable
        (fun x : Fin d → ℝ =>
          ∫⁻ y, (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d))
        (cubeMeasure d) := by
    intro i
    exact (Measurable.lintegral_prod_right (hjoint_xy i)).aemeasurable
  have hpull_x :
      ∫⁻ x, (∑ i : Fin d, ∫⁻ y,
          (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d))
          ∂(cubeMeasure d) =
        ∑ i : Fin d, ∫⁻ x, ∫⁻ y,
            (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) := by
    rw [MeasureTheory.lintegral_finset_sum']
    intro i _
    exact hsum_meas_x i
  -- Final calc chain.
  calc ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x
              - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ∂(cubeMeasure d)
      ≤ ∫⁻ x, ∫⁻ y,
            (∑ i : Fin d,
              ∫⁻ τ in Set.Icc (0 : ℝ) 1,
                F i x y τ ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) := h1
    _ = ∫⁻ x, (∑ i : Fin d,
              ∫⁻ y, (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ
                  ∂(volume : Measure ℝ)) ∂(cubeMeasure d))
            ∂(cubeMeasure d) := by
          refine MeasureTheory.lintegral_congr_ae ?_
          refine MeasureTheory.ae_of_all _ ?_
          intro x; exact hpull_y x
    _ = ∑ i : Fin d, ∫⁻ x, ∫⁻ y,
            (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) := hpull_x
    _ = ∑ i : Fin d, ∫⁻ q, F i q.1.1 q.1.2 q.2 ∂(axisTripleMeasure d) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hfubini i
    _ = ∑ i : Fin d,
          ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ∂(cubeMeasure d) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hpush i

/-- Sample example for the `p = 1` Lebesgue-form smooth Poincaré–Wirtinger
inequality: for the constant smooth-periodic function `const c`, both
sides reduce to `0` (since `φ - mean = 0` and `∂_iφ = 0`). -/
example [AxisMixMeasureHypothesis] (c : ℝ) :
    ∫⁻ x, ‖((SmoothPeriodic.const c : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x
              - periodicMean
                  ((SmoothPeriodic.const c : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ)‖ₑ ∂(cubeMeasure d)
      ≤ ∑ i : Fin d,
          ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
                  SmoothPeriodic d) : (Fin d → ℝ) → ℝ) z‖ₑ
            ∂(cubeMeasure d) :=
  eLpNormPer_one_sub_periodicMean_le (SmoothPeriodic.const c)

/-! ### `L^p`-RHS smooth Poincaré–Wirtinger on the unit cube (general `p > 1`)

We extend the `p = 1` headline to general `1 ≤ p < ∞`. The argument
combines:

* the pointwise integral telescope (`pointwise_diff_lintegral_bound`),
* Jensen on the probability measure `unitIntervalMeasure` (in `τ`),
* the power-mean inequality on the finite sum over `Fin d`
  (`ENNReal.rpow_arith_mean_le_arith_mean_rpow`),
* Jensen on the probability measure `cubeMeasure d` (in `y`),
* the axis-mix Fubini chain
  (`lintegral_axisMix_eq_cube_of_hyp`, identical to the `p = 1` case).

The constant is the loose `(d : ℝ≥0∞) ^ q` with `q := p.toReal`,
acceptable per the task spec; sharp `d ^ (q-1)` appears as an
intermediate.
-/

/-- The cube measure has total mass `1`. -/
lemma cubeMeasure_univ (d : ℕ) : cubeMeasure d Set.univ = 1 := by
  unfold cubeMeasure
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]

/-- **Jensen for a probability `lintegral`.** For a measure `μ` with
total mass `1` and any `g : α → ℝ≥0∞`, raising the integral of `g` to
the `q`-th power (`q ≥ 1`) is bounded by the integral of `g ^ q`.
This is Hölder's inequality with the constant function `1` on a
unit-mass measure. -/
private lemma lintegral_rpow_le_rpow_lintegral_of_prob
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ Set.univ = 1) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ a, g a ∂μ) ^ q ≤ ∫⁻ a, g a ^ q ∂μ := by
  -- Apply Hölder: ∫ g · 1 ≤ (∫ g^q)^(1/q) · (∫ 1^q')^(1/q'), with q' the conjugate.
  -- Since μ univ = 1, ∫ 1^q' = 1, so ∫ g ≤ (∫ g^q)^(1/q). Raise both sides to q.
  by_cases hq1 : q = 1
  · subst hq1
    simp [ENNReal.rpow_one]
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_lt : 1 < q := lt_of_le_of_ne hq (Ne.symm hq1)
  -- Conjugate exponent.
  set q' : ℝ := q / (q - 1) with hq'_def
  have hpq : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq_lt
  have hq'_pos : 0 < q' := hpq.symm.pos
  have hHolder :
      ∫⁻ a, g a * (1 : ℝ≥0∞) ∂μ ≤
        (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) *
          (∫⁻ a, (1 : ℝ≥0∞) ^ q' ∂μ) ^ (1 / q') :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg aemeasurable_const
  have h1pow : ∀ a : α, (1 : ℝ≥0∞) ^ q' = 1 := fun _ => ENNReal.one_rpow _
  have hint_one : ∫⁻ _ : α, (1 : ℝ≥0∞) ^ q' ∂μ = 1 := by
    simp [h1pow, hμ]
  rw [hint_one] at hHolder
  have hone_rpow : (1 : ℝ≥0∞) ^ (1 / q' : ℝ) = 1 := ENNReal.one_rpow _
  rw [hone_rpow, mul_one] at hHolder
  -- `hHolder : ∫ g ≤ (∫ g^q)^(1/q)`. Take q-th power.
  simp only [mul_one] at hHolder
  have hraise :
      (∫⁻ a, g a ∂μ) ^ q ≤
        ((∫⁻ a, g a ^ q ∂μ) ^ (1 / q)) ^ q :=
    ENNReal.rpow_le_rpow hHolder (le_of_lt hq_pos)
  rw [← ENNReal.rpow_mul] at hraise
  rw [one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one] at hraise
  exact hraise

/-- **Pointwise `q`-th-power bound after telescope and Jensen on `τ`.**
Combine the `axisMix` telescope with Jensen on the unit interval (a
probability measure) and the power-mean inequality on the `Fin d` sum.
For `(x, y) ∈ cube × cube` and `q ≥ 1`,
```
‖φ x − φ y‖ₑ^q ≤ (d : ℝ≥0∞)^(q-1) · ∑_i ∫⁻_τ ‖∂_iφ(axisMix i x y τ)‖ₑ^q
```
(up to a measurable-axis ordering). -/
private lemma pointwise_diff_qpow_lintegral_bound
    (φ : SmoothPeriodic d) {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d)
    {q : ℝ} (hq : 1 ≤ q) :
    ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ^ q ≤
      (d : ℝ≥0∞) ^ (q - 1) *
        ∑ i : Fin d,
          ∫⁻ τ in Set.Icc (0 : ℝ) 1,
            ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ ^ q
              ∂(volume : Measure ℝ) := by
  classical
  -- Step 1: pointwise enorm telescope.
  have hbase := pointwise_diff_lintegral_bound (d := d) φ hx hy
  -- Step 2: raise to q.
  have hpow1 :
      ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ^ q ≤
        (∑ i : Fin d,
          ∫⁻ τ in Set.Icc (0 : ℝ) 1,
            ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
              ∂(volume : Measure ℝ)) ^ q :=
    ENNReal.rpow_le_rpow hbase (le_trans zero_le_one hq)
  -- Step 3: power-mean on the finite sum (∑ a_i)^q ≤ d^(q-1) · ∑ a_i^q.
  -- When d = 0 the sum is empty, both sides are 0 since `Fin 0 → ℝ` is one-point.
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    -- `x = y` since `Fin 0 → ℝ` is a singleton; both sides become 0.
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    simp [ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hq)]
  -- For d > 0, apply the weighted power-mean with uniform weights w_i = 1/d.
  set w : Fin d → ℝ≥0∞ := fun _ => (d : ℝ≥0∞)⁻¹ with hw_def
  set z : Fin d → ℝ≥0∞ := fun i =>
    (d : ℝ≥0∞) *
      ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
          ∂(volume : Measure ℝ) with hz_def
  have hd_ne_zero : (d : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hdpos
  have hd_ne_top : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hw_sum : ∑ _i : Fin d, w _i = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.mul_inv_cancel hd_ne_zero hd_ne_top]
  -- The sum (∑ w_i z_i) equals ∑_i ∫⁻τ ... .
  have hwz : ∀ i : Fin d, w i * z i =
      ∫⁻ τ in Set.Icc (0 : ℝ) 1,
        ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
          ∂(volume : Measure ℝ) := by
    intro i
    show (d : ℝ≥0∞)⁻¹ *
        ((d : ℝ≥0∞) * (∫⁻ τ in Set.Icc (0 : ℝ) 1, _ ∂_)) = _
    rw [← mul_assoc, ENNReal.inv_mul_cancel hd_ne_zero hd_ne_top, one_mul]
  have hsum_eq :
      (∑ i : Fin d, w i * z i) =
        ∑ i : Fin d,
          ∫⁻ τ in Set.Icc (0 : ℝ) 1,
            ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
              ∂(volume : Measure ℝ) := by
    refine Finset.sum_congr rfl (fun i _ => hwz i)
  -- Apply the power-mean inequality.
  have hpm := ENNReal.rpow_arith_mean_le_arith_mean_rpow
    (s := (Finset.univ : Finset (Fin d))) w z hw_sum hq
  rw [hsum_eq] at hpm
  -- Compute (∑ w_i z_i^q) on the RHS = (1/d) ∑_i z_i^q
  --                                  = (1/d) ∑_i (d^q (∫⁻ τ ...)^q)
  --                                  = d^(q-1) ∑_i (∫⁻ τ ...)^q.
  -- Then bound (∫⁻ τ ...)^q ≤ ∫⁻ τ ...^q via Jensen (probability τ).
  -- We chain through hpm directly.
  refine hpow1.trans ?_
  refine hpm.trans ?_
  -- Now goal: ∑ w_i z_i^q ≤ d^(q-1) · ∑ ∫⁻ τ ...^q.
  have hwz_q : ∀ i : Fin d, w i * z i ^ q =
      (d : ℝ≥0∞) ^ (q - 1) *
        (∫⁻ τ in Set.Icc (0 : ℝ) 1,
          ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
            ∂(volume : Measure ℝ)) ^ q := by
    intro i
    show (d : ℝ≥0∞)⁻¹ *
        ((d : ℝ≥0∞) * (∫⁻ τ in Set.Icc (0 : ℝ) 1, _ ∂_)) ^ q = _
    rw [ENNReal.mul_rpow_of_nonneg _ _ (le_trans zero_le_one hq)]
    rw [show (d : ℝ≥0∞)⁻¹ = (d : ℝ≥0∞) ^ (-1 : ℝ) by
      rw [ENNReal.rpow_neg, ENNReal.rpow_one]]
    rw [show ((d : ℝ≥0∞) ^ (-1 : ℝ)) *
        ((d : ℝ≥0∞) ^ q *
          (∫⁻ τ in Set.Icc (0 : ℝ) 1, _ ∂_) ^ q) =
          ((d : ℝ≥0∞) ^ (-1 : ℝ) * (d : ℝ≥0∞) ^ q) *
          (∫⁻ τ in Set.Icc (0 : ℝ) 1, _ ∂_) ^ q by ring]
    rw [← ENNReal.rpow_add _ _ hd_ne_zero hd_ne_top]
    have heq : (-1 : ℝ) + q = q - 1 := by ring
    rw [heq]
  rw [show (∑ i : Fin d, w i * z i ^ q) =
      ∑ i : Fin d,
        (d : ℝ≥0∞) ^ (q - 1) *
          (∫⁻ τ in Set.Icc (0 : ℝ) 1,
            ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ
              ∂(volume : Measure ℝ)) ^ q from
      Finset.sum_congr rfl (fun i _ => hwz_q i)]
  rw [← Finset.mul_sum]
  -- Now: d^(q-1) · ∑ (∫⁻ τ G_i)^q ≤ d^(q-1) · ∑ ∫⁻ τ G_i^q.
  -- Use Jensen on each i, then sum.
  refine mul_le_mul_right ?_ _
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- Jensen on probability measure (volume restricted to Icc 0 1).
  -- We use the unit-interval measure.
  have hμ_uni : (Measure.restrict (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1))
      Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    simp
  have hg_meas : AEMeasurable
      (fun τ : ℝ => ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ)
      (Measure.restrict (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1)) := by
    have hcont : Continuous ((SmoothPeriodic.partialDeriv i φ :
          SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous
    have hcomp : Continuous (fun τ : ℝ =>
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (axisMix i x y τ)) :=
      hcont.comp (continuous_axisMix_τ i x y)
    exact hcomp.measurable.enorm.aemeasurable
  have hjensen :=
    lintegral_rpow_le_rpow_lintegral_of_prob (μ :=
      Measure.restrict (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1))
      hμ_uni hg_meas hq
  -- Rewrite the lintegral on `Icc` to match.
  show (∫⁻ τ in Set.Icc (0 : ℝ) 1, _ ∂(volume : Measure ℝ)) ^ q ≤
      ∫⁻ τ in Set.Icc (0 : ℝ) 1, _ ^ q ∂(volume : Measure ℝ)
  exact hjensen

/-- **Lintegral form of the `L^p`-RHS smooth Poincaré–Wirtinger
inequality on the unit cube, general `q ≥ 1`.** For `φ : SmoothPeriodic d`
and any real `q ≥ 1`,
```
∫⁻_x ‖φ x − periodicMean φ‖ₑ^q d(cube)
    ≤ (d : ℝ≥0∞)^q · ∑_i ∫⁻_z ‖∂_iφ(z)‖ₑ^q d(cube).
```
The constant is the loose `d^q` (acceptable per the task spec), arising
from `d^(q-1) · d` after the additional Jensen step on the cube measure
in `y`. -/
theorem lintegral_rpow_sub_periodicMean_le [AxisMixMeasureHypothesis]
    (φ : SmoothPeriodic d) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x
            - periodicMean (φ : (Fin d → ℝ) → ℝ)‖ₑ ^ q ∂(cubeMeasure d)
      ≤ (d : ℝ≥0∞) ^ q *
          ∑ i : Fin d,
            ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d) := by
  classical
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq_nn : 0 ≤ q := le_of_lt hq_pos
  -- Step 1: pointwise Jensen on the cube `y`. We have
  --   ‖φ x − ⟨φ⟩‖ₑ^q ≤ ∫⁻_y ‖φ x − φ y‖ₑ^q d(cube_y).
  -- This is `lintegral_rpow_le_rpow_lintegral_of_prob` applied with the
  -- function `y ↦ ‖φ x − φ y‖ₑ` and the cube measure (probability mass `1`).
  -- The mean is the cube integral on a measure-`1` cube, so
  -- `‖φ x − ⟨φ⟩‖ₑ ≤ ∫⁻_y ‖φ x − φ y‖ₑ`.
  have hpt_x : ∀ x ∈ UnitCube d,
      ‖(φ : (Fin d → ℝ) → ℝ) x
          - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ^ q ≤
        ∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ^ q
          ∂(cubeMeasure d) := by
    intro x hx
    -- First, ‖φx − ⟨φ⟩‖ₑ ≤ ∫⁻_y ‖φx − φy‖ₑ.
    have hφ_cont : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
    have hμ_finite : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by
      rw [volume_unitCube]; exact ENNReal.one_ne_top
    have hφ_int : IntegrableOn ((φ : (Fin d → ℝ) → ℝ)) (UnitCube d) := by
      have hcompact :
          IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
        isCompact_univ_pi (fun _ => isCompact_Icc)
      have hsub : UnitCube d ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
        intro y hy i _
        have := (mem_unitCube_iff.mp hy) i
        exact ⟨this.1, le_of_lt this.2⟩
      obtain ⟨M, hM⟩ := hcompact.bddAbove_image hφ_cont.norm.continuousOn
      refine Measure.integrableOn_of_bounded hμ_finite hφ_cont.aestronglyMeasurable
        (M := M) ?_
      refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
      refine MeasureTheory.ae_of_all _ (fun y hy => ?_)
      exact hM (Set.mem_image_of_mem _ (hsub hy))
    have hconst_int :
        IntegrableOn (fun _ : Fin d → ℝ => (φ : (Fin d → ℝ) → ℝ) x)
          (UnitCube d) := integrableOn_const hμ_finite
    have hsub :
        (∫ y in UnitCube d,
            ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y)) =
          (∫ _ in UnitCube d, (φ : (Fin d → ℝ) → ℝ) x) -
            ∫ y in UnitCube d, (φ : (Fin d → ℝ) → ℝ) y :=
      MeasureTheory.integral_sub hconst_int hφ_int
    have hvol : (∫ _ in UnitCube d, (φ : (Fin d → ℝ) → ℝ) x) =
        (φ : (Fin d → ℝ) → ℝ) x := by
      rw [setIntegral_const, measureReal_def, volume_unitCube]
      simp
    have hmean_eq :
        periodicMean ((φ : (Fin d → ℝ) → ℝ)) =
          ∫ y in UnitCube d, (φ : (Fin d → ℝ) → ℝ) y := rfl
    have hdiff_eq :
        (φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ)) =
          ∫ y in UnitCube d,
            ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y) := by
      rw [hsub, hvol, hmean_eq]
    have h_enorm_le :
        ‖(φ : (Fin d → ℝ) → ℝ) x
            - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ≤
          ∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ
            ∂(cubeMeasure d) := by
      rw [hdiff_eq]
      show _ ≤ ∫⁻ y, _ ∂(volume.restrict (UnitCube d))
      exact MeasureTheory.enorm_integral_le_lintegral_enorm _
    -- Raise to q.
    have h_pow := ENNReal.rpow_le_rpow h_enorm_le hq_nn
    -- Apply Jensen on probability measure cube_y.
    have hg_meas : AEMeasurable
        (fun y : Fin d → ℝ =>
          ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ)
        (cubeMeasure d) :=
      ((hφ_cont.measurable.const_sub _).enorm).aemeasurable
    have hjensen :=
      lintegral_rpow_le_rpow_lintegral_of_prob (μ := cubeMeasure d)
        (cubeMeasure_univ d) hg_meas hq
    exact h_pow.trans hjensen
  -- Step 2: pointwise telescope inside the integrand `‖φx − φy‖ₑ^q`.
  have hpt_xy : ∀ x ∈ UnitCube d, ∀ y ∈ UnitCube d,
      ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ^ q ≤
        (d : ℝ≥0∞) ^ (q - 1) *
          ∑ i : Fin d,
            ∫⁻ τ in Set.Icc (0 : ℝ) 1,
              ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ ^ q
                ∂(volume : Measure ℝ) := by
    intro x hx y hy
    exact pointwise_diff_qpow_lintegral_bound (d := d) φ hx hy hq
  -- Step 3: integrate the pointwise bound over y in cube.
  have hstep_a :
      ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ^ q
          ∂(cubeMeasure d)
        ≤ ∫⁻ x,
            (∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ^ q
              ∂(cubeMeasure d))
              ∂(cubeMeasure d) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro x hx
    show _ ≤ ∫⁻ y, _ ∂(volume.restrict (UnitCube d))
    exact hpt_x x hx
  have hstep_b :
      ∫⁻ x,
          (∫⁻ y, ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ₑ ^ q
            ∂(cubeMeasure d))
            ∂(cubeMeasure d)
        ≤ ∫⁻ x, ∫⁻ y,
            ((d : ℝ≥0∞) ^ (q - 1) *
              ∑ i : Fin d,
                ∫⁻ τ in Set.Icc (0 : ℝ) 1,
                  ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ ^ q
                    ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro x hx
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro y hy
    exact hpt_xy x hx y hy
  -- Step 4: pull constant `d^(q-1)` out of integrals; pull the sum out;
  -- identify each summand with the cube integral via Fubini + pushforward.
  set F : Fin d → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ≥0∞ :=
    fun i x y τ =>
      ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) (axisMix i x y τ)‖ₑ ^ q
    with hF_def
  have hF_meas : ∀ i : Fin d, Measurable
      (fun p : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ => F i p.1.1 p.1.2 p.2) := by
    intro i
    have h := measurable_partialDeriv_axisMix_enorm φ i
    exact h.pow_const q
  -- Joint measurability on (xy, τ).
  have hindic_full : ∀ i : Fin d, Measurable
      (fun p : ((Fin d → ℝ) × (Fin d → ℝ)) × ℝ =>
        (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) p.2 *
          F i p.1.1 p.1.2 p.2) := by
    intro i
    apply Measurable.mul
    · exact (Measurable.indicator measurable_const measurableSet_Icc).comp
        measurable_snd
    · exact hF_meas i
  -- Rewrite the τ-restrict lintegral as an indicator-multiplied integral.
  have hint_eq : ∀ i : Fin d, ∀ x y : Fin d → ℝ,
      ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ) =
        ∫⁻ τ, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) τ *
          F i x y τ ∂(volume : Measure ℝ) := by
    intro i x y
    rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
    refine MeasureTheory.lintegral_congr (fun τ => ?_)
    by_cases hτ : τ ∈ Set.Icc (0 : ℝ) 1
    · simp [Set.indicator_of_mem hτ]
    · simp [Set.indicator_of_notMem hτ]
  have hjoint_xy : ∀ i : Fin d, Measurable
      (fun xy : (Fin d → ℝ) × (Fin d → ℝ) =>
        ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i xy.1 xy.2 τ ∂(volume : Measure ℝ)) := by
    intro i
    simp_rw [hint_eq i]
    exact Measurable.lintegral_prod_right (hindic_full i)
  have hfubini : ∀ i : Fin d,
      ∫⁻ x, ∫⁻ y, (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d) ∂(cubeMeasure d)
        = ∫⁻ q, F i q.1.1 q.1.2 q.2 ∂(axisTripleMeasure d) := by
    intro i
    unfold axisTripleMeasure unitIntervalMeasure
    rw [MeasureTheory.lintegral_prod _ (hF_meas i).aemeasurable]
    rw [MeasureTheory.lintegral_prod]
    exact (hjoint_xy i).aemeasurable
  -- Pushforward identity for F.
  have hpush : ∀ i : Fin d,
      ∫⁻ q, F i q.1.1 q.1.2 q.2 ∂(axisTripleMeasure d) =
        ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d) := by
    intro i
    exact lintegral_axisMix_partialDeriv_pow (d := d) φ i q
  -- Pull the sum out of the iterated integrals (use measurability).
  have hsum_meas_y : ∀ x : Fin d → ℝ, ∀ i : Fin d,
      AEMeasurable
        (fun y : Fin d → ℝ =>
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
        (cubeMeasure d) := by
    intro x i
    have hcomp : Measurable (fun y : Fin d → ℝ => (x, y)) :=
      measurable_const.prodMk measurable_id
    exact ((hjoint_xy i).comp hcomp).aemeasurable
  have hpull_y : ∀ x : Fin d → ℝ,
      ∫⁻ y, (∑ i : Fin d,
          ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d) =
        ∑ i : Fin d, ∫⁻ y,
            (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) := by
    intro x
    rw [MeasureTheory.lintegral_finset_sum']
    intro i _
    exact hsum_meas_y x i
  have hsum_meas_x : ∀ i : Fin d,
      AEMeasurable
        (fun x : Fin d → ℝ =>
          ∫⁻ y, (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
            ∂(cubeMeasure d))
        (cubeMeasure d) := by
    intro i
    exact (Measurable.lintegral_prod_right (hjoint_xy i)).aemeasurable
  -- Combine: chain the inequalities and identify each summand.
  -- Strategy: Steps 3+4 give
  --    LHS ≤ ∫⁻x ∫⁻y (d^(q-1) * ∑_i ∫⁻τ G_i^q)
  -- Now pull constants and sums out:
  --    = d^(q-1) * ∫⁻x ∫⁻y ∑_i ∫⁻τ G_i^q
  --    = d^(q-1) * ∑_i ∫⁻x ∫⁻y ∫⁻τ G_i^q          (by hpull_y, hpull_x analog)
  --    = d^(q-1) * ∑_i ∫⁻z |∂_iφ z|^q d(cube)     (by Fubini + pushforward)
  -- We then absorb the d^(q-1) into d^q (acceptable looser constant).
  -- Step (4a): transport the Step-3 chain into one with const + sum on RHS.
  calc ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x
              - periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ^ q ∂(cubeMeasure d)
      ≤ ∫⁻ x, ∫⁻ y,
            ((d : ℝ≥0∞) ^ (q - 1) *
              ∑ i : Fin d,
                ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
              ∂(cubeMeasure d) ∂(cubeMeasure d) := hstep_a.trans hstep_b
    _ = ∫⁻ x, (d : ℝ≥0∞) ^ (q - 1) *
            ∫⁻ y, (∑ i : Fin d,
              ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
                ∂(cubeMeasure d)
            ∂(cubeMeasure d) := by
          have hd_ne_top : ((d : ℝ≥0∞) ^ (q - 1)) ≠ ⊤ :=
            ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hq)
              (ENNReal.natCast_ne_top _)
          refine MeasureTheory.lintegral_congr_ae ?_
          refine MeasureTheory.ae_of_all _ ?_
          intro x
          exact MeasureTheory.lintegral_const_mul' _ _ hd_ne_top
    _ = (d : ℝ≥0∞) ^ (q - 1) *
            ∫⁻ x, ∫⁻ y, (∑ i : Fin d,
              ∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
                ∂(cubeMeasure d) ∂(cubeMeasure d) := by
          have hd_ne_top : ((d : ℝ≥0∞) ^ (q - 1)) ≠ ⊤ :=
            ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hq)
              (ENNReal.natCast_ne_top _)
          exact MeasureTheory.lintegral_const_mul' _ _ hd_ne_top
    _ = (d : ℝ≥0∞) ^ (q - 1) *
            ∫⁻ x, (∑ i : Fin d, ∫⁻ y,
              (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
                ∂(cubeMeasure d)) ∂(cubeMeasure d) := by
          congr 1
          refine MeasureTheory.lintegral_congr_ae ?_
          refine MeasureTheory.ae_of_all _ ?_
          intro x
          exact hpull_y x
    _ = (d : ℝ≥0∞) ^ (q - 1) *
            ∑ i : Fin d, ∫⁻ x, ∫⁻ y,
              (∫⁻ τ in Set.Icc (0 : ℝ) 1, F i x y τ ∂(volume : Measure ℝ))
                ∂(cubeMeasure d) ∂(cubeMeasure d) := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum']
          intro i _
          exact hsum_meas_x i
    _ = (d : ℝ≥0∞) ^ (q - 1) *
            ∑ i : Fin d, ∫⁻ q', F i q'.1.1 q'.1.2 q'.2 ∂(axisTripleMeasure d) := by
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hfubini i
    _ = (d : ℝ≥0∞) ^ (q - 1) *
            ∑ i : Fin d,
              ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d) := by
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hpush i
    _ ≤ (d : ℝ≥0∞) ^ q *
            ∑ i : Fin d,
              ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d) := by
          -- For d > 0, d^(q-1) ≤ d^q.
          -- For d = 0, the sum is empty so both sides are 0.
          rcases Nat.eq_zero_or_pos d with hd0 | hdpos
          · subst hd0
            simp
          · have hd_one_le : (1 : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by
              exact_mod_cast hdpos
            have hd_le : (d : ℝ≥0∞) ^ (q - 1) ≤ (d : ℝ≥0∞) ^ q :=
              ENNReal.rpow_le_rpow_of_exponent_le hd_one_le (by linarith)
            exact mul_le_mul_left hd_le _

/-- Finite-sum subadditivity of `(·)^r` for `0 < r ≤ 1`: for `a : ι → ℝ≥0∞`,
`(∑ a_i)^r ≤ ∑ a_i^r`. Proved by induction over the finset. -/
private lemma finset_sum_rpow_le_of_le_one
    {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∑ i ∈ s, a i) ^ r ≤ ∑ i ∈ s, (a i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [ENNReal.zero_rpow_of_pos hr0]
  | insert i s hi IH =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    calc (a i + ∑ j ∈ s, a j) ^ r
        ≤ (a i) ^ r + (∑ j ∈ s, a j) ^ r :=
          ENNReal.rpow_add_le_add_rpow _ _ (le_of_lt hr0) hr1
      _ ≤ (a i) ^ r + ∑ j ∈ s, (a j) ^ r := by gcongr

/-- **Headline `L^p`-RHS smooth Poincaré–Wirtinger on the unit cube.**
For `φ : SmoothPeriodic d` and `1 ≤ p < ∞`, the periodic `L^p` seminorm
of `φ - periodicMean φ` is bounded by `d` times the sum of the
`L^p` seminorms of the partial derivatives:
```
eLpNormPer p (φ - periodicMean φ) ≤ d · ∑ i, eLpNormPer p (∂_iφ).
```
The constant `d` matches the standard Poincaré–Wirtinger
`poincareWirtingerConstant d`; the proof goes through the lintegral
form `lintegral_rpow_sub_periodicMean_le` and the conversion to
`eLpNormPer` via `eLpNorm_eq_lintegral_rpow_enorm_toReal`. -/
theorem poincareWirtinger_smooth_LpRHS [AxisMixMeasureHypothesis]
    (φ : SmoothPeriodic d) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNormPer (d := d) p
        ((φ : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      ≤ (d : ℝ≥0∞) *
          ∑ i : Fin d, eLpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) := by
  classical
  set q : ℝ := p.toReal with hq_def
  have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq_pos : 0 < q := ENNReal.toReal_pos hp_ne_zero hp_top
  have hq_one : 1 ≤ q := by
    rw [hq_def]
    have h1 : (1 : ℝ≥0∞).toReal ≤ p.toReal := ENNReal.toReal_mono hp_top hp
    simpa using h1
  have hq_inv_le : (1 / q : ℝ) ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ hq_one
  have hq_inv_pos : 0 < (1 / q : ℝ) := by positivity
  have hq_inv_nn : 0 ≤ (1 / q : ℝ) := le_of_lt hq_inv_pos
  -- Step 1: lintegral bound from the headline.
  have hbound := lintegral_rpow_sub_periodicMean_le (d := d) φ hq_one
  -- Step 2: take 1/q-th power.
  have hraise :
      (∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x
              - periodicMean (φ : (Fin d → ℝ) → ℝ)‖ₑ ^ q ∂(cubeMeasure d))
            ^ (1 / q) ≤
        ((d : ℝ≥0∞) ^ q *
          ∑ i : Fin d,
            ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) :=
    ENNReal.rpow_le_rpow hbound hq_inv_nn
  -- LHS rewrites as eLpNormPer p (φ - periodicMean φ).
  have hLHS_eq : eLpNormPer (d := d) p
      ((φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      = (∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x
              - periodicMean (φ : (Fin d → ℝ) → ℝ)‖ₑ ^ q
              ∂(cubeMeasure d)) ^ (1 / q) := by
    unfold eLpNormPer cubeMeasure
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top
      (φ.smooth.continuous.sub continuous_const).aestronglyMeasurable]
    rfl
  rw [hLHS_eq]
  -- Now bound the RHS of `hraise` further.
  refine hraise.trans ?_
  -- (d^q * ∑_i a_i)^(1/q) = d * (∑_i a_i)^(1/q).
  have hd_top : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd_rpow_eq : ((d : ℝ≥0∞) ^ q) ^ (1 / q : ℝ) = (d : ℝ≥0∞) := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hq_pos.ne', ENNReal.rpow_one]
  have hmul_rpow :
      ((d : ℝ≥0∞) ^ q *
        ∑ i : Fin d,
          ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) =
      (d : ℝ≥0∞) *
        (∑ i : Fin d,
          ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq_inv_nn, hd_rpow_eq]
  rw [hmul_rpow]
  -- Now: d * (∑_i a_i)^(1/q) ≤ d * ∑_i a_i^(1/q) where a_i = ∫⁻ ‖∂_iφ‖^q.
  -- Each a_i^(1/q) = eLpNormPer p ∂_iφ.
  have h_split :
      (∑ i : Fin d,
          ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) ≤
        ∑ i : Fin d,
          (∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) :=
    finset_sum_rpow_le_of_le_one _ _ hq_inv_pos hq_inv_le
  -- Identify each summand with eLpNormPer p ∂_iφ.
  have hRHSi_eq : ∀ i : Fin d,
      eLpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
        = (∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) := by
    intro i
    unfold eLpNormPer cubeMeasure
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous.aestronglyMeasurable]
  have hRHS_sum_eq :
      ∑ i : Fin d, eLpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
        = ∑ i : Fin d,
            (∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) z‖ₑ ^ q ∂(cubeMeasure d)) ^ (1 / q) :=
    Finset.sum_congr rfl (fun i _ => hRHSi_eq i)
  rw [hRHS_sum_eq]
  exact mul_le_mul_right h_split _

/-- Sanity-check `example`: for a constant smooth-periodic function
`φ = const c`, both `eLpNormPer p (φ - periodicMean φ)` and the sum of
`eLpNormPer p ∂_i φ` are zero, so the bound `0 ≤ d · 0` holds. -/
example [AxisMixMeasureHypothesis] (c : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNormPer (d := d) p
        (((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ =>
            periodicMean (((SmoothPeriodic.const c : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ))))
      ≤ (d : ℝ≥0∞) *
          ∑ i : Fin d, eLpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
                SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
  poincareWirtinger_smooth_LpRHS (SmoothPeriodic.const c) hp hp_top

/-! ### W^{1,1} density extension of the smooth Poincaré–Wirtinger inequality

We now lift the smooth `p = 1` bound `eLpNormPer_one_sub_periodicMean_le` to
all functions in `MemSobolevPer 1` via the density of `SmoothPeriodic d` in
`W^{1,1}_per` (see `SmoothPeriodic.denseInSobolevPer`). The general
`p > 1` smooth case is queued separately as
`infra:P1-poincare-smooth-LpRHS-pgt1`; until that lands, the density
extension here is restricted to `p = 1`.

The argument is the standard ε/3 (here ε/2) decomposition:

```
f − ⟨f⟩  =  (f − φ)  −  (⟨f⟩ − ⟨φ⟩)  +  (φ − ⟨φ⟩)
```

with `φ` a smooth approximation. The three summands are bounded by the
`L^1`-density witness, Jensen on the unit cube (cube has volume `1`), and
the smooth `p = 1` Poincaré inequality respectively.
-/

/-- The Lebesgue integral of `‖f‖ₑ` against the cube measure equals the
`p = 1` periodic `eLpNorm`. This is the cube-restricted specialisation of
the standard Mathlib identity `eLpNorm_one_eq_lintegral_enorm`. -/
private lemma eLpNormPer_one_eq_lintegral_enorm
    {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (cubeMeasure d)) :
    eLpNormPer (d := d) 1 f = ∫⁻ x, ‖f x‖ₑ ∂(cubeMeasure d) := by
  unfold eLpNormPer cubeMeasure at *
  exact MeasureTheory.eLpNorm_one_eq_lintegral_enorm hf

/-- For `f` integrable on the unit cube,
`|periodicMean f| ≤ ∫⁻ x, ‖f x‖ₑ ∂(cubeMeasure d)`. The cube has volume
`1`, so this is the trivial direction of Jensen for the `L^1` mean. -/
private lemma enorm_periodicMean_le_lintegral_enorm
    {f : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f (UnitCube d)) :
    ‖periodicMean f‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂(cubeMeasure d) := by
  -- `periodicMean f = ∫ x in UnitCube d, f x = ∫ x, f x ∂(cubeMeasure d)`.
  unfold cubeMeasure
  have h1 : periodicMean f = ∫ x, f x ∂(volume.restrict (UnitCube d)) := rfl
  rw [h1]
  exact MeasureTheory.enorm_integral_le_lintegral_enorm _

/-- Smooth `p = 1` Poincaré, in `eLpNormPer` form. This is just the
restatement of `eLpNormPer_one_sub_periodicMean_le` with both sides
expressed via `eLpNormPer 1 ·`. -/
theorem eLpNormPer_one_smooth_sub_periodicMean_le
    [AxisMixMeasureHypothesis] (φ : SmoothPeriodic d) :
    eLpNormPer (d := d) 1
        ((φ : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      ≤ ∑ i : Fin d, eLpNormPer (d := d) 1
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) := by
  classical
  -- Both sides are `lintegral` of `‖·‖ₑ` against the cube measure.
  have hφ_meas : Measurable (φ : (Fin d → ℝ) → ℝ) :=
    φ.smooth.continuous.measurable
  have hφ_aem : AEStronglyMeasurable
      ((φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      (cubeMeasure d) :=
    (hφ_meas.sub measurable_const).aestronglyMeasurable
  have hpartial_aem : ∀ i : Fin d,
      AEStronglyMeasurable
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)
        (cubeMeasure d) := fun i =>
    (SmoothPeriodic.partialDeriv i φ).smooth.continuous.measurable.aestronglyMeasurable
  have hbound := eLpNormPer_one_sub_periodicMean_le (d := d) φ
  -- Identify the LHS via `eLpNorm_one_eq_lintegral_enorm`.
  have hLHS : eLpNormPer (d := d) 1
      ((φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      = ∫⁻ x, ‖(φ : (Fin d → ℝ) → ℝ) x -
                periodicMean ((φ : (Fin d → ℝ) → ℝ))‖ₑ ∂(cubeMeasure d) := by
    rw [eLpNormPer_one_eq_lintegral_enorm hφ_aem]
    rfl
  -- Identify each RHS summand similarly.
  have hRHSi : ∀ i : Fin d,
      eLpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
        = ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) z‖ₑ ∂(cubeMeasure d) := by
    intro i
    exact eLpNormPer_one_eq_lintegral_enorm (hpartial_aem i)
  rw [hLHS]
  have hsum_eq :
      (∑ i : Fin d, eLpNormPer (d := d) 1
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ))
        = ∑ i : Fin d, ∫⁻ z, ‖((SmoothPeriodic.partialDeriv i φ :
                  SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z‖ₑ ∂(cubeMeasure d) :=
    Finset.sum_congr rfl (fun i _ => hRHSi i)
  rw [hsum_eq]
  exact hbound

/-- A `MemSobolevPer p` function is integrable on the unit cube whenever
`1 ≤ p`. (At `p = 1`, this is `MemLp f 1 ↔ Integrable f`.) -/
private lemma MemSobolevPer.integrableOn_one
    {f : (Fin d → ℝ) → ℝ} (hf : MemSobolevPer 1 f) :
    IntegrableOn f (UnitCube d) := by
  have hMemLp : MemLp f 1 (Measure.restrict volume (UnitCube d)) := hf.1
  exact (memLp_one_iff_integrable).1 hMemLp

/-- For `MemLpPer 1 h`, `‖periodicMean h‖ₑ ≤ eLpNormPer 1 h`. This is the
unit-cube specialisation of `eLpNorm_const_average_le` to `p = 1`, but
proved directly via `enorm_integral_le_lintegral_enorm`. -/
private lemma enorm_periodicMean_le_eLpNormPer_one
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer 1 f) :
    ‖periodicMean f‖ₑ ≤ eLpNormPer (d := d) 1 f := by
  have hint : IntegrableOn f (UnitCube d) :=
    (memLp_one_iff_integrable).1 hf
  have hbound := enorm_periodicMean_le_lintegral_enorm hint
  rw [eLpNormPer_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  exact hbound

/-- Helper: `eLpNormPer 1` of the constant function with value
`c : ℝ`. Cube has volume `1`, so the answer is `‖c‖ₑ`. -/
private lemma eLpNormPer_one_const (c : ℝ) :
    eLpNormPer (d := d) 1 (fun _ : Fin d → ℝ => c) = ‖c‖ₑ := by
  unfold eLpNormPer
  have hμ_univ : (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube d)) Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      volume_unitCube]
  have hμ_ne : (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube d)) ≠ 0 := by
    intro h
    rw [h] at hμ_univ
    simp at hμ_univ
  rw [MeasureTheory.eLpNorm_const c (by norm_num : (1 : ℝ≥0∞) ≠ 0) hμ_ne]
  simp [hμ_univ]

/-- **W^{1,1} density extension of the smooth Poincaré–Wirtinger
inequality on the unit cube.**

For every `f : (Fin d → ℝ) → ℝ` with `MemSobolevPer 1 f` and weak-derivative
family `g i` satisfying the standard regularity assumptions
(`Measurable`, `IsPeriodic`, `LocallyIntegrable`, `MemLpPer 1`), we have
the `L^1`-Poincaré inequality

```
lpNormPer 1 (f − periodicMean f) ≤ ∑ i, lpNormPer 1 (g i).
```

This is the headline `poincare_unitCube_W1p_public` from
`infra:P1-poincare-port-DeGiorgi-W1p`, restricted to `p = 1` because the
smooth `L^p`-RHS Poincaré inequality is currently only available at
`p = 1` (`eLpNormPer_one_sub_periodicMean_le`). The general `p > 1`
extension awaits `infra:P1-poincare-smooth-LpRHS-pgt1`.

Proof outline (the standard density argument): pick a smooth `φ` from
`SmoothPeriodic.denseInSobolevPer` with `sobolevNormPer 1 (f − φ)
(i ↦ g i − ∂_i φ) < δ` for any chosen `δ > 0`. Decompose

```
f − ⟨f⟩ = (f − φ) − (⟨f⟩ − ⟨φ⟩) + (φ − ⟨φ⟩),
```

bound each summand at the `eLpNormPer 1` level, and apply the smooth
Poincaré–Wirtinger inequality
`eLpNormPer_one_smooth_sub_periodicMean_le` to the third summand. Taking
`δ → 0` (or here, just sufficiently small) collapses the error terms.
The cube has volume `1`, which cleans up the bound between the `Lp`
norm of `f − φ` and the `enorm` of the mean difference. -/
theorem poincare_unitCube_W11_public
    [AxisMixMeasureHypothesis]
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : Measurable f) (hf_per : IsPeriodic f)
    (hf_loc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_sob : MemSobolevPer 1 f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_meas : ∀ i, Measurable (g i))
    (hg_per : ∀ i, IsPeriodic (g i))
    (hg_loc : ∀ i, MeasureTheory.LocallyIntegrable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    lpNormPer (d := d) 1
        ((f : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ => periodicMean f))
      ≤ ∑ i : Fin d, lpNormPer (d := d) 1 (g i) := by
  classical
  -- Regularity bookkeeping.
  have hf_lp : MemLpPer 1 f := hf_sob.1
  have hf_aem : AEStronglyMeasurable f (cubeMeasure d) :=
    hf_lp.aestronglyMeasurable
  have hg_lp : ∀ i, MemLpPer 1 (g i) := fun i => (hg_weak i).memLpPer
  -- Step 0: `eLpNormPer 1` of every term that will appear is finite.
  have hf_ne_top : eLpNormPer (d := d) 1 f ≠ ⊤ := hf_lp.eLpNormPer_ne_top
  have hg_ne_top : ∀ i, eLpNormPer (d := d) 1 (g i) ≠ ⊤ := fun i =>
    (hg_lp i).eLpNormPer_ne_top
  -- We want to show: real-valued
  --   lpNormPer 1 (f − ⟨f⟩) ≤ ∑ i, lpNormPer 1 (g i).
  -- We show the corresponding ENNReal bound; from finiteness, .toReal
  -- preserves the inequality.
  -- Step 1: an `eLpNormPer 1` triangle inequality on the decomposition
  --   f − ⟨f⟩ = (f − φ) − ⟨f − φ⟩ + (φ − ⟨φ⟩)
  -- Pick any `δ > 0`; we will contract the "error" terms below the
  -- Lebesgue-rhs sum by an arbitrarily small additive amount. The
  -- ENNReal version of the inequality with an arbitrary positive
  -- additive slack is easy to upgrade to the unscaled bound.
  -- Concrete strategy: for every `δ > 0`,
  --   eLpNormPer 1 (f − ⟨f⟩)
  --     ≤ ∑ i, eLpNormPer 1 (g i) + ENNReal.ofReal δ * (something).
  -- Then `δ → 0` gives the bound.
  -- Implementation: directly produce a single `φ` with
  -- `sobolevNormPer 1 (f − φ) (g − ∂φ) < δ` for an arbitrary `δ` and
  -- take `δ → 0` via `le_of_forall_pos_le_add` on `ℝ`.
  -- We will work entirely in ℝ for clarity, reducing the ENNReal pieces
  -- to `lpNormPer` values via `.toReal`.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ : ℝ := ε / ((d : ℝ) + 3) with hδ_def
  have hδ_pos : 0 < δ := by
    have hpos : (0 : ℝ) < (d : ℝ) + 3 := by positivity
    exact div_pos hε hpos
  -- Apply the density theorem.
  obtain ⟨φ, hφ⟩ :=
    SmoothPeriodic.denseInSobolevPer
      (p := 1) (le_refl _) ENNReal.one_ne_top
      hf_meas.aestronglyMeasurable hf_per hf_loc hf_lp
      hg_weak (fun i => (hg_meas i).aestronglyMeasurable)
      hg_per hg_loc hg_lp hδ_pos
  -- Unfold `sobolevNormPer 1 (f − φ) (g − ∂φ) < δ`.
  unfold sobolevNormPer at hφ
  -- Extract the two pieces.
  set u : (Fin d → ℝ) → ℝ :=
    (f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ) with hu_def
  set vi : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => g i x -
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x with hvi_def
  have hsum_lt :
      lpNormPer (d := d) 1 u + ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) < δ := by
    have h := hφ
    -- `(fun i x => g i x - ∂_i φ x) i x = vi i x` definitionally.
    -- Just re-fold via `change`.
    change lpNormPer (d := d) 1 u + ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) < δ at h
    exact h
  have hu_le_δ : lpNormPer (d := d) 1 u ≤ δ := by
    have hsum_nn : 0 ≤ ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) :=
      Finset.sum_nonneg (fun i _ => lpNormPer_nonneg _ _)
    linarith
  have hvi_sum_le_δ :
      ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) ≤ δ := by
    have hu_nn : 0 ≤ lpNormPer (d := d) 1 u := lpNormPer_nonneg _ _
    linarith
  -- Build the building blocks.
  -- (a) lpNormPer 1 (φ − ⟨φ⟩) ≤ ∑ i, lpNormPer 1 (∂_i φ).
  have h_smooth_real : lpNormPer (d := d) 1
      ((φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      ≤ ∑ i : Fin d, lpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) := by
    have hsmooth :=
      eLpNormPer_one_smooth_sub_periodicMean_le (d := d) φ
    -- Cast `.toReal`.
    have hLHS_ne_top : eLpNormPer (d := d) 1
        ((φ : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ)))) ≠ ⊤ := by
      have : MemLpPer 1
          ((φ : (Fin d → ℝ) → ℝ) -
            (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ)))) := by
        have h1 : MemLpPer 1 (φ : (Fin d → ℝ) → ℝ) :=
          MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ |>.1
        have h2 : MemLpPer 1
            (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))) := by
          have hcube : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by
            simp
          have : IsFiniteMeasure
              (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
            ⟨by
              rw [Measure.restrict_apply MeasurableSet.univ]
              simp⟩
          exact MemLp.toMemLpPer (memLp_const _)
        -- `f - g = f + (-g)`.
        have hsub : (φ : (Fin d → ℝ) → ℝ) -
            (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))) =
            (φ : (Fin d → ℝ) → ℝ) +
              (((-1 : ℝ)) • (fun _ : Fin d → ℝ =>
                periodicMean ((φ : (Fin d → ℝ) → ℝ)))) := by
          funext x; simp; ring
        rw [hsub]
        exact h1.add (h2.const_smul (-1 : ℝ))
      exact this.eLpNormPer_ne_top
    have hRHSi_ne_top : ∀ i : Fin d, eLpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) ≠ ⊤ := fun i => by
      have : MemLpPer 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) :=
        (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞)
          (SmoothPeriodic.partialDeriv i φ)).1
      exact this.eLpNormPer_ne_top
    have hRHS_ne_top : (∑ i : Fin d, eLpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)) ≠ ⊤ := by
      apply ENNReal.sum_ne_top.mpr
      intro i _
      exact hRHSi_ne_top i
    have htoReal := ENNReal.toReal_mono hRHS_ne_top hsmooth
    have hsum_toReal :
        (∑ i : Fin d, eLpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)).toReal =
        ∑ i : Fin d, lpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) := by
      rw [ENNReal.toReal_sum]
      · rfl
      · intro i _; exact hRHSi_ne_top i
    calc lpNormPer (d := d) 1
            ((φ : (Fin d → ℝ) → ℝ) -
              (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
        = (eLpNormPer (d := d) 1
            ((φ : (Fin d → ℝ) → ℝ) -
              (fun _ : Fin d → ℝ =>
                periodicMean ((φ : (Fin d → ℝ) → ℝ))))).toReal := rfl
      _ ≤ (∑ i : Fin d, eLpNormPer (d := d) 1
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)).toReal := htoReal
      _ = ∑ i : Fin d, lpNormPer (d := d) 1
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) := hsum_toReal
  -- (b) For each i: lpNormPer 1 (∂_i φ) = lpNormPer 1 (g i − vi i)
  --     ≤ lpNormPer 1 (g i) + lpNormPer 1 (vi i) (well, with a sign).
  -- We instead bound `lpNormPer 1 (∂_i φ) ≤ lpNormPer 1 (g i) +
  --   lpNormPer 1 (vi i)` via `∂_i φ = g i − vi i`. This is the
  -- triangle inequality after writing `∂_i φ = g i + (−vi i)`.
  have h_partial_le : ∀ i : Fin d,
      lpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
        ≤ lpNormPer (d := d) 1 (g i) + lpNormPer (d := d) 1 (vi i) := by
    intro i
    -- `∂_i φ = g i − vi i` pointwise.
    have hsplit : ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) =
        (g i) + (-1 : ℝ) • (vi i) := by
      funext x
      change ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x =
          g i x + (-1 : ℝ) * (vi i x)
      change ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x =
          g i x + (-1 : ℝ) * (g i x -
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
      ring
    -- `MemLpPer 1` of g i and vi i.
    have hg_lp_i : MemLpPer 1 (g i) := hg_lp i
    have hvi_lp_i : MemLpPer 1 (vi i) := by
      -- vi i = g i - ∂_i φ. The smooth function and its derivative are MemLpPer.
      have hgi : MemLpPer 1 (g i) := hg_lp_i
      have hpartial_lp : MemLpPer 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) :=
        (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞)
          (SmoothPeriodic.partialDeriv i φ)).1
      have heq : vi i = (g i) + (-1 : ℝ) • ((SmoothPeriodic.partialDeriv i φ :
            SmoothPeriodic d) : (Fin d → ℝ) → ℝ) := by
        funext x
        change g i x -
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x =
            g i x + (-1 : ℝ) * ((SmoothPeriodic.partialDeriv i φ :
                SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
        ring
      rw [heq]
      exact hgi.add (hpartial_lp.const_smul (-1 : ℝ))
    have hsmul_lp : MemLpPer 1 ((-1 : ℝ) • (vi i)) := hvi_lp_i.const_smul _
    have htri : lpNormPer (d := d) 1
        ((g i) + (-1 : ℝ) • (vi i))
          ≤ lpNormPer (d := d) 1 (g i) +
            lpNormPer (d := d) 1 ((-1 : ℝ) • (vi i)) :=
      lpNormPer_triangle hg_lp_i hsmul_lp (le_refl _)
    have hscale : lpNormPer (d := d) 1 ((-1 : ℝ) • (vi i)) =
        lpNormPer (d := d) 1 (vi i) := by
      rw [lpNormPer_smul]
      simp
    rw [hscale] at htri
    rw [hsplit]
    exact htri
  -- (c) Sum up: ∑ i lpNormPer 1 ∂_i φ ≤ ∑ i lpNormPer 1 (g i) + ∑ i lpNormPer 1 (vi i)
  have h_partial_sum :
      (∑ i : Fin d, lpNormPer (d := d) 1
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ))
        ≤ ∑ i : Fin d, lpNormPer (d := d) 1 (g i) +
            ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) := by
    have h1 : (∑ i : Fin d, lpNormPer (d := d) 1
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ))
        ≤ ∑ i : Fin d, (lpNormPer (d := d) 1 (g i) +
            lpNormPer (d := d) 1 (vi i)) :=
      Finset.sum_le_sum (fun i _ => h_partial_le i)
    have h2 : ∑ i : Fin d, (lpNormPer (d := d) 1 (g i) +
            lpNormPer (d := d) 1 (vi i)) =
        ∑ i : Fin d, lpNormPer (d := d) 1 (g i) +
            ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) :=
      Finset.sum_add_distrib
    linarith
  -- (d) Decompose `f − ⟨f⟩` as `(f − φ) − ⟨f − φ⟩ + (φ − ⟨φ⟩)` (pointwise).
  --     We bound each summand at the lpNormPer 1 level.
  -- Step (d.i): periodicMean f − periodicMean φ = periodicMean (f − φ).
  have hf_int : IntegrableOn f (UnitCube d) :=
    MemSobolevPer.integrableOn_one hf_sob
  have hφ_int : IntegrableOn (φ : (Fin d → ℝ) → ℝ) (UnitCube d) := by
    have : MemLpPer 1 (φ : (Fin d → ℝ) → ℝ) :=
      (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ).1
    exact (memLp_one_iff_integrable).1 this
  -- (d.ii): the "key triangle". We aim to show:
  --   lpNormPer 1 (f − ⟨f⟩) ≤ lpNormPer 1 u + |⟨u⟩| + lpNormPer 1 (φ − ⟨φ⟩)
  -- where `u = f − φ`. Concretely:
  --   f x − ⟨f⟩ = u x − ⟨u⟩ + (φ x − ⟨φ⟩).
  -- Compute lpNormPer 1 of each summand and apply triangle.
  -- Need MemLpPer 1 of each summand.
  have hu_lp : MemLpPer 1 u := by
    have hsub : u = f + ((-1 : ℝ)) • (φ : (Fin d → ℝ) → ℝ) := by
      funext x; simp [u]; ring
    have hφ_lp : MemLpPer 1 (φ : (Fin d → ℝ) → ℝ) :=
      (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ).1
    rw [hsub]
    exact hf_lp.add (hφ_lp.const_smul (-1 : ℝ))
  have hmean_u_const_lp : MemLpPer 1
      (fun _ : Fin d → ℝ => periodicMean u) := by
    have hcube : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by simp
    have : IsFiniteMeasure
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact MemLp.toMemLpPer (memLp_const _)
  have hφ_lp : MemLpPer 1 (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ).1
  have hmean_φ_const_lp : MemLpPer 1
      (fun _ : Fin d → ℝ =>
        periodicMean ((φ : (Fin d → ℝ) → ℝ))) := by
    have hcube : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by simp
    have : IsFiniteMeasure
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact MemLp.toMemLpPer (memLp_const _)
  -- The pointwise identity `f − ⟨f⟩ = (φ − ⟨φ⟩) + (u − ⟨u⟩)`, since
  -- ⟨f⟩ = ⟨φ⟩ + ⟨u⟩ and `f = φ + u`.
  have hmean_split : periodicMean f =
      periodicMean ((φ : (Fin d → ℝ) → ℝ)) + periodicMean u := by
    -- f = φ + u (since u = f - φ). Means add by `periodicMean_add`.
    have hreim : f = (φ : (Fin d → ℝ) → ℝ) + u := by
      funext x; simp [u]
    rw [hreim]
    exact periodicMean_add hφ_int (by
      -- u = f - φ integrable
      have h := hf_int.sub hφ_int
      simpa [u, sub_eq_add_neg] using h)
  -- Now build the pointwise decomposition.
  have hpoint :
      (fun x : Fin d → ℝ => f x - periodicMean f) =
        (fun x => ((φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ)))) +
          (fun x => u x - periodicMean u) := by
    funext x
    have huval : u x = f x - (φ : (Fin d → ℝ) → ℝ) x := rfl
    show f x - periodicMean f =
        ((φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
          (u x - periodicMean u)
    rw [hmean_split, huval]; ring
  -- Bound `lpNormPer 1 (f - ⟨f⟩)` by triangle.
  have hsum1_le : lpNormPer (d := d) 1
      ((fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
        (fun x => u x - periodicMean u))
      ≤ lpNormPer (d := d) 1
          (fun x : Fin d → ℝ =>
            (φ : (Fin d → ℝ) → ℝ) x -
              periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
        lpNormPer (d := d) 1 (fun x => u x - periodicMean u) := by
    -- MemLpPer of both summands.
    have hL1 : MemLpPer 1
        (fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ))) := by
      have hr : (fun x : Fin d → ℝ =>
            (φ : (Fin d → ℝ) → ℝ) x -
              periodicMean ((φ : (Fin d → ℝ) → ℝ))) =
          (φ : (Fin d → ℝ) → ℝ) + (-1 : ℝ) •
            (fun _ : Fin d → ℝ =>
              periodicMean ((φ : (Fin d → ℝ) → ℝ))) := by
        funext x; simp; ring
      rw [hr]
      exact hφ_lp.add (hmean_φ_const_lp.const_smul (-1 : ℝ))
    have hL2 : MemLpPer 1 (fun x : Fin d → ℝ => u x - periodicMean u) := by
      have hr : (fun x : Fin d → ℝ => u x - periodicMean u) =
          u + (-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u) := by
        funext x; simp; ring
      rw [hr]
      exact hu_lp.add (hmean_u_const_lp.const_smul (-1 : ℝ))
    exact lpNormPer_triangle hL1 hL2 (le_refl _)
  -- Convert the goal to use `fun x => f x - periodicMean f` so we can
  -- apply `hpoint`.
  have hgoal_eq : ((f : (Fin d → ℝ) → ℝ) -
      (fun _ : Fin d → ℝ => periodicMean f)) =
      fun x : Fin d → ℝ => f x - periodicMean f := by
    funext x; rfl
  rw [hgoal_eq, hpoint]
  -- Bound `lpNormPer 1 (u - ⟨u⟩) ≤ lpNormPer 1 u + lpNormPer 1 ⟨u⟩`.
  have hu_minus_mean : lpNormPer (d := d) 1
      (fun x : Fin d → ℝ => u x - periodicMean u)
      ≤ lpNormPer (d := d) 1 u +
        lpNormPer (d := d) 1
          (fun _ : Fin d → ℝ => periodicMean u) := by
    have hr : (fun x : Fin d → ℝ => u x - periodicMean u) =
        u + (-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp; ring
    rw [hr]
    have hsmul_lp : MemLpPer 1 ((-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u)) :=
      hmean_u_const_lp.const_smul _
    have htri : lpNormPer (d := d) 1
        (u + (-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u))
        ≤ lpNormPer (d := d) 1 u +
          lpNormPer (d := d) 1
            ((-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u)) :=
      lpNormPer_triangle hu_lp hsmul_lp (le_refl _)
    have hscale : lpNormPer (d := d) 1
        ((-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u)) =
        lpNormPer (d := d) 1 (fun _ : Fin d → ℝ => periodicMean u) := by
      rw [lpNormPer_smul]; simp
    linarith [htri, hscale.le, hscale.ge]
  -- The constant function `⟨u⟩` has lpNormPer 1 equal to `‖⟨u⟩‖ = |⟨u⟩|`.
  have hmean_const_lpnorm : lpNormPer (d := d) 1
      (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| := by
    unfold lpNormPer
    rw [eLpNormPer_one_const]
    simp [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal, abs_nonneg]
  -- Bound `|⟨u⟩| ≤ lpNormPer 1 u`. Use `enorm_periodicMean_le_eLpNormPer_one`.
  have habs_mean_u : |periodicMean u| ≤ lpNormPer (d := d) 1 u := by
    have hbnd := enorm_periodicMean_le_eLpNormPer_one (d := d) hu_lp
    have hLHS_eq : ‖periodicMean u‖ₑ = ENNReal.ofReal (|periodicMean u|) := by
      rw [Real.enorm_eq_ofReal_abs]
    have h_toReal :
        (ENNReal.ofReal (|periodicMean u|)).toReal ≤ (eLpNormPer 1 u).toReal :=
      ENNReal.toReal_mono hu_lp.eLpNormPer_ne_top (hLHS_eq ▸ hbnd)
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h_toReal
    exact h_toReal
  -- Now chain the inequalities.
  -- Final: lpNormPer 1 (f − ⟨f⟩)
  --   ≤ lpNormPer 1 (φ − ⟨φ⟩) + lpNormPer 1 (u − ⟨u⟩)        (triangle)
  --   ≤ ∑ i lpNormPer 1 (∂_i φ) + lpNormPer 1 u + |⟨u⟩|     (smooth + triangle)
  --   ≤ ∑ i lpNormPer 1 (∂_i φ) + 2 * lpNormPer 1 u           (mean Jensen)
  --   ≤ ∑ i lpNormPer 1 (g i) + ∑ i lpNormPer 1 (vi i) + 2 * lpNormPer 1 u
  --   ≤ ∑ i lpNormPer 1 (g i) + δ + 2 * δ
  -- and `δ = ε / (d + 3)` implies `2δ + δ * d ≤ ε`. We pick δ generously.
  -- Actually with the chosen δ = ε / (d + 3), we have:
  --   bound = ∑ + (d+3) * δ  is wrong; let's recount.
  -- At this point we want a clean linarith. Let's do it.
  have hu_le_real : lpNormPer (d := d) 1 u ≤ δ := hu_le_δ
  have hvi_sum_le_real : ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) ≤ δ := hvi_sum_le_δ
  have hmean_const_le : lpNormPer (d := d) 1
      (fun _ : Fin d → ℝ => periodicMean u) ≤ δ := by
    rw [hmean_const_lpnorm]; linarith [habs_mean_u, hu_le_real]
  -- chain
  have hfin1 : lpNormPer (d := d) 1
      (fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ)))
        ≤ ∑ i : Fin d, lpNormPer (d := d) 1
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) := h_smooth_real
  have hfin2 : (∑ i : Fin d, lpNormPer (d := d) 1
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)) ≤
      ∑ i : Fin d, lpNormPer (d := d) 1 (g i) + δ := by
    calc (∑ i : Fin d, lpNormPer (d := d) 1
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ))
        ≤ ∑ i : Fin d, lpNormPer (d := d) 1 (g i) +
            ∑ i : Fin d, lpNormPer (d := d) 1 (vi i) := h_partial_sum
      _ ≤ ∑ i : Fin d, lpNormPer (d := d) 1 (g i) + δ := by
            linarith
  -- We have d ≥ 0, and `δ ≤ ε`. We need: hsum1_le + hu_minus_mean
  -- ≤ ∑ + 3 δ ≤ ∑ + ε. Since δ = ε / (d + 3), we have 3δ ≤ ε for d ≥ 0.
  have hδ_three_le_ε : 3 * δ ≤ ε := by
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    have hpos : (0 : ℝ) < (d : ℝ) + 3 := by positivity
    have : 3 * δ = 3 * ε / ((d : ℝ) + 3) := by rw [hδ_def]; ring
    rw [this]
    rw [div_le_iff₀ hpos]
    nlinarith [hε.le, hd_nn]
  -- Chain.
  have hpart_LHS : lpNormPer (d := d) 1
      ((fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
        (fun x => u x - periodicMean u))
      ≤ ∑ i : Fin d, lpNormPer (d := d) 1 (g i) + ε := by
    have step1 := hsum1_le
    have step2 := hu_minus_mean
    have step3 := hfin1
    have step4 := hfin2
    have step5 := hmean_const_le
    have step6 := hu_le_real
    -- Combine.
    -- step1: lpNormPer (LHS) ≤ A + B where
    --   A = lpNormPer (φ − ⟨φ⟩) ≤ ∑ ∂_i φ ≤ ∑ g i + δ
    --   B = lpNormPer (u − ⟨u⟩) ≤ lpNormPer u + lpNormPer ⟨u⟩ ≤ δ + δ = 2δ
    -- so LHS ≤ ∑ g i + δ + 2δ = ∑ g i + 3δ ≤ ∑ g i + ε.
    linarith [step1, step2, step3, step4, step5, step6, hδ_three_le_ε]
  exact hpart_LHS

/-- Sanity-check `example`: the constant function `f = c` satisfies the
W^{1,1} Poincaré inequality trivially with `0 ≤ 0`, since `f − ⟨f⟩ = 0`
and any weak-derivative family is `0` a.e. -/
example [AxisMixMeasureHypothesis] (c : ℝ) :
    lpNormPer (d := d) 1
        ((fun _ : Fin d → ℝ => c) -
          (fun _ : Fin d → ℝ => periodicMean (fun _ : Fin d → ℝ => c)))
      ≤ ∑ _ : Fin d, lpNormPer (d := d) 1 (fun _ : Fin d → ℝ => (0 : ℝ)) := by
  -- Both sides are zero. The LHS reduces to `lpNormPer 1 0 = 0`.
  have hLHS_eq : ((fun _ : Fin d → ℝ => c) -
        (fun _ : Fin d → ℝ => periodicMean (fun _ : Fin d → ℝ => c))) =
      (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    funext x
    simp [periodicMean_const]
  rw [hLHS_eq]
  unfold lpNormPer eLpNormPer
  simp

/-! ### W^{1,p} density extension of the smooth Poincaré–Wirtinger inequality

The W^{1,1} version `poincare_unitCube_W11_public` lifted the smooth
`p = 1` bound to `MemSobolevPer 1`. With the general-`p` smooth bound
`poincareWirtinger_smooth_LpRHS` now available, the same density
argument extends to all `1 ≤ p < ∞`. The constant changes from `1`
(in the W^{1,1} version) to `poincareWirtingerConstant d = d`,
matching the universal Poincaré–Wirtinger constant.

The argument is the standard ε/3-style decomposition (the W^{1,1}
version uses ε/(d+3); here we use the same denominator scaled by `d`).

```
f − ⟨f⟩  =  (f − φ)  −  (⟨f⟩ − ⟨φ⟩)  +  (φ − ⟨φ⟩)
```

The mean-difference bound `|⟨u⟩| ≤ lpNormPer 1 u ≤ lpNormPer p u`
combines Jensen on the unit cube (volume `1`) with the Hölder
inclusion `lpNormPer_mono_exponent`.
-/

/-- Real-valued cast of the smooth Poincaré–Wirtinger inequality. For
`φ : SmoothPeriodic d` and `1 ≤ p < ∞`,
`lpNormPer p (φ − ⟨φ⟩) ≤ d · ∑ i, lpNormPer p (∂_i φ)`. -/
private theorem poincareWirtinger_smooth_LpRHS_real
    [AxisMixMeasureHypothesis]
    (φ : SmoothPeriodic d) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    lpNormPer (d := d) p
        ((φ : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      ≤ (d : ℝ) *
          ∑ i : Fin d, lpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) := by
  classical
  have hsmooth := poincareWirtinger_smooth_LpRHS (d := d) φ hp hp_top
  -- Finiteness of LHS (`MemLpPer p (φ − ⟨φ⟩)`).
  have hφ_lp : MemLpPer p (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic p φ).1
  have hcube_finite : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  have hmean_φ_const_lp : MemLpPer p
      (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))) :=
    MemLp.toMemLpPer (memLp_const _)
  have hLHS_lp : MemLpPer p
      ((φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ)))) := by
    have hsub : (φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))) =
        (φ : (Fin d → ℝ) → ℝ) +
          (((-1 : ℝ)) • (fun _ : Fin d → ℝ =>
            periodicMean ((φ : (Fin d → ℝ) → ℝ)))) := by
      funext x; simp; ring
    rw [hsub]
    exact hφ_lp.add (hmean_φ_const_lp.const_smul (-1 : ℝ))
  have hLHS_ne_top : eLpNormPer (d := d) p
      ((φ : (Fin d → ℝ) → ℝ) -
        (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ)))) ≠ ⊤ :=
    hLHS_lp.eLpNormPer_ne_top
  -- Each summand on the RHS is finite.
  have hRHSi_lp : ∀ i : Fin d, MemLpPer p
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) := fun i =>
    (MemSobolevPer.of_smoothPeriodic p
      (SmoothPeriodic.partialDeriv i φ)).1
  have hRHSi_ne_top : ∀ i : Fin d, eLpNormPer (d := d) p
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) ≠ ⊤ := fun i =>
    (hRHSi_lp i).eLpNormPer_ne_top
  have hsum_ne_top : (∑ i : Fin d, eLpNormPer (d := d) p
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact hRHSi_ne_top i
  have hd_ne_top : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hRHS_full_ne_top :
      (d : ℝ≥0∞) *
        ∑ i : Fin d, eLpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hd_ne_top hsum_ne_top
  have htoReal := ENNReal.toReal_mono hRHS_full_ne_top hsmooth
  -- Convert RHS toReal to real expression.
  have hd_toReal : ((d : ℝ≥0∞)).toReal = (d : ℝ) := by
    simp
  have hRHS_toReal :
      ((d : ℝ≥0∞) *
        ∑ i : Fin d, eLpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)).toReal =
      (d : ℝ) *
        ∑ i : Fin d, lpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) := by
    rw [ENNReal.toReal_mul, hd_toReal, ENNReal.toReal_sum]
    · rfl
    · intro i _; exact hRHSi_ne_top i
  calc lpNormPer (d := d) p
          ((φ : (Fin d → ℝ) → ℝ) -
            (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
      = (eLpNormPer (d := d) p
          ((φ : (Fin d → ℝ) → ℝ) -
            (fun _ : Fin d → ℝ =>
              periodicMean ((φ : (Fin d → ℝ) → ℝ))))).toReal := rfl
    _ ≤ ((d : ℝ≥0∞) *
          ∑ i : Fin d, eLpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)).toReal := htoReal
    _ = (d : ℝ) *
          ∑ i : Fin d, lpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) := hRHS_toReal

/-- **W^{1,p} density extension of the smooth Poincaré–Wirtinger
inequality on the unit cube** (the headline closing the `infra:P1-poincare`
PHASES.md bullet).

For every `f : (Fin d → ℝ) → ℝ` with `MemSobolevPer p f` and
weak-derivative family `g i` satisfying the standard regularity
hypotheses (`Measurable`, `IsPeriodic`, `LocallyIntegrable`, `MemLpPer p`),
the periodic Poincaré–Wirtinger inequality holds:

```
lpNormPer p (f − periodicMean f) ≤ d · ∑ i, lpNormPer p (g i).
```

The factor `d = poincareWirtingerConstant d` is the customary
Poincaré–Wirtinger constant on the unit cube. The proof is the
standard ε/(d+3) density argument: pick a smooth `φ` from
`SmoothPeriodic.denseInSobolevPer` with `sobolevNormPer p (f − φ)
(i ↦ g i − ∂_i φ) < δ`, decompose

```
f − ⟨f⟩ = (f − φ) − (⟨f⟩ − ⟨φ⟩) + (φ − ⟨φ⟩),
```

bound each summand at `lpNormPer p`, and apply the smooth bound
`poincareWirtinger_smooth_LpRHS_real` to the third summand. The mean
term uses `|⟨u⟩| ≤ lpNormPer 1 u ≤ lpNormPer p u` (Jensen + Hölder
inclusion under volume `1`). Taking `δ → 0` collapses the error terms.

The `MemLpPer p (g i)` hypothesis is required because `HasWeakDerivPer.memLpPer`
only delivers `MemLpPer 1`; for general `p` it must be supplied. -/
theorem poincareWirtinger
    [AxisMixMeasureHypothesis]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_sob : MemSobolevPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_per : ∀ i, IsPeriodic (g i))
    (hg_loc : ∀ i, MeasureTheory.LocallyIntegrable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_lp : ∀ i, MemLpPer p (g i)) :
    lpNormPer (d := d) p
        ((f : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ => periodicMean f))
      ≤ poincareWirtingerConstant d *
          ∑ i : Fin d, lpNormPer (d := d) p (g i) := by
  classical
  -- Regularity bookkeeping.
  have hf_lp : MemLpPer p f := hf_sob.1
  -- Also need MemLpPer 1 of f for the mean step (Jensen). At p ≥ 1 with
  -- finite-measure unit cube, `MemLpPer p` implies `MemLpPer 1` by
  -- Hölder inclusion at the eLpNormPer level.
  have hcube_finite : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Step 0: real-valued reformulation; we work in ℝ throughout.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ : ℝ := ε / ((d : ℝ) + 3) with hδ_def
  have hδ_pos : 0 < δ := by
    have hpos : (0 : ℝ) < (d : ℝ) + 3 := by positivity
    exact div_pos hε hpos
  -- Apply the density theorem at exponent p.
  obtain ⟨φ, hφ⟩ :=
    SmoothPeriodic.denseInSobolevPer
      (p := p) hp hp_top
      hf_meas hf_per hf_loc hf_lp
      hg_weak hg_meas
      hg_per hg_loc hg_lp hδ_pos
  unfold sobolevNormPer at hφ
  set u : (Fin d → ℝ) → ℝ :=
    (f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ) with hu_def
  set vi : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => g i x -
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x with hvi_def
  have hsum_lt :
      lpNormPer (d := d) p u + ∑ i : Fin d, lpNormPer (d := d) p (vi i) < δ := by
    have h := hφ
    change lpNormPer (d := d) p u + ∑ i : Fin d, lpNormPer (d := d) p (vi i) < δ at h
    exact h
  have hu_le_δ : lpNormPer (d := d) p u ≤ δ := by
    have hsum_nn : 0 ≤ ∑ i : Fin d, lpNormPer (d := d) p (vi i) :=
      Finset.sum_nonneg (fun i _ => lpNormPer_nonneg _ _)
    linarith
  have hvi_sum_le_δ :
      ∑ i : Fin d, lpNormPer (d := d) p (vi i) ≤ δ := by
    have hu_nn : 0 ≤ lpNormPer (d := d) p u := lpNormPer_nonneg _ _
    linarith
  -- (a) Smooth bound: lpNormPer p (φ − ⟨φ⟩) ≤ d · ∑ i, lpNormPer p (∂_i φ).
  have h_smooth_real :
      lpNormPer (d := d) p
          ((φ : (Fin d → ℝ) → ℝ) -
            (fun _ : Fin d → ℝ => periodicMean ((φ : (Fin d → ℝ) → ℝ))))
        ≤ (d : ℝ) *
            ∑ i : Fin d, lpNormPer (d := d) p
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) :=
    poincareWirtinger_smooth_LpRHS_real (d := d) φ hp hp_top
  -- (b) Triangle bound: lpNormPer p (∂_i φ) ≤ lpNormPer p (g i) + lpNormPer p (vi i).
  have h_partial_le : ∀ i : Fin d,
      lpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
        ≤ lpNormPer (d := d) p (g i) + lpNormPer (d := d) p (vi i) := by
    intro i
    have hsplit : ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) =
        (g i) + (-1 : ℝ) • (vi i) := by
      funext x
      change ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x =
          g i x + (-1 : ℝ) * (g i x -
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
      ring
    have hg_lp_i : MemLpPer p (g i) := hg_lp i
    have hvi_lp_i : MemLpPer p (vi i) := by
      have hpartial_lp : MemLpPer p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) :=
        (MemSobolevPer.of_smoothPeriodic p
          (SmoothPeriodic.partialDeriv i φ)).1
      have heq : vi i = (g i) + (-1 : ℝ) • ((SmoothPeriodic.partialDeriv i φ :
            SmoothPeriodic d) : (Fin d → ℝ) → ℝ) := by
        funext x
        change g i x -
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x =
            g i x + (-1 : ℝ) * ((SmoothPeriodic.partialDeriv i φ :
                SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
        ring
      rw [heq]
      exact hg_lp_i.add (hpartial_lp.const_smul (-1 : ℝ))
    have hsmul_lp : MemLpPer p ((-1 : ℝ) • (vi i)) := hvi_lp_i.const_smul _
    have htri : lpNormPer (d := d) p
        ((g i) + (-1 : ℝ) • (vi i))
          ≤ lpNormPer (d := d) p (g i) +
            lpNormPer (d := d) p ((-1 : ℝ) • (vi i)) :=
      lpNormPer_triangle hg_lp_i hsmul_lp hp
    have hscale : lpNormPer (d := d) p ((-1 : ℝ) • (vi i)) =
        lpNormPer (d := d) p (vi i) := by
      rw [lpNormPer_smul]; simp
    rw [hscale] at htri
    rw [hsplit]
    exact htri
  -- (c) Sum the partials: ∑ i lpNormPer p ∂_i φ ≤ ∑ i lpNormPer p (g i) + ∑ i lpNormPer p (vi i).
  have h_partial_sum :
      (∑ i : Fin d, lpNormPer (d := d) p
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ))
        ≤ ∑ i : Fin d, lpNormPer (d := d) p (g i) +
            ∑ i : Fin d, lpNormPer (d := d) p (vi i) := by
    have h1 : (∑ i : Fin d, lpNormPer (d := d) p
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ))
        ≤ ∑ i : Fin d, (lpNormPer (d := d) p (g i) +
            lpNormPer (d := d) p (vi i)) :=
      Finset.sum_le_sum (fun i _ => h_partial_le i)
    have h2 : ∑ i : Fin d, (lpNormPer (d := d) p (g i) +
            lpNormPer (d := d) p (vi i)) =
        ∑ i : Fin d, lpNormPer (d := d) p (g i) +
            ∑ i : Fin d, lpNormPer (d := d) p (vi i) :=
      Finset.sum_add_distrib
    linarith
  -- (d) Decompose `f − ⟨f⟩ = (φ − ⟨φ⟩) + (u − ⟨u⟩)` (pointwise).
  -- Need integrability of f, φ on the cube to use `periodicMean_add`.
  -- At p ≥ 1 we get IntegrableOn from `MemLpPer p` via Hölder inclusion to L^1.
  have hf_lp1 : MemLpPer 1 f := by
    -- Hölder inclusion: MemLpPer p f and 1 ≤ p give MemLpPer 1 f on a finite-measure space.
    refine ⟨hf_lp.aestronglyMeasurable, ?_⟩
    have hbound : eLpNormPer (d := d) 1 f ≤ eLpNormPer (d := d) p f :=
      eLpNormPer_mono_exponent f hf_lp.aestronglyMeasurable hp
    exact lt_of_le_of_lt hbound (lt_of_le_of_ne le_top hf_lp.eLpNormPer_ne_top)
  have hf_int : IntegrableOn f (UnitCube d) :=
    (memLp_one_iff_integrable).1 hf_lp1
  have hφ_lp_p : MemLpPer p (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic p φ).1
  have hφ_lp1 : MemLpPer 1 (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ).1
  have hφ_int : IntegrableOn (φ : (Fin d → ℝ) → ℝ) (UnitCube d) :=
    (memLp_one_iff_integrable).1 hφ_lp1
  have hu_lp : MemLpPer p u := by
    have hsub : u = f + ((-1 : ℝ)) • (φ : (Fin d → ℝ) → ℝ) := by
      funext x; simp [u]; ring
    rw [hsub]
    exact hf_lp.add (hφ_lp_p.const_smul (-1 : ℝ))
  have hu_lp1 : MemLpPer 1 u := by
    refine ⟨hu_lp.aestronglyMeasurable, ?_⟩
    have hbound : eLpNormPer (d := d) 1 u ≤ eLpNormPer (d := d) p u :=
      eLpNormPer_mono_exponent u hu_lp.aestronglyMeasurable hp
    exact lt_of_le_of_lt hbound (lt_of_le_of_ne le_top hu_lp.eLpNormPer_ne_top)
  have hmean_u_const_lp : MemLpPer p
      (fun _ : Fin d → ℝ => periodicMean u) :=
    MemLp.toMemLpPer (memLp_const _)
  have hmean_φ_const_lp : MemLpPer p
      (fun _ : Fin d → ℝ =>
        periodicMean ((φ : (Fin d → ℝ) → ℝ))) :=
    MemLp.toMemLpPer (memLp_const _)
  have hmean_split : periodicMean f =
      periodicMean ((φ : (Fin d → ℝ) → ℝ)) + periodicMean u := by
    have hreim : f = (φ : (Fin d → ℝ) → ℝ) + u := by
      funext x; simp [u]
    rw [hreim]
    exact periodicMean_add hφ_int (by
      have h := hf_int.sub hφ_int
      simpa [u, sub_eq_add_neg] using h)
  have hpoint :
      (fun x : Fin d → ℝ => f x - periodicMean f) =
        (fun x => ((φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ)))) +
          (fun x => u x - periodicMean u) := by
    funext x
    have huval : u x = f x - (φ : (Fin d → ℝ) → ℝ) x := rfl
    show f x - periodicMean f =
        ((φ : (Fin d → ℝ) → ℝ) x - periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
          (u x - periodicMean u)
    rw [hmean_split, huval]; ring
  have hsum1_le : lpNormPer (d := d) p
      ((fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
        (fun x => u x - periodicMean u))
      ≤ lpNormPer (d := d) p
          (fun x : Fin d → ℝ =>
            (φ : (Fin d → ℝ) → ℝ) x -
              periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
        lpNormPer (d := d) p (fun x => u x - periodicMean u) := by
    have hL1 : MemLpPer p
        (fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ))) := by
      have hr : (fun x : Fin d → ℝ =>
            (φ : (Fin d → ℝ) → ℝ) x -
              periodicMean ((φ : (Fin d → ℝ) → ℝ))) =
          (φ : (Fin d → ℝ) → ℝ) + (-1 : ℝ) •
            (fun _ : Fin d → ℝ =>
              periodicMean ((φ : (Fin d → ℝ) → ℝ))) := by
        funext x; simp; ring
      rw [hr]
      exact hφ_lp_p.add (hmean_φ_const_lp.const_smul (-1 : ℝ))
    have hL2 : MemLpPer p (fun x : Fin d → ℝ => u x - periodicMean u) := by
      have hr : (fun x : Fin d → ℝ => u x - periodicMean u) =
          u + (-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u) := by
        funext x; simp; ring
      rw [hr]
      exact hu_lp.add (hmean_u_const_lp.const_smul (-1 : ℝ))
    exact lpNormPer_triangle hL1 hL2 hp
  have hgoal_eq : ((f : (Fin d → ℝ) → ℝ) -
      (fun _ : Fin d → ℝ => periodicMean f)) =
      fun x : Fin d → ℝ => f x - periodicMean f := by
    funext x; rfl
  rw [hgoal_eq, hpoint]
  -- Bound `lpNormPer p (u - ⟨u⟩) ≤ lpNormPer p u + lpNormPer p ⟨u⟩`.
  have hu_minus_mean : lpNormPer (d := d) p
      (fun x : Fin d → ℝ => u x - periodicMean u)
      ≤ lpNormPer (d := d) p u +
        lpNormPer (d := d) p
          (fun _ : Fin d → ℝ => periodicMean u) := by
    have hr : (fun x : Fin d → ℝ => u x - periodicMean u) =
        u + (-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp; ring
    rw [hr]
    have hsmul_lp : MemLpPer p ((-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u)) :=
      hmean_u_const_lp.const_smul _
    have htri : lpNormPer (d := d) p
        (u + (-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u))
        ≤ lpNormPer (d := d) p u +
          lpNormPer (d := d) p
            ((-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u)) :=
      lpNormPer_triangle hu_lp hsmul_lp hp
    have hscale : lpNormPer (d := d) p
        ((-1 : ℝ) • (fun _ : Fin d → ℝ => periodicMean u)) =
        lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
      rw [lpNormPer_smul]; simp
    linarith [htri, hscale.le, hscale.ge]
  -- The constant function `⟨u⟩` has `lpNormPer 1 ⟨u⟩ = |⟨u⟩|`. By
  -- Hölder inclusion under volume `1`, `lpNormPer 1 ⟨u⟩ ≤ lpNormPer p ⟨u⟩`,
  -- and conversely from Jensen `|⟨u⟩| ≤ lpNormPer 1 u ≤ lpNormPer p u`.
  -- We bound `lpNormPer p ⟨u⟩` via this chain.
  have hmean_const_lpnorm_one : lpNormPer (d := d) 1
      (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| := by
    unfold lpNormPer
    rw [eLpNormPer_one_const]
    simp [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal, abs_nonneg]
  have habs_mean_u : |periodicMean u| ≤ lpNormPer (d := d) 1 u := by
    have hbnd := enorm_periodicMean_le_eLpNormPer_one (d := d) hu_lp1
    have hLHS_eq : ‖periodicMean u‖ₑ = ENNReal.ofReal (|periodicMean u|) := by
      rw [Real.enorm_eq_ofReal_abs]
    have h_toReal :
        (ENNReal.ofReal (|periodicMean u|)).toReal ≤ (eLpNormPer 1 u).toReal :=
      ENNReal.toReal_mono hu_lp1.eLpNormPer_ne_top (hLHS_eq ▸ hbnd)
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h_toReal
    exact h_toReal
  have hL1_le_Lp_u : lpNormPer (d := d) 1 u ≤ lpNormPer (d := d) p u :=
    lpNormPer_mono_exponent u hu_lp hp
  -- Bridge from `lpNormPer 1 ⟨u⟩` to `lpNormPer p ⟨u⟩`. The constant
  -- function `⟨u⟩` has `lpNormPer p` equal to `|⟨u⟩|` regardless of `p`,
  -- but it suffices to use `lpNormPer_mono_exponent` here.
  have hconst_le : lpNormPer (d := d) p
      (fun _ : Fin d → ℝ => periodicMean u) ≤ lpNormPer (d := d) p u := by
    -- |⟨u⟩| = lpNormPer 1 ⟨u⟩ ≤ lpNormPer p ⟨u⟩? Not quite — need the other direction.
    -- Direct route: |⟨u⟩| ≤ lpNormPer 1 u ≤ lpNormPer p u, and
    -- lpNormPer p (const c) = lpNormPer 1 (const c) (volume=1, so any L^p
    -- norm of a constant is |c|). We use the latter.
    have hp_const : lpNormPer (d := d) p
        (fun _ : Fin d → ℝ => periodicMean u) =
        |periodicMean u| := by
      -- For finite measure of total mass 1, `eLpNorm p (const c) = ‖c‖ₑ`.
      unfold lpNormPer eLpNormPer
      have hμ_univ : (Measure.restrict (volume : Measure (Fin d → ℝ))
          (UnitCube d)) Set.univ = 1 := by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      have hμ_ne : (Measure.restrict (volume : Measure (Fin d → ℝ))
          (UnitCube d)) ≠ 0 := by
        intro h
        rw [h] at hμ_univ
        simp at hμ_univ
      have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
      rw [MeasureTheory.eLpNorm_const _ hp_ne_zero hμ_ne]
      simp [hμ_univ, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal, abs_nonneg]
    rw [hp_const]
    calc |periodicMean u|
        ≤ lpNormPer (d := d) 1 u := habs_mean_u
      _ ≤ lpNormPer (d := d) p u := hL1_le_Lp_u
  -- Now chain everything.
  have hu_le_real : lpNormPer (d := d) p u ≤ δ := hu_le_δ
  have hvi_sum_le_real : ∑ i : Fin d, lpNormPer (d := d) p (vi i) ≤ δ :=
    hvi_sum_le_δ
  have hmean_const_le : lpNormPer (d := d) p
      (fun _ : Fin d → ℝ => periodicMean u) ≤ δ :=
    le_trans hconst_le hu_le_real
  -- Smooth bound + partial sum: ≤ d · (∑ g i + δ) = d · ∑ g i + d · δ.
  have hfin1 : lpNormPer (d := d) p
      (fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ)))
        ≤ (d : ℝ) *
            ∑ i : Fin d, lpNormPer (d := d) p
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) := h_smooth_real
  have hfin2 : (d : ℝ) *
        (∑ i : Fin d, lpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ)) ≤
      (d : ℝ) * (∑ i : Fin d, lpNormPer (d := d) p (g i) + δ) := by
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    have hinner : (∑ i : Fin d, lpNormPer (d := d) p
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ))
          ≤ ∑ i : Fin d, lpNormPer (d := d) p (g i) + δ := by
      calc (∑ i : Fin d, lpNormPer (d := d) p
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ))
          ≤ ∑ i : Fin d, lpNormPer (d := d) p (g i) +
              ∑ i : Fin d, lpNormPer (d := d) p (vi i) := h_partial_sum
        _ ≤ ∑ i : Fin d, lpNormPer (d := d) p (g i) + δ := by linarith
    exact mul_le_mul_of_nonneg_left hinner hd_nn
  -- Slack budget: total error ≤ (d + 2) δ ≤ ε since δ = ε / (d + 3).
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
  have hslack : ((d : ℝ) + 2) * δ ≤ ε := by
    have hpos : (0 : ℝ) < (d : ℝ) + 3 := by positivity
    have hkey : ((d : ℝ) + 2) * δ = ((d : ℝ) + 2) * ε / ((d : ℝ) + 3) := by
      rw [hδ_def]; ring
    rw [hkey]
    rw [div_le_iff₀ hpos]
    nlinarith [hε.le, hd_nn]
  -- Final chain.
  have hpart_LHS : lpNormPer (d := d) p
      ((fun x : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x -
            periodicMean ((φ : (Fin d → ℝ) → ℝ))) +
        (fun x => u x - periodicMean u))
      ≤ poincareWirtingerConstant d *
          ∑ i : Fin d, lpNormPer (d := d) p (g i) + ε := by
    -- Combine pieces.
    -- LHS ≤ A + B where
    --   A = lpNormPer p (φ − ⟨φ⟩) ≤ d · ∑ ∂_i φ ≤ d · (∑ g i + δ)
    --                              = d · ∑ g i + d · δ
    --   B = lpNormPer p (u − ⟨u⟩) ≤ lpNormPer p u + lpNormPer p ⟨u⟩
    --                              ≤ δ + δ = 2 δ
    -- Total ≤ d · ∑ g i + (d + 2) δ ≤ d · ∑ g i + ε.
    have step1 := hsum1_le
    have step2 := hu_minus_mean
    have step3 := hfin1
    have step4 := hfin2
    have step5 := hmean_const_le
    have step6 := hu_le_real
    have step7 := hslack
    have hpc : poincareWirtingerConstant d = (d : ℝ) :=
      poincareWirtingerConstant_def d
    rw [hpc]
    nlinarith [step1, step2, step3, step4, step5, step6, step7,
      lpNormPer_nonneg (d := d) p u,
      Finset.sum_nonneg (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer (d := d) p (g i))
        (fun i _ => lpNormPer_nonneg _ _)]
  exact hpart_LHS

/-- Sanity-check `example`: the constant smooth-periodic function
`φ = const c` satisfies the W^{1,p} Poincaré–Wirtinger inequality
trivially with `0 ≤ d · 0`, since `φ − ⟨φ⟩ = 0` and `∂_i φ = 0`. -/
example [AxisMixMeasureHypothesis] (c : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    lpNormPer (d := d) p
        (((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) -
          (fun _ : Fin d → ℝ =>
            periodicMean (((SmoothPeriodic.const c : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ))))
      ≤ (d : ℝ) *
          ∑ i : Fin d, lpNormPer (d := d) p
            ((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
                SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
  poincareWirtinger_smooth_LpRHS_real (SmoothPeriodic.const c) hp hp_top

/-! ### Phase 2c-α: AE-periodic Poincaré-Wirtinger wrapper

The downstream consumer chain (apriori bundles, `PaperCBundleForK`,
`T10PaperResidues`) holds Sobolev/Lp data only modulo a.e.-equality on
the unit cube. The wrapper `poincareWirtinger_AEPeriodicRep` accepts
a function `f` together with an `AEPeriodicRep` (chosen periodic
representative on the cube) and delegates to the pointwise-periodic
`poincareWirtinger` after transporting Sobolev membership and the
weak-derivative property to the representative side.

Supporting transport lemmas:

* `lpNormPer_congr_ae_unitCube`
* `periodicMean_congr_ae_unitCube`
* `MemLpPer.congr_ae_unitCube`
* `MemSobolevPer.congr_ae_unitCube`
* `HasWeakDerivPer.congr_ae_unitCube`

These say that the named quantity / property is invariant under
unit-cube a.e.-equality of its function (and, for `HasWeakDerivPer`,
also of its derivative). -/

section AEPeriodicPoincare

/-- Unit-cube a.e. equality preserves `lpNormPer`. -/
lemma lpNormPer_congr_ae_unitCube
    {p : ℝ≥0∞} {f g : (Fin d → ℝ) → ℝ}
    (hfg : f =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] g) :
    lpNormPer (d := d) p f = lpNormPer (d := d) p g := by
  unfold lpNormPer eLpNormPer
  rw [eLpNorm_congr_ae hfg]

/-- Unit-cube a.e. equality preserves `periodicMean`. -/
lemma periodicMean_congr_ae_unitCube
    {f g : (Fin d → ℝ) → ℝ}
    (hfg : f =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] g) :
    periodicMean (d := d) f = periodicMean (d := d) g := by
  unfold periodicMean periodicIntegral
  exact integral_congr_ae hfg

/-- Transport `MemLpPer` across unit-cube a.e. equality. -/
lemma MemLpPer.congr_ae_unitCube
    {p : ℝ≥0∞} {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (d := d) p f)
    (hfg : f =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] g) :
    MemLpPer (d := d) p g :=
  MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hfg hf.toMemLp)

/-- Transport `HasWeakDerivPer` across unit-cube a.e. equality of the
function `f` (the derivative `g` is unchanged). -/
lemma HasWeakDerivPer.congr_ae_unitCube_f
    {i : Fin d} {f f' g : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer (d := d) i f g)
    (hff' : f =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] f') :
    HasWeakDerivPer (d := d) i f' g := by
  refine ⟨h.memLpPer, ?_⟩
  intro φ
  -- For each test function `φ`, the IBP identity transfers because
  -- `f · ∂ᵢ φ =ᵐ f' · ∂ᵢ φ` on the cube.
  have hpair :
      (fun x => f x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
        =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)]
          (fun x => f' x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [hff'] with x hx
    simp [hx]
  have hint :
      periodicIntegral
          (fun x => f x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
        = periodicIntegral
            (fun x => f' x *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) := by
    unfold periodicIntegral
    exact integral_congr_ae hpair
  -- Combine with the IBP identity for `f`.
  have := h.integral_eq φ
  rw [this, hint]

/-- Transport `HasWeakDerivPer` across unit-cube a.e. equality of *both*
the function `f` and the derivative `g`. -/
lemma HasWeakDerivPer.congr_ae_unitCube
    {i : Fin d} {f f' g g' : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer (d := d) i f g)
    (hff' : f =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] f')
    (hg' : MemLpPer (d := d) 1 g')
    (hgg' : g =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] g') :
    HasWeakDerivPer (d := d) i f' g' :=
  (h.congr_ae_unitCube_f hff').congr_ae hg' hgg'

/-- Transport `MemSobolevPer` across unit-cube a.e. equality. -/
lemma MemSobolevPer.congr_ae_unitCube
    {p : ℝ≥0∞} {f g : (Fin d → ℝ) → ℝ}
    (hf : MemSobolevPer (d := d) p f)
    (hfg : f =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ))
              (UnitCube d)] g) :
    MemSobolevPer (d := d) p g := by
  refine ⟨hf.1.congr_ae_unitCube hfg, ?_⟩
  obtain ⟨w, hw⟩ := hf.2
  refine ⟨w, fun i => ?_⟩
  exact (hw i).congr_ae_unitCube_f hfg

/-- **Poincaré–Wirtinger with AE-periodic representatives.**

Conclusion in terms of the original bare functions `f`, `g`; uses
chosen periodic representatives internally only to satisfy the existing
pointwise-periodic `poincareWirtinger`. -/
theorem poincareWirtinger_AEPeriodicRep
    [AxisMixMeasureHypothesis]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : (Fin d → ℝ) → ℝ}
    (hf_rep : AEPeriodicRep (d := d) f)
    (hf_sob : MemSobolevPer (d := d) p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer (d := d) i f (g i))
    (hg_rep : ∀ i, AEPeriodicRep (d := d) (g i))
    (hg_lp : ∀ i, MemLpPer (d := d) p (g i)) :
    lpNormPer (d := d) p
        (f - fun _ : Fin d → ℝ => periodicMean (d := d) f)
      ≤ poincareWirtingerConstant d *
          ∑ i : Fin d, lpNormPer (d := d) p (g i) := by
  classical
  -- **Phase 2c-γ cleanup** (`infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`):
  -- the `_meas` arguments have been dropped because they were unused —
  -- the pointwise-periodic `poincareWirtinger` (applied below to the
  -- chosen representatives) consumes whole-volume measurability via
  -- `LocallyIntegrable.aestronglyMeasurable` on the periodic
  -- representatives, not on the bare functions `f` and `g i`.
  -- Step 1: transport `MemLpPer` from `f`/`g i` to their representatives.
  have hf_rep_lp : MemLpPer (d := d) p hf_rep.rep :=
    MemLpPer.congr_ae_unitCube hf_sob.1 hf_rep.ae_eq.symm
  have hg_rep_lp : ∀ i, MemLpPer (d := d) p (hg_rep i).rep :=
    fun i => MemLpPer.congr_ae_unitCube (hg_lp i) (hg_rep i).ae_eq.symm
  -- Step 2: local integrability of the representatives via periodicity.
  have hf_rep_loc : LocallyIntegrable hf_rep.rep
      (volume : Measure (Fin d → ℝ)) :=
    MemLpPer.locallyIntegrable_of_periodic (d := d) hp hf_rep_lp hf_rep.periodic
  have hg_rep_loc : ∀ i, LocallyIntegrable (hg_rep i).rep
      (volume : Measure (Fin d → ℝ)) :=
    fun i => MemLpPer.locallyIntegrable_of_periodic (d := d) hp
      (hg_rep_lp i) (hg_rep i).periodic
  -- Step 3: transport Sobolev membership to `hf_rep.rep`.
  have hf_rep_sob : MemSobolevPer (d := d) p hf_rep.rep :=
    hf_sob.congr_ae_unitCube hf_rep.ae_eq.symm
  -- Step 4: transport weak-derivative property to representatives.
  -- Need `MemLpPer 1 (hg_rep i).rep` for the derivative-side congr_ae,
  -- obtained from `MemLpPer p` via Hölder inclusion (cube is finite).
  have hg_rep_lp_one : ∀ i, MemLpPer (d := d) 1 (hg_rep i).rep := fun i =>
    -- Transport directly: `g i` has `MemLpPer 1` from `(hg_weak i).memLpPer`,
    -- so its a.e.-rep `(hg_rep i).rep` has it too.
    MemLpPer.congr_ae_unitCube (hg_weak i).memLpPer (hg_rep i).ae_eq.symm
  have hg_rep_weak : ∀ i,
      HasWeakDerivPer (d := d) i hf_rep.rep ((hg_rep i).rep) := by
    intro i
    exact (hg_weak i).congr_ae_unitCube
      hf_rep.ae_eq.symm
      (hg_rep_lp_one i)
      (hg_rep i).ae_eq.symm
  -- Step 5: apply the pointwise-periodic Poincaré-Wirtinger inequality.
  -- The whole-volume `AEStronglyMeasurable` predicates required by
  -- `poincareWirtinger` come from `LocallyIntegrable.aestronglyMeasurable`.
  have hf_rep_meas_full : AEStronglyMeasurable hf_rep.rep
      (volume : Measure (Fin d → ℝ)) :=
    hf_rep_loc.aestronglyMeasurable
  have hg_rep_meas_full : ∀ i, AEStronglyMeasurable ((hg_rep i).rep)
      (volume : Measure (Fin d → ℝ)) :=
    fun i => (hg_rep_loc i).aestronglyMeasurable
  have hrep :=
    poincareWirtinger (d := d) (p := p) hp hp_top
      hf_rep_meas_full
      hf_rep.periodic
      hf_rep_loc
      hf_rep_sob
      hg_rep_weak
      hg_rep_meas_full
      (fun i => (hg_rep i).periodic)
      hg_rep_loc
      hg_rep_lp
  -- Step 6: identify the mean of the representative with that of `f`.
  have hmean : periodicMean (d := d) hf_rep.rep = periodicMean (d := d) f :=
    periodicMean_congr_ae_unitCube hf_rep.ae_eq
  -- Step 7: identify the LHS norms via `lpNormPer_congr_ae_unitCube`.
  have hleft :
      lpNormPer (d := d) p
          (hf_rep.rep - fun _ : Fin d → ℝ => periodicMean (d := d) hf_rep.rep)
      = lpNormPer (d := d) p
          (f - fun _ : Fin d → ℝ => periodicMean (d := d) f) := by
    apply lpNormPer_congr_ae_unitCube
    filter_upwards [hf_rep.ae_eq] with x hx
    simp [hx, hmean]
  -- Step 8: identify the RHS sums coordinate-wise.
  have hright :
      (∑ i : Fin d, lpNormPer (d := d) p ((hg_rep i).rep))
      = (∑ i : Fin d, lpNormPer (d := d) p (g i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact lpNormPer_congr_ae_unitCube ((hg_rep i).ae_eq)
  -- Conclude.
  rw [← hleft, ← hright]
  exact hrep

end AEPeriodicPoincare

end Periodic
end StationaryMFG
