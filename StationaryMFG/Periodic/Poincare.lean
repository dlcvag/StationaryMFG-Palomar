module

public import StationaryMFG.Periodic.Sobolev

@[expose] public section

/-!
# Periodic Poincaré–Wirtinger inequality: foundational layer

Per `docs/CONVENTIONS.md` §1, integration on the torus is realised by
restricting Lebesgue measure to the unit cube. This file introduces the
**mean** of a periodic function over the unit cube,

```
periodicMean f := periodicIntegral f
```

and records the basic algebraic lemmas (constants, additivity, scalar
homogeneity) that Phase 1 dependents need. Together with the density of
`SmoothPeriodic` in `W^{1,p}_per` (proved in `Periodic/Sobolev.lean`),
these are the foundation on which the Poincaré–Wirtinger inequality

```
lpNormPer p (f − periodicMean f) ≤ C(d, p) * Σ_i lpNormPer p (g i)
```

is built. The actual inequality is delivered by the child tasks
`infra:P1-poincare-1d`, `infra:P1-poincare-fubini`, and
`infra:P1-poincare-density` (see backlog); this module is the splice
point on which they hang.

The split mirrors the strategy outlined in `docs/REFERENCES.md`:
the periodic case is *easier* than the whole-space / ball cases handled
in `DeGiorgi/Poincare.lean` and `DeGiorgi/SobolevPoincare.lean`, but the
chain of FTC + Fubini + density is still substantial enough to deserve
its own pipeline of tasks.
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ### Mean of a periodic function over the unit cube -/

/-- The mean value of `f : (Fin d → ℝ) → ℝ` over the torus. By the
unit-cube identification of the torus, this is just `periodicIntegral f`
(the cube has volume `1`, so the integral coincides with the mean). -/
noncomputable def periodicMean (f : (Fin d → ℝ) → ℝ) : ℝ :=
  periodicIntegral f

/-- The mean of the zero function is zero. -/
@[simp] lemma periodicMean_zero :
    periodicMean (d := d) (fun _ : (Fin d → ℝ) => (0 : ℝ)) = 0 := by
  unfold periodicMean
  exact periodicIntegral_zero

/-- The mean of a constant function on the torus is the constant itself,
because the unit cube has Lebesgue volume `1`. -/
@[simp] lemma periodicMean_const (c : ℝ) :
    periodicMean (d := d) (fun _ : (Fin d → ℝ) => c) = c := by
  unfold periodicMean
  exact periodicIntegral_const c

/-- Additivity of the mean for integrable functions on the unit cube. -/
lemma periodicMean_add {f g : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f (UnitCube d))
    (hg : IntegrableOn g (UnitCube d)) :
    periodicMean (f + g) = periodicMean f + periodicMean g := by
  unfold periodicMean
  exact periodicIntegral_add hf hg

/-- Scalar homogeneity of the mean. -/
lemma periodicMean_smul (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    periodicMean (fun x => c • f x) = c • periodicMean f := by
  unfold periodicMean
  exact periodicIntegral_smul (𝕜 := ℝ) c f

/-! ### Subtracting the mean

`f - periodicMean f` is the natural object on the LHS of the
Poincaré–Wirtinger inequality. We record that the mean of the
mean-subtracted function vanishes (when `f` is integrable on the unit
cube), which is the standard normalisation used throughout Phase 1.
-/

/-- The mean of `f − ⨏ f` vanishes for any function integrable on the
unit cube. -/
lemma periodicMean_sub_periodicMean {f : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f (UnitCube d)) :
    periodicMean (fun x => f x - periodicMean f) = 0 := by
  -- Rewrite the integrand as `f + (- periodicMean f)`; both summands are
  -- integrable on the unit cube (the second is constant), so apply
  -- additivity and the constant-mean lemma.
  have hconst :
      IntegrableOn (fun _ : Fin d → ℝ => -periodicMean f) (UnitCube d) := by
    have hvol : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by
      rw [volume_unitCube]; exact ENNReal.one_ne_top
    exact integrableOn_const hvol
  have hsplit :
      (fun x : Fin d → ℝ => f x - periodicMean f) =
        f + (fun _ : Fin d → ℝ => -periodicMean f) := by
    funext x; simp [sub_eq_add_neg]
  rw [hsplit, periodicMean_add hf hconst]
  -- The mean of the constant `−periodicMean f` is `−periodicMean f`.
  have hc : periodicMean (d := d)
      (fun _ : (Fin d → ℝ) => -periodicMean f) = -periodicMean f :=
    periodicMean_const (-periodicMean f)
  rw [hc]; ring

/-! ### Sample example

A constant function has zero deviation from its mean. -/

example (c : ℝ) :
    (fun _ : (Fin d → ℝ) => c) -
        (fun _ : (Fin d → ℝ) =>
          periodicMean (d := d) (fun _ : (Fin d → ℝ) => c)) =
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  funext x
  simp [periodicMean_const]

/-! ### One-dimensional Wirtinger inequality on `[0,1]`

For a `C¹` function `g : ℝ → ℝ`, every pair of points in `[0,1]`
satisfies `|g x − g y| ≤ ∫₀¹ |g'(t)| dt`, by the fundamental theorem of
calculus. Integrating in `y` yields the mean-subtracted bound
`|g x − ⟨g⟩₀¹| ≤ ∫₀¹ |g'(t)| dt`. This is the building block for the
`d`-dimensional periodic Poincaré–Wirtinger inequality
(`infra:P1-poincare-fubini`).

Although the task is phrased for periodic functions, the bound itself
only uses `g` restricted to `[0,1]`; periodicity is not actually
required for the pointwise statement, and we therefore state these
lemmas for general `C¹` functions on `ℝ`. -/

open intervalIntegral

/-- One-sided Wirtinger inequality: for any `C¹` function `g : ℝ → ℝ`
and any two points `x, y ∈ [0,1]`,
`|g x − g y| ≤ ∫₀¹ |g'(t)| dt`. -/
theorem wirtinger1D_pointwise_diff
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |g x - g y| ≤ ∫ t in (0 : ℝ)..1, |deriv g t| := by
  -- Differentiability and continuity facts.
  have hgd : Differentiable ℝ g := hg.differentiable_one
  have hgc : Continuous (deriv g) := hg.continuous_deriv_one
  have habs_c : Continuous (fun t => |deriv g t|) := hgc.abs
  -- FTC: g x − g y = ∫_y^x deriv g t.
  have hFTC : g x - g y = ∫ t in y..x, deriv g t := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := y) (b := x) (f := g) (f' := deriv g)
      (hderiv := fun t _ => (hgd t).hasDerivAt)
      (hint := (hgc.intervalIntegrable y x))
    linarith [this]
  -- Bound the absolute value of the FTC integral by the integral of the absolute value
  -- over `Ι y x`, then enlarge the domain to `Ι 0 1 = Ioc 0 1`.
  have h1 : |∫ t in y..x, deriv g t| ≤ ∫ t in Set.Ioc (min y x) (max y x), |deriv g t| := by
    have := intervalIntegral.norm_integral_le_integral_norm_uIoc
      (a := y) (b := x) (μ := MeasureTheory.volume) (f := deriv g)
    -- `Ι y x = Set.Ioc (min y x) (max y x)`
    simpa [Real.norm_eq_abs, Set.uIoc] using this
  -- `Ioc (min y x) (max y x) ⊆ Ioc 0 1`.
  have hsub : Set.Ioc (min y x) (max y x) ⊆ Set.Ioc (0 : ℝ) 1 := by
    apply Set.Ioc_subset_Ioc
    · exact le_min hy.1 hx.1
    · exact max_le hy.2 hx.2
  have habs_int_on : MeasureTheory.IntegrableOn
      (fun t => |deriv g t|) (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume := by
    have : IntervalIntegrable (fun t => |deriv g t|) MeasureTheory.volume (0 : ℝ) 1 :=
      habs_c.intervalIntegrable 0 1
    simpa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using this
  have h2 : ∫ t in Set.Ioc (min y x) (max y x), |deriv g t| ≤
      ∫ t in Set.Ioc (0 : ℝ) 1, |deriv g t| := by
    refine MeasureTheory.setIntegral_mono_set habs_int_on ?_ hsub.eventuallyLE
    exact MeasureTheory.ae_of_all _ (fun t => abs_nonneg _)
  -- Convert `∫ t in Ioc 0 1, …` to `∫ t in (0:ℝ)..1, …`.
  have h3 : (∫ t in Set.Ioc (0 : ℝ) 1, |deriv g t|) = ∫ t in (0 : ℝ)..1, |deriv g t| := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc |g x - g y|
      = |∫ t in y..x, deriv g t| := by rw [hFTC]
    _ ≤ ∫ t in Set.Ioc (min y x) (max y x), |deriv g t| := h1
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) 1, |deriv g t| := h2
    _ = ∫ t in (0 : ℝ)..1, |deriv g t| := h3

/-- Mean-subtracted 1D Wirtinger inequality on `[0,1]`. For a `C¹`
function `g : ℝ → ℝ` and any `x ∈ [0,1]`,

`|g x − ∫₀¹ g y dy| ≤ ∫₀¹ |g'(t)| dt`.

This is the pointwise Poincaré–Wirtinger bound used as the 1D base
case in the proof of the `d`-dimensional periodic inequality. -/
theorem wirtinger1D_smooth
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |g x - ∫ y in (0 : ℝ)..1, g y| ≤ ∫ t in (0 : ℝ)..1, |deriv g t| := by
  -- Continuity / integrability facts for `g` and `|g'|` on `[0,1]`.
  have hgc : Continuous g := hg.continuous
  have hg_int : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) 1 :=
    hgc.intervalIntegrable 0 1
  have habs_c : Continuous (fun t => |deriv g t|) :=
    (hg.continuous_deriv_one).abs
  have habs_int : IntervalIntegrable (fun t => |deriv g t|)
      MeasureTheory.volume (0 : ℝ) 1 :=
    habs_c.intervalIntegrable 0 1
  -- Step 1: `g x − ∫₀¹ g = ∫₀¹ (g x − g y) dy` since the unit interval has length 1.
  have hconst_int :
      (∫ _ in (0 : ℝ)..1, (g x : ℝ)) = g x := by
    simp [intervalIntegral.integral_const]
  have hdiff_eq :
      g x - (∫ y in (0 : ℝ)..1, g y) = ∫ y in (0 : ℝ)..1, (g x - g y) := by
    have := intervalIntegral.integral_sub
      (a := 0) (b := 1) (μ := MeasureTheory.volume)
      (f := fun _ => g x) (g := g)
      (intervalIntegrable_const) hg_int
    -- `this : ∫ y in 0..1, (g x − g y) = (∫ y in 0..1, g x) − (∫ y in 0..1, g y)`
    rw [this, hconst_int]
  -- Step 2: bound the absolute value of the integral by the integral of the absolute
  -- value over `[0,1]`, then apply the pointwise lemma.
  have hpt : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |g x - g y| ≤ ∫ t in (0 : ℝ)..1, |deriv g t| := by
    intro y hy
    exact wirtinger1D_pointwise_diff hg hx hy
  -- Use `abs_integral_le_integral_abs` followed by an `intervalIntegral.integral_mono`.
  have h_abs_le :
      |∫ y in (0 : ℝ)..1, (g x - g y)| ≤ ∫ y in (0 : ℝ)..1, |g x - g y| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)
  -- Bound `∫ y, |g x − g y|` by the constant `∫ t, |g'(t)|`.
  have h_diff_int : IntervalIntegrable (fun y => g x - g y)
      MeasureTheory.volume (0 : ℝ) 1 := intervalIntegrable_const.sub hg_int
  have h_abs_diff_int : IntervalIntegrable (fun y => |g x - g y|)
      MeasureTheory.volume (0 : ℝ) 1 := by
    exact (continuous_const.sub hgc).abs.intervalIntegrable 0 1
  have h_const_bound_int : IntervalIntegrable
      (fun _ : ℝ => ∫ t in (0 : ℝ)..1, |deriv g t|)
      MeasureTheory.volume (0 : ℝ) 1 := intervalIntegrable_const
  have h_mono :
      (∫ y in (0 : ℝ)..1, |g x - g y|) ≤
        ∫ _ in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, |deriv g t| := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      h_abs_diff_int h_const_bound_int ?_
    intro y hy; exact hpt y hy
  have h_const_eval :
      (∫ _ in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, |deriv g t|) =
        ∫ t in (0 : ℝ)..1, |deriv g t| := by
    simp [intervalIntegral.integral_const]
  calc |g x - ∫ y in (0 : ℝ)..1, g y|
      = |∫ y in (0 : ℝ)..1, (g x - g y)| := by rw [hdiff_eq]
    _ ≤ ∫ y in (0 : ℝ)..1, |g x - g y| := h_abs_le
    _ ≤ ∫ _ in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, |deriv g t| := h_mono
    _ = ∫ t in (0 : ℝ)..1, |deriv g t| := h_const_eval

/-- Sanity-check `example`: a constant function `g = fun _ ↦ c` satisfies
the 1D Wirtinger bound trivially (both sides vanish). -/
example (c : ℝ) :
    |(fun _ : ℝ => c) (0 : ℝ) - ∫ y in (0 : ℝ)..1, (fun _ : ℝ => c) y|
        ≤ ∫ t in (0 : ℝ)..1, |deriv (fun _ : ℝ => c) t| :=
  wirtinger1D_smooth (g := fun _ : ℝ => c) (contDiff_const) (x := 0)
    (by simp [Set.mem_Icc])

/-! ### One-axis Wirtinger inequality on a smooth periodic function

The next lemma is the building block for the Fubini iteration that
proves the `d`-dimensional Wirtinger inequality on the torus
(`infra:P1-poincare-fubini-mean` in the backlog). It specialises the 1D
pointwise lemma `wirtinger1D_pointwise_diff` to the slice
`t ↦ φ(Function.update x i t)` of a smooth periodic function. -/

open Function in
/-- One-axis pointwise Wirtinger inequality for a smooth periodic function.
For `φ : SmoothPeriodic d`, base point `x : Fin d → ℝ`, axis `i : Fin d`,
and `s, t ∈ [0, 1]`,

`|φ(update x i t) − φ(update x i s)| ≤ ∫₀¹ |∂_i φ (update x i τ)| dτ`.

This is the slice version of the 1D Wirtinger inequality
`wirtinger1D_pointwise_diff`, with the partial derivative
`SmoothPeriodic.partialDeriv i φ` playing the role of `g'`. -/
theorem wirtinger1D_axis_smoothPeriodic
    (φ : SmoothPeriodic d) (x : Fin d → ℝ) (i : Fin d)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(φ : (Fin d → ℝ) → ℝ) (Function.update x i t)
        - (φ : (Fin d → ℝ) → ℝ) (Function.update x i s)|
      ≤ ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (Function.update x i τ)| := by
  -- Slice function and its `C¹` regularity.
  set sl : ℝ → ℝ :=
    fun τ => (φ : (Fin d → ℝ) → ℝ) (Function.update x i τ) with hsl
  -- Smoothness of `φ` as a function on `Fin d → ℝ`.
  have hφ_C1 : ContDiff ℝ 1 (φ : (Fin d → ℝ) → ℝ) :=
    φ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hφ_diff : Differentiable ℝ (φ : (Fin d → ℝ) → ℝ) := hφ_C1.differentiable_one
  -- Update map and its derivative.
  have hupd_hasDeriv : ∀ τ : ℝ,
      HasDerivAt (Function.update x i) (Pi.single i (1 : ℝ)) τ :=
    fun τ => hasDerivAt_update x i τ
  -- Composition gives a `HasDerivAt` for `sl` at every `τ`.
  have hsl_hasDeriv : ∀ τ : ℝ,
      HasDerivAt sl
        (fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (Function.update x i τ)
            (Pi.single i (1 : ℝ))) τ := by
    intro τ
    have hf : HasFDerivAt (φ : (Fin d → ℝ) → ℝ)
        (fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (Function.update x i τ))
        (Function.update x i τ) :=
      (hφ_diff (Function.update x i τ)).hasFDerivAt
    exact hf.comp_hasDerivAt τ (hupd_hasDeriv τ)
  -- Identify `Pi.single i 1` with `Pi.basisFun ℝ (Fin d) i`.
  have hbasis : (Pi.single i (1 : ℝ) : Fin d → ℝ) = Pi.basisFun ℝ (Fin d) i := by
    classical
    simp
  -- Therefore `deriv sl τ = (partialDeriv i φ) (update x i τ)`.
  have hderiv_sl : ∀ τ : ℝ,
      deriv sl τ =
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (Function.update x i τ) := by
    intro τ
    have h := (hsl_hasDeriv τ).deriv
    -- Convert basis description.
    rw [hbasis] at h
    simp [SmoothPeriodic.coe_partialDeriv, h]
  -- `sl` is `C¹` since each composition is `C¹`.
  have hsl_C1 : ContDiff ℝ 1 sl := by
    have hupd_C1 : ContDiff ℝ 1 (fun τ : ℝ => Function.update x i τ) := by
      -- The update map equals an affine map: `τ ↦ x + (τ − x i) • e_i`. We
      -- prove smoothness componentwise using `contDiff_pi`.
      refine contDiff_pi.mpr ?_
      intro j
      classical
      by_cases hij : j = i
      · subst hij
        -- `(update x j τ) j = τ` (with `j = i`), which is the identity.
        have : (fun τ : ℝ => (Function.update x j τ) j) = id := by
          funext τ; simp
        rw [this]
        exact (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ))
      · -- `(update x i τ) j = x j` is constant in `τ`.
        have : (fun τ : ℝ => (Function.update x i τ) j) = (fun _ => x j) := by
          funext τ; simp [Function.update, hij]
        simpa [this] using (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x j))
    exact hφ_C1.comp hupd_C1
  -- Apply the 1D pointwise Wirtinger inequality to `sl` at points `t` and `s`.
  have hpt :
      |sl t - sl s| ≤ ∫ τ in (0 : ℝ)..1, |deriv sl τ| :=
    wirtinger1D_pointwise_diff (g := sl) hsl_C1 ht hs
  -- Rewrite `deriv sl τ = partialDeriv i φ (update x i τ)` inside the integrand.
  have hcong : (fun τ : ℝ => |deriv sl τ|) =
      (fun τ : ℝ => |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) (Function.update x i τ)|) := by
    funext τ; rw [hderiv_sl τ]
  -- Conclude.
  calc |sl t - sl s|
      ≤ ∫ τ in (0 : ℝ)..1, |deriv sl τ| := hpt
    _ = ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (Function.update x i τ)| := by
            rw [hcong]

/-- Sanity-check `example`: for the constant smooth-periodic function the
slice Wirtinger bound is trivial (both sides vanish). -/
example (c : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    |((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
          (Function.update x i 0)
        - ((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
          (Function.update x i 0)|
      ≤ ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
              SmoothPeriodic d) : (Fin d → ℝ) → ℝ) (Function.update x i τ)| :=
  wirtinger1D_axis_smoothPeriodic (SmoothPeriodic.const c) x i
    (by simp [Set.mem_Icc]) (by simp [Set.mem_Icc])

/-! ### Pointwise telescoping bound for smooth periodic functions

We deduce a pointwise bound on `|φ(x) − periodicMean φ|` by telescoping
along coordinate axes and using `wirtinger1D_axis_smoothPeriodic` at
each step.

**Note on the formulation.** The natural-looking pointwise bound
`|φ(x) − periodicMean φ| ≤ ∑ i, ∫_{[0,1]^d} |∂_i φ y| dy` (an `L^1`
bound on the right) is in fact **false** for `d ≥ 2`: take
`φ(x_1, x_2) = ψ_1(x_1)·ψ_2(x_2)` with each `ψ_j` a normalized narrow
bump of height `M ≫ 1` and zero mean — then the LHS scales like `M^2`
while `∑_i ∫|∂_i φ|` scales like `M`. The integrated version
(`∫_x |φ(x) − ⟨φ⟩| ≤ ∑_i ∫|∂_i φ|`) is the correct one and lives in the
`L^p` Poincaré–Wirtinger task downstream.

What the telescoping argument *does* yield pointwise is a bound by a
uniform `L^∞` bound on the partial derivatives:

```
|φ(x) − periodicMean φ| ≤ d · C
  whenever  ∀ i z, |partialDeriv i φ z| ≤ C.
```

This is what we deliver here. -/

open Function

/-- Telescoping path between two points `x, y : Fin d → ℝ`. At
"step" `k : ℕ`, the path takes the first `k` coordinates from `y` and
the remaining `d − k` coordinates from `x`. So `pathPoint x y 0 = x` and
`pathPoint x y d = y`; consecutive steps differ in exactly one
coordinate. -/
def pathPoint (x y : Fin d → ℝ) (k : ℕ) : Fin d → ℝ :=
  fun j => if (j : ℕ) < k then y j else x j

/-- The path starts at `x`: when `k = 0`, no coordinate has been
swapped. -/
@[simp] lemma pathPoint_zero (x y : Fin d → ℝ) :
    pathPoint x y 0 = x := by
  funext j
  simp [pathPoint]

/-- The path ends at `y`: when `k = d`, every coordinate `j : Fin d`
satisfies `(j : ℕ) < d`. -/
@[simp] lemma pathPoint_card (x y : Fin d → ℝ) :
    pathPoint x y d = y := by
  funext j
  simp [pathPoint, j.isLt]

/-- Step relation: increasing `k` to `k + 1` (with `k < d`) swaps
exactly the coordinate at position `k` from `x k` to `y k`. -/
lemma pathPoint_succ {x y : Fin d → ℝ} {k : ℕ} (hk : k < d) :
    pathPoint x y (k + 1) =
      Function.update (pathPoint x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  funext j
  by_cases hjk : j = (⟨k, hk⟩ : Fin d)
  · subst hjk
    simp [pathPoint]
  · -- `j ≠ ⟨k, hk⟩`, so the `update` does nothing at `j`.
    have hjne : (j : ℕ) ≠ k := by
      intro h
      apply hjk
      ext
      exact h
    -- At `j ≠ k` (as ℕ), `j < k + 1 ↔ j < k` (since `j ≠ k`).
    have hiff : ((j : ℕ) < k + 1) ↔ ((j : ℕ) < k) := by
      constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
        · exact hlt
        · exact (hjne heq).elim
      · intro h
        exact Nat.lt_succ_of_lt h
    simp [pathPoint, Function.update_of_ne hjk, hiff]

/-- Membership: if `x, y ∈ UnitCube d`, every path point also lies in
`UnitCube d`. -/
lemma pathPoint_mem_unitCube {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d) (k : ℕ) :
    pathPoint x y k ∈ UnitCube d := by
  rw [mem_unitCube_iff] at hx hy ⊢
  intro j
  by_cases hj : (j : ℕ) < k
  · have : pathPoint x y k j = y j := by simp [pathPoint, hj]
    rw [this]; exact hy j
  · have : pathPoint x y k j = x j := by simp [pathPoint, hj]
    rw [this]; exact hx j

/-- One-step bound from the slice Wirtinger inequality: if `|∂_i φ| ≤ C`
everywhere, then the `i`-th telescoping step contributes at most `C` to
the running difference. Here `i = ⟨k, hk⟩` for `k < d`. -/
lemma pointwise_step_bound {C : ℝ} (φ : SmoothPeriodic d)
    (hC : ∀ i : Fin d, ∀ z : Fin d → ℝ,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z| ≤ C)
    {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d)
    {k : ℕ} (hk : k < d) :
    |(φ : (Fin d → ℝ) → ℝ) (pathPoint x y (k + 1))
        - (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k)| ≤ C := by
  -- Identify both endpoints with `update`s of `pathPoint x y k`.
  set i : Fin d := ⟨k, hk⟩ with hidef
  set z : Fin d → ℝ := pathPoint x y k with hzdef
  -- `pathPoint x y (k+1) = update z i (y i)`.
  have hsucc : pathPoint x y (k + 1) = Function.update z i (y i) :=
    pathPoint_succ hk
  -- `pathPoint x y k = update z i (x i)` since `(i : ℕ) = k` is not `< k`.
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
  -- Membership of `x i, y i` in `[0,1]` (via membership in `UnitCube d`).
  have hxmem : x i ∈ Set.Icc (0 : ℝ) 1 := by
    have := (mem_unitCube_iff.mp hx) i
    exact ⟨this.1, le_of_lt this.2⟩
  have hymem : y i ∈ Set.Icc (0 : ℝ) 1 := by
    have := (mem_unitCube_iff.mp hy) i
    exact ⟨this.1, le_of_lt this.2⟩
  -- Apply `wirtinger1D_axis_smoothPeriodic` to bound the slice difference.
  have hslice :
      |(φ : (Fin d → ℝ) → ℝ) (Function.update z i (y i))
          - (φ : (Fin d → ℝ) → ℝ) (Function.update z i (x i))|
        ≤ ∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) (Function.update z i τ)| :=
    wirtinger1D_axis_smoothPeriodic φ z i hxmem hymem
  -- Bound the slice integral by `C` using the uniform L∞ bound.
  have hbnd_C : (∫ τ in (0 : ℝ)..1,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (Function.update z i τ)|) ≤ C := by
    have hcont : Continuous (fun τ : ℝ =>
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (Function.update z i τ)|) := by
      have hφc : Continuous ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) :=
        ((SmoothPeriodic.partialDeriv i φ).smooth).continuous
      have hupd : Continuous (fun τ : ℝ => Function.update z i τ) := by
        refine continuous_pi (fun j => ?_)
        classical
        by_cases hji : j = i
        · have hrew : (fun τ : ℝ => (Function.update z i τ) j) = (fun τ : ℝ => τ) := by
            funext τ; rw [hji]; simp
          rw [hrew]; exact continuous_id
        · have hrew : (fun τ : ℝ => (Function.update z i τ) j) = (fun _ => z j) := by
            funext τ; simp [Function.update, hji]
          rw [hrew]; exact continuous_const
      exact (hφc.comp hupd).abs
    have hII : IntervalIntegrable
        (fun τ : ℝ =>
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) (Function.update z i τ)|)
        MeasureTheory.volume (0 : ℝ) 1 :=
      hcont.intervalIntegrable 0 1
    have hII_const : IntervalIntegrable (fun _ : ℝ => C)
        MeasureTheory.volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) (Function.update z i τ)| ≤ C := by
      intro τ _
      exact hC i (Function.update z i τ)
    have hmono :
        (∫ τ in (0 : ℝ)..1,
            |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) (Function.update z i τ)|)
          ≤ ∫ _ in (0 : ℝ)..1, C :=
      intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        hII hII_const hpt
    have heval : (∫ _ in (0 : ℝ)..1, (C : ℝ)) = C := by
      simp [intervalIntegral.integral_const]
    linarith [hmono, heval.le, heval.ge]
  -- Re-express LHS and chain. Rewrite both endpoints in terms of `update`s.
  have hkrew : (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k)
      = (φ : (Fin d → ℝ) → ℝ) (Function.update z i (x i)) := by
    rw [show pathPoint x y k = Function.update z i (x i) from hzeq]
  have hk1rew : (φ : (Fin d → ℝ) → ℝ) (pathPoint x y (k + 1))
      = (φ : (Fin d → ℝ) → ℝ) (Function.update z i (y i)) := by
    rw [hsucc]
  calc |(φ : (Fin d → ℝ) → ℝ) (pathPoint x y (k + 1))
          - (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k)|
      = |(φ : (Fin d → ℝ) → ℝ) (Function.update z i (y i))
          - (φ : (Fin d → ℝ) → ℝ) (Function.update z i (x i))| := by
            rw [hkrew, hk1rew]
    _ ≤ ∫ τ in (0 : ℝ)..1,
          |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (Function.update z i τ)| := hslice
    _ ≤ C := hbnd_C

/-- Pointwise bound `|φ x − φ y| ≤ d · C` for `x, y ∈ UnitCube d`,
where `C` is any uniform `L^∞` bound on the partial derivatives of `φ`.
Proof by telescoping along coordinate axes. -/
lemma pointwise_diff_smoothPeriodic_le {C : ℝ} (φ : SmoothPeriodic d)
    (hC : ∀ i : Fin d, ∀ z : Fin d → ℝ,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z| ≤ C)
    {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : y ∈ UnitCube d) :
    |(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y| ≤ (d : ℝ) * C := by
  -- Telescope `φ(y) − φ(x) = ∑_{k < d} (φ(p (k+1)) − φ(p k))`.
  set f : ℕ → ℝ := fun k => (φ : (Fin d → ℝ) → ℝ) (pathPoint x y k) with hf
  have htel : ∀ m : ℕ, f m - f 0 =
      ∑ k ∈ Finset.range m, (f (k + 1) - f k) := by
    intro m
    induction m with
    | zero => simp
    | succ p ihp =>
      rw [Finset.sum_range_succ, ← ihp]; ring
  have hsum :
      f d - f 0 = ∑ k ∈ Finset.range d, (f (k + 1) - f k) := htel d
  have hfd : f d = (φ : (Fin d → ℝ) → ℝ) y := by
    simp [hf, pathPoint_card]
  have hf0 : f 0 = (φ : (Fin d → ℝ) → ℝ) x := by
    simp [hf, pathPoint_zero]
  -- Replace the LHS difference with the telescoping sum.
  have htele :
      (φ : (Fin d → ℝ) → ℝ) y - (φ : (Fin d → ℝ) → ℝ) x =
        ∑ k ∈ Finset.range d, (f (k + 1) - f k) := by
    rw [← hfd, ← hf0]; exact hsum
  -- Bound each summand by `C`.
  have hkbnd : ∀ k ∈ Finset.range d, |f (k + 1) - f k| ≤ C := by
    intro k hk
    have hkd : k < d := Finset.mem_range.mp hk
    have := pointwise_step_bound (C := C) φ hC hx hy hkd
    simpa [hf] using this
  -- Triangle inequality + uniform bound `C` summed `d` times.
  have htri : |∑ k ∈ Finset.range d, (f (k + 1) - f k)|
        ≤ ∑ k ∈ Finset.range d, |f (k + 1) - f k| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbnd : (∑ k ∈ Finset.range d, |f (k + 1) - f k|) ≤
        ∑ _k ∈ Finset.range d, C :=
    Finset.sum_le_sum hkbnd
  have hconst : (∑ _k ∈ Finset.range d, (C : ℝ)) = (d : ℝ) * C := by
    rw [Finset.sum_const, Finset.card_range]
    simp [mul_comm]
  -- Convert `|φ x − φ y|` to `|φ y − φ x|`.
  have habs : |(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y|
        = |(φ : (Fin d → ℝ) → ℝ) y - (φ : (Fin d → ℝ) → ℝ) x| := by
    rw [abs_sub_comm]
  rw [habs, htele]
  calc |∑ k ∈ Finset.range d, (f (k + 1) - f k)|
      ≤ ∑ k ∈ Finset.range d, |f (k + 1) - f k| := htri
    _ ≤ ∑ _k ∈ Finset.range d, C := hbnd
    _ = (d : ℝ) * C := hconst

/-- **Pointwise telescoping Poincaré–Wirtinger bound** for a smooth
periodic function. If `|∂_i φ| ≤ C` everywhere on `ℝ^d` for every axis
`i`, then for every `x ∈ UnitCube d`,

```
|φ(x) − periodicMean φ| ≤ d · C.
```

The argument is the standard telescope-along-coordinate-axes: write
`periodicMean φ = ∫_y φ(y) dy` and `φ(x) = ∫_y φ(x) dy` (the unit cube
has volume `1`), so `φ(x) − periodicMean φ = ∫_y (φ(x) − φ(y)) dy`;
each pointwise difference is bounded by `d · C` by
`pointwise_diff_smoothPeriodic_le`; integrating against the unit cube
preserves the bound. -/
theorem pointwise_wirtinger_smoothPeriodic {C : ℝ} (φ : SmoothPeriodic d)
    (hC : ∀ i : Fin d, ∀ z : Fin d → ℝ,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z| ≤ C)
    {x : Fin d → ℝ} (hx : x ∈ UnitCube d) :
    |(φ : (Fin d → ℝ) → ℝ) x - periodicMean (φ : (Fin d → ℝ) → ℝ)|
      ≤ (d : ℝ) * C := by
  -- Continuity / integrability of `φ` on the unit cube.
  have hφc : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
  have hμ_finite : (MeasureTheory.volume : Measure (Fin d → ℝ))
      (UnitCube d) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have hφ_int : IntegrableOn ((φ : (Fin d → ℝ) → ℝ)) (UnitCube d) := by
    -- Boundedness on the unit cube via compactness of [0,1]^d.
    have hcompact :
        IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : UnitCube d ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro y hy i _
      have := (mem_unitCube_iff.mp hy) i
      exact ⟨this.1, le_of_lt this.2⟩
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image hφc.norm.continuousOn
    refine Measure.integrableOn_of_bounded hμ_finite hφc.aestronglyMeasurable
      (M := M) ?_
    refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
    refine MeasureTheory.ae_of_all _ (fun y hy => ?_)
    exact hM (Set.mem_image_of_mem _ (hsub hy))
  -- Express `φ(x) − periodicMean φ = ∫_y (φ(x) − φ(y)) dy` using vol(cube)=1.
  have hvol : (∫ _ in UnitCube d, (φ : (Fin d → ℝ) → ℝ) x) =
      (φ : (Fin d → ℝ) → ℝ) x := by
    rw [setIntegral_const, measureReal_def, volume_unitCube]
    simp
  have hpm_eq :
      (φ : (Fin d → ℝ) → ℝ) x - periodicMean (φ : (Fin d → ℝ) → ℝ) =
        ∫ y in UnitCube d,
          ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y) := by
    have hcint : Integrable
        (fun _ : Fin d → ℝ => (φ : (Fin d → ℝ) → ℝ) x)
        (volume.restrict (UnitCube d)) := integrableOn_const hμ_finite
    have hφint' : Integrable ((φ : (Fin d → ℝ) → ℝ))
        (volume.restrict (UnitCube d)) := hφ_int
    have hsub :
        (∫ y in UnitCube d,
            ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y)) =
          (∫ _ in UnitCube d, (φ : (Fin d → ℝ) → ℝ) x) -
            ∫ y in UnitCube d, (φ : (Fin d → ℝ) → ℝ) y :=
      MeasureTheory.integral_sub hcint hφint'
    rw [hsub, hvol]
    rfl
  -- Bound the integrand pointwise on the cube.
  have hpt : ∀ y ∈ UnitCube d,
      ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ ≤ (d : ℝ) * C := by
    intro y hy
    have := pointwise_diff_smoothPeriodic_le (C := C) φ hC hx hy
    simpa [Real.norm_eq_abs] using this
  -- AEStronglyMeasurable hypothesis for the difference.
  have hdiff_int : IntegrableOn
      (fun y : Fin d → ℝ =>
          (φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y)
      (UnitCube d) := by
    have hconst_int :
        IntegrableOn (fun _ : Fin d → ℝ => (φ : (Fin d → ℝ) → ℝ) x)
          (UnitCube d) := integrableOn_const hμ_finite
    exact hconst_int.sub hφ_int
  -- Now bound `|∫|` by `∫ ‖…‖ ≤ ∫ d·C = d·C`.
  have hbnd_int :
      ‖∫ y in UnitCube d,
          ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y)‖
        ≤ (d : ℝ) * C := by
    have h1 :
        ‖∫ y in UnitCube d,
            ((φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y)‖
          ≤ ∫ y in UnitCube d,
              ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖ := by
      exact norm_integral_le_integral_norm _
    have h2 :
        (∫ y in UnitCube d,
            ‖(φ : (Fin d → ℝ) → ℝ) x - (φ : (Fin d → ℝ) → ℝ) y‖) ≤
          ∫ _y in UnitCube d, ((d : ℝ) * C) := by
      refine setIntegral_mono_on hdiff_int.norm ?_ measurableSet_unitCube hpt
      exact integrableOn_const hμ_finite
    have h3 : (∫ _y in UnitCube d, ((d : ℝ) * C)) = (d : ℝ) * C := by
      rw [setIntegral_const, measureReal_def, volume_unitCube]
      simp
    linarith [h1, h2, h3.le, h3.ge]
  rw [hpm_eq]
  simpa [Real.norm_eq_abs] using hbnd_int

/-- Sample example: for a constant smooth-periodic function `φ = const c`,
the partial derivatives vanish identically, so the bound becomes
`|c − c| ≤ d · 0`, which is `0 ≤ 0`. -/
example (c : ℝ) {x : Fin d → ℝ} (hx : x ∈ UnitCube d) :
    |((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
        - periodicMean
            ((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)|
      ≤ (d : ℝ) * 0 := by
  refine pointwise_wirtinger_smoothPeriodic (C := 0)
    (SmoothPeriodic.const c) ?_ hx
  intro i z
  -- `partialDeriv i (const c)` is the zero function: `fderiv` of a constant
  -- is `0`.
  have : ((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
        SmoothPeriodic d) : (Fin d → ℝ) → ℝ) z = 0 := by
    simp [SmoothPeriodic.coe_partialDeriv, SmoothPeriodic.coe_const]
  rw [this]; simp

/-! ### `Lᵖ` Poincaré–Wirtinger inequality on smooth periodic functions

We upgrade the pointwise bound `pointwise_wirtinger_smoothPeriodic`
(`|φ x − periodicMean φ| ≤ d · C` whenever each `|∂_i φ|` is bounded by
`C`) to an `Lᵖ` bound on the unit cube. The unit cube has Lebesgue
volume `1`, so a uniform pointwise bound by `M := d · C` directly
yields `lpNormPer p (φ − periodicMean φ) ≤ M`.

The argument routes through `MeasureTheory.eLpNorm_le_of_ae_bound`,
whose conclusion involves `μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal M`;
substituting `μ = volume.restrict (UnitCube d)` makes the measure of
the universe equal to `1`, collapsing the rpow factor.

The constant in the inequality is explicitly recorded as
`poincareWirtingerConstant d := (d : ℝ)`. -/

/-- Constant in the periodic `Lᵖ` Poincaré–Wirtinger inequality:
in dimension `d`, the constant is just `d`. -/
def poincareWirtingerConstant (d : ℕ) : ℝ := (d : ℝ)

@[simp] lemma poincareWirtingerConstant_def (d : ℕ) :
    poincareWirtingerConstant d = (d : ℝ) := rfl

/-- **Lᵖ Poincaré–Wirtinger inequality** for smooth periodic functions
on the torus, parametrised by a uniform `L^∞` bound on the partial
derivatives.

If `|∂_i φ z| ≤ C` for every axis `i` and every `z`, then for *any*
exponent `p : ℝ≥0∞`,

```
lpNormPer p (φ − periodicMean φ) ≤ poincareWirtingerConstant d · C.
```

Because `poincareWirtingerConstant d = d`, this is the customary
"`d`-dimensional" Wirtinger constant.

The bound holds without restriction on `p` (no `1 ≤ p` required):
it ultimately follows from the pointwise telescoping bound
`|φ x − periodicMean φ| ≤ d · C` on `UnitCube d`, which trivially
implies the corresponding `Lᵖ` bound when the cube has volume `1`. -/
theorem poincareWirtinger_smooth (p : ℝ≥0∞) {C : ℝ} (φ : SmoothPeriodic d)
    (hC : ∀ i : Fin d, ∀ z : Fin d → ℝ,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z| ≤ C) :
    lpNormPer p (fun x => (φ : (Fin d → ℝ) → ℝ) x
        - periodicMean (φ : (Fin d → ℝ) → ℝ)) ≤
      poincareWirtingerConstant d * C := by
  classical
  -- Abbreviate the difference and the bounding constant.
  set g : (Fin d → ℝ) → ℝ :=
    fun x => (φ : (Fin d → ℝ) → ℝ) x - periodicMean (φ : (Fin d → ℝ) → ℝ)
    with hg_def
  set M : ℝ := (d : ℝ) * C with hM_def
  -- The pointwise telescoping bound holds on the unit cube.
  have hpt_cube : ∀ x ∈ UnitCube d, ‖g x‖ ≤ M := by
    intro x hx
    have := pointwise_wirtinger_smoothPeriodic (C := C) φ hC hx
    simpa [g, hg_def, M, hM_def, Real.norm_eq_abs] using this
  -- Translate to an a.e. bound on the restricted measure.
  have hae : ∀ᵐ x ∂(MeasureTheory.Measure.restrict
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      (UnitCube d)), ‖g x‖ ≤ M := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).2 ?_
    exact MeasureTheory.ae_of_all _ hpt_cube
  -- Mathlib's bound: `eLpNorm g p μ ≤ μ univ ^ (1/p.toReal) * ENNReal.ofReal M`.
  have hbnd_e : MeasureTheory.eLpNorm g p
      (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube d))
      ≤ (MeasureTheory.Measure.restrict
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (UnitCube d)) Set.univ ^ p.toReal⁻¹
        * ENNReal.ofReal M := by
    simpa using MeasureTheory.eLpNorm_le_of_ae_bound (μ :=
        MeasureTheory.Measure.restrict
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (UnitCube d)) (p := p) (f := g) (C := M)
      (φ.smooth.continuous.sub continuous_const).aestronglyMeasurable hae
  -- The restricted measure of the universe equals the volume of the cube, which is `1`.
  have hμuniv :
      (MeasureTheory.Measure.restrict
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (UnitCube d)) Set.univ = 1 := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    rw [Set.univ_inter]
    exact volume_unitCube
  -- Therefore the rpow factor collapses to `1`.
  have hrpow :
      (MeasureTheory.Measure.restrict
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (UnitCube d)) Set.univ ^ p.toReal⁻¹ = 1 := by
    rw [hμuniv]; exact ENNReal.one_rpow _
  -- Combine: `eLpNormPer p g ≤ ENNReal.ofReal M`.
  have hbnd_e' : eLpNormPer p g ≤ ENNReal.ofReal M := by
    unfold eLpNormPer
    have := hbnd_e
    rw [hrpow, one_mul] at this
    exact this
  -- Pass to `.toReal` and finish. `M = d · C ≥ 0`: when `d > 0`, evaluating the
  -- bound `hC` at any axis-point shows `C ≥ 0`; when `d = 0`, `M = 0`.
  have hMnn : 0 ≤ M := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0; simp [hM_def]
    · have hC_nn : 0 ≤ C := (abs_nonneg _).trans
        (hC ⟨0, hdpos⟩ (fun _ => (0 : ℝ)))
      exact mul_nonneg (by exact_mod_cast Nat.zero_le _) hC_nn
  have htoReal :
      (eLpNormPer p g).toReal ≤ (ENNReal.ofReal M).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd_e'
  have hofReal : (ENNReal.ofReal M).toReal = M :=
    ENNReal.toReal_ofReal hMnn
  -- Conclude.
  have : lpNormPer p g ≤ M := by
    unfold lpNormPer
    rw [hofReal] at htoReal
    exact htoReal
  -- Rewrite `M` as `poincareWirtingerConstant d * C`.
  simpa [poincareWirtingerConstant, M, hM_def, g, hg_def] using this

/-- Sample example: for the constant smooth-periodic function `const c`,
the partial derivatives vanish, so the `Lᵖ` Wirtinger bound becomes
`lpNormPer p 0 ≤ d · 0`, both sides being `0`. -/
example (c : ℝ) (p : ℝ≥0∞) :
    lpNormPer p (fun x : Fin d → ℝ =>
        ((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
          - periodicMean
              ((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
      ≤ poincareWirtingerConstant d * 0 := by
  refine poincareWirtinger_smooth (C := 0) (p := p) (SmoothPeriodic.const c) ?_
  intro i z
  have : ((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
        SmoothPeriodic d) : (Fin d → ℝ) → ℝ) z = 0 := by
    simp [SmoothPeriodic.coe_partialDeriv, SmoothPeriodic.coe_const]
  rw [this]; simp

/-! ### Partial-mean operator on smooth periodic functions

For `f : (Fin d → ℝ) → ℝ` and `k : ℕ`, `partialMean f k` is the function
obtained by averaging `f` over its first `k` coordinates against the unit
interval `[0,1]` in each coordinate, with the remaining `d − k` coordinates
held fixed. The recursive definition unfolds one coordinate at a time.

This is the building block of the Fubini-iterated 1D Wirtinger argument
(`infra:P1-poincare-fubini-LpRHS-iteratedSlice` in the backlog), which
upgrades the pointwise telescoping bound to the `Lᵖ`-on-RHS Poincaré
inequality.

The Fubini collapse `partialMean f d = const (periodicMean f)` and the
smoothness preservation `partialMean φ k ∈ C^∞` are split off into
sibling tasks (`-card` and `-smooth`); this section provides only the
definition, the recursive unfolding, and the coordinate-independence
lemma. -/

/-- The partial-mean operator. `partialMean f k x` averages `f` over its
first `k` coordinates against `[0,1]` in each coordinate, with the
remaining `d − k` coordinates held fixed at the corresponding entries of
`x`. The recursive definition unfolds one coordinate at a time. For
`k ≥ d` the operator stops growing (the dependent-if guard fails), so
`partialMean f k = partialMean f d` whenever `k ≥ d`. -/
noncomputable def partialMean (f : (Fin d → ℝ) → ℝ) :
    ℕ → (Fin d → ℝ) → ℝ
  | 0 => f
  | k + 1 => fun x =>
      if h : k < d then
        ∫ t in (0 : ℝ)..1, partialMean f k (Function.update x ⟨k, h⟩ t)
      else
        partialMean f k x

/-- Base case: `partialMean f 0 = f`. -/
@[simp] lemma partialMean_zero (f : (Fin d → ℝ) → ℝ) :
    partialMean f 0 = f := rfl

/-- Recursive identity for `k < d`: averaging the `(k+1)`-fold partial
mean equals integrating the `k`-fold partial mean over the `k`-th
coordinate on `[0,1]`. -/
lemma partialMean_succ (f : (Fin d → ℝ) → ℝ) {k : ℕ} (hk : k < d)
    (x : Fin d → ℝ) :
    partialMean f (k + 1) x =
      ∫ t in (0 : ℝ)..1, partialMean f k (Function.update x ⟨k, hk⟩ t) := by
  change (if h : k < d then
        ∫ t in (0 : ℝ)..1, partialMean f k (Function.update x ⟨k, h⟩ t)
      else partialMean f k x) = _
  rw [dif_pos hk]

/-- Beyond-domain identity: for `k ≥ d`, the recursion is a no-op. -/
lemma partialMean_succ_of_ge (f : (Fin d → ℝ) → ℝ) {k : ℕ} (hk : ¬ k < d)
    (x : Fin d → ℝ) :
    partialMean f (k + 1) x = partialMean f k x := by
  change (if h : k < d then
        ∫ t in (0 : ℝ)..1, partialMean f k (Function.update x ⟨k, h⟩ t)
      else partialMean f k x) = _
  rw [dif_neg hk]

/-- **Coordinate-independence of the partial mean.** For `k ≤ d`, the
value of `partialMean f k x` depends only on those entries `x i` with
index `(i : ℕ) ≥ k`. Equivalently, integrating over the first `k`
coordinates erases their values from `x`. -/
lemma partialMean_indep (f : (Fin d → ℝ) → ℝ) :
    ∀ {k : ℕ}, k ≤ d → ∀ {x y : Fin d → ℝ},
      (∀ i : Fin d, k ≤ (i : ℕ) → x i = y i) →
        partialMean f k x = partialMean f k y := by
  intro k
  induction k with
  | zero =>
    intro _ x y hxy
    -- Hypothesis says `x i = y i` for all `i`, so `x = y`.
    have hxyfun : x = y := by
      funext i; exact hxy i (Nat.zero_le _)
    simp [hxyfun]
  | succ k ih =>
    intro hk1 x y hxy
    have hkd : k < d := hk1
    have hkle : k ≤ d := le_of_lt hkd
    -- Unfold the recursive identity at both `x` and `y`.
    rw [partialMean_succ f hkd x, partialMean_succ f hkd y]
    -- Reduce to pointwise equality of the integrand.
    refine intervalIntegral.integral_congr ?_
    intro t _
    -- Apply IH at level `k`. We need `update x ⟨k,hkd⟩ t` and
    -- `update y ⟨k,hkd⟩ t` to agree on indices `j` with `(j : ℕ) ≥ k`.
    refine ih hkle ?_
    intro j hjk
    by_cases hjeq : j = (⟨k, hkd⟩ : Fin d)
    · -- Index equals ⟨k, hkd⟩: both updates are `t`.
      subst hjeq
      simp
    · -- Index ≠ ⟨k, hkd⟩: update is a no-op; agreement follows from
      -- `(j : ℕ) ≥ k+1` and the original hypothesis.
      have hjnk : (j : ℕ) ≠ k := by
        intro heq; apply hjeq; ext; exact heq
      have hjk1 : k + 1 ≤ (j : ℕ) := by omega
      have hxy_j : x j = y j := hxy j hjk1
      rw [Function.update_of_ne hjeq, Function.update_of_ne hjeq, hxy_j]

/-- Sample example: `partialMean (const c) k = const c` for all `k ≤ d`,
since the partial-mean of a constant is the same constant. We illustrate
the `k = 0` case where this is definitional. -/
example (c : ℝ) (x : Fin d → ℝ) :
    partialMean (fun _ : Fin d → ℝ => c) 0 x = c := by
  simp [partialMean_zero]

/-! ### Fubini collapse: `partialMean f d = const (periodicMean f)`

After `d` iterated 1-D averages, all coordinates have been integrated
out, so `partialMean f d` is constant (by `partialMean_indep`) and equal
to the full periodic mean of `f`.

The Fubini step: for `g : (Fin d → ℝ) → ℝ` integrable on the cube,
integrating `g (update x ⟨k,h⟩ t)` over `(x, t) ∈ UnitCube d × [0,1]`
equals `∫_{UnitCube d} g`. We prove this via `MeasurableEquiv.piFinSuccAbove`,
which splits coordinate `⟨k,h⟩` off from the cube. -/

/-- Single Fubini step. For `k < d` and continuous `g`, integrating
`g(update x ⟨k,h⟩ t)` over `(x, t) ∈ UnitCube d × [0,1]` collapses to
`∫ x in UnitCube d, g x`. -/
private lemma setIntegral_intervalIntegral_update {k : ℕ} (hk : k < d)
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) :
    (∫ x in UnitCube d, ∫ t in (0 : ℝ)..1,
        g (Function.update x ⟨k, hk⟩ t)) =
      ∫ x in UnitCube d, g x := by
  classical
  -- Reduce `d = n + 1` since `k < d`.
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 :=
    ⟨d - 1, by omega⟩
  set i : Fin (n + 1) := ⟨k, hk⟩ with hidef
  -- Splitting equivalence and its measure-preservation.
  set e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i with he_def
  have hem : MeasurePreserving e (volume) ((volume).prod (volume)) := by
    have := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    convert this using 1
  have he_symm : MeasurePreserving e.symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) volume :=
    hem.symm
  -- `e.symm (s, y) = i.insertNth s y`.
  have he_symm_eq : ∀ p : ℝ × (Fin n → ℝ),
      e.symm p = i.insertNth p.1 p.2 := fun _ => rfl
  -- Pulled-back unit cube.
  have hpre :
      e.symm ⁻¹' UnitCube (n + 1) =
        Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
    ext ⟨s, y⟩
    simp only [Set.mem_preimage, mem_unitCube_iff, Set.mem_prod, Set.mem_Ico,
      Set.mem_pi, Set.mem_univ, true_imp_iff]
    rw [he_symm_eq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := h i; rw [Fin.insertNth_apply_same] at h1; exact h1
      · intro j; have hj := h (i.succAbove j); rw [Fin.insertNth_apply_succAbove] at hj
        exact hj
    · rintro ⟨hs, hy⟩
      intro j
      rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k', rfl⟩
      · subst hj; rw [Fin.insertNth_apply_same]; exact hs
      · rw [Fin.insertNth_apply_succAbove]; exact hy k'
  -- Continuity facts.
  have he_symm_cont : Continuous (e.symm : ℝ × (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
    change Continuous (fun p : ℝ × (Fin n → ℝ) => i.insertNth (α := fun _ => ℝ) p.1 p.2)
    exact Continuous.finInsertNth (A := fun _ => ℝ) i continuous_fst continuous_snd
  have hcont_g_e : Continuous (fun p : ℝ × (Fin n → ℝ) => g (e.symm p)) :=
    hg.comp he_symm_cont
  -- Compactness and integrability of `g ∘ e.symm` on the closed cube.
  have hcompact_prod :
      IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ
        Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hsub_prod :
      Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    refine ⟨Set.Ico_subset_Icc_self hs, ?_⟩
    intro j _; exact Set.Ico_subset_Icc_self (hy j (Set.mem_univ _))
  have hg_int_prod : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => g (e.symm p))
      (Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    have hLI : LocallyIntegrable (fun p : ℝ × (Fin n → ℝ) => g (e.symm p))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      hcont_g_e.locallyIntegrable
    exact (hLI.integrableOn_isCompact hcompact_prod).mono_set hsub_prod
  -- Step A: pull the RHS back via `e.symm`.
  have hRHS :
      (∫ x in UnitCube (n + 1), g x) =
        ∫ p in Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            g (e.symm p)
            ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    have himg : (UnitCube (n + 1) : Set (Fin (n + 1) → ℝ)) =
        e.symm '' (e.symm ⁻¹' UnitCube (n + 1)) :=
      (Set.image_preimage_eq _ e.symm.surjective).symm
    rw [himg, he_symm.setIntegral_image_emb e.symm.measurableEmbedding g _, hpre]
  -- Step B: convert RHS via Fubini to iterated form.
  have hg_int_restrict : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e.symm p))
      (((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1)).prod
        ((volume : Measure (Fin n → ℝ)).restrict
          (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)))) := by
    rw [Measure.prod_restrict]; exact hg_int_prod
  have hRHSiter :
      (∫ p in Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            g (e.symm p)
            ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))) =
        ∫ s in Set.Ico (0 : ℝ) 1, ∫ y in Set.pi Set.univ
            (fun _ : Fin n => Set.Ico (0 : ℝ) 1), g (i.insertNth s y) := by
    rw [← Measure.prod_restrict]
    rw [integral_prod _ hg_int_restrict]
    rfl
  -- Step C: convert LHS similarly. The integrand `λ x => ∫ t, g(update x i t)`
  -- on the cube. Pull back via `e.symm`: `update (e.symm (s, y)) i t = e.symm (t, y)`.
  have hupd_eq : ∀ (s : ℝ) (y : Fin n → ℝ) (t : ℝ),
      Function.update (i.insertNth (α := fun _ => ℝ) s y) i t =
        i.insertNth (α := fun _ => ℝ) t y := by
    intro s y t
    exact Fin.update_insertNth (α := fun _ => ℝ) i s t y
  -- Reformulate LHS via Fubini.
  have hLHS_pull :
      (∫ x in UnitCube (n + 1), ∫ t in (0 : ℝ)..1,
            g (Function.update x i t)) =
        ∫ p in Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            (∫ t in (0 : ℝ)..1, g (i.insertNth t p.2))
            ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    have himg : (UnitCube (n + 1) : Set (Fin (n + 1) → ℝ)) =
        e.symm '' (e.symm ⁻¹' UnitCube (n + 1)) :=
      (Set.image_preimage_eq _ e.symm.surjective).symm
    rw [himg, he_symm.setIntegral_image_emb e.symm.measurableEmbedding _ _, hpre]
    refine setIntegral_congr_fun ?_ ?_
    · exact (measurableSet_Ico).prod
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    · intro p _
      refine intervalIntegral.integral_congr ?_
      intro t _
      simp only [he_symm_eq]
      rw [hupd_eq p.1 p.2 t]
  -- Step D: rewrite the inner intervalIntegral as a setIntegral over Ico,
  -- then swap integrals using Fubini, then identify with `s`-independent integrand.
  have hinner_eq : ∀ (s : ℝ) (y : Fin n → ℝ),
      (∫ t in (0 : ℝ)..1, g (i.insertNth t y)) =
        ∫ t in Set.Ico (0 : ℝ) 1, g (i.insertNth t y) := by
    intro s y
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Ico_eq_integral_Ioc]
  have hLHS_iter1 :
      (∫ p in Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            (∫ t in (0 : ℝ)..1, g (i.insertNth t p.2))
            ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))) =
        ∫ s in Set.Ico (0 : ℝ) 1,
          ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            ∫ t in (0 : ℝ)..1, g (i.insertNth t y) := by
    -- Integrability of the parametric integrand on the product cube.
    have hcont' : Continuous
        (fun p : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..1, g (i.insertNth t p.2)) := by
      have : Continuous (fun y : Fin n → ℝ =>
          ∫ t in (0 : ℝ)..1, g (i.insertNth t y)) := by
        apply continuous_parametric_intervalIntegral_of_continuous
        · exact hg.comp (Continuous.finInsertNth (A := fun _ => ℝ) i
            continuous_snd continuous_fst)
        · exact continuous_const
      exact this.comp continuous_snd
    have hLI : LocallyIntegrable
        (fun p : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..1, g (i.insertNth t p.2))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      hcont'.locallyIntegrable
    have hint_prod := (hLI.integrableOn_isCompact hcompact_prod).mono_set hsub_prod
    have hint_restrict :
        Integrable (fun p : ℝ × (Fin n → ℝ) => ∫ t in (0 : ℝ)..1, g (i.insertNth t p.2))
          (((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1)).prod
            ((volume : Measure (Fin n → ℝ)).restrict
              (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)))) := by
      rw [Measure.prod_restrict]; exact hint_prod
    -- Apply Fubini.
    rw [← Measure.prod_restrict, integral_prod _ hint_restrict]
  -- Step E: Use that the inner integrand is `s`-independent: integrating over
  -- `s ∈ Ico 0 1` (volume 1) gives a no-op factor.
  have hvol_s : (volume : Measure ℝ) (Set.Ico (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Ico]; simp
  have hLHS_iter2 :
      (∫ s in Set.Ico (0 : ℝ) 1,
          ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            ∫ t in (0 : ℝ)..1, g (i.insertNth t y)) =
        ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
          ∫ t in (0 : ℝ)..1, g (i.insertNth t y) := by
    rw [setIntegral_const]
    rw [measureReal_def, hvol_s]
    simp
  -- Step F: convert inner intervalIntegral into setIntegral over Ico, then swap.
  have hLHS_iter3 :
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
          ∫ t in (0 : ℝ)..1, g (i.insertNth t y)) =
        ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
          ∫ t in Set.Ico (0 : ℝ) 1, g (i.insertNth t y) := by
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) ?_
    intro y _; exact hinner_eq 0 y
  -- Step G: swap the order of integration.
  have hLHS_iter4 :
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
          ∫ t in Set.Ico (0 : ℝ) 1, g (i.insertNth t y)) =
        ∫ t in Set.Ico (0 : ℝ) 1,
          ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            g (i.insertNth t y) := by
    -- Reduce to product-integrability of `(t, y) ↦ g(insertNth i t y)`.
    have hprod_int : Integrable (fun p : ℝ × (Fin n → ℝ) => g (i.insertNth p.1 p.2))
        (((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1)).prod
          ((volume : Measure (Fin n → ℝ)).restrict
            (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)))) := by
      have hcont : Continuous
          (fun p : ℝ × (Fin n → ℝ) => g (i.insertNth p.1 p.2)) := by
        exact hg.comp (Continuous.finInsertNth (A := fun _ => ℝ) i
          continuous_fst continuous_snd)
      have hLI : LocallyIntegrable
          (fun p : ℝ × (Fin n → ℝ) => g (i.insertNth p.1 p.2))
          ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
        hcont.locallyIntegrable
      have hint := (hLI.integrableOn_isCompact hcompact_prod).mono_set hsub_prod
      -- `IntegrableOn` unfolds to `Integrable _ ((vol.prod vol).restrict (...))`.
      -- Use `Measure.prod_restrict` to convert to `(vol.restrict _).prod (vol.restrict _)`.
      rwa [show (((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1)).prod
              ((volume : Measure (Fin n → ℝ)).restrict
                (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)))) =
            ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).restrict
              (Set.Ico (0 : ℝ) 1 ×ˢ Set.pi Set.univ
                (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) from
          Measure.prod_restrict _ _]
    -- Rearrange: outer y, inner t ↔ outer t, inner y.
    have h1 := integral_integral_swap (μ := (volume : Measure (Fin n → ℝ)).restrict
        (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)))
      (ν := (volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1))
      (f := fun y t => g (i.insertNth t y))
    apply h1
    -- Hypothesis: integrability of `uncurry (fun y t => ...)` on the product.
    -- `uncurry (fun y t => g (insertNth t y)) p = g (insertNth p.2 p.1)`.
    have hsw : (Function.uncurry (fun (y : Fin n → ℝ) (t : ℝ) => g (i.insertNth t y)))
        = (fun p : (Fin n → ℝ) × ℝ => g (i.insertNth p.2 p.1)) := by
      funext p; rfl
    rw [hsw]
    -- Use `integrable_swap`: prod_swap exchanges product measure.
    have hswap := hprod_int.swap
    -- `hswap : Integrable (fun p => g (insertNth p.2 p.1)) (ν'.prod μ')`.
    simpa only [Function.comp_def, Prod.swap] using hswap
  -- Step H: Apply `piFinSuccAbove` to identify
  -- `∫_t ∫_y g(insertNth t y)` with `∫_x g(x)` over UnitCube (n+1).
  have hfinal :
      (∫ t in Set.Ico (0 : ℝ) 1,
          ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
            g (i.insertNth t y)) =
        ∫ x in UnitCube (n + 1), g x := by
    -- Reverse the chain: this is exactly Step B run backwards on `g`.
    have hg_int_restrict' : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e.symm p))
        (((volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1)).prod
          ((volume : Measure (Fin n → ℝ)).restrict
            (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)))) := hg_int_restrict
    have hRHS' := hRHS
    rw [hRHSiter] at hRHS'
    -- `hRHS' : ∫ g = ∫_s ∫_y g(insertNth s y)`
    rw [← hRHS']
  -- Combine all steps.
  rw [hLHS_pull, hLHS_iter1, hLHS_iter2, hLHS_iter3, hLHS_iter4, hfinal]

/-- Auxiliary: continuity of `partialMean f k` when `f` is continuous.
The recursion involves an `intervalIntegral` of a continuous function, which is
continuous in the parameter. -/
private lemma continuous_partialMean {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    ∀ k : ℕ, Continuous (partialMean f k) := by
  intro k
  induction k with
  | zero => simpa [partialMean_zero] using hf
  | succ k ih =>
    by_cases hk : k < d
    · -- Apply `partialMean_succ`: continuity of parametric intervalIntegral.
      have hexpr :
          partialMean f (k + 1) =
            fun x => ∫ t in (0 : ℝ)..1, partialMean f k (Function.update x ⟨k, hk⟩ t) := by
        funext x; exact partialMean_succ f hk x
      rw [hexpr]
      -- The integrand is continuous in `(t, x)` since `update x i t` is continuous.
      apply continuous_parametric_intervalIntegral_of_continuous
      · -- Continuity of `(x, t) ↦ partialMean f k (update x ⟨k,hk⟩ t)`.
        have : Continuous
            (fun p : (Fin d → ℝ) × ℝ => Function.update p.1 ⟨k, hk⟩ p.2) := by
          refine continuous_pi (fun j => ?_)
          classical
          by_cases hj : j = (⟨k, hk⟩ : Fin d)
          · subst hj
            have : (fun p : (Fin d → ℝ) × ℝ => (Function.update p.1 ⟨k, hk⟩ p.2) ⟨k, hk⟩)
                = (fun p : (Fin d → ℝ) × ℝ => p.2) := by
              funext p; simp
            rw [this]; exact continuous_snd
          · have : (fun p : (Fin d → ℝ) × ℝ => (Function.update p.1 ⟨k, hk⟩ p.2) j)
                = (fun p : (Fin d → ℝ) × ℝ => p.1 j) := by
              funext p; simp [Function.update_of_ne hj]
            rw [this]; exact (continuous_apply j).comp continuous_fst
        exact ih.comp this
      · exact continuous_const
    · -- For `k ≥ d`, recursion is a no-op, reuse IH.
      have hexpr : partialMean f (k + 1) = partialMean f k := by
        funext x; exact partialMean_succ_of_ge f hk x
      rw [hexpr]; exact ih

/-- Auxiliary: integrating `partialMean f k` over the cube collapses to
integrating `f`, by repeated Fubini. -/
private lemma setIntegral_partialMean_eq {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) :
    ∀ {k : ℕ}, k ≤ d →
      (∫ x in UnitCube d, partialMean f k x) = ∫ x in UnitCube d, f x := by
  intro k
  induction k with
  | zero => intro _; rw [partialMean_zero]
  | succ k ih =>
    intro hk1
    have hkd : k < d := hk1
    have hkle : k ≤ d := le_of_lt hkd
    -- Unfold `partialMean f (k+1) x = ∫ t, partialMean f k (update x ⟨k,_⟩ t)`.
    have hcong : (fun x => partialMean f (k + 1) x) =
        (fun x => ∫ t in (0 : ℝ)..1,
            partialMean f k (Function.update x ⟨k, hkd⟩ t)) := by
      funext x; exact partialMean_succ f hkd x
    rw [show (fun x => partialMean f (k + 1) x) = partialMean f (k + 1) from rfl] at hcong
    have : (∫ x in UnitCube d, partialMean f (k + 1) x) =
        ∫ x in UnitCube d, ∫ t in (0 : ℝ)..1,
            partialMean f k (Function.update x ⟨k, hkd⟩ t) := by
      rw [hcong]
    rw [this]
    -- Apply Fubini-step lemma with `g = partialMean f k`.
    rw [setIntegral_intervalIntegral_update hkd (continuous_partialMean hf k)]
    exact ih hkle

/-- **Fubini collapse for the partial-mean operator.**

After `d` iterated 1-D averages over the unit cube, the partial-mean
operator collapses to the (constant) full periodic mean:

```
partialMean f d = fun _ => periodicMean f.
```

The proof combines:
- `partialMean_indep` (with `k = d`): `partialMean f d` is constant.
- `setIntegral_partialMean_eq` at `k = d`: integrating `partialMean f d`
  over the cube equals `∫_{UnitCube d} f = periodicMean f`.
Together with `vol(UnitCube d) = 1`, this pins the constant value to
`periodicMean f`. -/
theorem partialMean_card (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    partialMean f d = fun _ : Fin d → ℝ => periodicMean f := by
  -- `partialMean f d` is constant by independence.
  funext x
  have hconst : ∀ y : Fin d → ℝ, partialMean f d x = partialMean f d y := by
    intro y
    refine partialMean_indep f le_rfl ?_
    intro i hi
    -- `(i : ℕ) ≥ d` is impossible since `i < d`, so this is vacuous.
    exact (Nat.not_lt.mpr hi i.isLt).elim
  -- Integrate the constant identity over the cube.
  have hμ_finite : (volume : Measure (Fin d → ℝ)) (UnitCube d) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have hint_const :
      (∫ _y in UnitCube d, partialMean f d x) = partialMean f d x := by
    rw [setIntegral_const, measureReal_def, volume_unitCube]; simp
  have hcong_int :
      (∫ y in UnitCube d, partialMean f d x) =
        ∫ y in UnitCube d, partialMean f d y := by
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro y _; exact hconst y
  have heq := setIntegral_partialMean_eq hf (le_refl d)
  -- Combine.
  have : partialMean f d x = ∫ x in UnitCube d, f x := by
    rw [← hint_const, hcong_int, heq]
  rw [this]; rfl

/-- Sample example: for the constant function `f = const c`, `partialMean f d`
collapses to `const c`. (Both sides equal `fun _ => c`.) -/
example (c : ℝ) :
    partialMean (d := d) (fun _ : Fin d → ℝ => c) d =
      fun _ : Fin d → ℝ => periodicMean (fun _ : Fin d → ℝ => c) := by
  exact partialMean_card (fun _ : Fin d → ℝ => c) continuous_const

/-! ### Change-of-variables for `pathPoint`

The `pathPoint x y m` construction blends the first `m` coordinates of
`y` with the last `d − m` coordinates of `x`. The "irrelevant"
coordinates (`x_{<m}` and `y_{≥m}`) each contribute a unit factor when
integrated against `vol(UnitCube d) = 1`. The change-of-variables
identity below makes this precise:

```
∫_x ∫_y F(pathPoint x y m) dy dx = ∫_z F(z) dz   (m ≤ d, F continuous).
```

This is the key combinatorial fact behind the `L^p`-on-RHS Wirtinger
inequality (`infra:P1-poincare-LpRHS-smooth`). It is proved by induction
on `m`, peeling off one coordinate per step using the existing Fubini
collapse `setIntegral_intervalIntegral_update`. -/

/-- Coordinate-by-coordinate identity relating `pathPoint x y (m+1)` to
`pathPoint x y m` updated at index `⟨m, hm⟩`. -/
private lemma pathPoint_update_eq_succ {m : ℕ} (hm : m < d)
    (x y : Fin d → ℝ) (τ : ℝ) :
    Function.update (pathPoint x y m) ⟨m, hm⟩ τ =
      pathPoint x (Function.update y ⟨m, hm⟩ τ) (m + 1) := by
  classical
  funext j
  by_cases hjm : j = (⟨m, hm⟩ : Fin d)
  · subst hjm
    simp [pathPoint, Function.update]
  · have hjne : (j : ℕ) ≠ m := by
      intro h; apply hjm; ext; exact h
    by_cases hjlt : (j : ℕ) < m
    · have hjlt1 : (j : ℕ) < m + 1 := Nat.lt_succ_of_lt hjlt
      simp [pathPoint, hjlt, hjlt1, Function.update_of_ne hjm]
    · have hjnotlt1 : ¬ ((j : ℕ) < m + 1) := by omega
      simp [pathPoint, hjlt, hjnotlt1, Function.update_of_ne hjm]

/-- A second coordinate identity: updating `x` at `⟨m, hm⟩` and then taking
`pathPoint` at level `m` is the same as updating the level-`m` `pathPoint`. -/
private lemma pathPoint_update_x_eq {m : ℕ} (hm : m < d)
    (x y : Fin d → ℝ) (τ : ℝ) :
    pathPoint (Function.update x ⟨m, hm⟩ τ) y m =
      Function.update (pathPoint x y m) ⟨m, hm⟩ τ := by
  classical
  funext j
  by_cases hjm : j = (⟨m, hm⟩ : Fin d)
  · subst hjm
    -- LHS pathPoint at j = ⟨m,_⟩: (j:ℕ) = m not < m, so equals (update x ⟨m,_⟩ τ)_j = τ.
    -- RHS update at j = ⟨m,_⟩: τ.
    simp [pathPoint, Function.update]
  · have hjne : (j : ℕ) ≠ m := by
      intro h; apply hjm; ext; exact h
    by_cases hjlt : (j : ℕ) < m
    · simp [pathPoint, hjlt, Function.update_of_ne hjm]
    · simp [pathPoint, hjlt, Function.update_of_ne hjm]

/-- Continuity of `(x, y) ↦ pathPoint x y m` for any fixed `m`. -/
private lemma continuous_pathPoint_pair (m : ℕ) :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => pathPoint p.1 p.2 m) := by
  refine continuous_pi (fun j => ?_)
  unfold pathPoint
  by_cases hjk : (j : ℕ) < m
  · have h : (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        if (j : ℕ) < m then p.2 j else p.1 j) =
        (fun p => p.2 j) := by
      funext p; simp [hjk]
    rw [h]; exact (continuous_apply j).comp continuous_snd
  · have h : (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        if (j : ℕ) < m then p.2 j else p.1 j) =
        (fun p => p.1 j) := by
      funext p; simp [hjk]
    rw [h]; exact (continuous_apply j).comp continuous_fst

/-- Continuity of `(x, y) ↦ F(pathPoint x y m)` when `F` is continuous. -/
private lemma continuous_pathPoint_pair_apply {F : (Fin d → ℝ) → ℝ}
    (hF : Continuous F) (m : ℕ) :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => F (pathPoint p.1 p.2 m)) :=
  hF.comp (continuous_pathPoint_pair m)

/-- Continuity of `x ↦ F(pathPoint x y m)` for fixed `y`. -/
private lemma continuous_pathPoint_x {F : (Fin d → ℝ) → ℝ}
    (hF : Continuous F) (m : ℕ) (y : Fin d → ℝ) :
    Continuous (fun x : Fin d → ℝ => F (pathPoint x y m)) :=
  (continuous_pathPoint_pair_apply hF m).comp (Continuous.prodMk continuous_id continuous_const)

/-- Continuity of `y ↦ F(pathPoint x y m)` for fixed `x`. -/
private lemma continuous_pathPoint_y {F : (Fin d → ℝ) → ℝ}
    (hF : Continuous F) (m : ℕ) (x : Fin d → ℝ) :
    Continuous (fun y : Fin d → ℝ => F (pathPoint x y m)) :=
  (continuous_pathPoint_pair_apply hF m).comp (Continuous.prodMk continuous_const continuous_id)

/-! ### Weighted power-mean inequality (Hölder)

The following lemma is **domain-agnostic**: it holds on any measurable
set in any measure space. We port it verbatim from
`docs/references/DeGiorgi/DeGiorgi/Poincare.lean:1224` because Phase B
(the periodic Sobolev–Poincaré argument) needs it on the unit cube,
where the cube has finite Lebesgue measure (in fact volume `1`). The
proof reduces to Hölder's inequality after re-weighting the measure by
`w` (via `withDensity`).

Adapted from DeGiorgi.Poincare (whole-space version);
the proof is genuinely domain-agnostic so we keep the statement as is.
-/

/-- **Weighted power-mean inequality.** For nonnegative `f, w` and
`p > 1`, on any measurable set `s` of any measure space,

```
(∫_s f · w dμ) ^ p ≤ (∫_s w dμ) ^ (p − 1) · ∫_s f^p · w dμ.
```

This is Hölder's inequality applied to the measure `μ.restrict s`
re-weighted by `w` via `withDensity`. -/
theorem weighted_power_mean_setIntegral
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {s : Set α} (hs : MeasurableSet s)
    {p : ℝ} (hp : 1 < p)
    {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hw : ∀ x, 0 ≤ w x)
    (hf_meas : AEMeasurable f (μ.restrict s))
    (hwi : MeasureTheory.IntegrableOn w s μ)
    (hfpwi : MeasureTheory.IntegrableOn (fun x => (f x) ^ p * w x) s μ) :
    (∫ x in s, f x * w x ∂μ) ^ p ≤
      (∫ x in s, w x ∂μ) ^ (p - 1) * ∫ x in s, (f x) ^ p * w x ∂μ := by
  set μs : MeasureTheory.Measure α := μ.restrict s
  set ρ : α → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)
  set ν : MeasureTheory.Measure α := μs.withDensity ρ
  let q : ℝ := p / (p - 1)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpq : p.HolderConjugate q := by
    dsimp [q]
    exact Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := hpq.symm.pos
  have hρ_aemeas : AEMeasurable ρ μs := by
    simpa [ρ, μs] using hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ x ∂μs, ρ x < ∞ := by
    filter_upwards with x
    simp [ρ]
  have hρ_lint_ne_top : ∫⁻ x, ρ x ∂μs ≠ ∞ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hwi
      (MeasureTheory.ae_of_all _ fun x => hw x)]
    simp
  haveI : MeasureTheory.IsFiniteMeasure ν :=
    MeasureTheory.isFiniteMeasure_withDensity hρ_lint_ne_top
  have hf_meas_ν : AEMeasurable f ν := by
    exact hf_meas.mono_ac (MeasureTheory.withDensity_absolutelyContinuous _ _)
  have hpow_int_base :
      MeasureTheory.Integrable (fun x => (ρ x).toReal • (‖f x‖ ^ p)) μs := by
    refine hfpwi.congr ?_
    filter_upwards with x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hw x), Real.norm_of_nonneg (hf x)]
    ring
  have hpow_int : MeasureTheory.Integrable (fun x => ‖f x‖ ^ p) ν := by
    rw [show ν = μs.withDensity ρ from rfl]
    exact
      (MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
        (μ := μs) hρ_aemeas hρ_lt_top).2 hpow_int_base
  have hf_mem : MeasureTheory.MemLp f (ENNReal.ofReal p) ν := by
    exact
      (MeasureTheory.integrable_norm_rpow_iff
        (μ := ν) hf_meas_ν.aestronglyMeasurable
        (by simp [hp_pos]) ENNReal.ofReal_ne_top).1 <| by
          simpa [ENNReal.toReal_ofReal hp_nonneg] using hpow_int
  have h_one_mem :
      MeasureTheory.MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal q) ν := by
    simpa [q] using
      (MeasureTheory.memLp_const (μ := ν) (p := ENNReal.ofReal q) (1 : ℝ))
  have hHolder :
      ∫ x, f x * (1 : ℝ) ∂ν ≤
        (∫ x, (f x) ^ p ∂ν) ^ (1 / p : ℝ) *
          (∫ x, (1 : ℝ) ^ q ∂ν) ^ (1 / q : ℝ) := by
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := ν) hpq
      (MeasureTheory.ae_of_all _ fun x => hf x)
      (MeasureTheory.ae_of_all _ fun _ => by positivity)
      hf_mem h_one_mem
  have hleft_eq : ∫ x, f x ∂ν = ∫ x in s, f x * w x ∂μ := by
    rw [show ν = μs.withDensity ρ from rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hpow_eq : ∫ x, (f x) ^ p ∂ν = ∫ x in s, (f x) ^ p * w x ∂μ := by
    rw [show ν = μs.withDensity ρ from rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hone_eq : ∫ x, (1 : ℝ) ^ q ∂ν = ∫ x in s, w x ∂μ := by
    rw [show ν = μs.withDensity ρ from rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, q, smul_eq_mul, ENNReal.toReal_ofReal, hw]
  set A := ∫ x in s, f x * w x ∂μ
  set I := ∫ x in s, (f x) ^ p * w x ∂μ
  set W := ∫ x in s, w x ∂μ
  have hA_nonneg : 0 ≤ A := by
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
  have hI_nonneg : 0 ≤ I := by
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ =>
      mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))
  have hW_nonneg : 0 ≤ W := by
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ => hw x)
  -- Case split on whether `∫ w = 0`.
  by_cases hW_zero : ∫ x in s, w x ∂μ = 0
  · -- If `w` integrates to zero (so `w = 0` a.e. on `s`), both sides vanish.
    have hfw_nonneg : 0 ≤ ∫ x in s, f x * w x ∂μ :=
      MeasureTheory.setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
    have hfw_zero : ∫ x in s, f x * w x ∂μ ≤ 0 := by
      by_cases hfwi : MeasureTheory.IntegrableOn (fun x => f x * w x) s μ
      · have hwi := hwi
        have hw_ae : w =ᵐ[μ.restrict s] 0 := by
          rwa [MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
            (MeasureTheory.ae_restrict_of_ae
              (MeasureTheory.ae_of_all _ (fun x => hw x))) hwi] at hW_zero
        have : (fun x => f x * w x) =ᵐ[μ.restrict s] 0 :=
          hw_ae.mono (fun x hx => by simp [hx])
        rw [MeasureTheory.integral_congr_ae this]; simp
      · simp [MeasureTheory.integral_undef hfwi]
    have h0 := le_antisymm hfw_zero hfw_nonneg
    simpa [A, I, W, h0, hW_zero] using
      (show A ^ p ≤ W ^ (p - 1) * I from by
        simp [A, I, W, h0, hW_zero,
          mul_nonneg (Real.rpow_nonneg (le_refl _) _)
            (MeasureTheory.setIntegral_nonneg hs
              (fun x _ => mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))),
          Real.zero_rpow (by linarith : p ≠ 0)])
  · have hW_pos : 0 < ∫ x in s, w x ∂μ :=
      lt_of_le_of_ne (MeasureTheory.setIntegral_nonneg hs (fun x _ => hw x))
        (Ne.symm hW_zero)
    have hνreal_eq : ν.real Set.univ = W := by
      calc
        ν.real Set.univ = ∫ x, (1 : ℝ) ∂ν := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real]
        _ = ∫ x, (1 : ℝ) ^ q ∂ν := by simp [q]
        _ = W := hone_eq
    have hHolder' : A ≤ W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ) := by
      simpa [A, I, W, hleft_eq, hpow_eq, hνreal_eq, one_div,
              mul_comm, mul_left_comm, mul_assoc]
        using hHolder
    have hpow := Real.rpow_le_rpow hA_nonneg hHolder' (le_of_lt hp_pos)
    have hWroot_nonneg : 0 ≤ W ^ (1 / q : ℝ) := Real.rpow_nonneg hW_nonneg _
    have hIroot_nonneg : 0 ≤ I ^ (1 / p : ℝ) := Real.rpow_nonneg hI_nonneg _
    have hp_ne_zero : p ≠ 0 := by linarith
    have hrhs :
        (W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ)) ^ p = W ^ (p - 1) * I := by
      rw [Real.mul_rpow hWroot_nonneg hIroot_nonneg]
      rw [← Real.rpow_mul hW_nonneg, ← Real.rpow_mul hI_nonneg]
      have hWq : (1 / q : ℝ) * p = p - 1 := by
        dsimp [q]
        field_simp [hp_ne_zero, show p - 1 ≠ 0 by linarith]
      have hIp : (1 / p : ℝ) * p = 1 := by
        field_simp [hp_ne_zero]
      rw [hWq, hIp, Real.rpow_one]
    simpa [A, I, W] using hpow.trans_eq hrhs

/-- Trivial sanity-check for `weighted_power_mean_setIntegral`: with
`f = w = 1` on the unit cube and any `p > 1`, both sides reduce to
`1`, and the inequality `1 ≤ 1` is obvious. -/
example {p : ℝ} (hp : 1 < p) :
    (∫ _ in UnitCube d, (1 : ℝ) * (1 : ℝ)) ^ p ≤
      (∫ _ in UnitCube d, (1 : ℝ)) ^ (p - 1) *
        ∫ _ in UnitCube d, (1 : ℝ) ^ p * (1 : ℝ) := by
  refine weighted_power_mean_setIntegral measurableSet_unitCube hp
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    (aemeasurable_const) ?_ ?_
  · -- `IntegrableOn (fun _ => (1 : ℝ)) (UnitCube d) volume`.
    have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube d) ≠ ⊤ := by
      rw [volume_unitCube]; exact ENNReal.one_ne_top
    exact MeasureTheory.integrableOn_const hvol
  · -- `IntegrableOn (fun _ => 1 ^ p * 1) (UnitCube d) volume` — also constant.
    have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube d) ≠ ⊤ := by
      rw [volume_unitCube]; exact ENNReal.one_ne_top
    have h1 :
        (fun _ : Fin d → ℝ => (1 : ℝ) ^ p * (1 : ℝ)) =
          (fun _ : Fin d → ℝ => (1 : ℝ) ^ p * (1 : ℝ)) := rfl
    exact MeasureTheory.integrableOn_const hvol

/-! ### `poincare_smooth_unitCube`: the smooth-case Poincaré–Wirtinger
inequality on the unit cube

This is the periodic analogue of DeGiorgi's `poincare_smooth_unitBall`
(`docs/references/DeGiorgi/DeGiorgi/Poincare.lean:1359`). On the
torus we don't need the Riesz-potential representation formula nor a
ball-extension layer: the telescoping pointwise bound
`pointwise_wirtinger_smoothPeriodic` gives the result directly on
`UnitCube d`. The actual content is delivered by
`poincareWirtinger_smooth` above; this is a renaming alias matching
the task spec. -/

/-- **Poincaré–Wirtinger inequality on the unit cube, smooth case.**
The periodic analogue of DeGiorgi's `poincare_smooth_unitBall`. Under
a uniform `L^∞` bound `|∂_i φ z| ≤ C` on the partial derivatives of a
smooth periodic function `φ`, for any exponent `p`,

```
‖φ − ⨏ φ‖_{L^p_per} ≤ C(d) · C,
```

where `C(d) = poincareWirtingerConstant d = d`. The bound holds without
restriction on `p` (no `1 ≤ p` required) because it descends from the
pointwise telescoping bound on `UnitCube d` and the cube has unit
volume. -/
theorem poincare_smooth_unitCube (p : ℝ≥0∞) {C : ℝ} (φ : SmoothPeriodic d)
    (hC : ∀ i : Fin d, ∀ z : Fin d → ℝ,
        |((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) z| ≤ C) :
    lpNormPer p (fun x => (φ : (Fin d → ℝ) → ℝ) x
        - periodicMean (φ : (Fin d → ℝ) → ℝ)) ≤
      poincareWirtingerConstant d * C :=
  poincareWirtinger_smooth p φ hC

/-- Sample example for `poincare_smooth_unitCube`: a constant smooth-periodic
function `const c` has zero gradient, so the bound reduces to `0 ≤ d · 0`. -/
example (c : ℝ) (p : ℝ≥0∞) :
    lpNormPer p (fun x : Fin d → ℝ =>
        ((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
          - periodicMean
              ((SmoothPeriodic.const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
      ≤ poincareWirtingerConstant d * 0 := by
  refine poincare_smooth_unitCube (C := 0) (p := p) (SmoothPeriodic.const c) ?_
  intro i z
  have : ((SmoothPeriodic.partialDeriv i (SmoothPeriodic.const c) :
        SmoothPeriodic d) : (Fin d → ℝ) → ℝ) z = 0 := by
    simp [SmoothPeriodic.coe_partialDeriv, SmoothPeriodic.coe_const]
  rw [this]; simp

end Periodic
end StationaryMFG
