module

public import StationaryMFG.Periodic.Mollifier1D
public import StationaryMFG.Periodic.Integral
public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.TestFunctions
public import StationaryMFG.Periodic.Translation
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-!
# d-dimensional periodic mollifier

This file constructs the d-dimensional periodic mollifier
`periodicMollifier ε : (Fin d → ℝ) → ℝ` as the tensor product of the
1D periodic mollifier `periodicMollifier1D ε` along each coordinate:

`periodicMollifier ε x := ∏ i, periodicMollifier1D ε (x i)`.

For each `0 < ε < 1/2`, we show:

* `periodicMollifier_smooth` — `ContDiff ℝ ∞` (i.e. `(⊤ : ℕ∞)`).
* `periodicMollifier_periodic` — invariance under integer translations
  in `(Fin d → ℝ)`.
* `periodicMollifier_nonneg` — pointwise non-negativity.
* `periodicIntegral_periodicMollifier` — integral over the unit cube
  equals `1`.
* `periodicMollifier_asSmoothPeriodic` — the packaging into the
  `SmoothPeriodic d` structure of `TestFunctions.lean`.

The integral identity uses Fubini on `[0,1)^d = ∏ i, [0,1)`:

```
∫_{[0,1)^d} ∏ i, η¹(x i) = ∏ i, ∫_{[0,1)} η¹(x i) dx_i = 1^d = 1.
```

-- Adapted from LpSpaces.Mollification (whole-space convolution-based
-- mollifier); here we tensor the 1D periodic mollifier instead.
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Set Function Filter
open scoped ContDiff Topology ENNReal NNReal

variable {d : ℕ}

/-! ### Definition -/

/-- The d-dimensional periodic mollifier of width `ε`, defined as the
tensor product of the 1D periodic mollifier `periodicMollifier1D ε`
along each coordinate. For `0 < ε < 1/2` it is smooth, periodic,
non-negative and integrates to `1` over the unit cube. -/
noncomputable def periodicMollifier (d : ℕ) (ε : ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => ∏ i : Fin d, periodicMollifier1D ε (x i)

@[simp] lemma periodicMollifier_apply (ε : ℝ) (x : Fin d → ℝ) :
    periodicMollifier d ε x = ∏ i : Fin d, periodicMollifier1D ε (x i) := rfl

/-! ### Non-negativity -/

/-- The d-dimensional periodic mollifier is everywhere non-negative. -/
lemma periodicMollifier_nonneg (ε : ℝ) (x : Fin d → ℝ) :
    0 ≤ periodicMollifier d ε x :=
  Finset.prod_nonneg (fun i _ => periodicMollifier1D_nonneg ε (x i))

/-! ### Periodicity -/

/-- The d-dimensional periodic mollifier is invariant under every integer
translation. The proof uses 1D periodicity in each coordinate independently. -/
lemma periodicMollifier_periodic (ε : ℝ) :
    IsPeriodic (periodicMollifier d ε) := by
  intro k x
  -- Reduce to 1D periodicity coordinate-by-coordinate.
  unfold periodicMollifier
  apply Finset.prod_congr rfl
  intro i _
  -- Need: `periodicMollifier1D ε ((x + fun j => ↑(k j)) i)
  --        = periodicMollifier1D ε (x i)`.
  have hcoord : (x + fun j => ((k j : ℝ))) i = x i + (k i : ℝ) := by
    simp [Pi.add_apply]
  rw [hcoord]
  -- Apply 1D periodicity by induction on `k i : ℤ`.
  have hper := periodicMollifier1D_periodic ε
  -- `Function.Periodic` gives invariance under any integer multiple of `1`.
  have := hper.int_mul (k i) (x i)
  -- `(k i : ℝ) * 1 = (k i : ℝ)`, so `(x i) + (k i : ℝ) * 1 = (x i) + (k i : ℝ)`.
  simpa [mul_one] using this

/-! ### Smoothness -/

/-- Smoothness of the d-dim mollifier (in the sense `ContDiff ℝ (⊤ : ℕ∞)`,
i.e. infinitely differentiable) for `0 < ε < 1/2`. -/
lemma periodicMollifier_smooth (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ContDiff ℝ ((⊤ : ℕ∞)) (periodicMollifier d ε) := by
  -- Each factor `x ↦ periodicMollifier1D ε (x i)` is smooth: the 1D
  -- mollifier is smooth and the `i`-th projection is smooth.
  have h1D : ContDiff ℝ ((⊤ : ℕ∞)) (periodicMollifier1D ε) :=
    periodicMollifier1D_contDiff_of_lt_half ε hε hε'
  have hfactor : ∀ i : Fin d,
      ContDiff ℝ ((⊤ : ℕ∞))
        (fun x : Fin d → ℝ => periodicMollifier1D ε (x i)) := by
    intro i
    exact h1D.comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) (n := ((⊤ : ℕ∞))) i)
  -- Now use the finite-product closure for `ContDiff`.
  exact contDiff_prod (t := (Finset.univ : Finset (Fin d)))
    (fun i _ => hfactor i)

/-! ### Integral over the unit cube -/

/-- The d-dim periodic mollifier integrates to `1` over the unit cube
`[0,1)^d`. -/
theorem periodicIntegral_periodicMollifier (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < 1 / 2) :
    periodicIntegral (periodicMollifier d ε) = 1 := by
  -- Step 1: unfold definitions and use Fubini.
  unfold periodicIntegral periodicMollifier
  unfold UnitCube
  -- Convert `∫ in s, f ∂μ` to `∫ f ∂(μ.restrict s)`, then identify the
  -- restricted product measure with the product of restricted measures.
  rw [show (∫ x in (univ : Set (Fin d)).pi (fun _ : Fin d => Ico (0 : ℝ) 1),
            ∏ i : Fin d, periodicMollifier1D ε (x i)) =
          ∫ x, ∏ i : Fin d, periodicMollifier1D ε (x i)
            ∂((volume : Measure (Fin d → ℝ)).restrict
                ((univ : Set (Fin d)).pi (fun _ => Ico (0 : ℝ) 1))) from rfl,
      show (volume : Measure (Fin d → ℝ)) =
            Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi,
      Measure.restrict_pi_pi]
  -- Step 2: apply Fubini for finite products.
  rw [integral_fintype_prod_eq_prod
        (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
        (fun _ y => periodicMollifier1D ε y)
        (μ := fun _ => (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))]
  -- Step 3: each inner integral equals `1`, by `integral_periodicMollifier1D`.
  have hinner : ∀ _ : Fin d,
      ∫ y, periodicMollifier1D ε y
          ∂((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)) = 1 := by
    intro _
    -- `∫ y, f y ∂(μ.restrict s) = ∫ y in s, f y ∂μ`.
    rw [show (∫ y, periodicMollifier1D ε y
              ∂((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))) =
            ∫ y in Ico (0 : ℝ) 1, periodicMollifier1D ε y from rfl]
    exact integral_periodicMollifier1D ε hε hε'
  rw [Finset.prod_congr rfl (fun i _ => hinner i)]
  simp

/-! ### `SmoothPeriodic` packaging -/

/-- Package the d-dim periodic mollifier into the `SmoothPeriodic d`
structure of `TestFunctions.lean`. Requires `0 < ε < 1/2`. -/
noncomputable def periodicMollifier_asSmoothPeriodic
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) : SmoothPeriodic d where
  toFun    := periodicMollifier d ε
  smooth   := periodicMollifier_smooth ε hε hε'
  periodic := periodicMollifier_periodic ε

@[simp] lemma coe_periodicMollifier_asSmoothPeriodic
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ((periodicMollifier_asSmoothPeriodic (d := d) ε hε hε'
        : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = periodicMollifier d ε := rfl

/-! ### Sample example -/

/-- Sample example: the `SmoothPeriodic` packaging compiles. -/
example (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ φ : SmoothPeriodic 3,
      (φ : (Fin 3 → ℝ) → ℝ) = periodicMollifier 3 ε :=
  ⟨periodicMollifier_asSmoothPeriodic ε hε hε', rfl⟩

/-! ## Compactly-supported smooth bump kernel and `mollifiedApprox`

This section defines the **non-periodic** d-dim smooth compactly-supported
bump `bumpKernel d ε hε`, built as a tensor product of normalised 1D
`ContDiffBump`s. It is the kernel used in `mollifiedApprox f ε`, the
convolution `bumpKernel ⋆ f` against full Lebesgue measure on
`(Fin d → ℝ)`.

The convolution with a periodic `f` produces a periodic output (because
Lebesgue measure is translation-invariant; periodicity of the *kernel*
is **not** required for this — periodicity of `f` suffices). For
`MemLpPer 1 f` together with `IsPeriodic f`, the resulting function is
smooth and periodic, hence packageable as a `SmoothPeriodic d`.

`L^p_per` convergence of `mollifiedApprox f ε → f` as `ε → 0⁺` is
deferred to follow-up tasks (`infra:P1-density-Lp-young`,
`infra:P1-density-Lp-translation`, `infra:P1-density-Lp-conv`).

-- Adapted from LpSpaces.Mollification (definitional skeleton; the
-- convergence theorem is split off).
-/

/-! ### Compactly-supported smooth bump kernel -/

/-- A `ContDiffBump` centred at `0 : ℝ` with `rIn = ε/2`, `rOut = ε`. The
1D analogue used to build the d-dim tensor-product bump kernel. -/
noncomputable def palomar_Mollifier_auxBump1D (ε : ℝ) (hε : 0 < ε) :
    ContDiffBump (0 : ℝ) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Normalised 1D bump: `palomar_Mollifier_auxBump1D` divided by its integral. Smooth,
non-negative, supported in `(-ε, ε)`, integrates to `1`. -/
noncomputable def palomar_Mollifier_auxNormedBump1D (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ :=
  (palomar_Mollifier_auxBump1D ε hε).normed (volume : Measure ℝ)

private lemma auxNormedBump1D_nonneg (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    0 ≤ palomar_Mollifier_auxNormedBump1D ε hε x :=
  (palomar_Mollifier_auxBump1D ε hε).nonneg_normed x

private lemma auxNormedBump1D_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞)) (palomar_Mollifier_auxNormedBump1D ε hε) :=
  (palomar_Mollifier_auxBump1D ε hε).contDiff_normed

private lemma auxNormedBump1D_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (palomar_Mollifier_auxNormedBump1D ε hε) = Metric.ball (0 : ℝ) ε :=
  (palomar_Mollifier_auxBump1D ε hε).support_normed_eq

private lemma auxNormedBump1D_eq_zero_of_abs_ge (ε : ℝ) (hε : 0 < ε)
    {x : ℝ} (hx : ε ≤ |x|) : palomar_Mollifier_auxNormedBump1D ε hε x = 0 := by
  by_contra hne
  have hxsupp : x ∈ Function.support (palomar_Mollifier_auxNormedBump1D ε hε) := hne
  rw [auxNormedBump1D_support] at hxsupp
  have hxlt : |x| < ε := by
    have hd : dist x (0 : ℝ) < ε := hxsupp
    simpa [Real.dist_eq] using hd
  exact (not_lt.mpr hx) hxlt

/-- The d-dimensional compactly-supported smooth bump kernel of width
`ε`, defined as the tensor product of the normalised 1D bump
`palomar_Mollifier_auxNormedBump1D ε hε` along each coordinate:
`bumpKernel d ε hε x = ∏ i, palomar_Mollifier_auxNormedBump1D ε hε (x i)`. Unlike the
periodic mollifier, this kernel has compact support in the open box
`(-ε, ε)^d`. -/
noncomputable def bumpKernel (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (Fin d → ℝ) → ℝ :=
  fun x => ∏ i : Fin d, palomar_Mollifier_auxNormedBump1D ε hε (x i)

@[simp] lemma bumpKernel_apply (d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (x : Fin d → ℝ) :
    bumpKernel d ε hε x = ∏ i : Fin d, palomar_Mollifier_auxNormedBump1D ε hε (x i) := rfl

lemma bumpKernel_nonneg (d : ℕ) (ε : ℝ) (hε : 0 < ε) (x : Fin d → ℝ) :
    0 ≤ bumpKernel d ε hε x :=
  Finset.prod_nonneg (fun i _ => auxNormedBump1D_nonneg ε hε (x i))

/-- Smoothness of the d-dim bump kernel. -/
lemma bumpKernel_contDiff (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞)) (bumpKernel d ε hε) := by
  have h1D : ContDiff ℝ ((⊤ : ℕ∞)) (palomar_Mollifier_auxNormedBump1D ε hε) :=
    auxNormedBump1D_contDiff ε hε
  have hfactor : ∀ i : Fin d,
      ContDiff ℝ ((⊤ : ℕ∞))
        (fun x : Fin d → ℝ => palomar_Mollifier_auxNormedBump1D ε hε (x i)) := by
    intro i
    exact h1D.comp (contDiff_apply ℝ (fun _ : Fin d => ℝ) (n := ((⊤ : ℕ∞))) i)
  exact contDiff_prod (t := (Finset.univ : Finset (Fin d)))
    (fun i _ => hfactor i)

/-- The bump kernel vanishes outside the closed box `[-ε, ε]^d`. -/
lemma bumpKernel_eq_zero_of_exists_abs_ge (d : ℕ) (ε : ℝ) (hε : 0 < ε)
    {x : Fin d → ℝ} (hx : ∃ i, ε ≤ |x i|) :
    bumpKernel d ε hε x = 0 := by
  obtain ⟨i, hi⟩ := hx
  unfold bumpKernel
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  exact auxNormedBump1D_eq_zero_of_abs_ge ε hε hi

/-- The bump kernel has compact support, contained in the closed box
`[-ε, ε]^d`. -/
lemma bumpKernel_hasCompactSupport (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (bumpKernel d ε hε) := by
  -- The support is contained in the compact box K = ∏ i, [-ε, ε].
  set K : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ : Fin d => Set.Icc (-ε) ε)
    with hK_def
  have hK_compact : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  -- Outside K, some coordinate satisfies |x i| > ε ≥ ε, so the kernel vanishes.
  refine HasCompactSupport.intro hK_compact ?_
  intro x hx
  -- `x ∉ K` means some coordinate is outside `[-ε, ε]`, i.e. `|x i| > ε`.
  have hexists : ∃ i, |x i| > ε := by
    by_contra hall
    have hall' : ∀ i, |x i| ≤ ε := by
      intro i
      by_contra hi
      exact hall ⟨i, lt_of_not_ge hi⟩
    apply hx
    intro i _
    have habs : |x i| ≤ ε := hall' i
    have h1 : -ε ≤ x i := by
      have := neg_abs_le (x i)
      linarith
    have h2 : x i ≤ ε := (abs_le.mp habs).2
    exact ⟨h1, h2⟩
  obtain ⟨i, hi⟩ := hexists
  exact bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨i, le_of_lt hi⟩

/-! ### Mollified approximation -/

/-- The mollified approximation of `f` at width `ε`: the convolution of
the compactly-supported bump kernel `bumpKernel d ε hε` with `f` (against
full Lebesgue measure on `Fin d → ℝ`). For `ε ≤ 0` we return the zero
function, so the definition is total. -/
noncomputable def mollifiedApprox {d : ℕ} (f : (Fin d → ℝ) → ℝ) (ε : ℝ) :
    (Fin d → ℝ) → ℝ :=
  if hε : 0 < ε then
    MeasureTheory.convolution (bumpKernel d ε hε) f
      (ContinuousLinearMap.lsmul ℝ ℝ) (MeasureTheory.volume)
  else 0

/-- Unfolding for `0 < ε`. -/
lemma mollifiedApprox_eq_convolution {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    mollifiedApprox f ε =
      MeasureTheory.convolution (bumpKernel d ε hε) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
  unfold mollifiedApprox; rw [dif_pos hε]

/-- A measurable input has an a.e. strongly measurable mollification. -/
lemma mollifiedApprox_aestronglyMeasurable {d : ℕ}
    {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f volume)
    {ε : ℝ} (hε : 0 < ε) : AEStronglyMeasurable (mollifiedApprox f ε) volume := by
  rw [mollifiedApprox_eq_convolution f hε]
  exact (bumpKernel_contDiff d ε hε).continuous.aestronglyMeasurable.convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hf

/-! ### Periodicity of the mollified approximation -/

/-- If `f` is periodic, so is `bumpKernel ⋆ f`. The proof uses the
periodicity of `f` directly inside the convolution integrand: for any
integer translate `k : Fin d → ℤ`,
`(η ⋆ f)(x + k) = ∫ t, η(t) * f(x + k - t) dt = ∫ t, η(t) * f(x - t) dt
                = (η ⋆ f)(x)`,
the second equality being periodicity of `f`. -/
lemma mollifiedApprox_periodic {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsPeriodic f) (ε : ℝ) :
    IsPeriodic (mollifiedApprox f ε) := by
  by_cases hε : 0 < ε
  · -- Convolution case.
    rw [show mollifiedApprox f ε =
          MeasureTheory.convolution (bumpKernel d ε hε) f
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume from
        mollifiedApprox_eq_convolution f hε]
    intro k x
    -- Goal: (η ⋆ f)(x + k_ℝ) = (η ⋆ f)(x).
    change (∫ t, ContinuousLinearMap.lsmul ℝ ℝ
              (bumpKernel d ε hε t) (f (x + (fun i => (k i : ℝ)) - t))
            ∂(MeasureTheory.volume : Measure (Fin d → ℝ)))
          = ∫ t, ContinuousLinearMap.lsmul ℝ ℝ
              (bumpKernel d ε hε t) (f (x - t))
            ∂MeasureTheory.volume
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    -- Use periodicity of f: f((x - t) + k_ℝ) = f(x - t).
    have hreassoc : x + (fun i => (k i : ℝ)) - t
        = (x - t) + (fun i => (k i : ℝ)) := by
      ext i; simp [Pi.add_apply, Pi.sub_apply]; ring
    have hper : f ((x - t) + fun i => (k i : ℝ)) = f (x - t) := hf k (x - t)
    rw [hreassoc, hper]
  · -- Trivial case: mollifiedApprox = 0.
    have : mollifiedApprox f ε = 0 := by unfold mollifiedApprox; rw [dif_neg hε]
    rw [this]
    exact IsPeriodic.zero

/-! ### Smoothness of the mollified approximation -/

/-- Smoothness of the convolution `bumpKernel ⋆ f`, given local
integrability of `f`. The bump kernel is smooth with compact support, so
this follows from `HasCompactSupport.contDiff_convolution_left`. -/
lemma mollifiedApprox_contDiff_of_locallyIntegrable {d : ℕ}
    {f : (Fin d → ℝ) → ℝ} (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞)) (mollifiedApprox f ε) := by
  rw [mollifiedApprox_eq_convolution f hε]
  exact (bumpKernel_hasCompactSupport d ε hε).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (bumpKernel_contDiff d ε hε) hf

/-- Alias for the smoothness lemma using the natural Mathlib hypothesis
`LocallyIntegrable f volume`. The bridge from `MemLpPer 1 f + IsPeriodic f`
to `LocallyIntegrable f volume` is handled in a follow-up task; once that
lemma exists, `mollifiedApprox_contDiff` will compose them. -/
lemma mollifiedApprox_smooth {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞)) (mollifiedApprox f ε) :=
  mollifiedApprox_contDiff_of_locallyIntegrable hf hε

/-! ### Packaging as `SmoothPeriodic` -/

/-- Package the mollified approximation of a periodic, locally integrable
function `f` into the `SmoothPeriodic d` structure. The smoothness level
is the standard `((⊤ : ℕ∞) : ℕ∞ω)` used by `SmoothPeriodic`. -/
noncomputable def mollifiedApprox_asSmoothPeriodic {d : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    (hper : IsPeriodic f) {ε : ℝ} (hε : 0 < ε) : SmoothPeriodic d where
  toFun    := mollifiedApprox f ε
  smooth   := mollifiedApprox_smooth hf hε
  periodic := mollifiedApprox_periodic hper ε

@[simp] lemma coe_mollifiedApprox_asSmoothPeriodic {d : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    (hper : IsPeriodic f) {ε : ℝ} (hε : 0 < ε) :
    ((mollifiedApprox_asSmoothPeriodic hf hper hε : SmoothPeriodic d)
        : (Fin d → ℝ) → ℝ)
      = mollifiedApprox f ε := rfl

/-! ### Sample example -/

/-- Sample example: the constant function `1` is periodic and locally
integrable; its mollified approximation packages into `SmoothPeriodic 2`. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic 2,
      (φ : (Fin 2 → ℝ) → ℝ) =
        mollifiedApprox (fun _ : Fin 2 → ℝ => (1 : ℝ)) ε := by
  refine ⟨mollifiedApprox_asSmoothPeriodic (f := fun _ => (1 : ℝ)) ?_ ?_ hε, rfl⟩
  · -- `LocallyIntegrable` of the constant function.
    exact MeasureTheory.locallyIntegrable_const _
  · -- Periodicity of the constant function.
    exact IsPeriodic.const _

/-! ## Young's L¹ convolution inequality on the torus

For the compactly-supported smooth bump kernel `B = bumpKernel d ε hε` and
a periodic measurable `f`, the periodic `L¹` seminorm of the convolution
`B ⋆ f` is bounded by the whole-space `L¹` mass of `B` times the periodic
`L¹` seminorm of `f`:

`eLpNormPer 1 (mollifiedApprox f ε) ≤ (∫⁻ |B|) * eLpNormPer 1 f`.

This is the simplest `p = 1` case of Young's inequality. The proof is by
`Tonelli/Fubini` after the pointwise enorm bound for the Bochner integral.
The general `1 ≤ p < ∞` case is handled in the follow-up child task
`infra:P1-density-Lp-young-lp`.

-- Adapted from LpSpaces.YoungConvolution (whole-space L¹ × L^p version);
-- in the `p = 1` case the Minkowski integral inequality reduces to plain
-- Tonelli, which is what we use here.
-/

/-- **Young's convolution inequality, `p = 1` case, on the torus.**
For `B = bumpKernel d ε hε` (smooth, compactly supported, non-negative) and
periodic measurable real-valued `f`,

`eLpNormPer 1 (B ⋆ f) ≤ (∫⁻ x, ‖B x‖ₑ) * eLpNormPer 1 f`.

The proof uses the pointwise `‖∫ B(t) f(x-t) dt‖ₑ ≤ ∫⁻ ‖B(t)‖ₑ * ‖f(x-t)‖ₑ`
bound, Tonelli to swap the cube integral with the kernel integral, and the
periodic translation invariance of the lintegral
(`lintegral_unitCube_translate_eq_sub`). -/
theorem eLpNormPer_convolution_bumpKernel_le_l1
    {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf_meas : Measurable f) (hf_per : IsPeriodic f)
    {ε : ℝ} (hε : 0 < ε) :
    eLpNormPer 1 (mollifiedApprox f ε) ≤
      (∫⁻ t, ‖bumpKernel d ε hε t‖ₑ ∂(volume : Measure (Fin d → ℝ))) *
        eLpNormPer 1 f := by
  -- Set `B := bumpKernel d ε hε`, real-valued bump.
  set B : (Fin d → ℝ) → ℝ := bumpKernel d ε hε with hB_def
  -- Measurability of `B`.
  have hB_meas : Measurable B :=
    (bumpKernel_contDiff d ε hε).continuous.measurable
  -- Definition `mollifiedApprox f ε = B ⋆ f`.
  have hconv : mollifiedApprox f ε
      = MeasureTheory.convolution B f
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Fin d → ℝ)) :=
    mollifiedApprox_eq_convolution f hε
  -- Unfold `eLpNormPer 1 _` to a single lintegral on the cube.
  have h_unfold_conv :
      eLpNormPer (d := d) 1 (mollifiedApprox f ε)
        = ∫⁻ x in UnitCube d, ‖mollifiedApprox f ε x‖ₑ
          ∂(volume : Measure (Fin d → ℝ)) := by
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm
      (mollifiedApprox_aestronglyMeasurable hf_meas.aestronglyMeasurable hε).restrict]
  have h_unfold_f :
      eLpNormPer (d := d) 1 f
        = ∫⁻ x in UnitCube d, ‖f x‖ₑ
          ∂(volume : Measure (Fin d → ℝ)) := by
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm hf_meas.aestronglyMeasurable]
  rw [h_unfold_conv, h_unfold_f]
  -- Step 1: pointwise bound `‖(B ⋆ f)(x)‖ₑ ≤ ∫⁻ t, ‖B t‖ₑ * ‖f(x-t)‖ₑ`.
  have h_pointwise : ∀ x : Fin d → ℝ,
      ‖mollifiedApprox f ε x‖ₑ
        ≤ ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ
            ∂(volume : Measure (Fin d → ℝ)) := by
    intro x
    rw [hconv]
    -- Mathlib: convolution unfolds to `∫ t, L (B t) (f (x - t)) ∂volume`.
    change ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t))
              ∂(volume : Measure (Fin d → ℝ))‖ₑ ≤ _
    -- Then `lsmul` is just multiplication for real-valued functions.
    have h_simp : (fun t : Fin d → ℝ =>
        (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t)))
        = (fun t => B t * f (x - t)) := by
      funext t; simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [h_simp]
    -- Apply `enorm_integral_le_lintegral_enorm`, then `enorm_mul`.
    refine (MeasureTheory.enorm_integral_le_lintegral_enorm _).trans ?_
    refine MeasureTheory.lintegral_mono (fun t => ?_)
    rw [enorm_mul]
  -- Step 2: integrate the pointwise bound over the cube.
  refine (MeasureTheory.setLIntegral_mono ?_ (fun x _ => h_pointwise x)).trans ?_
  · -- Measurability of the RHS: `x ↦ ∫⁻ t, ‖B t‖ₑ * ‖f(x-t)‖ₑ`.
    -- The integrand is jointly measurable, then take lintegral in `t`.
    have hjoint : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        ‖B p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ) := by
      have h1 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖B p.2‖ₑ) :=
        (hB_meas.comp measurable_snd).enorm
      have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
          ‖f (p.1 - p.2)‖ₑ) :=
        (hf_meas.comp (measurable_fst.sub measurable_snd)).enorm
      exact h1.mul h2
    -- Now `lintegral_prod` reduces to a measurable function in the first variable.
    exact hjoint.lintegral_prod_right
  -- Step 3: swap the integrals and use periodic translation invariance of f.
  -- `∫⁻ x in cube, ∫⁻ t, ‖B t‖ₑ * ‖f(x-t)‖ₑ = ∫⁻ t, ‖B t‖ₑ * ∫⁻ x in cube, ‖f(x-t)‖ₑ`.
  -- The inner cube-lintegral equals `∫⁻ x in cube, ‖f x‖ₑ` by translation invariance.
  -- Then pull out the constant.
  have h_swap :
      ∫⁻ x in UnitCube d,
          (∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ∂(volume : Measure (Fin d → ℝ)))
          ∂(volume : Measure (Fin d → ℝ))
        = ∫⁻ t, ‖B t‖ₑ *
            (∫⁻ x in UnitCube d, ‖f (x - t)‖ₑ
              ∂(volume : Measure (Fin d → ℝ)))
            ∂(volume : Measure (Fin d → ℝ)) := by
    -- Reformulate the LHS as a setLIntegral on the product `cube × ℝ^d`.
    -- We use `lintegral_lintegral_swap` under the restricted measure on the
    -- first factor.
    rw [show (fun x : Fin d → ℝ =>
            ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ∂(volume : Measure (Fin d → ℝ)))
            = (fun x : Fin d → ℝ => ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ
                  ∂(volume : Measure (Fin d → ℝ))) from rfl]
    -- joint measurability of (x, t) ↦ ‖B t‖ₑ * ‖f (x - t)‖ₑ
    have hjoint : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        ‖B p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ) := by
      have h1 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖B p.2‖ₑ) :=
        (hB_meas.comp measurable_snd).enorm
      have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
          ‖f (p.1 - p.2)‖ₑ) :=
        (hf_meas.comp (measurable_fst.sub measurable_snd)).enorm
      exact h1.mul h2
    -- Swap, then pull `‖B t‖ₑ` out of the inner integral.
    rw [MeasureTheory.lintegral_lintegral_swap
      (μ := (volume : Measure (Fin d → ℝ)).restrict (UnitCube d))
      (ν := (volume : Measure (Fin d → ℝ)))
      (f := fun x t => ‖B t‖ₑ * ‖f (x - t)‖ₑ)
      (hjoint.aemeasurable
        (μ := ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)).prod
                (volume : Measure (Fin d → ℝ))))]
    refine lintegral_congr (fun t => ?_)
    -- Pull the constant `‖B t‖ₑ` out of the inner setLIntegral.
    have hmeas_inner : Measurable (fun x : Fin d → ℝ => ‖f (x - t)‖ₑ) :=
      (hf_meas.comp (measurable_id.sub_const t)).enorm
    exact MeasureTheory.lintegral_const_mul _ hmeas_inner
  rw [h_swap]
  -- Step 4: the inner cube-lintegral of `‖f(· - t)‖ₑ` is independent of `t`,
  -- by periodic translation invariance.
  have hper_enorm : IsPeriodic (fun x : Fin d → ℝ => ‖f x‖ₑ) := by
    intro k x
    change ‖f (x + fun i => (k i : ℝ))‖ₑ = ‖f x‖ₑ
    rw [hf_per k x]
  have h_translation : ∀ t : Fin d → ℝ,
      ∫⁻ x in UnitCube d, ‖f (x - t)‖ₑ
          ∂(volume : Measure (Fin d → ℝ))
        = ∫⁻ x in UnitCube d, ‖f x‖ₑ
            ∂(volume : Measure (Fin d → ℝ)) :=
    fun t => lintegral_unitCube_translate_eq_sub (g := fun x => ‖f x‖ₑ)
      hper_enorm t
  -- Replace the inner integral by the constant `∫⁻_cube ‖f‖ₑ`.
  rw [show (fun t : Fin d → ℝ =>
          ‖B t‖ₑ * ∫⁻ x in UnitCube d, ‖f (x - t)‖ₑ
                    ∂(volume : Measure (Fin d → ℝ)))
        = (fun t : Fin d → ℝ =>
          ‖B t‖ₑ * ∫⁻ x in UnitCube d, ‖f x‖ₑ
                    ∂(volume : Measure (Fin d → ℝ))) from
        funext (fun t => by rw [h_translation t])]
  -- Pull the constant out and rearrange to the desired RHS shape.
  rw [MeasureTheory.lintegral_mul_const _ hB_meas.enorm]

/-! ## Young's L^p convolution inequality on the torus

The general `1 ≤ p < ∞` case of Young's inequality for the periodic
mollifier. The proof proceeds by Hölder/Jensen on the inner convolution
integrand, then Tonelli + periodic translation invariance.

-- Adapted from LpSpaces.YoungConvolution (whole-space L¹ × L^p version).
-- We bypass the Minkowski integral inequality used there in favour of a
-- direct Hölder split via `ENNReal.lintegral_mul_norm_pow_le`.
-/

/-- **Hölder/Jensen helper.** For `B, h : α → ℝ≥0∞` AE-measurable and
real `p ≥ 1`,
`(∫⁻ B(t) h(t) dt)^p ≤ (∫⁻ B(t) dt)^(p-1) * ∫⁻ B(t) h(t)^p dt`.
This is the integral form of Jensen's inequality for the (sub)probability
kernel `B`; the `p = 1` case is trivial. -/
private lemma lintegral_mul_pow_le_pow_lintegral_mul_pow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {B h : α → ℝ≥0∞} (hB : AEMeasurable B μ) (hh : AEMeasurable h μ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ a, B a * h a ∂μ) ^ p
      ≤ (∫⁻ a, B a ∂μ) ^ (p - 1) * ∫⁻ a, B a * (h a) ^ p ∂μ := by
  -- Reduce trivially at `p = 1`.
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · -- `p = 1` case: both sides equal `∫⁻ B h`.
    subst hp1
    simp
  -- Now `1 < p`. Set the splitting exponents.
  have hp_pos : 0 < p := lt_trans one_pos hp1
  have hp_ne : p ≠ 0 := hp_pos.ne'
  set α₁ : ℝ := 1 - 1 / p with hα₁_def
  set α₂ : ℝ := 1 / p with hα₂_def
  have hα₂_pos : 0 < α₂ := by
    change 0 < 1 / p; positivity
  have hα₁_pos : 0 < α₁ := by
    change 0 < 1 - 1 / p
    have : 1 / p < 1 := by
      rw [div_lt_one hp_pos]; exact hp1
    linarith
  have hα₁_nn : 0 ≤ α₁ := hα₁_pos.le
  have hα₂_nn : 0 ≤ α₂ := hα₂_pos.le
  have hα_sum : α₁ + α₂ = 1 := by
    change (1 - 1 / p) + 1 / p = 1; ring
  -- Define `u := B` and `v := B · h^p`.
  set u : α → ℝ≥0∞ := B with hu_def
  set v : α → ℝ≥0∞ := fun a => B a * (h a) ^ p with hv_def
  have hu_meas : AEMeasurable u μ := hB
  have hv_meas : AEMeasurable v μ := hB.mul (hh.pow_const p)
  -- Hölder-Jensen: `∫⁻ u^α₁ * v^α₂ ≤ (∫⁻ u)^α₁ * (∫⁻ v)^α₂`.
  have hHolder := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ) (f := u) (g := v) hu_meas hv_meas hα₁_nn hα₂_nn hα_sum
  -- Identify the LHS of `hHolder` with `∫⁻ B h`.
  -- `u(a)^α₁ * v(a)^α₂ = B(a)^(1-1/p) * (B(a) h(a)^p)^(1/p) = B(a) * h(a)`.
  have h_pα₁ : p * α₁ = p - 1 := by
    change p * (1 - 1 / p) = p - 1
    field_simp
  have h_pα₂ : p * α₂ = 1 := by
    change p * (1 / p) = 1
    field_simp
  have h_α₁_α₂_eq : ∀ a : α, (B a) ^ α₁ * (v a) ^ α₂ = B a * h a := by
    intro a
    change (B a) ^ α₁ * (B a * (h a) ^ p) ^ α₂ = B a * h a
    rw [ENNReal.mul_rpow_of_nonneg _ _ hα₂_nn]
    rw [show (B a) ^ α₁ * ((B a) ^ α₂ * ((h a) ^ p) ^ α₂)
            = ((B a) ^ α₁ * (B a) ^ α₂) * ((h a) ^ p) ^ α₂ from by ring]
    rw [← ENNReal.rpow_add_of_nonneg α₁ α₂ hα₁_nn hα₂_nn, hα_sum,
        ENNReal.rpow_one,
        ← ENNReal.rpow_mul, h_pα₂, ENNReal.rpow_one]
  have h_lhs_eq : (∫⁻ a, (u a) ^ α₁ * (v a) ^ α₂ ∂μ) = ∫⁻ a, B a * h a ∂μ := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun a => ?_)
    exact h_α₁_α₂_eq a
  rw [h_lhs_eq] at hHolder
  -- Now raise both sides of `hHolder` to power `p` to clear the `^α_i` on the RHS.
  have h_pow := ENNReal.rpow_le_rpow hHolder hp_pos.le
  -- Decompose the RHS power.
  have h_rhs_decomp :
      ((∫⁻ a, u a ∂μ) ^ α₁ * (∫⁻ a, v a ∂μ) ^ α₂) ^ p
        = (∫⁻ a, B a ∂μ) ^ (p - 1) * ∫⁻ a, B a * (h a) ^ p ∂μ := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_comm α₁ p, mul_comm α₂ p, h_pα₁, h_pα₂, ENNReal.rpow_one]
  rw [h_rhs_decomp] at h_pow
  exact h_pow

/-- **Young's convolution inequality, general `1 ≤ p < ∞` case, on the torus.**
For `B = bumpKernel d ε hε` (smooth, compactly supported, non-negative) and
periodic measurable real-valued `f` with `MemLpPer p f`,

`eLpNormPer p (B ⋆ f) ≤ (∫⁻ x, ‖B x‖ₑ) * eLpNormPer p f`.

The proof reduces the `p`-th power of the cube `lintegral` of `‖B ⋆ f‖ₑ`
to `(∫⁻ ‖B‖)^p` times the `p`-th power of `eLpNormPer p f`, via:
1. Pointwise bound `‖(B⋆f) x‖ₑ ≤ ∫⁻ t, ‖B t‖ₑ * ‖f(x-t)‖ₑ`.
2. Hölder/Jensen on the inner kernel-integral, taking `p`-th power.
3. Tonelli swap of cube/whole-space integrals.
4. Periodic translation invariance for the inner cube-lintegral. -/
theorem eLpNormPer_convolution_bumpKernel_le
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : Measurable f) (hf_per : IsPeriodic f)
    (_hf_mem : MemLpPer p f)
    {ε : ℝ} (hε : 0 < ε) :
    eLpNormPer p (mollifiedApprox f ε) ≤
      (∫⁻ t, ‖bumpKernel d ε hε t‖ₑ ∂(volume : Measure (Fin d → ℝ))) *
        eLpNormPer p f := by
  -- Handle the `p = 1` boundary case up front; only `1 < p < ∞` is new.
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · -- `p = 1` reduces to the L¹ case already proved.
    subst hp1
    exact eLpNormPer_convolution_bumpKernel_le_l1 hf_meas hf_per hε
  -- Now `1 < p`, and `p ≠ ∞`. Set `pr := p.toReal`.
  set B : (Fin d → ℝ) → ℝ := bumpKernel d ε hε with hB_def
  have hB_meas : Measurable B :=
    (bumpKernel_contDiff d ε hε).continuous.measurable
  set pr : ℝ := p.toReal with hpr_def
  have hp_ne_zero : p ≠ 0 := by
    intro h
    rw [h] at hp1
    exact absurd hp1 (by simp)
  have hpr_pos : 0 < pr := by
    rw [hpr_def]; exact ENNReal.toReal_pos hp_ne_zero hp_top
  have hpr_ge : 1 ≤ pr := by
    rw [hpr_def]
    have := ENNReal.toReal_mono hp_top hp1.le
    simpa using this
  have hconv : mollifiedApprox f ε
      = MeasureTheory.convolution B f
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Fin d → ℝ)) :=
    mollifiedApprox_eq_convolution f hε
  -- Step 1: pointwise bound `‖(B ⋆ f)(x)‖ₑ ≤ ∫⁻ t, ‖B t‖ₑ * ‖f(x-t)‖ₑ`.
  have h_pointwise : ∀ x : Fin d → ℝ,
      ‖mollifiedApprox f ε x‖ₑ
        ≤ ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ
            ∂(volume : Measure (Fin d → ℝ)) := by
    intro x
    rw [hconv]
    change ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t))
              ∂(volume : Measure (Fin d → ℝ))‖ₑ ≤ _
    have h_simp : (fun t : Fin d → ℝ =>
        (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t)))
        = (fun t => B t * f (x - t)) := by
      funext t; simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [h_simp]
    refine (MeasureTheory.enorm_integral_le_lintegral_enorm _).trans ?_
    refine MeasureTheory.lintegral_mono (fun t => ?_)
    rw [enorm_mul]
  -- Step 2: take pr-th power and apply Hölder-Jensen.
  have h_pow_pointwise : ∀ x : Fin d → ℝ,
      ‖mollifiedApprox f ε x‖ₑ ^ pr
        ≤ (∫⁻ t, ‖B t‖ₑ ∂(volume : Measure (Fin d → ℝ))) ^ (pr - 1)
            * ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ^ pr
              ∂(volume : Measure (Fin d → ℝ)) := by
    intro x
    have hB_aemeas : AEMeasurable (fun t : Fin d → ℝ => ‖B t‖ₑ)
        (volume : Measure (Fin d → ℝ)) := hB_meas.enorm.aemeasurable
    have hf_shift_aemeas : AEMeasurable (fun t : Fin d → ℝ => ‖f (x - t)‖ₑ)
        (volume : Measure (Fin d → ℝ)) :=
      ((hf_meas.comp (measurable_const.sub measurable_id)).enorm).aemeasurable
    have h_inner_le := lintegral_mul_pow_le_pow_lintegral_mul_pow
      (μ := (volume : Measure (Fin d → ℝ)))
      (B := fun t => ‖B t‖ₑ) (h := fun t => ‖f (x - t)‖ₑ)
      hB_aemeas hf_shift_aemeas hpr_ge
    -- The RHS of h_inner_le matches our goal once we have the pointwise bound.
    have h_lift : ‖mollifiedApprox f ε x‖ₑ ^ pr
        ≤ (∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ
              ∂(volume : Measure (Fin d → ℝ))) ^ pr :=
      ENNReal.rpow_le_rpow (h_pointwise x) hpr_pos.le
    exact h_lift.trans h_inner_le
  -- Step 3: integrate over the cube.
  have h_cube_bound :
      ∫⁻ x in UnitCube d, ‖mollifiedApprox f ε x‖ₑ ^ pr
        ∂(volume : Measure (Fin d → ℝ))
        ≤ (∫⁻ t, ‖B t‖ₑ ∂(volume : Measure (Fin d → ℝ))) ^ (pr - 1)
            * ∫⁻ x in UnitCube d, ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ^ pr
                ∂(volume : Measure (Fin d → ℝ))
              ∂(volume : Measure (Fin d → ℝ)) := by
    -- Bound the cube-lintegral pointwise then pull the constant out.
    have h_step :
        ∫⁻ x in UnitCube d, ‖mollifiedApprox f ε x‖ₑ ^ pr
          ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫⁻ x in UnitCube d,
              ((∫⁻ t, ‖B t‖ₑ ∂(volume : Measure (Fin d → ℝ))) ^ (pr - 1)
              * ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ^ pr
                ∂(volume : Measure (Fin d → ℝ)))
            ∂(volume : Measure (Fin d → ℝ)) :=
      MeasureTheory.lintegral_mono (fun x => h_pow_pointwise x)
    refine h_step.trans ?_
    have hjoint_inner : AEMeasurable (fun x : Fin d → ℝ =>
        ∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ^ pr ∂(volume : Measure (Fin d → ℝ)))
        ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)) := by
      have hjoint : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
          ‖B p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ ^ pr) := by
        have h1 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖B p.2‖ₑ) :=
          (hB_meas.comp measurable_snd).enorm
        have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
            ‖f (p.1 - p.2)‖ₑ ^ pr) :=
          ((hf_meas.comp (measurable_fst.sub measurable_snd)).enorm).pow_const pr
        exact h1.mul h2
      exact hjoint.lintegral_prod_right.aemeasurable
    rw [MeasureTheory.lintegral_const_mul'' _ hjoint_inner]
  -- Step 4: Tonelli swap and use periodic translation invariance.
  have h_swap :
      ∫⁻ x in UnitCube d,
        (∫⁻ t, ‖B t‖ₑ * ‖f (x - t)‖ₑ ^ pr ∂(volume : Measure (Fin d → ℝ)))
        ∂(volume : Measure (Fin d → ℝ))
        = ∫⁻ t, ‖B t‖ₑ *
            (∫⁻ x in UnitCube d, ‖f (x - t)‖ₑ ^ pr
              ∂(volume : Measure (Fin d → ℝ)))
            ∂(volume : Measure (Fin d → ℝ)) := by
    have hjoint : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        ‖B p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ ^ pr) := by
      have h1 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖B p.2‖ₑ) :=
        (hB_meas.comp measurable_snd).enorm
      have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
          ‖f (p.1 - p.2)‖ₑ ^ pr) :=
        ((hf_meas.comp (measurable_fst.sub measurable_snd)).enorm).pow_const pr
      exact h1.mul h2
    rw [MeasureTheory.lintegral_lintegral_swap
      (μ := (volume : Measure (Fin d → ℝ)).restrict (UnitCube d))
      (ν := (volume : Measure (Fin d → ℝ)))
      (f := fun x t => ‖B t‖ₑ * ‖f (x - t)‖ₑ ^ pr)
      (hjoint.aemeasurable
        (μ := ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)).prod
                (volume : Measure (Fin d → ℝ))))]
    refine lintegral_congr (fun t => ?_)
    have hmeas_inner : Measurable (fun x : Fin d → ℝ => ‖f (x - t)‖ₑ ^ pr) :=
      ((hf_meas.comp (measurable_id.sub_const t)).enorm).pow_const pr
    exact MeasureTheory.lintegral_const_mul _ hmeas_inner
  -- Use periodic translation to drop the `(· - t)` from the inner cube-lintegral.
  have hper_pow : IsPeriodic (fun x : Fin d → ℝ => ‖f x‖ₑ ^ pr) := by
    intro k x
    change ‖f (x + fun i => (k i : ℝ))‖ₑ ^ pr = ‖f x‖ₑ ^ pr
    rw [hf_per k x]
  have h_translate : ∀ t : Fin d → ℝ,
      ∫⁻ x in UnitCube d, ‖f (x - t)‖ₑ ^ pr
          ∂(volume : Measure (Fin d → ℝ))
        = ∫⁻ x in UnitCube d, ‖f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ)) := fun t =>
    lintegral_unitCube_translate_eq_sub (g := fun x => ‖f x‖ₑ ^ pr) hper_pow t
  -- Step 5: assemble.
  -- First, rewrite the cube bound using h_swap and h_translate.
  rw [h_swap] at h_cube_bound
  have h_inner_const :
      (fun t : Fin d → ℝ =>
          ‖B t‖ₑ * ∫⁻ x in UnitCube d, ‖f (x - t)‖ₑ ^ pr
                  ∂(volume : Measure (Fin d → ℝ)))
        = (fun t : Fin d → ℝ =>
          ‖B t‖ₑ * ∫⁻ x in UnitCube d, ‖f x‖ₑ ^ pr
                  ∂(volume : Measure (Fin d → ℝ))) :=
    funext (fun t => by rw [h_translate t])
  rw [h_inner_const] at h_cube_bound
  rw [MeasureTheory.lintegral_mul_const _ hB_meas.enorm] at h_cube_bound
  -- Now `h_cube_bound`:
  --   ∫⁻ x in cube, ‖(B⋆f) x‖ₑ^pr
  --     ≤ (∫⁻ B)^(pr-1) * ((∫⁻ B) * (∫⁻ x in cube, ‖f x‖ₑ^pr))
  -- Massage the RHS to `(∫⁻ B)^pr * (∫⁻_cube ‖f‖ₑ^pr)`.
  set Bint : ℝ≥0∞ := ∫⁻ t, ‖B t‖ₑ ∂(volume : Measure (Fin d → ℝ)) with hBint_def
  have h_combine :
      Bint ^ (pr - 1) * (Bint * ∫⁻ x in UnitCube d, ‖f x‖ₑ ^ pr
                ∂(volume : Measure (Fin d → ℝ)))
      = Bint ^ pr * ∫⁻ x in UnitCube d, ‖f x‖ₑ ^ pr
              ∂(volume : Measure (Fin d → ℝ)) := by
    have hpr_sub_nn : 0 ≤ pr - 1 := by linarith
    have hsplit : Bint ^ pr = Bint ^ (pr - 1) * Bint := by
      have := ENNReal.rpow_add_of_nonneg (x := Bint) (pr - 1) 1 hpr_sub_nn zero_le_one
      rw [show (pr - 1 + 1 : ℝ) = pr from by ring] at this
      rw [this, ENNReal.rpow_one]
    rw [hsplit, mul_assoc]
  rw [h_combine] at h_cube_bound
  -- Now turn `h_cube_bound` into the statement on `eLpNormPer`.
  -- `eLpNormPer p g = (∫⁻_cube ‖g‖ₑ^pr)^(1/pr)`.
  have h_unfold_conv :
      eLpNormPer (d := d) p (mollifiedApprox f ε)
        = (∫⁻ x in UnitCube d, ‖mollifiedApprox f ε x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ))) ^ (1 / pr) := by
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top
      (mollifiedApprox_aestronglyMeasurable hf_meas.aestronglyMeasurable hε).restrict]
  have h_unfold_f :
      eLpNormPer (d := d) p f
        = (∫⁻ x in UnitCube d, ‖f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ))) ^ (1 / pr) := by
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top
      hf_meas.aestronglyMeasurable]
  rw [h_unfold_conv]
  -- Apply rpow monotonicity (with exponent `1/pr > 0`).
  have h_one_div_pos : 0 < 1 / pr := by positivity
  refine (ENNReal.rpow_le_rpow h_cube_bound h_one_div_pos.le).trans ?_
  -- Now massage the RHS.
  rw [ENNReal.mul_rpow_of_nonneg _ _ h_one_div_pos.le,
      ← ENNReal.rpow_mul, mul_one_div, div_self hpr_pos.ne', ENNReal.rpow_one,
      h_unfold_f]

/-! ## Differentiation commutes with convolution: the Mathlib half

For the smooth compactly-supported bump kernel `B = bumpKernel d ε hε`
and a periodic locally-integrable `f`, the classical partial derivative
of the mollified approximation `B ⋆ f` in coordinate `i` equals the
convolution of the partial derivative of the kernel with `f`:

`∂_i (B ⋆ f)(x) = ((∂_i B) ⋆ f)(x)`.

This is the half of `weakDeriv_mollifiedApprox` that does **not** use
the weak derivative — it follows from
`HasCompactSupport.hasFDerivAt_convolution_left`.

-- Adapted from Mathlib's `HasCompactSupport.hasFDerivAt_convolution_left`;
-- specialised to our compactly-supported `bumpKernel`.
-/

/-- The partial derivative of `bumpKernel d ε hε` in any coordinate has
compact support. The full Frechet derivative inherits compact support
from the kernel itself, and the partial derivative is the evaluation of
the Frechet derivative on a constant basis vector. -/
lemma bumpKernel_partialDeriv_hasCompactSupport
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    HasCompactSupport
      (fun t : Fin d → ℝ => fderiv ℝ (bumpKernel d ε hε) t
        (Pi.basisFun ℝ (Fin d) i)) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ)
    (bumpKernel_hasCompactSupport d ε hε) (Pi.basisFun ℝ (Fin d) i)

/-- Opaque alias for the partial derivative of `bumpKernel d ε hε` in
coordinate `i`. Wrapping it in a non-reducible `def` keeps the
statement of `partialDeriv_mollifiedApprox_eq_convolution_partialKernel`
small enough to elaborate without exhausting heartbeats on the
`fderiv`/`Pi.basisFun`/`precompL` cascade. -/
noncomputable def partialKernel (d : ℕ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    (Fin d → ℝ) → ℝ :=
  fun t => fderiv ℝ (bumpKernel d ε hε) t (Pi.basisFun ℝ (Fin d) i)

lemma partialKernel_def (d : ℕ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    partialKernel d ε hε i =
      (fun t : Fin d → ℝ =>
        fderiv ℝ (bumpKernel d ε hε) t (Pi.basisFun ℝ (Fin d) i)) := rfl

lemma partialKernel_hasCompactSupport
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    HasCompactSupport (partialKernel d ε hε i) :=
  bumpKernel_partialDeriv_hasCompactSupport d ε hε i

lemma partialKernel_continuous
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    Continuous (partialKernel d ε hε i) := by
  -- `fderiv ℝ B` is continuous since `B` is `C^∞`; evaluation at a fixed
  -- vector is continuous.
  have hB : ContDiff ℝ ((⊤ : ℕ∞)) (bumpKernel d ε hε) :=
    bumpKernel_contDiff d ε hε
  have hB1 : ContDiff ℝ ((1 : ℕ∞)) (bumpKernel d ε hε) :=
    hB.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hcont_fderiv : Continuous (fderiv ℝ (bumpKernel d ε hε)) :=
    hB1.continuous_fderiv (by norm_num)
  -- Apply the continuous evaluation `L ↦ L (e_i)`.
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.basisFun ℝ (Fin d) i)).continuous.comp
    hcont_fderiv

set_option maxHeartbeats 800000 in
-- The statement involves `(fderiv B ⋆[L.precompL G] f) x`, whose elaboration
-- exhausts the default heartbeat budget on the `precompL` instance cascade.
/-- The Frechet-derivative version: at every `x`, the mollified
approximation `B ⋆ f` has Frechet derivative equal to the convolution
of `fderiv ℝ B` with `f` (using `L.precompL G`). Direct application of
`HasCompactSupport.hasFDerivAt_convolution_left`. -/
lemma mollifiedApprox_hasFDerivAt
    {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    HasFDerivAt (mollifiedApprox f ε)
      ((MeasureTheory.convolution (fderiv ℝ (bumpKernel d ε hε)) f
          ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Fin d → ℝ))
          MeasureTheory.volume) x) x := by
  rw [mollifiedApprox_eq_convolution f hε]
  have hB_compact : HasCompactSupport (bumpKernel d ε hε) :=
    bumpKernel_hasCompactSupport d ε hε
  have hB_smooth : ContDiff ℝ ((⊤ : ℕ∞)) (bumpKernel d ε hε) :=
    bumpKernel_contDiff d ε hε
  have hB1 : ContDiff ℝ ((1 : ℕ∞)) (bumpKernel d ε hε) :=
    hB_smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact hB_compact.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hB1 hf x

-- Integrability of the precompL-convolution integrand is proved inline in
-- the headline theorem below; pulling it into a separate lemma triggered
-- whnf timeout on the type elaboration.

set_option maxHeartbeats 800000 in
-- The proof internally elaborates `(fderiv B ⋆[L.precompL G] f) x` via the
-- `mollifiedApprox_hasFDerivAt` step and the `convolutionExists_left`
-- integrability hypothesis; both are heartbeat-heavy.
/-- **Headline equality (Mathlib half).** The partial derivative in
coordinate `i` of the mollified approximation `B ⋆ f` equals the
convolution of the partial derivative of the kernel with `f`:
`(∂_i (B ⋆ f))(x) = ((∂_i B) ⋆ f)(x)`.

The RHS is stated using the opaque alias `partialKernel d ε hε i` to
keep the goal type cheap to elaborate. -/
theorem partialDeriv_mollifiedApprox_eq_convolution_partialKernel
    {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    {ε : ℝ} (hε : 0 < ε) (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ (mollifiedApprox f ε) x (Pi.basisFun ℝ (Fin d) i)
      = MeasureTheory.convolution (partialKernel d ε hε i) f
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
  -- 1. The Frechet derivative is the convolution-with-precompL.
  have hfderiv := (mollifiedApprox_hasFDerivAt hf hε x).fderiv
  rw [hfderiv]
  -- 2. Integrability of the precompL convolution integrand at `x`.
  have hfderiv_compact : HasCompactSupport (fderiv ℝ (bumpKernel d ε hε)) :=
    (bumpKernel_hasCompactSupport d ε hε).fderiv ℝ
  have hB_smooth : ContDiff ℝ ((⊤ : ℕ∞)) (bumpKernel d ε hε) :=
    bumpKernel_contDiff d ε hε
  have hB1' : ContDiff ℝ ((1 : ℕ∞)) (bumpKernel d ε hε) :=
    hB_smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hfderiv_cont : Continuous (fderiv ℝ (bumpKernel d ε hε)) :=
    hB1'.continuous_fderiv (by norm_num)
  have hint := hfderiv_compact.convolutionExists_left
    (L := ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Fin d → ℝ)))
    hfderiv_cont hf x
  -- LHS now: `((fderiv B ⋆[L.precompL G] f) x) (e_i)`.
  -- Unfold the convolution and pass the application inside the integral.
  change ((∫ t,
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Fin d → ℝ))
        (fderiv ℝ (bumpKernel d ε hε) t) (f (x - t))
      ∂(MeasureTheory.volume : Measure (Fin d → ℝ)))
      : (Fin d → ℝ) →L[ℝ] ℝ) (Pi.basisFun ℝ (Fin d) i) = _
  rw [ContinuousLinearMap.integral_apply hint]
  -- 3. Identify the integrand with the partial-kernel convolution integrand.
  -- Goal: `∫ t, (precompL ...) (fderiv B t) (f (x - t)) (e_i)
  --        = ∫ t, lsmul ℝ ℝ (partialKernel ... t) (f (x - t))`.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  -- Pointwise: `precompL_apply` gives
  --   `precompL G L u f g = L (u g) f`,
  -- so the LHS is `lsmul ℝ ℝ ((fderiv B t) (e_i)) (f (x - t))`,
  -- which is exactly the partial-kernel convolution integrand.
  rfl

/-! ### Sample example exercising the bound at `p = 2`. -/

/-- Sample example: the constant `0` periodic function (which is in every
`MemLpPer p`) satisfies the Young L^p bound at `p = 2`. -/
example {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    eLpNormPer (d := d) 2 (mollifiedApprox (fun _ => (0 : ℝ)) ε) ≤
      (∫⁻ t, ‖bumpKernel d ε hε t‖ₑ ∂(volume : Measure (Fin d → ℝ))) *
        eLpNormPer 2 (fun _ : Fin d → ℝ => (0 : ℝ)) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    decide
  have hcube : volume (UnitCube d) ≠ ⊤ := by simp
  have hfin : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  exact eLpNormPer_convolution_bumpKernel_le hp hp_top
    (f := fun _ : Fin d → ℝ => (0 : ℝ)) measurable_const (IsPeriodic.const _)
    (MemLp.toMemLpPer (memLp_const _)) hε

/-! ## `L^p_per` convergence of the periodic mollifier

The headline theorem: `‖B_ε ⋆ f − f‖_{L^p_per} → 0` as `ε → 0⁺`, for
`MemLpPer p f` and periodic `f` with `1 ≤ p < ∞`.

The proof uses three ingredients all in this codebase:

1. The bump kernel has total mass `1` (`lintegral_bumpKernel_eq_one` below),
   built by Fubini on the tensor product and `ContDiffBump.integral_normed`.
2. Young's `L^p` convolution inequality on the torus
   (`eLpNormPer_convolution_bumpKernel_le`).
3. Translation continuity in `L^p_per`
   (`tendsto_eLpNormPer_translation_sub` from `Periodic/Translation.lean`).

The combinatorial step is a Hölder/Jensen-style bound on
`‖(B ⋆ f)(x) − f(x)‖ₑ^p` using the existing private helper
`lintegral_mul_pow_le_pow_lintegral_mul_pow`, followed by Tonelli + the
periodic translation invariance.

-- Adapted from LpSpaces.Mollification (whole-space version); the
-- periodic adaptation reuses Young + translation continuity directly,
-- avoiding the separate truncation by `C_c`.
-/

/-! ### Total mass of the bump kernel -/

/-- The 1D normalised bump integrates to `1` over Lebesgue. -/
private lemma integral_auxNormedBump1D (ε : ℝ) (hε : 0 < ε) :
    ∫ y, palomar_Mollifier_auxNormedBump1D ε hε y ∂(volume : Measure ℝ) = 1 :=
  (palomar_Mollifier_auxBump1D ε hε).integral_normed

/-- The d-dim bump kernel integrates to `1` over `(Fin d → ℝ)`. -/
lemma integral_bumpKernel_eq_one (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∫ t, bumpKernel d ε hε t ∂(volume : Measure (Fin d → ℝ)) = 1 := by
  -- Tensor product: ∫ ∏ i, η₁(t i) = ∏ i, ∫ η₁ = 1^d = 1.
  unfold bumpKernel
  rw [show (volume : Measure (Fin d → ℝ)) =
        Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi]
  rw [integral_fintype_prod_eq_prod
        (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
        (fun _ y => palomar_Mollifier_auxNormedBump1D ε hε y)
        (μ := fun _ => (volume : Measure ℝ))]
  simp [integral_auxNormedBump1D ε hε]

/-- Total `ℝ≥0∞` mass of the bump kernel: `∫⁻ ‖B t‖ₑ = 1`. -/
lemma lintegral_enorm_bumpKernel_eq_one (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ t, ‖bumpKernel d ε hε t‖ₑ ∂(volume : Measure (Fin d → ℝ)) = 1 := by
  have hnn : ∀ t, 0 ≤ bumpKernel d ε hε t := bumpKernel_nonneg d ε hε
  have hint : Integrable (bumpKernel d ε hε) (volume : Measure (Fin d → ℝ)) := by
    refine (bumpKernel_contDiff d ε hε).continuous.integrable_of_hasCompactSupport ?_
    exact bumpKernel_hasCompactSupport d ε hε
  have hstep : (fun t => ‖bumpKernel d ε hε t‖ₑ)
      = (fun t => ENNReal.ofReal (bumpKernel d ε hε t)) := by
    funext t; rw [Real.enorm_of_nonneg (hnn t)]
  rw [hstep, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hnn),
      integral_bumpKernel_eq_one d ε hε, ENNReal.ofReal_one]

/-! ### Support of the bump kernel inside the sup-norm ball -/

/-- The bump kernel vanishes outside the closed sup-norm ball of radius `ε`.
The norm on `Fin d → ℝ` is the sup norm `max_i |x i|`. -/
lemma bumpKernel_eq_zero_of_norm_ge {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {t : Fin d → ℝ} (ht : ε ≤ ‖t‖) :
    bumpKernel d ε hε t = 0 := by
  -- ‖t‖ ≥ ε on the Pi sup norm ⇒ some coordinate has `|t i| ≥ ε`.
  by_contra hne
  have hsupp : t ∈ Function.support (bumpKernel d ε hε) := hne
  -- Negate: if `∀ i, |t i| < ε`, then `‖t‖ < ε`, contradiction with `ε ≤ ‖t‖`.
  by_cases h : ∀ i, |t i| < ε
  · -- ‖t‖ ≤ ε would suffice (then `ε ≤ ‖t‖ ≤ ε` and `|t i| < ε` for all i is fine,
    -- but we need a strict bound to contradict). Use `pi_norm_lt_iff` style.
    have hbound_le : ∀ i, ‖t i‖ ≤ ε := fun i => (h i).le
    have hnorm_le : ‖t‖ ≤ ε := (pi_norm_le_iff_of_nonneg hε.le).mpr hbound_le
    -- Now ε ≤ ‖t‖ ≤ ε, so ‖t‖ = ε. We need to refine: ∀ i, |t i| < ε ⇒ ‖t‖ < ε.
    -- The pi sup norm equals max over (finite, nonempty) set; if all entries < ε,
    -- the max < ε. This holds when `Fin d` is nonempty.
    have hbound_lt : ∀ i, ‖t i‖ < ε := fun i => h i
    have hnorm_lt : ‖t‖ < ε := (pi_norm_lt_iff hε).mpr hbound_lt
    exact (not_lt.mpr ht hnorm_lt).elim
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact hne (bumpKernel_eq_zero_of_exists_abs_ge d ε hε ⟨i, hi⟩)

/-! ### Pointwise identity for `(B ⋆ f) - f`

For the compactly-supported smooth bump kernel `B = bumpKernel d ε hε`,
locally integrable `f`, and any `x`,

`(B ⋆ f) x − f x = ∫ t, B t * (f (x - t) − f x) ∂volume`,

via `∫ B = 1` and integrability of `t ↦ B t * f (x - t)` (from
`HasCompactSupport.convolutionExists_left`) and `t ↦ B t * f x` (constant
times integrable).

-- Adapted from LpSpaces.Mollification (whole-space pointwise identity).
-/

/-- **Pointwise identity for `(B ⋆ f)(x) − f(x)`.**

For `B = bumpKernel d ε hε` and locally-integrable real-valued `f`,

`mollifiedApprox f ε x − f x = ∫ t, B t * (f (x − t) − f x) ∂volume`. -/
theorem mollifiedApprox_sub_eq_integral_translate_sub
    {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f (volume : Measure (Fin d → ℝ)))
    {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    mollifiedApprox f ε x - f x
      = ∫ t, bumpKernel d ε hε t * (f (x - t) - f x)
          ∂(volume : Measure (Fin d → ℝ)) := by
  set B : (Fin d → ℝ) → ℝ := bumpKernel d ε hε with hB_def
  have hB_cont : Continuous B := (bumpKernel_contDiff d ε hε).continuous
  have hB_compact : HasCompactSupport B := bumpKernel_hasCompactSupport d ε hε
  -- Integrability of `t ↦ B t * f (x - t)`.
  have hint1 : Integrable (fun t : Fin d → ℝ => B t * f (x - t))
      (volume : Measure (Fin d → ℝ)) := by
    have hex : MeasureTheory.ConvolutionExistsAt B f x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Fin d → ℝ)) :=
      hB_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hB_cont hf x
    -- `ConvolutionExistsAt B f x L μ` unfolds to `Integrable (fun t => L (B t) (f (x - t)))`.
    have hex' : Integrable (fun t : Fin d → ℝ =>
        (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t)))
        (volume : Measure (Fin d → ℝ)) := hex
    have hsimp : (fun t : Fin d → ℝ =>
          (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t)))
        = (fun t => B t * f (x - t)) := by
      funext t; simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [hsimp] at hex'
    exact hex'
  -- Integrability of `t ↦ B t * f x` (constant times integrable bump).
  have hB_int : Integrable B (volume : Measure (Fin d → ℝ)) :=
    hB_cont.integrable_of_hasCompactSupport hB_compact
  have hint2 : Integrable (fun t : Fin d → ℝ => B t * f x)
      (volume : Measure (Fin d → ℝ)) := hB_int.mul_const (f x)
  -- Compute `(B ⋆ f) x` directly.
  have hconv : mollifiedApprox f ε x = ∫ t, B t * f (x - t)
      ∂(volume : Measure (Fin d → ℝ)) := by
    rw [mollifiedApprox_eq_convolution f hε]
    change (∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (B t) (f (x - t))
          ∂(volume : Measure (Fin d → ℝ))) = _
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- Compute `∫ t, B t * f x = f x` from `∫ B = 1`.
  have hconst : (∫ t, B t * f x ∂(volume : Measure (Fin d → ℝ))) = f x := by
    rw [MeasureTheory.integral_mul_const, integral_bumpKernel_eq_one d ε hε,
        one_mul]
  -- Assemble using `integral_sub`.
  have hRHS : (∫ t, B t * (f (x - t) - f x)
          ∂(volume : Measure (Fin d → ℝ)))
        = (∫ t, B t * f (x - t) ∂(volume : Measure (Fin d → ℝ)))
            - ∫ t, B t * f x ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← MeasureTheory.integral_sub hint1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    ring
  rw [hRHS, ← hconv, hconst]

/-- **Pointwise enorm bound for `(B ⋆ f)(x) − f(x)`.**

Immediate from `mollifiedApprox_sub_eq_integral_translate_sub` and
`enorm_integral_le_lintegral_enorm`, using `‖B t * (f(x-t) - f x)‖ₑ
= ‖B t‖ₑ * ‖f(x-t) - f x‖ₑ`. -/
theorem enorm_mollifiedApprox_sub_le_lintegral
    {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f (volume : Measure (Fin d → ℝ)))
    {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) :
    ‖mollifiedApprox f ε x - f x‖ₑ
      ≤ ∫⁻ t, ‖bumpKernel d ε hε t‖ₑ * ‖f (x - t) - f x‖ₑ
          ∂(volume : Measure (Fin d → ℝ)) := by
  rw [mollifiedApprox_sub_eq_integral_translate_sub hf hε x]
  refine (MeasureTheory.enorm_integral_le_lintegral_enorm _).trans ?_
  refine MeasureTheory.lintegral_mono (fun t => ?_)
  rw [enorm_mul]

/-! ### Jensen + Tonelli `L^p_per` bound on `(B ⋆ f) − f`

For the compactly-supported smooth bump kernel `B = bumpKernel d ε hε`
and periodic measurable real-valued `f` with `MemLpPer p f`,

`(eLpNormPer p ((B ⋆ f) − f))^p ≤ ∫⁻ t, ‖B t‖ₑ * (eLpNormPer p (f(· - t) − f))^p`.

This is the Jensen + Tonelli step that reduces mollifier-difference
control to translation-difference control. The proof mirrors
`eLpNormPer_convolution_bumpKernel_le` (lines 678-872 of this file)
but applied to the *difference* via the pointwise identity
`mollifiedApprox_sub_eq_integral_translate_sub`. The total mass
`∫⁻ ‖B‖ₑ = 1` makes the `(∫⁻ B)^(p-1)` Jensen factor collapse to `1`.
-/

/-- **Jensen + Tonelli `L^p_per` bound on the convolution difference.**
For `1 ≤ p < ∞`, `MemLpPer p f`, `IsPeriodic f`, `0 < ε`,

`(eLpNormPer p (B⋆f − f))^p ≤ ∫⁻ t, ‖B t‖ₑ * (eLpNormPer p (f(·-t) − f))^p`.

Reduces mollifier-difference control to translation-difference control. -/
theorem eLpNormPer_pow_mollifiedApprox_sub_le
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : Measurable f)
    (hf_loc : MeasureTheory.LocallyIntegrable f (volume : Measure (Fin d → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    (eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ p.toReal
      ≤ ∫⁻ t, ‖bumpKernel d ε hε t‖ₑ
          * (eLpNormPer p (fun x => f (x - t) - f x)) ^ p.toReal
          ∂(volume : Measure (Fin d → ℝ)) := by
  set B : (Fin d → ℝ) → ℝ := bumpKernel d ε hε with hB_def
  have hB_meas : Measurable B :=
    (bumpKernel_contDiff d ε hε).continuous.measurable
  set pr : ℝ := p.toReal with hpr_def
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by simp)
  have hpr_pos : 0 < pr := by
    rw [hpr_def]; exact ENNReal.toReal_pos hp_ne_zero hp_top
  have hpr_ge : 1 ≤ pr := by
    rw [hpr_def]
    have := ENNReal.toReal_mono hp_top hp
    simpa using this
  -- Step 0: total mass of B is one.
  have hB_total_one :
      (∫⁻ t, ‖B t‖ₑ ∂(volume : Measure (Fin d → ℝ))) = 1 :=
    lintegral_enorm_bumpKernel_eq_one d ε hε
  -- Step 1: pointwise enorm bound on the difference.
  have h_pointwise : ∀ x : Fin d → ℝ,
      ‖mollifiedApprox f ε x - f x‖ₑ
        ≤ ∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ
            ∂(volume : Measure (Fin d → ℝ)) := fun x =>
    enorm_mollifiedApprox_sub_le_lintegral hf_loc hε x
  -- Step 2: take pr-th power and apply Jensen.
  have h_pow_pointwise : ∀ x : Fin d → ℝ,
      ‖mollifiedApprox f ε x - f x‖ₑ ^ pr
        ≤ ∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ)) := by
    intro x
    have hB_aemeas : AEMeasurable (fun t : Fin d → ℝ => ‖B t‖ₑ)
        (volume : Measure (Fin d → ℝ)) := hB_meas.enorm.aemeasurable
    have hf_shift_aemeas : AEMeasurable
        (fun t : Fin d → ℝ => ‖f (x - t) - f x‖ₑ)
        (volume : Measure (Fin d → ℝ)) := by
      refine Measurable.aemeasurable ?_
      exact ((hf_meas.comp (measurable_const.sub measurable_id)).sub
              measurable_const).enorm
    have h_jensen := lintegral_mul_pow_le_pow_lintegral_mul_pow
      (μ := (volume : Measure (Fin d → ℝ)))
      (B := fun t => ‖B t‖ₑ) (h := fun t => ‖f (x - t) - f x‖ₑ)
      hB_aemeas hf_shift_aemeas hpr_ge
    have h_lift : ‖mollifiedApprox f ε x - f x‖ₑ ^ pr
        ≤ (∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ
              ∂(volume : Measure (Fin d → ℝ))) ^ pr :=
      ENNReal.rpow_le_rpow (h_pointwise x) hpr_pos.le
    have h_rhs : (∫⁻ t, ‖B t‖ₑ ∂(volume : Measure (Fin d → ℝ))) ^ (pr - 1)
        * ∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ))
        = ∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ)) := by
      rw [hB_total_one, ENNReal.one_rpow, one_mul]
    exact h_lift.trans (h_jensen.trans h_rhs.le)
  -- Step 3: integrate over the cube.
  have hjoint : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      ‖B p.2‖ₑ * ‖f (p.1 - p.2) - f p.1‖ₑ ^ pr) := by
    have h1 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖B p.2‖ₑ) :=
      (hB_meas.comp measurable_snd).enorm
    have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        ‖f (p.1 - p.2) - f p.1‖ₑ ^ pr) :=
      (((hf_meas.comp (measurable_fst.sub measurable_snd)).sub
          (hf_meas.comp measurable_fst)).enorm).pow_const pr
    exact h1.mul h2
  have h_cube_bound :
      ∫⁻ x in UnitCube d, ‖mollifiedApprox f ε x - f x‖ₑ ^ pr
        ∂(volume : Measure (Fin d → ℝ))
        ≤ ∫⁻ x in UnitCube d,
            (∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
              ∂(volume : Measure (Fin d → ℝ)))
            ∂(volume : Measure (Fin d → ℝ)) :=
    MeasureTheory.lintegral_mono (fun x => h_pow_pointwise x)
  -- Step 4: Tonelli swap.
  have h_swap :
      ∫⁻ x in UnitCube d,
          (∫⁻ t, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ)))
          ∂(volume : Measure (Fin d → ℝ))
        = ∫⁻ t,
            (∫⁻ x in UnitCube d, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
              ∂(volume : Measure (Fin d → ℝ)))
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [MeasureTheory.lintegral_lintegral_swap
      (μ := (volume : Measure (Fin d → ℝ)).restrict (UnitCube d))
      (ν := (volume : Measure (Fin d → ℝ)))
      (f := fun x t => ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr)
      (hjoint.aemeasurable
        (μ := ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)).prod
                (volume : Measure (Fin d → ℝ))))]
  -- Step 5: pull `‖B t‖ₑ` outside the inner cube-lintegral.
  have h_pull : ∀ t : Fin d → ℝ,
      ∫⁻ x in UnitCube d, ‖B t‖ₑ * ‖f (x - t) - f x‖ₑ ^ pr
          ∂(volume : Measure (Fin d → ℝ))
        = ‖B t‖ₑ *
          ∫⁻ x in UnitCube d, ‖f (x - t) - f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ)) := by
    intro t
    have hmeas_inner : Measurable (fun x : Fin d → ℝ =>
        ‖f (x - t) - f x‖ₑ ^ pr) :=
      (((hf_meas.comp (measurable_id.sub_const t)).sub hf_meas).enorm).pow_const pr
    exact MeasureTheory.lintegral_const_mul _ hmeas_inner
  -- Step 6: identify the inner cube-lintegral with `(eLpNormPer p g_t)^pr`.
  have h_eLp_form : ∀ t : Fin d → ℝ,
      ∫⁻ x in UnitCube d, ‖f (x - t) - f x‖ₑ ^ pr
          ∂(volume : Measure (Fin d → ℝ))
        = (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr := by
    intro t
    unfold eLpNormPer
    have hmeas : AEStronglyMeasurable (fun x => f (x - t) - f x)
        (volume.restrict (UnitCube d)) := by
      simpa only [Function.comp_def, Pi.sub_def, id_eq] using
        ((hf_meas.comp (measurable_id.sub_const t)).sub hf_meas).aestronglyMeasurable
          (μ := volume.restrict (UnitCube d))
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hmeas]
    have h_one_div_pos : 0 < 1 / pr := by positivity
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr_pos.ne', ENNReal.rpow_one]
  -- Step 7: identify the LHS cube-lintegral with `(eLpNormPer p (B⋆f - f))^pr`.
  have h_eLp_lhs :
      (eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr
        = ∫⁻ x in UnitCube d, ‖mollifiedApprox f ε x - f x‖ₑ ^ pr
            ∂(volume : Measure (Fin d → ℝ)) := by
    unfold eLpNormPer
    have hmeas : AEStronglyMeasurable (fun x => mollifiedApprox f ε x - f x)
        (volume.restrict (UnitCube d)) := by
      simpa only [Pi.sub_def] using
        ((mollifiedApprox_aestronglyMeasurable hf_meas.aestronglyMeasurable hε).sub
          hf_meas.aestronglyMeasurable).restrict (s := UnitCube d)
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hmeas]
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr_pos.ne', ENNReal.rpow_one]
  -- Assemble.
  rw [h_eLp_lhs]
  refine h_cube_bound.trans ?_
  rw [h_swap]
  refine le_of_eq ?_
  refine lintegral_congr (fun t => ?_)
  rw [h_pull t, h_eLp_form t]

/-! ### Bare-hypotheses version: drop `Measurable f`

The `Measurable f` hypothesis in `eLpNormPer_pow_mollifiedApprox_sub_le`
is structural, used only to construct measurable composites under
`lintegral`. We can drop it by routing through a measurable representative
`f' := hf_aem.mk f` (where `hf_aem : AEStronglyMeasurable f volume` is
extracted from `LocallyIntegrable f volume`). Both sides of the
inequality are unchanged when `f` is replaced by `f'`:

* The LHS `eLpNormPer p (mollifiedApprox f ε − f)` equals
  `eLpNormPer p (mollifiedApprox f' ε − f')` because
  `mollifiedApprox f ε = mollifiedApprox f' ε` pointwise (by
  `convolution_congr`, since translation `t ↦ x − t` is measure-preserving
  on `volume`) and `f =ᵐ[volume.restrict (UnitCube d)] f'`.

* The RHS integrand `eLpNormPer p (f(· − t) − f(·))` equals
  `eLpNormPer p (f'(· − t) − f'(·))` for each `t`, again because
  translation is measure-preserving and `=ᵐ[volume]` restricts to the cube.

Hence applying the measurable form to `f'` and transferring back yields
the bare-hypotheses inequality on `f`. -/

/-- **Bare-hypotheses Jensen + Tonelli inequality.** Same as
`eLpNormPer_pow_mollifiedApprox_sub_le` but without the `Measurable f`
hypothesis. -/
theorem eLpNormPer_pow_mollifiedApprox_sub_le_bare
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_loc : MeasureTheory.LocallyIntegrable f (volume : Measure (Fin d → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    (eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ p.toReal
      ≤ ∫⁻ t, ‖bumpKernel d ε hε t‖ₑ
          * (eLpNormPer p (fun x => f (x - t) - f x)) ^ p.toReal
          ∂(volume : Measure (Fin d → ℝ)) := by
  -- Pick a strongly-measurable representative `f'` of `f`.
  have hf_aem : AEStronglyMeasurable f (volume : Measure (Fin d → ℝ)) :=
    hf_loc.aestronglyMeasurable
  set f' : (Fin d → ℝ) → ℝ := hf_aem.mk f with hf'_def
  have hae : f =ᵐ[(volume : Measure (Fin d → ℝ))] f' := hf_aem.ae_eq_mk
  have hf'_strong : StronglyMeasurable f' := hf_aem.stronglyMeasurable_mk
  have hf'_meas : Measurable f' := hf'_strong.measurable
  have hf'_loc : MeasureTheory.LocallyIntegrable f'
      (volume : Measure (Fin d → ℝ)) :=
    hf_loc.congr hae
  -- Both sides agree when we replace `f` by `f'`.
  -- Step A: pointwise equality `mollifiedApprox f ε = mollifiedApprox f' ε`
  -- via `convolution_congr`.
  have hmoll_eq : mollifiedApprox f ε = mollifiedApprox f' ε := by
    rw [mollifiedApprox_eq_convolution f hε,
        mollifiedApprox_eq_convolution f' hε]
    exact convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
      (Filter.EventuallyEq.refl _ _) hae
  -- Step B: `f =ᵐ[volume.restrict cube] f'`.
  have hae_cube : f =ᵐ[(volume : Measure (Fin d → ℝ)).restrict (UnitCube d)] f' :=
    hae.restrict
  -- Step C: LHS unchanged.
  have h_lhs :
      eLpNormPer p (fun x => mollifiedApprox f ε x - f x)
        = eLpNormPer p (fun x => mollifiedApprox f' ε x - f' x) := by
    unfold eLpNormPer
    refine MeasureTheory.eLpNorm_congr_ae ?_
    refine hae_cube.mono fun x hx => ?_
    change mollifiedApprox f ε x - f x = mollifiedApprox f' ε x - f' x
    rw [hmoll_eq, hx]
  -- Step D: RHS integrand unchanged for each `t`.
  -- Translation `x ↦ x - t` is measure-preserving on `volume`, so
  -- `(fun x => f(x-t)) =ᵐ[volume] (fun x => f'(x-t))`, which restricts
  -- to the cube measure.
  have h_rhs_eq : ∀ t : Fin d → ℝ,
      eLpNormPer p (fun x => f (x - t) - f x)
        = eLpNormPer p (fun x => f' (x - t) - f' x) := by
    intro t
    unfold eLpNormPer
    refine MeasureTheory.eLpNorm_congr_ae ?_
    -- Get a.e. equality on volume of `x ↦ f(x-t)` vs `x ↦ f'(x-t)` using
    -- the measure-preserving translation `x ↦ x - t`.
    have hmp_t : MeasureTheory.MeasurePreserving
        (fun x : Fin d → ℝ => x - t)
        (volume : Measure (Fin d → ℝ)) (volume : Measure (Fin d → ℝ)) :=
      MeasureTheory.measurePreserving_sub_right
        (volume : Measure (Fin d → ℝ)) t
    have hae_shift : (fun x : Fin d → ℝ => f (x - t))
        =ᵐ[(volume : Measure (Fin d → ℝ))] fun x => f' (x - t) :=
      hmp_t.quasiMeasurePreserving.ae_eq_comp hae
    -- Now restrict to the cube.
    have hae_shift_cube :
        (fun x : Fin d → ℝ => f (x - t))
          =ᵐ[(volume : Measure (Fin d → ℝ)).restrict (UnitCube d)]
        fun x => f' (x - t) := hae_shift.restrict
    exact hae_shift_cube.sub hae_cube
  -- Apply the measurable-form inequality to `f'`.
  have h_meas := eLpNormPer_pow_mollifiedApprox_sub_le (d := d) (p := p)
    hp hp_top hf'_meas hf'_loc (ε := ε) hε
  -- Transfer back.
  rw [h_lhs]
  refine h_meas.trans ?_
  refine le_of_eq ?_
  refine MeasureTheory.lintegral_congr (fun t => ?_)
  rw [h_rhs_eq t]

/-! ### Final convergence: `‖B ⋆ f − f‖_{L^p_per} → 0` as `ε ↘ 0`

The squeeze combines:

* the Jensen + Tonelli inequality
  `eLpNormPer_pow_mollifiedApprox_sub_le`,
* translation continuity `tendsto_eLpNormPer_translation_sub`, and
* support shrinkage of the bump kernel
  (`bumpKernel_eq_zero_of_norm_ge`).

Given `δ > 0`, by translation continuity pick `r > 0` with
`‖t‖ < r ⇒ eLpNormPer p (f(·−t) − f(·)) ≤ δ`. For `0 < ε < r`, the
bump kernel vanishes outside `‖t‖ < ε`, so the integrand of the
Jensen + Tonelli bound is `≤ ‖B t‖ₑ * δ^pr` everywhere. Using
`∫⁻ ‖B‖ₑ = 1`, the lintegral is bounded by `δ^pr`. Taking `pr`-th
roots concludes.

-- Adapted from LpSpaces.Mollification (whole-space final squeeze).
-/

/-- **`L^p_per` convergence of the periodic mollifier.**
For `1 ≤ p < ∞`, periodic `MemLpPer p f` with measurable, locally
integrable `f`,

`Tendsto (fun ε => eLpNormPer p (mollifiedApprox f ε − f))
  (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_lpNormPer_mollifiedApprox_sub
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : Measurable f)
    (hf_loc : MeasureTheory.LocallyIntegrable f (volume : Measure (Fin d → ℝ)))
    (hf_lp : MemLpPer p f) (hper : IsPeriodic f) :
    Tendsto (fun ε : ℝ => eLpNormPer p (fun x => mollifiedApprox f ε x - f x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by simp)
  set pr : ℝ := p.toReal with hpr_def
  have hpr_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_top
  have hpr_ge : 1 ≤ pr := by
    have := ENNReal.toReal_mono hp_top hp; simpa using this
  -- Translation continuity along `t ∈ Fin d → ℝ`.
  haveI : Fact (1 ≤ p) := ⟨hp⟩
  have htrans :
      Tendsto (fun y : Fin d → ℝ =>
        eLpNormPer p (fun x => f (x - y) - f x)) (𝓝 0) (𝓝 0) :=
    tendsto_eLpNormPer_translation_sub hp_top hf_lp hper
  -- Convert tendsto to: ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0, eLpNormPer ≤ δ.
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ_pos
  -- Replace δ by δ' := min δ 1 to keep things finite.
  set δ' : ℝ≥0∞ := min δ 1 with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos (by norm_num)
  have hδ'_le : δ' ≤ δ := min_le_left _ _
  have hδ'_le_one : δ' ≤ 1 := min_le_right _ _
  have hδ'_ne_top : δ' ≠ (⊤ : ℝ≥0∞) :=
    ne_of_lt (lt_of_le_of_lt hδ'_le_one ENNReal.one_lt_top)
  -- From `htrans`, find `r > 0` such that `‖y‖ < r` ⇒ eLpNormPer ≤ δ'.
  have h_evt :
      ∀ᶠ y : Fin d → ℝ in 𝓝 0,
        eLpNormPer p (fun x => f (x - y) - f x) ≤ δ' :=
    (ENNReal.tendsto_nhds_zero.mp htrans) δ' hδ'_pos
  rw [Metric.eventually_nhds_iff] at h_evt
  obtain ⟨r, hr_pos, hr⟩ := h_evt
  -- For `0 < ε < r`, all `t` with `bumpKernel d ε hε t ≠ 0` satisfy `‖t‖ < ε ≤ r`.
  -- Therefore the integrand `‖B t‖ₑ * eLpNormPer^pr ≤ ‖B t‖ₑ * δ^pr`.
  -- Choose the `Ioo (0, r)` neighbourhood of 0 in `𝓝[>] 0`.
  have h_nhds : Set.Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT hr_pos
  refine Filter.eventually_of_mem h_nhds ?_
  intro ε hε
  obtain ⟨hε_pos, hε_lt⟩ := hε
  -- The Jensen + Tonelli bound on `eLpNormPer^pr`.
  have h_jensen :=
    eLpNormPer_pow_mollifiedApprox_sub_le (d := d) (p := p) hp hp_top
      hf_meas hf_loc (ε := ε) hε_pos
  -- Bound the integrand pointwise by `‖B t‖ₑ * δ'^pr`.
  have h_int_bd :
      ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ
          * (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr
          ∂(volume : Measure (Fin d → ℝ))
        ≤ δ' ^ pr := by
    -- Pointwise: integrand ≤ ‖B t‖ₑ * δ'^pr.
    have h_ptwise : ∀ t : Fin d → ℝ,
        ‖bumpKernel d ε hε_pos t‖ₑ
            * (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr
          ≤ ‖bumpKernel d ε hε_pos t‖ₑ * δ' ^ pr := by
      intro t
      by_cases ht : ε ≤ ‖t‖
      · -- bumpKernel vanishes here.
        have hzero : bumpKernel d ε hε_pos t = 0 :=
          bumpKernel_eq_zero_of_norm_ge hε_pos ht
        rw [hzero]
        simp
      · push_neg at ht
        have hdist : dist t (0 : Fin d → ℝ) < r := by
          rw [dist_zero_right]; exact lt_trans ht hε_lt
        have h_le : eLpNormPer p (fun x => f (x - t) - f x) ≤ δ' := hr hdist
        exact mul_le_mul_right (ENNReal.rpow_le_rpow h_le hpr_pos.le) _
    have h_lint_le :
        ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ
              * (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr
            ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ * δ' ^ pr
            ∂(volume : Measure (Fin d → ℝ)) :=
      MeasureTheory.lintegral_mono h_ptwise
    -- ∫⁻ ‖B‖ * δ'^pr = δ'^pr * ∫⁻ ‖B‖ = δ'^pr.
    have h_eq :
        ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ * δ' ^ pr
            ∂(volume : Measure (Fin d → ℝ))
          = δ' ^ pr := by
      rw [MeasureTheory.lintegral_mul_const' _ _
        (ENNReal.rpow_ne_top_of_nonneg hpr_pos.le hδ'_ne_top)]
      rw [lintegral_enorm_bumpKernel_eq_one d ε hε_pos, one_mul]
    exact h_lint_le.trans h_eq.le
  have h_pow_le :
      (eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr ≤ δ' ^ pr :=
    h_jensen.trans h_int_bd
  -- Take pr-th root.
  have h_root :
      ((eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr) ^ (1 / pr)
        ≤ (δ' ^ pr) ^ (1 / pr) :=
    ENNReal.rpow_le_rpow h_pow_le (by positivity)
  have h_lhs_simp :
      ((eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr) ^ (1 / pr)
        = eLpNormPer p (fun x => mollifiedApprox f ε x - f x) := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hpr_pos.ne', ENNReal.rpow_one]
  have h_rhs_simp : (δ' ^ pr) ^ (1 / pr) = δ' := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hpr_pos.ne', ENNReal.rpow_one]
  rw [h_lhs_simp, h_rhs_simp] at h_root
  exact h_root.trans hδ'_le

/-- **Bare-hypotheses `L^p_per` convergence of the periodic mollifier.**
Drops the `Measurable f` and `LocallyIntegrable f volume` hypotheses of
`tendsto_lpNormPer_mollifiedApprox_sub`: from `MemLpPer p f + IsPeriodic f`
alone, we derive `LocallyIntegrable f volume` via the periodic bridge
`MemLpPer.locallyIntegrable_of_periodic`, and the inner Jensen + Tonelli
inequality is taken in its bare form (`eLpNormPer_pow_mollifiedApprox_sub_le_bare`),
which routes through a measurable representative internally. -/
theorem tendsto_lpNormPer_mollifiedApprox_sub_bare
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_lp : MemLpPer p f) (hper : IsPeriodic f) :
    Tendsto (fun ε : ℝ => eLpNormPer p (fun x => mollifiedApprox f ε x - f x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Derive `LocallyIntegrable f volume` from the bridge.
  have hf_loc : MeasureTheory.LocallyIntegrable f
      (volume : Measure (Fin d → ℝ)) :=
    hf_lp.locallyIntegrable_of_periodic hp hper
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by simp)
  set pr : ℝ := p.toReal with hpr_def
  have hpr_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_top
  have hpr_ge : 1 ≤ pr := by
    have := ENNReal.toReal_mono hp_top hp; simpa using this
  -- Translation continuity along `t ∈ Fin d → ℝ`.
  haveI : Fact (1 ≤ p) := ⟨hp⟩
  have htrans :
      Tendsto (fun y : Fin d → ℝ =>
        eLpNormPer p (fun x => f (x - y) - f x)) (𝓝 0) (𝓝 0) :=
    tendsto_eLpNormPer_translation_sub hp_top hf_lp hper
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ_pos
  set δ' : ℝ≥0∞ := min δ 1 with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos (by norm_num)
  have hδ'_le : δ' ≤ δ := min_le_left _ _
  have hδ'_le_one : δ' ≤ 1 := min_le_right _ _
  have hδ'_ne_top : δ' ≠ (⊤ : ℝ≥0∞) :=
    ne_of_lt (lt_of_le_of_lt hδ'_le_one ENNReal.one_lt_top)
  have h_evt :
      ∀ᶠ y : Fin d → ℝ in 𝓝 0,
        eLpNormPer p (fun x => f (x - y) - f x) ≤ δ' :=
    (ENNReal.tendsto_nhds_zero.mp htrans) δ' hδ'_pos
  rw [Metric.eventually_nhds_iff] at h_evt
  obtain ⟨r, hr_pos, hr⟩ := h_evt
  have h_nhds : Set.Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT hr_pos
  refine Filter.eventually_of_mem h_nhds ?_
  intro ε hε
  obtain ⟨hε_pos, hε_lt⟩ := hε
  -- Use the bare Jensen + Tonelli bound.
  have h_jensen :=
    eLpNormPer_pow_mollifiedApprox_sub_le_bare (d := d) (p := p) hp hp_top
      hf_loc (ε := ε) hε_pos
  have h_int_bd :
      ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ
          * (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr
          ∂(volume : Measure (Fin d → ℝ))
        ≤ δ' ^ pr := by
    have h_ptwise : ∀ t : Fin d → ℝ,
        ‖bumpKernel d ε hε_pos t‖ₑ
            * (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr
          ≤ ‖bumpKernel d ε hε_pos t‖ₑ * δ' ^ pr := by
      intro t
      by_cases ht : ε ≤ ‖t‖
      · have hzero : bumpKernel d ε hε_pos t = 0 :=
          bumpKernel_eq_zero_of_norm_ge hε_pos ht
        rw [hzero]; simp
      · push_neg at ht
        have hdist : dist t (0 : Fin d → ℝ) < r := by
          rw [dist_zero_right]; exact lt_trans ht hε_lt
        have h_le : eLpNormPer p (fun x => f (x - t) - f x) ≤ δ' := hr hdist
        exact mul_le_mul_right (ENNReal.rpow_le_rpow h_le hpr_pos.le) _
    have h_lint_le :
        ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ
              * (eLpNormPer p (fun x => f (x - t) - f x)) ^ pr
            ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ * δ' ^ pr
            ∂(volume : Measure (Fin d → ℝ)) :=
      MeasureTheory.lintegral_mono h_ptwise
    have h_eq :
        ∫⁻ t, ‖bumpKernel d ε hε_pos t‖ₑ * δ' ^ pr
            ∂(volume : Measure (Fin d → ℝ))
          = δ' ^ pr := by
      rw [MeasureTheory.lintegral_mul_const' _ _
        (ENNReal.rpow_ne_top_of_nonneg hpr_pos.le hδ'_ne_top)]
      rw [lintegral_enorm_bumpKernel_eq_one d ε hε_pos, one_mul]
    exact h_lint_le.trans h_eq.le
  have h_pow_le :
      (eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr ≤ δ' ^ pr :=
    h_jensen.trans h_int_bd
  have h_root :
      ((eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr) ^ (1 / pr)
        ≤ (δ' ^ pr) ^ (1 / pr) :=
    ENNReal.rpow_le_rpow h_pow_le (by positivity)
  have h_lhs_simp :
      ((eLpNormPer p (fun x => mollifiedApprox f ε x - f x)) ^ pr) ^ (1 / pr)
        = eLpNormPer p (fun x => mollifiedApprox f ε x - f x) := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hpr_pos.ne', ENNReal.rpow_one]
  have h_rhs_simp : (δ' ^ pr) ^ (1 / pr) = δ' := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hpr_pos.ne', ENNReal.rpow_one]
  rw [h_lhs_simp, h_rhs_simp] at h_root
  exact h_root.trans hδ'_le

/-! ### Sample example -/

/-- Sample example: applied to the constant function `fun _ => 1`, the
`L^p_per` mollifier convergence is the trivial statement that
`eLpNormPer p (mollifiedApprox 1 ε − 1)` tends to `0`. -/
example {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε : ℝ =>
        eLpNormPer p
          (fun x : Fin d → ℝ =>
            mollifiedApprox (fun _ : Fin d → ℝ => (1 : ℝ)) ε x - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  refine tendsto_lpNormPer_mollifiedApprox_sub_bare (d := d) (p := p)
    hp hp_top ?_ (IsPeriodic.const _)
  exact MemLp.toMemLpPer (memLp_const _)

/-! ## Density of `SmoothPeriodic d` in `L^p_per`

For every `1 ≤ p < ∞` and every periodic, measurable, locally
integrable `f` with `MemLpPer p f`, the smooth-periodic mollified
approximations `mollifiedApprox_asSmoothPeriodic` are arbitrarily
close to `f` in `eLpNormPer p`. This is the periodic analogue of
the classical "smooth functions dense in `L^p`" statement, and the
foundational AC of the `LimitPairingSelector`-AC1 task
(`infra-P4-pairing-selector-AC1-density-Lq`).

**AC1 amendment.** The original task's AC1 quantified over bare
`MemLpPer p f` only. We deliver the strengthened "+ `IsPeriodic f`
+ `Measurable f` + `LocallyIntegrable f volume`" form because the
existing convergence input `tendsto_lpNormPer_mollifiedApprox_sub`
requires those three additional hypotheses, and the bridge from
bare `MemLpPer` to those three is the multi-week Path-A
periodic-representative obstruction. See the in-flight task file
for the AC tightening rationale and the follow-up
`infra-P4-pairing-selector-AC1-density-Lq-bare`.
-/

/-- **Density of `SmoothPeriodic d` in `L^p_per`** (bare-hypotheses form).
For every `1 ≤ p < ∞`, every periodic `f` with `MemLpPer p f`, and every
`δ > 0` (as an `ℝ≥0∞`), there exists a smooth periodic test
function `φ : SmoothPeriodic d` with
`eLpNormPer p (f - φ) ≤ δ`.

The witness is the mollified approximation
`mollifiedApprox_asSmoothPeriodic hf_loc hper hε` at a small enough
width `ε`, where `LocallyIntegrable f volume` is derived from
`MemLpPer p f + IsPeriodic f` via the bridge
`MemLpPer.locallyIntegrable_of_periodic`. -/
theorem SmoothPeriodic.exists_eLpNormPer_sub_le
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_lp : MemLpPer p f) (hper : IsPeriodic f)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ φ : SmoothPeriodic d,
      eLpNormPer p (fun x => f x - (φ : (Fin d → ℝ) → ℝ) x) ≤ δ := by
  -- Derive `LocallyIntegrable f volume` from the bridge.
  have hf_loc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : Measure (Fin d → ℝ)) :=
    hf_lp.locallyIntegrable_of_periodic hp hper
  -- Convergence of the L^p-distance ‖mollifiedApprox f ε - f‖_p → 0
  -- gives an ε > 0 with ‖mollifiedApprox f ε - f‖_p ≤ δ.
  have h_tend := tendsto_lpNormPer_mollifiedApprox_sub_bare
    (d := d) (p := p) hp hp_top hf_lp hper
  -- Specialize to δ > 0.
  have h_evt :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        eLpNormPer p (fun x => mollifiedApprox f ε x - f x) ≤ δ :=
    (ENNReal.tendsto_nhds_zero.mp h_tend) δ hδ
  -- Extract a witness ε > 0.
  have h_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε :=
    eventually_mem_nhdsWithin
  rcases (h_evt.and h_pos).exists with ⟨ε, hε_le, hε_pos⟩
  -- Package the witness.
  refine ⟨mollifiedApprox_asSmoothPeriodic (f := f) hf_loc hper hε_pos, ?_⟩
  -- The L^p-distance is symmetric: f - φ vs φ - f have equal eLpNormPer.
  have h_eq :
      eLpNormPer p (fun x => f x
            - (mollifiedApprox_asSmoothPeriodic (d := d)
                hf_loc hper hε_pos : (Fin d → ℝ) → ℝ) x)
        = eLpNormPer p
            (fun x => mollifiedApprox f ε x - f x) := by
    -- f - mollifiedApprox = -(mollifiedApprox - f); seminorms agree.
    have h_neg : (fun x => f x - mollifiedApprox f ε x)
        = (fun x => -(mollifiedApprox f ε x - f x)) := by
      funext x; ring
    have h_unfold :
        ((mollifiedApprox_asSmoothPeriodic (d := d)
            hf_loc hper hε_pos : SmoothPeriodic d)
              : (Fin d → ℝ) → ℝ)
          = mollifiedApprox f ε := rfl
    rw [show (fun x => f x
              - (mollifiedApprox_asSmoothPeriodic (d := d)
                  hf_loc hper hε_pos : (Fin d → ℝ) → ℝ) x)
            = (fun x => f x - mollifiedApprox f ε x) from by
          funext x; rw [h_unfold]]
    rw [h_neg]
    -- eLpNorm of negation equals eLpNorm.
    unfold eLpNormPer
    exact MeasureTheory.eLpNorm_neg
      (f := fun x => mollifiedApprox f ε x - f x) (p := p)
      (μ := MeasureTheory.Measure.restrict
        (MeasureTheory.volume : Measure (Fin d → ℝ)) (UnitCube d))
  rw [h_eq]; exact hε_le

/-- **Real-valued form of the density theorem (bare-hypotheses form).**
Given `MemLpPer p f + IsPeriodic f`, for every `ε > 0 : ℝ` there exists
a smooth periodic test function `φ` with `lpNormPer p (f - φ) ≤ ε`. -/
theorem SmoothPeriodic.exists_lpNormPer_sub_le
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_lp : MemLpPer p f) (hper : IsPeriodic f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic d,
      lpNormPer p (fun x => f x - (φ : (Fin d → ℝ) → ℝ) x) ≤ ε := by
  -- Apply the eLpNorm form with δ := ENNReal.ofReal ε.
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  rcases SmoothPeriodic.exists_eLpNormPer_sub_le
      (p := p) hp hp_top hf_lp hper hδ with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  unfold lpNormPer
  -- (eLpNormPer ...).toReal ≤ (ENNReal.ofReal ε).toReal = ε.
  have h_top : ENNReal.ofReal ε ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono h_top hφ
  simpa [ENNReal.toReal_ofReal hε.le] using h

end Periodic
end StationaryMFG
