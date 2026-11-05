module

public import StationaryMFG.Periodic.WeakDerivative
public import StationaryMFG.Periodic.BumpKernelPeriodization

@[expose] public section

/-!
# Bare-function `W^{1,p}_per` predicate and seminorm on the torus

Per `docs/CONVENTIONS.md` §1b, the project's Sobolev machinery works on **bare**
functions `(Fin d → ℝ) → ℝ` (no quotient by a.e.-equality). This file
introduces the `k = 1` predicate `MemSobolevPer p f` and the seminorm

```
sobolevNormPer p f g = lpNormPer p f + ∑ i, lpNormPer p (g i)
```

where `g : Fin d → (Fin d → ℝ) → ℝ` is an explicit witness family of weak
partial derivatives. Because weak derivatives are only unique a.e., the
seminorm value is a function of the chosen representatives; passing
`g` explicitly avoids tying the definition to a particular choice.

The seminorm axioms (non-negativity, absolute homogeneity, triangle
inequality) are proved coordinate-wise from their `lpNormPer` counterparts
in `Periodic/Lp.lean`.

The Banach-space structure obtained via the `toLp` bridge is deferred to a
follow-up task (`infra:P1-Sobolev-banach`).
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

variable {d : ℕ}

/-- A bare function `f : (Fin d → ℝ) → ℝ` is `W^{1,p}_per` iff it lies in
`L^p_per` and has *some* family of weak partial derivatives in each
coordinate direction. The witness family is existentially quantified: at the
bare-function level, weak derivatives are only unique a.e. -/
def MemSobolevPer (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℝ) : Prop :=
  MemLpPer p f ∧
    ∃ g : Fin d → ((Fin d → ℝ) → ℝ), ∀ i, HasWeakDerivPer i f (g i)

/-- The `W^{1,p}_per` seminorm of a bare function `f`, with respect to an
*explicit* witness family `g` of weak partial derivatives:
`sobolevNormPer p f g = lpNormPer p f + ∑ i, lpNormPer p (g i)`. -/
noncomputable def sobolevNormPer (p : ℝ≥0∞)
    (f : (Fin d → ℝ) → ℝ)
    (g : Fin d → ((Fin d → ℝ) → ℝ)) : ℝ :=
  lpNormPer p f + ∑ i : Fin d, lpNormPer p (g i)

/-! ### Non-negativity -/

/-- The Sobolev seminorm is non-negative. -/
theorem sobolevNormPer_nonneg (p : ℝ≥0∞)
    (f : (Fin d → ℝ) → ℝ) (g : Fin d → ((Fin d → ℝ) → ℝ)) :
    0 ≤ sobolevNormPer p f g := by
  unfold sobolevNormPer
  have h₁ : 0 ≤ lpNormPer p f := lpNormPer_nonneg p f
  have h₂ : 0 ≤ ∑ i : Fin d, lpNormPer p (g i) :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (g i))
  linarith

/-! ### Absolute homogeneity -/

/-- Scalar homogeneity of the Sobolev seminorm:
`sobolevNormPer p (c • f) (c • g) = |c| * sobolevNormPer p f g`. -/
theorem sobolevNormPer_smul (p : ℝ≥0∞) (c : ℝ)
    (f : (Fin d → ℝ) → ℝ) (g : Fin d → ((Fin d → ℝ) → ℝ)) :
    sobolevNormPer p (c • f) (c • g) = |c| * sobolevNormPer p f g := by
  unfold sobolevNormPer
  have hf : lpNormPer p (c • f) = |c| * lpNormPer p f :=
    lpNormPer_smul p c f
  have hgi : ∀ i : Fin d,
      lpNormPer p ((c • g) i) = |c| * lpNormPer p (g i) := by
    intro i
    change lpNormPer p (c • g i) = |c| * lpNormPer p (g i)
    exact lpNormPer_smul p c (g i)
  have hsum :
      ∑ i : Fin d, lpNormPer p ((c • g) i) =
        |c| * ∑ i : Fin d, lpNormPer p (g i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hgi i)
  rw [hf, hsum]
  ring

/-! ### Triangle inequality -/

/-- Triangle inequality for the Sobolev seminorm. With witness derivative
families `g₁` for `f₁` and `g₂` for `f₂`, the natural witness family for
`f₁ + f₂` is `g₁ + g₂`, and the corresponding seminorms add.

The hypotheses `hg₁p`, `hg₂p` record `MemLpPer p` of each derivative; this is
extra information beyond `HasWeakDerivPer` (which only gives `MemLpPer 1`)
and is needed to apply the `Lᵖ` triangle inequality for general `p`. For
`p = 1`, these follow from `HasWeakDerivPer.memLpPer`. -/
theorem sobolevNormPer_triangle {p : ℝ≥0∞}
    {f₁ f₂ : (Fin d → ℝ) → ℝ}
    {g₁ g₂ : Fin d → ((Fin d → ℝ) → ℝ)}
    (hf₁ : MemSobolevPer p f₁) (hf₂ : MemSobolevPer p f₂)
    (hg₁p : ∀ i, MemLpPer p (g₁ i))
    (hg₂p : ∀ i, MemLpPer p (g₂ i))
    (hp : 1 ≤ p) :
    sobolevNormPer p (f₁ + f₂) (g₁ + g₂) ≤
      sobolevNormPer p f₁ g₁ + sobolevNormPer p f₂ g₂ := by
  unfold sobolevNormPer
  -- Triangle inequality on the `Lp` part of `f`.
  have hL : lpNormPer p (f₁ + f₂) ≤ lpNormPer p f₁ + lpNormPer p f₂ :=
    lpNormPer_triangle hf₁.1 hf₂.1 hp
  -- Triangle inequality on each derivative coordinate.
  have hLi : ∀ i : Fin d,
      lpNormPer p ((g₁ + g₂) i) ≤
        lpNormPer p (g₁ i) + lpNormPer p (g₂ i) := by
    intro i
    change lpNormPer p (g₁ i + g₂ i) ≤ lpNormPer p (g₁ i) + lpNormPer p (g₂ i)
    exact lpNormPer_triangle (hg₁p i) (hg₂p i) hp
  -- Sum the coordinate-wise bound.
  have hsum :
      ∑ i : Fin d, lpNormPer p ((g₁ + g₂) i) ≤
        ∑ i : Fin d, lpNormPer p (g₁ i) +
          ∑ i : Fin d, lpNormPer p (g₂ i) := by
    have hstep : ∑ i : Fin d, lpNormPer p ((g₁ + g₂) i) ≤
        ∑ i : Fin d, (lpNormPer p (g₁ i) + lpNormPer p (g₂ i)) :=
      Finset.sum_le_sum (fun i _ => hLi i)
    have hdistrib :
        ∑ i : Fin d, (lpNormPer p (g₁ i) + lpNormPer p (g₂ i)) =
          ∑ i : Fin d, lpNormPer p (g₁ i) +
            ∑ i : Fin d, lpNormPer p (g₂ i) :=
      Finset.sum_add_distrib
    linarith
  linarith

/-! ### Example: a smooth periodic function is `MemSobolevPer p` for any `p` -/

/-- A `SmoothPeriodic` function is in `MemSobolevPer p` for any `p`: it lies
in `L^p_per` (it is continuous on a finite-measure cube), and its classical
partial derivatives furnish a weak derivative family by
`HasWeakDerivPer.of_contDiff`. -/
theorem MemSobolevPer.of_smoothPeriodic (p : ℝ≥0∞) (φ : SmoothPeriodic d) :
    MemSobolevPer p ((φ : (Fin d → ℝ) → ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- `MemLpPer p φ`: φ is continuous, the unit cube is compact-bounded with
    -- finite measure, so φ is bounded ⇒ in `L^p`.
    have hfinite :
        IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    have hcont : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
    -- Bound `‖φ‖` on the closed cube ⊇ unit cube.
    have hcompact :
        IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hcont.norm.continuousOn
    -- Use `MemLp.of_bound` (almost everywhere on the cube ‖φ‖ ≤ C).
    refine MemLp.toMemLpPer ?_
    refine MemLp.of_bound (f := (φ : (Fin d → ℝ) → ℝ))
      hcont.aestronglyMeasurable C ?_
    refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    apply hC
    refine ⟨x, ?_, rfl⟩
    intro j _
    exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))
  · -- The classical partial derivatives form a weak-derivative family.
    refine ⟨fun i =>
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ), ?_⟩
    intro i
    exact HasWeakDerivPer.of_contDiff i φ

example (p : ℝ≥0∞) (φ : SmoothPeriodic d) :
    MemSobolevPer p ((φ : (Fin d → ℝ) → ℝ)) :=
  MemSobolevPer.of_smoothPeriodic p φ

/-! ### Weak limit of weak derivatives (P2d)

The genuine functional-analytic content underpinning the congestion weak
limit (paper `eq:compactness.congestion`): the weak derivative of a weak
limit is the weak limit of the weak derivatives.

Concretely, suppose a sequence of functions `uSeq k` has weak `i`-th
partial derivative `gSeq k`, and both sequences converge *weakly* in the
sense that, tested against every smooth periodic function `ψ`, the
pairings converge:

* `∫ uSeq k · ψ → ∫ u · ψ`,
* `∫ gSeq k · ψ → ∫ g · ψ`.

(This is exactly the form weak `L^{γ̄}`-convergence supplies, because
each `ψ ∈ C^∞_per` and its derivative are bounded, hence lie in the
Hölder-conjugate `L^{γ̄'}`; the integration-against-`ψ` functional is then
a `StrongDual` element, hence weakly continuous.)

The integration-by-parts identity
`∫ gSeq k · ψ = -∫ uSeq k · ∂_i ψ` then passes to the limit:
`∫ g · ψ = -∫ u · ∂_i ψ`, i.e. `HasWeakDerivPer i u g`.

NO Brouwer, NO oracle: this is pure weak continuity of a fixed linear
functional plus uniqueness of limits in `ℝ`. -/
theorem hasWeakDerivPer_of_weak_limit
    {i : Fin d} {u g : (Fin d → ℝ) → ℝ}
    {uSeq gSeq : ℕ → (Fin d → ℝ) → ℝ}
    (hg : MemLpPer 1 g)
    (hWeak : ∀ k, HasWeakDerivPer i (uSeq k) (gSeq k))
    (hConvU : ∀ ψ : SmoothPeriodic d,
      Tendsto
        (fun k => periodicIntegral
          (fun x => uSeq k x * (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (periodicIntegral
          (fun x => u x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hConvG : ∀ ψ : SmoothPeriodic d,
      Tendsto
        (fun k => periodicIntegral
          (fun x => gSeq k x * (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (periodicIntegral
          (fun x => g x * (ψ : (Fin d → ℝ) → ℝ) x)))) :
    HasWeakDerivPer i u g := by
  refine ⟨hg, ?_⟩
  intro φ
  -- Abbreviation for `∂_i φ`.
  set dφ : SmoothPeriodic d := SmoothPeriodic.partialDeriv i φ with hdφ_def
  -- Per-`k` IBP identity:  ∫ gSeq k · φ = - ∫ uSeq k · ∂_i φ.
  have hIBP : ∀ k,
      periodicIntegral (fun x => gSeq k x * (φ : (Fin d → ℝ) → ℝ) x)
        = - periodicIntegral
            (fun x => uSeq k x * (dφ : (Fin d → ℝ) → ℝ) x) := by
    intro k
    have := (hWeak k).integral_eq φ
    simpa [hdφ_def] using this
  -- LHS converges to `∫ g · φ`.
  have hLHS :
      Tendsto
        (fun k => periodicIntegral
          (fun x => gSeq k x * (φ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (periodicIntegral
          (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x))) :=
    hConvG φ
  -- RHS converges to `- ∫ u · ∂_i φ`.
  have hRHS :
      Tendsto
        (fun k => - periodicIntegral
          (fun x => uSeq k x * (dφ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (- periodicIntegral
          (fun x => u x * (dφ : (Fin d → ℝ) → ℝ) x))) :=
    (hConvU dφ).neg
  -- The two sequences are equal (by `hIBP`), so their limits coincide.
  have hLHS' :
      Tendsto
        (fun k => - periodicIntegral
          (fun x => uSeq k x * (dφ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (periodicIntegral
          (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x))) := by
    refine hLHS.congr ?_
    intro k
    exact hIBP k
  -- Uniqueness of limits in `ℝ`.
  have heq :
      periodicIntegral (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x)
        = - periodicIntegral
            (fun x => u x * (dφ : (Fin d → ℝ) → ℝ) x) :=
    tendsto_nhds_unique hLHS' hRHS
  simpa [hdφ_def] using heq

/-! ### Density of `SmoothPeriodic` in `W^{1,p}_per`: smooth-input case

The headline density theorem `SmoothPeriodic.denseInSobolevPer` — every
`MemSobolevPer p f` has an `ε`-close witness in `SmoothPeriodic d`
under `sobolevNormPer 1 p` — is the goal of `infra:P1-density-W1p-main`
(see `docs/TASKS/backlog/`). Its proof requires
`tendsto_lpNormPer_mollifiedApprox_sub`, which currently lives in the
parked child task `infra:P1-density-Lp-conv` (see PHASES.md), and the
classical `∂_i (η_ε ⋆ f) = η_ε ⋆ g` commutation lemma sketched in
`infra:P1-density-W1p-deriv-comm`.

Pending those two pieces, we record here the **smooth-input case**: when
`f` is itself the coercion of a `SmoothPeriodic d`, the density witness
is `f` itself and the seminorm of the error vanishes. Although trivial,
this case will be a strict sub-case of the general theorem and so is the
right shape to expose as the public API.
-/

/-- The `lpNormPer` of the zero function vanishes for any `p`. -/
private lemma lpNormPer_zero_eq_zero (p : ℝ≥0∞) :
    lpNormPer (d := d) p (fun _ : (Fin d → ℝ) => (0 : ℝ)) = 0 := by
  unfold lpNormPer eLpNormPer
  simp

/-- The `sobolevNormPer` with both `f` and the witness derivative family
identically zero vanishes. -/
private lemma sobolevNormPer_zero_zero (p : ℝ≥0∞) :
    sobolevNormPer (d := d) p
        (fun _ : (Fin d → ℝ) => (0 : ℝ))
        (fun _ : Fin d => fun _ : (Fin d → ℝ) => (0 : ℝ)) = 0 := by
  unfold sobolevNormPer
  rw [lpNormPer_zero_eq_zero]
  -- The sum `∑ i, lpNormPer p 0` collapses to zero.
  have hsum : ∑ _ : Fin d, lpNormPer (d := d) p
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) = 0 := by
    rw [Finset.sum_const, lpNormPer_zero_eq_zero]
    simp
  rw [hsum]; ring

/-- **Density of `SmoothPeriodic` in `W^{1,p}_per`, smooth-input case.**

When the source function `f` is itself the coercion of a smooth periodic
function `φ₀`, the density witness is `φ₀` itself: the difference `f - φ₀`
is identically zero, so the corresponding `sobolevNormPer` vanishes and
trivially undercuts any positive `ε`.

The witness family for the error is the constant-zero family `fun _ _ ↦ 0`:
this is the coordinate-wise difference between the classical partial
derivatives `∂_i φ₀` (a weak-derivative family for the source) and
themselves (a weak-derivative family for the witness).

This statement is the smooth-input restriction of the headline density
theorem `SmoothPeriodic.denseInSobolevPer` (target of the backlog task
`infra:P1-density-W1p-main`); the latter additionally handles general
`MemSobolevPer p f` and requires the parked
`tendsto_lpNormPer_mollifiedApprox_sub` convergence theorem. -/
theorem SmoothPeriodic.denseInSobolevPer_of_smooth
    {p : ℝ≥0∞} (φ₀ : SmoothPeriodic d) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic d,
      sobolevNormPer p
        ((φ₀ : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ))
        (fun _ : Fin d => fun _ : (Fin d → ℝ) => (0 : ℝ)) < ε := by
  refine ⟨φ₀, ?_⟩
  -- The difference `φ₀ - φ₀` is identically zero on the nose.
  have hdiff_zero :
      ((φ₀ : (Fin d → ℝ) → ℝ) - (φ₀ : (Fin d → ℝ) → ℝ))
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    funext x; simp
  rw [hdiff_zero]
  rw [sobolevNormPer_zero_zero]
  exact hε

/-- Sample example for acceptance: the smooth-input density theorem
provides a SmoothPeriodic witness within any positive `ε` of a smooth
periodic source under the Sobolev seminorm. -/
example (p : ℝ≥0∞) (φ₀ : SmoothPeriodic d) :
    ∃ φ : SmoothPeriodic d,
      sobolevNormPer p
        ((φ₀ : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ))
        (fun _ : Fin d => fun _ : (Fin d → ℝ) => (0 : ℝ)) < (1 : ℝ) :=
  SmoothPeriodic.denseInSobolevPer_of_smooth (p := p) φ₀ (by norm_num)

/-! ### Headline density theorem -/

/-- **Density of `SmoothPeriodic` in `W^{1,p}_per`.**

For every `MemSobolevPer p f` with explicit weak-derivative family `g i`
(plus the standard regularity hypotheses `Measurable`, `IsPeriodic`,
`LocallyIntegrable` on `f` and on each `g i`, and `MemLpPer p (g i)`),
and for every `ε > 0`, there exists a smooth periodic function `φ` such
that

```
sobolevNormPer p (f − φ) (i ↦ g i − ∂_i φ) < ε.
```

The witness `φ` is the periodic mollification
`mollifiedApprox_asSmoothPeriodic` at width `η`, for some `η ∈ (0, 1/2)`
chosen small enough using `tendsto_lpNormPer_mollifiedApprox_sub` applied
in parallel to `f` and to each `g i`. The identification of
`∂_i (B_η ⋆ f)` with `B_η ⋆ g i` uses
`partialDeriv_mollifiedApprox_eq_convolution_partialKernel` (Mathlib
half) followed by `convolution_partialKernel_eq_convolution_weakDeriv`
(IBP half). -/
theorem SmoothPeriodic.denseInSobolevPer
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_lp : MemLpPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_per : ∀ i, IsPeriodic (g i))
    (hg_loc : ∀ i, MeasureTheory.LocallyIntegrable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_lp : ∀ i, MemLpPer p (g i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic d,
      sobolevNormPer p
        ((f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ))
        (fun i x => g i x -
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) < ε := by
  classical
  -- Set the per-coordinate target. Fineness factor `(d + 2)` is enough.
  set M : ℝ := (d : ℝ) + 2 with hM_def
  have hM_pos : 0 < M := by
    change (0 : ℝ) < (d : ℝ) + 2
    positivity
  set δr : ℝ := ε / (2 * M) with hδr_def
  have hδr_pos : 0 < δr := by
    change (0 : ℝ) < ε / (2 * M)
    positivity
  set δ : ℝ≥0∞ := ENNReal.ofReal δr with hδ_def
  have hδ_pos : 0 < δ := ENNReal.ofReal_pos.mpr hδr_pos
  -- Apply the L^p_per convergence theorem to `f` and each `g i`.
  have h_f := tendsto_lpNormPer_mollifiedApprox_sub_bare (d := d) (p := p)
    hp hp_top hf_lp hf_per
  have h_g : ∀ i, Filter.Tendsto
      (fun η : ℝ => eLpNormPer p
        (fun x : Fin d → ℝ => mollifiedApprox (g i) η x - g i x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by
    intro i
    exact tendsto_lpNormPer_mollifiedApprox_sub_bare (d := d) (p := p)
      hp hp_top (hg_lp i) (hg_per i)
  -- Convert each Tendsto to an eventual bound and intersect.
  have h_f_evt : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      eLpNormPer p (fun x => mollifiedApprox f η x - f x) ≤ δ :=
    (ENNReal.tendsto_nhds_zero.mp h_f) δ hδ_pos
  have h_g_evt : ∀ i, ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      eLpNormPer p (fun x => mollifiedApprox (g i) η x - g i x) ≤ δ := by
    intro i
    exact (ENNReal.tendsto_nhds_zero.mp (h_g i)) δ hδ_pos
  -- Intersect the eventual bounds.
  have h_g_all : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i : Fin d,
        eLpNormPer p (fun x => mollifiedApprox (g i) η x - g i x) ≤ δ :=
    Filter.eventually_all.mpr h_g_evt
  -- Combine with `f` and add the constraint `η < 1/2`.
  have h_half : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0), η < 1/2 := by
    have : Set.Iio ((1 : ℝ)/2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
    exact this
  have h_combined : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      η < 1/2 ∧
      eLpNormPer p (fun x => mollifiedApprox f η x - f x) ≤ δ ∧
      ∀ i : Fin d,
        eLpNormPer p (fun x => mollifiedApprox (g i) η x - g i x) ≤ δ :=
    h_half.and (h_f_evt.and h_g_all)
  -- Extract a witness `η ∈ (0, 1/2)` satisfying the bounds.
  rcases (h_combined.and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
    with ⟨η, ⟨hη_half, hη_f, hη_g⟩, hη_pos⟩
  -- Build the smooth-periodic witness.
  refine ⟨mollifiedApprox_asSmoothPeriodic hf_loc hf_per hη_pos, ?_⟩
  set φ : SmoothPeriodic d := mollifiedApprox_asSmoothPeriodic hf_loc hf_per hη_pos
    with hφ_def
  -- `(φ : ...) = mollifiedApprox f η` definitionally.
  have hφ_coe : (φ : (Fin d → ℝ) → ℝ) = mollifiedApprox f η := rfl
  -- For each i, identify `∂_i φ` with `mollifiedApprox (g i) η`.
  have hpartial : ∀ i x,
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x = mollifiedApprox (g i) η x := by
    intro i x
    -- Step (a): unfold `partialDeriv` of φ as `fderiv ℝ φ x e_i`.
    have h_a :
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x
          = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i) := by
      simp [SmoothPeriodic.coe_partialDeriv]
    -- Step (b): identify `(φ : …) = mollifiedApprox f η` then apply the
    -- Mathlib half: `fderiv (B ⋆ f) x e_i = (∂_i B) ⋆ f`.
    have h_b :
        fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i)
          = MeasureTheory.convolution (partialKernel d η hη_pos i) f
              (ContinuousLinearMap.lsmul ℝ ℝ)
              (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) x := by
      rw [hφ_coe]
      exact partialDeriv_mollifiedApprox_eq_convolution_partialKernel
        hf_loc hη_pos i x
    -- Step (c): IBP-on-convolution: `(∂_i B) ⋆ f = B ⋆ g i`.
    have h_c :
        MeasureTheory.convolution (partialKernel d η hη_pos i) f
            (ContinuousLinearMap.lsmul ℝ ℝ)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) x =
          MeasureTheory.convolution (bumpKernel d η hη_pos) (g i)
            (ContinuousLinearMap.lsmul ℝ ℝ)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) x :=
      convolution_partialKernel_eq_convolution_weakDeriv hη_pos hη_half i
        hf_meas hf_per hf_loc
        (hg_meas i) (hg_per i) (hg_loc i)
        (hg_weak i) x
    -- Step (d): `B ⋆ g i = mollifiedApprox (g i) η`.
    have h_d :
        MeasureTheory.convolution (bumpKernel d η hη_pos) (g i)
            (ContinuousLinearMap.lsmul ℝ ℝ)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) x
          = mollifiedApprox (g i) η x := by
      rw [mollifiedApprox_eq_convolution (g i) hη_pos]
    rw [h_a, h_b, h_c, h_d]
  -- Now bound each `lpNormPer` term.
  -- Key reformulation: rewrite the eLpNorm of `(a - b)` as the eLpNorm of
  -- `-(b - a)`, which has the same value by `eLpNorm_neg`.
  have h_swap : ∀ (u v : (Fin d → ℝ) → ℝ),
      eLpNormPer p (fun x => u x - v x) = eLpNormPer p (fun x => v x - u x) := by
    intro u v
    have hfun : (fun x : Fin d → ℝ => v x - u x)
        = -(fun x : Fin d → ℝ => u x - v x) := by
      funext x; simp
    unfold eLpNormPer
    rw [hfun, MeasureTheory.eLpNorm_neg]
  -- (1) `lpNormPer p (f - φ) ≤ δr`.
  have hfφ_eLp :
      eLpNormPer p ((f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ)) ≤ δ := by
    change eLpNormPer p (fun x => f x - (φ : (Fin d → ℝ) → ℝ) x) ≤ δ
    rw [show (fun x : Fin d → ℝ => f x - (φ : (Fin d → ℝ) → ℝ) x)
          = (fun x => f x - mollifiedApprox f η x) from by
      funext x; rw [hφ_coe]]
    rw [h_swap]
    exact hη_f
  have hfφ_lp : lpNormPer p ((f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ)) ≤ δr := by
    unfold lpNormPer
    exact ENNReal.toReal_le_of_le_ofReal hδr_pos.le hfφ_eLp
  -- (2) For each i, `lpNormPer p (g i - ∂_i φ) ≤ δr`.
  have hgi_lp : ∀ i, lpNormPer p
      (fun x => g i x -
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) ≤ δr := by
    intro i
    have h_eq : (fun x : Fin d → ℝ => g i x -
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        = (fun x => g i x - mollifiedApprox (g i) η x) := by
      funext x; rw [hpartial i x]
    have h_eLp : eLpNormPer p (fun x => g i x -
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) ≤ δ := by
      rw [h_eq, h_swap]
      exact hη_g i
    unfold lpNormPer
    exact ENNReal.toReal_le_of_le_ofReal hδr_pos.le h_eLp
  -- (3) Sum: sobolevNormPer = lpNormPer (f - φ) + ∑ i, lpNormPer (g i - ∂_i φ)
  --     ≤ (d + 1) * δr < ε.
  unfold sobolevNormPer
  have hsum_le :
      ∑ i : Fin d, lpNormPer p
          (fun x => g i x -
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
        ≤ (d : ℝ) * δr := by
    have hbd : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        lpNormPer p
            (fun x => g i x -
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) ≤ δr := fun i _ => hgi_lp i
    have h := Finset.sum_le_sum hbd
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
    simpa [nsmul_eq_mul] using h
  -- Cast `(g - g_φ) i = (fun x => g i x - ...)` so we can plug `hsum_le` in.
  have h_total :
      lpNormPer p ((f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ)) +
        ∑ i : Fin d, lpNormPer p
          (fun x => g i x -
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
        ≤ δr + (d : ℝ) * δr := by
    have := add_le_add hfφ_lp hsum_le
    linarith
  have h_final : δr + (d : ℝ) * δr < ε := by
    -- δr * (d + 1) < δr * (d + 2) = δr * M = ε / 2 < ε
    have hMcalc : δr * M = ε / 2 := by
      change ε / (2 * M) * M = ε / 2
      field_simp
    have hrew : δr + (d : ℝ) * δr = δr * ((d : ℝ) + 1) := by ring
    rw [hrew]
    have h1 : (d : ℝ) + 1 < M := by
      change (d : ℝ) + 1 < (d : ℝ) + 2
      linarith
    have h2 : δr * ((d : ℝ) + 1) < δr * M :=
      mul_lt_mul_of_pos_left h1 hδr_pos
    linarith
  exact lt_of_le_of_lt h_total h_final

/-! ### Sobolev `≤ ε` density corollary (paper line 1524)

The strict-inequality form `denseInSobolevPer` is the right shape for
`Tendsto`-style consumers, but the paper-step
`paper-lem-weak-is-strong-c` invokes the density via the closed-form
"approximate to within `ε`" idiom. This corollary repackages
`denseInSobolevPer` as a `≤ ε` statement (apply with `ε/2 < ε`).

Combined with `Hamiltonian.mDpH_mem_Lp_gammaBar'_congestion`
(`eq:boundsmDpH+`), this is the density step that extends the
smooth-test conclusion of `infra:P5-iota-firstorder` to the full
Sobolev test space `W^{1,γ̄}_per`.

The hypotheses match `denseInSobolevPer`: as documented at
`infra-P4-pairing-selector-AC1-density-Lq` (the parallel `L^p`-case
density step), the underlying mollifier-convergence theorem
`tendsto_lpNormPer_mollifiedApprox_sub` requires `Measurable f`,
`IsPeriodic f`, `LocallyIntegrable f volume`, plus the same
hypotheses on each weak-derivative witness `g i` together with
`MemLpPer p (g i)`. Bridging to a strict bare-`MemSobolevPer p f`
form depends on the same periodic-representative selector that
gates the bare-`MemLpPer` density variant. -/
theorem SmoothPeriodic.exists_sobolevPer_sub_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_lp : MemLpPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_per : ∀ i, IsPeriodic (g i))
    (hg_loc : ∀ i, MeasureTheory.LocallyIntegrable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_lp : ∀ i, MemLpPer p (g i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic d,
      sobolevNormPer p
        ((f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ))
        (fun i x => g i x -
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) ≤ ε := by
  -- Apply the strict density theorem at slack `ε/2`.
  have hε2 : 0 < ε / 2 := by positivity
  rcases SmoothPeriodic.denseInSobolevPer (p := p) hp hp_top
      hf_meas hf_per hf_loc hf_lp
      hg_weak hg_meas hg_per hg_loc hg_lp hε2 with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  -- ε/2 ≤ ε since 0 < ε.
  have h_half : ε / 2 ≤ ε := by linarith
  exact le_trans hφ.le h_half

/-- **Sobolev density corollary, bundled with the standard
`MemSobolevPer` predicate.**

This is the user-facing form for downstream consumers (e.g. paper
`lem:weak.is.strong.c`): given `MemSobolevPer p f` plus the regularity
strengthenings and an explicit `L^p_per` weak-derivative family `g`
witnessing the existential in the predicate, we can approximate `f`
arbitrarily well by smooth periodic functions in the Sobolev seminorm.

Caller-side, `paper-lem-weak-is-strong-c` will choose `g i := Du i`
from its Sobolev test function. -/
theorem SmoothPeriodic.exists_sobolevPer_sub_le_of_memSobolevPer
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (_hf : MemSobolevPer p f)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : MeasureTheory.LocallyIntegrable f
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hf_lp : MemLpPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_per : ∀ i, IsPeriodic (g i))
    (hg_loc : ∀ i, MeasureTheory.LocallyIntegrable (g i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hg_lp : ∀ i, MemLpPer p (g i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic d,
      sobolevNormPer p
        ((f : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ))
        (fun i x => g i x -
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) ≤ ε :=
  SmoothPeriodic.exists_sobolevPer_sub_le hp hp_top
    hf_meas hf_per hf_loc hf_lp
    hg_weak hg_meas hg_per hg_loc hg_lp hε

/-- **Sample example** for acceptance: smooth-input case. The
density corollary is satisfied trivially when the source `f` is
itself a smooth periodic function: take `φ := f`, in which case the
left-hand side vanishes. -/
example {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (φ₀ : SmoothPeriodic d) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SmoothPeriodic d,
      sobolevNormPer p
        ((φ₀ : (Fin d → ℝ) → ℝ) - (φ : (Fin d → ℝ) → ℝ))
        (fun i x => ((SmoothPeriodic.partialDeriv i φ₀
              : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x -
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) ≤ ε := by
  -- Reuse the smooth-input density theorem with strict `< ε`,
  -- then weaken to `≤ ε`.
  have _ := hp
  have _ := hp_top
  refine ⟨φ₀, ?_⟩
  -- Both differences vanish at `φ := φ₀`.
  have h_f : ((φ₀ : (Fin d → ℝ) → ℝ) - (φ₀ : (Fin d → ℝ) → ℝ))
      = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    funext x; simp
  have h_g : (fun i x => ((SmoothPeriodic.partialDeriv i φ₀
        : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x -
        ((SmoothPeriodic.partialDeriv i φ₀ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
      = (fun _ : Fin d => fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    funext i x; simp
  rw [h_f, h_g]
  rw [sobolevNormPer_zero_zero]
  exact hε.le

noncomputable section BanachBridge

/-! ### Banach-space bridge for `W^{1,p}_per`

This section provides a quotient-style type `SobolevPerLp 1 p d` together
with `NormedAddCommGroup`, `NormedSpace ℝ`, and `CompleteSpace` instances,
following `infra:P1-Sobolev-banach`. The construction is intentionally the
*shortest* Banach realisation: an element of `SobolevPerLp 1 p d` is a
`(d+1)`-tuple consisting of an `L^p` class for the function plus an
`L^p`-class for each coordinate weak partial derivative. Mathlib's
`MeasureTheory.Lp` already provides the underlying complete normed-space
structure, and the Mathlib product instances on `× ` and `Π` lift it to the
tuple. The bare-function predicate `MemSobolevPer` continues to be the public
API everywhere else; this file is the only place the quotient type appears.

Adapted from `DeGiorgi/LpFunctionToolkit.lean`, which advocates routing
completeness through Mathlib's `Lp` locally rather than re-deriving it on
bare functions.
-/

/-- Local abbreviation for the cube-restricted Lebesgue measure that all of
the periodic `Lᵖ` machinery uses. -/
local notation "μPer" => MeasureTheory.Measure.restrict (volume) (UnitCube d)

/-- The quotient `W^{1,p}_per` realisation: an element is a tuple consisting
of an `L^p` class for the function value plus an `L^p` class for each weak
partial derivative.

The `k`-th index just records which Sobolev order the type is intended to
realise; only `k = 1` is used in the rest of the development, and the type
ignores `k = 0` and any higher orders. The definition is intentionally a
*coarse* realisation — there is no constraint relating the function class
and the derivative classes — but it is enough to inherit completeness from
Mathlib's `Lp` and to bridge bare `MemSobolevPer` witnesses into a
Banach-space setting whenever one is needed (reflexivity, duality). -/
abbrev SobolevPerLp (_k : ℕ) (p : ℝ≥0∞) (d : ℕ) : Type :=
  MeasureTheory.Lp ℝ p (MeasureTheory.Measure.restrict
      (volume) (UnitCube d)) ×
    (Fin d → MeasureTheory.Lp ℝ p (MeasureTheory.Measure.restrict
      (volume) (UnitCube d)))

-- Instances on `SobolevPerLp k p d` are inherited automatically from the
-- product structure and from Mathlib's `Lp` (`NormedAddCommGroup`,
-- `NormedSpace ℝ`, `CompleteSpace`); the `Fact (1 ≤ p)` hypothesis is what
-- unlocks Mathlib's instances. The synthesiser finds them through the
-- `abbrev`-reducible definition without needing manual instance declarations.

/-! ### Bridge from bare `MemSobolevPer` witnesses

`MemSobolevPer.toLpSobolev` takes a bare-function Sobolev witness — a
function `f` with `MemSobolevPer p f`, an explicit weak-derivative family
`g`, and a proof that each `g i` lies in `L^p_per` — and produces a
`SobolevPerLp 1 p d` element.

Note: `MemSobolevPer p f` only guarantees `MemLpPer 1 (g i)` for each weak
derivative `g i`. To bridge into `SobolevPerLp 1 p d` for general `p`, the
caller must supply the stronger hypothesis `MemLpPer p (g i)` for every `i`.
For `p = 1` the upgrade is automatic from `HasWeakDerivPer.memLpPer`.
-/

/-- Bridge a bare `MemSobolevPer` witness, together with an explicit
`L^p`-integrable family of weak partial derivatives `g`, into a
`SobolevPerLp 1 p d` element. The first component is the `Lp` class of `f`;
the `i`-th derivative component is the `Lp` class of `g i`. -/
noncomputable def MemSobolevPer.toLpSobolev {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemSobolevPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg : ∀ i, MemLpPer p (g i)) :
    SobolevPerLp 1 p d :=
  (hf.1.toLp, fun i => (hg i).toLp)

/-- Sanity check: the Banach-space instance is available. The product of an
`Lp` factor and a `Fin d`-indexed family of `Lp` factors is complete. -/
example (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (SobolevPerLp 1 p d) := inferInstance

/-- Sanity check: `SobolevPerLp 1 p d` is a normed `ℝ`-vector space. -/
example (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedSpace ℝ (SobolevPerLp 1 p d) := inferInstance

/-- Sanity check: `SobolevPerLp 1 p d` is a normed additive commutative
group. -/
example (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedAddCommGroup (SobolevPerLp 1 p d) := inferInstance

/-! ### Banach-norm-vs-integrated translation lemmas

The two lemmas in this section are the Sobolev-side counterparts of
`MemLpPer.norm_toLp_rpow_eq` (in `Periodic/Lp.lean`). They are the
*reusable infrastructure* that allows Phase-4 apriori-bound clients to
translate between the Mathlib `Lp`/`Lp × (Fin d → Lp)` Banach norm of
`toLpSobolev` and the integrated quantities `∫ |f|^p`, `∑ i, ∫ |g i|^p`
that the bare-function bounds control.

* `MemSobolevPer.norm_toLpSobolev_rpow_le` is the headline Sobolev
  translation, with dimension constant `(d + 1) ^ p.toReal`.
* `XBanachPair.norm_rpow_le` is the product-pair version that covers
  `LpPer βBar d × SobolevPerLp 1 γBar d`, the actual Banach pair used by
  the regularised-MFG operator.
-/

/-- For nonnegative reals `x_0, …, x_d`, the bound
`(x_0 + … + x_d)^p ≤ (d+1)^p · (x_0^p + … + x_d^p)` whenever `0 ≤ p`.

Proof: `x_0 + … + x_d ≤ (d+1) · max_i x_i`, then raise to the `p`-th
power and bound `max_i x_i ^ p` by the sum. -/
lemma _root_.StationaryMFG.Periodic.sum_succ_rpow_le
    (a : ℝ) (b : Fin d → ℝ)
    (ha : 0 ≤ a) (hb : ∀ i, 0 ≤ b i) (p : ℝ) (hp : 0 ≤ p) :
    (a + ∑ i, b i) ^ p ≤
      ((d : ℝ) + 1) ^ p * (a ^ p + ∑ i, (b i) ^ p) := by
  -- `S = a + ∑ b i` is nonneg.
  set S : ℝ := a + ∑ i, b i with hS_def
  have hsum_b : 0 ≤ ∑ i, b i :=
    Finset.sum_nonneg (fun i _ => hb i)
  have hS_nn : 0 ≤ S := by
    change 0 ≤ a + ∑ i, b i; linarith
  -- The "max" we'll use: `S` itself is a uniform upper bound for each term
  -- (so `a^p + ∑ (b i)^p ≥ S^p / (d+1)^p` is what we'd need; instead we
  -- bound `S^p ≤ (d+1)^p * (a^p ⊔ max (b i)^p) ≤ (d+1)^p * (a^p + ∑ b_i^p)`).
  -- A direct calculation: `S ≤ (d+1) * (a ⊔ max b)`. We avoid `max`
  -- machinery and instead bound each summand by `a + ∑ b j` itself.
  -- Here is a cleaner route: each of `a` and `b i` is `≤ S`, so
  -- `S = a + ∑ b i ≤ S + d · S = (d+1) · S`, but that is the wrong
  -- direction. We use Cauchy–Schwarz / `pow_arith_mean`-style instead.
  -- ----
  -- Simple route: `(d+1) * (a^p + ∑ b_i^p) ≥ ?`. Use Jensen:
  -- The arithmetic-mean-power-mean inequality gives
  -- `((a + ∑ b_i) / (d+1))^p ≤ (a^p + ∑ b_i^p) / (d+1)`
  -- whenever `1 ≤ p`. For `0 ≤ p < 1`, the inequality reverses, so the
  -- statement above with the extra `(d+1)^p` factor still holds via
  -- `(a + ∑ b)^p ≤ (d+1)^p * max^p ≤ (d+1)^p * ∑^p`.
  -- We give a self-contained proof using only `Real.rpow` monotonicity
  -- and `Finset.sum_le_sum_of_ne`-style bounds:
  --   * Step 1: `S ≤ (d+1) * M` where `M = max_{i ∈ {-1, 0, …, d-1}} (·)`.
  --   * Step 2: `S^p ≤ ((d+1) * M)^p = (d+1)^p * M^p`.
  --   * Step 3: `M^p ≤ a^p + ∑ b_i^p` (for the dominating term).
  -- We pick the easier `M := max a (max over Fin d of b i)`.
  -- For brevity, use a *cruder* but still adequate bound:
  --   `(d+1) * (a^p + ∑ b_i^p) ≥ (a + ∑ b_i)^p / (d+1)^(p-1)`
  -- via `rpow_arith_mean_le_arith_mean_rpow`.
  -- Actually, the cleanest is: power-of-sum bound for nonneg reals via
  -- `Finset.inner_mul_le_norm_mul_norm` style, but let's just do the
  -- direct calculation by induction on `Fin d` would be heavy. Instead,
  -- cleanly:
  -- Define the indexed family `c : Fin (d+1) → ℝ` by `c 0 = a`, `c (i+1) = b i`.
  -- Then `∑ i, c i = S`, and `∑ i, (c i)^p = a^p + ∑ i, b i^p`.
  -- Bound: `(∑ c)^p ≤ (d+1)^p · ∑ (c i)^p` is the "p-mean ≥ 1-mean"
  -- inequality with `(d+1)^p` slack. Prove it via: each `c i ≤ ∑ c`, so
  -- `(c i)^p ≤ (∑ c)^p`; summing, `∑ (c i)^p ≤ (d+1) (∑ c)^p`. Then
  -- multiply by `(d+1)^(p-1)` … OK that gives the *opposite* direction.
  -- ----
  -- Final approach: **bound each piece at the integrand level**:
  -- `S = a + ∑ b_i` nonneg, so `S^p ≤ ((d+1) S)^p`?? No, only if
  -- `(d+1) ≥ 1`, which holds, and `S ≥ 0`. But `S ≤ (d+1) S` is trivial.
  -- That just multiplies by `(d+1)^p`. We actually want to relate `S^p`
  -- to `a^p + ∑ b_i^p`. We use: each of `a, b_0, …, b_{d-1}` is `≤ S`,
  -- so `a^p + ∑ b_i^p ≥ ?`. No, the inequality `x^p ≤ S^p` for `x ≤ S`
  -- and `0 ≤ x, S` and `0 ≤ p` goes the wrong way for our needs.
  -- ----
  -- Use `Real.rpow_natCast`-friendly reformulation via:
  -- `Real.add_rpow` for two summands, then induct on `Fin d`.
  -- For the binary case `(a + b)^p ≤ 2^p * (a^p + b^p)` (nonneg, `0 ≤ p`)
  -- holds via `(a+b)^p ≤ (2 max(a,b))^p = 2^p max(a,b)^p ≤ 2^p(a^p + b^p)`.
  -- Iterate `d` times: `(a + ∑_{i < d} b_i)^p ≤ 2^p (a^p + (∑_{i<d} b_i)^p)`
  --     ≤ 2^p (a^p + 2^p (b_0^p + (∑_{i<d-1} b_{i+1})^p)) … = 2^{p(d+1)}.
  -- That gives `(d+1)^p` only when `d ≤ 1`; we want `(d+1)^p`, not
  -- `2^{p(d+1)}`. To get `(d+1)^p` we use the cleaner argument:
  --   `S = a + ∑ b_i ≤ (d+1) max(a, max_i b_i)`  (≤ from `n` terms ≤ n·max)
  --   `S^p ≤ (d+1)^p · max(...)^p ≤ (d+1)^p · (a^p + ∑ b_i^p)`.
  -- We do exactly that.
  --
  -- 1. M := max a (Finset.univ.sup' h fun i => b i) when d > 0; just `a`
  --    when `d = 0`. Easier: bound `S ≤ (d+1) * M'` where
  --    `M' := a + ∑ b_i = S`. That gives `S ≤ (d+1) * S`, useless.
  -- ----
  -- Simplest bullet-proof route: use the auxiliary family
  -- `c : Fin d.succ → ℝ` and apply `Finset.inner_mul_le_norm_mul_norm`?
  -- No, use a *Cauchy–Schwarz* style: by Cauchy–Schwarz with vector of
  -- ones, `(∑ c_i)^2 ≤ (d+1) · ∑ c_i^2`. For general `p ≥ 1`, the
  -- generalisation is the `power-mean` inequality
  -- `((∑ c_i)/N)^p ≤ (∑ c_i^p)/N`, i.e., `(∑ c_i)^p ≤ N^{p-1} · ∑ c_i^p`.
  -- For `0 ≤ p ≤ 1`, the inequality reverses, so we need the slacker
  -- `(∑ c_i)^p ≤ N^p · ∑ c_i^p` form which holds for both ranges via
  -- `c_i ≤ ∑ c_j` and `c_i^p ≤ (∑ c_j)^p`.
  -- We just need ONE of: (a) `1 ≤ p` case via power-mean, or (b) any
  -- `0 ≤ p` via the cruder argument. For the headline Sobolev lemma we
  -- only need `1 ≤ p` (since the apriori bounds use `p > 1`), but we
  -- prove the more general `0 ≤ p` form for reusability.
  --
  -- We use the cruder "each term ≤ S" bound, *but* on the RHS sum, not
  -- on `S` itself: `a^p + ∑ b_i^p ≥ M^p` where `M = max(a, max b_i)`.
  -- Then `S = a + ∑ b_i ≤ (d+1) · M`, so `S^p ≤ (d+1)^p · M^p ≤ …`.
  --
  -- Implementation: rather than fight with `max`, use the bound
  -- `S^p ≤ (d+1)^p · (a^p ⊔ (Finset.univ.sup' nonempty (fun i => (b i)^p)))`,
  -- which reduces to RHS via `Finset.sup'_le_sum`. We only need the
  -- monotone inequalities, no Jensen.
  --
  -- Concretely we proceed by cases on `d`.
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: empty sum.
    subst hd0
    simp only [hS_def, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    -- Goal: a^p ≤ ((0:ℝ)+1)^p * (a^p + 0)
    have h1 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
    rw [h1, Real.one_rpow, one_mul]
  · -- d ≥ 1: use the `(d+1)·max` bound.
    -- Define the augmented family.
    -- M := max of (a, max over i of b i)
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, hdpos⟩⟩
    -- Step 1: S ≤ (d+1) * (a ⊔ Finset.sup' univ hne (fun i => b i))
    set Mb : ℝ := (Finset.univ : Finset (Fin d)).sup' hne (fun i => b i) with hMb_def
    set M : ℝ := max a Mb with hM_def
    have hMb_nn : 0 ≤ Mb := by
      have hi₀ : ⟨0, hdpos⟩ ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
      have : b ⟨0, hdpos⟩ ≤ Mb := Finset.le_sup' (f := fun i => b i) hi₀
      exact le_trans (hb _) this
    have hM_nn : 0 ≤ M := le_max_of_le_left ha
    have ha_le_M : a ≤ M := le_max_left _ _
    have hb_le_M : ∀ i, b i ≤ M := by
      intro i
      have hbi : b i ≤ Mb :=
        Finset.le_sup' (f := fun j => b j) (Finset.mem_univ i)
      exact le_trans hbi (le_max_right _ _)
    -- ∑ b_i ≤ d * M
    have hsum_le : ∑ i, b i ≤ (d : ℝ) * M := by
      have h := Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => b i) (g := fun _ => M)
        (fun i _ => hb_le_M i)
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] using h
    -- a + ∑ b_i ≤ (d+1) * M
    have hS_le : S ≤ ((d : ℝ) + 1) * M := by
      have : S = a + ∑ i, b i := rfl
      rw [this]
      have : a + ∑ i, b i ≤ M + (d : ℝ) * M := by
        exact add_le_add ha_le_M hsum_le
      have : a + ∑ i, b i ≤ ((d : ℝ) + 1) * M := by
        calc a + ∑ i, b i ≤ M + (d : ℝ) * M :=
              add_le_add ha_le_M hsum_le
          _ = ((d : ℝ) + 1) * M := by ring
      exact this
    -- Step 2: S^p ≤ ((d+1) * M)^p = (d+1)^p * M^p.
    have hd1_nn : 0 ≤ ((d : ℝ) + 1) := by positivity
    have hSp_le : S ^ p ≤ ((d : ℝ) + 1) ^ p * M ^ p := by
      have h1 : S ^ p ≤ (((d : ℝ) + 1) * M) ^ p :=
        Real.rpow_le_rpow hS_nn hS_le hp
      have h2 : (((d : ℝ) + 1) * M) ^ p = ((d : ℝ) + 1) ^ p * M ^ p :=
        Real.mul_rpow hd1_nn hM_nn
      linarith
    -- Step 3: M^p ≤ a^p + ∑ (b i)^p.
    -- Either M = a or M = b j for some j; in both cases M^p ≤ RHS.
    have hMp_le : M ^ p ≤ a ^ p + ∑ i, (b i) ^ p := by
      have hsumbp_nn : 0 ≤ ∑ i, (b i) ^ p :=
        Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hb i) _)
      have hap_nn : 0 ≤ a ^ p := Real.rpow_nonneg ha _
      -- M ≤ max(a, sup_i b_i). Distinguish.
      rcases le_total a Mb with hcase | hcase
      · -- M = Mb.
        have hMeq : M = Mb := by simp [hM_def, hcase]
        rw [hMeq]
        -- Mb is a sup' so equals b j for some j.
        obtain ⟨j, _, hj⟩ :=
          (Finset.univ : Finset (Fin d)).exists_mem_eq_sup' hne (fun i => b i)
        rw [show Mb = b j from hj]
        have hbjp_le : (b j) ^ p ≤ ∑ i, (b i) ^ p := by
          have h := Finset.single_le_sum
            (f := fun i => (b i) ^ p)
            (fun i _ => Real.rpow_nonneg (hb i) _)
            (Finset.mem_univ j)
          exact h
        linarith
      · -- M = a.
        have hMeq : M = a := by simp [hM_def, hcase]
        rw [hMeq]
        linarith
    -- Combine.
    calc S ^ p ≤ ((d : ℝ) + 1) ^ p * M ^ p := hSp_le
      _ ≤ ((d : ℝ) + 1) ^ p * (a ^ p + ∑ i, (b i) ^ p) := by
          apply mul_le_mul_of_nonneg_left hMp_le
          exact Real.rpow_nonneg hd1_nn _

/-- **Sobolev-norm-vs-component-sum.** The `p`-th power of the
`SobolevPerLp 1 p d`-norm of `toLpSobolev hf hg` is bounded by
`(d+1)^p` times the sum of the integrated `p`-th powers of `f` and the
witness derivatives `g i`.

This is the Sobolev-side counterpart of
`MemLpPer.norm_toLp_rpow_eq` (in `Periodic/Lp.lean`): together they
translate the abstract Banach norm into the concrete pointwise
quantities controlled by the Phase-4 apriori bound.

The dimension constant `(d+1)^p.toReal` is not tight; tighter constants
are available via Jensen / power-mean inequalities and may be filed as
follow-up infrastructure if a sharp Sobolev embedding ever requires
them. -/
theorem MemSobolevPer.norm_toLpSobolev_rpow_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_zero : p ≠ 0) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemSobolevPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg : ∀ i, MemLpPer p (g i)) :
    ‖MemSobolevPer.toLpSobolev hf hg‖ ^ p.toReal
      ≤ ((d : ℝ) + 1) ^ p.toReal *
        ((∫ x in UnitCube d, |f x| ^ p.toReal) +
          ∑ i, ∫ x in UnitCube d, |g i x| ^ p.toReal) := by
  -- Local notation.
  set s : SobolevPerLp 1 p d := MemSobolevPer.toLpSobolev hf hg with hs_def
  -- Step 1: `‖s‖ ≤ ‖hf.1.toLp‖ + ∑ i, ‖(hg i).toLp‖`.
  -- `s = (hf.1.toLp, fun i => (hg i).toLp)`, so by `Prod.norm_def`,
  -- `‖s‖ = max ‖hf.1.toLp‖ ‖fun i => (hg i).toLp‖`.
  have h_normLp_nn : ∀ i, 0 ≤ ‖(hg i).toLp‖ := fun i => norm_nonneg _
  have h_normTo_nn : 0 ≤ ‖hf.1.toLp‖ := norm_nonneg _
  -- max ≤ sum-of-nonneg.
  have h_max_le_sum : ∀ {a b : ℝ} (_ : 0 ≤ a) (_ : 0 ≤ b),
      max a b ≤ a + b := fun ha hb => max_le (by linarith) (by linarith)
  -- The Pi norm: `‖fun i => (hg i).toLp‖ ≤ ∑ i, ‖(hg i).toLp‖`.
  -- Mathlib's `Pi.norm_def` gives `‖(·)‖ = (Finset.univ.sup fun i => ‖·‖₊ : ℝ≥0)`.
  -- We instead use the simple bound `pi_norm_le_iff_of_nonneg`-style:
  -- show `‖(g i).toLp‖ ≤ ∑ j, ‖(hg j).toLp‖` for each `i`, then `‖_‖` ≤ sup ≤ sum.
  have h_pi_le : ‖(fun i => (hg i).toLp :
        Fin d → MeasureTheory.Lp ℝ p (Measure.restrict volume (UnitCube d)))‖
      ≤ ∑ i, ‖(hg i).toLp‖ := by
    -- For Mathlib's `Pi` norm, use `pi_norm_le_iff_of_nonneg`.
    have hsum_nn : 0 ≤ ∑ i, ‖(hg i).toLp‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    rw [pi_norm_le_iff_of_nonneg hsum_nn]
    intro i
    exact Finset.single_le_sum
      (f := fun j => ‖(hg j).toLp‖)
      (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  -- Combine.
  have h_norm_le : ‖s‖ ≤ ‖hf.1.toLp‖ + ∑ i, ‖(hg i).toLp‖ := by
    have hpi_nn : 0 ≤ ‖(fun i => (hg i).toLp :
          Fin d → MeasureTheory.Lp ℝ p (Measure.restrict volume (UnitCube d)))‖ :=
      norm_nonneg _
    have hmax : ‖s‖ = max ‖hf.1.toLp‖ ‖(fun i => (hg i).toLp :
          Fin d → MeasureTheory.Lp ℝ p (Measure.restrict volume (UnitCube d)))‖ :=
      Prod.norm_def _
    rw [hmax]
    calc max ‖hf.1.toLp‖ ‖(fun i => (hg i).toLp :
            Fin d → MeasureTheory.Lp ℝ p
              (Measure.restrict volume (UnitCube d)))‖
        ≤ ‖hf.1.toLp‖ + ‖(fun i => (hg i).toLp :
            Fin d → MeasureTheory.Lp ℝ p
              (Measure.restrict volume (UnitCube d)))‖ :=
          h_max_le_sum h_normTo_nn hpi_nn
      _ ≤ ‖hf.1.toLp‖ + ∑ i, ‖(hg i).toLp‖ := by
          linarith
  -- Step 2: take the `p.toReal`-th power.
  have hs_nn : 0 ≤ ‖s‖ := norm_nonneg _
  have hp_nn : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have h_normp_le :
      ‖s‖ ^ p.toReal
        ≤ (‖hf.1.toLp‖ + ∑ i, ‖(hg i).toLp‖) ^ p.toReal :=
    Real.rpow_le_rpow hs_nn h_norm_le hp_nn
  -- Step 3: bound the rpow of a sum by `(d+1)^p · (sum of rpows)`.
  have h_sum_bound :
      (‖hf.1.toLp‖ + ∑ i, ‖(hg i).toLp‖) ^ p.toReal
        ≤ ((d : ℝ) + 1) ^ p.toReal *
          ((‖hf.1.toLp‖ ^ p.toReal) +
            ∑ i, ‖(hg i).toLp‖ ^ p.toReal) := by
    apply StationaryMFG.Periodic.sum_succ_rpow_le
        ‖hf.1.toLp‖ (fun i => ‖(hg i).toLp‖) h_normTo_nn h_normLp_nn
        p.toReal hp_nn
  -- Step 4: translate each `‖·.toLp‖^p` to an integrated `|·|^p` via lemma (1).
  have hf_eq : ‖hf.1.toLp‖ ^ p.toReal
      = ∫ x in UnitCube d, |f x| ^ p.toReal :=
    MemLpPer.norm_toLp_rpow_eq hp_zero hp_top hf.1
  have hg_eq : ∀ i, ‖(hg i).toLp‖ ^ p.toReal
      = ∫ x in UnitCube d, |g i x| ^ p.toReal := by
    intro i
    exact MemLpPer.norm_toLp_rpow_eq hp_zero hp_top (hg i)
  -- Combine.
  calc ‖s‖ ^ p.toReal
      ≤ (‖hf.1.toLp‖ + ∑ i, ‖(hg i).toLp‖) ^ p.toReal := h_normp_le
    _ ≤ ((d : ℝ) + 1) ^ p.toReal *
          ((‖hf.1.toLp‖ ^ p.toReal) +
            ∑ i, ‖(hg i).toLp‖ ^ p.toReal) := h_sum_bound
    _ = ((d : ℝ) + 1) ^ p.toReal *
          ((∫ x in UnitCube d, |f x| ^ p.toReal) +
            ∑ i, ∫ x in UnitCube d, |g i x| ^ p.toReal) := by
          rw [hf_eq]
          congr 2
          exact Finset.sum_congr rfl (fun i _ => hg_eq i)

/-! ### Banach-pair-norm translation

The product `LpPer βBar d × SobolevPerLp 1 γBar d` is the Banach pair
sitting under the regularised-MFG operator. The next lemma packages
`MemLpPer.norm_toLp_rpow_eq` (for the first factor) and
`MemSobolevPer.norm_toLpSobolev_rpow_le` (for the second factor) into a
single bound on the *product* norm.

Note: the product norm on `(A × B)` is `max ‖a‖ ‖b‖` (`Prod.norm_def`),
so the `p`-th power obeys
`max(x, y)^p = max(x^p, y^p) ≤ x^p + y^p` for nonneg `x, y` and
`0 ≤ p`. The product-norm bound therefore inherits the Sobolev side's
`(d+1)^p` constant.
-/

/-- **Banach-pair-norm translation.** For a pair `(q₁, q₂)` of bridged
elements coming from bare functions `m : (Fin d → ℝ) → ℝ` (with
`MemLpPer βBar m`) and `(u, Du)` (with `MemSobolevPer γBar u` and
`MemLpPer γBar (Du i)` for each `i`), the `max` of the `βBar`-th power
of the `LpPer`-norm and the `γBar`-th power of the
`SobolevPerLp`-norm is bounded by the dimensioned sum of integrated
quantities.

This is the headline product-pair-norm translation feeding the apriori
bound discharge — both factors are controlled by integrated quantities
that the Phase-4 a-priori bounds already produce. -/
theorem MemLpPer.norm_pair_rpow_le
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (hβ_zero : βBar ≠ 0) (hβ_top : βBar ≠ (⊤ : ℝ≥0∞))
    (hγ_zero : γBar ≠ 0) (hγ_top : γBar ≠ (⊤ : ℝ≥0∞))
    {m : (Fin d → ℝ) → ℝ} (hm : MemLpPer βBar m)
    {u : (Fin d → ℝ) → ℝ} (hu : MemSobolevPer γBar u)
    {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hDu : ∀ i, MemLpPer γBar (Du i)) :
    -- The βBar-th power of the first-factor norm is exactly the integrated |m|^β.
    ‖hm.toLp‖ ^ βBar.toReal = ∫ x in UnitCube d, |m x| ^ βBar.toReal ∧
    -- The γBar-th power of the second-factor norm is bounded by the dimensioned
    -- integrated sum.
    ‖MemSobolevPer.toLpSobolev hu hDu‖ ^ γBar.toReal
      ≤ ((d : ℝ) + 1) ^ γBar.toReal *
        ((∫ x in UnitCube d, |u x| ^ γBar.toReal) +
          ∑ i, ∫ x in UnitCube d, |Du i x| ^ γBar.toReal) := by
  refine ⟨?_, ?_⟩
  · exact MemLpPer.norm_toLp_rpow_eq hβ_zero hβ_top hm
  · exact MemSobolevPer.norm_toLpSobolev_rpow_le hγ_zero hγ_top hu hDu

/-! ### Product-pair `rpow` reduction (`min`-exponent slack form)

The lemma below expresses the abstract pair-norm
`‖q‖ = max ‖q.1‖ ‖q.2‖` (`Prod.norm_def`) of a `LpPer βBar × SobolevPerLp 1 γBar`
pair raised to a *single* exponent `r := min βBar.toReal γBar.toReal`
in terms of the *sum* of the per-factor `rpow`s, which the apriori bound
already controls.

The key inequality, isolated as `max_rpow_min_le_one_add_pair_rpow`, is
purely real-valued and does not depend on the periodic Banach
infrastructure: for nonneg reals `a, b` and exponents `p, q ≥ 1`,
`max a b ^ min p q ≤ 1 + a^p + b^q`. The constant `1` is the unavoidable
slack when `max a b ≤ 1` (then both `a^p` and `b^q` may be very small).
-/

/-- **Real-valued `rpow_min` reduction.** For nonneg reals `a, b` and
exponents `p, q ≥ 1`, the `min p q`-th power of `max a b` is bounded by
`1 + a^p + b^q`.

Three cases:

* `max a b ≤ 1`: `max a b ^ min p q ≤ 1` (nonneg exponent on a
  base in `[0, 1]`).
* `1 < a` (and `b ≤ a`): `a ^ min p q ≤ a^p` (since `1 ≤ a` and
  `min p q ≤ p`), then `a^p ≤ 1 + a^p + b^q`.
* `1 < b` (and `a < b`): symmetric. -/
private lemma _root_.StationaryMFG.Periodic.max_rpow_min_le_one_add_pair_rpow
    {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    max a b ^ min p q ≤ 1 + a ^ p + b ^ q := by
  have hmin_nn : 0 ≤ min p q := le_min (le_trans zero_le_one hp)
                                        (le_trans zero_le_one hq)
  have hap_nn : 0 ≤ a ^ p := Real.rpow_nonneg ha _
  have hbq_nn : 0 ≤ b ^ q := Real.rpow_nonneg hb _
  have hmax_nn : 0 ≤ max a b := le_max_of_le_left ha
  rcases le_or_gt (max a b) 1 with hle | hgt
  · -- `max a b ≤ 1`: `max a b ^ min p q ≤ 1`.
    have h1 : max a b ^ min p q ≤ 1 :=
      Real.rpow_le_one hmax_nn hle hmin_nn
    linarith
  · -- `1 < max a b`. Either `a` or `b` exceeds `1`.
    rcases le_total a b with hab | hba
    · -- `max a b = b`, and `1 < b`.
      have hmax_eq : max a b = b := by simpa [max_eq_right hab]
      have hb1 : (1 : ℝ) < b := by rw [hmax_eq] at hgt; exact hgt
      have hb1_le : (1 : ℝ) ≤ b := hb1.le
      have hmin_le_q : min p q ≤ q := min_le_right _ _
      -- `b ^ (min p q) ≤ b ^ q` for `1 ≤ b` and `min p q ≤ q`.
      have hbm_le : b ^ min p q ≤ b ^ q :=
        Real.rpow_le_rpow_of_exponent_le hb1_le hmin_le_q
      calc max a b ^ min p q
          = b ^ min p q := by rw [hmax_eq]
        _ ≤ b ^ q := hbm_le
        _ ≤ 1 + a ^ p + b ^ q := by linarith
    · -- `max a b = a`, and `1 < a`.
      have hmax_eq : max a b = a := by simpa [max_eq_left hba]
      have ha1 : (1 : ℝ) < a := by rw [hmax_eq] at hgt; exact hgt
      have ha1_le : (1 : ℝ) ≤ a := ha1.le
      have hmin_le_p : min p q ≤ p := min_le_left _ _
      have ham_le : a ^ min p q ≤ a ^ p :=
        Real.rpow_le_rpow_of_exponent_le ha1_le hmin_le_p
      calc max a b ^ min p q
          = a ^ min p q := by rw [hmax_eq]
        _ ≤ a ^ p := ham_le
        _ ≤ 1 + a ^ p + b ^ q := by linarith

/-- **Product-pair `rpow` reduction (closed form).** For a pair
`(q₁, q₂) : LpPer βBar d × SobolevPerLp 1 γBar d` formed from bare
functions, the `min βBar γBar`-th power of the product norm
`‖(q₁, q₂)‖ = max ‖q₁‖ ‖q₂‖` is bounded by
`1 + ‖q₁‖^βBar + ‖q₂‖^γBar`. This is the closed-form reduction
feeding the AC2 closed-form Banach-pair-norm bound:

* the `‖q₁‖^βBar` factor is exactly `∫ |m|^βBar` (via
  `MemLpPer.norm_toLp_rpow_eq`);
* the `‖q₂‖^γBar` factor is bounded by `(d+1)^γBar * (∫ |u|^γBar +
  ∑ i, ∫ |Du i|^γBar)` (via `MemSobolevPer.norm_toLpSobolev_rpow_le`).

The constant `1` is unavoidable slack from the small-norm regime
(`max ‖q₁‖ ‖q₂‖ ≤ 1`); it is absorbed into the apriori constant at
the consumer site.

The exponent `min βBar.toReal γBar.toReal` is the natural single-power
exponent for the closed-form bound; both `βBar, γBar ≥ 1` is enforced by
the `[Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]` instances. -/
theorem MemLpPer.norm_pair_rpow_min_le
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (hβ_top : βBar ≠ ⊤) (hγ_top : γBar ≠ ⊤)
    (q₁ : MeasureTheory.Lp ℝ βBar
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (q₂ : SobolevPerLp 1 γBar d) :
    ‖((q₁, q₂))‖ ^ min βBar.toReal γBar.toReal
      ≤ 1 + ‖q₁‖ ^ βBar.toReal + ‖q₂‖ ^ γBar.toReal := by
  have hβ : (1 : ℝ) ≤ βBar.toReal := by
    have h1 : (1 : ℝ≥0∞) ≤ βBar := Fact.out
    have h2 : ((1 : ℝ≥0∞).toReal) ≤ βBar.toReal :=
      ENNReal.toReal_mono hβ_top h1
    simpa using h2
  have hγ : (1 : ℝ) ≤ γBar.toReal := by
    have h1 : (1 : ℝ≥0∞) ≤ γBar := Fact.out
    have h2 : ((1 : ℝ≥0∞).toReal) ≤ γBar.toReal :=
      ENNReal.toReal_mono hγ_top h1
    simpa using h2
  have h_norm_eq : ‖((q₁, q₂))‖ = max ‖q₁‖ ‖q₂‖ := Prod.norm_def _
  rw [h_norm_eq]
  exact StationaryMFG.Periodic.max_rpow_min_le_one_add_pair_rpow
    (norm_nonneg _) (norm_nonneg _) hβ hγ

/-! ### Sanity-check examples -/

/-- The first translation lemma is consumable by the apriori bound:
given any real `β > 1` (the typical apriori-side hypothesis) and a bare
function `m`, the lemma reduces `‖hm.toLp‖^β` to a concrete integrated
`p`-th power. -/
example {β : ℝ} (hβ : 1 < β)
    {m : (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal β) m) :
    ‖hm.toLp‖ ^ (ENNReal.ofReal β).toReal
      = ∫ x in UnitCube d, |m x| ^ (ENNReal.ofReal β).toReal := by
  have hβ_pos : 0 < β := lt_trans Real.zero_lt_one hβ
  exact MemLpPer.norm_toLp_rpow_eq
    (ENNReal.ofReal_pos.mpr hβ_pos).ne'
    ENNReal.ofReal_ne_top hm

/-- The Sobolev translation lemma is consumable by the apriori bound:
given any `γ > 1` (the typical apriori-side hypothesis), the
`‖toLpSobolev …‖^γ` quantity is bounded by `(d+1)^γ` times an integrated
sum of `f` and the witness derivatives. -/
example {γ : ℝ} (hγ : 1 < γ)
    {u : (Fin d → ℝ) → ℝ}
    (hu : MemSobolevPer (ENNReal.ofReal γ) u)
    {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal γ) (Du i)) :
    let _ : Fact (1 ≤ ENNReal.ofReal γ) :=
      ⟨by
        have : ENNReal.ofReal 1 ≤ ENNReal.ofReal γ :=
          ENNReal.ofReal_le_ofReal hγ.le
        simpa using this⟩
    ‖MemSobolevPer.toLpSobolev hu hDu‖ ^ (ENNReal.ofReal γ).toReal
      ≤ ((d : ℝ) + 1) ^ (ENNReal.ofReal γ).toReal *
        ((∫ x in UnitCube d, |u x| ^ (ENNReal.ofReal γ).toReal) +
          ∑ i, ∫ x in UnitCube d, |Du i x| ^ (ENNReal.ofReal γ).toReal) := by
  intro _
  have hγ_pos : 0 < γ := lt_trans Real.zero_lt_one hγ
  exact MemSobolevPer.norm_toLpSobolev_rpow_le
    (ENNReal.ofReal_pos.mpr hγ_pos).ne'
    ENNReal.ofReal_ne_top hu hDu

/-- The product-pair `rpow_min` reduction is consumable by the
AC2 closed-form Banach-norm bound: given any real `β, γ > 1`, the
`min(β, γ)`-th power of the pair norm reduces to a sum of per-factor
`rpow`s plus an additive `1` slack. Pin the type-shape with
`ENNReal.ofReal`-shaped exponents (the apriori-side hypothesis
shape). -/
example {β γ : ℝ} (hβ : 1 < β) (hγ : 1 < γ)
    (q₁ : MeasureTheory.Lp ℝ (ENNReal.ofReal β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (q₂ : SobolevPerLp 1 (ENNReal.ofReal γ) d) :
    let _ : Fact (1 ≤ ENNReal.ofReal β) :=
      ⟨by
        have : ENNReal.ofReal 1 ≤ ENNReal.ofReal β :=
          ENNReal.ofReal_le_ofReal hβ.le
        simpa using this⟩
    let _ : Fact (1 ≤ ENNReal.ofReal γ) :=
      ⟨by
        have : ENNReal.ofReal 1 ≤ ENNReal.ofReal γ :=
          ENNReal.ofReal_le_ofReal hγ.le
        simpa using this⟩
    ‖((q₁, q₂))‖
        ^ min (ENNReal.ofReal β).toReal (ENNReal.ofReal γ).toReal
      ≤ 1 + ‖q₁‖ ^ (ENNReal.ofReal β).toReal
          + ‖q₂‖ ^ (ENNReal.ofReal γ).toReal := by
  intro _ _
  exact MemLpPer.norm_pair_rpow_min_le
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top q₁ q₂

end BanachBridge

end Periodic
end StationaryMFG
