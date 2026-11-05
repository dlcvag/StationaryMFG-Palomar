module

public import StationaryMFG.Theorems.InfimalConvolution.Kernel
public import StationaryMFG.Hamiltonian.Differentiability
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Finite-dimensional envelope analysis for the inf-convolution gradient

This module supplies the **reusable, hypothesis-free analysis** behind paper
`lem:inf-conv-props` (especially `eq:DpH-epsilon-formula`,
`eq:DpHdelta.dotp.minusH`, `eq:inf-conv.diff-relation1`,
`Source/FGU-monotone_revised.tex`): the fact that a **continuous subgradient
field** on the finite-dimensional space `Fin d → ℝ` is in fact the Fréchet
derivative, and the FTC-slice integral identity that follows.

## Main results

* `hasFDerivAt_of_continuous_subgradient_field` — if `g` is continuous and
  `g p` is a subgradient of `f` at every `p`, then `f` is Fréchet
  differentiable at every `p` with derivative `dotCLMHam (g p)`. This is the
  finite-dimensional envelope/sandwich lemma, proved with pure coordinate
  estimates — **no** invariance of domain / Brouwer / continuity-of-inverse.

* `ftc_slice_of_hasFDerivAt_continuous_gradient` — the FTC-slice integral
  identity `eq:DpHdelta.dotp.minusH` for any `F` whose Fréchet derivative is a
  *continuous* gradient field `G`, via the 1-D fundamental theorem of calculus
  along the segment `[0, p]`.

The mathematical crux is the sandwich
`0 ≤ f y - f p - g p ⬝ (y - p) ≤ (g y - g p) ⬝ (y - p)`, where the lower bound
is the subgradient inequality at `p` and the upper bound is the subgradient
inequality at `y`; continuity of `g` turns the right-hand side into a little-o
of `‖y - p‖`.
-/

namespace StationaryMFG
namespace InfimalConvolution

open Filter Topology Asymptotics
open StationaryMFG.Hamiltonian

variable {d : ℕ}

/-! ## Task 1 — abstract finite-dimensional envelope lemma -/

/-- The canonical pairing `∑ i, v i * (y i - p i)` used in `HasSubgradientAt`
agrees with the Euclidean dot product `v ⬝ (y - p)`. -/
private lemma subgrad_sum_eq_dot (v y p : Fin d → ℝ) :
    ∑ i, v i * (y i - p i) = v ⬝ (y - p) := by
  unfold euclideanDot
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.sub_apply]

/-- **Task 1 — finite-dimensional envelope lemma.**

If `g : (Fin d → ℝ) → (Fin d → ℝ)` is continuous and, for every `p`, the value
`g p` is a (convex-analysis) subgradient of `f` at `p`, then `f` is Fréchet
differentiable at every `p`, with derivative the continuous linear functional
`w ↦ g p ⬝ w` (`dotCLMHam (g p)`).

This is the paper's envelope-theorem step `eq:inf-conv.diff-relation1`: a
continuous selection of subgradients is the genuine gradient. The proof is a
pure finite-dimensional coordinate sandwich:
`0 ≤ f y - f p - g p ⬝ (y - p) ≤ (g y - g p) ⬝ (y - p)`, bounded in absolute
value by `d * ‖g y - g p‖ * ‖y - p‖`, which is `o(‖y - p‖)` by continuity of
`g`. **No** invariance of domain / Brouwer / continuity-of-inverse is used. -/
theorem hasFDerivAt_of_continuous_subgradient_field
    {f : (Fin d → ℝ) → ℝ}
    {g : (Fin d → ℝ) → (Fin d → ℝ)}
    (hg : Continuous g)
    (hsub : ∀ p, HasSubgradientAt f p (g p)) :
    ∀ p, HasFDerivAt f (Hamiltonian.dotCLMHam (g p)) p := by
  intro p
  rw [hasFDerivAt_iff_isLittleO]
  -- The remainder `r y = f y - f p - g p ⬝ (y - p)`.
  -- Lower bound `0 ≤ r y` from `hsub p` at `y`;
  -- upper bound `r y ≤ (g y - g p) ⬝ (y - p)` from `hsub y` at `p`.
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- By continuity of `g` at `p`, `d * ‖g y - g p‖ < c` eventually.
  have hg_tendsto : Tendsto (fun y => (d : ℝ) * ‖g y - g p‖) (𝓝 p) (𝓝 0) := by
    have h0 : Tendsto (fun y => g y - g p) (𝓝 p) (𝓝 0) := by
      have := (hg.tendsto p).sub (tendsto_const_nhds (x := g p) (f := 𝓝 p))
      simpa using this
    have hnorm : Tendsto (fun y => ‖g y - g p‖) (𝓝 p) (𝓝 0) := by
      have := (continuous_norm.tendsto (0 : Fin d → ℝ)).comp h0
      simpa only [Function.comp_def, norm_zero] using this
    have := hnorm.const_mul (d : ℝ)
    simpa using this
  have hev : ∀ᶠ y in 𝓝 p, (d : ℝ) * ‖g y - g p‖ < c :=
    hg_tendsto.eventually (eventually_lt_nhds (by simpa using hc))
  filter_upwards [hev] with y hy
  -- Abbreviation: the remainder.
  set r : ℝ := f y - f p - Hamiltonian.dotCLMHam (g p) (y - p) with hr
  -- Lower bound: `0 ≤ r`.
  have hlow : (0 : ℝ) ≤ r := by
    have := hsub p y
    -- `f p + ∑ i, g p i * (y i - p i) ≤ f y`
    rw [subgrad_sum_eq_dot] at this
    have hdot : Hamiltonian.dotCLMHam (g p) (y - p) = g p ⬝ (y - p) := rfl
    rw [hr, hdot]; linarith
  -- Upper bound: `r ≤ (g y - g p) ⬝ (y - p)`.
  have hupp : r ≤ (g y - g p) ⬝ (y - p) := by
    have := hsub y p
    -- `f y + ∑ i, g y i * (p i - y i) ≤ f p`
    rw [subgrad_sum_eq_dot] at this
    -- `g y ⬝ (p - y) = -(g y ⬝ (y - p))`
    have hpy : g y ⬝ (p - y) = -(g y ⬝ (y - p)) := by
      unfold euclideanDot
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Pi.sub_apply]; ring
    rw [hpy] at this
    -- `this : f y - g y ⬝ (y - p) ≤ f p`, i.e. `f y - f p ≤ g y ⬝ (y - p)`.
    have hdot : Hamiltonian.dotCLMHam (g p) (y - p) = g p ⬝ (y - p) := rfl
    have hsub_dot : (g y - g p) ⬝ (y - p) = g y ⬝ (y - p) - g p ⬝ (y - p) := by
      unfold euclideanDot
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Pi.sub_apply]; ring
    rw [hr, hdot, hsub_dot]; linarith
  -- `|r| ≤ d * ‖g y - g p‖ * ‖y - p‖` from the sandwich + dot-product bound.
  have hbound : |r| ≤ (d : ℝ) * ‖g y - g p‖ * ‖y - p‖ := by
    have hdotbound : |(g y - g p) ⬝ (y - p)| ≤ (d : ℝ) * ‖g y - g p‖ * ‖y - p‖ :=
      abs_euclideanDot_le_card_mul_norm (d := d) (g y - g p) (y - p)
    have hr_le : r ≤ (d : ℝ) * ‖g y - g p‖ * ‖y - p‖ :=
      le_trans hupp (le_trans (le_abs_self _) hdotbound)
    rw [abs_le]
    refine ⟨?_, hr_le⟩
    have : (0 : ℝ) ≤ (d : ℝ) * ‖g y - g p‖ * ‖y - p‖ :=
      le_trans (abs_nonneg _) hdotbound
    linarith
  -- Conclude `‖r‖ ≤ c * ‖y - p‖`.
  have hnorm_nn : (0 : ℝ) ≤ ‖y - p‖ := norm_nonneg _
  calc ‖f y - f p - Hamiltonian.dotCLMHam (g p) (y - p)‖
      = |r| := by rw [hr]; rw [Real.norm_eq_abs]
    _ ≤ (d : ℝ) * ‖g y - g p‖ * ‖y - p‖ := hbound
    _ = ((d : ℝ) * ‖g y - g p‖) * ‖y - p‖ := by ring
    _ ≤ c * ‖y - p‖ := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hy) hnorm_nn

/-! ## Task 2 — FTC slice from a continuous gradient -/

/-- For a fixed `p`, the curve `t ↦ t • p` has derivative `p` at every `t`. -/
private lemma hasDerivAt_smul_line (p : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s • p) p t := by
  have := (hasDerivAt_id t).smul_const p
  simpa using this

/-- **Task 2 — FTC-slice identity from a continuous gradient field.**

If `F` is Fréchet-differentiable everywhere with derivative `dotCLMHam (G ·)`
for a **continuous** gradient field `G`, then the paper's FTC-slice integral
identity `eq:DpHdelta.dotp.minusH` holds:

`G p ⬝ p − (F p − F 0) = ∫₀¹ (G p − G (t • p)) ⬝ p dt`.

Proof: the 1-D curve `φ t = F (t • p)` has derivative `φ' t = G (t • p) ⬝ p`
(chain rule); `φ'` is continuous hence interval-integrable; the 1-D fundamental
theorem of calculus gives `F p − F 0 = ∫₀¹ G (t • p) ⬝ p dt`; subtracting from
the constant `∫₀¹ G p ⬝ p dt = G p ⬝ p` and combining the integrals yields the
claim. -/
theorem ftc_slice_of_hasFDerivAt_continuous_gradient
    {F : (Fin d → ℝ) → ℝ}
    {G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hderiv : ∀ p, HasFDerivAt F (Hamiltonian.dotCLMHam (G p)) p)
    (hG : Continuous G) :
    ∀ p, G p ⬝ p - (F p - F 0)
        = ∫ t in (0:ℝ)..1, ((G p - G (t • p)) ⬝ p) := by
  intro p
  -- The 1-D curve and its derivative.
  set φ : ℝ → ℝ := fun t => F (t • p) with hφ
  set φ' : ℝ → ℝ := fun t => G (t • p) ⬝ p with hφ'
  -- Chain rule: `φ' t = G (t • p) ⬝ p` is the derivative of `φ`.
  have hφderiv : ∀ t : ℝ, HasDerivAt φ (φ' t) t := by
    intro t
    have hcomp : HasDerivAt (F ∘ (fun s : ℝ => s • p))
        (Hamiltonian.dotCLMHam (G (t • p)) p) t :=
      (hderiv (t • p)).comp_hasDerivAt t (hasDerivAt_smul_line p t)
    have : HasDerivAt φ (Hamiltonian.dotCLMHam (G (t • p)) p) t := hcomp
    simpa [hφ'] using this
  -- Continuity of the integrand `φ'`.
  have hφ'_cont : Continuous φ' := by
    have hcurve : Continuous (fun t : ℝ => t • p) := by
      exact (continuous_id.smul continuous_const)
    have hGcomp : Continuous (fun t : ℝ => G (t • p)) := hG.comp hcurve
    -- `t ↦ G (t • p) ⬝ p = dotCLMHam p (G (t • p))` is continuous.
    have : Continuous (fun t : ℝ => Hamiltonian.dotCLMHam p (G (t • p))) :=
      (Hamiltonian.dotCLMHam p).continuous.comp hGcomp
    have hsymm : (fun t : ℝ => Hamiltonian.dotCLMHam p (G (t • p)))
        = φ' := by
      funext t
      simp only [hφ', Hamiltonian.dotCLMHam_apply]
      -- `p ⬝ G (t•p) = G (t•p) ⬝ p`
      unfold euclideanDot
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rwa [hsymm] at this
  -- FTC: `∫₀¹ φ' = φ 1 - φ 0 = F p - F 0`.
  have hFTC : (∫ t in (0:ℝ)..1, φ' t) = F p - F 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := φ) (f' := φ') (a := 0) (b := 1)
      (fun t _ => hφderiv t) (hφ'_cont.intervalIntegrable 0 1)
    simpa [hφ, one_smul, zero_smul] using h
  -- Combine: `G p ⬝ p - (F p - F 0) = ∫₀¹ (G p ⬝ p - φ' t) = ∫₀¹ (G p - G(t•p))⬝p`.
  have hconst : (∫ _t in (0:ℝ)..1, (G p ⬝ p)) = G p ⬝ p := by
    simp
  have hintdiff :
      (∫ t in (0:ℝ)..1, ((G p - G (t • p)) ⬝ p))
        = (∫ t in (0:ℝ)..1, (G p ⬝ p - φ' t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hφ']
    -- `(G p - G (t•p)) ⬝ p = G p ⬝ p - G (t•p) ⬝ p`
    unfold euclideanDot
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.sub_apply]; ring
  rw [hintdiff]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hφ'_cont.intervalIntegrable 0 1)]
  rw [hconst, hFTC]

end InfimalConvolution
end StationaryMFG
