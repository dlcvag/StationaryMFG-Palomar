module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.Congestion

@[expose] public section

/-!
# The three original simple-power growth bounds

`HypothesisPowerGrowthCore` records exactly the three inequalities in paper
Assumption `onH.powergrowth` (Source/FGU-monotone_revised.tex, lines 458–465),
over the current `RegularityH` representation. With the existing
`HypothesisMonotone`, it produces the implementation's `HypothesisPowerGrowth`:
the Lagrangian bound follows from `convex_at_zero`, and the all-momentum upper
bound follows from the gradient estimate and Young's inequality. Both use the
radial FTC identity already contained in `HypothesisMonotone`.

The common growth constant may increase; the exponents are preserved exactly.
This is an internal migration bridge, not a final paper-faithful public API:
`RegularityH` and `HypothesisMonotone` still contain their existing encoding
choices and explicit radial FTC premise.
-/

namespace StationaryMFG.Hamiltonian

open MeasureTheory
open StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The three inequalities of paper Assumption `onH.powergrowth`, without
the two derived-estimate fields of `HypothesisPowerGrowth`. -/
structure HypothesisPowerGrowthCore
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

private lemma dot_le_dimension_norm (v w : Fin d → ℝ) :
    v ⬝ w ≤ (d : ℝ) * ‖v‖ * ‖w‖ := by
  calc
    v ⬝ w ≤ ∑ _i : Fin d, ‖v‖ * ‖w‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        v i * w i ≤ |v i * w i| := le_abs_self _
        _ = |v i| * |w i| := abs_mul _ _
        _ ≤ ‖v‖ * ‖w‖ := by
          exact mul_le_mul (by simpa using norm_le_pi_norm v i)
            (by simpa using norm_le_pi_norm w i) (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖v‖ * ‖w‖ := by simp [mul_assoc]

/-- The upper estimate before absorbing its mixed mass/momentum term. The
dimension factor is required because the momentum norm is the product norm. -/
lemma HypothesisPowerGrowthCore.upper_before_young
    (h : HypothesisPowerGrowthCore H DpH) (hmon : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      H x p m ≤ -(m ^ h.β) / h.C + h.C
        + ((d : ℝ) * h.C) * ‖p‖ ^ h.α
        + ((d : ℝ) * h.C) * (‖p‖ * (m ^ (h.β - h.β / h.α) + 1)) := by
  filter_upwards [h.upper, h.DpH_upper, hmon.convex_at_zero] with x hUp hDp hCx
  intro p m hm
  have hcollapse : ‖p‖ ^ (h.α - 1) * ‖p‖ = ‖p‖ ^ h.α := by
    have hr := Real.rpow_add_one' (norm_nonneg p)
      (y := h.α - 1) (by linarith [h.hα] : h.α - 1 + 1 ≠ 0)
    simpa using hr.symm
  have hdot := dot_le_dimension_norm (DpH x p m) p
  have hmul := mul_le_mul_of_nonneg_left (hDp p m hm)
    (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg p))
  have hdot_bound : (DpH x p m) ⬝ p ≤ ((d : ℝ) * h.C) * ‖p‖ ^ h.α
      + ((d : ℝ) * h.C) * (‖p‖ * (m ^ (h.β - h.β / h.α) + 1)) := by
    calc
      (DpH x p m) ⬝ p
          ≤ ((d : ℝ) * ‖p‖) *
              (h.C * (‖p‖ ^ (h.α - 1) + m ^ (h.β - h.β / h.α) + 1)) := by
            nlinarith [hdot, hmul]
      _ = ((d : ℝ) * h.C) * (‖p‖ ^ (h.α - 1) * ‖p‖)
          + ((d : ℝ) * h.C) * (‖p‖ * (m ^ (h.β - h.β / h.α) + 1)) := by ring
      _ = _ := by rw [hcollapse]
  linarith [hUp m hm, hCx p m hm, hdot_bound]

/-- Paper Lemma `lem:ADFGU`: the all-momentum upper bound is a consequence
of the three core bounds and the existing monotonicity/FTC bundle. The new
constant also dominates the old constant, so all original bounds persist. -/
theorem HypothesisPowerGrowthCore.exists_upper_constant
    (h : HypothesisPowerGrowthCore H DpH) (hmon : HypothesisMonotone H DpH) :
    ∃ C' : ℝ, 0 < C' ∧ h.C ≤ C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
        H x p m ≤ C' * (‖p‖ ^ h.α + 1) - (m ^ h.β) / C' := by
  have hC : 0 < h.C := h.hC
  -- The general Young estimate is independent of a Hamiltonian bundle.
  -- Its τ=0 specialization is exactly the simple-power mixed term.
  obtain ⟨c, hc, hyoung⟩ := young_congestion_case (d := d) h.hα h.hβ (le_refl (0 : ℝ))
  let D : ℝ := (d : ℝ) * h.C
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg d) h.hC.le
  let B : ℝ := D * c
  have hB : 0 ≤ B := mul_nonneg hD hc.le
  let θ : ℝ := 1 / (2 * h.C * (B + 1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have ht : 0 < θ ^ (h.α - 1) := Real.rpow_pos_of_pos hθ _
  have hBθ : B * θ ≤ 1 / (2 * h.C) := by
    have hfrac : B / (B + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < B + 1)).2 (by linarith)
    calc
      B * θ = (B / (B + 1)) / (2 * h.C) := by
        dsimp [θ]
        field_simp
      _ ≤ 1 / (2 * h.C) := div_le_div_of_nonneg_right hfrac (by positivity)
  let A : ℝ := D + B / (θ ^ (h.α - 1) * 2)
  let E : ℝ := h.C + B * θ
  let C' : ℝ := max h.C (max (2 * h.C) (max A E))
  have hCC' : h.C ≤ C' := le_max_left _ _
  have hC' : 0 < C' := lt_of_lt_of_le h.hC hCC'
  have h2CC' : 2 * h.C ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hAC' : A ≤ C' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hEC' : E ≤ C' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C', hC', hCC', ?_⟩
  filter_upwards [h.upper_before_young hmon] with x hx
  intro p m hm
  have hp : 0 ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg p) _
  have hmβ : 0 ≤ m ^ h.β := Real.rpow_nonneg hm.le _
  have hy : ‖p‖ * (m ^ (h.β - h.β / h.α) + 1) ≤
      c * (‖p‖ ^ h.α / (θ ^ (h.α - 1) * 2) + θ * (m ^ h.β + 1)) := by
    simpa only [zero_div, add_zero, zero_add, mul_one, Real.rpow_zero,
      one_add_one_eq_two] using hyoung θ m hθ hm p
  have hdy := mul_le_mul_of_nonneg_left hy hD
  have hpre : H x p m ≤ A * ‖p‖ ^ h.α + E
      - (m ^ h.β) / h.C + B * θ * (m ^ h.β) := by
    have hx' := hx p m hm
    change H x p m ≤ -(m ^ h.β) / h.C + h.C + D * ‖p‖ ^ h.α
      + D * (‖p‖ * (m ^ (h.β - h.β / h.α) + 1)) at hx'
    calc
      H x p m ≤ -(m ^ h.β) / h.C + h.C + D * ‖p‖ ^ h.α
          + D * (c * (‖p‖ ^ h.α / (θ ^ (h.α - 1) * 2)
            + θ * (m ^ h.β + 1))) := by linarith
      _ = _ := by dsimp [A, E, B]; ring
  have hmass : B * θ * (m ^ h.β) ≤ (m ^ h.β) / (2 * h.C) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      mul_le_mul_of_nonneg_right hBθ hmβ
  have hdiv := div_le_div_of_nonneg_left hmβ (by positivity : 0 < 2 * h.C) h2CC'
  have hcoeff := mul_le_mul_of_nonneg_right hAC' hp
  have hhalf : (m ^ h.β) / h.C = 2 * ((m ^ h.β) / (2 * h.C)) := by ring
  calc
    H x p m ≤ C' * (‖p‖ ^ h.α + 1) - (m ^ h.β) / (2 * h.C) := by
      nlinarith [hpre, hmass, hcoeff, hEC', hhalf]
    _ ≤ C' * (‖p‖ ^ h.α + 1) - (m ^ h.β) / C' := by linarith

/-- Enlarge the common constant and supply both derived fields of the old
implementation bundle. The exponents remain definitionally unchanged. -/
noncomputable def HypothesisPowerGrowthCore.toHypothesisPowerGrowth
    (h : HypothesisPowerGrowthCore H DpH) (hmon : HypothesisMonotone H DpH) :
    HypothesisPowerGrowth H DpH := by
  let C' := Classical.choose (h.exists_upper_constant hmon)
  have hspec := Classical.choose_spec (h.exists_upper_constant hmon)
  have hC' : 0 < C' := hspec.1
  have hCC' : h.C ≤ C' := hspec.2.1
  exact
    { toRegularityH := h.toRegularityH
      C := C'
      α := h.α
      β := h.β
      hC := hC'
      hα := h.hα
      hβ := h.hβ
      upper := by
        filter_upwards [h.upper] with x hx m hm
        have hdiv := div_le_div_of_nonneg_left (Real.rpow_nonneg hm.le h.β) h.hC hCC'
        have := hx m hm
        simp only [neg_div] at this ⊢
        linarith
      DpH_upper := by
        filter_upwards [h.DpH_upper] with x hx p m hm
        exact (hx p m hm).trans (mul_le_mul_of_nonneg_right hCC' (by positivity))
      lower := by
        filter_upwards [h.lower] with x hx p m hm
        have hdiv := div_le_div_of_nonneg_left
          (Real.rpow_nonneg (norm_nonneg p) h.α) h.hC hCC'
        have hmul := mul_le_mul_of_nonneg_right hCC'
          (show 0 ≤ m ^ h.β + 1 by positivity)
        have := hx p m hm
        linarith
      H_upper_pointwise := hspec.2.2
      lagr := by
        filter_upwards [h.upper, hmon.convex_at_zero] with x hx hcx p m hm
        have hdiv := div_le_div_of_nonneg_left (Real.rpow_nonneg hm.le h.β) h.hC hCC'
        have := hx m hm
        simp only [neg_div] at this
        have := hcx p m hm
        linarith }

@[simp] theorem HypothesisPowerGrowthCore.toHypothesisPowerGrowth_alpha
    (h : HypothesisPowerGrowthCore H DpH) (hmon : HypothesisMonotone H DpH) :
    (h.toHypothesisPowerGrowth hmon).α = h.α := rfl

@[simp] theorem HypothesisPowerGrowthCore.toHypothesisPowerGrowth_beta
    (h : HypothesisPowerGrowthCore H DpH) (hmon : HypothesisMonotone H DpH) :
    (h.toHypothesisPowerGrowth hmon).β = h.β := rfl

theorem HypothesisPowerGrowthCore.le_toHypothesisPowerGrowth_C
    (h : HypothesisPowerGrowthCore H DpH) (hmon : HypothesisMonotone H DpH) :
    h.C ≤ (h.toHypothesisPowerGrowth hmon).C :=
  (Classical.choose_spec (h.exists_upper_constant hmon)).2.1

end StationaryMFG.Hamiltonian
