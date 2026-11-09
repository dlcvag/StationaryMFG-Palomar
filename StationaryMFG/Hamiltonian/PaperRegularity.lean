module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.Differentiability
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The paper's regularity and monotonicity assumptions

`Paper.RegularityH` records the standing regularity (H1) of
`Source/FGU-monotone_revised.tex`, with `DpH` certified to be the genuine
momentum derivative. Its periodicity and measurability conditions concern
strictly positive mass only. `Paper.HypothesisMonotone` adds precisely the
Lasry–Lions inequality (A1).

The radial FTC identity used in Lemma `lem:A1+anyother` and momentum
convexity in Remark `rmk:cxty` are consequences proved below, rather than
additional fields of these bundles.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory StationaryMFG.Periodic

variable {d : ℕ}

/-- Standing assumption (H1), including the meaning of the notation `D_pH`.
No value at nonpositive mass is constrained by this structure. -/
structure RegularityH
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  periodic_H : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m)
  measurable_H : Measurable
    (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
      H xpm.1 xpm.2.1 xpm.2.2)
  continuous_H_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
        {pm | 0 < pm.2}
  hasFDerivAt_H_p :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        HasFDerivAt (fun q : Fin d → ℝ => H x q m) (dotCLMHam (DpH x p m)) p
  continuous_DpH_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
        {pm | 0 < pm.2}

/-- Assumption (A1), without an additional FTC or convexity field. -/
structure HypothesisMonotone
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop
    extends RegularityH H DpH where
  monotone :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
        0 ≤ (-H x p₁ m₁ + H x p₂ m₂) * (m₁ - m₂)
              + (m₁ • DpH x p₁ m₁ - m₂ • DpH x p₂ m₂) ⬝ (p₁ - p₂)

section Pointwise

variable {F : (Fin d → ℝ) → ℝ} {G : (Fin d → ℝ) → (Fin d → ℝ)}

/-- Chain rule along an affine momentum line. -/
lemma hasDerivAt_momentum_line
    (hderiv : ∀ p, HasFDerivAt F (dotCLMHam (G p)) p)
    (p v : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (p + s • v)) (G (p + t • v) ⬝ v) t := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  simpa [Function.comp_def] using (hderiv (p + t • v)).comp_hasDerivAt t hline

/-- Continuity of the gradient pairing along an affine momentum line. -/
lemma continuous_gradient_line (hG : Continuous G) (p v : Fin d → ℝ) :
    Continuous (fun t : ℝ => G (p + t • v) ⬝ v) := by
  have hline : Continuous (fun t : ℝ => G (p + t • v)) := hG.comp (by fun_prop)
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hline).mul continuous_const

/-- FTC along a momentum segment, with no monotonicity requirement. -/
lemma integral_gradient_line
    (hderiv : ∀ p, HasFDerivAt F (dotCLMHam (G p)) p)
    (hG : Continuous G) (p v : Fin d → ℝ) :
    (∫ t in (0 : ℝ)..1, G (p + t • v) ⬝ v) = F (p + v) - F p := by
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_momentum_line hderiv p v t)
    ((continuous_gradient_line hG p v).intervalIntegrable 0 1)

/-- The radial Lagrangian identity follows from genuine differentiability
and a continuous gradient. -/
lemma lagr_ftc_slice_of_hasFDerivAt
    (hderiv : ∀ p, HasFDerivAt F (dotCLMHam (G p)) p)
    (hG : Continuous G) (p : Fin d → ℝ) :
    G p ⬝ p - (F p - F 0) =
      ∫ t in (0 : ℝ)..1, (G p - G (t • p)) ⬝ p := by
  have hInt : (∫ t in (0 : ℝ)..1, G (t • p) ⬝ p) = F p - F 0 := by
    simpa using integral_gradient_line hderiv hG 0 p
  have hcont : Continuous (fun t : ℝ => G (t • p) ⬝ p) := by
    simpa using continuous_gradient_line hG 0 p
  simp_rw [euclideanDot_sub_left]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable 0 1)]
  simp [hInt]

/-- A monotone gradient makes the restriction to each momentum line convex. -/
lemma convexOn_momentum_line
    (hderiv : ∀ p, HasFDerivAt F (dotCLMHam (G p)) p)
    (hmono : ∀ p q, 0 ≤ (G p - G q) ⬝ (p - q))
    (p v : Fin d → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => F (p + t • v)) := by
  let f : ℝ → ℝ := fun t => F (p + t • v)
  have hd (t : ℝ) : HasDerivAt f (G (p + t • v) ⬝ v) t :=
    hasDerivAt_momentum_line hderiv p v t
  have hmonoLine : Monotone (deriv f) := by
    intro s t hst
    rw [(hd s).deriv, (hd t).deriv]
    rcases eq_or_lt_of_le hst with rfl | hst
    · exact le_rfl
    have h := hmono (p + t • v) (p + s • v)
    have hsub : p + t • v - (p + s • v) = (t - s) • v := by
      module
    rw [hsub, euclideanDot_smul_right, euclideanDot_sub_left] at h
    have hdiff := (mul_nonneg_iff_of_pos_left (sub_pos.mpr hst)).mp h
    linarith
  exact Monotone.convexOn_univ_of_deriv (fun t => (hd t).differentiableAt) hmonoLine

/-- A genuine gradient satisfying the monotone-gradient inequality makes
its potential convex. This pointwise proof is independent of the mass variable. -/
lemma convexOn_of_monotone_gradient
    (hderiv : ∀ p, HasFDerivAt F (dotCLMHam (G p)) p)
    (hmono : ∀ p q, 0 ≤ (G p - G q) ⬝ (p - q)) :
    ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) F := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  have hc := convexOn_momentum_line hderiv hmono p (q - p)
  have hineq := hc.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
  have harg : p + b • (q - p) = a • p + b • q := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    ring
  simpa [harg] using hineq

/-- The supporting-hyperplane inequality from a genuine monotone gradient. -/
lemma supporting_hyperplane_of_monotone_gradient
    (hderiv : ∀ p, HasFDerivAt F (dotCLMHam (G p)) p)
    (hmono : ∀ p q, 0 ≤ (G p - G q) ⬝ (p - q))
    (p q : Fin d → ℝ) : F q + G q ⬝ (p - q) ≤ F p := by
  have hc := convexOn_momentum_line hderiv hmono q (p - q)
  have h := hc.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by norm_num)
    (hasDerivAt_momentum_line hderiv q (p - q) 0)
  simp [slope] at h
  simp only [dotProduct_sub]
  linarith

end Pointwise

variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The radial FTC identity of Lemma `lem:A1+anyother` is derived from (H1). -/
lemma RegularityH.lagr_ftc_slice (hreg : RegularityH H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      (DpH x p m) ⬝ p - (H x p m - H x (0 : Fin d → ℝ) m) =
        ∫ t in (0 : ℝ)..1, (DpH x p m - DpH x (t • p) m) ⬝ p := by
  filter_upwards [hreg.hasFDerivAt_H_p, hreg.continuous_DpH_pm] with x hdiff hcont
  intro p m hm
  have hG : Continuous (fun q : Fin d → ℝ => DpH x q m) :=
    hcont.comp_continuous (f := fun q : Fin d → ℝ => (q, m))
      (continuous_id.prodMk continuous_const) (fun _ => hm)
  exact lagr_ftc_slice_of_hasFDerivAt (fun q => hdiff q m hm) hG p

/-- Equal positive masses in (A1) give monotonicity of the momentum gradient. -/
lemma HypothesisMonotone.monotone_gradient (hmon : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ m, 0 < m → ∀ p q,
      0 ≤ (DpH x p m - DpH x q m) ⬝ (p - q) := by
  filter_upwards [hmon.monotone] with x hx
  intro m hm p q
  have h := hx p m q m hm hm
  rw [sub_self, mul_zero, zero_add, ← smul_sub, euclideanDot_smul_left] at h
  exact (mul_nonneg_iff_of_pos_left hm).mp h

/-- Momentum convexity in Remark `rmk:cxty` follows from (H1) and (A1). -/
lemma HypothesisMonotone.convexOn_H_p (hmon : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ m : ℝ, 0 < m →
      ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (fun p => H x p m) := by
  filter_upwards [hmon.hasFDerivAt_H_p, hmon.monotone_gradient] with x hdiff hmono
  intro m hm
  exact convexOn_of_monotone_gradient (fun p => hdiff p m hm) (hmono m hm)

/-- The supporting-hyperplane inequality at every positive mass, used in
the finite-boundary flux argument as well as the growth estimates. -/
lemma HypothesisMonotone.supporting_hyperplane (hmon : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p q m, 0 < m →
      H x q m + DpH x q m ⬝ (p - q) ≤ H x p m := by
  filter_upwards [hmon.hasFDerivAt_H_p, hmon.monotone_gradient] with x hdiff hmono
  intro p q m hm
  exact supporting_hyperplane_of_monotone_gradient
    (fun r => hdiff r m hm) (hmono m hm) p q

/-- The old differentiability/convexity bundle is an output of the paper
assumptions; its convexity field need not be independently assumed. -/
def HypothesisMonotone.toHypothesisHpDifferentiable (hmon : HypothesisMonotone H DpH) :
    Hamiltonian.HypothesisHpDifferentiable H DpH where
  hasFDerivAt_H_p := hmon.hasFDerivAt_H_p
  convexOn_H_p := hmon.convexOn_H_p

end StationaryMFG.Hamiltonian.Paper
