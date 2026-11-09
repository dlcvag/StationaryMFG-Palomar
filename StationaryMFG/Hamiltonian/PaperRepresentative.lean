module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.PaperRegularity
public import StationaryMFG.Hamiltonian.PaperExtension
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Measurable periodic representatives of the momentum gradient

The paper's standing regularity (H1) identifies `DpH` with the derivative
for almost every spatial point. The older implementation additionally
requires a globally measurable, globally periodic gradient representative.
Here `canonicalGradient H` obtains that representative from coordinate
difference quotients of the positive-mass Hamiltonian alone. It agrees
with the supplied gradient simultaneously at all positive masses and
momenta for almost every spatial point.

Together with `finiteExtension H`, this constructs the older regularity
and monotonicity bundles without additional public hypotheses. No finite
boundary-limit assumption is needed for these positive-mass properties.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Topology Set StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- Ignore arbitrary values of the supplied Hamiltonian at nonpositive mass. -/
noncomputable def positiveValue
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) (m : ℝ) : ℝ :=
  if 0 < m then H x p m else 0

@[simp] theorem positiveValue_of_pos
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) {m : ℝ} (hm : 0 < m) :
    positiveValue H x p m = H x p m := if_pos hm

theorem positiveValue_periodic
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) (m : ℝ) : IsPeriodic (fun x => positiveValue H x p m) := by
  by_cases hm : 0 < m
  · simpa only [positiveValue, if_pos hm] using hper p m hm
  · simpa only [positiveValue, if_neg hm] using IsPeriodic.const (0 : ℝ)

theorem positiveValue_measurable
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      positiveValue H xpm.1 xpm.2.1 xpm.2.2) := by
  let s : Set ((Fin d → ℝ) × (Fin d → ℝ) × ℝ) := {xpm | 0 < xpm.2.2}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_snd.snd
  have hpos : Measurable (fun xpm : s => H xpm.1.1 xpm.1.2.1 xpm.1.2.2) := by
    exact hH.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
      (((measurable_fst.comp measurable_snd).comp measurable_subtype_coe).prodMk
        (((measurable_snd.comp measurable_snd).comp measurable_subtype_coe).subtype_mk
          (h := fun y => y.property))))
  exact hpos.dite (measurable_const (a := (0 : ℝ))) hs

/-- A gradient representative defined by limits of coordinate difference
quotients. At exceptional spatial points a missing limit is handled by
`limUnder`; no assertion about a derivative at those points is required. -/
noncomputable def canonicalGradient
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  fun i => limUnder atTop (fun n : ℕ =>
    (positiveValue H x (p + boundaryMass n • (Pi.single i 1 : Fin d → ℝ)) m -
      positiveValue H x p m) /
      boundaryMass n)

theorem canonicalGradient_periodic
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) (m : ℝ) : IsPeriodic (fun x => canonicalGradient H x p m) := by
  intro k x
  funext i
  apply congrArg (limUnder atTop)
  funext n
  exact congrArg (fun r : ℝ => r / boundaryMass n)
    (congrArg₂ (fun a b : ℝ => a - b)
      (positiveValue_periodic hper (p + boundaryMass n • (Pi.single i 1 : Fin d → ℝ)) m k x)
      (positiveValue_periodic hper p m k x))

theorem canonicalGradient_measurable
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      canonicalGradient H xpm.1 xpm.2.1 xpm.2.2) := by
  apply measurable_pi_lambda
  intro i
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  have hpos := positiveValue_measurable hH
  have hshift : Measurable
      (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        (xpm.1, xpm.2.1 + boundaryMass n • (Pi.single i 1 : Fin d → ℝ), xpm.2.2)) :=
    measurable_fst.prodMk
      ((measurable_snd.fst.add_const _).prodMk measurable_snd.snd)
  exact (((hpos.comp hshift).sub hpos).div_const (boundaryMass n)).stronglyMeasurable

/-- At a point where the momentum derivative exists everywhere, the
coordinate difference quotients recover the supplied gradient. -/
theorem canonicalGradient_eq_of_hasFDerivAt
    {x : Fin d → ℝ} {m : ℝ} (hm : 0 < m)
    (hdiff : ∀ p, HasFDerivAt (fun q => H x q m) (dotCLMHam (DpH x p m)) p)
    (p : Fin d → ℝ) : canonicalGradient H x p m = DpH x p m := by
  funext i
  have hd := hasDerivAt_momentum_line hdiff p (Pi.single i 1 : Fin d → ℝ) 0
  have ht := hd.tendsto_slope_zero_right.comp boundaryMass_tendsto
  have hlim : Tendsto
      (fun n : ℕ =>
        (positiveValue H x (p + boundaryMass n • (Pi.single i 1 : Fin d → ℝ)) m -
          positiveValue H x p m) /
          boundaryMass n) atTop (𝓝 (DpH x p m i)) := by
    simpa [Function.comp_def, positiveValue, hm, dotProduct, Pi.single_apply,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  exact hlim.limUnder_eq

/-- The canonical representative agrees with the supplied gradient on
positive mass, with a single exceptional set for all momenta and masses. -/
theorem RegularityH.canonicalGradient_eq (hreg : RegularityH H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      canonicalGradient H x p m = DpH x p m := by
  filter_upwards [hreg.hasFDerivAt_H_p] with x hx
  intro p m hm
  exact canonicalGradient_eq_of_hasFDerivAt hm (fun q => hx q m hm) p

/-- Positive-mass joint continuity is preserved by the canonical gradient. -/
theorem RegularityH.continuous_canonicalGradient_pm (hreg : RegularityH H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => canonicalGradient H x pm.1 pm.2)
        {pm | 0 < pm.2} := by
  filter_upwards [hreg.continuous_DpH_pm, hreg.canonicalGradient_eq] with x hx heq
  exact hx.congr (fun pm hpm => heq pm.1 pm.2 hpm)

/-- The canonical representative is the genuine momentum derivative on
the same almost-everywhere set as the supplied gradient. -/
theorem RegularityH.hasFDerivAt_canonicalGradient (hreg : RegularityH H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      HasFDerivAt (fun q => H x q m) (dotCLMHam (canonicalGradient H x p m)) p := by
  filter_upwards [hreg.hasFDerivAt_H_p, hreg.canonicalGradient_eq] with x hx heq
  intro p m hm
  rw [heq p m hm]
  exact hx p m hm

/-- The canonical Hamiltonian and gradient satisfy all requirements of
the older regularity bundle. Boundary finiteness is not needed here. -/
def RegularityH.finiteExtension_regularity (hreg : RegularityH H DpH) :
    Hamiltonian.RegularityH (finiteExtension H) (canonicalGradient H) where
  periodic_H := finiteExtension_periodic hreg.periodic_H
  periodic_DpH := canonicalGradient_periodic hreg.periodic_H
  measurable_H := finiteExtension_measurable hreg.measurable_H
  measurable_DpH := canonicalGradient_measurable hreg.measurable_H
  continuous_H_pm := by
    filter_upwards [hreg.continuous_H_pm] with x hx
    exact hx.congr (fun pm hpm => finiteExtension_of_pos H x pm.1 hpm)
  continuous_DpH_pm := hreg.continuous_canonicalGradient_pm

/-- The representative pair also retains the paper derivative certificate,
so its FTC identity can be derived directly. -/
def RegularityH.finiteExtension_paper_regularity (hreg : RegularityH H DpH) :
    RegularityH (finiteExtension H) (canonicalGradient H) where
  periodic_H := fun p m _ => finiteExtension_periodic hreg.periodic_H p m
  measurable_H := by
    convert hreg.measurable_H using 1
    ext xpm
    exact finiteExtension_of_pos H xpm.1 xpm.2.1 xpm.2.2.property
  continuous_H_pm := hreg.finiteExtension_regularity.continuous_H_pm
  hasFDerivAt_H_p := by
    filter_upwards [hreg.hasFDerivAt_canonicalGradient] with x hx
    intro p m hm
    simpa only [finiteExtension_of_pos H x _ hm] using hx p m hm
  continuous_DpH_pm := hreg.continuous_canonicalGradient_pm

/-- The implementation's FTC field and global representative conditions
follow from the paper assumptions after choosing canonical representatives. -/
def HypothesisMonotone.finiteExtension_monotone (hmon : HypothesisMonotone H DpH) :
    Hamiltonian.HypothesisMonotone (finiteExtension H) (canonicalGradient H) where
  toRegularityH := hmon.toRegularityH.finiteExtension_regularity
  monotone := by
    filter_upwards [hmon.monotone, hmon.toRegularityH.canonicalGradient_eq] with x hx heq
    intro p₁ m₁ p₂ m₂ hm₁ hm₂
    simpa only [finiteExtension_of_pos H x _ hm₁, finiteExtension_of_pos H x _ hm₂,
      heq p₁ m₁ hm₁, heq p₂ m₂ hm₂] using hx p₁ m₁ p₂ m₂ hm₁ hm₂
  lagr_ftc_slice := hmon.toRegularityH.finiteExtension_paper_regularity.lagr_ftc_slice

end StationaryMFG.Hamiltonian.Paper
