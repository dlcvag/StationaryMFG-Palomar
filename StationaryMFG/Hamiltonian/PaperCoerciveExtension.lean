module

public import StationaryMFG.Hamiltonian.PaperRepresentative
public import StationaryMFG.Theorems.Congestion.PaperCore

@[expose] public section

/-!
# A coercive real representative for singular Hamiltonians

Infinite boundary values have no real representative. Away from the finite
boundary domain, the internal real extension may be chosen arbitrarily. We
choose it above the coercive lower bound so that the existing a priori estimate
kernels apply. At every finite boundary limit it still equals the actual limit.
The public solution uses Hext and never this arbitrary value at infinity.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Set Topology StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

noncomputable def coerciveExtension
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) (α C : ℝ)
    (x p : Fin d → ℝ) (m : ℝ) : ℝ :=
  if 0 < m then H x p m else max (boundaryTrace H x p) (‖p‖ ^ α / C - C)

@[simp] theorem coerciveExtension_of_pos (α C : ℝ) (x p : Fin d → ℝ)
    {m : ℝ} (hm : 0 < m) : coerciveExtension H α C x p m = H x p m := if_pos hm

theorem coerciveExtension_lower_zero (α C : ℝ) (x p : Fin d → ℝ) :
    ‖p‖ ^ α / C - C ≤ coerciveExtension H α C x p 0 := by
  simp only [coerciveExtension, lt_self_iff_false, ↓reduceIte]
  exact le_max_right _ _

private theorem measurable_extension_max
    (F : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (B : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (α C : ℝ)
    (hF : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      F xpm.1 xpm.2.1 xpm.2.2))
    (hB : Measurable (fun xp : (Fin d → ℝ) × (Fin d → ℝ) => B xp.1 xp.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      if 0 < xpm.2.2 then F xpm.1 xpm.2.1 xpm.2.2
      else max (B xpm.1 xpm.2.1) (‖xpm.2.1‖ ^ α / C - C)) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd.snd) hF
  exact (hB.comp (measurable_fst.prodMk measurable_snd.fst)).max
    (((measurable_snd.fst.norm.pow_const α).div_const C).sub_const C)

theorem coerciveExtension_measurable (α C : ℝ)
    (hH : Measurable
      (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m} =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      coerciveExtension H α C xpm.1 xpm.2.1 xpm.2.2) := by
  have hm := measurable_extension_max (positiveValue H) (boundaryTrace H) α C
    (positiveValue_measurable hH) (boundaryTrace_measurable hH)
  convert hm using 1
  funext xpm
  by_cases hx : 0 < xpm.2.2 <;> simp [coerciveExtension, positiveValue, hx]

theorem coerciveExtension_periodic (α C : ℝ)
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) (m : ℝ) : IsPeriodic (fun x => coerciveExtension H α C x p m) := by
  intro k x
  by_cases hm : 0 < m
  · simpa only [coerciveExtension, if_pos hm] using hper p m hm k x
  · simp only [coerciveExtension, if_neg hm, boundaryTrace_periodic hper p k x]

theorem coerciveExtension_zero_of_tendsto (α C : ℝ) {x p : Fin d → ℝ} {L : ℝ}
    (hL : Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hlower : ‖p‖ ^ α / C - C ≤ L) : coerciveExtension H α C x p 0 = L := by
  simp only [coerciveExtension, lt_self_iff_false, ↓reduceIte,
    boundaryTrace_eq_of_tendsto hL, max_eq_left hlower]

def RegularityH.coerciveExtension_regularity (hreg : RegularityH H DpH) (α C : ℝ) :
    Hamiltonian.RegularityH (coerciveExtension H α C) (canonicalGradient H) where
  periodic_H := coerciveExtension_periodic α C hreg.periodic_H
  periodic_DpH := canonicalGradient_periodic hreg.periodic_H
  measurable_H := coerciveExtension_measurable α C hreg.measurable_H
  measurable_DpH := canonicalGradient_measurable hreg.measurable_H
  continuous_H_pm := by
    filter_upwards [hreg.continuous_H_pm] with x hx
    exact hx.congr (fun pm hpm => coerciveExtension_of_pos α C x pm.1 hpm)
  continuous_DpH_pm := hreg.continuous_canonicalGradient_pm

def RegularityH.coerciveExtension_paper_regularity (hreg : RegularityH H DpH) (α C : ℝ) :
    RegularityH (coerciveExtension H α C) (canonicalGradient H) where
  periodic_H := fun p m _ => coerciveExtension_periodic α C hreg.periodic_H p m
  measurable_H := by
    convert hreg.measurable_H using 1
    ext xpm
    exact coerciveExtension_of_pos α C xpm.1 xpm.2.1 xpm.2.2.property
  continuous_H_pm := (hreg.coerciveExtension_regularity α C).continuous_H_pm
  hasFDerivAt_H_p := by
    filter_upwards [hreg.hasFDerivAt_canonicalGradient] with x hx
    intro p m hm
    simpa only [coerciveExtension_of_pos α C x _ hm] using hx p m hm
  continuous_DpH_pm := hreg.continuous_canonicalGradient_pm

def HypothesisMonotone.coerciveExtension_monotone
    (hmon : HypothesisMonotone H DpH) (α C : ℝ) :
    Hamiltonian.HypothesisMonotone (coerciveExtension H α C) (canonicalGradient H) where
  toRegularityH := hmon.toRegularityH.coerciveExtension_regularity α C
  monotone := by
    filter_upwards [hmon.monotone, hmon.toRegularityH.canonicalGradient_eq] with x hx he
    intro p₁ m₁ p₂ m₂ hm₁ hm₂
    simpa only [coerciveExtension_of_pos α C x _ hm₁,
      coerciveExtension_of_pos α C x _ hm₂, he p₁ m₁ hm₁, he p₂ m₂ hm₂]
      using hx p₁ m₁ p₂ m₂ hm₁ hm₂
  lagr_ftc_slice := (hmon.toRegularityH.coerciveExtension_paper_regularity α C).lagr_ftc_slice

theorem lower_of_finite_boundary (h : CongestionAprioriPowerData H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → ‖p‖ ^ h.α / h.C - h.C ≤ L := by
  filter_upwards [h.lower] with x hx p L hL
  have ht : ContinuousAt
      (fun m : ℝ => ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1)) 0 :=
    continuousAt_const.sub (continuousAt_const.mul
      (((Real.continuous_rpow_const h.hβ.le).continuousAt).add continuousAt_const))
  have hbound : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x p m := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact hx p m hm
  have hl := le_of_tendsto_of_tendsto
    (ht.tendsto.mono_left nhdsWithin_le_nhds) hL hbound
  simpa only [Real.zero_rpow h.hβ.ne', zero_add, mul_one] using hl

end StationaryMFG.Hamiltonian.Paper
