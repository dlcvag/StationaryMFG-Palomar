module

public import StationaryMFG.Theorems.Congestion.PaperGrowth
public import StationaryMFG.Theorems.Congestion.PaperCore
public import StationaryMFG.Hamiltonian.PaperFluxRepresentative
public import StationaryMFG.Hamiltonian.PaperCoerciveExtension

@[expose] public section

/-!
# Representatives for the unrestricted congestion proof

The literal paper assumptions construct all convenient implementation
representatives. The real boundary trace is only used at points subsequently
proved finite; no global finite-H or zero-flux premise is introduced.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Topology Set StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The canonical flux provides the implementation's measurable extension
interface without any restriction at vacuum. -/
def RegularityH.canonicalFluxCore (hreg : RegularityH H DpH)
    (hJ : PaperFluxExtension DpH J) :
    CongestionFluxCore (canonicalGradient H) (canonicalFlux H) where
  J_of_pos := (canonicalFlux_extension hreg hJ).J_of_pos
  tendsto_at_zero := (canonicalFlux_extension hreg hJ).tendsto_at_zero
  continuous_J := (canonicalFlux_extension hreg hJ).continuous_J
  measurable_J := canonicalFlux_measurable hreg.measurable_H

/-- Convert the paper-facing congestion assumptions to the implementation
core by proved canonical representatives. Constants and exponents are
preserved definitionally. -/
def HypothesisCongestionGrowth.toCore
    (h : HypothesisCongestionGrowth H DpH J) :
    CongestionGrowthCore (finiteExtension H) (canonicalGradient H) (canonicalFlux H) where
  toRegularityH := h.toRegularityH.finiteExtension_regularity
  C := h.C
  α := h.α
  β := h.β
  τ := h.τ
  hC := h.hC
  hα := h.hα
  hβ := h.hβ
  hτ := h.hτ
  mDpHat0 := h.toRegularityH.canonicalFluxCore h.mDpHat0
  upper := by
    filter_upwards [h.upper] with x hx
    intro m hm
    simpa only [finiteExtension_of_pos H x _ hm] using hx m hm
  DpH_upper := by
    filter_upwards [h.DpH_upper, h.toRegularityH.canonicalGradient_eq] with x hx hg
    intro p m hm
    simpa only [hg p m hm] using hx p m hm
  lower := by
    filter_upwards [h.lower] with x hx
    intro p m hm
    simpa only [finiteExtension_of_pos H x p hm] using hx p m hm

/-- A coercive real representative can also be used internally; its positive
mass data and the derived flux are unchanged. -/
def HypothesisCongestionGrowth.toCoerciveCore
    (h : HypothesisCongestionGrowth H DpH J) (α C : ℝ) :
    CongestionGrowthCore (coerciveExtension H α C) (canonicalGradient H) (canonicalFlux H) where
  toRegularityH := h.toRegularityH.coerciveExtension_regularity α C
  C := h.C
  α := h.α
  β := h.β
  τ := h.τ
  hC := h.hC
  hα := h.hα
  hβ := h.hβ
  hτ := h.hτ
  mDpHat0 := h.toRegularityH.canonicalFluxCore h.mDpHat0
  upper := by
    filter_upwards [h.upper] with x hx
    intro m hm
    simpa only [coerciveExtension_of_pos α C x _ hm] using hx m hm
  DpH_upper := by
    filter_upwards [h.DpH_upper, h.toRegularityH.canonicalGradient_eq] with x hx hg
    intro p m hm
    simpa only [hg p m hm] using hx p m hm
  lower := by
    filter_upwards [h.lower] with x hx
    intro p m hm
    simpa only [coerciveExtension_of_pos α C x p hm] using hx p m hm

/-- The coercive representative agrees with every finite boundary limit.
The power data are derived from the positive-mass congestion assumptions. -/
theorem coerciveExtension_finite_agree
    (hpow : CongestionAprioriPowerData (finiteExtension H) (canonicalGradient H)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (coerciveExtension H hpow.α hpow.C x p) (𝓝[>] (0 : ℝ)) (𝓝 L) →
      coerciveExtension H hpow.α hpow.C x p 0 = L := by
  filter_upwards [lower_of_finite_boundary hpow] with x hx p L hL
  have hLH : Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    apply hL.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact coerciveExtension_of_pos hpow.α hpow.C x p ht
  exact coerciveExtension_zero_of_tendsto hpow.α hpow.C hLH
    (hx p L (finiteExtension_tendsto_of_tendsto hLH))

/-- At finite boundary points the canonical general flux vanishes, derived
from the literal paper gradient and convexity assumptions. -/
theorem HypothesisCongestionGrowth.coerciveExtension_flux_zero
    (h : HypothesisCongestionGrowth H DpH J)
    (hmon : HypothesisMonotone H DpH) (α C : ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (coerciveExtension H α C x p) (𝓝[>] (0 : ℝ)) (𝓝 L) →
      canonicalFlux H x p 0 = 0 := by
  filter_upwards [h.flux_zero_at_finite_boundary hmon,
    canonicalFlux_eq h.toRegularityH h.mDpHat0] with x hz he p L hL
  have hLH : Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    apply hL.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact coerciveExtension_of_pos α C x p ht
  rw [he p 0 le_rfl]
  exact hz p L hLH

end StationaryMFG.Hamiltonian.Paper
