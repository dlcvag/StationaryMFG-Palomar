module

public import StationaryMFG.Theorems.Congestion.PaperAbstractTransport
public import StationaryMFG.Theorems.Congestion.PaperSolutionBoundary

@[expose] public section

/-! # Transport at the solution, retaining the supplied boundary flux -/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Solutions.MFG

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The core's general flux has the dual gradient integrability. -/
theorem flux_memLp_gammaBar'_core (h : CongestionGrowthCore H DpH J)
    {m : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (h.β + 1)) m)
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) (Du i)) :
    MemLpPer (ENNReal.ofReal ((h.α * (h.β + 1) / h.β) /
      (h.α * (h.β + 1) / h.β - 1)))
      (fun x => J x (fun i => Du i x) (m x)) := by
  have hp : AEMeasurable (fun x i => Du i x) (volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
  have hmeas := (h.mDpHat0.aemeasurable_J_comp hp
    hm.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hdom := congestion_flux_dominator_memLp_gammaBar'_le
    (K := h.C) h.hα h.hβ h.hτ.1 h.hτ.2 hm hmnn hDu
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hdom.toMemLp hmeas
  filter_upwards [hmnn, h.mDpH_extended_bound] with x hmx hx
  have hb := hx (fun i => Du i x) (m x) hmx
  have hn := (norm_nonneg _).trans hb
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hn] using hb

/-- The corrected HJB bound supplies exactly the weighted-gradient
integrability needed to pass to the transport equation with general J. -/
theorem transport_of_abstractPeriodicVI
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmPer : IsPeriodic m) (huPer : IsPeriodic u)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (huSob : MemSobolevPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDuWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ))
    (habs : ∀ T : CongestionLimitVITestPair (d := d)
      (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      hcong.α hcong.β hcong.τ,
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
        T.Dυ T.μ T.υ (fun i x => T.Dυ i x - Du i x) (T.μ - m) (T.υ - u)) :
    Solutions.Strong.IsStrongSolution_Transport V J Du m u := by
  have hQ := solution_quotient_memLp hmon hcong hm hu hV hDu hmnn hHJB
  have hflux := flux_memLp_gammaBar'_core hcong hm hmnn hDu
  have hγ : 1 < hcong.α * (hcong.β + 1) / hcong.β :=
    one_lt_gammaBar hcong.α hcong.β hcong.hα hcong.hβ
  have hdual : 1 ≤ ENNReal.ofReal ((hcong.α * (hcong.β + 1) / hcong.β) /
      (hcong.α * (hcong.β + 1) / hcong.β - 1)) := by
    apply ENNReal.one_le_ofReal.mpr
    rw [le_div_iff₀ (by linarith)]
    linarith
  refine ⟨?_, ?_⟩
  · exact memLp_one_iff_integrable.mp
      (hflux.toMemLp.mono_exponent hdual)
  · intro φ
    have hu1 := huSob.1.mono_exponent_finite (Fact.out :
      1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) ENNReal.ofReal_ne_top
    have hh := h_transport_iota_of_abstractPeriodicVI hmon hcong hm hmnn huSob.1
      hDu hQ hV hmPer huPer hDuPer huSob hu1 hDuWeak habs φ
    simpa only [zero_mul, add_zero, integral_zero] using hh

end StationaryMFG.Theorems.Congestion.Paper
