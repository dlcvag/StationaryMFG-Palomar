module

public import StationaryMFG.Theorems.Congestion.PaperExistence
public import StationaryMFG.Theorems.Congestion.PaperAbstractHJB
public import StationaryMFG.Theorems.Congestion.PaperCoreTransport
public import StationaryMFG.Solutions.PaperStrong

@[expose] public section

/-! # The strong equations at the corrected weak limit -/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Solutions.MFG

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {V : (Fin d → ℝ) → ℝ}

/-- Density dual integrability of the value function follows from its
stronger Sobolev exponent. -/
theorem CoreWeakSolution.u_mem_dual {hcong : CongestionGrowthCore H DpH J}
    (w : CoreWeakSolution V H DpH J hcong) :
    MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) w.u := by
  apply w.uSob.1.mono_exponent_finite _ ENNReal.ofReal_ne_top
  apply ENNReal.ofReal_le_ofReal
  unfold betaBar' gammaBar
  rw [div_le_div_iff_of_pos_right hcong.hβ]
  nlinarith [hcong.hα, hcong.hβ]

/-- The actual limit satisfies the extended HJB inequality. -/
theorem CoreWeakSolution.HJB_le {hcong : CongestionGrowthCore H DpH J}
    (w : CoreWeakSolution V H DpH J hcong)
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVPer : IsPeriodic V) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => w.Du i x) (w.m x) ≤ ((V x - w.u x : ℝ) : WithTop ℝ) :=
  HJB_le_of_abstractPeriodicVI hmon hcong w.mLp w.u_mem_dual hV w.DuLp
    w.m_nonneg w.m_periodic w.u_periodic hVPer w.Du_periodic
    (fun p m _ => hcong.periodic_H p m) w.uSob w.Du_weak w.hVI

/-- The actual limit satisfies the transport equation with general J. -/
theorem CoreWeakSolution.transport {hcong : CongestionGrowthCore H DpH J}
    (w : CoreWeakSolution V H DpH J hcong)
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVPer : IsPeriodic V) :
    Solutions.Strong.IsStrongSolution_Transport V J w.Du w.m w.u := by
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.β + 1)) := fact_one_le_ofReal_betaBar hcong.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β)) :=
    fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
    fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ
  exact transport_of_abstractPeriodicVI hmon hcong w.mLp w.u_mem_dual hV w.DuLp
    w.m_nonneg w.m_periodic w.u_periodic w.Du_periodic w.uSob w.Du_weak
    (w.HJB_le hmon hV hVPer) w.hVI

/-- Once the complementary equation on positive density is supplied, the
limit has all strong PDE clauses. -/
theorem CoreWeakSolution.strong_of_HJB_eq {hcong : CongestionGrowthCore H DpH J}
    (w : CoreWeakSolution V H DpH J hcong)
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVPer : IsPeriodic V)
    (heq : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < w.m x →
      w.u x + H x (fun i => w.Du i x) (w.m x) - V x = 0) :
    Solutions.PaperStrong.IsStrongSolution V H J w.Du w.m w.u := by
  refine ⟨⟨w.HJB_le hmon hV hVPer, ?_⟩, w.transport hmon hV hVPer⟩
  filter_upwards [heq] with x hx hm
  rw [Hext_of_pos H x _ hm, WithTop.coe_inj]
  linarith [hx hm]

/-- Positive-mass agreement of H and nonnegative-mass agreement of J
transfer the strong solution from internal representatives to the supplied data. -/
theorem strongSolution_of_positive_agreement
    {G : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {K : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hH : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p t, 0 < t → G x p t = H x p t)
    (hJ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p t, 0 ≤ t → K x p t = J x p t)
    (hs : Solutions.PaperStrong.IsStrongSolution V G K Du m u) :
    Solutions.PaperStrong.IsStrongSolution V H J Du m u := by
  have hHe : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p t,
      Hext G x p t = Hext H x p t := by
    filter_upwards [hH] with x hx p t
    exact Hext_congr_on_pos (hx p) t
  have hJe : (fun x => K x (fun i => Du i x) (m x)) =ᵐ[volume.restrict (UnitCube d)]
      (fun x => J x (fun i => Du i x) (m x)) := by
    filter_upwards [hm, hJ] with x hn hx
    exact hx _ _ hn
  refine ⟨⟨?_, ?_⟩, hs.2.1.congr hJe, ?_⟩
  · filter_upwards [hs.1.1, hHe] with x hx he
    rwa [he] at hx
  · filter_upwards [hs.1.2, hHe] with x hx he hp
    have hh := hx hp
    rwa [he] at hh
  · intro φ
    rw [← hs.2.2 φ]
    apply integral_congr_ae
    filter_upwards [hJe] with x hx
    rw [hx]

end StationaryMFG.Theorems.Congestion.Paper
