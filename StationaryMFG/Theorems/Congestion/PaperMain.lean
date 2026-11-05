module

public import StationaryMFG.Theorems.Congestion.PaperSequence
public import StationaryMFG.Theorems.Congestion.PaperCoreBridge
public import StationaryMFG.Theorems.Congestion.PaperFinalAssembly

@[expose] public section

/-!
# Theorem 2 with the paper's boundary scope

The Hamiltonian may have an infinite right limit at zero mass. The supplied
flux can have a nonzero value at zero mass. The proof uses a measurable
coercive representative internally, proves finite boundary control only at
solution arguments, and transfers all conclusions back to the supplied data.
-/

namespace StationaryMFG.Theorems.Congestion

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Theorems.Congestion.Paper

variable {d : ℕ}

/-- The paper-faithful congestion existence theorem. Every implementation
boundary fact is derived; no global finite-H or zero-flux hypothesis appears. -/
theorem thm_main_congestion_growth_faithful
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : Hamiltonian.Paper.HypothesisMonotone H DpH)
    (hcong : Hamiltonian.Paper.HypothesisCongestionGrowth H DpH J)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVPer : IsPeriodic V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Solutions.PaperStrong.IsStrongSolution V H J Du m u ∧
      MemLpPer (ENNReal.ofReal (hcong.β + 1)) m ∧
      MemSobolevPer (ENNReal.ofReal (gammaBar hcong.α hcong.β)) u ∧
      (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) ∧
      (∀ i, HasWeakDerivPer i u (Du i)) ∧
      (∀ i, MemLpPer (ENNReal.ofReal (gammaBar hcong.α hcong.β)) (Du i)) := by
  classical
  let hbase := hcong.toCore.toCongestionAprioriPowerData
    hmon.finiteExtension_monotone.convex_at_zero
  let G := coerciveExtension H hbase.α hbase.C
  let hc := hcong.toCoerciveCore hbase.α hbase.C
  let hmc := hmon.coerciveExtension_monotone hbase.α hbase.C
  haveI : Fact (1 ≤ ENNReal.ofReal (hc.β + 1)) := fact_one_le_ofReal_betaBar hc.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal (gammaBar hc.α hc.β)) :=
    fact_one_le_ofReal_gammaBar hc.hα hc.hβ
  have hzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (G x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → G x p 0 = L :=
    coerciveExtension_finite_agree hbase
  have hfluxzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (G x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → canonicalFlux H x p 0 = 0 :=
    hcong.coerciveExtension_flux_zero hmon hbase.α hbase.C
  let pack := upstreamPack V hc hV hmc.convex_at_zero
  let seq := sequenceData hmc hc hV hzero hfluxzero
  have hLower : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      ‖p‖ ^ pack.hPowerCong.α / pack.hPowerCong.C - pack.hPowerCong.C ≤ G x p 0 := by
    exact Eventually.of_forall fun x p => coerciveExtension_lower_zero hbase.α hbase.C x p
  let bounds := congestionAprioriBoundsNN_of_boundaryLower V pack hLower seq
  let w := weakLimit_of_bounded_sequence hmc hc hV seq bounds
  have hle := w.HJB_le hmc hV hVPer
  have heq := HJB_eq_pos_of_abstractPeriodicVI hmc hc
    w.mLp w.u_mem_dual hV w.DuLp w.m_nonneg
    w.m_periodic w.u_periodic hVPer w.Du_periodic
    (fun p m _ => hc.periodic_H p m) w.uSob w.Du_weak hle w.hVI
  have hs := w.strong_of_HJB_eq hmc hV hVPer heq
  have hOriginal : Solutions.PaperStrong.IsStrongSolution V H J w.Du w.m w.u := by
    apply strongSolution_of_positive_agreement w.m_nonneg _
      (canonicalFlux_eq hcong.toRegularityH hcong.mDpHat0) hs
    exact Eventually.of_forall fun x p t ht =>
      coerciveExtension_of_pos hbase.α hbase.C x p ht
  exact ⟨w.m, w.u, w.Du, hOriginal, w.mLp, w.uSob, w.m_nonneg, w.Du_weak, w.DuLp⟩

end StationaryMFG.Theorems.Congestion
