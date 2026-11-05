module

public import StationaryMFG.Theorems.Congestion.LimitPassage
public import StationaryMFG.Theorems.Congestion.PaperApriori

@[expose] public section

/-! # Compactness and the limit variational inequality for the corrected theorem -/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Solutions.MFG

variable {d : ℕ}

/-- The weak limit with the full periodic variational inequality. -/
structure CoreWeakSolution
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hcong : CongestionGrowthCore H DpH J) where
  m : (Fin d → ℝ) → ℝ
  u : (Fin d → ℝ) → ℝ
  Du : Fin d → (Fin d → ℝ) → ℝ
  mLp : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m
  uSob : MemSobolevPer (ENNReal.ofReal (gammaBar hcong.α hcong.β)) u
  m_nonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x
  m_periodic : IsPeriodic m
  u_periodic : IsPeriodic u
  Du_periodic : ∀ i, IsPeriodic (Du i)
  Du_weak : ∀ i, HasWeakDerivPer i u (Du i)
  DuLp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar hcong.α hcong.β)) (Du i)
  hVI : ∀ T : CongestionLimitVITestPair (d := d)
    (ENNReal.ofReal (hcong.β + 1))
    (ENNReal.ofReal (betaBar' hcong.β))
    (ENNReal.ofReal (gammaBar hcong.α hcong.β)) hcong.α hcong.β hcong.τ,
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
      T.Dυ T.μ T.υ (fun i x => T.Dυ i x - Du i x) (T.μ - m) (T.υ - u)

/-- The established compactness and pairing estimates apply to the relaxed
core. The density of every test pair is positive, so the flux conversion in
the pairing argument never imposes a boundary value. -/
noncomputable def weakLimit_of_bounded_sequence
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (seq : CongestionRegularizedSequenceDataNN V H DpH J
      (hcong.toCongestionAprioriPowerData hmon.convex_at_zero) hcong.τ)
    (bounds : CongestionAprioriBoundData V H DpH J
      (hcong.toCongestionAprioriPowerData hmon.convex_at_zero) seq.m seq.u seq.Du) :
    CoreWeakSolution V H DpH J hcong := by
  classical
  let h := hcong.toCongestionAprioriPowerData hmon.convex_at_zero
  haveI : Fact (1 ≤ ENNReal.ofReal (h.β + 1)) := fact_one_le_ofReal_betaBar h.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β)) :=
    fact_one_le_ofReal_gammaBar h.hα h.hβ
  let oracle := CongestionPack4BanachRealisationOracle.of_paperHypotheses
    V H DpH J h seq bounds
  let pack := congestionWeakCompactnessUpstreamPack_of_paperHypotheses
    V h seq bounds oracle
  haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
  haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
  let lim := congestionWeakLimit_of_paperHypotheses V h seq pack
  have hε : Tendsto (fun k => pack.εSeq (lim.φ k)) atTop (𝓝 (0 : ℝ)) :=
    eNullSeq_of_oneOverNSucc_strictMono lim.hMono
  have hpair : ∀ T : CongestionLimitVITestPair (d := d)
      pack.βBar (ENNReal.ofReal (betaBar' hcong.β)) pack.γBar
      hcong.α hcong.β hcong.τ,
      Tendsto (fun k => mfgOperatorPair (V := V) (H := H) (DpH := DpH)
        T.Dυ T.μ T.υ (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
        (T.μ - seq.m (pack.εSeq (lim.φ k))) (T.υ - seq.u (pack.εSeq (lim.φ k)))) atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          T.Dυ T.μ T.υ (fun i x => T.Dυ i x - lim.Du i x) (T.μ - lim.m) (T.υ - lim.u))) := by
    intro T
    exact congestionPairConv_of_weakLimit h seq pack hcong rfl rfl rfl rfl
      (fun _ => rfl) lim T T.hDυ_memGamma lim.hDu_memGamma
      (congestion_hg_at_testPair hmon hcong T hV)
  have hVIeps : ∀ T : CongestionLimitVITestPair (d := d)
      pack.βBar (ENNReal.ofReal (betaBar' hcong.β)) pack.γBar
      hcong.α hcong.β hcong.τ, ∀ k : ℕ,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (gammaBar hcong.α hcong.β) (pack.εSeq (lim.φ k)) T.Dυ T.μ T.υ
        (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
        (T.μ - seq.m (pack.εSeq (lim.φ k))) (T.υ - seq.u (pack.εSeq (lim.φ k))) := by
    intro T k
    exact seq.hVIeps T.μ T.υ T.Dυ T.μLp T.υSob T.hDυ_memGamma T.hDυ_weak T.hCone
      _ (pack.εSeq_pos (lim.φ k))
  let limVI := congestionLimitVI_of_paperHypotheses V h seq pack lim bounds hcong hV
    (gammaBar hcong.α hcong.β) rfl hε hpair rfl rfl hVIeps {}
  exact
    { m := lim.m
      u := lim.u
      Du := lim.Du
      mLp := lim.mLp
      uSob := lim.uSob
      m_nonneg := lim.m_nonneg
      m_periodic := lim.hMper
      u_periodic := lim.hUper
      Du_periodic := lim.hDuPer
      Du_weak := lim.hDuWeak
      DuLp := lim.hDu_memGamma
      hVI := limVI.hLimitVI }

end StationaryMFG.Theorems.Congestion.Paper
