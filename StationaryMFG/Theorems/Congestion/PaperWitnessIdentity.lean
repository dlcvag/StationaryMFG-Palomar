module

public import StationaryMFG.Theorems.Congestion.PaperApriori

@[expose] public section

/-! # The regularized energy identity with only local boundary information

The extended HJB inequality proves that the Hamiltonian is finite at the
solution's vacuum momenta. The zero-flux fact used below is restricted to
those finite boundary points and is derived from the paper hypotheses.
-/

noncomputable section
namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Periodic StationaryMFG.Congestion
open StationaryMFG.Solutions.MFG
open scoped ENNReal NNReal

variable {d : ℕ}

/-- The exact energy identity at the native Banach witness. The only
boundary information used concerns points with a finite right limit. -/
theorem regularizedData_identity
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hfluxzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → J x p 0 = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hHJBeq : let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < w.1 x →
        w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x = 0) :
    let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
    (∫ x in UnitCube d, w.2.1 x) =
      ∫ x in UnitCube d,
        w.1 x * (-H x (fun i => w.2.2 i x) (w.1 x) +
          (DpH x (fun i => w.2.2 i x) (w.1 x)) ⬝ (fun i => w.2.2 i x)) +
        V x * w.1 x + coeEpsTermsFn ε (gammaBar hcong.α hcong.β) w x := by
  classical
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
    ‹Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))›
  let data := regularizedData hmon hcong hV ε hε
  let w := data.weakVI.choose
  obtain ⟨hm, hu, hDu⟩ := coeMemLpPer_witness_bundle_of_closure data
  have hmnn := coeM_nonneg_atWitness_of_closure data rfl
  have hweak := coeWeakDeriv_atWitness_of_closure data rfl
  have hHext := regularizedData_Hext_le hmon hcong hV ε hε
  have huBeta := u_memLp_betaBar' hcong.hα hcong.hβ hu
  have hQ := solution_quotient_memLp hmon hcong hm huBeta hV hDu hmnn hHext
  have hJzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      w.1 x = 0 → J x (fun i => w.2.2 i x) 0 = 0 := by
    filter_upwards [hHext, hfluxzero, antitone_in_m hmon] with x hx hz ha hm0
    change Hext H x (fun i => w.2.2 i x) (w.1 x) ≤ _ at hx
    rw [hm0] at hx
    obtain ⟨L, _, hL⟩ := finiteBoundary_of_Hext_zero_le (ha _) hx
    exact hz _ L hL
  have htransport := congestion_transport_at_u_witness_AEPeriodicRep
    hmon hcong hm hmnn hu hDu hQ hV.aestronglyMeasurable hV
    (w := w) (Aop := data.A) (K := data.K) rfl rfl data.weakVI.choose_spec.2
    rfl rfl (fun _ => rfl) hweak
    (bareCoeFnOfLpPer w.2.1) (fun i => bareCoeFnOfLpPer (w.2.2 i)) hJzero
  have hepsEq :
      (∫ x in UnitCube d, coeEpsTermsFn ε (gammaBar hcong.α hcong.β) w x) =
        ∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => w.2.2 i x) * ((fun i => w.2.2 i x) ⬝ (fun i => w.2.2 i x)) +
          ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (w.2.1 x) *
            (w.2.1 x * w.2.1 x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    unfold coeEpsTermsFn gammaBar
    ring
  rw [← hepsEq] at htransport
  obtain ⟨hu_int, hmu_int, hVm_int⟩ :=
    congestion_VIid_easy_int_certs hcong.hα hcong.hβ hm hu hV
  have hmFlux_int := congestion_VIid_mFlux_int hmon hcong hm hmnn hDu
  have hmH_int := congestion_VIid_mH_int hmon hcong hm hmnn hDu
  have heps_int := congestionRegularizedBuilderInputs_hEpsTerms_int
    (betaBar := ENNReal.ofReal (hcong.β + 1))
    (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
    (V := V) (H := H) (DpH := DpH) ε
    (γBarReal := gammaBar hcong.α hcong.β)
    (one_lt_gammaBar hcong.α hcong.β hcong.hα hcong.hβ).le rfl w
  rw [congestionRegularizedBuilderInputs_gap_project_epsTerms] at heps_int
  have hHJ0 : (∫ x in UnitCube d,
      w.1 x * (w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hmnn, hHJBeq] with x hn he
    rcases hn.eq_or_lt with hn | hn
    · have hz : w.1 x = 0 := hn.symm
      simp only [hz, zero_mul, Pi.zero_apply]
    · exact mul_eq_zero_of_right _ (he hn)
  exact coeVI_identity_from_transport_and_HJ0
    hu_int hmFlux_int hVm_int heps_int hmH_int hmu_int htransport hHJ0

end StationaryMFG.Theorems.Congestion.Paper
