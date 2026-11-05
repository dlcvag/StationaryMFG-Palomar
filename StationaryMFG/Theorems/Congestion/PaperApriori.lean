module

public import StationaryMFG.Theorems.Congestion.AprioriBounds
public import StationaryMFG.Theorems.Congestion.PaperWitnessHJB
public import StationaryMFG.Theorems.Congestion.PaperSolutionBoundary

@[expose] public section

/-! # Congestion a priori sequence from the unrestricted core

The native Banach witness is named once. Internal witness conclusions are
assembled without transporting through different exponent bundles.
-/

noncomputable section
namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Periodic StationaryMFG.Congestion
open scoped ENNReal NNReal

variable {d : ℕ}

noncomputable def upstreamPack
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (h_convex_at_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m) :
    CongestionAprioriUpstreamPack (d := d) V H DpH J := by
  classical
  set hPow : CongestionAprioriPowerData (d := d) H DpH :=
    hcong.toCongestionAprioriPowerData h_convex_at_zero
    with hPow_def
  have hβ_eq : hPow.β = hcong.β := rfl
  have hα_eq : hPow.α = hcong.α := rfl
  have hV_meas : AEStronglyMeasurable V
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    hV.aestronglyMeasurable
  have hβp_pos : 0 < betaBar' hcong.β := by
    have hβ := hcong.hβ; unfold betaBar'; positivity
  have hβp_ne_top : (ENNReal.ofReal (betaBar' hcong.β)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hβp_ne_zero : (ENNReal.ofReal (betaBar' hcong.β)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hβp_toReal : (ENNReal.ofReal (betaBar' hcong.β)).toReal
      = betaBar' hcong.β :=
    ENNReal.toReal_ofReal hβp_pos.le
  have hVbetap_int_aux :
      Integrable
        (fun x => ‖V x‖ ^ (ENNReal.ofReal (betaBar' hcong.β)).toReal)
        (volume.restrict (UnitCube d)) :=
    MeasureTheory.MemLp.integrable_norm_rpow
      (hV.toMemLp) hβp_ne_zero hβp_ne_top
  have hcong_norm_abs :
      (fun x => ‖V x‖ ^ (ENNReal.ofReal (betaBar' hcong.β)).toReal)
        = (fun x => |V x| ^ betaBar' hcong.β) := by
    funext x; rw [Real.norm_eq_abs, hβp_toReal]
  have hVbetap_int :
      Integrable (fun x => |V x| ^ betaBar' hcong.β)
        (volume.restrict (UnitCube d)) := by
    rw [← hcong_norm_abs]; exact hVbetap_int_aux
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with Vint_def
  set Vβp : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' hcong.β
                    ∂(volume : Measure (Fin d → ℝ)) with Vβp_def
  have hVint_nn : 0 ≤ Vint := by
    rw [Vint_def]
    refine MeasureTheory.integral_nonneg ?_
    intro x; exact abs_nonneg _
  have hVβp_nn : 0 ≤ Vβp := by
    rw [Vβp_def]
    refine MeasureTheory.integral_nonneg ?_
    intro x; exact Real.rpow_nonneg (abs_nonneg _) _
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β) :=
    (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
  have hγ_top : ENNReal.ofReal (gammaBar hcong.α hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  exact
    { hPowerCong := hPow
      axisMix := inferInstance
      hV := hV
      hV_meas := hV_meas
      Vint_bound := Vint
      Vβp_bound := Vβp
      hVint := le_refl _
      hVint_nn := hVint_nn
      hVβp_nn := hVβp_nn
      hVbetap_int := hVbetap_int
      hVβp := le_refl _
      hγ_one_le := hγ_one_le
      hγ_top := hγ_top }


/-- The concrete Banach witness at the native paper exponents. -/
noncomputable def regularizedData
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε) :
    CongestionRegularizedSolutionData
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal (betaBar' hcong.β))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      V H DpH J hcong.α hcong.β hcong.τ ε
      (LpPer (ENNReal.ofReal (hcong.β + 1)) d ×
        SobolevPerLp 1 (ENNReal.ofReal (gammaBar hcong.α hcong.β)) d) :=
  congestionRegularizedSolutionAtEps_of_paperHypotheses V H DpH J ε hε hcong hV
    Fact.out Fact.out
    (congestionSequenceBuilderPack hmon hcong hV.aestronglyMeasurable hV ε hε)


/-- Extended HJB at the fixed regularized witness, with no boundary premise. -/
theorem regularizedData_Hext_le
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε) :
    let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => w.2.2 i x) (w.1 x) ≤ ((V x - w.2.1 x : ℝ) : WithTop ℝ) := by
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
    ‹Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))›
  let data := regularizedData hmon hcong hV ε hε
  exact HJB_le_of_BanachVI hmon hcong hV.aestronglyMeasurable hV ε data.weakVI.choose
    data.weakVI.choose_spec.2 (coeM_nonneg_atWitness_of_closure data rfl)
    (coeWeakDeriv_atWitness_of_closure data rfl)

/-- At finite boundary arguments the real representative inherits that HJB bound. -/
theorem regularizedData_raw_HJB
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → H x p 0 = L)
    (ε : ℝ) (hε : 0 < ε) :
    let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x ≤ 0 := by
  let data := regularizedData hmon hcong hV ε hε
  have hnn := coeM_nonneg_atWitness_of_closure data rfl
  have hH := regularizedData_Hext_le hmon hcong hV ε hε
  filter_upwards [hH, hnn, hzero, antitone_in_m hmon] with x hx hn hz ha
  have hh := raw_HJB_of_Hext_le (ha _) hn (hz _) hx
  linarith

/-- Assemble the periodic sequence once the three PDE conclusions have been
proved for the native variational witnesses. All premise fields here are
internal proof steps, discharged by the final paper-facing construction. -/
noncomputable def sequenceData_of_witnessProperties
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hHJB : ∀ (ε : ℝ) (hε : 0 < ε),
      let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x ≤ 0)
    (hHJBeq : ∀ (ε : ℝ) (hε : 0 < ε),
      let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < w.1 x →
        w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x = 0)
    (hIdentity : ∀ (ε : ℝ) (hε : 0 < ε),
      let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
      (∫ x in UnitCube d, w.2.1 x) =
        ∫ x in UnitCube d,
          w.1 x * (-H x (fun i => w.2.2 i x) (w.1 x) +
            (DpH x (fun i => w.2.2 i x) (w.1 x)) ⬝ (fun i => w.2.2 i x)) +
          V x * w.1 x + coeEpsTermsFn ε (gammaBar hcong.α hcong.β) w x) :
    CongestionRegularizedSequenceDataNN V H DpH J
      (upstreamPack V hcong hV hmon.convex_at_zero).hPowerCong hcong.τ := by
  let pack3 := upstreamPack V hcong hV hmon.convex_at_zero
  have hpowα_eq : pack3.hPowerCong.α = hcong.α := rfl
  have hpowβ_eq : pack3.hPowerCong.β = hcong.β := rfl
  haveI hfb : Fact (1 ≤ ENNReal.ofReal (pack3.hPowerCong.β + 1)) :=
    fact_one_le_ofReal_betaBar pack3.hPowerCong.hβ
  haveI hfg : Fact (1 ≤ ENNReal.ofReal (gammaBar pack3.hPowerCong.α pack3.hPowerCong.β)) :=
    fact_one_le_ofReal_gammaBar pack3.hPowerCong.hα pack3.hPowerCong.hβ
  let dataAt (ε : ℝ) (hε : 0 < ε) := regularizedData hmon hcong hV ε hε
  let gapAt (ε : ℝ) (hε : 0 < ε) :=
    congestionSequenceBuilderPack_atPowerData_gap (V := V) pack3.hPowerCong ε
  let mNNAt (ε : ℝ) (hε : 0 < ε) := coeM_nonneg_atWitness_of_closure (dataAt ε hε) rfl
  let decompAt (ε : ℝ) (hε : 0 < ε) :=
    BanachBareDecomposition.ofLpProductGap_nonneg (gapAt ε hε)
      (dataAt ε hε).weakVI.choose (mNNAt ε hε)
      (coeWeakDeriv_atWitness_of_closure (dataAt ε hε) rfl)
      (coeMemSob_u_atWitness_of_closure (dataAt ε hε) rfl)
      (hHJB ε hε) (hIdentity ε hε)
      (congestionSequenceBuilderPack_atPowerData_coeEpsNN
        (V := V) pack3.hPowerCong hε (dataAt ε hε).weakVI.choose)
  let repsAt (ε : ℝ) (hε : 0 < ε) :=
    bareRepresentativeNN_of_BanachWeakVI (dataAt ε hε) (decompAt ε hε)
  let hHJBeqAt := hHJBeq

  let hbetaBar_eq :
      (ENNReal.ofReal (pack3.hPowerCong.β + 1) :  ℝ≥0∞)
        = ENNReal.ofReal (pack3.hPowerCong.β + 1) := rfl
  let hgammaBar_eq :
      (ENNReal.ofReal (gammaBar pack3.hPowerCong.α pack3.hPowerCong.β) : ℝ≥0∞)
        = ENNReal.ofReal (gammaBar pack3.hPowerCong.α pack3.hPowerCong.β) := rfl
  let hγBar_pos : 0 < gammaBar pack3.hPowerCong.α pack3.hPowerCong.β :=
    gammaBar_pos pack3.hPowerCong.α pack3.hPowerCong.β
      (lt_trans zero_lt_one pack3.hPowerCong.hα) pack3.hPowerCong.hβ
  let hγBar_ge_alpha_betaBarP :
      pack3.hPowerCong.α * betaBar' pack3.hPowerCong.β
        ≤ gammaBar pack3.hPowerCong.α pack3.hPowerCong.β := by
    rw [gammaBar_eq_alpha_mul_betaBar' pack3.hPowerCong.α pack3.hPowerCong.β
          pack3.hPowerCong.hβ.ne']
  let hbetaBarP_le_gBar :
      betaBar' pack3.hPowerCong.β
        ≤ gammaBar pack3.hPowerCong.α pack3.hPowerCong.β := by
    rw [gammaBar_eq_alpha_mul_betaBar' pack3.hPowerCong.α pack3.hPowerCong.β
          pack3.hPowerCong.hβ.ne']
    have hbp_pos : 0 < betaBar' pack3.hPowerCong.β :=
      lt_trans zero_lt_one (one_lt_betaBar' pack3.hPowerCong.β pack3.hPowerCong.hβ)
    have hα_ge_one : 1 ≤ pack3.hPowerCong.α := le_of_lt pack3.hPowerCong.hα
    calc betaBar' pack3.hPowerCong.β
        = 1 * betaBar' pack3.hPowerCong.β := by ring
      _ ≤ pack3.hPowerCong.α * betaBar' pack3.hPowerCong.β := by
          exact mul_le_mul_of_nonneg_right hα_ge_one hbp_pos.le
  let hV_aesm : MeasureTheory.AEStronglyMeasurable V
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    pack3.hV_meas
  let hV_int : MeasureTheory.Integrable (fun x => |V x|)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    haveI hcube_fin :
        MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
            Set.univ_inter, volume_unitCube]
        exact ENNReal.one_lt_top⟩
    have hbp_pos : 0 < betaBar' pack3.hPowerCong.β :=
      lt_trans zero_lt_one (one_lt_betaBar' pack3.hPowerCong.β pack3.hPowerCong.hβ)
    have hone_le_bp : 1 ≤ ENNReal.ofReal (betaBar' pack3.hPowerCong.β) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact (ENNReal.ofReal_le_ofReal_iff hbp_pos.le).mpr
        (le_of_lt (one_lt_betaBar' pack3.hPowerCong.β pack3.hPowerCong.hβ))
    have hV_memLp : MeasureTheory.MemLp V (ENNReal.ofReal (betaBar' pack3.hPowerCong.β))
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      pack3.hV
    have hV_int' : MeasureTheory.Integrable V
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (hV_memLp.mono_exponent hone_le_bp)
    exact hV_int'.abs
  exact
    { m := fun ε x =>
        if h : 0 < ε then (repsAt ε h).m x else 0
      u := fun ε x =>
        if h : 0 < ε then (repsAt ε h).u x else 0
      Du := fun ε i x =>
        if h : 0 < ε then (repsAt ε h).Du i x else 0
      epsTerms := fun ε x =>
        if h : 0 < ε then (repsAt ε h).epsTerms x else 0
      mε_nonneg := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).mε_nonneg
      hHJB_le := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hHJB_le
      hHJB_eq_pos := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hHJB_eq_pos (hHJBeqAt ε hε)
      hLagr := fun _ _ => pack3.hPowerCong.lagr
      hEpsNN := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hEpsNN
      hVIIdentity := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hVIIdentity
      hu_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hu_int hfg.out
      hRHSabove_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hRHSabove_int pack3.hPowerCong hV_int hbetaBar_eq
      hLB_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hLB_int pack3.hPowerCong.hβ hbetaBar_eq
      hm_lp := fun ε hε => by
        simp only [dif_pos hε]
        exact Periodic.MemLpPer.congr_ae_unitCube
          (repsAt ε hε).hmem_lp_coe_m (repsAt ε hε).hae_m.symm
      hMbeta_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hMbeta_int pack3.hPowerCong.hβ hbetaBar_eq
      hRHSbelow_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hRHSbelow_int pack3.hPowerCong hcong
          hpowα_eq hpowβ_eq hbetaBar_eq
          hγBar_pos hgammaBar_eq hγBar_ge_alpha_betaBarP hV_aesm
          (by
            set z := (dataAt ε hε).weakVI.choose with hz
            have hpm : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (pack3.hPowerCong.β + 1))
                ((gapAt ε hε).project_m z) :=
              Periodic.MemLpPer.congr_ae_unitCube
                (Periodic.MemLp.toMemLpPer
                  (MeasureTheory.Lp.memLp (z.1 : Periodic.LpPer
                    (ENNReal.ofReal (pack3.hPowerCong.β + 1)) d)))
                ((gapAt ε hε).ae_m z).symm
            have hVabs : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' pack3.hPowerCong.β)) (fun x => |V x|) := by
              have hVn : MeasureTheory.MemLp (fun x => ‖V x‖)
                  (ENNReal.ofReal (betaBar' pack3.hPowerCong.β))
                  (MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)) :=
                hV.toMemLp.norm
              exact Periodic.MemLp.toMemLpPer (by simpa [Real.norm_eq_abs] using hVn)
            have hpq : (pack3.hPowerCong.β + 1).HolderConjugate
                (betaBar' pack3.hPowerCong.β) := by
              have hβ_pos : 0 < pack3.hPowerCong.β := pack3.hPowerCong.hβ
              refine (Real.holderConjugate_iff).mpr ⟨by linarith, ?_⟩
              unfold betaBar'
              field_simp
              ring
            exact Periodic.MemLpPer.integrable_mul
              (p := betaBar' pack3.hPowerCong.β) (q := pack3.hPowerCong.β + 1)
              hpq.symm hVabs hpm)
          (by
            exact congestionSequenceBuilderPack_atPowerData_coeEpsTerms_int
              (V := V) pack3.hPowerCong ε (dataAt ε hε).weakVI.choose)
      hu_meas := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hu_meas hfg.out
      hu_per := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hu_per
      hu_loc := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hu_loc hfg.out
      hu_sob := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hu_sob
      hDu_weak := fun ε hε => by
        simp only [dif_pos hε]
        intro i
        have h := (repsAt ε hε).hDu_weak i
        convert h using 1
      hDu_meas := fun ε hε i => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hDu_meas hfg.out i
      hDu_per := fun ε hε i => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hDu_per i
      hDu_loc := fun ε hε i => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hDu_loc hfg.out i
      hDu_lp := fun ε hε i => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hDu_lp i
      hDu_norm_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hDu_norm_int hγBar_pos hgammaBar_eq
      hUbetap_int := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hUbetap_int pack3.hPowerCong.hβ hbetaBarP_le_gBar
          hgammaBar_eq
      hu_lp_γ := fun ε hε => by
        simp only [dif_pos hε]
        exact (repsAt ε hε).hu_lp_γ
      hVIeps := fun μ υ Dυ hμ_mem hυ_sob hDυ_mem hDυ_weak hdom ε hε => by
        simp only [dif_pos hε]
        haveI : Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
          ‹Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))›
        exact congestion_vIEps_at_testPair hmon hcong hμ_mem hυ_sob hDυ_mem hDυ_weak
          hdom hV.aestronglyMeasurable hV rfl rfl
          ((dataAt ε hε).weakVI.choose_spec.2)
          (repsAt ε hε).hae_m (repsAt ε hε).hae_u (repsAt ε hε).hae_Du }

end StationaryMFG.Theorems.Congestion.Paper
