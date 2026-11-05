module

public import StationaryMFG.Theorems.SimplePower.StrongIsStrong
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Periodic.SobolevPoincare
public import Mathlib.Analysis.MeanInequalities
public import StationaryMFG.Theorems.SimplePower.Apriori.Part1
import all StationaryMFG.Theorems.SimplePower.Apriori.Part1

@[expose] public section

noncomputable section
namespace StationaryMFG
namespace Theorems
namespace SimplePower
open MeasureTheory Set Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal Topology
variable {d : ℕ}


/-- **AE-periodic sibling of `apriori_aggregate_bound_residue_form_int`.**

Same statement as `apriori_aggregate_bound_residue_form_int` except
for the periodicity / locality hypothesis swap on `u` and `Du i`
(`IsPeriodic` → `Periodic.AEPeriodic`, drop `hu_loc`/`hDu_loc`).
Body identical to the pointwise variant except the inner calls to
the closed-form `_int` apriori theorems are routed to their
`_aePeriodic` siblings. -/
theorem apriori_aggregate_bound_residue_form_int_aePeriodic
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed_int (d := d) h Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  -- Step 1: closed-form m bound via `_int`.
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMpos] with x hxpos
    rw [abs_of_pos hxpos]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  -- Step 2: AE-periodic closed-form Du bound via the new sibling.
  set Cd : ℝ := aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form_int_aePeriodic (h := h) V Du m u epsTerms
      Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  -- Step 3: AE-periodic closed-form Lp bound on u via the new sibling.
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int_aePeriodic (h := h) V Du m u epsTerms
      Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  -- The remainder is identical to `apriori_aggregate_bound_residue_form_int`.
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    exact Real.rpow_le_rpow (abs_nonneg _) h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, ‖(fun j => Du j x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hDu_i_le_Cd : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ Cd := fun i =>
    le_trans (hDu_i_le i) hCd_bound
  have hSum_Du_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
        ∂(volume : Measure (Fin d → ℝ))) ≤ (d : ℝ) * Cd := by
    have hsum_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ ∑ _i : Fin d, Cd :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∫ x in UnitCube d, |Du i x| ^ γ
                  ∂(volume : Measure (Fin d → ℝ)))
        (g := fun _ => Cd)
        (fun i _ => hDu_i_le_Cd i)
    have hconst_sum : ∑ _i : Fin d, Cd = (d : ℝ) * Cd := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← hconst_sum]; exact hsum_le
  have hCd_nn : 0 ≤ Cd := by
    have h_int_nn : (0 : ℝ) ≤ ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    linarith [le_trans h_int_nn hCd_bound]
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq : lpNormPer p (Du i) ^ γ ≤ Cd := by
      rw [hDu_lp_γ i]
      exact hDu_i_le_Cd i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn
    exact le_trans hu_pw h2
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  have hu_lp_eq : lpNormPer p u ^ γ
      = ∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := u) hp_ne_zero hp_top hu_lp_γ
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p u ^ γ
          = (((∫ x, ‖u x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  unfold aprioriUniformConstantClosed_int
  show (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ## HMpos-2 — `_nonneg` siblings along the active `_int_aePeriodic` chain

The six theorems below are HMpos-2 of the 5-step plan to drain
`paperHMposAuth`. Each is the `_nonneg` (i.e. `0 ≤ m` a.e.) sibling of
the strict-positive (`0 < m` a.e.) chain theorem with the same name
(without the `_nonneg` suffix); the three Hat0 riders
`(hHat0, hFin, hAgree)` are added so that boundary `m = 0` cases can
be discharged by the HMpos-0 helpers
`negH_upper_bound_ae_nonneg` / `H_lower_bound_ae_nonneg`.

The Du-integrated chain additionally needs two auxiliary `_nonneg`
siblings of pre-chain pieces (`apriori_Du_pointwise_bound_closed`,
`apriori_Du_integrated_bound_closed`), provided locally below. -/

/-- **HMpos-2 helper.** Nonneg sibling of
`apriori_Du_pointwise_bound_closed`. Routes the unraised bound through
`apriori_Du_alpha_pointwise_nonneg`. -/
private theorem apriori_Du_pointwise_bound_closed_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β ≤
        aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := by
  have hα_pointwise :=
    apriori_Du_alpha_pointwise_nonneg (h := h) hHat0 hFin hAgree V Du m u hHJB hmNonneg
  have hβ_pos : 0 < h.β := h.hβ
  have hβ_ne : h.β ≠ 0 := ne_of_gt hβ_pos
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_nn : (0 : ℝ) ≤ h.α := hα_pos.le
  have hβ' : 1 < betaBar' h.β := one_lt_betaBar' h.β hβ_pos
  have hβ'_pos : 0 < betaBar' h.β := lt_trans zero_lt_one hβ'
  have hβ'_nn : (0 : ℝ) ≤ betaBar' h.β := hβ'_pos.le
  have hidα : h.α * betaBar' h.β = gammaBar h.α h.β :=
    (gammaBar_eq_alpha_mul_betaBar' h.α h.β hβ_ne).symm
  have hidβ : h.β * betaBar' h.β = betaBar h.β := by
    unfold betaBar betaBar'; field_simp
  set K : ℝ := h.C + h.C ^ 2 with hK_def
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hK_nn : 0 ≤ K := by
    have : 0 ≤ h.C ^ 2 := by positivity
    simp [hK_def]; linarith
  have hCeq : aprioriDuPointwiseConst h
                = K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β := by
    unfold aprioriDuPointwiseConst; rfl
  have hKβ'_nn : (0 : ℝ) ≤ K ^ betaBar' h.β :=
    Real.rpow_nonneg hK_nn _
  have h4β'_nn : (0 : ℝ) ≤ (4 : ℝ) ^ betaBar' h.β :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _
  filter_upwards [hα_pointwise, hmNonneg] with x hx hxm
  have hLHS_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hsum_nn :
      (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm _
    have h2 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hraised :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β ≤
        (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β :=
    Real.rpow_le_rpow hLHS_nn hx hβ'_nn
  have hLHS_rewrite :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β =
        ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β := by
    rw [← Real.rpow_mul (norm_nonneg _) h.α (betaBar' h.β)]
    rw [hidα]
  have hRHS_split :
      (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β =
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
    Real.mul_rpow hK_nn hsum_nn
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm _
  have hSpow :
      (m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β ≤
        (4 : ℝ) ^ betaBar' h.β *
          ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β) :=
    four_add_rpow_le_four_rpow_mul hmβ_nn (abs_nonneg _) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1) hβ'_nn
  have hmβ_id : (m x ^ h.β) ^ betaBar' h.β = m x ^ betaBar h.β := by
    rw [← Real.rpow_mul hxm h.β (betaBar' h.β)]; rw [hidβ]
  have h1pow : (1 : ℝ) ^ betaBar' h.β = 1 := Real.one_rpow _
  have hRHS_bound :
      K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
        aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := by
    have hstep1 :
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
          K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β)) :=
      mul_le_mul_of_nonneg_left hSpow hKβ'_nn
    rw [hmβ_id, h1pow] at hstep1
    calc K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β)
        ≤ K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + 1)) := hstep1
      _ = (K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β) *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by ring
      _ = aprioriDuPointwiseConst h *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by rw [hCeq]
  calc ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
      = (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β := hLHS_rewrite.symm
    _ ≤ (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β := hraised
    _ = K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
        hRHS_split
    _ ≤ aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := hRHS_bound

/-- **HMpos-2 helper.** Nonneg sibling of
`apriori_Du_integrated_bound_closed`. Routes the pointwise bound
through `apriori_Du_pointwise_bound_closed_nonneg`. -/
private theorem apriori_Du_integrated_bound_closed_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_int : Integrable (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
                 (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable (fun x => m x ^ betaBar h.β)
                    (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable (fun x => |u x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable (fun x => |V x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuPointwiseConst h *
        ((∫ x in UnitCube d, m x ^ betaBar h.β
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |u x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |V x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + (volume (UnitCube (d := d))).toReal) := by
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hpoint :=
    apriori_Du_pointwise_bound_closed_nonneg (h := h) hHat0 hFin hAgree
      V Du m u hHJB hmNonneg
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have hμfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set g : (Fin d → ℝ) → ℝ :=
    fun x => C₁ * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                    + |V x| ^ betaBar' h.β + 1) with hg_def
  have hone_int : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
  have hsum1 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hMbeta_int.add hUbetap_int
  have hsum2 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hsum1.add hVbetap_int
  have hsum3 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β + 1)
      (volume.restrict (UnitCube d)) := hsum2.add hone_int
  have hg_int : Integrable g (volume.restrict (UnitCube d)) :=
    hsum3.const_mul C₁
  have hint_le :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hDu_int hg_int hpoint
  have h_int_g_eq :
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ))
        = C₁ * (Im + Iu + Iv + vol) := by
    rw [hg_def, integral_const_mul]
    have hinner_eq :
        ∫ x in UnitCube d,
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = Im + Iu + Iv + vol := by
      rw [integral_add hsum2 hone_int]
      rw [integral_add hsum1 hVbetap_int]
      rw [integral_add hMbeta_int hUbetap_int]
      have hone_int_eq :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int_eq]
    rw [hinner_eq]
  calc ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ))
      ≤ ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := hint_le
    _ = C₁ * (Im + Iu + Iv + vol) := h_int_g_eq

/-- **HMpos-2.** Nonneg variant of `apriori_uepsi_below_closed_int`. -/
theorem apriori_uepsi_below_closed_int_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConst_int h Vint_bound Vβp_bound)
        * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConst_int h Vint_bound Vβp_bound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  -- Constants.
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have h2C_pos : 0 < 2 * h.C := by linarith
  -- Young scale (same as the strict variant).
  set lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1)) with hlamdef
  have hbasis_pos : 0 < (h.β + 1) / (2 * h.C) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (h.β + 1) = (h.β + 1) / (2 * h.C) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by
      field_simp
    rw [heq, Real.rpow_one]
  set K_eff : ℝ := h.C + Vβp_bound ^ (h.β / (h.β + 1)) with hK_eff_def
  have hVβp_pow_nn : 0 ≤ Vβp_bound ^ (h.β / (h.β + 1)) :=
    Real.rpow_nonneg hVβp_nn _
  have hK_eff_nn : 0 ≤ K_eff := by
    have : 0 ≤ h.C := hC_pos.le
    linarith
  set K_Y_int : ℝ := (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1))
    with hK_Y_int_def
  have hK_Y_int_nn : 0 ≤ K_Y_int := by
    have h1 : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have h2 : 0 ≤ (K_eff / lam) ^ ((h.β + 1) / h.β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  -- Step A: Pointwise via nonneg multiplied Lagrangian.
  have hlagr_mul :=
    mul_lagrangian_lower_bound_ae_nonneg (β := h.β) (C := h.C) hβ_pos hC_pos h_lagr
  have hpointA :
      (fun x => m x ^ (h.β + 1) / h.C - h.C * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))) := by
    filter_upwards [hlagr_mul, hmNonneg] with x hLag hxm
    exact hLag (fun i => Du i x) (m x) hxm
  have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
  have hLB_int_div :
      Integrable (fun x => m x ^ (h.β + 1) / h.C)
        (volume.restrict (UnitCube d)) := by
    have h := hLB_int.const_mul (1 / h.C)
    refine h.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  have hM_int_const :
      Integrable (fun x => h.C * m x) (volume.restrict (UnitCube d)) :=
    hM_int.const_mul _
  have hLHS_A_int :
      Integrable (fun x => m x ^ (h.β + 1) / h.C - h.C * m x)
        (volume.restrict (UnitCube d)) := hLB_int_div.sub hM_int_const
  have hpointAfull :
      (fun x => m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [hlagr_mul, hmNonneg, hEpsNN] with x hLag hxm hxe
    have hL := hLag (fun i => Du i x) (m x) hxm
    linarith
  have hVm_int_signed : Integrable (fun x => V x * m x)
      (volume.restrict (UnitCube d)) := by
    have hVm_meas : AEStronglyMeasurable (fun x => V x * m x)
        (volume.restrict (UnitCube d)) := hV_meas.mul hm_meas
    have hbound : (fun x => |V x * m x|)
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hmNonneg] with x hxm
      rw [abs_mul, abs_of_nonneg hxm]
    refine Integrable.mono' hVm_int hVm_meas ?_
    filter_upwards [hbound] with x hb using hb
  have hLHS_full_int :
      Integrable (fun x => m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        (volume.restrict (UnitCube d)) :=
    hLHS_A_int.add hVm_int_signed
  have hIntStep :
      ∫ x in UnitCube d,
          (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_full_int hRHS_int hpointAfull
  rw [← h_identity] at hIntStep
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Im : ℝ := ∫ x in UnitCube d, m x ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  have hIm_nn : 0 ≤ Im := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmNonneg] with x hxm
    exact hxm
  set IVm : ℝ := ∫ x in UnitCube d, V x * m x
                  ∂(volume : Measure (Fin d → ℝ)) with hIVm_def
  set IabsVm : ℝ := ∫ x in UnitCube d, |V x| * m x
                      ∂(volume : Measure (Fin d → ℝ)) with hIabsVm_def
  have hLHS_split :
      ∫ x in UnitCube d,
          (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / h.C) * X - h.C * Im + IVm := by
    have h1 : ∫ x in UnitCube d, m x ^ (h.β + 1) / h.C
                ∂(volume : Measure (Fin d → ℝ))
              = (1 / h.C) * X := by
      have hcongr : ∀ x, m x ^ (h.β + 1) / h.C
                          = (1 / h.C) * m x ^ (h.β + 1) := by
        intro x; ring
      simp only [hcongr]
      rw [integral_const_mul]
    have h2 : ∫ x in UnitCube d, h.C * m x
                ∂(volume : Measure (Fin d → ℝ))
              = h.C * Im := by
      rw [integral_const_mul]
    have hadd :
        ∫ x in UnitCube d,
            (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (m x ^ (h.β + 1) / h.C - h.C * m x)
            ∂(volume : Measure (Fin d → ℝ))
          + ∫ x in UnitCube d, V x * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      integral_add hLHS_A_int hVm_int_signed
    have hsub :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) / h.C - h.C * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, m x ^ (h.β + 1) / h.C
              ∂(volume : Measure (Fin d → ℝ))
          - ∫ x in UnitCube d, h.C * m x
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_sub hLB_int_div hM_int_const
    rw [hadd, hsub, h1, h2]
  rw [hLHS_split] at hIntStep
  have hIVm_lb : -IabsVm ≤ IVm := by
    have hae : (fun x => -(V x * m x))
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hmNonneg] with x hxm
      have hVneg : -V x ≤ |V x| := neg_le_abs _
      have := mul_le_mul_of_nonneg_right hVneg hxm
      simpa [neg_mul] using this
    have hIneg :
        ∫ x in UnitCube d, -(V x * m x)
            ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫ x in UnitCube d, |V x| * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hVm_int_signed.neg hVm_int hae
    have hIneg' : -IVm ≤ IabsVm := by
      simpa [hIVm_def, hIabsVm_def, integral_neg] using hIneg
    linarith
  have hHolder :
      IabsVm ≤ Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1)) := by
    have h_holder := holder_Vm_betaBar (d := d) (β := h.β) hβ_pos
        V m hmNonneg hV_meas hm_meas hVβp_int hLB_int
    have hVβp_int_nn :
        0 ≤ ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
              ∂(volume : Measure (Fin d → ℝ)) := by
      refine integral_nonneg_of_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hexp_nn : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    have hMono : (∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
                    ∂(volume : Measure (Fin d → ℝ))) ^ (h.β / (h.β + 1))
                  ≤ Vβp_bound ^ (h.β / (h.β + 1)) :=
      Real.rpow_le_rpow hVβp_int_nn hVβp ((div_pos hβ_pos hβp1_pos).le)
    have hX_pow_nn : 0 ≤ X ^ (1 / (h.β + 1)) := Real.rpow_nonneg hX_nn _
    have hMul := mul_le_mul_of_nonneg_right hMono hX_pow_nn
    exact h_holder.trans hMul
  have hHolder_m : Im ≤ X ^ (1 / (h.β + 1)) := by
    have h1_meas : AEStronglyMeasurable (fun _ : Fin d → ℝ => (1 : ℝ))
        (volume.restrict (UnitCube d)) := aestronglyMeasurable_const
    have h1_int : Integrable
        (fun x : Fin d → ℝ => |(1 : ℝ)| ^ ((h.β + 1) / h.β))
        (volume.restrict (UnitCube d)) := by
      have hcongr : ∀ x : Fin d → ℝ, |(1 : ℝ)| ^ ((h.β + 1) / h.β) = 1 := by
        intro _
        rw [abs_one, Real.one_rpow]
      have hconst : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
      refine hconst.congr ?_
      filter_upwards with x using (hcongr x).symm
    have h_holder := holder_Vm_betaBar (d := d) (β := h.β) hβ_pos
        (fun _ => (1 : ℝ)) m hmNonneg h1_meas hm_meas h1_int hLB_int
    have hLHS_eq :
        ∫ x in UnitCube d, |(1 : ℝ)| * m x
            ∂(volume : Measure (Fin d → ℝ))
          = Im := by
      have hcongr : ∀ x : Fin d → ℝ, |(1 : ℝ)| * m x = m x := by
        intro x; rw [abs_one, one_mul]
      simp only [hcongr, hIm_def]
    have hRHS_first :
        (∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
            ∂(volume : Measure (Fin d → ℝ))) ^ (h.β / (h.β + 1)) = 1 := by
      have hint_eq :
          ∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
              ∂(volume : Measure (Fin d → ℝ))
            = 1 := by
        have : ∫ _x in UnitCube d, (1 : ℝ) ∂(volume : Measure (Fin d → ℝ))
              = 1 := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
            Set.univ_inter, volume_unitCube]
        calc ∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
                ∂(volume : Measure (Fin d → ℝ))
            = ∫ _x in UnitCube d, (1 : ℝ)
                ∂(volume : Measure (Fin d → ℝ)) := by
              refine integral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro x; rw [abs_one, Real.one_rpow]
          _ = 1 := this
      rw [hint_eq, Real.one_rpow]
    rw [hLHS_eq, hRHS_first, one_mul] at h_holder
    exact h_holder
  have hX_pow_nn : 0 ≤ X ^ (1 / (h.β + 1)) := Real.rpow_nonneg hX_nn _
  have hCm_ub : h.C * Im ≤ h.C * X ^ (1 / (h.β + 1)) :=
    mul_le_mul_of_nonneg_left hHolder_m hC_pos.le
  have hVm_lb_X : -(Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1))) ≤ IVm := by
    have := neg_le_neg hHolder
    linarith [hIVm_lb]
  have hCombined :
      -(K_eff * X ^ (1 / (h.β + 1))) ≤ -h.C * Im + IVm := by
    have hsplit : K_eff * X ^ (1 / (h.β + 1))
                    = h.C * X ^ (1 / (h.β + 1))
                      + Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1)) := by
      rw [hK_eff_def]; ring
    have h1 : -h.C * Im ≥ -h.C * X ^ (1 / (h.β + 1)) := by
      have := hCm_ub
      linarith
    linarith [hVm_lb_X, hsplit]
  have hY_X : (X ^ (1 / (h.β + 1))) ^ (h.β + 1) = X := by
    rw [← Real.rpow_mul hX_nn]
    have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  have hY_pt :
      K_eff * X ^ (1 / (h.β + 1))
        ≤ (1 / (2 * h.C)) * X + K_Y_int := by
    have hylam_nn : 0 ≤ lam * X ^ (1 / (h.β + 1)) :=
      mul_nonneg hlam_pos.le hX_pow_nn
    have hKlam_nn : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have hY := young_absorb_lin_into_betaPlusOne hβ_pos
                  (K_eff / lam) hKlam_nn (lam * X ^ (1 / (h.β + 1))) hylam_nn
    have hLHS : (K_eff / lam) * (lam * X ^ (1 / (h.β + 1))) = K_eff * X ^ (1 / (h.β + 1)) := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    have hpow_mul :
        (lam * X ^ (1 / (h.β + 1))) ^ (h.β + 1)
          = lam ^ (h.β + 1) * (X ^ (1 / (h.β + 1))) ^ (h.β + 1) :=
      Real.mul_rpow hlam_pos.le hX_pow_nn
    have hR1 :
        (lam * X ^ (1 / (h.β + 1))) ^ (h.β + 1) / (h.β + 1)
          = (1 / (2 * h.C)) * X := by
      rw [hpow_mul, hlam_pow_p, hY_X]
      have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    have hRY : (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1)) = K_Y_int := by
      rw [hK_Y_int_def]
    rw [hRY] at hY
    exact hY
  have hChain :
      (1 / (2 * h.C)) * X - K_Y_int
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
    have h1 : (1 / h.C) * X - K_eff * X ^ (1 / (h.β + 1))
                ≤ (1 / h.C) * X - h.C * Im + IVm := by
      linarith
    have hinequalities : (1 / h.C) * X - K_eff * X ^ (1 / (h.β + 1))
                ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
      linarith [hIntStep]
    have h_split : (1 / h.C) * X = (1 / (2 * h.C)) * X + (1 / (2 * h.C)) * X := by
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      have hCne : h.C ≠ 0 := ne_of_gt hC_pos
      field_simp; ring
    linarith [hY_pt]
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_unfold : C' = max (2 * h.C) (K_Y_int + 1) := by
    show aprioriUepsiBelowConst_int h Vint_bound Vβp_bound = _
    rfl
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hC'_ge_2C : 2 * h.C ≤ C' := by
    rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : K_Y_int ≤ C' := by
    rw [hC'_unfold]
    have : K_Y_int ≤ K_Y_int + 1 := by linarith
    exact this.trans (le_max_right _ _)
  have h_coeff : (1 / C') ≤ (1 / (2 * h.C)) :=
    one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  have h_lhs_term : (1 / C') * X ≤ (1 / (2 * h.C)) * X :=
    mul_le_mul_of_nonneg_right h_coeff hX_nn
  have h_rhs_const : -C' ≤ -K_Y_int := by linarith
  linarith [h_lhs_term, h_rhs_const, hChain]

/-- **HMpos-2.** Nonneg variant of `apriori_m_bound_closed_int`. -/
theorem apriori_m_bound_closed_int_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosed_int h Vint_bound Vβp_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by
    simp [hvol_def]
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_int_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_nonneg (h := h) hHat0 hFin hAgree
      V Du m u hHJB hmNonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul h.C
      have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                    - h.C * (m x ^ h.β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hcomb : (1 / C') * X - C' ≤ Vint + h.C * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + h.C * (Y + vol) := habove_eq
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (h.β / (h.β + 1)) = δ := by
    rw [hlam_pow_def]
    field_simp
  set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((h.β + 1) / h.β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : h.β / (h.β + 1) * ((h.β + 1) / h.β) = 1 := by
      have hβne : h.β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : h.β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  set R : ℝ := aprioriMBoundResidual_int h Vint_bound Vβp_bound with hR_def
  have hR_unfold : R = (h.C / lam) ^ (h.β + 1) / (h.β + 1) := by
    show aprioriMBoundResidual_int h Vint_bound Vβp_bound = _
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      h.C * mx ^ h.β ≤ δ * mx ^ (h.β + 1) + R := by
    intro mx hmx
    have hY := young_absorb_pow_into_betaPlusOne (β := h.β) hβ_pos
                  h.C hC_pos.le mx hmx lam hlam_pos
    rw [hlam_pow_id] at hY
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  have hY_int :
      Integrable (fun x => h.C * m x ^ h.β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul h.C
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (h.β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => h.C * m x ^ h.β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (h.β + 1) + R) := by
    filter_upwards [hmNonneg] with x hxm
    exact hYoung_pt (m x) hxm
  have hYint_le :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  have hYint_LHS :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ))
        = h.C * Y := by
    rw [integral_const_mul]
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ))
        = δ * X + R * vol := by
    rw [integral_add (hLB_int.const_mul δ) (integrable_const _),
        integral_const_mul]
    have hone_int :
        ∫ _ in UnitCube d, R ∂(volume : Measure (Fin d → ℝ)) = R * vol := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, hvol_def, mul_comm]
    rw [hone_int]
  rw [hYint_LHS, hYint_RHS] at hYint_le
  have hcomb' :
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + h.C * vol := by
    have : h.C * (Y + vol) = h.C * Y + h.C * vol := by ring
    have h1 : Vint + h.C * (Y + vol) ≤ Vint + (δ * X + R * vol) + h.C * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + h.C * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + h.C * vol := by
    linarith [habs, hVint_le]
  have hM_unfold :
      aprioriMBoundClosed_int h Vint_bound Vβp_bound
        = 2 * C' * (C' + Vint_bound + R + h.C) := by
    show aprioriMBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + h.C * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  rw [hM_unfold]
  exact hmul

/-- **HMpos-2.** Nonneg variant of `apriori_uepsi_mean_closed_int`. -/
theorem apriori_uepsi_mean_closed_int_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_int_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_nonneg (h := h) hHat0 hFin hAgree
      V Du m u hHJB hmNonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                  - h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hY_le_X_plus_vol : Y ≤ X + vol := by
    have hpoint :
        (fun x => m x ^ h.β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (h.β + 1) + 1) := by
      filter_upwards [hmNonneg] with x hxm
      exact rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (h.β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ h.β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = X + vol := by
      rw [integral_add hLB_int hone_int']
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hRHS_eq] at hint_le
    exact hint_le
  have hX_le_M : X ≤ M := hM_le
  have hY_le_M_plus_vol : Y ≤ M + vol := by linarith
  have hVint_le : Vint ≤ Vint_bound := hVint
  set Uint : ℝ := ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) with hUint_def
  have hUint_ub : Uint ≤ Vint_bound + h.C * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + h.C * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : h.C * (Y + vol) ≤ h.C * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + h.C * (Y + vol) ≤ Vint_bound + h.C * (M + 2 * vol) := by
      have : h.C * ((M + vol) + vol) = h.C * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  have hCmean_unfold :
      aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound
        = max C' (Vint_bound + h.C * (M + 2)) := by
    show aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  have hUint_ub' : Uint ≤ Vint_bound + h.C * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + h.C * (M + 2) ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hneg : -aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · linarith [hUint_ub', hCmean_ge_ub]

/-- **HMpos-2.** Nonneg variant of `apriori_uepsi_Lp_closed_int_aePeriodic`. -/
theorem apriori_uepsi_Lp_closed_int_aePeriodic_nonneg
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean :=
    aprioriUepsiMeanClosed_int_nn h Vint_bound Vβp_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_int_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  let hu_rep : Periodic.AEPeriodicRep (d := d) u := Classical.choice hu_per
  let hDu_rep : ∀ i, Periodic.AEPeriodicRep (d := d) (Du i) :=
    fun i => Classical.choice (hDu_per i)
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    Periodic.poincareWirtinger_AEPeriodicRep (d := d) (p := p) hγ_one_le hγ_top
      hu_rep hu_sob
      hDu_weak hDu_rep hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **HMpos-2.** Nonneg variant of `apriori_Du_bound_closed_form_int_aePeriodic`. -/
theorem apriori_Du_bound_closed_form_int_aePeriodic_nonneg
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  -- Step 1: integrated Du bound. We need to route through the nonneg sibling
  -- of `apriori_Du_integrated_bound_closed`. That sibling does not exist in
  -- HMpos-1/2 scope, so we recover it by routing through
  -- `apriori_Du_alpha_pointwise_nonneg` and raising to βp; but
  -- `apriori_Du_integrated_bound_closed` itself only consumes `hMpos` via
  -- `apriori_Du_pointwise_bound_closed`, which uses
  -- `apriori_Du_alpha_pointwise`. Since the algebraic skeleton is
  -- unchanged, we reuse `apriori_Du_integrated_bound_closed` modulo the
  -- pointwise lower bound. For HMpos-2 it suffices to route the `_int`-chain
  -- pieces (M-bound and U-bound) through their nonneg siblings; the
  -- pointwise Du-integrated bound from `apriori_Du_integrated_bound_closed`
  -- is already proved for `0 ≤ m` because at `m = 0` the boundary case is
  -- the `H_lower_bound_ae_nonneg` rider, but the strict version is what is
  -- in the codebase. We use it via the `m > 0` filter eventually upgrades.
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hint_bound :=
    apriori_Du_integrated_bound_closed_nonneg (h := h) hHat0 hFin hAgree
      V Du m u hHJB hmNonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  -- Step 2: closed-form m bound via the `_int` chain (nonneg).
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  -- Step 3: AE-periodic closed-form Poincaré bound via the new nonneg sibling.
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int_aePeriodic_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  -- The rest of the proof is identical to the strict-positive aePeriodic sibling.
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn' : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hmNonneg] with x hxm
        exact Real.rpow_nonneg hxm _
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  have hclosed_eq :
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

/-- **HMpos-2 (top-level).** Nonneg variant of
`apriori_aggregate_bound_residue_form_int_aePeriodic`. -/
theorem apriori_aggregate_bound_residue_form_int_aePeriodic_nonneg
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed_int (d := d) h Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hmNonneg] with x hxnn
    rw [abs_of_nonneg hxnn]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  set Cd : ℝ := aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form_int_aePeriodic_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int_aePeriodic_nonneg (h := h) hHat0 hFin hAgree
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    exact Real.rpow_le_rpow (abs_nonneg _) h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, ‖(fun j => Du j x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hDu_i_le_Cd : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ Cd := fun i =>
    le_trans (hDu_i_le i) hCd_bound
  have hSum_Du_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
        ∂(volume : Measure (Fin d → ℝ))) ≤ (d : ℝ) * Cd := by
    have hsum_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ ∑ _i : Fin d, Cd :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∫ x in UnitCube d, |Du i x| ^ γ
                  ∂(volume : Measure (Fin d → ℝ)))
        (g := fun _ => Cd)
        (fun i _ => hDu_i_le_Cd i)
    have hconst_sum : ∑ _i : Fin d, Cd = (d : ℝ) * Cd := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← hconst_sum]; exact hsum_le
  have hCd_nn : 0 ≤ Cd := by
    have h_int_nn : (0 : ℝ) ≤ ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    linarith [le_trans h_int_nn hCd_bound]
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq : lpNormPer p (Du i) ^ γ ≤ Cd := by
      rw [hDu_lp_γ i]
      exact hDu_i_le_Cd i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn
    exact le_trans hu_pw h2
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  have hu_lp_eq : lpNormPer p u ^ γ
      = ∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := u) hp_ne_zero hp_top hu_lp_γ
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p u ^ γ
          = (((∫ x, ‖u x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  unfold aprioriUniformConstantClosed_int
  show (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ## `Hext_finite_at_zero`-free boundary chain (`_riderNN`)

The `_nonneg` chain above extends the `m > 0` Hamiltonian bounds to
`0 ≤ m` by funnelling its boundary `m = 0` work through
`H_lower_bound_ae_nonneg` / `negH_upper_bound_ae_nonneg`, both of which
invoke `H_rc0_of_hHat0` and therefore CONSUME `hFin : Hext_finite_at_zero`
(it `untop`s the `WithTop`-valued right-limit). The directive
`feedback_t2_nonneg_apriori_refactor` forbids `Hext_finite_at_zero` on
the nonneg-track public signature.

This block re-derives the entire chain with the paper-faithful rider
```
hH0 : ∀ᵐ x, ∀ p, ‖p‖^α / C - C ≤ H x p 0
```
in place of `hHat0/hFin/hAgree`. This is exactly the `m = 0` instance of
`eq:assH.lower.simple` (`Source/FGU-monotone_revised.tex` line 464),
which the paper states "hold[s] even when m = 0" (line 508) under
`(onH.*growth)` + `(a:Hat0)`. From this single boundary rider BOTH
boundary directions follow at `m = 0`:
* lower:  `‖p‖^α/C − C(0^β+1) = ‖p‖^α/C − C ≤ H x p 0` (the rider itself);
* upper:  `−H x p 0 ≤ C − ‖p‖^α/C ≤ C = C(0^β+1)` (drop `‖p‖^α/C ≥ 0`).

No `Hext_finite_at_zero`, no power-growth predicate, no division by `m`,
no Brouwer, no oracle. -/

/-- **Boundary lower bound (rider).** Extends `h.lower` to `0 ≤ m` using
the `m = 0` rider `hH0`, WITHOUT `Hext_finite_at_zero`. -/
theorem H_lower_bound_ae_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m →
        ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x p m := by
  have hβ := h.hβ
  filter_upwards [h.lower, hH0] with x hxL hx0
  intro p m hm_nn
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · exact hxL p m hm_pos
  · subst hm_eq
    have h0β_eq : ((0 : ℝ)) ^ h.β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β_eq]
    have := hx0 p
    linarith

/-- **Boundary upper bound on `−H` (rider).** Extends `negH_upper_bound_ae`
to `0 ≤ m` using the `m = 0` rider `hH0`, WITHOUT `Hext_finite_at_zero`. -/
theorem negH_upper_bound_ae_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m → -H x p m ≤ h.C * (m ^ h.β + 1) := by
  have hC := h.hC
  have hβ := h.hβ
  filter_upwards [h.lower, hH0] with x hxL hx0
  intro p m hm_nn
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · have hb := hxL p m hm_pos
    have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hquot_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α / h.C := div_nonneg hp_nn hC.le
    linarith
  · subst hm_eq
    have h0β_eq : ((0 : ℝ)) ^ h.β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β_eq]
    have hL := hx0 p
    have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hquot_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α / h.C := div_nonneg hp_nn hC.le
    linarith

/-! ### D3b — raw-real (`α, β, C`)-keyed boundary leaf lemmas

These mirror `H_lower_bound_ae_riderNN` / `negH_upper_bound_ae_riderNN` but are
keyed by explicit reals `(α β C : ℝ)` (with `0 < β`, `0 < C`) and take the
*content* of the bundle's `lower` field as a plain hypothesis `hLower`, together
with the boundary rider `hH0` keyed to `α/C`. They never read a
`CongestionAprioriPowerData` bundle, so they can be instantiated against a
coercive constant `C0 ≠ h.C` (task `…-D3-a2g-coercive-uniformity-rewire`).

This is the bottom layer of the D3b raw aggregate-engine chain; the remaining raw
helpers are filed as child tasks `…-D3b-(2..)` (see split note). -/

/-- Raw-real form of `H_lower_bound_ae_riderNN`, keyed by `(α β C : ℝ)`.
`hLower` is the content of `CongestionAprioriPowerData.lower`. -/
theorem H_lower_bound_ae_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (α β C : ℝ) (hβ : 0 < β)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C - C ≤ H x p 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m →
        ‖p‖ ^ α / C - C * (m ^ β + 1) ≤ H x p m := by
  filter_upwards [hLower, hH0] with x hxL hx0
  intro p m hm_nn
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · exact hxL p m hm_pos
  · subst hm_eq
    have h0β_eq : ((0 : ℝ)) ^ β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β_eq]
    have := hx0 p
    linarith

/-- Raw-real form of `negH_upper_bound_ae_riderNN`, keyed by `(α β C : ℝ)`.
`hLower` is the content of `CongestionAprioriPowerData.lower`. -/
theorem negH_upper_bound_ae_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (α β C : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C - C ≤ H x p 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m → -H x p m ≤ C * (m ^ β + 1) := by
  filter_upwards [hLower, hH0] with x hxL hx0
  intro p m hm_nn
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · have hb := hxL p m hm_pos
    have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have hquot_nn : (0 : ℝ) ≤ ‖p‖ ^ α / C := div_nonneg hp_nn hC.le
    linarith
  · subst hm_eq
    have h0β_eq : ((0 : ℝ)) ^ β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β_eq]
    have hL := hx0 p
    have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have hquot_nn : (0 : ℝ) ≤ ‖p‖ ^ α / C := div_nonneg hp_nn hC.le
    linarith

/-- **Above-bound (rider).** `apriori_uepsi_above` for `0 ≤ m` via the
boundary rider; no `Hext_finite_at_zero`. -/
theorem apriori_uepsi_above_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu : Integrable u (volume.restrict (UnitCube d)))
    (hRHS : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
        ∂(volume : Measure (Fin d → ℝ)) := by
  have hpointwise :
      u ≤ᵐ[volume.restrict (UnitCube d)]
        fun x => |V x| + h.C * (m x ^ h.β + 1) := by
    filter_upwards [hHJB, hMnn,
        negH_upper_bound_ae_riderNN (d := d) h hH0]
      with x hx hxm hxnegH
    have hH_bnd : -H x (fun i => Du i x) (m x) ≤ h.C * (m x ^ h.β + 1) :=
      hxnegH (fun i => Du i x) (m x) hxm
    have hu_le : u x ≤ V x - H x (fun i => Du i x) (m x) := by linarith
    have hVabs : V x ≤ |V x| := le_abs_self _
    have : u x ≤ V x + h.C * (m x ^ h.β + 1) := by linarith
    linarith
  exact setIntegral_mono_ae_restrict hu hRHS hpointwise

/-- Raw-real form of `apriori_uepsi_above_riderNN`, keyed by `(α β C : ℝ)`.
`hLower` is the content of `CongestionAprioriPowerData.lower`. -/
theorem apriori_uepsi_above_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (α β C : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C - C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu : Integrable u (volume.restrict (UnitCube d)))
    (hRHS : Integrable
              (fun x => |V x| + C * (m x ^ β + 1))
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (|V x| + C * (m x ^ β + 1))
        ∂(volume : Measure (Fin d → ℝ)) := by
  have hpointwise :
      u ≤ᵐ[volume.restrict (UnitCube d)]
        fun x => |V x| + C * (m x ^ β + 1) := by
    filter_upwards [hHJB, hMnn,
        negH_upper_bound_ae_riderNN_raw (d := d) α β C hβ hC hLower hH0]
      with x hx hxm hxnegH
    have hH_bnd : -H x (fun i => Du i x) (m x) ≤ C * (m x ^ β + 1) :=
      hxnegH (fun i => Du i x) (m x) hxm
    have hu_le : u x ≤ V x - H x (fun i => Du i x) (m x) := by linarith
    have hVabs : V x ≤ |V x| := le_abs_self _
    have : u x ≤ V x + C * (m x ^ β + 1) := by linarith
    linarith
  exact setIntegral_mono_ae_restrict hu hRHS hpointwise

/-- **Du α-pointwise (rider).** Copy of `apriori_Du_alpha_pointwise_nonneg`
routing the boundary lower bound through `H_lower_bound_ae_riderNN`. -/
theorem apriori_Du_alpha_pointwise_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ h.α ≤
        (h.C + h.C ^ 2) *
          (m x ^ h.β + |u x| + |V x| + 1) := by
  filter_upwards [hHJB, hMnn,
      H_lower_bound_ae_riderNN (d := d) h hH0]
    with x hx hxm hxlow
  have hLow := hxlow (fun i => Du i x) (m x) hxm
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hC2_nn : (0 : ℝ) ≤ h.C ^ 2 := by positivity
  have hpow_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hVabs : V x ≤ |V x| := le_abs_self _
  have hUabs : -u x ≤ |u x| := neg_le_abs _
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β :=
    Real.rpow_nonneg hxm _
  have hα_aux :
      ‖(fun i => Du i x)‖ ^ h.α ≤
        h.C * H x (fun i => Du i x) (m x) +
          h.C ^ 2 * (m x ^ h.β + 1) := by
    have hCne : h.C ≠ 0 := ne_of_gt hC_pos
    have hmul := mul_le_mul_of_nonneg_left hLow hC_nn
    have heq1 : h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C
                        - h.C * (m x ^ h.β + 1))
               = ‖(fun i => Du i x)‖ ^ h.α
                   - h.C ^ 2 * (m x ^ h.β + 1) := by
      have hcancel : h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C) =
              ‖(fun i => Du i x)‖ ^ h.α := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ _ hCne
      have hsq : h.C * (h.C * (m x ^ h.β + 1)) = h.C ^ 2 * (m x ^ h.β + 1) := by
        ring
      calc h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C
                    - h.C * (m x ^ h.β + 1))
          = h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C)
              - h.C * (h.C * (m x ^ h.β + 1)) := by ring
        _ = ‖(fun i => Du i x)‖ ^ h.α
              - h.C ^ 2 * (m x ^ h.β + 1) := by rw [hcancel, hsq]
    rw [heq1] at hmul
    linarith
  have hHJB' : H x (fun i => Du i x) (m x) ≤ V x - u x := by linarith
  have hCH_le : h.C * H x (fun i => Du i x) (m x) ≤ h.C * (V x - u x) :=
    mul_le_mul_of_nonneg_left hHJB' hC_nn
  have hCVu : h.C * (V x - u x) ≤ h.C * |V x| + h.C * |u x| := by
    have h1 : h.C * V x ≤ h.C * |V x| := mul_le_mul_of_nonneg_left hVabs hC_nn
    have h2 : h.C * (-u x) ≤ h.C * |u x| := mul_le_mul_of_nonneg_left hUabs hC_nn
    have heq : h.C * (V x - u x) = h.C * V x + h.C * (-u x) := by ring
    linarith
  have hstep :
      ‖(fun i => Du i x)‖ ^ h.α ≤
        h.C * |V x| + h.C * |u x| + h.C ^ 2 * (m x ^ h.β) + h.C ^ 2 := by
    have : h.C ^ 2 * (m x ^ h.β + 1) =
              h.C ^ 2 * (m x ^ h.β) + h.C ^ 2 := by ring
    linarith
  have hsum_nn : (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hKge_C : h.C ≤ h.C + h.C ^ 2 := by linarith
  have hKge_C2 : h.C ^ 2 ≤ h.C + h.C ^ 2 := by linarith
  have hK_nn : (0 : ℝ) ≤ h.C + h.C ^ 2 := by linarith
  have h_Vbound : h.C * |V x| ≤ (h.C + h.C ^ 2) * |V x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Ubound : h.C * |u x| ≤ (h.C + h.C ^ 2) * |u x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Mbound : h.C ^ 2 * (m x ^ h.β) ≤ (h.C + h.C ^ 2) * (m x ^ h.β) :=
    mul_le_mul_of_nonneg_right hKge_C2 hmβ_nn
  have h_Cbound : h.C ^ 2 ≤ (h.C + h.C ^ 2) * 1 := by linarith
  have hRHS_eq : (h.C + h.C ^ 2) * (m x ^ h.β + |u x| + |V x| + 1)
                  = (h.C + h.C ^ 2) * (m x ^ h.β)
                    + (h.C + h.C ^ 2) * |u x|
                    + (h.C + h.C ^ 2) * |V x|
                    + (h.C + h.C ^ 2) * 1 := by ring
  linarith

/-- Raw-real form of `apriori_Du_alpha_pointwise_riderNN`, keyed by `(α β C : ℝ)`.
`hLower` is the content of `CongestionAprioriPowerData.lower`. -/
theorem apriori_Du_alpha_pointwise_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (α β C : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C - C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ α ≤
        (C + C ^ 2) *
          (m x ^ β + |u x| + |V x| + 1) := by
  filter_upwards [hHJB, hMnn,
      H_lower_bound_ae_riderNN_raw (d := d) α β C hβ hLower hH0]
    with x hx hxm hxlow
  have hLow := hxlow (fun i => Du i x) (m x) hxm
  have hC_pos : 0 < C := hC
  have hC_nn : (0 : ℝ) ≤ C := hC_pos.le
  have hC2_nn : (0 : ℝ) ≤ C ^ 2 := by positivity
  have hpow_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hVabs : V x ≤ |V x| := le_abs_self _
  have hUabs : -u x ≤ |u x| := neg_le_abs _
  have hmβ_nn : (0 : ℝ) ≤ m x ^ β :=
    Real.rpow_nonneg hxm _
  have hα_aux :
      ‖(fun i => Du i x)‖ ^ α ≤
        C * H x (fun i => Du i x) (m x) +
          C ^ 2 * (m x ^ β + 1) := by
    have hCne : C ≠ 0 := ne_of_gt hC_pos
    have hmul := mul_le_mul_of_nonneg_left hLow hC_nn
    have heq1 : C * (‖(fun i => Du i x)‖ ^ α / C
                        - C * (m x ^ β + 1))
               = ‖(fun i => Du i x)‖ ^ α
                   - C ^ 2 * (m x ^ β + 1) := by
      have hcancel : C * (‖(fun i => Du i x)‖ ^ α / C) =
              ‖(fun i => Du i x)‖ ^ α := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ _ hCne
      have hsq : C * (C * (m x ^ β + 1)) = C ^ 2 * (m x ^ β + 1) := by
        ring
      calc C * (‖(fun i => Du i x)‖ ^ α / C
                    - C * (m x ^ β + 1))
          = C * (‖(fun i => Du i x)‖ ^ α / C)
              - C * (C * (m x ^ β + 1)) := by ring
        _ = ‖(fun i => Du i x)‖ ^ α
              - C ^ 2 * (m x ^ β + 1) := by rw [hcancel, hsq]
    rw [heq1] at hmul
    linarith
  have hHJB' : H x (fun i => Du i x) (m x) ≤ V x - u x := by linarith
  have hCH_le : C * H x (fun i => Du i x) (m x) ≤ C * (V x - u x) :=
    mul_le_mul_of_nonneg_left hHJB' hC_nn
  have hCVu : C * (V x - u x) ≤ C * |V x| + C * |u x| := by
    have h1 : C * V x ≤ C * |V x| := mul_le_mul_of_nonneg_left hVabs hC_nn
    have h2 : C * (-u x) ≤ C * |u x| := mul_le_mul_of_nonneg_left hUabs hC_nn
    have heq : C * (V x - u x) = C * V x + C * (-u x) := by ring
    linarith
  have hstep :
      ‖(fun i => Du i x)‖ ^ α ≤
        C * |V x| + C * |u x| + C ^ 2 * (m x ^ β) + C ^ 2 := by
    have : C ^ 2 * (m x ^ β + 1) =
              C ^ 2 * (m x ^ β) + C ^ 2 := by ring
    linarith
  have hsum_nn : (0 : ℝ) ≤ m x ^ β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hKge_C : C ≤ C + C ^ 2 := by linarith
  have hKge_C2 : C ^ 2 ≤ C + C ^ 2 := by linarith
  have hK_nn : (0 : ℝ) ≤ C + C ^ 2 := by linarith
  have h_Vbound : C * |V x| ≤ (C + C ^ 2) * |V x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Ubound : C * |u x| ≤ (C + C ^ 2) * |u x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Mbound : C ^ 2 * (m x ^ β) ≤ (C + C ^ 2) * (m x ^ β) :=
    mul_le_mul_of_nonneg_right hKge_C2 hmβ_nn
  have h_Cbound : C ^ 2 ≤ (C + C ^ 2) * 1 := by linarith
  have hRHS_eq : (C + C ^ 2) * (m x ^ β + |u x| + |V x| + 1)
                  = (C + C ^ 2) * (m x ^ β)
                    + (C + C ^ 2) * |u x|
                    + (C + C ^ 2) * |V x|
                    + (C + C ^ 2) * 1 := by ring
  linarith

/-! ### D3b2 — raw-real (`α, β, C`)-keyed aggregate-engine MIDDLE + TOP layers

These mirror the bundle-keyed closed-form helpers below but are keyed by explicit
reals `(α β C0 : ℝ)` (with `1 < α`, `0 < β`, `0 < C0`), take the *content* of the
bundle's `lower` field as `hLower`, the `lagr` content via the existing `h_lagr`
parameter, and the boundary rider `hH0` keyed to `α/C0`. They output via the D3
`…Raw` constant defs. Originals are kept intact (additive). -/

/-- Raw-real form of `apriori_Du_pointwise_bound_closed_riderNN`,
keyed by `(α β C0 : ℝ)`. `hLower` carries the `CongestionAprioriPowerData.lower`
content. -/
theorem apriori_Du_pointwise_bound_closed_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ gammaBar α β ≤
        aprioriDuPointwiseConstRaw β C0 *
          (m x ^ betaBar β + |u x| ^ betaBar' β
            + |V x| ^ betaBar' β + 1) := by
  have hα_pointwise :=
    apriori_Du_alpha_pointwise_riderNN_raw (d := d) α β C0 hβ hC0 hLower hH0
      V Du m u hHJB hmNonneg
  have hβ_pos : 0 < β := hβ
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα_nn : (0 : ℝ) ≤ α := hα_pos.le
  have hβ' : 1 < betaBar' β := one_lt_betaBar' β hβ_pos
  have hβ'_pos : 0 < betaBar' β := lt_trans zero_lt_one hβ'
  have hβ'_nn : (0 : ℝ) ≤ betaBar' β := hβ'_pos.le
  have hidα : α * betaBar' β = gammaBar α β :=
    (gammaBar_eq_alpha_mul_betaBar' α β hβ_ne).symm
  have hidβ : β * betaBar' β = betaBar β := by
    unfold betaBar betaBar'; field_simp
  set K : ℝ := C0 + C0 ^ 2 with hK_def
  have hC_pos : 0 < C0 := hC0
  have hC_nn : (0 : ℝ) ≤ C0 := hC_pos.le
  have hK_nn : 0 ≤ K := by
    have : 0 ≤ C0 ^ 2 := by positivity
    simp [hK_def]; linarith
  have hCeq : aprioriDuPointwiseConstRaw β C0
                = K ^ betaBar' β * (4 : ℝ) ^ betaBar' β := by
    unfold aprioriDuPointwiseConstRaw; rfl
  have hKβ'_nn : (0 : ℝ) ≤ K ^ betaBar' β :=
    Real.rpow_nonneg hK_nn _
  have h4β'_nn : (0 : ℝ) ≤ (4 : ℝ) ^ betaBar' β :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _
  filter_upwards [hα_pointwise, hmNonneg] with x hx hxm
  have hLHS_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hsum_nn :
      (0 : ℝ) ≤ m x ^ β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ m x ^ β := Real.rpow_nonneg hxm _
    have h2 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hraised :
      (‖(fun i => Du i x)‖ ^ α) ^ betaBar' β ≤
        (K * (m x ^ β + |u x| + |V x| + 1)) ^ betaBar' β :=
    Real.rpow_le_rpow hLHS_nn hx hβ'_nn
  have hLHS_rewrite :
      (‖(fun i => Du i x)‖ ^ α) ^ betaBar' β =
        ‖(fun i => Du i x)‖ ^ gammaBar α β := by
    rw [← Real.rpow_mul (norm_nonneg _) α (betaBar' β)]
    rw [hidα]
  have hRHS_split :
      (K * (m x ^ β + |u x| + |V x| + 1)) ^ betaBar' β =
        K ^ betaBar' β * ((m x ^ β + |u x| + |V x| + 1) ^ betaBar' β) :=
    Real.mul_rpow hK_nn hsum_nn
  have hmβ_nn : (0 : ℝ) ≤ m x ^ β := Real.rpow_nonneg hxm _
  have hSpow :
      (m x ^ β + |u x| + |V x| + 1) ^ betaBar' β ≤
        (4 : ℝ) ^ betaBar' β *
          ((m x ^ β) ^ betaBar' β + |u x| ^ betaBar' β
            + |V x| ^ betaBar' β + (1 : ℝ) ^ betaBar' β) :=
    four_add_rpow_le_four_rpow_mul hmβ_nn (abs_nonneg _) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1) hβ'_nn
  have hmβ_id : (m x ^ β) ^ betaBar' β = m x ^ betaBar β := by
    rw [← Real.rpow_mul hxm β (betaBar' β)]; rw [hidβ]
  have h1pow : (1 : ℝ) ^ betaBar' β = 1 := Real.one_rpow _
  have hRHS_bound :
      K ^ betaBar' β * ((m x ^ β + |u x| + |V x| + 1) ^ betaBar' β) ≤
        aprioriDuPointwiseConstRaw β C0 *
          (m x ^ betaBar β + |u x| ^ betaBar' β
            + |V x| ^ betaBar' β + 1) := by
    have hstep1 :
        K ^ betaBar' β * ((m x ^ β + |u x| + |V x| + 1) ^ betaBar' β) ≤
          K ^ betaBar' β *
            ((4 : ℝ) ^ betaBar' β *
              ((m x ^ β) ^ betaBar' β + |u x| ^ betaBar' β
                + |V x| ^ betaBar' β + (1 : ℝ) ^ betaBar' β)) :=
      mul_le_mul_of_nonneg_left hSpow hKβ'_nn
    rw [hmβ_id, h1pow] at hstep1
    calc K ^ betaBar' β * ((m x ^ β + |u x| + |V x| + 1) ^ betaBar' β)
        ≤ K ^ betaBar' β *
            ((4 : ℝ) ^ betaBar' β *
              (m x ^ betaBar β + |u x| ^ betaBar' β
                + |V x| ^ betaBar' β + 1)) := hstep1
      _ = (K ^ betaBar' β * (4 : ℝ) ^ betaBar' β) *
            (m x ^ betaBar β + |u x| ^ betaBar' β
              + |V x| ^ betaBar' β + 1) := by ring
      _ = aprioriDuPointwiseConstRaw β C0 *
            (m x ^ betaBar β + |u x| ^ betaBar' β
              + |V x| ^ betaBar' β + 1) := by rw [hCeq]
  calc ‖(fun i => Du i x)‖ ^ gammaBar α β
      = (‖(fun i => Du i x)‖ ^ α) ^ betaBar' β := hLHS_rewrite.symm
    _ ≤ (K * (m x ^ β + |u x| + |V x| + 1)) ^ betaBar' β := hraised
    _ = K ^ betaBar' β * ((m x ^ β + |u x| + |V x| + 1) ^ betaBar' β) :=
        hRHS_split
    _ ≤ aprioriDuPointwiseConstRaw β C0 *
          (m x ^ betaBar β + |u x| ^ betaBar' β
            + |V x| ^ betaBar' β + 1) := hRHS_bound

/-- Non-negativity of `aprioriDuPointwiseConstRaw`. -/
theorem aprioriDuPointwiseConstRaw_nn (β C0 : ℝ) (hC0 : 0 < C0) :
    0 ≤ aprioriDuPointwiseConstRaw β C0 := by
  unfold aprioriDuPointwiseConstRaw
  have hK_nn : (0 : ℝ) ≤ C0 + C0 ^ 2 := by
    have : 0 ≤ C0 ^ 2 := by positivity
    linarith
  exact mul_nonneg
    (Real.rpow_nonneg hK_nn _)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)

/-! ### D3c — non-negativity of the raw-real (`α, β, C`)-keyed aggregate constants

These mirror the bundle-keyed non-negativity lemmas (`aprioriMBoundClosed_nn_of_Vint_nn`,
`aprioriDuBoundClosed_nn`, `aprioriUniformConstantClosed_nn`) but are keyed by explicit
reals `(α β C : ℝ)` with `1 < α`, `0 < β`, `0 < C`, so the coercive uniform-bound
aggregator can supply a non-negative `∃ C`-witness from the `ε`-independent coercive
constant `C0` WITHOUT fabricating a `HypothesisPowerGrowth` bundle. -/

/-- Non-negativity of the raw `M`-residual constant (keyed by `β, C`). -/
theorem aprioriMBoundResidualRaw_nn (β C Vbound : ℝ) (hβ : 0 < β) (hC : 0 < C) :
    0 ≤ aprioriMBoundResidualRaw β C Vbound := by
  unfold aprioriMBoundResidualRaw
  have hβp1_pos : 0 < β + 1 := by linarith
  set C' : ℝ := aprioriUepsiBelowConstRaw β C Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConstRaw_pos β C Vbound hC
  have h2C'_pos : 0 < 2 * C' := by linarith
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (β + 1) * δ / β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]; exact div_pos (mul_pos hβp1_pos hδ_pos) hβ
  set lam : ℝ := lam_pow ^ (β / (β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hCnn : 0 ≤ C / lam := div_nonneg hC.le hlam_pos.le
  have hpow_nn : 0 ≤ (C / lam) ^ (β + 1) := Real.rpow_nonneg hCnn _
  exact div_nonneg hpow_nn hβp1_pos.le

/-- Non-negativity of the raw `M`-bound constant (keyed by `β, C`). -/
theorem aprioriMBoundClosedRaw_nn (β C Vbound Vint_bound : ℝ)
    (hβ : 0 < β) (hC : 0 < C) (hVint_nn : 0 ≤ Vint_bound) :
    0 ≤ aprioriMBoundClosedRaw β C Vbound Vint_bound := by
  unfold aprioriMBoundClosedRaw
  have hC'_pos : 0 < aprioriUepsiBelowConstRaw β C Vbound :=
    aprioriUepsiBelowConstRaw_pos β C Vbound hC
  have h2C'_nn : 0 ≤ 2 * aprioriUepsiBelowConstRaw β C Vbound := by linarith
  have hR_nn : 0 ≤ aprioriMBoundResidualRaw β C Vbound :=
    aprioriMBoundResidualRaw_nn β C Vbound hβ hC
  have hsum_nn :
      0 ≤ aprioriUepsiBelowConstRaw β C Vbound + Vint_bound
            + aprioriMBoundResidualRaw β C Vbound + C := by
    linarith [hC'_pos, hC, hR_nn]
  exact mul_nonneg h2C'_nn hsum_nn

/-- Non-negativity of the raw `Du`-bound constant (keyed by `α, β, C`). -/
theorem aprioriDuBoundClosedRaw_nn (d : ℕ) (α β C Vbound Vint_bound Vβp_bound : ℝ)
    (hβ : 0 < β) (hC : 0 < C) (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriDuBoundClosedRaw d α β C Vbound Vint_bound Vβp_bound := by
  unfold aprioriDuBoundClosedRaw
  set C₁ : ℝ := aprioriDuPointwiseConstRaw β C with hC₁_def
  set M  : ℝ := aprioriMBoundClosedRaw β C Vbound Vint_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosedRaw d β C Vbound Vint_bound with hCu_def
  set βp : ℝ := betaBar' β with hβp_def
  set γ  : ℝ := gammaBar α β with hγ_def
  set A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  set r  : ℝ := γ⁻¹ * βp with hr_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConstRaw_nn β C hC
  have hM_nn : 0 ≤ M := aprioriMBoundClosedRaw_nn β C Vbound Vint_bound hβ hC hVint_nn
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosedRaw_nn (d := d) β C Vbound Vint_bound
  have hβp_pos : 0 < βp := lt_trans zero_lt_one (one_lt_betaBar' β hβ)
  have hCuβp_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2βp_nn : 0 ≤ (2 : ℝ) ^ βp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdβp_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := mul_nonneg hC₁_nn (mul_nonneg (mul_nonneg hCuβp_nn h2βp_nn) hdβp_nn)
  have h2A_nn : 0 ≤ 2 * A := by linarith
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have h1 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCuβp_nn h2βp_nn
    linarith
  have h2B_nn : 0 ≤ 2 * B := by linarith
  have hfirst_nn : 0 ≤ (2 * A) ^ (1 / (1 - r)) := Real.rpow_nonneg h2A_nn _
  linarith

/-- Non-negativity of the raw uniform-a-priori constant (keyed by `α, β, C`). -/
theorem aprioriUniformConstantClosedRaw_nn
    (d : ℕ) (α β C Vbound Vint_bound Vβp_bound : ℝ)
    (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriUniformConstantClosedRaw d α β C Vbound Vint_bound Vβp_bound := by
  unfold aprioriUniformConstantClosedRaw
  set M : ℝ := aprioriMBoundClosedRaw β C Vbound Vint_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosedRaw d β C Vbound Vint_bound with hCu_def
  set Cd : ℝ := aprioriDuBoundClosedRaw d α β C Vbound Vint_bound Vβp_bound with hCd_def
  set γ : ℝ := gammaBar α β with hγ_def
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hM_nn : 0 ≤ M := aprioriMBoundClosedRaw_nn β C Vbound Vint_bound hβ hC hVint_nn
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosedRaw_nn (d := d) β C Vbound Vint_bound
  have hCd_nn : 0 ≤ Cd :=
    aprioriDuBoundClosedRaw_nn d α β C Vbound Vint_bound Vβp_bound hβ hC hVint_nn hVβp_nn
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hUγ_nn : 0 ≤ U ^ γ := Real.rpow_nonneg hU_nn _
  have hdCd_nn : 0 ≤ (d : ℝ) * Cd := mul_nonneg hd_nn hCd_nn
  linarith

/-- Raw-real form of `apriori_Du_integrated_bound_closed_riderNN`,
keyed by `(α β C0 : ℝ)`. Calls the raw pointwise helper. -/
theorem apriori_Du_integrated_bound_closed_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_int : Integrable (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α β)
                 (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable (fun x => m x ^ betaBar β)
                    (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable (fun x => |u x| ^ betaBar' β)
                     (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable (fun x => |V x| ^ betaBar' β)
                     (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar α β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuPointwiseConstRaw β C0 *
        ((∫ x in UnitCube d, m x ^ betaBar β
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |u x| ^ betaBar' β
              ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |V x| ^ betaBar' β
              ∂(volume : Measure (Fin d → ℝ)))
          + (volume (UnitCube (d := d))).toReal) := by
  set C₁ : ℝ := aprioriDuPointwiseConstRaw β C0 with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConstRaw_nn β C0 hC0
  have hpoint :=
    apriori_Du_pointwise_bound_closed_riderNN_raw (d := d) α β C0 hα hβ hC0
      hLower hH0 V Du m u hHJB hmNonneg
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have hμfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set g : (Fin d → ℝ) → ℝ :=
    fun x => C₁ * (m x ^ betaBar β + |u x| ^ betaBar' β
                    + |V x| ^ betaBar' β + 1) with hg_def
  have hone_int : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
  have hsum1 : Integrable
      (fun x => m x ^ betaBar β + |u x| ^ betaBar' β)
      (volume.restrict (UnitCube d)) := hMbeta_int.add hUbetap_int
  have hsum2 : Integrable
      (fun x => m x ^ betaBar β + |u x| ^ betaBar' β
                  + |V x| ^ betaBar' β)
      (volume.restrict (UnitCube d)) := hsum1.add hVbetap_int
  have hsum3 : Integrable
      (fun x => m x ^ betaBar β + |u x| ^ betaBar' β
                  + |V x| ^ betaBar' β + 1)
      (volume.restrict (UnitCube d)) := hsum2.add hone_int
  have hg_int : Integrable g (volume.restrict (UnitCube d)) :=
    hsum3.const_mul C₁
  have hint_le :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar α β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hDu_int hg_int hpoint
  have h_int_g_eq :
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ))
        = C₁ * (Im + Iu + Iv + vol) := by
    rw [hg_def, integral_const_mul]
    have hinner_eq :
        ∫ x in UnitCube d,
          (m x ^ betaBar β + |u x| ^ betaBar' β
            + |V x| ^ betaBar' β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = Im + Iu + Iv + vol := by
      rw [integral_add hsum2 hone_int]
      rw [integral_add hsum1 hVbetap_int]
      rw [integral_add hMbeta_int hUbetap_int]
      have hone_int_eq :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int_eq]
    rw [hinner_eq]
  calc ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar α β
            ∂(volume : Measure (Fin d → ℝ))
      ≤ ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := hint_le
    _ = C₁ * (Im + Iu + Iv + vol) := h_int_g_eq

/-- **Du pointwise closed (rider).** Copy of
`apriori_Du_pointwise_bound_closed_nonneg` via the α-pointwise rider. -/
theorem apriori_Du_pointwise_bound_closed_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β ≤
        aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := by
  have hα_pointwise :=
    apriori_Du_alpha_pointwise_riderNN (h := h) hH0 V Du m u hHJB hmNonneg
  have hβ_pos : 0 < h.β := h.hβ
  have hβ_ne : h.β ≠ 0 := ne_of_gt hβ_pos
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_nn : (0 : ℝ) ≤ h.α := hα_pos.le
  have hβ' : 1 < betaBar' h.β := one_lt_betaBar' h.β hβ_pos
  have hβ'_pos : 0 < betaBar' h.β := lt_trans zero_lt_one hβ'
  have hβ'_nn : (0 : ℝ) ≤ betaBar' h.β := hβ'_pos.le
  have hidα : h.α * betaBar' h.β = gammaBar h.α h.β :=
    (gammaBar_eq_alpha_mul_betaBar' h.α h.β hβ_ne).symm
  have hidβ : h.β * betaBar' h.β = betaBar h.β := by
    unfold betaBar betaBar'; field_simp
  set K : ℝ := h.C + h.C ^ 2 with hK_def
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hK_nn : 0 ≤ K := by
    have : 0 ≤ h.C ^ 2 := by positivity
    simp [hK_def]; linarith
  have hCeq : aprioriDuPointwiseConst h
                = K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β := by
    unfold aprioriDuPointwiseConst; rfl
  have hKβ'_nn : (0 : ℝ) ≤ K ^ betaBar' h.β :=
    Real.rpow_nonneg hK_nn _
  have h4β'_nn : (0 : ℝ) ≤ (4 : ℝ) ^ betaBar' h.β :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _
  filter_upwards [hα_pointwise, hmNonneg] with x hx hxm
  have hLHS_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hsum_nn :
      (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm _
    have h2 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hraised :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β ≤
        (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β :=
    Real.rpow_le_rpow hLHS_nn hx hβ'_nn
  have hLHS_rewrite :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β =
        ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β := by
    rw [← Real.rpow_mul (norm_nonneg _) h.α (betaBar' h.β)]
    rw [hidα]
  have hRHS_split :
      (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β =
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
    Real.mul_rpow hK_nn hsum_nn
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm _
  have hSpow :
      (m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β ≤
        (4 : ℝ) ^ betaBar' h.β *
          ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β) :=
    four_add_rpow_le_four_rpow_mul hmβ_nn (abs_nonneg _) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1) hβ'_nn
  have hmβ_id : (m x ^ h.β) ^ betaBar' h.β = m x ^ betaBar h.β := by
    rw [← Real.rpow_mul hxm h.β (betaBar' h.β)]; rw [hidβ]
  have h1pow : (1 : ℝ) ^ betaBar' h.β = 1 := Real.one_rpow _
  have hRHS_bound :
      K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
        aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := by
    have hstep1 :
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
          K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β)) :=
      mul_le_mul_of_nonneg_left hSpow hKβ'_nn
    rw [hmβ_id, h1pow] at hstep1
    calc K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β)
        ≤ K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + 1)) := hstep1
      _ = (K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β) *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by ring
      _ = aprioriDuPointwiseConst h *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by rw [hCeq]
  calc ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
      = (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β := hLHS_rewrite.symm
    _ ≤ (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β := hraised
    _ = K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
        hRHS_split
    _ ≤ aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := hRHS_bound

/-- **Du integrated closed (rider).** Copy of
`apriori_Du_integrated_bound_closed_nonneg` via the pointwise rider. -/
theorem apriori_Du_integrated_bound_closed_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_int : Integrable (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
                 (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable (fun x => m x ^ betaBar h.β)
                    (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable (fun x => |u x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable (fun x => |V x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuPointwiseConst h *
        ((∫ x in UnitCube d, m x ^ betaBar h.β
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |u x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |V x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + (volume (UnitCube (d := d))).toReal) := by
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hpoint :=
    apriori_Du_pointwise_bound_closed_riderNN (h := h) hH0
      V Du m u hHJB hmNonneg
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have hμfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set g : (Fin d → ℝ) → ℝ :=
    fun x => C₁ * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                    + |V x| ^ betaBar' h.β + 1) with hg_def
  have hone_int : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
  have hsum1 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hMbeta_int.add hUbetap_int
  have hsum2 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hsum1.add hVbetap_int
  have hsum3 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β + 1)
      (volume.restrict (UnitCube d)) := hsum2.add hone_int
  have hg_int : Integrable g (volume.restrict (UnitCube d)) :=
    hsum3.const_mul C₁
  have hint_le :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hDu_int hg_int hpoint
  have h_int_g_eq :
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ))
        = C₁ * (Im + Iu + Iv + vol) := by
    rw [hg_def, integral_const_mul]
    have hinner_eq :
        ∫ x in UnitCube d,
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = Im + Iu + Iv + vol := by
      rw [integral_add hsum2 hone_int]
      rw [integral_add hsum1 hVbetap_int]
      rw [integral_add hMbeta_int hUbetap_int]
      have hone_int_eq :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int_eq]
    rw [hinner_eq]
  calc ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ))
      ≤ ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := hint_le
    _ = C₁ * (Im + Iu + Iv + vol) := h_int_g_eq

/-- **Below-bound `_int` (rider).** Thin copy of
`apriori_uepsi_below_closed_int_nonneg`; the boundary riders are dropped
because that lemma's body never consumes them (the lower direction is
fully m-weighted). No `Hext_finite_at_zero`. -/
theorem apriori_uepsi_below_closed_int_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConst_int h Vint_bound Vβp_bound)
        * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConst_int h Vint_bound Vβp_bound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have h2C_pos : 0 < 2 * h.C := by linarith
  set lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1)) with hlamdef
  have hbasis_pos : 0 < (h.β + 1) / (2 * h.C) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (h.β + 1) = (h.β + 1) / (2 * h.C) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by
      field_simp
    rw [heq, Real.rpow_one]
  set K_eff : ℝ := h.C + Vβp_bound ^ (h.β / (h.β + 1)) with hK_eff_def
  have hVβp_pow_nn : 0 ≤ Vβp_bound ^ (h.β / (h.β + 1)) :=
    Real.rpow_nonneg hVβp_nn _
  have hK_eff_nn : 0 ≤ K_eff := by
    have : 0 ≤ h.C := hC_pos.le
    linarith
  set K_Y_int : ℝ := (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1))
    with hK_Y_int_def
  have hK_Y_int_nn : 0 ≤ K_Y_int := by
    have h1 : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have h2 : 0 ≤ (K_eff / lam) ^ ((h.β + 1) / h.β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  have hlagr_mul :=
    mul_lagrangian_lower_bound_ae_nonneg (β := h.β) (C := h.C) hβ_pos hC_pos h_lagr
  have hpointA :
      (fun x => m x ^ (h.β + 1) / h.C - h.C * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))) := by
    filter_upwards [hlagr_mul, hmNonneg] with x hLag hxm
    exact hLag (fun i => Du i x) (m x) hxm
  have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
  have hLB_int_div :
      Integrable (fun x => m x ^ (h.β + 1) / h.C)
        (volume.restrict (UnitCube d)) := by
    have h := hLB_int.const_mul (1 / h.C)
    refine h.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  have hM_int_const :
      Integrable (fun x => h.C * m x) (volume.restrict (UnitCube d)) :=
    hM_int.const_mul _
  have hLHS_A_int :
      Integrable (fun x => m x ^ (h.β + 1) / h.C - h.C * m x)
        (volume.restrict (UnitCube d)) := hLB_int_div.sub hM_int_const
  have hpointAfull :
      (fun x => m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [hlagr_mul, hmNonneg, hEpsNN] with x hLag hxm hxe
    have hL := hLag (fun i => Du i x) (m x) hxm
    linarith
  have hVm_int_signed : Integrable (fun x => V x * m x)
      (volume.restrict (UnitCube d)) := by
    have hVm_meas : AEStronglyMeasurable (fun x => V x * m x)
        (volume.restrict (UnitCube d)) := hV_meas.mul hm_meas
    have hbound : (fun x => |V x * m x|)
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hmNonneg] with x hxm
      rw [abs_mul, abs_of_nonneg hxm]
    refine Integrable.mono' hVm_int hVm_meas ?_
    filter_upwards [hbound] with x hb using hb
  have hLHS_full_int :
      Integrable (fun x => m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        (volume.restrict (UnitCube d)) :=
    hLHS_A_int.add hVm_int_signed
  have hIntStep :
      ∫ x in UnitCube d,
          (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_full_int hRHS_int hpointAfull
  rw [← h_identity] at hIntStep
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Im : ℝ := ∫ x in UnitCube d, m x ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  have hIm_nn : 0 ≤ Im := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmNonneg] with x hxm
    exact hxm
  set IVm : ℝ := ∫ x in UnitCube d, V x * m x
                  ∂(volume : Measure (Fin d → ℝ)) with hIVm_def
  set IabsVm : ℝ := ∫ x in UnitCube d, |V x| * m x
                      ∂(volume : Measure (Fin d → ℝ)) with hIabsVm_def
  have hLHS_split :
      ∫ x in UnitCube d,
          (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / h.C) * X - h.C * Im + IVm := by
    have h1 : ∫ x in UnitCube d, m x ^ (h.β + 1) / h.C
                ∂(volume : Measure (Fin d → ℝ))
              = (1 / h.C) * X := by
      have hcongr : ∀ x, m x ^ (h.β + 1) / h.C
                          = (1 / h.C) * m x ^ (h.β + 1) := by
        intro x; ring
      simp only [hcongr]
      rw [integral_const_mul]
    have h2 : ∫ x in UnitCube d, h.C * m x
                ∂(volume : Measure (Fin d → ℝ))
              = h.C * Im := by
      rw [integral_const_mul]
    have hadd :
        ∫ x in UnitCube d,
            (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (m x ^ (h.β + 1) / h.C - h.C * m x)
            ∂(volume : Measure (Fin d → ℝ))
          + ∫ x in UnitCube d, V x * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      integral_add hLHS_A_int hVm_int_signed
    have hsub :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) / h.C - h.C * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, m x ^ (h.β + 1) / h.C
              ∂(volume : Measure (Fin d → ℝ))
          - ∫ x in UnitCube d, h.C * m x
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_sub hLB_int_div hM_int_const
    rw [hadd, hsub, h1, h2]
  rw [hLHS_split] at hIntStep
  have hIVm_lb : -IabsVm ≤ IVm := by
    have hae : (fun x => -(V x * m x))
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hmNonneg] with x hxm
      have hVneg : -V x ≤ |V x| := neg_le_abs _
      have := mul_le_mul_of_nonneg_right hVneg hxm
      simpa [neg_mul] using this
    have hIneg :
        ∫ x in UnitCube d, -(V x * m x)
            ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫ x in UnitCube d, |V x| * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hVm_int_signed.neg hVm_int hae
    have hIneg' : -IVm ≤ IabsVm := by
      simpa [hIVm_def, hIabsVm_def, integral_neg] using hIneg
    linarith
  have hHolder :
      IabsVm ≤ Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1)) := by
    have h_holder := holder_Vm_betaBar (d := d) (β := h.β) hβ_pos
        V m hmNonneg hV_meas hm_meas hVβp_int hLB_int
    have hVβp_int_nn :
        0 ≤ ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
              ∂(volume : Measure (Fin d → ℝ)) := by
      refine integral_nonneg_of_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hexp_nn : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    have hMono : (∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
                    ∂(volume : Measure (Fin d → ℝ))) ^ (h.β / (h.β + 1))
                  ≤ Vβp_bound ^ (h.β / (h.β + 1)) :=
      Real.rpow_le_rpow hVβp_int_nn hVβp ((div_pos hβ_pos hβp1_pos).le)
    have hX_pow_nn : 0 ≤ X ^ (1 / (h.β + 1)) := Real.rpow_nonneg hX_nn _
    have hMul := mul_le_mul_of_nonneg_right hMono hX_pow_nn
    exact h_holder.trans hMul
  have hHolder_m : Im ≤ X ^ (1 / (h.β + 1)) := by
    have h1_meas : AEStronglyMeasurable (fun _ : Fin d → ℝ => (1 : ℝ))
        (volume.restrict (UnitCube d)) := aestronglyMeasurable_const
    have h1_int : Integrable
        (fun x : Fin d → ℝ => |(1 : ℝ)| ^ ((h.β + 1) / h.β))
        (volume.restrict (UnitCube d)) := by
      have hcongr : ∀ x : Fin d → ℝ, |(1 : ℝ)| ^ ((h.β + 1) / h.β) = 1 := by
        intro _
        rw [abs_one, Real.one_rpow]
      have hconst : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
      refine hconst.congr ?_
      filter_upwards with x using (hcongr x).symm
    have h_holder := holder_Vm_betaBar (d := d) (β := h.β) hβ_pos
        (fun _ => (1 : ℝ)) m hmNonneg h1_meas hm_meas h1_int hLB_int
    have hLHS_eq :
        ∫ x in UnitCube d, |(1 : ℝ)| * m x
            ∂(volume : Measure (Fin d → ℝ))
          = Im := by
      have hcongr : ∀ x : Fin d → ℝ, |(1 : ℝ)| * m x = m x := by
        intro x; rw [abs_one, one_mul]
      simp only [hcongr, hIm_def]
    have hRHS_first :
        (∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
            ∂(volume : Measure (Fin d → ℝ))) ^ (h.β / (h.β + 1)) = 1 := by
      have hint_eq :
          ∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
              ∂(volume : Measure (Fin d → ℝ))
            = 1 := by
        have : ∫ _x in UnitCube d, (1 : ℝ) ∂(volume : Measure (Fin d → ℝ))
              = 1 := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
            Set.univ_inter, volume_unitCube]
        calc ∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
                ∂(volume : Measure (Fin d → ℝ))
            = ∫ _x in UnitCube d, (1 : ℝ)
                ∂(volume : Measure (Fin d → ℝ)) := by
              refine integral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro x; rw [abs_one, Real.one_rpow]
          _ = 1 := this
      rw [hint_eq, Real.one_rpow]
    rw [hLHS_eq, hRHS_first, one_mul] at h_holder
    exact h_holder
  have hX_pow_nn : 0 ≤ X ^ (1 / (h.β + 1)) := Real.rpow_nonneg hX_nn _
  have hCm_ub : h.C * Im ≤ h.C * X ^ (1 / (h.β + 1)) :=
    mul_le_mul_of_nonneg_left hHolder_m hC_pos.le
  have hVm_lb_X : -(Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1))) ≤ IVm := by
    have := neg_le_neg hHolder
    linarith [hIVm_lb]
  have hCombined :
      -(K_eff * X ^ (1 / (h.β + 1))) ≤ -h.C * Im + IVm := by
    have hsplit : K_eff * X ^ (1 / (h.β + 1))
                    = h.C * X ^ (1 / (h.β + 1))
                      + Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1)) := by
      rw [hK_eff_def]; ring
    have h1 : -h.C * Im ≥ -h.C * X ^ (1 / (h.β + 1)) := by
      have := hCm_ub
      linarith
    linarith [hVm_lb_X, hsplit]
  have hY_X : (X ^ (1 / (h.β + 1))) ^ (h.β + 1) = X := by
    rw [← Real.rpow_mul hX_nn]
    have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  have hY_pt :
      K_eff * X ^ (1 / (h.β + 1))
        ≤ (1 / (2 * h.C)) * X + K_Y_int := by
    have hylam_nn : 0 ≤ lam * X ^ (1 / (h.β + 1)) :=
      mul_nonneg hlam_pos.le hX_pow_nn
    have hKlam_nn : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have hY := young_absorb_lin_into_betaPlusOne hβ_pos
                  (K_eff / lam) hKlam_nn (lam * X ^ (1 / (h.β + 1))) hylam_nn
    have hLHS : (K_eff / lam) * (lam * X ^ (1 / (h.β + 1))) = K_eff * X ^ (1 / (h.β + 1)) := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    have hpow_mul :
        (lam * X ^ (1 / (h.β + 1))) ^ (h.β + 1)
          = lam ^ (h.β + 1) * (X ^ (1 / (h.β + 1))) ^ (h.β + 1) :=
      Real.mul_rpow hlam_pos.le hX_pow_nn
    have hR1 :
        (lam * X ^ (1 / (h.β + 1))) ^ (h.β + 1) / (h.β + 1)
          = (1 / (2 * h.C)) * X := by
      rw [hpow_mul, hlam_pow_p, hY_X]
      have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    have hRY : (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1)) = K_Y_int := by
      rw [hK_Y_int_def]
    rw [hRY] at hY
    exact hY
  have hChain :
      (1 / (2 * h.C)) * X - K_Y_int
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
    have h1 : (1 / h.C) * X - K_eff * X ^ (1 / (h.β + 1))
                ≤ (1 / h.C) * X - h.C * Im + IVm := by
      linarith
    have hinequalities : (1 / h.C) * X - K_eff * X ^ (1 / (h.β + 1))
                ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
      linarith [hIntStep]
    have h_split : (1 / h.C) * X = (1 / (2 * h.C)) * X + (1 / (2 * h.C)) * X := by
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      have hCne : h.C ≠ 0 := ne_of_gt hC_pos
      field_simp; ring
    linarith [hY_pt]
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_unfold : C' = max (2 * h.C) (K_Y_int + 1) := by
    show aprioriUepsiBelowConst_int h Vint_bound Vβp_bound = _
    rfl
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hC'_ge_2C : 2 * h.C ≤ C' := by
    rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : K_Y_int ≤ C' := by
    rw [hC'_unfold]
    have : K_Y_int ≤ K_Y_int + 1 := by linarith
    exact this.trans (le_max_right _ _)
  have h_coeff : (1 / C') ≤ (1 / (2 * h.C)) :=
    one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  have h_lhs_term : (1 / C') * X ≤ (1 / (2 * h.C)) * X :=
    mul_le_mul_of_nonneg_right h_coeff hX_nn
  have h_rhs_const : -C' ≤ -K_Y_int := by linarith
  linarith [h_lhs_term, h_rhs_const, hChain]

/-- **m-bound `_int` (rider).** Copy of `apriori_m_bound_closed_int_nonneg`
via the above/below riders. No `Hext_finite_at_zero`. -/
theorem apriori_m_bound_closed_int_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosed_int h Vint_bound Vβp_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_int_riderNN (h := h)
      V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN (h := h) hH0
      V Du m u hHJB hmNonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul h.C
      have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                    - h.C * (m x ^ h.β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hcomb : (1 / C') * X - C' ≤ Vint + h.C * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + h.C * (Y + vol) := habove_eq
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (h.β / (h.β + 1)) = δ := by
    rw [hlam_pow_def]
    field_simp
  set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((h.β + 1) / h.β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : h.β / (h.β + 1) * ((h.β + 1) / h.β) = 1 := by
      have hβne : h.β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : h.β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  set R : ℝ := aprioriMBoundResidual_int h Vint_bound Vβp_bound with hR_def
  have hR_unfold : R = (h.C / lam) ^ (h.β + 1) / (h.β + 1) := by
    show aprioriMBoundResidual_int h Vint_bound Vβp_bound = _
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      h.C * mx ^ h.β ≤ δ * mx ^ (h.β + 1) + R := by
    intro mx hmx
    have hY := young_absorb_pow_into_betaPlusOne (β := h.β) hβ_pos
                  h.C hC_pos.le mx hmx lam hlam_pos
    rw [hlam_pow_id] at hY
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  have hY_int :
      Integrable (fun x => h.C * m x ^ h.β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul h.C
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (h.β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => h.C * m x ^ h.β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (h.β + 1) + R) := by
    filter_upwards [hmNonneg] with x hxm
    exact hYoung_pt (m x) hxm
  have hYint_le :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  have hYint_LHS :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ))
        = h.C * Y := by
    rw [integral_const_mul]
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ))
        = δ * X + R * vol := by
    rw [integral_add (hLB_int.const_mul δ) (integrable_const _),
        integral_const_mul]
    have hone_int :
        ∫ _ in UnitCube d, R ∂(volume : Measure (Fin d → ℝ)) = R * vol := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, hvol_def, mul_comm]
    rw [hone_int]
  rw [hYint_LHS, hYint_RHS] at hYint_le
  have hcomb' :
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + h.C * vol := by
    have : h.C * (Y + vol) = h.C * Y + h.C * vol := by ring
    have h1 : Vint + h.C * (Y + vol) ≤ Vint + (δ * X + R * vol) + h.C * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + h.C * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + h.C * vol := by
    linarith [habs, hVint_le]
  have hM_unfold :
      aprioriMBoundClosed_int h Vint_bound Vβp_bound
        = 2 * C' * (C' + Vint_bound + R + h.C) := by
    show aprioriMBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + h.C * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  rw [hM_unfold]
  exact hmul

/-- **Mean-bound `_int` (rider).** Copy of
`apriori_uepsi_mean_closed_int_nonneg` via the rider chain. -/
theorem apriori_uepsi_mean_closed_int_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int_riderNN (h := h) hH0
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_int_riderNN (h := h)
      V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN (h := h) hH0
      V Du m u hHJB hmNonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                  - h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hY_le_X_plus_vol : Y ≤ X + vol := by
    have hpoint :
        (fun x => m x ^ h.β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (h.β + 1) + 1) := by
      filter_upwards [hmNonneg] with x hxm
      exact rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (h.β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ h.β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = X + vol := by
      rw [integral_add hLB_int hone_int']
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hRHS_eq] at hint_le
    exact hint_le
  have hX_le_M : X ≤ M := hM_le
  have hY_le_M_plus_vol : Y ≤ M + vol := by linarith
  have hVint_le : Vint ≤ Vint_bound := hVint
  set Uint : ℝ := ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) with hUint_def
  have hUint_ub : Uint ≤ Vint_bound + h.C * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + h.C * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : h.C * (Y + vol) ≤ h.C * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + h.C * (Y + vol) ≤ Vint_bound + h.C * (M + 2 * vol) := by
      have : h.C * ((M + vol) + vol) = h.C * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  have hCmean_unfold :
      aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound
        = max C' (Vint_bound + h.C * (M + 2)) := by
    show aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  have hUint_ub' : Uint ≤ Vint_bound + h.C * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + h.C * (M + 2) ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hneg : -aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · linarith [hUint_ub', hCmean_ge_ub]

/-- **Lp-bound `_int` aePeriodic (rider).** Copy of
`apriori_uepsi_Lp_closed_int_aePeriodic_nonneg` via the mean rider. -/
theorem apriori_uepsi_Lp_closed_int_aePeriodic_riderNN
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean :=
    aprioriUepsiMeanClosed_int_nn h Vint_bound Vβp_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_int_riderNN (h := h) hH0
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  let hu_rep : Periodic.AEPeriodicRep (d := d) u := Classical.choice hu_per
  let hDu_rep : ∀ i, Periodic.AEPeriodicRep (d := d) (Du i) :=
    fun i => Classical.choice (hDu_per i)
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    Periodic.poincareWirtinger_AEPeriodicRep (d := d) (p := p) hγ_one_le hγ_top
      hu_rep hu_sob
      hDu_weak hDu_rep hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **Du-bound `_int` aePeriodic (rider).** Copy of
`apriori_Du_bound_closed_form_int_aePeriodic_nonneg` via the rider chain. -/
theorem apriori_Du_bound_closed_form_int_aePeriodic_riderNN
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hint_bound :=
    apriori_Du_integrated_bound_closed_riderNN (h := h) hH0
      V Du m u hHJB hmNonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int_riderNN (h := h) hH0
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int_aePeriodic_riderNN (h := h) hH0
      V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hmNonneg hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn' : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hmNonneg] with x hxm
        exact Real.rpow_nonneg hxm _
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  have hclosed_eq :
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

/-! ## Pointwise nonneg (`riderNN`) m-bound leg — A2f nonneg refactor

The closed-form pointwise m-bound `apriori_m_bound_closed` carries a
strict `hMpos : 0 < m`. Per the project HARD BAN, `0 < m_ε` is FALSE for
the regularized witness and must NOT be invented. This block reworks the
m-bound to hold from `0 ≤ m` (a.e.), mirroring the `_int`-shaped
`Hext_finite_at_zero`-free `_riderNN` chain (further below) but in the
pointwise / `Vbound` / `aprioriUniformConstantClosed` shape that A2f
consumes.

The boundary `m = 0` content of the strict m-bound enters ONLY through the
HJB-upper leg (`apriori_uepsi_above`). We route that leg through the
paper-faithful rider
```
hH0 : ∀ᵐ x, ∀ p, ‖p‖^α/C − C ≤ H x p 0
```
(the `m = 0` instance of `eq:assH.lower.simple`,
`Source/FGU-monotone_revised.tex` line 464, stated to "hold even when
m = 0" at line 508) via `apriori_uepsi_above_riderNN`. The lower leg is
fully `m`-weighted, so its nonneg variant
`apriori_uepsi_below_closed_nonneg` needs only `mul_lagrangian_lower_bound_ae_nonneg`
(no boundary rider). No `Hext_finite_at_zero`, no division by `m`, no
`0 < m`. -/

/-- **Nonneg variant of `apriori_uepsi_below_closed`.** Identical
conclusion and witness `aprioriUepsiBelowConst h Vbound`, but with
`hMpos : 0 < m` relaxed to `hMnonneg : 0 ≤ m`. The lower direction is
fully `m`-weighted, so the only change versus the strict proof is routing
the pointwise Lagrangian step through `mul_lagrangian_lower_bound_ae_nonneg`
(which collapses at `m = 0` algebraically, no Hat0 rider). -/
theorem apriori_uepsi_below_closed_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConst h Vbound)
        * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConst h Vbound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have h2C_pos : 0 < 2 * h.C := by linarith
  set Vp : ℝ := h.C + max Vbound 0 with hVpdef
  have hVp_nn : 0 ≤ Vp := by
    have h1 : (0 : ℝ) ≤ max Vbound 0 := le_max_right _ _
    linarith [hC_pos.le]
  set lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1)) with hlamdef
  have hbasis_pos : 0 < (h.β + 1) / (2 * h.C) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (h.β + 1) = (h.β + 1) / (2 * h.C) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  set K_Y : ℝ := (Vp / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1)) with hK_Ydef
  have hK_Y_nn : 0 ≤ K_Y := by
    have h1 : 0 ≤ Vp / lam := div_nonneg hVp_nn hlam_pos.le
    have h2 : 0 ≤ (Vp / lam) ^ ((h.β + 1) / h.β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      Vp * mx ≤ (1 / (2 * h.C)) * mx ^ (h.β + 1) + K_Y := by
    intro mx hmx
    have hlammx_nn : 0 ≤ lam * mx := mul_nonneg hlam_pos.le hmx
    have hVplam_nn : 0 ≤ Vp / lam := div_nonneg hVp_nn hlam_pos.le
    have hY := young_absorb_lin_into_betaPlusOne hβ_pos (Vp / lam) hVplam_nn (lam * mx) hlammx_nn
    have hLHS : (Vp / lam) * (lam * mx) = Vp * mx := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    have hpow_mul :
        (lam * mx) ^ (h.β + 1) = lam ^ (h.β + 1) * mx ^ (h.β + 1) :=
      Real.mul_rpow hlam_pos.le hmx
    have hR1 :
        (lam * mx) ^ (h.β + 1) / (h.β + 1)
          = (1 / (2 * h.C)) * mx ^ (h.β + 1) := by
      rw [hpow_mul, hlam_pow_p]
      have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    exact hY
  have hpoint :
      (fun x => (1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [mul_lagrangian_lower_bound_ae_nonneg (β := h.β) (C := h.C)
          hβ_pos hC_pos h_lagr,
        hMnonneg, hVbnd, hEpsNN] with x hLag hxm hxV hxE
    have hxm_nn : 0 ≤ m x := hxm
    have hL : m x ^ (h.β + 1) / h.C - h.C * m x
                ≤ m x * (-H x (fun i => Du i x) (m x)
                          + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)) :=
      hLag (fun i => Du i x) (m x) hxm_nn
    have habsmle : |V x| ≤ Vbound := hxV
    have hVbound_le_max : Vbound ≤ max Vbound 0 := le_max_left _ _
    have habs_le_pos : |V x| ≤ max Vbound 0 := habsmle.trans hVbound_le_max
    have hneg_le : -V x ≤ |V x| := neg_le_abs _
    have hneg_max : -V x ≤ max Vbound 0 := hneg_le.trans habs_le_pos
    have hmaxneg : -max Vbound 0 ≤ V x := by linarith
    have hVm_lb : -max Vbound 0 * m x ≤ V x * m x :=
      mul_le_mul_of_nonneg_right hmaxneg hxm_nn
    have h12 :
        (1 / h.C) * m x ^ (h.β + 1) - Vp * m x
          ≤ m x * (-H x (fun i => Du i x) (m x)
                      + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x := by
      have hLrw : m x ^ (h.β + 1) / h.C - h.C * m x
                    = (1 / h.C) * m x ^ (h.β + 1) - h.C * m x := by ring
      rw [hLrw] at hL
      have : Vp * m x = h.C * m x + max Vbound 0 * m x := by
        rw [hVpdef]; ring
      linarith [hL, hVm_lb]
    have hY := hYoung_pt (m x) hxm_nn
    have hY' : (1 / h.C) * m x ^ (h.β + 1) - Vp * m x
                  ≥ (1 / (2 * h.C)) * m x ^ (h.β + 1) - K_Y := by
      have h_aux : (1 / h.C) - (1 / (2 * h.C)) = (1 / (2 * h.C)) := by
        field_simp; ring
      have hrpow_nn : 0 ≤ m x ^ (h.β + 1) := Real.rpow_nonneg hxm_nn _
      have hcoeff_pos : 0 ≤ (1 / (2 * h.C)) := by positivity
      have hsplit : (1 / h.C) * m x ^ (h.β + 1)
                      = (1 / (2 * h.C)) * m x ^ (h.β + 1)
                        + (1 / (2 * h.C)) * m x ^ (h.β + 1) := by
        have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
        have hCne : h.C ≠ 0 := ne_of_gt hC_pos
        field_simp; ring
      linarith [hY, hsplit]
    have hgoal :
        (1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y)
          ≤ m x * (-H x (fun i => Du i x) (m x)
                      + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x := by
      have h2C_nn : 0 ≤ 2 * h.C := h2C_pos.le
      linarith [hY', h12, hxE]
    exact hgoal
  have hLHS_int :
      Integrable (fun x => (1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        (volume.restrict (UnitCube d)) := by
    have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp
    have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
    have hconst : Integrable (fun _ : Fin d → ℝ => (2 * h.C + K_Y))
                    (volume.restrict (UnitCube d)) := integrable_const _
    have hpow : Integrable (fun x => (1 / (2 * h.C)) * m x ^ (h.β + 1))
                  (volume.restrict (UnitCube d)) :=
      hLB_int.const_mul (1 / (2 * h.C))
    exact hpow.sub hconst
  have hint_le :
      ∫ x in UnitCube d,
          ((1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_int hRHS_int hpoint
  rw [← h_identity] at hint_le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have hcube_finite_inst : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  have hLHS_eq :
      ∫ x in UnitCube d,
          ((1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / (2 * h.C))
          * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
        - (2 * h.C + K_Y) * (volume (UnitCube d)).toReal := by
    have hsub :
        ∫ x in UnitCube d,
            ((1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
          ∂(volume : Measure (Fin d → ℝ))
        = (∫ x in UnitCube d, (1 / (2 * h.C)) * m x ^ (h.β + 1)
            ∂(volume : Measure (Fin d → ℝ)))
          - (∫ x in UnitCube d, (2 * h.C + K_Y)
              ∂(volume : Measure (Fin d → ℝ))) := by
      rw [integral_sub (hLB_int.const_mul (1 / (2 * h.C))) (integrable_const _)]
    rw [hsub]
    congr 1
    · rw [integral_const_mul]
    · rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, mul_comm]
  rw [hLHS_eq] at hint_le
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def, volume_unitCube]
  set C' : ℝ := aprioriUepsiBelowConst (d := d) h Vbound with hC'def
  have hC'_unfold :
      C' = max (2 * h.C) ((2 * h.C + K_Y) + 1) := by
    show aprioriUepsiBelowConst (d := d) h Vbound = _
    rfl
  have hC'_pos : 0 < C' := by
    rw [hC'_unfold]
    have h1 : 0 ≤ 2 * h.C + K_Y := by linarith [h2C_pos.le, hK_Y_nn]
    have h2 : (0 : ℝ) < (2 * h.C + K_Y) + 1 := by linarith
    exact lt_of_lt_of_le h2 (le_max_right _ _)
  have hC'_ge_2C : 2 * h.C ≤ C' := by
    rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : (2 * h.C + K_Y) * vol ≤ C' := by
    rw [hC'_unfold, hvol_eq_one, mul_one]
    have : (2 * h.C + K_Y) ≤ (2 * h.C + K_Y) + 1 := by linarith
    exact this.trans (le_max_right _ _)
  have hint_nn : 0 ≤ ∫ x in UnitCube d, m x ^ (h.β + 1)
                        ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  have h_coeff : (1 / C') ≤ (1 / (2 * h.C)) := by
    apply one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  have h_lhs_term :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ)))
        ≤ (1 / (2 * h.C)) * (∫ x in UnitCube d, m x ^ (h.β + 1)
                              ∂(volume : Measure (Fin d → ℝ))) :=
    mul_le_mul_of_nonneg_right h_coeff hint_nn
  have h_rhs_const : -C' ≤ -((2 * h.C + K_Y) * vol) := by linarith
  linarith [h_lhs_term, h_rhs_const, hint_le]

/-- **Pointwise nonneg (`riderNN`) closed-form m-bound.** Identical
conclusion and witness `aprioriMBoundClosed h Vbound Vint_bound` as the
strict `apriori_m_bound_closed`, but with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m`. The boundary `m = 0` content enters only through the
HJB-upper leg, routed through `apriori_uepsi_above_riderNN` with the
paper rider `hH0`; the lower leg uses `apriori_uepsi_below_closed_nonneg`.
No `Hext_finite_at_zero`, no `0 < m`. -/
theorem apriori_m_bound_closed_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosed h Vbound Vint_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set C' : ℝ := aprioriUepsiBelowConst h Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_pos h Vbound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_nonneg (h := h) V Du m u epsTerms Vbound
      h_lagr hMnonneg hVbnd hEpsNN h_identity hLB_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN (h := h.toCongestionAprioriPowerData) hH0
      V Du m u hHJB hMnonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul h.C
      have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                    - h.C * (m x ^ h.β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hcomb : (1 / C') * X - C' ≤ Vint + h.C * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + h.C * (Y + vol) := habove_eq
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (h.β / (h.β + 1)) = δ := by
    rw [hlam_pow_def]; field_simp
  set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((h.β + 1) / h.β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : h.β / (h.β + 1) * ((h.β + 1) / h.β) = 1 := by
      have hβne : h.β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : h.β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  set R : ℝ := aprioriMBoundResidual h Vbound with hR_def
  have hR_unfold : R = (h.C / lam) ^ (h.β + 1) / (h.β + 1) := by
    show aprioriMBoundResidual h Vbound = _
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      h.C * mx ^ h.β ≤ δ * mx ^ (h.β + 1) + R := by
    intro mx hmx
    have hY := young_absorb_pow_into_betaPlusOne (β := h.β) hβ_pos
                  h.C hC_pos.le mx hmx lam hlam_pos
    rw [hlam_pow_id] at hY
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  have hY_int :
      Integrable (fun x => h.C * m x ^ h.β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul h.C
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (h.β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => h.C * m x ^ h.β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (h.β + 1) + R) := by
    filter_upwards [hMnonneg] with x hxm
    exact hYoung_pt (m x) hxm
  have hYint_le :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  have hYint_LHS :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ))
        = h.C * Y := by
    rw [integral_const_mul]
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ))
        = δ * X + R * vol := by
    rw [integral_add (hLB_int.const_mul δ) (integrable_const _),
        integral_const_mul]
    have hone_int :
        ∫ _ in UnitCube d, R ∂(volume : Measure (Fin d → ℝ)) = R * vol := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, hvol_def, mul_comm]
    rw [hone_int]
  rw [hYint_LHS, hYint_RHS] at hYint_le
  have hcomb' :
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + h.C * vol := by
    have : h.C * (Y + vol) = h.C * Y + h.C * vol := by ring
    have h1 : Vint + h.C * (Y + vol) ≤ Vint + (δ * X + R * vol) + h.C * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + h.C * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + h.C * vol := by
    linarith [habs, hVint_le]
  have hM_unfold :
      aprioriMBoundClosed h Vbound Vint_bound
        = 2 * C' * (C' + Vint_bound + R + h.C) := by
    show aprioriMBoundClosed h Vbound Vint_bound = _
    rfl
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + h.C * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  rw [hM_unfold]
  exact hmul

/-- **Nonneg (`riderNN`) closed-form mean bound on `∫ u`.** Mirror of
`apriori_uepsi_mean_closed` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0`. The m-bound leg uses `apriori_m_bound_closed_riderNN`,
the lower leg `apriori_uepsi_below_closed_nonneg`, the upper leg
`apriori_uepsi_above_riderNN`; the three nonneg sites use `hMnonneg`
directly. No `Hext_finite_at_zero`, no `0 < m`. -/
theorem apriori_uepsi_mean_closed_riderNN
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  set C' : ℝ := aprioriUepsiBelowConst h Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_pos h Vbound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_nonneg (h := h) V Du m u epsTerms Vbound
      h_lagr hMnonneg hVbnd hEpsNN h_identity hLB_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN (h := h.toCongestionAprioriPowerData) hH0
      V Du m u hHJB hMnonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                  - h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hY_le_X_plus_vol : Y ≤ X + vol := by
    have hpoint :
        (fun x => m x ^ h.β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (h.β + 1) + 1) := by
      filter_upwards [hMnonneg] with x hxm
      exact rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (h.β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ h.β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = X + vol := by
      rw [integral_add hLB_int hone_int']
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hRHS_eq] at hint_le
    exact hint_le
  have hX_le_M : X ≤ M := hM_le
  have hY_le_M_plus_vol : Y ≤ M + vol := by linarith
  have hVint_le : Vint ≤ Vint_bound := hVint
  set Uint : ℝ := ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) with hUint_def
  have hUint_ub : Uint ≤ Vint_bound + h.C * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + h.C * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : h.C * (Y + vol) ≤ h.C * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + h.C * (Y + vol) ≤ Vint_bound + h.C * (M + 2 * vol) := by
      have : h.C * ((M + vol) + vol) = h.C * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  have hCmean_unfold :
      aprioriUepsiMeanClosed h Vbound Vint_bound
        = max C' (Vint_bound + h.C * (M + 2)) := by
    show aprioriUepsiMeanClosed h Vbound Vint_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  have hUint_ub' : Uint ≤ Vint_bound + h.C * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + h.C * (M + 2) ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hneg : -aprioriUepsiMeanClosed h Vbound Vint_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · linarith [hUint_ub', hCmean_ge_ub]

/-- **Nonneg (`riderNN`) closed-form Lᵖ bound on `u`.** Mirror of
`apriori_uepsi_Lp_closed` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0` (via `apriori_uepsi_mean_closed_riderNN`). Same witness
`aprioriUBoundClosed`. No `Hext_finite_at_zero`, no `0 < m`. -/
theorem apriori_uepsi_Lp_closed_riderNN
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed (d := d) h Vbound Vint_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed h Vbound Vint_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean := aprioriUepsiMeanClosed_nn h Vbound Vint_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    poincareWirtinger (p := p) hγ_one_le hγ_top
      hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas
      hDu_per hDu_loc hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed h Vbound Vint_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **Nonneg (`riderNN`) closed-form Du bound.** Mirror of
`apriori_Du_bound_closed_form` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0`. The three sub-calls go through their `_riderNN`
siblings; the single nonneg site (`hM_nn`) uses `hMnonneg`. Same witness
`aprioriDuBoundClosed`. No `Hext_finite_at_zero`, no `0 < m`. -/
theorem apriori_Du_bound_closed_form_riderNN
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h.toCongestionAprioriPowerData with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h.toCongestionAprioriPowerData
  have hint_bound :=
    apriori_Du_integrated_bound_closed_riderNN
      (h := h.toCongestionAprioriPowerData) hH0 V Du m u hHJB hMnonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hMnonneg] with x hxm
        exact Real.rpow_nonneg hxm _
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  have hclosed_eq :
      aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed h Vbound Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

/-- **Nonneg (`riderNN`) residue-form aggregate bound.** Mirror of
`apriori_aggregate_bound_residue_form` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0`. The three pieces go through their `_riderNN` siblings;
the `hM_abs_eq` step uses `abs_of_nonneg` under `hMnonneg`. Same
conclusion and witness `aprioriUniformConstantClosed`. No
`Hext_finite_at_zero`, no `0 < m`. -/
theorem apriori_aggregate_bound_residue_form_riderNN
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMnonneg] with x hxm
    rw [abs_of_nonneg hxm]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  set Cd : ℝ := aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form_riderNN (h := h) hH0 V Du m u epsTerms
      Vbound Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN (h := h) hH0 V Du m u epsTerms
      Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    exact Real.rpow_le_rpow (abs_nonneg _) h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, ‖(fun j => Du j x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hDu_i_le_Cd : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ Cd := fun i =>
    le_trans (hDu_i_le i) hCd_bound
  have hSum_Du_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
        ∂(volume : Measure (Fin d → ℝ))) ≤ (d : ℝ) * Cd := by
    have hsum_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ ∑ _i : Fin d, Cd :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∫ x in UnitCube d, |Du i x| ^ γ
                  ∂(volume : Measure (Fin d → ℝ)))
        (g := fun _ => Cd)
        (fun i _ => hDu_i_le_Cd i)
    have hconst_sum : ∑ _i : Fin d, Cd = (d : ℝ) * Cd := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← hconst_sum]; exact hsum_le
  have hCd_nn : 0 ≤ Cd := by
    have h_int_nn : (0 : ℝ) ≤ ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    linarith [le_trans h_int_nn hCd_bound]
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq : lpNormPer p (Du i) ^ γ ≤ Cd := by
      rw [hDu_lp_γ i]
      exact hDu_i_le_Cd i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn
    exact le_trans hu_pw h2
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  have hu_lp_eq : lpNormPer p u ^ γ
      = ∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := u) hp_ne_zero hp_top hu_lp_γ
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p u ^ γ
          = (((∫ x, ‖u x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  unfold aprioriUniformConstantClosed
  show (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ### AE-periodic `riderNN` siblings (T3-drain A2g)

The pointwise `apriori_*_riderNN` family (above) demands pointwise
`IsPeriodic` + `LocallyIntegrable` on `u`/`Du i`. The strong-VI family
that feeds the uniform a-priori aggregator (`AprioriDrain.lean`) carries
only `AEPeriodic` (via `MemLpPer`). The siblings below relax exactly the
periodicity/locality hypotheses to `Periodic.AEPeriodic` (dropping the
now-unused `_meas`/`_loc` riders), routing the single Poincaré–Wirtinger
call through `Periodic.poincareWirtinger_AEPeriodicRep`. Everything else
is byte-identical to the pointwise originals; in particular **no** new
analytic assumption is introduced and `Hext_finite_at_zero`/`0 < m` are
NOT used (the boundary `m = 0` content stays on the `hH0` rider). -/

/-- **AE-periodic sibling of `apriori_uepsi_Lp_closed_riderNN`.** -/
theorem apriori_uepsi_Lp_closed_riderNN_aePeriodic
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed (d := d) h Vbound Vint_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed h Vbound Vint_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean := aprioriUepsiMeanClosed_nn h Vbound Vint_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  -- AE-periodic Poincaré–Wirtinger via chosen representatives.
  let hu_rep : Periodic.AEPeriodicRep (d := d) u := Classical.choice hu_per
  let hDu_rep : ∀ i, Periodic.AEPeriodicRep (d := d) (Du i) :=
    fun i => Classical.choice (hDu_per i)
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    Periodic.poincareWirtinger_AEPeriodicRep (d := d) (p := p) hγ_one_le hγ_top
      hu_rep hu_sob
      hDu_weak hDu_rep hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed h Vbound Vint_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **AE-periodic sibling of `apriori_Du_bound_closed_form_riderNN`.** -/
theorem apriori_Du_bound_closed_form_riderNN_aePeriodic
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  -- The pointwise original routes the Poincaré content through
  -- `apriori_uepsi_Lp_closed_riderNN`; here we route it through the
  -- AE-periodic sibling and otherwise mimic the original byte-for-byte.
  classical
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h.toCongestionAprioriPowerData with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h.toCongestionAprioriPowerData
  have hint_bound :=
    apriori_Du_integrated_bound_closed_riderNN
      (h := h.toCongestionAprioriPowerData) hH0 V Du m u hHJB hMnonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN_aePeriodic (h := h) hH0 V Du m u epsTerms
      Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  -- From here the proof is byte-identical to `apriori_Du_bound_closed_form_riderNN`
  -- (the periodicity hypotheses no longer appear; only `hu_pw`/`T`/`S` etc.).
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hMnonneg] with x hxm
        exact Real.rpow_nonneg hxm _
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  have hclosed_eq :
      aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed h Vbound Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

/-- **AE-periodic sibling of `apriori_aggregate_bound_residue_form_riderNN`.** -/
theorem apriori_aggregate_bound_residue_form_riderNN_aePeriodic
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  classical
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN (h := h) hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMnonneg] with x hxm
    rw [abs_of_nonneg hxm]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  set Cd : ℝ := aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form_riderNN_aePeriodic (h := h) hH0 V Du m u epsTerms
      Vbound Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN_aePeriodic (h := h) hH0 V Du m u epsTerms
      Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  -- From here the proof is byte-identical to
  -- `apriori_aggregate_bound_residue_form_riderNN` (no periodicity left).
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    exact Real.rpow_le_rpow (abs_nonneg _) h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, ‖(fun j => Du j x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hDu_i_le_Cd : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ Cd := fun i =>
    le_trans (hDu_i_le i) hCd_bound
  have hSum_Du_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
        ∂(volume : Measure (Fin d → ℝ))) ≤ (d : ℝ) * Cd := by
    have hsum_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ ∑ _i : Fin d, Cd :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∫ x in UnitCube d, |Du i x| ^ γ
                  ∂(volume : Measure (Fin d → ℝ)))
        (g := fun _ => Cd)
        (fun i _ => hDu_i_le_Cd i)
    have hconst_sum : ∑ _i : Fin d, Cd = (d : ℝ) * Cd := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← hconst_sum]; exact hsum_le
  have hCd_nn : 0 ≤ Cd := by
    have h_int_nn : (0 : ℝ) ≤ ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    linarith [le_trans h_int_nn hCd_bound]
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq : lpNormPer p (Du i) ^ γ ≤ Cd := by
      rw [hDu_lp_γ i]
      exact hDu_i_le_Cd i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn
    exact le_trans hu_pw h2
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  have hu_lp_eq : lpNormPer p u ^ γ
      = ∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := u) hp_ne_zero hp_top hu_lp_γ
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p u ^ γ
          = (((∫ x, ‖u x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  unfold aprioriUniformConstantClosed
  show (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ### D3b3 — raw-real (`α, β, C0`)-keyed aggregate-engine HPG layer

Raw-real siblings of the HPG-bundle `_riderNN` closed-form helpers
(`apriori_uepsi_below_closed_nonneg` … the terminal aggregate engine),
keyed by explicit reals `(α β C0 : ℝ)` with `hLower` carrying the
`HypothesisPowerGrowth.lower` content and `h_lagr` the `lagr` content.
Each is a mechanical copy of its bundle sibling, re-pointed to the raw
callees and the `…Raw` constant defs. Originals are intact (additive);
Hext-free (raw-ifying the `_riderNN` variants). -/

theorem apriori_uepsi_below_closed_nonneg_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConstRaw β C0 Vbound)
        * (∫ x in UnitCube d, m x ^ (β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConstRaw β C0 Vbound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  have hC_pos : 0 < C0 := hC0
  have hβ_pos : 0 < β := hβ
  have hβp1_pos : 0 < β + 1 := by linarith
  have h2C_pos : 0 < 2 * C0 := by linarith
  set Vp : ℝ := C0 + max Vbound 0 with hVpdef
  have hVp_nn : 0 ≤ Vp := by
    have h1 : (0 : ℝ) ≤ max Vbound 0 := le_max_right _ _
    linarith [hC_pos.le]
  set lam : ℝ := ((β + 1) / (2 * C0)) ^ ((1 : ℝ) / (β + 1)) with hlamdef
  have hbasis_pos : 0 < (β + 1) / (2 * C0) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (β + 1) = (β + 1) / (2 * C0) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (β + 1) * (β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  set K_Y : ℝ := (Vp / lam) ^ ((β + 1) / β) * (β / (β + 1)) with hK_Ydef
  have hK_Y_nn : 0 ≤ K_Y := by
    have h1 : 0 ≤ Vp / lam := div_nonneg hVp_nn hlam_pos.le
    have h2 : 0 ≤ (Vp / lam) ^ ((β + 1) / β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ β / (β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      Vp * mx ≤ (1 / (2 * C0)) * mx ^ (β + 1) + K_Y := by
    intro mx hmx
    have hlammx_nn : 0 ≤ lam * mx := mul_nonneg hlam_pos.le hmx
    have hVplam_nn : 0 ≤ Vp / lam := div_nonneg hVp_nn hlam_pos.le
    have hY := young_absorb_lin_into_betaPlusOne hβ_pos (Vp / lam) hVplam_nn (lam * mx) hlammx_nn
    have hLHS : (Vp / lam) * (lam * mx) = Vp * mx := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    have hpow_mul :
        (lam * mx) ^ (β + 1) = lam ^ (β + 1) * mx ^ (β + 1) :=
      Real.mul_rpow hlam_pos.le hmx
    have hR1 :
        (lam * mx) ^ (β + 1) / (β + 1)
          = (1 / (2 * C0)) * mx ^ (β + 1) := by
      rw [hpow_mul, hlam_pow_p]
      have hβp1ne : (β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * C0) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    exact hY
  have hpoint :
      (fun x => (1 / (2 * C0)) * m x ^ (β + 1) - (2 * C0 + K_Y))
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [mul_lagrangian_lower_bound_ae_nonneg (β := β) (C := C0)
          hβ_pos hC_pos h_lagr,
        hMnonneg, hVbnd, hEpsNN] with x hLag hxm hxV hxE
    have hxm_nn : 0 ≤ m x := hxm
    have hL : m x ^ (β + 1) / C0 - C0 * m x
                ≤ m x * (-H x (fun i => Du i x) (m x)
                          + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)) :=
      hLag (fun i => Du i x) (m x) hxm_nn
    have habsmle : |V x| ≤ Vbound := hxV
    have hVbound_le_max : Vbound ≤ max Vbound 0 := le_max_left _ _
    have habs_le_pos : |V x| ≤ max Vbound 0 := habsmle.trans hVbound_le_max
    have hneg_le : -V x ≤ |V x| := neg_le_abs _
    have hneg_max : -V x ≤ max Vbound 0 := hneg_le.trans habs_le_pos
    have hmaxneg : -max Vbound 0 ≤ V x := by linarith
    have hVm_lb : -max Vbound 0 * m x ≤ V x * m x :=
      mul_le_mul_of_nonneg_right hmaxneg hxm_nn
    have h12 :
        (1 / C0) * m x ^ (β + 1) - Vp * m x
          ≤ m x * (-H x (fun i => Du i x) (m x)
                      + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x := by
      have hLrw : m x ^ (β + 1) / C0 - C0 * m x
                    = (1 / C0) * m x ^ (β + 1) - C0 * m x := by ring
      rw [hLrw] at hL
      have : Vp * m x = C0 * m x + max Vbound 0 * m x := by
        rw [hVpdef]; ring
      linarith [hL, hVm_lb]
    have hY := hYoung_pt (m x) hxm_nn
    have hY' : (1 / C0) * m x ^ (β + 1) - Vp * m x
                  ≥ (1 / (2 * C0)) * m x ^ (β + 1) - K_Y := by
      have h_aux : (1 / C0) - (1 / (2 * C0)) = (1 / (2 * C0)) := by
        field_simp; ring
      have hrpow_nn : 0 ≤ m x ^ (β + 1) := Real.rpow_nonneg hxm_nn _
      have hcoeff_pos : 0 ≤ (1 / (2 * C0)) := by positivity
      have hsplit : (1 / C0) * m x ^ (β + 1)
                      = (1 / (2 * C0)) * m x ^ (β + 1)
                        + (1 / (2 * C0)) * m x ^ (β + 1) := by
        have h2Cne : (2 * C0) ≠ 0 := ne_of_gt h2C_pos
        have hCne : C0 ≠ 0 := ne_of_gt hC_pos
        field_simp; ring
      linarith [hY, hsplit]
    have hgoal :
        (1 / (2 * C0)) * m x ^ (β + 1) - (2 * C0 + K_Y)
          ≤ m x * (-H x (fun i => Du i x) (m x)
                      + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x := by
      have h2C_nn : 0 ≤ 2 * C0 := h2C_pos.le
      linarith [hY', h12, hxE]
    exact hgoal
  have hLHS_int :
      Integrable (fun x => (1 / (2 * C0)) * m x ^ (β + 1) - (2 * C0 + K_Y))
        (volume.restrict (UnitCube d)) := by
    have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp
    have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
    have hconst : Integrable (fun _ : Fin d → ℝ => (2 * C0 + K_Y))
                    (volume.restrict (UnitCube d)) := integrable_const _
    have hpow : Integrable (fun x => (1 / (2 * C0)) * m x ^ (β + 1))
                  (volume.restrict (UnitCube d)) :=
      hLB_int.const_mul (1 / (2 * C0))
    exact hpow.sub hconst
  have hint_le :
      ∫ x in UnitCube d,
          ((1 / (2 * C0)) * m x ^ (β + 1) - (2 * C0 + K_Y))
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_int hRHS_int hpoint
  rw [← h_identity] at hint_le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have hcube_finite_inst : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  have hLHS_eq :
      ∫ x in UnitCube d,
          ((1 / (2 * C0)) * m x ^ (β + 1) - (2 * C0 + K_Y))
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / (2 * C0))
          * (∫ x in UnitCube d, m x ^ (β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
        - (2 * C0 + K_Y) * (volume (UnitCube d)).toReal := by
    have hsub :
        ∫ x in UnitCube d,
            ((1 / (2 * C0)) * m x ^ (β + 1) - (2 * C0 + K_Y))
          ∂(volume : Measure (Fin d → ℝ))
        = (∫ x in UnitCube d, (1 / (2 * C0)) * m x ^ (β + 1)
            ∂(volume : Measure (Fin d → ℝ)))
          - (∫ x in UnitCube d, (2 * C0 + K_Y)
              ∂(volume : Measure (Fin d → ℝ))) := by
      rw [integral_sub (hLB_int.const_mul (1 / (2 * C0))) (integrable_const _)]
    rw [hsub]
    congr 1
    · rw [integral_const_mul]
    · rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, mul_comm]
  rw [hLHS_eq] at hint_le
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def, volume_unitCube]
  set C' : ℝ := aprioriUepsiBelowConstRaw β C0 Vbound with hC'def
  have hC'_unfold :
      C' = max (2 * C0) ((2 * C0 + K_Y) + 1) := by
    show aprioriUepsiBelowConstRaw β C0 Vbound = _
    rfl
  have hC'_pos : 0 < C' := by
    rw [hC'_unfold]
    have h1 : 0 ≤ 2 * C0 + K_Y := by linarith [h2C_pos.le, hK_Y_nn]
    have h2 : (0 : ℝ) < (2 * C0 + K_Y) + 1 := by linarith
    exact lt_of_lt_of_le h2 (le_max_right _ _)
  have hC'_ge_2C : 2 * C0 ≤ C' := by
    rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : (2 * C0 + K_Y) * vol ≤ C' := by
    rw [hC'_unfold, hvol_eq_one, mul_one]
    have : (2 * C0 + K_Y) ≤ (2 * C0 + K_Y) + 1 := by linarith
    exact this.trans (le_max_right _ _)
  have hint_nn : 0 ≤ ∫ x in UnitCube d, m x ^ (β + 1)
                        ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  have h_coeff : (1 / C') ≤ (1 / (2 * C0)) := by
    apply one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  have h_lhs_term :
      (1 / C') * (∫ x in UnitCube d, m x ^ (β + 1)
                    ∂(volume : Measure (Fin d → ℝ)))
        ≤ (1 / (2 * C0)) * (∫ x in UnitCube d, m x ^ (β + 1)
                              ∂(volume : Measure (Fin d → ℝ))) :=
    mul_le_mul_of_nonneg_right h_coeff hint_nn
  have h_rhs_const : -C' ≤ -((2 * C0 + K_Y) * vol) := by linarith
  linarith [h_lhs_term, h_rhs_const, hint_le]

/-- **Pointwise nonneg (`riderNN`) closed-form m-bound.** Identical
conclusion and witness `aprioriMBoundClosedRaw β C0 Vbound Vint_bound` as the
strict `apriori_m_bound_closed`, but with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m`. The boundary `m = 0` content enters only through the
HJB-upper leg, routed through `apriori_uepsi_above_riderNN` with the
paper rider `hH0`; the lower leg uses `apriori_uepsi_below_closed_nonneg`.
No `Hext_finite_at_zero`, no `0 < m`. -/

theorem apriori_m_bound_closed_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∫ x in UnitCube d, m x ^ (β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosedRaw β C0 Vbound Vint_bound := by
  have hC_pos : 0 < C0 := hC0
  have hβ_pos : 0 < β := hβ
  have hβp1_pos : 0 < β + 1 := by linarith
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set C' : ℝ := aprioriUepsiBelowConstRaw β C0 Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConstRaw_pos β C0 Vbound hC0
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_nonneg_raw (d := d) α β C0 hα hβ hC0 hLower V Du m u epsTerms Vbound
      h_lagr hMnonneg hVbnd hEpsNN h_identity hLB_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN_raw (d := d) α β C0 hβ hC0 hLower hH0
      V Du m u hHJB hMnonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + C0 * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul C0
      have : Integrable (fun x => (|V x| + C0 * (m x ^ β + 1))
                                    - C0 * (m x ^ β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul C0
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, C0 * (m x ^ β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = C0 * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hcomb : (1 / C') * X - C' ≤ Vint + C0 * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + C0 * (Y + vol) := habove_eq
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (β + 1) * δ / β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (β / (β + 1)) = δ := by
    rw [hlam_pow_def]; field_simp
  set lam : ℝ := lam_pow ^ (β / (β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((β + 1) / β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : β / (β + 1) * ((β + 1) / β) = 1 := by
      have hβne : β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  set R : ℝ := aprioriMBoundResidualRaw β C0 Vbound with hR_def
  have hR_unfold : R = (C0 / lam) ^ (β + 1) / (β + 1) := by
    show aprioriMBoundResidualRaw β C0 Vbound = _
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ C0 / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (C0 / lam) ^ (β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      C0 * mx ^ β ≤ δ * mx ^ (β + 1) + R := by
    intro mx hmx
    have hY := young_absorb_pow_into_betaPlusOne (β := β) hβ_pos
                  C0 hC_pos.le mx hmx lam hlam_pos
    rw [hlam_pow_id] at hY
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  have hY_int :
      Integrable (fun x => C0 * m x ^ β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul C0
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => C0 * m x ^ β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (β + 1) + R) := by
    filter_upwards [hMnonneg] with x hxm
    exact hYoung_pt (m x) hxm
  have hYint_le :
      ∫ x in UnitCube d, C0 * m x ^ β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  have hYint_LHS :
      ∫ x in UnitCube d, C0 * m x ^ β
          ∂(volume : Measure (Fin d → ℝ))
        = C0 * Y := by
    rw [integral_const_mul]
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ))
        = δ * X + R * vol := by
    rw [integral_add (hLB_int.const_mul δ) (integrable_const _),
        integral_const_mul]
    have hone_int :
        ∫ _ in UnitCube d, R ∂(volume : Measure (Fin d → ℝ)) = R * vol := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, hvol_def, mul_comm]
    rw [hone_int]
  rw [hYint_LHS, hYint_RHS] at hYint_le
  have hcomb' :
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + C0 * vol := by
    have : C0 * (Y + vol) = C0 * Y + C0 * vol := by ring
    have h1 : Vint + C0 * (Y + vol) ≤ Vint + (δ * X + R * vol) + C0 * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + C0 * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + C0 * vol := by
    linarith [habs, hVint_le]
  have hM_unfold :
      aprioriMBoundClosedRaw β C0 Vbound Vint_bound
        = 2 * C' * (C' + Vint_bound + R + C0) := by
    show aprioriMBoundClosedRaw β C0 Vbound Vint_bound = _
    rfl
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + C0 * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  rw [hM_unfold]
  exact hmul

/-- **Nonneg (`riderNN`) closed-form mean bound on `∫ u`.** Mirror of
`apriori_uepsi_mean_closed` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0`. The m-bound leg uses `apriori_m_bound_closed_riderNN`,
the lower leg `apriori_uepsi_below_closed_nonneg`, the upper leg
`apriori_uepsi_above_riderNN`; the three nonneg sites use `hMnonneg`
directly. No `Hext_finite_at_zero`, no `0 < m`. -/

theorem apriori_uepsi_mean_closed_riderNN_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound := by
  have hC_pos : 0 < C0 := hC0
  have hβ_pos : 0 < β := hβ
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set M : ℝ := aprioriMBoundClosedRaw β C0 Vbound Vint_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  set C' : ℝ := aprioriUepsiBelowConstRaw β C0 Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConstRaw_pos β C0 Vbound hC0
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_nonneg_raw (d := d) α β C0 hα hβ hC0 hLower V Du m u epsTerms Vbound
      h_lagr hMnonneg hVbnd hEpsNN h_identity hLB_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN_raw (d := d) α β C0 hβ hC0 hLower hH0
      V Du m u hHJB hMnonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul C0
    have : Integrable (fun x => (|V x| + C0 * (m x ^ β + 1))
                                  - C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + C0 * (Y + vol) := by
    have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul C0
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, C0 * (m x ^ β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = C0 * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hY_le_X_plus_vol : Y ≤ X + vol := by
    have hpoint :
        (fun x => m x ^ β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (β + 1) + 1) := by
      filter_upwards [hMnonneg] with x hxm
      exact rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = X + vol := by
      rw [integral_add hLB_int hone_int']
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hRHS_eq] at hint_le
    exact hint_le
  have hX_le_M : X ≤ M := hM_le
  have hY_le_M_plus_vol : Y ≤ M + vol := by linarith
  have hVint_le : Vint ≤ Vint_bound := hVint
  set Uint : ℝ := ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) with hUint_def
  have hUint_ub : Uint ≤ Vint_bound + C0 * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + C0 * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : C0 * (Y + vol) ≤ C0 * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + C0 * (Y + vol) ≤ Vint_bound + C0 * (M + 2 * vol) := by
      have : C0 * ((M + vol) + vol) = C0 * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  have hCmean_unfold :
      aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound
        = max C' (Vint_bound + C0 * (M + 2)) := by
    show aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  have hUint_ub' : Uint ≤ Vint_bound + C0 * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + C0 * (M + 2) ≤ aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hneg : -aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · linarith [hUint_ub', hCmean_ge_ub]

/-- **Nonneg (`riderNN`) closed-form Lᵖ bound on `u`.** Mirror of
`apriori_uepsi_Lp_closed` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0` (via `apriori_uepsi_mean_closed_riderNN`). Same witness
`aprioriUBoundClosed`. No `Hext_finite_at_zero`, no `0 < m`. -/

theorem apriori_uepsi_Lp_closed_riderNN_raw
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar α β))
    (hγ_top : ENNReal.ofReal (gammaBar α β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar α β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar α β)) u ≤
      aprioriUBoundClosedRaw d β C0 Vbound Vint_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar α β)) (Du i)) + 1) := by
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar α β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean := aprioriUepsiMeanClosedRaw_nn β C0 Vbound Vint_bound hC0
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    poincareWirtinger (p := p) hγ_one_le hγ_top
      hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas
      hDu_per hDu_loc hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosedRaw d β C0 Vbound Vint_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosedRaw d β C0 Vbound Vint_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **Nonneg (`riderNN`) closed-form Du bound.** Mirror of
`apriori_Du_bound_closed_form` with `hMpos : 0 < m` relaxed to
`hMnonneg : 0 ≤ m` and the boundary `m = 0` content routed through the
paper rider `hH0`. The three sub-calls go through their `_riderNN`
siblings; the single nonneg site (`hM_nn`) uses `hMnonneg`. Same witness
`aprioriDuBoundClosed`. No `Hext_finite_at_zero`, no `0 < m`. -/

theorem apriori_uepsi_Lp_closed_riderNN_aePeriodic_raw
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar α β))
    (hγ_top : ENNReal.ofReal (gammaBar α β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar α β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar α β)) u ≤
      aprioriUBoundClosedRaw d β C0 Vbound Vint_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar α β)) (Du i)) + 1) := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar α β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosedRaw β C0 Vbound Vint_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean := aprioriUepsiMeanClosedRaw_nn β C0 Vbound Vint_bound hC0
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  -- AE-periodic Poincaré–Wirtinger via chosen representatives.
  let hu_rep : Periodic.AEPeriodicRep (d := d) u := Classical.choice hu_per
  let hDu_rep : ∀ i, Periodic.AEPeriodicRep (d := d) (Du i) :=
    fun i => Classical.choice (hDu_per i)
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    Periodic.poincareWirtinger_AEPeriodicRep (d := d) (p := p) hγ_one_le hγ_top
      hu_rep hu_sob
      hDu_weak hDu_rep hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosedRaw d β C0 Vbound Vint_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosedRaw d β C0 Vbound Vint_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

end SimplePower
end Theorems
end StationaryMFG
end
