module

public import StationaryMFG.Theorems.SimplePower.StrongIsStrong
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Periodic.SobolevPoincare
public import Mathlib.Analysis.MeanInequalities
public import StationaryMFG.Theorems.SimplePower.Apriori.Part1
import all StationaryMFG.Theorems.SimplePower.Apriori.Part1
public import StationaryMFG.Theorems.SimplePower.Apriori.Part2
import all StationaryMFG.Theorems.SimplePower.Apriori.Part2

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


theorem apriori_Du_bound_closed_form_riderNN_raw
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
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
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
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar α β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar α β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar α β with hγ_def
  set βp : ℝ := betaBar' β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < β := hβ
  have hα_one_lt : 1 < α := hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos α β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' α β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConstRaw β C0 with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConstRaw_nn β C0 hC0
  have hint_bound :=
    apriori_Du_integrated_bound_closed_riderNN_raw
      (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u hHJB hMnonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  set M : ℝ := aprioriMBoundClosedRaw β C0 Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  set Cu : ℝ := aprioriUBoundClosedRaw d β C0 Vbound Vint_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosedRaw_nn (d := d) β C0 Vbound Vint_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar α β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar α β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
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
  have hbetaBar_eq : betaBar β = β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' β
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
      aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound = _
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

theorem apriori_Du_bound_closed_form_riderNN_aePeriodic_raw
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
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
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
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar α β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar α β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound := by
  -- The pointwise original routes the Poincaré content through
  -- `apriori_uepsi_Lp_closed_riderNN`; here we route it through the
  -- AE-periodic sibling and otherwise mimic the original byte-for-byte.
  classical
  set γ : ℝ := gammaBar α β with hγ_def
  set βp : ℝ := betaBar' β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < β := hβ
  have hα_one_lt : 1 < α := hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos α β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' α β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConstRaw β C0 with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConstRaw_nn β C0 hC0
  have hint_bound :=
    apriori_Du_integrated_bound_closed_riderNN_raw
      (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u hHJB hMnonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  set M : ℝ := aprioriMBoundClosedRaw β C0 Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  set Cu : ℝ := aprioriUBoundClosedRaw d β C0 Vbound Vint_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosedRaw_nn (d := d) β C0 Vbound Vint_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar α β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar α β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN_aePeriodic_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms
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
  have hbetaBar_eq : betaBar β = β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' β
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
      aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

theorem apriori_aggregate_bound_residue_form_riderNN_aePeriodic_raw
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
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
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
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar α β)) u) :
    (∫ x in UnitCube d, |m x| ^ (β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar α β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar α β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosedRaw d α β C0 Vbound Vint_bound Vβp_bound := by
  classical
  set γ : ℝ := gammaBar α β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < β := hβ
  have hα_one_lt : 1 < α := hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos α β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  set M : ℝ := aprioriMBoundClosedRaw β C0 Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_riderNN_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMnonneg] with x hxm
    rw [abs_of_nonneg hxm]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  set Cd : ℝ := aprioriDuBoundClosedRaw d α β C0 Vbound Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form_riderNN_aePeriodic_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms
      Vbound Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  set Cu : ℝ := aprioriUBoundClosedRaw d β C0 Vbound Vint_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosedRaw_nn (d := d) β C0 Vbound Vint_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_riderNN_aePeriodic_raw (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms
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
  unfold aprioriUniformConstantClosedRaw
  show (∫ x in UnitCube d, |m x| ^ (β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ### Day-6 closed-field probe — migrated to `Banach/AssemblyContext.lean`

The Day-6 audit probe `paperSection8_h_upper_of_powerGrowth`
(`infra-P5-T10-v7-paperSolFor-pre-scope` D-pre.6) has been promoted to
a non-private producer in
`StationaryMFG/Theorems/SimplePower/Banach/AssemblyContext.lean`
as part of the `PaperSection8ClosedMeasFields` partial bundle
(task `paperSolFor-analytic-measurability`, 2026-05-15). The producer
is a one-line projection of `HypothesisPowerGrowth.H_upper_pointwise`
and is consumed by both the audit and the
`PaperSection8ClosedMeasFields.of_paperHypotheses` discharger. -/

end SimplePower
end Theorems
end StationaryMFG
