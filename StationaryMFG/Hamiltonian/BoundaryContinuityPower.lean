module

public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Monotone
public import StationaryMFG.Hamiltonian.BoundaryContinuityConvex

@[expose] public section

/-!
# Joint boundary continuity under simple power growth

Lasry--Lions monotonicity at masses `m` and `m / 2` bounds the difference
of two momentum slices by the locally bounded momentum field. Passing to
the finite boundary limits makes the boundary trace locally Lipschitz.
No identification of the supplied field with a derivative is required.
-/

noncomputable section

namespace StationaryMFG.Hamiltonian

open MeasureTheory Filter Topology
open StationaryMFG.Periodic
open scoped ENNReal

variable {d : ℕ}

private lemma boundary_abs_dot_le (v w : Fin d → ℝ) :
    |euclideanDot v w| ≤ (d : ℝ) * ‖v‖ * ‖w‖ := by
  calc
    |euclideanDot v w| ≤ ∑ i, |v i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖v‖ * ‖w‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w i)
        (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖v‖ * ‖w‖ := by simp [mul_assoc]

private lemma boundary_field_bound
    {F : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C a b R : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ p m, 0 < m → ‖F p m‖ ≤ C * (‖p‖ ^ a + m ^ b + 1))
    {p : Fin d → ℝ} {m : ℝ} (hp : ‖p‖ ≤ R) (hm : 0 < m) (hm1 : m ≤ 1) :
    ‖F p m‖ ≤ C * (R ^ a + 2) := by
  have hpPow := Real.rpow_le_rpow (norm_nonneg p) hp ha
  have hmPow := Real.rpow_le_one hm.le hm1 hb
  exact (hF p m hm).trans (mul_le_mul_of_nonneg_left (by linarith) hC)

private lemma boundary_scaled_upper
    {H : (Fin d → ℝ) → ℝ → ℝ}
    {F : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C a b R : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ p m, 0 < m → ‖F p m‖ ≤ C * (‖p‖ ^ a + m ^ b + 1))
    (hmon : ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
      0 ≤ (-H p₁ m₁ + H p₂ m₂) * (m₁ - m₂) +
        euclideanDot (m₁ • F p₁ m₁ - m₂ • F p₂ m₂) (p₁ - p₂))
    {p q : Fin d → ℝ} {m : ℝ}
    (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R) (hm : 0 < m) (hm1 : m ≤ 1) :
    H p m - H q (m / 2) ≤
      (3 * (d : ℝ) * (C * (R ^ a + 2))) * ‖p - q‖ := by
  let M := C * (R ^ a + 2)
  have hFp : ‖F p m‖ ≤ M := boundary_field_bound hC ha hb hF hp hm hm1
  have hFq : ‖F q (m / 2)‖ ≤ M :=
    boundary_field_bound hC ha hb hF hq (half_pos hm) (by linarith)
  have hdp := (boundary_abs_dot_le (F p m) (p - q)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFp (Nat.cast_nonneg d)) (norm_nonneg _))
  have hdq := (boundary_abs_dot_le (F q (m / 2)) (p - q)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFq (Nat.cast_nonneg d)) (norm_nonneg _))
  have hmono := hmon p m q (m / 2) hm (half_pos hm)
  rw [euclideanDot_sub_left, euclideanDot_smul_left, euclideanDot_smul_left] at hmono
  have hfactor : 0 ≤ (-H p m + H q (m / 2) +
      2 * euclideanDot (F p m) (p - q) -
      euclideanDot (F q (m / 2)) (p - q)) * (m / 2) := by
    nlinarith only [hmono]
  have hdiff := nonneg_of_mul_nonneg_left hfactor (half_pos hm)
  have hdp' := (abs_le.mp hdp).2
  have hdq' := (abs_le.mp hdq).1
  dsimp [M] at hdp' hdq'
  nlinarith only [hdiff, hdp', hdq']

private lemma boundary_trace_upper
    {H : (Fin d → ℝ) → ℝ → ℝ}
    {F : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C a b R : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ p m, 0 < m → ‖F p m‖ ≤ C * (‖p‖ ^ a + m ^ b + 1))
    (hmon : ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
      0 ≤ (-H p₁ m₁ + H p₂ m₂) * (m₁ - m₂) +
        euclideanDot (m₁ • F p₁ m₁ - m₂ • F p₂ m₂) (p₁ - p₂))
    (hlim : ∀ p, Tendsto (H p) (𝓝[>] (0 : ℝ)) (𝓝 (H p 0)))
    {p q : Fin d → ℝ} (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R) :
    H p 0 - H q 0 ≤ (3 * (d : ℝ) * (C * (R ^ a + 2))) * ‖p - q‖ := by
  have hhalf : Tendsto (fun m : ℝ => m / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).div_const 2
    · filter_upwards [self_mem_nhdsWithin] with m hm
      change 0 < m / 2
      exact half_pos hm
  apply le_of_tendsto ((hlim p).sub ((hlim q).comp hhalf))
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ m : ℝ in 𝓝[>] 0, m < 1 from
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds)] with m hm hm1
  exact boundary_scaled_upper hC ha hb hF hmon hp hq hm hm1.le

private lemma continuous_boundary_trace_of_power_bound
    {H : (Fin d → ℝ) → ℝ → ℝ}
    {F : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ p m, 0 < m → ‖F p m‖ ≤ C * (‖p‖ ^ a + m ^ b + 1))
    (hmon : ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
      0 ≤ (-H p₁ m₁ + H p₂ m₂) * (m₁ - m₂) +
        euclideanDot (m₁ • F p₁ m₁ - m₂ • F p₂ m₂) (p₁ - p₂))
    (hlim : ∀ p, Tendsto (H p) (𝓝[>] (0 : ℝ)) (𝓝 (H p 0))) :
    Continuous (fun p => H p 0) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let R := ‖q‖ + 1
  let K := 3 * (d : ℝ) * (C * (R ^ a + 2))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by positivity) (mul_nonneg hC (by positivity))
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨min 1 (ε / (K + 1)), lt_min (by norm_num) (div_pos hε hK1), ?_⟩
  intro p hp
  have hpdist : ‖p - q‖ < min 1 (ε / (K + 1)) := by simpa [dist_eq_norm] using hp
  have hp1 : ‖p - q‖ < 1 := lt_of_lt_of_le hpdist (min_le_left _ _)
  have hpR : ‖p‖ ≤ R := by
    have htri : ‖p‖ ≤ ‖p - q‖ + ‖q‖ := by
      simpa using norm_add_le (p - q) q
    dsimp [R]
    linarith
  have hqR : ‖q‖ ≤ R := by dsimp [R]; linarith
  have hup : H p 0 - H q 0 ≤ K * ‖p - q‖ :=
    boundary_trace_upper hC ha hb hF hmon hlim hpR hqR
  have hlo : H q 0 - H p 0 ≤ K * ‖p - q‖ := by
    simpa [norm_sub_rev] using
      (boundary_trace_upper hC ha hb hF hmon hlim hqR hpR)
  have habs : |H p 0 - H q 0| ≤ K * ‖p - q‖ :=
    abs_le.mpr ⟨by linarith, hup⟩
  have hpε : ‖p - q‖ < ε / (K + 1) :=
    lt_of_lt_of_le hpdist (min_le_right _ _)
  have hmul : (K + 1) * ‖p - q‖ < ε := by
    have := (lt_div_iff₀ hK1).mp hpε
    nlinarith only [this]
  rw [Real.dist_eq]
  exact lt_of_le_of_lt habs (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (norm_nonneg _)) hmul)

/-- Under the existing simple-power hypotheses, the Hamiltonian is jointly
continuous up to zero mass. The locally bounded field and Lasry--Lions
monotonicity give a locally Lipschitz boundary trace; monotonicity in mass
then upgrades the finite slice limits to joint continuity. -/
theorem HypothesisHextJointCont.of_powerGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hHat0 : HypothesisHat0 (d := d) H)
    (hAgree : H_zero_eq_Hext (d := d) H) :
    HypothesisHextJointCont (d := d) H := by
  have ha : 0 ≤ hpow.α - 1 := sub_nonneg.mpr hpow.hα.le
  have hαpos : 0 < hpow.α := lt_trans zero_lt_one hpow.hα
  have hb : 0 ≤ hpow.β - hpow.β / hpow.α := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hαpos).mpr
    simpa using mul_le_mul_of_nonneg_left hpow.hα.le hpow.hβ.le
  filter_upwards [hmon.monotone, hpow.DpH_upper, hpow.continuous_H_pm,
    H_rc0_of_hHat0_powerGrowth hpow hHat0 hAgree, antitone_in_m hmon]
    with x hxmon hxbound hxcont hxlim hxanti
  exact continuousOn_closedHalfspace_of_antitone (H x) hxcont hxlim hxanti
    (continuous_boundary_trace_of_power_bound hpow.hC.le ha hb hxbound hxmon hxlim)

end StationaryMFG.Hamiltonian
