module

public import StationaryMFG.Theorems.Congestion.PaperSolutionBoundary
public import StationaryMFG.Theorems.Congestion.PaperWitnessHJB
public import StationaryMFG.Theorems.Congestion.PaperMinLimit

@[expose] public section

/-!
# Complementary Hamilton--Jacobi equality

The downward test density is the minimum of the solution density and the
positive-domain auxiliary infimum at tolerance `-k`. All boundary values
needed for this test are finite locally by the extended HJB inequality.
-/

noncomputable section

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Solutions.MFG

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}

/-- Positive points below the auxiliary infimum cannot have a Hamiltonian
value strictly below its threshold. -/
theorem le_value_of_le_positiveAux {F : ℝ → ℝ} {b a : ℝ}
    (hn : (positiveAuxSet F 0 b).Nonempty)
    (hc : ContinuousOn F (Ioi 0)) (ha : AntitoneOn F (Ioi 0))
    (hapos : 0 < a) (hle : a ≤ positiveAux F 0 b) : b ≤ F a := by
  rcases hle.eq_or_lt with he | hl
  · rw [he, positiveAux_value_eq_of_lt hn hc ha le_rfl (he ▸ hapos)]
  · by_contra hnot
    have hF : F a ≤ b := (lt_of_not_ge hnot).le
    have hμa := (positiveAux_le_iff hn hc ha hapos).2 ⟨hapos.le, hF⟩
    exact (not_lt_of_ge hμa) hl

/-- The density used for the complementary HJB test. -/
def complementDensity (k : ℝ) (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => min (m x) (positiveAux (H x (fun i => Du i x)) 0 (-k - u x + V x))

theorem complementDensity_memLp
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i)) :
    MemLpPer (ENNReal.ofReal (hcong.β + 1)) (complementDensity k m u V Du H) := by
  apply MemLp.toMemLpPer
  simpa only [complementDensity, Pi.inf_def] using!
    hm.toMemLp.inf (positiveAux_memLp (k := -k) hmon hcong (MemLpPer.const 0) hu hV hDu).toMemLp

theorem complementDensity_nonneg
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hne : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (fun i => Du i x)) 0 (-k - u x + V x)).Nonempty) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ complementDensity k m u V Du H x := by
  filter_upwards [hm, hne] with x hx hn
  exact le_min hx (positiveAux_nonneg hn)

/-- The downward test inherits the finite extended HJB upper bound. -/
theorem Hext_complementDensity_le
    {k : ℝ} (hk : 0 ≤ k) {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hne : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (fun i => Du i x)) 0 (-k - u x + V x)).Nonempty)
    (hc : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0))
    (ha : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0))
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (complementDensity k m u V Du H x) ≤
        ((V x - u x : ℝ) : WithTop ℝ) := by
  filter_upwards [hne, hc, ha, hHJB] with x hn hc ha hH
  unfold complementDensity
  rcases le_total (m x) (positiveAux (H x (fun i => Du i x)) 0 (-k - u x + V x)) with h | h
  · rwa [min_eq_left h]
  · rw [min_eq_right h]
    exact (Hext_positiveAux_le hn hc ha).trans (WithTop.coe_le_coe.mpr (by linarith))

/-- The integral inequality forces the downward correction to vanish. -/
theorem HJB_ge_at_k_of_complement_integral
    {k : ℝ} (hk : 0 < k) {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hne : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (fun i => Du i x)) 0 (-k - u x + V x)).Nonempty)
    (hc : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0))
    (ha : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0))
    (hdiff : Integrable (fun x => m x - complementDensity k m u V Du H x)
      (volume.restrict (UnitCube d)))
    (hprod : Integrable (fun x =>
      (u x + finiteExtension H x (fun i => Du i x)
        (complementDensity k m u V Du H x) - V x) *
        (complementDensity k m u V Du H x - m x)) (volume.restrict (UnitCube d)))
    (hint : (∫ x in UnitCube d,
      (u x + finiteExtension H x (fun i => Du i x)
        (complementDensity k m u V Du H x) - V x) *
        (complementDensity k m u V Du H x - m x)) ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → -k ≤ u x + H x (fun i => Du i x) (m x) - V x := by
  let ν := complementDensity k m u V Du H
  have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      k * (m x - ν x) ≤
        (u x + finiteExtension H x (fun i => Du i x) (ν x) - V x) * (ν x - m x) := by
    filter_upwards [hne, hc, ha] with x hn hc ha
    rcases le_total (m x) (positiveAux (H x (fun i => Du i x)) 0 (-k - u x + V x)) with h | h
    · have he : ν x = m x := min_eq_left h
      rw [he, sub_self, mul_zero, mul_zero]
    · have he : ν x = positiveAux (H x (fun i => Du i x)) 0 (-k - u x + V x) := min_eq_right h
      have hlow : u x + finiteExtension H x (fun i => Du i x) (ν x) - V x ≤ -k := by
        rw [he]
        linarith [finiteExtension_positiveAux_le hn hc ha]
      have hnm : ν x - m x ≤ 0 := sub_nonpos.mpr (min_le_left _ _)
      have hh := mul_le_mul_of_nonpos_right hlow hnm
      nlinarith
  have hn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x - ν x :=
    Eventually.of_forall fun x => sub_nonneg.mpr (min_le_left _ _)
  have hi : k * (∫ x in UnitCube d, m x - ν x) ≤ 0 := by
    rw [← integral_const_mul]
    exact (integral_mono_ae (hdiff.const_mul k) hprod hbound).trans hint
  have hz : (∫ x in UnitCube d, m x - ν x) = 0 := by
    have hp := integral_nonneg_of_ae hn
    nlinarith
  have heq := (integral_eq_zero_iff_of_nonneg_ae hn hdiff).mp hz
  filter_upwards [heq, hne, hc, ha] with x he hn hc ha hmx
  have hmin : min (m x) (positiveAux (H x (fun i => Du i x)) 0 (-k - u x + V x)) = m x :=
    (sub_eq_zero.mp he).symm
  have hle := le_value_of_le_positiveAux hn hc ha hmx (min_eq_left_iff.mp hmin)
  linarith

/-- Countably many lower tolerances give equality on the positive-density
set once the extended HJB upper bound is known. -/
theorem HJB_eq_pos_of_negative_tolerances
    {m u V : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ))
    (hge : ∀ k : ℝ, 0 < k → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → -k ≤ u x + H x (fun i => Du i x) (m x) - V x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x →
      u x + H x (fun i => Du i x) (m x) - V x = 0 := by
  have hall := ae_all_iff.mpr fun n => hge (boundaryMass n) (boundaryMass_pos n)
  filter_upwards [hall, hHJB] with x hx hH hp
  rw [Hext_of_pos H x (fun i => Du i x) hp] at hH
  have hle := WithTop.coe_le_coe.mp hH
  have ht : Tendsto (fun n => -boundaryMass n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using
      (boundaryMass_tendsto.mono_right nhdsWithin_le_nhds).neg
  have hge := le_of_tendsto ht (Eventually.of_forall fun n => hx n hp)
  linarith

/-- Complementary HJB equality from positive truncations of the downward
test, common to the Banach witness and periodic limiting VI. -/
theorem HJB_eq_pos_of_complement_truncationVI
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {m u V : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ))
    (hper : ∀ k : ℝ, 0 < k → ∀ δ : ℝ, 0 < δ →
      (∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (max (complementDensity k m u V Du H x) δ) - V x) *
          (max (complementDensity k m u V Du H x) δ - m x)) ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x →
      u x + H x (fun i => Du i x) (m x) - V x = 0 := by
  have hc : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have ha : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0) :=
    (antitone_in_m hmon).mono fun x hx => hx _
  apply HJB_eq_pos_of_negative_tolerances hHJB
  intro k hk
  let ν := complementDensity k m u V Du H
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong (-k)
    (fun _ => 0) u V Du
  have hν : MemLpPer (ENNReal.ofReal (hcong.β + 1)) ν :=
    complementDensity_memLp hmon hcong hm hu hV hDu
  have hνnn := complementDensity_nonneg hmnn hne
  have hHν := Hext_complementDensity_le hk.le hne hc ha hHJB
  have hp : AEMeasurable (fun x i => Du i x) (volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
  obtain ⟨hprod, hlim⟩ := boundedDensity_integral_tendsto hmon hcong
    (fun x i => Du i x) m u V ν hp hm.aestronglyMeasurable.aemeasurable
    hu.aestronglyMeasurable.aemeasurable hV.aestronglyMeasurable.aemeasurable
    hν.aestronglyMeasurable.aemeasurable hνnn hHν
    (auxiliary_dominator_integrable hcong.hβ hcong.C 0 hm hu hV hν hνnn)
  have hint := le_of_tendsto hlim
    (Eventually.of_forall fun n => hper k hk (boundaryMass n) (boundaryMass_pos n))
  have hdiff : Integrable (fun x => m x - ν x) (volume.restrict (UnitCube d)) := by
    apply memLp_one_iff_integrable.mp
    have hd : MemLpPer (ENNReal.ofReal (hcong.β + 1)) (fun x => m x - ν x) :=
      hm.toMemLp.sub hν.toMemLp
    exact (hd.mono_exponent_finite (ENNReal.one_le_ofReal.mpr (by linarith [hcong.hβ]))
      ENNReal.ofReal_ne_top).toMemLp
  exact HJB_ge_at_k_of_complement_integral hk hne hc ha hdiff hprod hint

/-- The downward density is an admissible weighted-gradient test, using
the locally finite extended HJB bound. -/
theorem complementDensity_quotient_memLp
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {k : ℝ} (hk : 0 ≤ k) {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ)) :
    MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
        (complementDensity k m u V Du H x ^ hcong.τ + 1)) := by
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong (-k)
    (fun _ => 0) u V Du
  have hν := complementDensity_memLp (k := k) hmon hcong hm hu hV hDu
  have hνnn := complementDensity_nonneg hmnn hne
  have hc : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have ha : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0) :=
    (antitone_in_m hmon).mono fun x hx => hx _
  exact solution_quotient_memLp hmon hcong hν hu hV hDu hνnn
    (Hext_complementDensity_le hk hne hc ha hHJB)

/-- Complementary HJB equality for the abstract periodic variational
inequality. The extended upper bound is the already-proved first step. -/
theorem HJB_eq_pos_of_abstractPeriodicVI
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {m u V : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmPer : IsPeriodic m) (huPer : IsPeriodic u) (hVPer : IsPeriodic V)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hHPer : ∀ p t, 0 < t → IsPeriodic (fun x => H x p t))
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
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x →
      u x + H x (fun i => Du i x) (m x) - V x = 0 := by
  apply HJB_eq_pos_of_complement_truncationVI hmon hcong hm hu hV hDu hmnn hHJB
  intro k hk δ hδ
  have hν := complementDensity_memLp (k := k) hmon hcong hm hu hV hDu
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong (-k)
    (fun _ => 0) u V Du
  have hνnn := complementDensity_nonneg hmnn hne
  have hQ := complementDensity_quotient_memLp hmon hcong hk.le hm hu hV hDu hmnn hHJB
  have hσPer : IsPeriodic (fun x => positiveAux (H x (fun i => Du i x))
      0 (-k - u x + V x)) := by
    apply positiveAux_periodic _ (IsPeriodic.const 0)
      (((IsPeriodic.const (-k)).sub huPer).add hVPer)
    intro t ht κ x
    have hpEq : (fun i => Du i (x + fun i => (κ i : ℝ))) = (fun i => Du i x) :=
      funext fun i => hDuPer i κ x
    dsimp only
    rw [hpEq]
    exact hHPer _ t ht κ x
  have hνPer : IsPeriodic (complementDensity k m u V Du H) := by
    intro κ x
    unfold complementDensity
    have hs := hσPer κ x
    dsimp only at hs
    rw [hmPer κ x, hs]
  have hαt : 0 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    exact mul_nonneg (le_of_lt (lt_trans zero_lt_one hcong.hα))
      (by have := div_nonneg hcong.hτ.1 hcong.hβ.le; linarith)
  let T := positiveTruncTestPair hδ hcong.hτ.1 hαt hνPer huPer hDuPer
    hν hνnn huSob hDu hDuWeak hQ
  exact congestionLimitVI_integral_le_of_abstract_at_periodicDensity habs T rfl rfl

/-- Complementary HJB equality at the same concrete Banach witness as
the regularized VI. No global finite-boundary agreement is assumed. -/
theorem HJB_eq_pos_of_BanachVI
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    (w : congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hVI : ∀ v ∈ congestionBanachK d
      (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      hcong.α hcong.β hcong.τ,
      0 ≤ congestionAepsiOpK hmon hcong hVmeas hV ε v (v - w))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ w.1 x)
    (hDuWeak : ∀ i, HasWeakDerivPer i (⇑w.2.1) (⇑(w.2.2 i))) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < w.1 x →
      w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x = 0 := by
  have hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) (⇑w.1) := Lp.memLp w.1
  have huGamma : MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (⇑w.2.1) := Lp.memLp w.2.1
  have hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (⇑(w.2.2 i)) :=
    fun i => Lp.memLp (w.2.2 i)
  have hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) (⇑w.2.1) := by
    apply huGamma.mono_exponent_finite _ ENNReal.ofReal_ne_top
    apply ENNReal.ofReal_le_ofReal
    have hb : 0 < (hcong.β + 1) / hcong.β := div_pos (by linarith [hcong.hβ]) hcong.hβ
    nlinarith [mul_le_mul_of_nonneg_right hcong.hα.le hb.le,
      mul_div_assoc hcong.α (hcong.β + 1) hcong.β]
  have hHJB := HJB_le_of_BanachVI hmon hcong hVmeas hV ε w hVI hmnn hDuWeak
  apply HJB_eq_pos_of_complement_truncationVI hmon hcong hm hu hV hDu hmnn hHJB
  intro k hk δ hδ
  have hν := complementDensity_memLp (k := k) hmon hcong hm hu hV hDu
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong (-k)
    (fun _ => 0) (⇑w.2.1) V (fun i => ⇑(w.2.2 i))
  have hνnn := complementDensity_nonneg hmnn hne
  have hQ := complementDensity_quotient_memLp hmon hcong hk.le hm hu hV hDu hmnn hHJB
  exact perdelta_vi_integral_le_of_density hmon hcong hν hQ hνnn hVmeas hV
    rfl rfl hVI rfl rfl (fun _ => rfl) hDuWeak hδ

end StationaryMFG.Theorems.Congestion.Paper
