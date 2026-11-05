module

public import StationaryMFG.Theorems.Congestion.PaperTestPair
public import StationaryMFG.Theorems.Congestion.PaperHJB
public import StationaryMFG.Theorems.Congestion.PaperMuIntegrability
public import StationaryMFG.Theorems.Congestion.PaperMuLimit

@[expose] public section

/-!
# The paper's HJB inequality from the periodic variational inequality

All tests have strictly positive density. The finite boundary value at the
auxiliary infimum is derived locally, so the conclusion permits Hamiltonians
whose boundary value is infinite at other momenta.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Solutions.MFG

variable {d : ℕ}

/-- The HJB inequality from the positive auxiliary tests, with their
variational inequalities supplied by either the Banach or periodic formulation. -/
theorem HJB_le_of_positiveAux_truncationVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
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
    (hper : ∀ k : ℝ, 0 < k → ∀ δ : ℝ, 0 < δ →
      (∫ x in UnitCube d,
        (u x + H x (fun i => Du i x)
          (max (positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)) δ) - V x) *
          (max (positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)) δ - m x)) ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ) := by
  have hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx _
  have hp : AEMeasurable (fun x i => Du i x) (volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
  apply HJB_le_of_positive_tolerances
  intro k hk
  let μ := fun x => positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong k m u V Du
  have hμ : MemLpPer (ENNReal.ofReal (hcong.β + 1)) μ :=
    positiveAux_memLp hmon hcong hm hu hV hDu
  have hμnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    hne.mono fun _ hx => positiveAux_nonneg hx
  have hlim := positiveAux_integral_tendsto hcong (fun x i => Du i x) m u V μ k hp
    hm.aestronglyMeasurable.aemeasurable hu.aestronglyMeasurable.aemeasurable
    hV.aestronglyMeasurable.aemeasurable hμ.aestronglyMeasurable.aemeasurable
    (Eventually.of_forall fun _ => rfl) hne hcont hanti
    (auxiliary_dominator_integrable hcong.hβ hcong.C k hm hu hV hμ hμnn)
  have hint := le_of_tendsto hlim (Eventually.of_forall fun n => hper k hk (boundaryMass n) (boundaryMass_pos n))
  have hdiff : Integrable (fun x => μ x - m x) (volume.restrict (UnitCube d)) := by
    apply memLp_one_iff_integrable.mp
    have hd : MemLpPer (ENNReal.ofReal (hcong.β + 1)) (fun x => μ x - m x) :=
      hμ.toMemLp.sub hm.toMemLp
    apply MemLpPer.toMemLp
    apply hd.mono_exponent_finite _ ENNReal.ofReal_ne_top
    exact ENNReal.one_le_ofReal.mpr (by linarith [hcong.hβ])
  exact HJB_le_at_k_of_positiveAux_integral hk hcont hanti hne hmnn hdiff hint


theorem HJB_le_of_abstractPeriodicVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
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
    (habs : ∀ T : CongestionLimitVITestPair (d := d)
      (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      hcong.α hcong.β hcong.τ,
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
        T.Dυ T.μ T.υ (fun i x => T.Dυ i x - Du i x) (T.μ - m) (T.υ - u)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ) := by
  have hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx _
  have hp : AEMeasurable (fun x i => Du i x) (volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
  apply HJB_le_of_positive_tolerances
  intro k hk
  let μ := fun x => positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong k m u V Du
  have hμ : MemLpPer (ENNReal.ofReal (hcong.β + 1)) μ :=
    positiveAux_memLp hmon hcong hm hu hV hDu
  have hμnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    hne.mono fun _ hx => positiveAux_nonneg hx
  have hμPer : IsPeriodic μ := by
    apply positiveAux_periodic _ hmPer (((IsPeriodic.const k).sub huPer).add hVPer)
    intro t ht κ x
    have hpEq : (fun i => Du i (x + fun i => (κ i : ℝ))) = (fun i => Du i x) :=
      funext fun i => hDuPer i κ x
    dsimp only
    rw [hpEq]
    exact hHPer _ t ht κ x
  have hQ := positiveAux_quotient_memLp (k := k) hmon hcong hm hu hV hDu
  have hαt : 0 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    exact mul_nonneg (le_of_lt (lt_trans zero_lt_one hcong.hα))
      (by have := div_nonneg hcong.hτ.1 hcong.hβ.le; linarith)
  let T (n : ℕ) := positiveTruncTestPair (boundaryMass_pos n) hcong.hτ.1 hαt
    hμPer huPer hDuPer hμ hμnn huSob hDu hDuWeak hQ
  have hper (n : ℕ) : (∫ x in UnitCube d,
      (u x + H x (fun i => Du i x) (max (μ x) (boundaryMass n)) - V x) *
        (max (μ x) (boundaryMass n) - m x)) ≤ 0 :=
    congestionLimitVI_integral_le_of_abstract_at_periodicDensity habs (T n) rfl rfl
  have hlim := positiveAux_integral_tendsto hcong (fun x i => Du i x) m u V μ k hp
    hm.aestronglyMeasurable.aemeasurable hu.aestronglyMeasurable.aemeasurable
    hV.aestronglyMeasurable.aemeasurable hμ.aestronglyMeasurable.aemeasurable
    (Eventually.of_forall fun _ => rfl) hne hcont hanti
    (auxiliary_dominator_integrable hcong.hβ hcong.C k hm hu hV hμ hμnn)
  have hint := le_of_tendsto hlim (Eventually.of_forall hper)
  have hdiff : Integrable (fun x => μ x - m x) (volume.restrict (UnitCube d)) := by
    apply memLp_one_iff_integrable.mp
    have hd : MemLpPer (ENNReal.ofReal (hcong.β + 1)) (fun x => μ x - m x) :=
      hμ.toMemLp.sub hm.toMemLp
    apply MemLpPer.toMemLp
    apply hd.mono_exponent_finite _ ENNReal.ofReal_ne_top
    exact ENNReal.one_le_ofReal.mpr (by linarith [hcong.hβ])
  exact HJB_le_at_k_of_positiveAux_integral hk hcont hanti hne hmnn hdiff hint

end StationaryMFG.Theorems.Congestion.Paper
