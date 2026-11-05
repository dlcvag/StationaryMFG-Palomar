module

public import StationaryMFG.Theorems.Congestion.PaperMuLimit
public import StationaryMFG.Theorems.Congestion.PaperSolutionBoundary

@[expose] public section

/-! # Dominated convergence for any density satisfying the extended HJB bound -/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- A finite extended HJB upper bound gives the exact boundary control
needed for both integrability and the positive-truncation limit. -/
theorem boundedDensity_integral_tendsto
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    (p : (Fin d → ℝ) → (Fin d → ℝ)) (m u V μ : (Fin d → ℝ) → ℝ)
    (hp : AEMeasurable p (volume.restrict (UnitCube d)))
    (hm : AEMeasurable m (volume.restrict (UnitCube d)))
    (hu : AEMeasurable u (volume.restrict (UnitCube d)))
    (hV : AEMeasurable V (volume.restrict (UnitCube d)))
    (hμ : AEMeasurable μ (volume.restrict (UnitCube d)))
    (hμnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hH : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (p x) (μ x) ≤ ((V x - u x : ℝ) : WithTop ℝ))
    (hdom : Integrable (fun x =>
      (|u x| + |V x| + |0 - u x + V x| + hcong.C * ((μ x + 1) ^ hcong.β + 1)) *
        (μ x + 1 + |m x|)) (volume.restrict (UnitCube d))) :
    Integrable (fun x => (u x + finiteExtension H x (p x) (μ x) - V x) * (μ x - m x))
      (volume.restrict (UnitCube d)) ∧
    Tendsto (fun n => ∫ x in UnitCube d,
      (u x + H x (p x) (max (μ x) (boundaryMass n)) - V x) *
        (max (μ x) (boundaryMass n) - m x)) atTop
      (𝓝 (∫ x in UnitCube d,
        (u x + finiteExtension H x (p x) (μ x) - V x) * (μ x - m x))) := by
  let k : ℝ := 0
  have hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (p x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (p x)) (Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx _
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong k μ u V
    (fun i x => p x i)
  have hμeq : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      μ x = positiveAux (H x (p x)) (μ x) (k - u x + V x) := by
    filter_upwards [hne, hcont, hanti, hμnn, hH] with x hn hc ha hm hH
    exact (positiveAux_eq_of_Hext_le hn hc ha hm (by simpa [k, sub_eq_add_neg, add_comm] using hH)).symm
  have hδlim : Tendsto boundaryMass atTop (𝓝 (0 : ℝ)) :=
    boundaryMass_tendsto.mono_right nhdsWithin_le_nhds
  have hδle (n : ℕ) : boundaryMass n ≤ 1 := by
    unfold boundaryMass
    apply (div_le_one (by positivity)).2
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  let F := fun n x => (u x + H x (p x) (max (μ x) (boundaryMass n)) - V x) *
    (max (μ x) (boundaryMass n) - m x)
  let f := fun x => (u x + finiteExtension H x (p x) (μ x) - V x) * (μ x - m x)
  let G := fun x =>
    (|u x| + |V x| + |k - u x + V x| + hcong.C * ((μ x + 1) ^ hcong.β + 1)) *
      (μ x + 1 + |m x|)
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (UnitCube d)) := by
    intro n
    dsimp only [F]
    have hρ := hμ.max (aemeasurable_const (b := boundaryMass n))
    have hH := hcong.measurable_H.comp_aemeasurable
      (aemeasurable_id.prodMk (hp.prodMk hρ))
    exact (((hu.add hH).sub hV).mul (hρ.sub hm)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖F n x‖ ≤ G x := by
    intro n
    dsimp only [F, G]
    filter_upwards [hμeq, hne, hcont, hanti, positiveAux_max_H_abs_bound hcong]
      with x he hn hc ha hb
    have hμnn : 0 ≤ μ x := he ▸ positiveAux_nonneg hn
    have hρpos : 0 < max (μ x) (boundaryMass n) :=
      (boundaryMass_pos n).trans_le (le_max_right _ _)
    have hρle : max (μ x) (boundaryMass n) ≤ μ x + 1 :=
      max_le (by linarith) (by linarith [hδle n])
    have hH : |H x (p x) (max (μ x) (boundaryMass n))| ≤
        |k - u x + V x| + hcong.C * ((μ x + 1) ^ hcong.β + 1) := by
      rw [he]
      exact hb _ _ _ hn hc ha _ (boundaryMass_pos n) (hδle n)
    have hfirst : |u x + H x (p x) (max (μ x) (boundaryMass n)) - V x| ≤
        |u x| + |V x| + |k - u x + V x| +
          hcong.C * ((μ x + 1) ^ hcong.β + 1) := by
      calc
        _ ≤ |u x + H x (p x) (max (μ x) (boundaryMass n))| + |V x| :=
          abs_sub _ _
        _ ≤ (|u x| + |H x (p x) (max (μ x) (boundaryMass n))|) + |V x| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ ≤ _ := by linarith
    have hsecond : |max (μ x) (boundaryMass n) - m x| ≤ μ x + 1 + |m x| := by
      calc
        _ ≤ |max (μ x) (boundaryMass n)| + |m x| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_pos hρpos]; linarith
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hfirst hsecond (abs_nonneg _) ((abs_nonneg _).trans hfirst)
  have hlim : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    dsimp only [F, f]
    filter_upwards [hμeq, hne, hcont, hanti] with x he hn hc ha
    have hμnn : 0 ≤ μ x := he ▸ positiveAux_nonneg hn
    have hH : Tendsto (fun n => H x (p x) (max (μ x) (boundaryMass n))) atTop
        (𝓝 (finiteExtension H x (p x) (μ x))) := by
      rw [he]
      exact positiveAux_max_H_tendsto hn hc ha hδlim
        (Eventually.of_forall boundaryMass_pos)
    have hρ : Tendsto (fun n => max (μ x) (boundaryMass n)) atTop (𝓝 (μ x)) := by
      simpa only [max_eq_left hμnn] using
        (tendsto_const_nhds (x := μ x)).max hδlim
    exact ((tendsto_const_nhds.add hH).sub tendsto_const_nhds).mul
      (hρ.sub tendsto_const_nhds)
  have hfmeas := aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  have hfb : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖f x‖ ≤ G x := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with x hx hb
    exact le_of_tendsto hx.norm (Eventually.of_forall hb)
  exact ⟨hdom.mono' hfmeas hfb,
    tendsto_integral_of_dominated_convergence G hmeas hdom hbound hlim⟩

end StationaryMFG.Theorems.Congestion.Paper
