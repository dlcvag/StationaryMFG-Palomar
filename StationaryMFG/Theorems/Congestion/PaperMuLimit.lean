module

public import StationaryMFG.Theorems.Congestion.PaperMuBoundary
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Dominated convergence at the positive auxiliary density

Only the Hamiltonian values at the selected auxiliary argument need finite
boundary limits. This limit passage permits infinite boundary values at other
momenta and makes no zero-flux assumption.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

theorem positiveAux_integral_tendsto
    (hcong : CongestionGrowthCore H DpH J)
    (p : (Fin d → ℝ) → (Fin d → ℝ)) (m u V μ : (Fin d → ℝ) → ℝ) (k : ℝ)
    (hp : AEMeasurable p (volume.restrict (UnitCube d)))
    (hm : AEMeasurable m (volume.restrict (UnitCube d)))
    (hu : AEMeasurable u (volume.restrict (UnitCube d)))
    (hV : AEMeasurable V (volume.restrict (UnitCube d)))
    (hμ : AEMeasurable μ (volume.restrict (UnitCube d)))
    (hμeq : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      μ x = positiveAux (H x (p x)) (m x) (k - u x + V x))
    (hne : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (p x)) (m x) (k - u x + V x)).Nonempty)
    (hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (p x)) (Ioi (0 : ℝ)))
    (hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (p x)) (Ioi (0 : ℝ)))
    (hdom : Integrable (fun x =>
      (|u x| + |V x| + |k - u x + V x| + hcong.C * ((μ x + 1) ^ hcong.β + 1)) *
        (μ x + 1 + |m x|)) (volume.restrict (UnitCube d))) :
    Tendsto (fun n => ∫ x in UnitCube d,
      (u x + H x (p x) (max (μ x) (boundaryMass n)) - V x) *
        (max (μ x) (boundaryMass n) - m x)) atTop
      (𝓝 (∫ x in UnitCube d,
        (u x + finiteExtension H x (p x) (μ x) - V x) * (μ x - m x))) := by
  have hδlim : Tendsto boundaryMass atTop (𝓝 (0 : ℝ)) :=
    boundaryMass_tendsto.mono_right nhdsWithin_le_nhds
  have hδle (n : ℕ) : boundaryMass n ≤ 1 := by
    unfold boundaryMass
    apply (div_le_one (by positivity)).2
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  apply tendsto_integral_of_dominated_convergence _ ?_ hdom ?_ ?_
  · intro n
    have hρ := hμ.max (aemeasurable_const (b := boundaryMass n))
    have hH := hcong.measurable_H.comp_aemeasurable
      (aemeasurable_id.prodMk (hp.prodMk hρ))
    exact (((hu.add hH).sub hV).mul (hρ.sub hm)).aestronglyMeasurable
  · intro n
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
  · filter_upwards [hμeq, hne, hcont, hanti] with x he hn hc ha
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

end StationaryMFG.Theorems.Congestion.Paper
