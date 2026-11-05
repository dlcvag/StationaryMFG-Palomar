module

public import StationaryMFG.Theorems.Congestion.PaperMuBoundary

@[expose] public section

/-!
# Hamilton--Jacobi inequality from the positive auxiliary density

This is the paper's Step 1 after the positive-truncation variational
inequality has passed to its limit. Finite boundary values are obtained
from the auxiliary construction at the solution arguments only.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}

/-- The nonnegative correction vanishes because its positive-tolerance
multiple has nonpositive integral. The resulting HJB bound uses Hext. -/
theorem HJB_le_at_k_of_positiveAux_integral
    {p : (Fin d → ℝ) → (Fin d → ℝ)} {m u V : (Fin d → ℝ) → ℝ}
    {k : ℝ} (hk : 0 < k)
    (hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (p x)) (Ioi (0 : ℝ)))
    (hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (p x)) (Ioi (0 : ℝ)))
    (hne : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (p x)) (m x) (k - u x + V x)).Nonempty)
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hdiff : Integrable (fun x =>
      positiveAux (H x (p x)) (m x) (k - u x + V x) - m x)
      (volume.restrict (UnitCube d)))
    (hint : (∫ x in UnitCube d,
      (u x + finiteExtension H x (p x)
        (positiveAux (H x (p x)) (m x) (k - u x + V x)) - V x) *
      (positiveAux (H x (p x)) (m x) (k - u x + V x) - m x)) ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (p x) (m x) ≤ ((k - u x + V x : ℝ) : WithTop ℝ) := by
  let μ : (Fin d → ℝ) → ℝ := fun x =>
    positiveAux (H x (p x)) (m x) (k - u x + V x)
  have hprod : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (u x + finiteExtension H x (p x) (μ x) - V x) * (μ x - m x) =
        k * (μ x - m x) := by
    filter_upwards [hne, hcont, hanti, hm] with x hx hc ha hmx
    have hz := positiveAux_product_identity hx hc ha hmx
      (fun t ht => finiteExtension_of_pos H x (p x) ht)
    change (μ x - m x) *
      (finiteExtension H x (p x) (μ x) - (k - u x + V x)) = 0 at hz
    nlinarith
  have hki : k * (∫ x in UnitCube d, μ x - m x) ≤ 0 := by
    rw [← integral_const_mul]
    calc (∫ x in UnitCube d, k * (μ x - m x)) =
        ∫ x in UnitCube d,
          (u x + finiteExtension H x (p x) (μ x) - V x) * (μ x - m x) :=
      integral_congr_ae (hprod.mono fun _ hx => hx.symm)
      _ ≤ 0 := hint
  have hdiffnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x - m x := by
    filter_upwards [hne] with x hx
    exact sub_nonneg.mpr (le_positiveAux hx)
  have hzero : (∫ x in UnitCube d, μ x - m x) = 0 := by
    have hnonneg := integral_nonneg_of_ae hdiffnn
    nlinarith
  have heq : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x = m x := by
    have hh := (integral_eq_zero_iff_of_nonneg_ae hdiffnn hdiff).mp hzero
    filter_upwards [hh] with x hx
    exact sub_eq_zero.mp hx
  filter_upwards [heq, hne, hcont, hanti] with x hx hn hc ha
  have hb := Hext_positiveAux_le hn hc ha
  change Hext H x (p x) (μ x) ≤ ((k - u x + V x : ℝ) : WithTop ℝ) at hb
  rwa [hx] at hb

/-- Countably many positive tolerances tending to zero yield the paper's
extended-real HJB inequality. This also rules out Hext=∞ at the solution. -/
theorem HJB_le_of_positive_tolerances
    {p : (Fin d → ℝ) → (Fin d → ℝ)} {m u V : (Fin d → ℝ) → ℝ}
    (h : ∀ k : ℝ, 0 < k → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (p x) (m x) ≤ ((k - u x + V x : ℝ) : WithTop ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (p x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ) := by
  have hall := (ae_all_iff.mpr fun n => h (boundaryMass n) (boundaryMass_pos n))
  filter_upwards [hall] with x hx
  have ht : Tendsto (fun n => boundaryMass n - u x + V x) atTop (𝓝 (V x - u x)) := by
    simpa only [zero_sub, neg_add_eq_sub] using
      ((tendsto_nhds_of_tendsto_nhdsWithin boundaryMass_tendsto).sub_const (u x)).add_const (V x)
  have hcoe := WithTop.continuous_coe.continuousAt.tendsto.comp ht
  exact ge_of_tendsto hcoe (Eventually.of_forall hx)

end StationaryMFG.Theorems.Congestion.Paper
