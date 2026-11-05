module

public import StationaryMFG.Theorems.Congestion.PaperMuAux
public import StationaryMFG.Theorems.Congestion.PaperCore

@[expose] public section

/-!
# Finite boundary values at the positive auxiliary density

The paper needs finite Hamiltonian values at its chosen auxiliary density,
not at every momentum. These lemmas derive that local property, the HJB
upper bound, and convergence of positive truncations to the canonical
real representative. Infinite boundary values elsewhere are permitted.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {x p : Fin d → ℝ} {m b : ℝ}

/-- The extended-real Hamiltonian is bounded at the auxiliary density;
this simultaneously excludes an infinite value at its zero endpoint. -/
theorem Hext_positiveAux_le
    (hne : (positiveAuxSet (H x p) m b).Nonempty)
    (hcont : ContinuousOn (H x p) (Ioi (0 : ℝ)))
    (hanti : AntitoneOn (H x p) (Ioi (0 : ℝ))) :
    Hext H x p (positiveAux (H x p) m b) ≤ (b : WithTop ℝ) := by
  rcases eq_or_lt_of_le (positiveAux_nonneg hne) with hz | hp
  · obtain ⟨L, hLb, hL⟩ := finiteBoundary_of_positiveAux_zero hne hcont hanti hz.symm
    rw [← hz, Hext_zero_eq_of_tendsto hL]
    exact WithTop.coe_le_coe.mpr hLb
  · simpa only [Hext, if_pos hp] using
      (WithTop.coe_le_coe.mpr (positiveAux_mem_of_pos hne hcont hanti hp).2.2)

/-- The canonical real representative agrees with the extended value at
this auxiliary argument, including when the density is zero. -/
theorem Hext_positiveAux_eq_finiteExtension
    (hne : (positiveAuxSet (H x p) m b).Nonempty)
    (hcont : ContinuousOn (H x p) (Ioi (0 : ℝ)))
    (hanti : AntitoneOn (H x p) (Ioi (0 : ℝ))) :
    Hext H x p (positiveAux (H x p) m b) =
      (finiteExtension H x p (positiveAux (H x p) m b) : WithTop ℝ) := by
  rcases eq_or_lt_of_le (positiveAux_nonneg hne) with hz | hp
  · obtain ⟨L, _, hL⟩ := finiteBoundary_of_positiveAux_zero hne hcont hanti hz.symm
    rw [← hz, Hext_zero_eq_of_tendsto hL, finiteExtension_zero,
      boundaryTrace_eq_of_tendsto hL]
  · simp only [Hext, if_pos hp, finiteExtension_of_pos H x p hp]

theorem finiteExtension_positiveAux_le
    (hne : (positiveAuxSet (H x p) m b).Nonempty)
    (hcont : ContinuousOn (H x p) (Ioi (0 : ℝ)))
    (hanti : AntitoneOn (H x p) (Ioi (0 : ℝ))) :
    finiteExtension H x p (positiveAux (H x p) m b) ≤ b := by
  have h := Hext_positiveAux_le hne hcont hanti
  rw [Hext_positiveAux_eq_finiteExtension hne hcont hanti] at h
  exact WithTop.coe_le_coe.mp h

/-- Positive truncations converge to the finite auxiliary value. No
boundary information at other momenta is used. -/
theorem positiveAux_max_H_tendsto
    (hne : (positiveAuxSet (H x p) m b).Nonempty)
    (hcont : ContinuousOn (H x p) (Ioi (0 : ℝ)))
    (hanti : AntitoneOn (H x p) (Ioi (0 : ℝ)))
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ}
    (hδ : Tendsto δ l (𝓝 0)) (hδpos : ∀ᶠ i in l, 0 < δ i) :
    Tendsto (fun i => H x p (max (positiveAux (H x p) m b) (δ i))) l
      (𝓝 (finiteExtension H x p (positiveAux (H x p) m b))) := by
  have hμ := positiveAux_nonneg hne
  have hmax : Tendsto (fun i => max (positiveAux (H x p) m b) (δ i)) l
      (𝓝 (positiveAux (H x p) m b)) := by
    have ht : Tendsto (fun i => max (positiveAux (H x p) m b) (δ i)) l
        (𝓝 (max (positiveAux (H x p) m b) 0)) := tendsto_const_nhds.max hδ
    simpa only [max_eq_left hμ] using ht
  rcases eq_or_lt_of_le hμ with hz | hp
  · obtain ⟨L, _, hL⟩ := finiteBoundary_of_positiveAux_zero hne hcont hanti hz.symm
    rw [← hz, finiteExtension_zero, boundaryTrace_eq_of_tendsto hL]
    apply hL.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa only [← hz] using hmax,
      hδpos.mono fun i hi => hi.trans_le (le_max_right _ _)⟩
  · rw [finiteExtension_of_pos H x p hp]
    exact (hcont.continuousAt (isOpen_Ioi.mem_nhds hp)).tendsto.comp hmax

/-- Congestion's coercive lower bound passes to any finite boundary
limit at one momentum; no global finite-boundary hypothesis is needed. -/
theorem congestion_lower_of_finite_boundary
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) →
      (1 / h.C) * (1 / ((0 : ℝ) ^ h.τ + 1)) *
        ‖p‖ ^ (h.α * (1 + h.τ / h.β)) - h.C ≤ L := by
  filter_upwards [h.lower] with x hx p L hL
  have hden : (0 : ℝ) ^ h.τ + 1 ≠ 0 := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) h.τ
    positivity
  have hτ := (Real.continuous_rpow_const h.hτ.1).continuousAt (x := (0 : ℝ))
  have hβ := (Real.continuous_rpow_const h.hβ.le).continuousAt (x := (0 : ℝ))
  have hR : ContinuousAt (fun t : ℝ =>
      (1 / h.C) * (1 / (t ^ h.τ + 1)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β))
        - h.C * (t ^ h.β + 1)) 0 :=
    ((continuousAt_const.mul (continuousAt_const.div
      (hτ.add continuousAt_const) hden)).mul continuousAt_const).sub
      (continuousAt_const.mul (hβ.add continuousAt_const))
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (1 / h.C) * (1 / (t ^ h.τ + 1)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β))
        - h.C * (t ^ h.β + 1) ≤ H x p t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hx p t ht
  have hr := le_of_tendsto_of_tendsto (hR.tendsto.mono_left nhdsWithin_le_nhds) hL hbound
  simpa only [Real.zero_rpow h.hβ.ne', zero_add, mul_one] using hr

/-- The full coercive lower bound holds at the auxiliary density. Its
zero case uses the local finite limit already supplied by the infimum. -/
theorem finiteExtension_positiveAux_lower
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m b,
      (positiveAuxSet (H x p) m b).Nonempty →
      ContinuousOn (H x p) (Ioi (0 : ℝ)) →
      AntitoneOn (H x p) (Ioi (0 : ℝ)) →
      (1 / h.C) * (1 / (positiveAux (H x p) m b ^ h.τ + 1)) *
        ‖p‖ ^ (h.α * (1 + h.τ / h.β)) -
          h.C * (positiveAux (H x p) m b ^ h.β + 1) ≤
        finiteExtension H x p (positiveAux (H x p) m b) := by
  filter_upwards [h.lower, congestion_lower_of_finite_boundary h] with x hx hb
  intro p m b hne hcont hanti
  rcases eq_or_lt_of_le (positiveAux_nonneg hne) with hz | hp
  · obtain ⟨L, _, hL⟩ := finiteBoundary_of_positiveAux_zero hne hcont hanti hz.symm
    rw [← hz, finiteExtension_zero, boundaryTrace_eq_of_tendsto hL]
    simpa only [Real.zero_rpow h.hβ.ne', zero_add, mul_one] using hb p L hL
  · rw [finiteExtension_of_pos H x p hp]
    exact hx p _ hp

/-- A uniform absolute-value envelope for all small positive truncations.
This is the domination needed for the auxiliary-density HJB limit. -/
theorem positiveAux_max_H_abs_bound
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m b,
      (positiveAuxSet (H x p) m b).Nonempty →
      ContinuousOn (H x p) (Ioi (0 : ℝ)) →
      AntitoneOn (H x p) (Ioi (0 : ℝ)) →
      ∀ δ, 0 < δ → δ ≤ 1 →
        |H x p (max (positiveAux (H x p) m b) δ)| ≤
          |b| + h.C * ((positiveAux (H x p) m b + 1) ^ h.β + 1) := by
  filter_upwards [h.lower] with x hx
  intro p m b hne hcont hanti δ hδ hδ1
  have hμ := positiveAux_nonneg hne
  have hρ : 0 < max (positiveAux (H x p) m b) δ := hδ.trans_le (le_max_right _ _)
  have hρle : max (positiveAux (H x p) m b) δ ≤ positiveAux (H x p) m b + 1 :=
    max_le (by linarith) (by linarith)
  have hpw := Real.rpow_le_rpow hρ.le hρle h.hβ.le
  have hpos : 0 ≤ (1 / h.C) * (1 / (max (positiveAux (H x p) m b) δ ^ h.τ + 1)) *
      ‖p‖ ^ (h.α * (1 + h.τ / h.β)) := by
    have hC := h.hC
    have ht := Real.rpow_nonneg hρ.le h.τ
    positivity
  have hlow := hx p _ hρ
  have hupper := positiveAux_max_bound hne hcont hanti hδ
  have hmult := mul_le_mul_of_nonneg_left hpw h.hC.le
  have hbabs := le_abs_self b
  have hbn := abs_nonneg b
  have hdom : 0 ≤ h.C * ((positiveAux (H x p) m b + 1) ^ h.β + 1) := by
    have hC := h.hC
    have ht := Real.rpow_nonneg (by linarith : 0 ≤ positiveAux (H x p) m b + 1) h.β
    positivity
  apply abs_le.mpr
  constructor <;> nlinarith

end StationaryMFG.Theorems.Congestion.Paper
