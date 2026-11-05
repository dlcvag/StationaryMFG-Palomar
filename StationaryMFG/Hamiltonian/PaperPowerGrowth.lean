module

public import StationaryMFG.Hamiltonian.PaperRepresentative
public import StationaryMFG.Hamiltonian.PowerGrowthCore

@[expose] public section

/-!
# The literal simple-power hypothesis and its derived boundary extension

This is paper Assumption `onH.powergrowth` over positive masses. Both the
auxiliary growth estimates and the finite boundary extension are derived,
so neither is part of the input to the paper-facing existence theorem.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Topology Set StationaryMFG.Periodic

variable {d : ℕ}

/-- Exactly the three inequalities of (A2), with the paper regularity. -/
structure HypothesisPowerGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- Supply the old representation internally, preserving all growth data. -/
noncomputable def HypothesisPowerGrowth.toCore
    (h : HypothesisPowerGrowth H DpH) :
    HypothesisPowerGrowthCore (finiteExtension H) (canonicalGradient H) where
  toRegularityH := h.toRegularityH.finiteExtension_regularity
  C := h.C
  α := h.α
  β := h.β
  hC := h.hC
  hα := h.hα
  hβ := h.hβ
  upper := by
    filter_upwards [h.upper] with x hx m hm
    simpa only [finiteExtension_of_pos H x _ hm] using hx m hm
  DpH_upper := by
    filter_upwards [h.DpH_upper, h.toRegularityH.canonicalGradient_eq] with x hx he p m hm
    rw [he p m hm]
    exact hx p m hm
  lower := by
    filter_upwards [h.lower] with x hx p m hm
    simpa only [finiteExtension_of_pos H x _ hm] using hx p m hm

/-- The real boundary limits in T1 follow from the three growth bounds and
monotonicity. No value of the original H at zero appears. -/
theorem HypothesisPowerGrowth.finite_boundary_limits
    (h : HypothesisPowerGrowth H DpH) (hmon : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      ∃ L : ℝ, Tendsto (H x p) (𝓝[>] 0) (𝓝 L) := by
  let hfull := h.toCore.toHypothesisPowerGrowth hmon.finiteExtension_monotone
  filter_upwards [antitone_in_m hmon.finiteExtension_monotone,
    hfull.H_upper_pointwise] with x hanti hupper p
  have hantiH : AntitoneOn (H x p) (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    simpa only [finiteExtension_of_pos H x p ha, finiteExtension_of_pos H x p hb]
      using hanti p ha hb hab
  have hb : BddAbove (H x p '' Ioi (0 : ℝ)) := by
    refine ⟨hfull.C * (‖p‖ ^ hfull.α + 1), ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    have hu := hupper p m hm
    rw [finiteExtension_of_pos H x p hm] at hu
    have hn : 0 ≤ m ^ hfull.β / hfull.C :=
      div_nonneg (Real.rpow_nonneg hm.le _) hfull.hC.le
    linarith
  exact ⟨_, hantiH.tendsto_nhdsGT hb⟩

theorem HypothesisPowerGrowth.finiteExtension_boundary
    (h : HypothesisPowerGrowth H DpH) (hmon : HypothesisMonotone H DpH) :
    HypothesisHZeroExtension (finiteExtension H) :=
  ⟨finiteExtension_hat0 (h.finite_boundary_limits hmon),
    finiteExtension_agree (h.finite_boundary_limits hmon)⟩

end StationaryMFG.Hamiltonian.Paper
