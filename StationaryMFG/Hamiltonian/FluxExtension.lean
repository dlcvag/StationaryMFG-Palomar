module

public import StationaryMFG.Hamiltonian.Assumptions

@[expose] public section

/-!
# General boundary flux from the paper

The paper's hypothesis `(a:mDpHat0)` asks for a continuous extension of
`m D_pH` to the closed half-space. It does not require that extension to
vanish at zero mass. The existing `HypothesismDpHat0` contains that extra
restriction and a measurable-representative premise; the bridges below
record exactly how the two interfaces relate.
-/

namespace StationaryMFG.Hamiltonian

open MeasureTheory StationaryMFG.Periodic
open Filter Topology

variable {d : ℕ}

/-- The simple-power flux using only the prescribed positive-mass data. -/
noncomputable def JsimplePositiveExt
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  if 0 < m then m • DpH x p m else 0

/-- The guarded challenge flux agrees with the old simple-power flux at
every nonnegative density, regardless of supplied values of DpH at zero. -/
theorem JsimplePositiveExt_eq_of_nonneg
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) {m : ℝ} (hm : 0 ≤ m) :
    JsimplePositiveExt DpH x p m = JsimpleExt DpH x p m := by
  rcases eq_or_lt_of_le hm with hz | hp
  · rw [← hz]
    simp [JsimplePositiveExt]
  · simp [JsimplePositiveExt, JsimpleExt, hp]

/-- The literal continuous-flux extension hypothesis, with no restriction
on the value of the flux at zero mass. -/
structure PaperFluxExtension
    (DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  J_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m
  tendsto_at_zero :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      Tendsto (fun m : ℝ => m • DpH x p m)
        (𝓝[>] (0 : ℝ)) (𝓝 (J x p 0))
  continuous_J :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => J x pm.1 pm.2)
        {pm | 0 ≤ pm.2}

/-- Every flux allowed by the existing restricted interface is also
allowed by the paper's general boundary-flux interface. -/
theorem HypothesismDpHat0.toPaperFluxExtension
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesismDpHat0 DpH J) : PaperFluxExtension DpH J :=
  ⟨h.J_of_pos, h.tendsto_at_zero, h.continuous_J⟩

/-- Reconstruct the old interface only when its two additional
conditions have actually been supplied or proved. -/
theorem PaperFluxExtension.toRestricted
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : PaperFluxExtension DpH J)
    (hMeas : Measurable (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
      J xpm.1 xpm.2.1 xpm.2.2))
    (hZero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      J x p 0 = 0) : HypothesismDpHat0 DpH J :=
  ⟨h.J_of_pos, h.tendsto_at_zero, h.continuous_J, hMeas, hZero⟩

end StationaryMFG.Hamiltonian
