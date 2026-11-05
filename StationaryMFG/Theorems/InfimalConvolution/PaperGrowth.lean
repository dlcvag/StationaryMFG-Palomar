module

public import StationaryMFG.Hamiltonian.PaperRegularity

@[expose] public section

/-!
# The literal weak-growth hypothesis

This is assumption (A4) in `Source/FGU-monotone_revised.tex`. It adds only
its three displayed estimates to positive-mass regularity. There is no
boundary-value, convexity, gradient-measurability, or FTC premise.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory StationaryMFG.Periodic

variable {d : ℕ}

/-- Assumption (A4), with its literal zero-momentum upper bound, continuous
positive-mass gradient dominator, and coercive lower bound. -/
structure HypothesisWeakGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  f : (Fin d → ℝ) → ℝ → ℝ
  hf_continuous :
    ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => f pm.1 pm.2)
      {pm | 0 < pm.2}
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → ‖DpH x p m‖ ≤ f p m
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

end StationaryMFG.Hamiltonian.Paper
