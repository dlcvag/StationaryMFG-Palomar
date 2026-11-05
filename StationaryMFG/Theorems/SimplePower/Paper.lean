module

public import StationaryMFG.Theorems.SimplePower.CoreExistence
public import StationaryMFG.Hamiltonian.PaperPowerGrowth
public import StationaryMFG.Hamiltonian.FluxExtension
public import StationaryMFG.Solutions.PaperStrongTransport

@[expose] public section

/-!
# Theorem 1 from the paper's hypotheses

The input regularity concerns only positive masses and certifies the genuine
momentum gradient. The proof constructs measurable representatives and a finite
boundary extension, derives the auxiliary growth estimates, applies the existing
existence machinery, and transports every conclusion to the original data.
No boundary, FTC, convexity, or derivative-measurability premise is supplied.
-/

namespace StationaryMFG.Theorems.SimplePower

open MeasureTheory StationaryMFG.Periodic StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- Paper Theorem `thm:main-simple.power.growth`, using only (H1), (A1),
(A2), and the potential's prescribed integrability. -/
theorem thm_main_simplePowerGrowth_faithful
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : Hamiltonian.Paper.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.Paper.HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
      (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Solutions.PaperStrong.IsStrongSolution V H (JsimplePositiveExt DpH) Du m u
        ∧ Periodic.MemLpPer (ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) m
        ∧ Periodic.MemSobolevPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) u
        ∧ (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i))
        ∧ (∀ i, Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) (Du i)) := by
  have hboundary := hpow.finiteExtension_boundary hmon
  obtain ⟨m, u, Du, hsol, hmLp, huSob, hm, hDuWeak, hDuLp⟩ :=
    thm_simplePowerGrowth_core_finiteBoundary V
      (Hamiltonian.Paper.finiteExtension H) (Hamiltonian.Paper.canonicalGradient H)
      hmon.finiteExtension_monotone hpow.toCore hV hboundary.hHat0 hboundary.hAgree
  refine ⟨m, u, Du, hsol.congr_representatives ?_ ?_, hmLp, huSob, hm, hDuWeak, hDuLp⟩
  · exact Filter.Eventually.of_forall fun x p t ht =>
      Hamiltonian.Paper.finiteExtension_of_pos H x p ht
  · filter_upwards [hm, hpow.toRegularityH.canonicalGradient_eq] with x hmx hx
    rcases eq_or_lt_of_le hmx with hz | hp
    · rw [← hz]
      simp [JsimplePositiveExt]
    · simp only [JsimpleExt, JsimplePositiveExt, if_pos hp, hx _ _ hp]

end StationaryMFG.Theorems.SimplePower
