module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.InfimalConvolution.Main
public import StationaryMFG.Theorems.InfimalConvolution.PaperRepresentative

@[expose] public section

/-!
# Theorem 3 from the paper's positive-mass assumptions

The input bundles contain the literal regularity, monotonicity, and weak
growth assumptions. Measurable periodic representatives, the FTC identity,
and convexity are constructed internally. Only the regularized Hamiltonians
receive finite boundary extensions; no boundary condition is imposed on the
original Hamiltonian. Positive test masses allow the resulting weak solution
to be transported back to the original data.
-/

namespace StationaryMFG.Theorems.InfimalConvolution

open MeasureTheory StationaryMFG.Periodic StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- Paper Theorem `thm:main-weak.power.growth`, with no premise at zero mass. -/
theorem thm_main_weak_power_growth_faithful
    [Fact (0 < d)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (hmon : Hamiltonian.Paper.HypothesisMonotone H DpH)
    (hweak : Hamiltonian.Paper.HypothesisWeakGrowth H DpH)
    (hV : MemLpPer (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Solutions.Weak.IsWeakSolution V H DpH Du m u
        ∧ MemLpPer (ENNReal.ofReal (hweak.β + 1)) m
        ∧ MemSobolevPer (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) u
        ∧ (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer i u (Du i))
        ∧ (∀ i, MemLpPer
            (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (Du i)) := by
  have hcanonical : Hamiltonian.Paper.HypothesisMonotone
      (Hamiltonian.Paper.finiteExtension H) (Hamiltonian.Paper.canonicalGradient H) :=
    { toRegularityH := hmon.toRegularityH.finiteExtension_paper_regularity
      monotone := hmon.finiteExtension_monotone.monotone }
  have hmeas : HypothesisDpHMeasurable
      (Hamiltonian.Paper.finiteExtension H) (Hamiltonian.Paper.canonicalGradient H) :=
    ⟨Hamiltonian.Paper.finiteExtension_measurable hmon.measurable_H,
      Hamiltonian.Paper.canonicalGradient_measurable hmon.measurable_H⟩
  obtain ⟨m, u, Du, hsol, hmLp, huSob, hm, hDuWeak, hDuLp⟩ :=
    thm_main_weak_power_growth_no_boundary V hmon.finiteExtension_monotone
      hweak.toCanonical hcanonical.toHypothesisHpDifferentiable hmeas hV
  exact ⟨m, u, Du, Hamiltonian.Paper.weakSolution_of_canonical hmon.toRegularityH hsol,
    hmLp, huSob, hm, hDuWeak, hDuLp⟩

end StationaryMFG.Theorems.InfimalConvolution
