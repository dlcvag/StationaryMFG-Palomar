module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.SimplePower.BanachBridge
public import StationaryMFG.Hamiltonian.PowerGrowthCore
public import StationaryMFG.Solutions.PaperStrong

@[expose] public section

/-!
# Simple-power existence from the three original growth bounds

This migration corollary of paper Theorem `thm:main-simple.power.growth`
removes the two derived growth estimates from the caller's assumptions,
using `HypothesisPowerGrowthCore.toHypothesisPowerGrowth`, and expresses the
solution through the extended-real HJB predicate `PaperStrong.IsStrongSolution`.
The exponents and all six conclusion clauses of the existing theorem are
preserved.

The existing regularity representation, the radial FTC premise carried by
`HypothesisMonotone`, and the zero-mass limit existence and finite agreement
premises remain. This is an intermediate finite-boundary theorem, not a proof
of the corrected standalone challenge.
-/

namespace StationaryMFG.Theorems.SimplePower

open MeasureTheory StationaryMFG.Periodic StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- Simple-power existence from the three paper growth inequalities, retaining
the existing regularity/FTC assumptions and finite boundary agreement.

The two auxiliary estimates in `HypothesisPowerGrowth` are derived internally.
The returned solution uses the extended-real HJB formulation, with density and
Sobolev exponents determined by the original core bundle. -/
theorem thm_simplePowerGrowth_core_finiteBoundary
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hcore : HypothesisPowerGrowthCore H DpH)
    (hV : Periodic.MemLpPer
      (ENNReal.ofReal (Hamiltonian.betaBar' hcore.β)) V)
    (hHat0 : HypothesisHat0 (d := d) H)
    (hAgree : H_zero_eq_Hext (d := d) H) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Solutions.PaperStrong.IsStrongSolution V H (Hamiltonian.JsimpleExt DpH) Du m u
        ∧ Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar hcore.β)) m
        ∧ Periodic.MemSobolevPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hcore.α hcore.β)) u
        ∧ (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hcore.α hcore.β)) (Du i)) := by
  obtain ⟨m, u, Du, hsol, hmLp, huSob, hm, hDuWeak, hDuLp⟩ :=
    thm_main_simplePowerGrowth_paper V H DpH hmon
      (hcore.toHypothesisPowerGrowth hmon) hV hHat0 hAgree
  exact ⟨m, u, Du, (Solutions.PaperStrong.strong_iff_of_agree hAgree hm).2 hsol,
    hmLp, huSob, hm, hDuWeak, hDuLp⟩

end StationaryMFG.Theorems.SimplePower
