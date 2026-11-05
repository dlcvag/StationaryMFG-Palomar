module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.SimplePower.Apriori
public import StationaryMFG.Theorems.InfimalConvolution.InfConv

@[expose] public section

/-!
# `thm:apriori-weak.power.growth` — ε-uniform `L^β̄ × W^{1,γ̄}` apriori bound

This module formalizes Theorem `thm:apriori-weak.power.growth` of
Ferreira–Gomes–Üçer (`Source/FGU-monotone_revised.tex`, lines 1881–1895).

## Paper statement (line 1881)

Under the assumptions of Theorem `thm:main-weak.power.growth`, let
`(m_ε, u_ε) ∈ L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d)` be given by Proposition
`thm:strongAepsi.delta`. Then
```
‖m_ε‖_{L^{β̄}(𝕋^d)}^{β̄} + ‖u_ε‖_{W^{1,γ̄}(𝕋^d)}^{γ̄} ≤ C,
```
with `C > 0` independent of `ε ∈ (0, 1]`.

## Paper proof (line 1894)

> "Follow the proof of Theorem `thm:apriori-simple.power.growth` line by
> line, replacing Lemma `lem:strong.is.strong` by Lemma
> `lem:strong.is.strong.delta`, `eq:DpHdotpminusH-estimate1` by
> `eq:DpHdelta.dotp.minusH`, and `eq:assH.lower.simple` by
> `eq:H-epsilon.lower.uniform`."

## Lean strategy

The Phase-4 aggregator `thm_apriori_simplePowerGrowth`
(`SimplePower/Apriori.lean`) is fully polymorphic in `H` and `DpH`. The
power-growth bundle `h : HypothesisPowerGrowth H DpH` is consumed only to
extract the numerical exponents `h.α, h.β` and constant `h.C`; the
analytic content (HJB inequality, Lagrangian lower bound,
integrability, …) is passed in as abstract hypotheses. To obtain the
Phase-6 statement we therefore **specialize** the Phase-4 theorem at:

* `H := Hdelta hHyp ε`  — the regularized Hamiltonian
  (paper line 1624, `eq:defHdelta`).
* `DpH := DpHε`  — the regularized gradient.
* `h := hPow`  — an externally provided `HypothesisPowerGrowth` bundle
  for `(Hdelta hHyp ε, DpHε)` carrying the uniform constants of
  `lem:H-epsilon.lower.uniform`.

The "verbatim with `H ↦ H^ε`" content of the paper proof is captured
entirely by the fact that the Phase-4 result is `H`-polymorphic. This
mirrors the wrappers `Hdelta_strong_HJB_le`,
`Hdelta_strong_HJB_eq_on_pos`, `Hdelta_strong_transport_eq` of
`InfimalConvolution/StrongIsStrong.lean`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace InfimalConvolution

open MeasureTheory Set Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.InfimalConvolution
open StationaryMFG.Theorems.SimplePower
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Main theorem: ε-uniform `L^β̄ × W^{1,γ̄}` apriori bound -/

/-- **`paper:thm:apriori-weak.power.growth`** (paper line 1881).

Specialization of the Phase-4 aggregator
`thm_apriori_simplePowerGrowth` at the regularized Hamiltonian
`H := Hdelta hHyp ε` and a generic gradient `DpH := DpHε`.

The numerical constants `α, β, C` are supplied by an externally provided
`HypothesisPowerGrowth (Hdelta hHyp ε) DpHε` bundle — in the paper this
is delivered by `lem:H-epsilon.lower.uniform` together with the
Lagrangian lower bound `eq:DpHdelta.dotp.minusH` (paper deps
`paper:prop:boundsHepsilon.{c,d}`). The HJB inequality is exactly the
one supplied by `Hdelta_strong_HJB_le`
(`paper:lem:strong.is.strong.delta` (a)).

Adapted from `thm_apriori_simplePowerGrowth` (Phase 4): the Phase-4
proof goes through verbatim under the substitution `H ↦ H^ε`, just as
prescribed by the paper at line 1894. -/
theorem apriori_weak_power_growth
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hPow : HypothesisPowerGrowth (Hdelta hHyp ε) DpHε)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + Hdelta hHyp ε x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hPow.β) / hPow.C - hPow.C ≤
            (DpHε x p mx) ⬝ p - Hdelta hHyp ε x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-Hdelta hHyp ε x (fun i => Du i x) (m x)
                    + (DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + hPow.C * (m x ^ hPow.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (hPow.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ hPow.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-Hdelta hHyp ε x (fun i => Du i x) (m x)
                            + (DpHε x (fun i => Du i x) (m x))
                                ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar hPow.α hPow.β))
    (hγ_top : ENNReal.ofReal (gammaBar hPow.α hPow.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar hPow.α hPow.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar hPow.α hPow.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar hPow.α hPow.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' hPow.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' hPow.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' hPow.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar hPow.α hPow.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, m x ^ betaBar hPow.β
          ∂(volume : Measure (Fin d → ℝ)))
        + lpNormPer (ENNReal.ofReal (gammaBar hPow.α hPow.β)) u
            ^ gammaBar hPow.α hPow.β
        + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar hPow.α hPow.β
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C :=
  -- Adapted from `thm_apriori_simplePowerGrowth` (Phase 4): specialize
  -- the `H`-polymorphic Phase-4 theorem at `H := Hdelta hHyp ε`,
  -- `DpH := DpHε`, with the externally-provided `HypothesisPowerGrowth`
  -- bundle `hPow` for `(Hdelta hHyp ε, DpHε)` supplying the numerical
  -- constants `α, β, C` of paper `lem:H-epsilon.lower.uniform`.
  thm_apriori_simplePowerGrowth (h := hPow) V Du m u epsTerms
    Vbound Vint_bound Vβp_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint
    hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
    hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
    hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ

end InfimalConvolution
end Theorems
end StationaryMFG
