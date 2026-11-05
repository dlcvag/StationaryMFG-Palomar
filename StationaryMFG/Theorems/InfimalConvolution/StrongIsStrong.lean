module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.SimplePower.StrongIsStrong
public import StationaryMFG.Theorems.InfimalConvolution.Properties

@[expose] public section

/-!
# `lem:strong.is.strong.delta`, part (a): HJB inequality for `H^ε`

This module formalizes Lemma `lem:strong.is.strong.delta`, item (a) of
Ferreira–Gomes–Üçer (`Source/FGU-monotone_revised.tex`, line 1858–1875).

## Paper statement (line 1866)

Let `0 < ε ≤ 1` and `(m, u) ∈ L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d)` satisfy the
strong variational inequality
```
⟨A_ε[m, u], (μ − m, υ − u)⟩ ≥ 0   for all (μ, υ) ∈ L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d).
```
Then
```
u(x) + H^ε(x, Du(x), m(x)) − V(x) ≤ 0   for a.e. x ∈ 𝕋^d.
```

## Paper proof (line 1878)

> "The proof is the same as that of Lemma `lem:strong.is.strong` verbatim,
> with `H` replaced by `H^ε` everywhere."

## Lean strategy

The Phase-4 lemma `lem_strong_is_strong_HJB_ineq`
(`StationaryMFG.Theorems.SimplePower.StrongIsStrong`) is fully abstract over
the Hamiltonian `H` (and its gradient `DpH`). To obtain the Phase-6 statement
it therefore suffices to **specialize** Phase-4 at the regularized
Hamiltonian `H := HdeltaK0 h ε` (defined in
`StationaryMFG.Theorems.InfimalConvolution.InfConv`). The integrability of the
residual and the set-form strong VI are passed through verbatim with `H^ε` in
place of `H`. The "verbatim with `H` ↦ `H^ε`" content of the paper proof is
captured by the very fact that Phase 4 is `H`-polymorphic.
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

/-! ## Main theorem: HJB inequality for `H^ε` from the strong VI -/

/-- **`lem:strong.is.strong.delta`, part (a)** (paper line 1866).

Under the strong variational inequality (in its set-test-pair form
`StrongVI_setForm` at `H := HdeltaK0 h ε`) and integrability of the
`H^ε`-residual on the unit cube,
```
u(x) + H^ε(x, Du(x), m(x)) − V(x) ≤ 0   for a.e. x ∈ 𝕋^d.
```

The proof is a direct specialization of the Phase-4
`lem_strong_is_strong_HJB_ineq` at the regularized Hamiltonian `HdeltaK0 h ε`:
since the Phase-4 result is polymorphic in `H`, the very same proof applies
verbatim with `H` ↦ `H^ε`, matching the paper's one-line argument
(line 1878). -/
theorem Hdelta_strong_HJB_le
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hRes : Integrable (hjbResidual V (HdeltaK0 hHyp ε) Du m u)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm V (HdeltaK0 hHyp ε) DpHε γBar ε Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + HdeltaK0 hHyp ε x (fun i => Du i x) (m x) - V x ≤ 0 :=
  -- Adapted from `lem_strong_is_strong_HJB_ineq` (Phase 4): specialize the
  -- `H`-polymorphic Phase-4 lemma at `H := HdeltaK0 hHyp ε`.
  lem_strong_is_strong_HJB_ineq (V := V) (H := HdeltaK0 hHyp ε) (DpH := DpHε)
    γBar ε Du m u hRes hVI

/-! ## Unit-test sanity check

We verify that `Hdelta_strong_HJB_le` reduces verbatim, by feeding it directly
to the Phase-4 lemma at `H := HdeltaK0 hHyp ε`. This is a type-level check that
the Phase-6 wrapper has the right signature and routes through the Phase-4
abstract lemma without any side conditions. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hRes : Integrable (hjbResidual V (HdeltaK0 hHyp ε) Du m u)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm V (HdeltaK0 hHyp ε) DpHε γBar ε Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + HdeltaK0 hHyp ε x (fun i => Du i x) (m x) - V x ≤ 0 :=
  Hdelta_strong_HJB_le hHyp V DpHε γBar ε Du m u hRes hVI

/-! ## Part (b): HJB equality on `{m > 0}` for `H^ε` -/

/-- **`lem:strong.is.strong.delta`, part (b)** (paper line 1868).

Under the signed set-test-pair form of the strong VI at the regularized
operator `A_ε` and integrability of the pointwise product `hjbResidual · m` on
the unit cube,
```
(u(x) + H^ε(x, Du(x), m(x)) − V(x)) · m(x) = 0   for a.e. x ∈ UnitCube d.
```
Equivalently, since `m ≥ 0`, this is `u + H^ε − V = 0` a.e. on `{m > 0}`.

The proof is a direct specialization of the Phase-4
`lem_strong_is_strong_HJB_eq_paperForm` at the regularized Hamiltonian
`HdeltaK0 hHyp ε`: since the Phase-4 result is polymorphic in `H`, the very
same proof applies verbatim with `H` ↦ `H^ε`, matching the paper's one-line
argument (line 1878). -/
theorem Hdelta_strong_HJB_eq_on_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hResM : Integrable
              (fun x => hjbResidual V (HdeltaK0 hHyp ε) Du m u x * m x)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm_signed V (HdeltaK0 hHyp ε) DpHε γBar ε Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (u x + HdeltaK0 hHyp ε x (fun i => Du i x) (m x) - V x) * m x = 0 :=
  -- Adapted from `lem_strong_is_strong_HJB_eq_paperForm` (Phase 4):
  -- specialize the `H`-polymorphic Phase-4 lemma at `H := HdeltaK0 hHyp ε`.
  lem_strong_is_strong_HJB_eq_paperForm (V := V) (H := HdeltaK0 hHyp ε)
    (DpH := DpHε) γBar ε Du m u hResM hVI

/-! ## Unit-test sanity check for part (b)

We verify that `Hdelta_strong_HJB_eq_on_pos` reduces verbatim, by feeding it
directly to the Phase-4 lemma at `H := HdeltaK0 hHyp ε`. This is a type-level
check that the Phase-6 wrapper has the right signature and routes through the
Phase-4 abstract lemma without any side conditions. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hResM : Integrable
              (fun x => hjbResidual V (HdeltaK0 hHyp ε) Du m u x * m x)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm_signed V (HdeltaK0 hHyp ε) DpHε γBar ε Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (u x + HdeltaK0 hHyp ε x (fun i => Du i x) (m x) - V x) * m x = 0 :=
  Hdelta_strong_HJB_eq_on_pos hHyp V DpHε γBar ε Du m u hResM hVI

/-! ## Part (c): regularized weak transport equation for `H^ε` -/

/-- **`lem:strong.is.strong.delta`, part (c)** (paper line 1872, eq.
`eq:strong-transport` regularized).

Under the transport-form specialization of the strong VI at the regularized
operator `A_ε` (`StrongVI_transportForm` at `H := HdeltaK0 hHyp ε`), the
regularized transport bracketed integral splits into the unregularized flux
part and the γ̄-Laplacian Gateaux part, and the linear combination
```
∫_{𝕋^d} transportFluxIntegrand DpHε Du m φ dx
   + ε · ∫_{𝕋^d} transportGateauxIntegrand γBar Du u φ dx = 0
```
holds for every smooth periodic test function `φ`. Equivalently, this is
the paper's regularized eq. `eq:strong-transport`:
```
∫_{𝕋^d} [(m - 1) φ + m · D_pH^ε(x, Du, m) · Dφ
         + ε |Du|^{γ̄-2} Du · Dφ + ε |u|^{γ̄-2} u · φ] dx = 0.
```

The proof is a direct specialization of the Phase-4
`lem_strong_is_strong_transport` at the regularized Hamiltonian
`HdeltaK0 hHyp ε`: since the Phase-4 result is polymorphic in `H` (and in `DpH`,
which here plays the role of `D_pH^ε`), the very same proof applies verbatim
with `H` ↦ `H^ε` and `D_pH` ↦ `D_pH^ε`, matching the paper's one-line
argument (line 1878). -/
theorem Hdelta_strong_transport_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hVI : StrongVI_transportForm V (HdeltaK0 hHyp ε) DpHε γBar ε Du m u) :
    ∀ φ : SmoothPeriodic d,
      (∫ x in UnitCube d, transportFluxIntegrand DpHε Du m φ x
          ∂(volume : Measure (Fin d → ℝ))) +
        ε * ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
              ∂(volume : Measure (Fin d → ℝ)) = 0 :=
  -- Adapted from `lem_strong_is_strong_transport` (Phase 4): specialize the
  -- `H`-polymorphic Phase-4 lemma at `H := HdeltaK0 hHyp ε`.
  lem_strong_is_strong_transport (V := V) (H := HdeltaK0 hHyp ε) (DpH := DpHε)
    γBar ε Du m u hVI

/-! ## Unit-test sanity check for part (c)

We verify that `Hdelta_strong_transport_eq` reduces verbatim, by feeding it
directly to the Phase-4 lemma at `H := HdeltaK0 hHyp ε`. This is a type-level
check that the Phase-6 wrapper has the right signature and routes through the
Phase-4 abstract lemma without any side conditions. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hVI : StrongVI_transportForm V (HdeltaK0 hHyp ε) DpHε γBar ε Du m u) :
    ∀ φ : SmoothPeriodic d,
      (∫ x in UnitCube d, transportFluxIntegrand DpHε Du m φ x
          ∂(volume : Measure (Fin d → ℝ))) +
        ε * ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
              ∂(volume : Measure (Fin d → ℝ)) = 0 :=
  Hdelta_strong_transport_eq hHyp V DpHε γBar ε Du m u hVI

end InfimalConvolution
end Theorems
end StationaryMFG
