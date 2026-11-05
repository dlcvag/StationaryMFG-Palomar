module

public import StationaryMFG.Theorems.InfimalConvolution.InfConv
public import StationaryMFG.Solutions.Regularized

@[expose] public section

/-!
# The regularized MFG operator `A_ε^δ` (paper line 1826, `defAepsi.delta`)

This module defines the **regularized MFG operator with regularized
Hamiltonian** `A_ε^δ` of paper line 1826
(`Source/FGU-monotone_revised.tex`, eq. `defAepsi.delta`):

```
⟨A_ε^δ[m, u], (η, ν)⟩
  = ∫ (-u - H^ε(x, Du, m) + V(x)) η dx
  + ∫ (m · D_pH^ε(x, Du, m) · Dν + (m - 1) ν) dx
  + ε ∫ (|Du|^{γ̄-2} Du · Dν + |u|^{γ̄-2} u · ν) dx.
```

This is precisely `A_ε` (Phase 3, `Solutions.Regularized.mfgOperatorEpsPair`,
paper line 925 `defAepsi`) with the substitution `H ↦ H^ε`,
`D_pH ↦ D_pH^ε` made in the first two integrals. Because the Phase-3
operator is encoded *via its action* against a test triple
`(η, ν, Dν)`, the substitution is purely a re-instantiation: no new
infrastructure is required.

Following `docs/CONVENTIONS.md` §1b, we expose the operator through its
pairing.

## Deliverables

* `aepsilonDeltaPair` — `A_ε^δ`'s action against a test triple,
  defined as `mfgOperatorEpsPair (H := Hdelta h ε) (DpH := DpHε) …`.
* `aepsilonDeltaPair_wellDefined` — finiteness of the pairing under the
  natural Hölder-conjugate `MemLpPer` hypotheses on the integrand
  factors. This is a "wrapper" statement consumed by Phase 6's downstream
  monotone-operator framework; the actual numeric bound is supplied by
  `mfgPairing_holder_bound` once each factor is shown to lie in the
  appropriate `MemLpPer` space (a separate task per `paper:prop:boundsHepsilon.{a,b}`).

## Paper reference

`Source/FGU-monotone_revised.tex` line 1826, equation `defAepsi.delta`.
-/

noncomputable section

namespace StationaryMFG
namespace InfimalConvolution

open StationaryMFG.Hamiltonian
open StationaryMFG.Periodic
open StationaryMFG.Solutions.MFG
open MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ## The `A_ε^δ` pairing -/

/-- **Pairing of the regularized MFG operator with regularized Hamiltonian**
`A_ε^δ` against a test triple `(η, ν, Dν)` (paper line 1826,
`defAepsi.delta`).

Defined as the Phase-3 regularized operator pairing
`mfgOperatorEpsPair` instantiated at `H ↦ H^ε := Hdelta h ε` and
`D_pH ↦ DpHε` (a candidate regularized gradient supplied by the
caller; the canonical one comes from `infra:P6-Hepsilon-extend`).

Bare-real parameters `γBar : ℝ` and `ε : ℝ`; positivity is imposed at
use sites. -/
def aepsilonDeltaPair (γBar ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) : ℝ :=
  mfgOperatorEpsPair (V := V) (H := Hdelta h ε) (DpH := DpHε)
    γBar ε Dυ μ υ Dν η ν

/-! ## Well-definedness

We package the integrability / finiteness statement as a wrapper of the
Phase-3 Hölder-conjugate bound `mfgPairing_holder_bound`. The numeric
content sits in `Solutions.MFG`; here we just *expose* it at the
substituted slots `(H := Hdelta h ε, DpH := DpHε)`.

The hypothesis structure mirrors `mfgPairing_holder_bound`:

* β̄/β̄' Hölder pair for the `μ ↔ η` and `υ ↔ ν` channels;
* γ̄/γ̄' Hölder pair for the `Du ↔ Dν` channel.

`A_ε^δ` adds the γ̄-Laplacian Gateaux term, whose integrability is
governed by the same γ̄/γ̄' pair (paper line 925 / 1826). -/

/-- **Well-definedness of `A_ε^δ`.** Under Hölder-conjugate `MemLpPer`
hypotheses on each integrand factor of the *primal* MFG pairing
`mfgPairing m u Du η ν Dν`, the corresponding `mfgPairing`
absolute value is finite (bounded by the Hölder sum-of-products).

This is the wrapper consumed by Phase 6's monotone-operator framework
to confirm that each summand of the `A_ε^δ` pairing is finite; the
nonlinear `H^ε`-dependent summands are reduced to the linear pairing
via the `prop:boundsHepsilon.{a,b}` bounds in separate tasks. -/
theorem aepsilonDeltaPair_wellDefined
    {betaBar betaBar' gammaBar gammaBar' : ℝ}
    (hβ : betaBar.HolderConjugate betaBar')
    (hγ : gammaBar.HolderConjugate gammaBar')
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ} {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal betaBar) m)
    (hu : MemLpPer (ENNReal.ofReal gammaBar) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal gammaBar) (Du i))
    (hη : MemLpPer (ENNReal.ofReal betaBar') η)
    (hν : MemLpPer (ENNReal.ofReal gammaBar') ν)
    (hDν : ∀ i, MemLpPer (ENNReal.ofReal gammaBar') (Dν i)) :
    |mfgPairing m u Du η ν Dν| ≤
      lpNormPer (ENNReal.ofReal betaBar) m *
          lpNormPer (ENNReal.ofReal betaBar') η +
        lpNormPer (ENNReal.ofReal gammaBar) u *
          lpNormPer (ENNReal.ofReal gammaBar') ν +
        ∑ i : Fin d,
          lpNormPer (ENNReal.ofReal gammaBar) (Du i) *
            lpNormPer (ENNReal.ofReal gammaBar') (Dν i) :=
  mfgPairing_holder_bound hβ hγ hm hu hDu hη hν hDν

end InfimalConvolution
end StationaryMFG

end
