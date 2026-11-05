module

public import StationaryMFG.Hamiltonian.Basic
public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.UnitCube

@[expose] public section

/-!
# Integral V-data scaffold (Phase D4.0a)

This module ships **D4.0a**, the first child of
`infra-P5-T10-D4-0-Vbound-refactor`. It introduces the integral
record `AprioriVData` carrying the two paper-form bounds
`∫|V| ≤ Vint_bound` and `∫|V|^βp ≤ Vβp_bound`, and a producer
`AprioriVData.of_hV` that derives such a record directly from a
single `MemLpPer (ENNReal.ofReal (Hamiltonian.betaBar' β)) V`
hypothesis.

The motivation: the existing `AprioriUniformPerSolHypotheses`
(and its C-class core) carries a pointwise field
`hVbnd : ∀ᵐ x, |V x| ≤ Vbound`, which is **not** derivable from
the paper hypothesis `hV : V ∈ L^{β̄'}`. Replacing `hVbnd` with
integral data is the structural goal of D4.0; D4.0a lands the
new structure and producer without yet refactoring the bundles
or the closed-form Apriori chain — those are sized into D4.0b/c
children.

## Design

`AprioriVData (βp : ℝ) (V : (Fin d → ℝ) → ℝ)` carries:

* `Vint_bound`, `Vβp_bound` — two real upper bounds;
* `hVint_nn`, `hVβp_nn` — non-negativity of those bounds;
* `hVint : ∫|V| ≤ Vint_bound` and `hVβp : ∫|V|^βp ≤ Vβp_bound`.

The producer `AprioriVData.of_hV` chooses the trivial *reflexive*
witnesses `Vint_bound := ∫|V|`, `Vβp_bound := ∫|V|^βp`. Their
non-negativity follows from `MeasureTheory.integral_nonneg` (each
integrand is pointwise nonneg). The `hV : MemLpPer …` argument is
present for forward-compatibility with D4.0b (where the reflexive
choice will be relaxed to genuine `L^{β̄'}`-derived bounds and
where measurability/finiteness of the integrals will become
relevant); in D4.0a the producer's body never inspects it.

After D4.0b refactors `apriori_*_closed` to consume `(hVint, hVβp)`
in place of `(Vbound, hVbnd)`, the bundles' `hVbnd` field can be
dropped (D4.0c), and the diagnostic stub
`T10PaperResidues.of_paperHypotheses` will route its V-data
through `AprioriVData.of_hV` (closing the iter-0531 D2
`Vbound := 0` scaffold).
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- **Integral V-data record.**

Carries integral upper bounds on `|V|` and `|V|^βp` over the unit
cube `[0,1]^d`, together with non-negativity certificates. The
exponent `βp` is taken as a real (the paper-canonical instance is
`βp = Hamiltonian.betaBar' β`).

Replacing the pointwise residue field
`hVbnd : ∀ᵐ x, |V x| ≤ Vbound` of
`AprioriUniformPerSolHypotheses` /
`AprioriUniformPerSolHypothesesC` with this record is the
structural goal of D4.0; this file lands the record (D4.0a),
the closed-form Apriori chain refactor follows in D4.0b, and the
bundle drop follows in D4.0c. -/
structure AprioriVData
    (βp : ℝ)
    (V : (Fin d → ℝ) → ℝ) where
  /-- Real-valued `L¹` bound on `|V|`. -/
  Vint_bound : ℝ
  /-- Real-valued `L^βp` bound on `|V|^βp`. -/
  Vβp_bound : ℝ
  /-- Non-negativity of the `L¹` bound. -/
  hVint_nn : 0 ≤ Vint_bound
  /-- Non-negativity of the `L^βp` bound. -/
  hVβp_nn : 0 ≤ Vβp_bound
  /-- `∫|V| ≤ Vint_bound` over the unit cube. -/
  hVint :
    ∫ x in UnitCube d, |V x|
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ Vint_bound
  /-- `∫|V|^βp ≤ Vβp_bound` over the unit cube. -/
  hVβp :
    ∫ x in UnitCube d, |V x| ^ βp
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ Vβp_bound

/-- **Producer: `AprioriVData` from `hV : V ∈ L^{β̄'}` (D4.0a, trivial
witness).**

Given the paper hypothesis `hV : MemLpPer (ofReal (betaBar' β)) V`,
return an `AprioriVData (betaBar' β) V` whose two bounds are taken
to be the integrals themselves (so `hVint` and `hVβp` hold by
reflexivity). Non-negativity of each bound follows from
`MeasureTheory.integral_nonneg` applied to the pointwise-nonneg
integrand.

The `hV` argument is present for forward-compatibility with
D4.0b/c — the body does not consume it. After D4.0b's refactor of
the closed-form Apriori chain, the producer will be re-tuned to
deliver bounds of a shape compatible with the chain's residue
form (e.g. `lpNormPer` rather than the raw integral), and the
`MemLpPer` hypothesis will be the source of those bounds. -/
noncomputable def AprioriVData.of_hV
    {β : ℝ}
    (_hβ : 0 < β)
    (V : (Fin d → ℝ) → ℝ)
    (_hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' β)) V) :
    AprioriVData (d := d) (Hamiltonian.betaBar' β) V where
  Vint_bound :=
    ∫ x in UnitCube d, |V x|
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  Vβp_bound :=
    ∫ x in UnitCube d, |V x| ^ Hamiltonian.betaBar' β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  hVint_nn := by
    refine MeasureTheory.integral_nonneg ?_
    intro x; exact abs_nonneg _
  hVβp_nn := by
    refine MeasureTheory.integral_nonneg ?_
    intro x; exact Real.rpow_nonneg (abs_nonneg _) _
  hVint := le_refl _
  hVβp := le_refl _

/-! ### Sanity-check unit tests pinning the type-shape

Pin the type-shape of `AprioriVData` and `AprioriVData.of_hV` via
forwarding `example`s — these guarantee the producer matches the
specification exactly. -/

/-- **Unit test for `AprioriVData.of_hV`:** the producer's
type-shape is paper-input → integral-record. -/
example
    {β : ℝ} (hβ : 0 < β)
    (V : (Fin d → ℝ) → ℝ)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' β)) V) :
    AprioriVData (d := d) (Hamiltonian.betaBar' β) V :=
  AprioriVData.of_hV hβ V hV

/-- **Unit test:** the produced record has non-negative bounds. -/
example
    {β : ℝ} (hβ : 0 < β)
    (V : (Fin d → ℝ) → ℝ)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' β)) V) :
    0 ≤ (AprioriVData.of_hV hβ V hV).Vint_bound
      ∧ 0 ≤ (AprioriVData.of_hV hβ V hV).Vβp_bound :=
  ⟨(AprioriVData.of_hV hβ V hV).hVint_nn,
   (AprioriVData.of_hV hβ V hV).hVβp_nn⟩

end Banach
end SimplePower
end Theorems
end StationaryMFG

end
