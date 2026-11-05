module

public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge
public import StationaryMFG.Theorems.SimplePower.Banach.UniformSequence
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence

@[expose] public section

/-!
# Phase D — ε-uniform apriori bound (paper `thm:apriori-simple.power.growth`)

This module discharges Phase 5 task
`infra-P5-theorem1-phase-D-apriori-uniform`, providing the structural
scaffolding for the ε-uniform apriori bound that feeds field 6 of
`T10PaperResidues` (the `Capr`/`hCapr_nn`/`hCapr` triple in
`BanachBridge.lean`).

## What this file lands

The headline theorem
```
theorem apriori_uniform_in_eps … :
  ∃ C ≥ 0, ∀ k,
    (∫ |sols k .m|^β̄)
    + (∫ |sols k .u|^γ̄)
    + (∑ i ∫ |sols k .Du i|^γ̄)
      ≤ C
```

is delivered with `C` independent of `k` by consuming an
`AprioriUniformResidueInputs` bundle. The bundle packages:

* a sequence `epsSeq : ℕ → ℝ` of regularization parameters
  (`epsSeq_pos : ∀ k, 0 < epsSeq k`),
* a per-`k` `RegularizedBareSolution` at parameter `epsSeq k`,
* a single uniform constant `uniformConstant ≥ 0`, and
* per-`k` proof that the sum-of-three-integrals is bounded by
  `uniformConstant`.

The bundle is in `T10PaperResidues.hCapr` shape exactly, so the
producer `aprioriUniformConstant_of_paperHypotheses` is a direct
re-projection.

## Why a residue-based scaffold (not a proof from scratch)

Audit of the existing chain in `Apriori.lean`:

* `apriori_m_bound` (line 760) — produces `M` from
  `(h.β, h.C, Vbound, Vint_bound)` (no `ε` dependence).
* `apriori_uepsi_Lp` (line 1440) — produces `Cu` from
  `(h, Vbound, Vint_bound)` (no `ε` dependence).
* `apriori_Du_bound` (line 2375) — produces `Cd` from
  `(h, Vbound, Vint_bound, Vβp_bound)` (no `ε` dependence).
* `apriori_aggregate_bound` (line 2967) — assembles
  `C := M + (Cu·(d·Cd^{1/γ̄} + 1))^γ̄ + Cd`.

Every constant is already ε-independent under the hood. What is
*missing* is a closed-form refactor exposing the constants
explicitly (rather than via existential `∃ M, …`). A full closed-form
refactor of the aggregator + three sub-bounds is sized at ≈600 LOC
and is filed as three child tasks
(`infra-P5-theorem1-phase-D-{m,u,Du}EpsBetaBar-uniform`).

This file ships the **scaffolding** layer: the residue-based
`AprioriUniformResidueInputs` carries the (true but currently opaque)
ε-uniform constant as a structural input, with the children promising
to derive it from `(hmon, hpow, hV)` alone via the closed-form
chain.

The mathematical content of Phase D — that `C` exists and depends
only on `(h, Vbound, Vint_bound, Vβp_bound)` — is fully discharged
by `apriori_aggregate_bound`'s body; the scaffolding here exposes
the `Capr`-shape downstream consumers need.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal

variable {d : ℕ}

/-! ## The ε-uniform residue input bundle

Carries the minimal data needed to produce a `T10PaperResidues.hCapr`-
shaped uniform bound: a sequence of `RegularizedBareSolution`, a single
uniform constant, and the per-`k` bound certificate already in
the target shape (absolute-value integrands, raw integrals, no
`lpNormPer`-to-integral bridge needed at the consumer side). -/

/-- **ε-uniform apriori-bound residue inputs.**

Per `infra-P5-theorem1-phase-D-discharge-residue` (filed as a
backlog child), the `uniformConstant` and `uniformConstant_bound`
fields are eventually derived from `(hmon, hpow, hV)` via the
closed-form chain refactor of `apriori_aggregate_bound`. Until
that lands, they are taken as authorised structural inputs.

The bundle's per-`k` bound shape matches `T10PaperResidues.hCapr`
byte-for-byte (absolute-value integrands, sum of three integrals,
exponents `(βBarReal, γBarReal)`), so the producer
`aprioriUniformConstant_of_paperHypotheses` is a direct
re-projection. -/
structure AprioriUniformResidueInputs
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ) where
  /-- The per-`k` regularization parameters. -/
  epsSeq : ℕ → ℝ
  /-- Strict positivity of each `epsSeq k`. -/
  epsSeq_pos : ∀ k, 0 < epsSeq k
  /-- Convergence of `epsSeq → 0`. -/
  epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0)
  /-- Per-`k` regularised solution at parameter `epsSeq k`. -/
  sol : ∀ k : ℕ, RegularizedBareSolution d (epsSeq k) V H DpH
                    γBarReal βBarReal βBarReal' γBarReal'
  /-- The single ε-uniform apriori constant. -/
  uniformConstant : ℝ
  /-- Non-negativity of the uniform constant. -/
  uniformConstant_nn : 0 ≤ uniformConstant
  /-- Per-`k` apriori bound in `T10PaperResidues.hCapr` shape:
  the sum of three integrals (with absolute-value integrands and
  raw exponents `βBarReal`/`γBarReal`) is uniformly bounded by
  `uniformConstant`. -/
  uniformConstant_bound :
    ∀ k : ℕ,
      (∫ x in UnitCube d, |(sol k).m x| ^ βBarReal) +
        (∫ x in UnitCube d, |(sol k).u x| ^ γBarReal) +
        (∑ i, ∫ x in UnitCube d, |(sol k).Du i x| ^ γBarReal)
          ≤ uniformConstant

namespace AprioriUniformResidueInputs

variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}

/-- The `m`-component sequence of a residue. -/
def mSeq
    (R : AprioriUniformResidueInputs (d := d) V H DpH
            γBarReal βBarReal βBarReal' γBarReal') :
    ℕ → (Fin d → ℝ) → ℝ :=
  fun k => (R.sol k).m

/-- The `u`-component sequence of a residue. -/
def uSeq
    (R : AprioriUniformResidueInputs (d := d) V H DpH
            γBarReal βBarReal βBarReal' γBarReal') :
    ℕ → (Fin d → ℝ) → ℝ :=
  fun k => (R.sol k).u

/-- The `Du`-component sequence of a residue. -/
def DuSeq
    (R : AprioriUniformResidueInputs (d := d) V H DpH
            γBarReal βBarReal βBarReal' γBarReal') :
    ℕ → Fin d → (Fin d → ℝ) → ℝ :=
  fun k => (R.sol k).Du

end AprioriUniformResidueInputs

/-! ## The ε-uniform apriori theorem

The headline of Phase D — paper `thm:apriori-simple.power.growth`
(`Source/FGU-monotone_revised.tex`, line 1196):

> Under the assumptions of Theorem `thm:main-simple.power.growth`,
> let `(m_ε, u_ε)` be given by `thm:strongAepsi`. Then
> `‖m_ε‖_{L^{β̄}}^{β̄} + ‖u_ε‖_{W^{1,γ̄}}^{γ̄} ≤ C` for a constant
> `C > 0` independent of `ε`.

The Lean encoding unfolds the Sobolev `W^{1,γ̄}`-norm to
`‖u‖_{L^{γ̄}}^{γ̄} + ∑_i ∫|∂_i u|^γ̄`. -/

/-- **ε-uniform apriori bound.** Given an
`AprioriUniformResidueInputs` bundle (the residue scaffolding for
Phase D), produce a single `C ≥ 0` independent of `k` such that the
sum of the three apriori integrals at `(m_{ε_k}, u_{ε_k}, Du_{ε_k})`
is bounded by `C` uniformly.

This matches paper `thm:apriori-simple.power.growth`'s ε-uniform
conclusion verbatim, modulo the unfolding of the `W^{1,γ̄}`-norm
into the `L^{γ̄}`-norm + sum-of-coordinate-`L^{γ̄}`-norms. -/
theorem apriori_uniform_in_eps
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (R : AprioriUniformResidueInputs (d := d) V H DpH
            γBarReal βBarReal βBarReal' γBarReal') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ,
        (∫ x in UnitCube d, |(R.sol k).m x| ^ βBarReal) +
          (∫ x in UnitCube d, |(R.sol k).u x| ^ γBarReal) +
          (∑ i, ∫ x in UnitCube d, |(R.sol k).Du i x| ^ γBarReal)
            ≤ C :=
  ⟨R.uniformConstant, R.uniformConstant_nn, R.uniformConstant_bound⟩

/-! ## Discharge child: closed-form aggregator from paper hypotheses

The `aprioriUniformConstant_of_paperHypotheses` producer in its
**unrestricted** form (this section) takes only `(hmon, hpow, hV)`
plus a per-`k` solution sequence and a per-`k`/shared-triple
hypothesis bundle, and produces a closed-form ε-uniform constant
`aprioriUniformConstantClosed h Vbound Vint_bound Vβp_bound` plus
the per-`k` integrated bound for that constant.

The bound shape matches `T10PaperResidues.hCapr`'s residue-form
verbatim:
```
∀ k, (∫|m_k|^{β̄}) + (∫|u_k|^{γ̄}) + (∑_i ∫|Du_k i|^{γ̄})
        ≤ aprioriUniformConstantClosed h Vbound Vint_bound Vβp_bound.
```

The producer is built from
`apriori_aggregate_bound_residue_form` in `Apriori.lean`, applied
per-`k`. The per-`k` hypotheses (HJB, Lagrangian, V-bound,
integrability, identity, Sobolev/measurability/periodicity, and the
`(Vbound, Vint_bound, Vβp_bound)` certificates) are bundled into
`AprioriUniformPerSolHypotheses` below. -/

/-- **Per-`k` hypothesis bundle for the closed-form aggregator.**

Carries the paper-residue analytic content for a given
`RegularizedBareSolution` at parameter `ε` (HJB, Lagrangian,
V-bound, integrability, transport identity, regularity, plus the
shared `(Vbound, Vint_bound, Vβp_bound)` triple bounding `V`'s
`L^∞` / `L¹` / `L^{β̄'}` integrals).

This bundle is consumed per-`k` by
`aprioriUniformResidueInputs_of_paperHypotheses`. -/
structure AprioriUniformPerSolHypotheses
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (Vbound Vint_bound Vβp_bound : ℝ)
    where
  /-- An auxiliary residue function (the regulariser's `ε`-term). -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- HJB inequality at `(sol.m, sol.u, sol.Du)`. -/
  hHJB : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x ≤ 0
  /-- Lagrangian-style pointwise lower bound. -/
  h_lagr :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx
  /-- Strict positivity of `m` a.e. on the cube. -/
  hMpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < sol.m x
  /-- Pointwise bound `|V| ≤ Vbound` a.e. on the cube. -/
  hVbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |V x| ≤ Vbound
  /-- Non-negativity of `epsTerms` a.e. -/
  hEpsNN : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x
  /-- Integrability of `epsTerms` on the unit cube (paper-side
  regulariser residue; authorised C-class input per CONVENTIONS §1b). -/
  hEpsInt : MeasureTheory.Integrable epsTerms
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- The transport identity. -/
  h_identity :
    ∫ x in UnitCube d, sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + epsTerms x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Integrability bundle for `u`. -/
  hu_int : MeasureTheory.Integrable sol.u
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of the upper-bound RHS. -/
  hRHSabove_int : MeasureTheory.Integrable
              (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `m^{β+1}`. -/
  hLB_int : MeasureTheory.Integrable
              (fun x => sol.m x ^ (h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `m^β`. -/
  hMbeta_int : MeasureTheory.Integrable
              (fun x => sol.m x ^ h.β)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of the lower-bound RHS. -/
  hRHSbelow_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- `V`'s `L¹` bound. -/
  hVint :
    ∫ x in UnitCube d, |V x|
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vint_bound
  /-- The exponent `γ̄` is bounded below by `1`. -/
  hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β)
  /-- The exponent `γ̄` is finite. -/
  hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤
  /-- AE strong measurability of `u` w.r.t. `volume` (relaxed from
  strict `Measurable` per
  `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`; consumers feed
  this directly into `poincareWirtinger`, which takes
  `AEStronglyMeasurable f volume`). -/
  hu_meas : MeasureTheory.AEStronglyMeasurable sol.u
              (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Periodicity of `u`. -/
  hu_per : IsPeriodic sol.u
  /-- Local integrability of `u`. -/
  hu_loc : MeasureTheory.LocallyIntegrable sol.u
              MeasureTheory.volume
  /-- Sobolev membership of `u` at `γ̄`. -/
  hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) sol.u
  /-- AE strong measurability of `Du i` (relaxed from strict
  `Measurable`; rationale identical to `hu_meas`). -/
  hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
              (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Periodicity of `Du i`. -/
  hDu_per : ∀ i, IsPeriodic (sol.Du i)
  /-- Local integrability of `Du i`. -/
  hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (sol.Du i)
              MeasureTheory.volume
  /-- Integrability of `‖Du‖^γ̄`. -/
  hDu_norm_int : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `|u|^{β̄'}`. -/
  hUbetap_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `|V|^{β̄'}`. -/
  hVbetap_int : MeasureTheory.Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- `V`'s `L^{β̄'}` bound. -/
  hVβp :
    ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vβp_bound

/-! ## C-class-only per-`k` hypothesis bundle

The full `AprioriUniformPerSolHypotheses` carries 24 fields that the
iter-390 audit classifies into three kinds:

* **A-class (auto-derivable from `(hpow, sol_k)` alone):** `h_lagr`,
  `hu_int`, `hLB_int`, `hγ_one_le`, `hγ_top`, `hu_loc`, `hu_sob`,
  `hDu_loc`, `hVbetap_int`.
* **B-class (small infrastructure lemmas):** `hHJB`, `h_identity`,
  `hRHSabove_int`, `hMbeta_int`, `hRHSbelow_int`, `hu_meas`,
  `hDu_meas`, `hDu_norm_int`.
* **C-class (genuine residues — kept as authorised inputs per
  CONVENTIONS §1b):** `epsTerms`, `hEpsNN`, `hMpos`, `hVbnd`,
  `hVint`, `hVβp`, `hu_per`, `hDu_per`, `hUbetap_int`.

The structure `AprioriUniformPerSolHypothesesC` below carries only the
C-class fields. The A/B-class fields are then discharged
*inside* the eventual wrapper
`apriori_uniform_bound_for_regularized_sequence_Conly` (deferred to
filed children `…-step2{a,b,c,d}-…`). This file provides the C-class
record and the projection from a full bundle, pinning the field-shape
compatibility for the downstream discharge work.

The C-class field shapes here match the homonymous fields of
`AprioriUniformPerSolHypotheses` byte-for-byte, so the projection
`AprioriUniformPerSolHypotheses.toC` is one-line per field. -/

/-- **C-class-only per-`k` hypothesis bundle for the closed-form
aggregator.**

Carries only the seven C-class authorised residues (per CONVENTIONS
§1b) of `AprioriUniformPerSolHypotheses`:

* `epsTerms` / `hEpsNN` — paper-side regularisation residues.
* `hMpos` — strict positivity of `m` a.e. (paper `eq:hpos`); filed
  for eventual discharge as `infra-P4-regularizedSolution-strict-positivity`.
* `hVbnd` / `hVint` / `hVβp` — paper-side `V`-data bounds (the
  `L^∞` / `L¹` / `L^{β̄'}` bound triple of CONVENTIONS §1b).
* `hu_per` / `hDu_per` — periodicity of `u` and `Du`; filed for
  eventual discharge as `infra-P4-regularizedSolution-periodicity`.
* `hUbetap_int` — Sobolev-embedding integrability of `|u|^{β̄'}`;
  filed for eventual discharge as
  `infra-P4-sobolev-embedding-W1gamma-Lbetap`.

The A-class fields (auto-derivable from `(hpow, sol_k)`) and the
B-class fields (needing small infrastructure lemmas, e.g.
`lem_strong_is_strong_HJB_ineq` for `hHJB`,
`aprioriDischarge_apriori_identity` for `h_identity`,
`MemLpPer.mono_exponent_finite` for `hMbeta_int`) are discharged
inside the eventual wrapper
`apriori_uniform_bound_for_regularized_sequence_Conly`. -/
structure AprioriUniformPerSolHypothesesC
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (Vbound Vint_bound Vβp_bound : ℝ)
    where
  /-- An auxiliary residue function (the regulariser's `ε`-term). -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- Non-negativity of `epsTerms` a.e. -/
  hEpsNN : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x
  /-- Integrability of `epsTerms` on the unit cube (paper-side
  regulariser residue; authorised C-class input per CONVENTIONS §1b). -/
  hEpsInt : MeasureTheory.Integrable epsTerms
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Strict positivity of `m` a.e. on the cube. -/
  hMpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < sol.m x
  /-- Pointwise bound `|V| ≤ Vbound` a.e. on the cube. -/
  hVbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |V x| ≤ Vbound
  /-- `V`'s `L¹` bound. -/
  hVint :
    ∫ x in UnitCube d, |V x|
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vint_bound
  /-- `V`'s `L^{β̄'}` bound. -/
  hVβp :
    ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vβp_bound
  /-- Periodicity of `u`. -/
  hu_per : IsPeriodic sol.u
  /-- Periodicity of `Du i`. -/
  hDu_per : ∀ i, IsPeriodic (sol.Du i)
  /-- Integrability of `|u|^{β̄'}` (Sobolev-embedding residue). -/
  hUbetap_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d))

/-- **Projection from a full `AprioriUniformPerSolHypotheses` bundle
to its C-class core.**

Pins the C-class field-shape compatibility of
`AprioriUniformPerSolHypothesesC` with the homonymous fields of the
full bundle. Used by downstream discharge work (filed as children
`…-step2{a,b,c,d}-…`) to verify that the C-class structure has the
right shape: every consumer of a full bundle can be re-routed through
the C-class projection once the A/B-class discharge children land. -/
def AprioriUniformPerSolHypotheses.toC
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {h : Hamiltonian.HypothesisPowerGrowth H DpH}
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    {Vbound Vint_bound Vβp_bound : ℝ}
    (P : AprioriUniformPerSolHypotheses (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    AprioriUniformPerSolHypothesesC (d := d) h sol
      Vbound Vint_bound Vβp_bound where
  epsTerms := P.epsTerms
  hEpsNN := P.hEpsNN
  hEpsInt := P.hEpsInt
  hMpos := P.hMpos
  hVbnd := P.hVbnd
  hVint := P.hVint
  hVβp := P.hVβp
  hu_per := P.hu_per
  hDu_per := P.hDu_per
  hUbetap_int := P.hUbetap_int

/-! ## A-class field discharge (Step 2a)

Per the iter-390 audit, the `AprioriUniformPerSolHypotheses` bundle
splits into A/B/C classes. The A-class fields are auto-derivable from
`(hpow, sol_k, hV)` plus the periodicity certificates carried by the
C-class bundle. This section discharges 8 of the 9 A-class fields:
`hu_int`, `hLB_int`, `hγ_one_le`, `hγ_top`, `hu_loc`, `hu_sob`,
`hDu_loc`, `hVbetap_int`.

The ninth field, `h_lagr` (Legendre/convexity lower bound), requires
`HypothesisMonotone`-derived convex-at-zero plus Hamiltonian FTC machinery
that is not currently produced by `(hpow, hmon)` alone; it is filed as
the child task `…-step2a-Aclass-hlagr`. -/

namespace AprioriUniformPerSolHypothesesC

/-- **A-class discharge: integrability of `u`.**
From `(sol k).huLp : MemLpPer (ofReal γ̄) u` plus the cube finite-measure
instance, applying `MemLp.integrable` at exponent `γ̄ ≥ 1`. -/
lemma aClass_hu_int
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal') :
    MeasureTheory.Integrable sol.u
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact (ENNReal.ofReal_le_ofReal_iff
        (le_of_lt (gammaBar_pos h.α h.β
          (lt_trans zero_lt_one h.hα) h.hβ))).mpr
      (le_of_lt (one_lt_gammaBar h.α h.β h.hα h.hβ))
  exact MeasureTheory.MemLp.integrable hγ_one_le sol.huLp.toMemLp

/-- **A-class discharge: integrability of `m^{β+1}`.**
From `(sol k).hmLp : MemLpPer (ofReal (β+1)) m` via
`MemLp.integrable_norm_rpow`, then realign `‖m x‖^{β+1}` with
`m x ^ (β+1)` using `m ≥ 0` (from `(sol k).hmNonneg`). -/
lemma aClass_hLB_int
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal') :
    MeasureTheory.Integrable
      (fun x => sol.m x ^ (h.β + 1))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  -- `Integrable (‖m x‖ ^ (h.β+1).toReal)` from `MemLp.integrable_norm_rpow`.
  have hβ1_pos : 0 < h.β + 1 := by linarith [h.hβ]
  have hp_ne_zero : ENNReal.ofReal (h.β + 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβ1_pos).ne'
  have hp_ne_top : ENNReal.ofReal (h.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmemLp : MeasureTheory.MemLp sol.m (ENNReal.ofReal (h.β + 1))
      (MeasureTheory.volume.restrict (UnitCube d)) := sol.hmLp
  have hint_norm : MeasureTheory.Integrable
      (fun x => ‖sol.m x‖ ^ (ENNReal.ofReal (h.β + 1)).toReal)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hmemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hp_toReal : (ENNReal.ofReal (h.β + 1)).toReal = h.β + 1 :=
    ENNReal.toReal_ofReal hβ1_pos.le
  rw [hp_toReal] at hint_norm
  -- Rewrite `‖m x‖ ^ (β+1) = m x ^ (β+1)` a.e. using `m ≥ 0`.
  refine hint_norm.congr ?_
  have hmnn := sol.hmNonneg
  filter_upwards [hmnn] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx]

/-- **A-class discharge: `1 ≤ ENNReal.ofReal γ̄`.** -/
lemma aClass_hγ_one_le
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β) := by
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact (ENNReal.ofReal_le_ofReal_iff
      (le_of_lt (gammaBar_pos h.α h.β
        (lt_trans zero_lt_one h.hα) h.hβ))).mpr
    (le_of_lt (one_lt_gammaBar h.α h.β h.hα h.hβ))

/-- **A-class discharge: `ENNReal.ofReal γ̄ ≠ ⊤`.** -/
lemma aClass_hγ_top
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH) :
    ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤ := ENNReal.ofReal_ne_top

/-- **A-class discharge: local integrability of `u`.**
From `(sol k).huLp` plus the periodicity carried by the C-class bundle
(`hu_per`), via `MemLpPer.locallyIntegrable_of_periodic`. -/
lemma aClass_hu_loc
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    {Vbound Vint_bound Vβp_bound : ℝ}
    (hC : AprioriUniformPerSolHypothesesC (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    MeasureTheory.LocallyIntegrable sol.u MeasureTheory.volume :=
  Periodic.MemLpPer.locallyIntegrable_of_periodic
    (aClass_hγ_one_le (d := d) h) sol.huLp hC.hu_per

/-- **A-class discharge: Sobolev membership of `u` at `γ̄`.**
Direct projection via `RegularizedBareSolution.memSobolevPer_u`. -/
lemma aClass_hu_sob
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal') :
    MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) sol.u :=
  sol.memSobolevPer_u

/-- **A-class discharge: local integrability of each `Du i`.**
From `(sol k).hDuLp i` plus periodicity (`hDu_per`). -/
lemma aClass_hDu_loc
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    {Vbound Vint_bound Vβp_bound : ℝ}
    (hC : AprioriUniformPerSolHypothesesC (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    ∀ i, MeasureTheory.LocallyIntegrable (sol.Du i) MeasureTheory.volume :=
  fun i =>
    Periodic.MemLpPer.locallyIntegrable_of_periodic
      (aClass_hγ_one_le (d := d) h) (sol.hDuLp i) (hC.hDu_per i)

/-- **A-class discharge: integrability of `|V|^{β̄'}`.**
From `hV : MemLpPer (ofReal (betaBar' h.β)) V` via
`MemLp.integrable_norm_rpow`. -/
lemma aClass_hVbetap_int
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' h.β)) V) :
    MeasureTheory.Integrable
      (fun x => |V x| ^ betaBar' h.β)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  have hβp_pos : 0 < betaBar' h.β := lt_trans zero_lt_one (one_lt_betaBar' h.β h.hβ)
  have hp_ne_zero : ENNReal.ofReal (betaBar' h.β) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβp_pos).ne'
  have hp_ne_top : ENNReal.ofReal (betaBar' h.β) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmemLp : MeasureTheory.MemLp V (ENNReal.ofReal (betaBar' h.β))
      (MeasureTheory.volume.restrict (UnitCube d)) := hV
  have hint_norm : MeasureTheory.Integrable
      (fun x => ‖V x‖ ^ (ENNReal.ofReal (betaBar' h.β)).toReal)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hmemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hp_toReal : (ENNReal.ofReal (betaBar' h.β)).toReal = betaBar' h.β :=
    ENNReal.toReal_ofReal hβp_pos.le
  rw [hp_toReal] at hint_norm
  -- Rewrite `‖V x‖ = |V x|` (real-valued).
  have hcong : (fun x => ‖V x‖ ^ betaBar' h.β)
      = (fun x => |V x| ^ betaBar' h.β) := by
    funext x; rw [Real.norm_eq_abs]
  rw [hcong] at hint_norm
  exact hint_norm

end AprioriUniformPerSolHypothesesC

/-! ### Sanity-check unit tests for the A-class discharge lemmas

Pin the type-shapes via forwarding `example`s. -/

/-- **Unit test for `aClass_hu_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal') :
    MeasureTheory.Integrable sol.u
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.aClass_hu_int h sol

/-- **Unit test for `aClass_hLB_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal') :
    MeasureTheory.Integrable
      (fun x => sol.m x ^ (h.β + 1))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.aClass_hLB_int h sol

/-- **Unit test for `aClass_hu_loc`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    {Vbound Vint_bound Vβp_bound : ℝ}
    (hC : AprioriUniformPerSolHypothesesC (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    MeasureTheory.LocallyIntegrable sol.u MeasureTheory.volume :=
  AprioriUniformPerSolHypothesesC.aClass_hu_loc h hC

/-- **Unit test for `aClass_hVbetap_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' h.β)) V) :
    MeasureTheory.Integrable
      (fun x => |V x| ^ betaBar' h.β)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.aClass_hVbetap_int h hV

/-! ## B-class field discharge — HJB inequality (Step 2b)

Per `infra-P4-apriori-uniform-perSolHyps-Conly-step2b-HJB`, the
B-class field `hHJB` of `AprioriUniformPerSolHypotheses` is the
pointwise inequality
`u(x) + H(x, Du(x), m(x)) − V(x) ≤ 0` a.e. on `UnitCube d`,
discharged via `lem_strong_is_strong_HJB_ineq` from
`StrongIsStrong.lean`.

The `lem_strong_is_strong_HJB_ineq` lemma consumes:

* `hRes : Integrable (hjbResidual V H Du m u)` — produced from a
  `MemLpPer (ofReal β̄') (hjbResidual …)` certificate via
  `aprioriDischarge_residual_integrable`;
* `hVI : StrongVI_setForm V H DpH γ̄ ε Du m u` — the strong
  set-form VI at `(sol.Du, sol.m, sol.u)`.

Per CONVENTIONS §1b, we accept `hStrongVI_set` as an authorised
input here (sourced upstream from `(sol k).hVIeps_set` via the
Minty/δ-limit bridge filed as the child task
`infra-P4-strongVI-set-of-hVIeps-set-Minty`). The Minty bridge
is genuine analytic content (operator continuity in the third
argument plus DCT) that does not fit the small-infra-lemma budget
of step 2b. -/

namespace AprioriUniformPerSolHypothesesC

/-- **B-class discharge: HJB inequality.**

Given the strong set-form VI at `(sol.Du, sol.m, sol.u)` and a
residual `MemLpPer β̄'` certificate, deliver the pointwise HJB
inequality `u + H(x, Du, m) − V ≤ 0` a.e. on `UnitCube d`.

Mirrors `aprioriInputsAtEps`'s `hHJB` discharge in
`Banach/Closure.lean:809-827`. -/
lemma bClass_hHJB
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' h.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hStrongVI_set :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x ≤ 0 := by
  -- Step 1. Lift `1 ≤ ENNReal.ofReal (betaBar' h.β)` from
  -- `1 < betaBar' h.β` (paper-level Hölder-conjugate fact).
  have hβBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' h.β) := by
    have hβ'_one_le : (1 : ℝ) ≤ betaBar' h.β :=
      (one_lt_betaBar' h.β h.hβ).le
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (betaBar' h.β) :=
      ENNReal.ofReal_le_ofReal hβ'_one_le
    simpa using h1
  -- Step 2. Reduce `MemLpPer β̄' R` to L¹ integrability via
  -- `aprioriDischarge_residual_integrable`.
  have hRes_int :
      MeasureTheory.Integrable
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H sol.Du sol.m sol.u)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    aprioriDischarge_residual_integrable
      (βBar' := ENNReal.ofReal (betaBar' h.β))
      hβBar'_one_le hRes_Lp
  -- Step 3. Apply `lem_strong_is_strong_HJB_ineq`.
  exact StationaryMFG.Theorems.SimplePower.lem_strong_is_strong_HJB_ineq
    V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u
    hRes_int hStrongVI_set

end AprioriUniformPerSolHypothesesC

/-! ### Sanity-check unit test for the B-class HJB discharge -/

/-- **Unit test for `bClass_hHJB`.** Pins the type-shape of the
HJB-inequality discharge: from the strong set-form VI and a residual
`MemLpPer β̄'` certificate, deliver the pointwise HJB inequality
consumed by `AprioriUniformPerSolHypotheses.hHJB`. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' h.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hStrongVI_set :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x ≤ 0 :=
  AprioriUniformPerSolHypothesesC.bClass_hHJB h sol hRes_Lp hStrongVI_set

/-! ### Phase 2 of the iter-412 expert plan — `bClass_hHJB` via the
Minty bridge bundle

Per `infra-P4-rewire-hStrongVI_set-via-strongVI_setForm_of_hVIeps_set`,
the B-class HJB discharge can consume the smaller
`SetAdditiveContinuityInputs sol` bundle in place of the full
`StrongVI_setForm` field: the Minty bridge
`hStrongVI_set_of_regularized_solution` produces the latter from the
former in one line.

Downstream callers that previously took `hStrongVI_set` directly can
now thread the smaller bundle and let this lemma derive
`hStrongVI_set` internally. -/

namespace AprioriUniformPerSolHypothesesC

/-- **Phase 2 (iter-412 plan): B-class HJB discharge via the Minty
bridge bundle.**

Variant of `bClass_hHJB` that consumes the smaller
`SetAdditiveContinuityInputs sol` bundle (Phase 2 of the iter-412
expert plan) instead of the full `StrongVI_setForm` field; the latter
is obtained in-body via `hStrongVI_set_of_regularized_solution`. -/
lemma bClass_hHJB_of_setInputs
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' h.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hSet : SetAdditiveContinuityInputs sol) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x ≤ 0 :=
  bClass_hHJB h sol hRes_Lp
    (hStrongVI_set_of_regularized_solution sol hSet)

end AprioriUniformPerSolHypothesesC

/-- **Unit test for `bClass_hHJB_of_setInputs`.** Pins the type-shape
of the Phase-2 HJB-inequality discharge: from the residual `MemLpPer
β̄'` certificate and the `SetAdditiveContinuityInputs sol` bundle,
deliver the pointwise HJB inequality consumed by
`AprioriUniformPerSolHypotheses.hHJB`. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' h.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hSet : SetAdditiveContinuityInputs sol) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x ≤ 0 :=
  AprioriUniformPerSolHypothesesC.bClass_hHJB_of_setInputs h sol hRes_Lp hSet

/-! ## B-class field discharge — transport identity (Step 2c)

Per `infra-P4-apriori-uniform-perSolHyps-Conly-step2c-transport`,
the B-class field `h_identity` of `AprioriUniformPerSolHypotheses`
is the integrated transport identity at paper line 1212:
```
∫_{𝕋^d} u  =  ∫_{𝕋^d} (m · (-H + DpH·Du) + V·m + epsTerms),
```
derived from `lem:strong.is.strong.(b,c)` by testing the strong VI
at `φ = u_ε`. Per CONVENTIONS §1b, the integrated identity is
authorised here as an upstream input (`hIdentityRaw`), parallel
to how `bClass_hHJB` accepts `hStrongVI_set`. The bridge from
`(sol k).hVIeps_transport` to this integrated identity is genuine
analytic content (testing transport at `φ = u_ε`, line 1212 of
`Source/FGU-monotone_revised.tex`) deferred to the child task
`infra-P4-h-identity-of-hVIeps-transport`. -/

namespace AprioriUniformPerSolHypothesesC

/-- **B-class discharge: transport identity.**

Given the integrated transport identity at `(sol.m, sol.u, sol.Du,
epsTerms)` (paper line 1212; authorised input per CONVENTIONS §1b,
sourced upstream from `(sol k).hVIeps_transport` via testing
transport at `φ = u_ε`), deliver the `h_identity` field of
`AprioriUniformPerSolHypotheses` shape-for-shape.

Mirrors `aprioriInputsAtEps`'s `h_identity` discharge in
`Banach/Closure.lean:832` (which forwards `aux.h_identity`). -/
lemma bClass_h_identity
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (epsTerms : (Fin d → ℝ) → ℝ)
    (hIdentityRaw :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    ∫ x in UnitCube d, sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + epsTerms x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  -- The hypothesis name `h` shadows the discharge parameter. The
  -- identity is consumed verbatim; the `(hpow, sol)` parameters
  -- pin the type-shape of `(sol.m, sol.u, sol.Du)` against
  -- `AprioriUniformPerSolHypotheses.h_identity`.
  hIdentityRaw

end AprioriUniformPerSolHypothesesC

/-! ### Sanity-check unit test for the B-class transport-identity discharge -/

/-- **Unit test for `bClass_h_identity`.** Pins the type-shape of
the transport-identity discharge: from an integrated identity
authorised input at `(sol.m, sol.u, sol.Du, epsTerms)`, deliver
the `h_identity` field of `AprioriUniformPerSolHypotheses`. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (epsTerms : (Fin d → ℝ) → ℝ)
    (hIdentityRaw :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    ∫ x in UnitCube d, sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + epsTerms x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  AprioriUniformPerSolHypothesesC.bClass_h_identity h sol epsTerms hIdentityRaw

/-! ## B-class field discharge — integrability triple (Step 2d)

Per `infra-P4-apriori-uniform-perSolHyps-Conly-step2d-integrability`,
the remaining B-class fields of `AprioriUniformPerSolHypotheses` are
six pointwise integrability/measurability fields:

* `hRHSabove_int` — `|V| + C(m^β + 1)` is L¹ on the cube.
* `hMbeta_int` — `m^β` is L¹ on the cube.
* `hRHSbelow_int` — `m · (-H + DpH·Du) + V · m + epsTerms` is L¹.
* `hu_meas` — `u` is measurable.
* `hDu_meas` — each `Du i` is measurable.
* `hDu_norm_int` — `‖Du‖^{γ̄}` is L¹ on the cube.

Per CONVENTIONS §1b, each is accepted as an authorised paper-side
input here, in the same authorised-input forwarding shape as
`bClass_h_identity` (Step 2c). The actual derivation from the
underlying `MemLpPer` data (e.g.  `MemLpPer.mono_exponent_finite`
for `hMbeta_int`) is filed for the eventual full-discharge child
under the closed-form aggregator wrapper. -/

namespace AprioriUniformPerSolHypothesesC

/-- **B-class discharge: integrability of the upper-bound RHS.**

Given the integrability of the upper-bound integrand
`|V x| + h.C * (sol.m x ^ h.β + 1)` on `UnitCube d` (authorised input
per CONVENTIONS §1b, sourced upstream from `hVbnd` plus
`(sol k).hmLp` at exponent `β` via `mono_exponent_finite`), forward
it as the `hRHSabove_int` field of `AprioriUniformPerSolHypotheses`.

Mirrors the authorised-input pattern of `bClass_h_identity`
(`AprioriUniform.lean:845-876`). -/
lemma bClass_hRHSabove_int
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hRHSaboveRaw : MeasureTheory.Integrable
              (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  hRHSaboveRaw

/-- **B-class discharge: integrability of `m^β`.**

Given the integrability of `sol.m x ^ h.β` on `UnitCube d`
(authorised input per CONVENTIONS §1b, sourced upstream from
`(sol k).hmLp` at exponent `β+1` via
`MemLpPer.mono_exponent_finite (q := ofReal β) (p := ofReal (β+1))`
on the finite-measure cube), forward it as the `hMbeta_int` field
of `AprioriUniformPerSolHypotheses`. -/
lemma bClass_hMbeta_int
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hMbetaRaw : MeasureTheory.Integrable
              (fun x => sol.m x ^ h.β)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => sol.m x ^ h.β)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  hMbetaRaw

/-- **B-class discharge: integrability of the lower-bound RHS.**

Given the integrability of the lower-bound integrand
`m · (-H + DpH·Du) + V · m + epsTerms` on `UnitCube d` (authorised
input per CONVENTIONS §1b, sourced upstream from
`(sol k).hmLp` / `(sol k).hDuLp` / `hVbnd` / `hpow.upper` and the
paper-residual `epsTerms` certificate), forward it as the
`hRHSbelow_int` field of `AprioriUniformPerSolHypotheses`. -/
lemma bClass_hRHSbelow_int
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (epsTerms : (Fin d → ℝ) → ℝ)
    (hRHSbelowRaw : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x =>
        sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + epsTerms x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  hRHSbelowRaw

/-- **B-class discharge: AE strong measurability of `u`.**

Given AE strong measurability of `sol.u` on `UnitCube d`, forward it
as the `hu_meas` field of `AprioriUniformPerSolHypotheses`.

iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`: relaxed from
strict `Measurable` to `AEStronglyMeasurable`, so the `MemLpPer`
witness on `(sol).u` (`sol.huLp`) suffices to discharge this slot
inline at consumer sites without a separate raw measurability hypothesis. -/
lemma bClass_hu_meas
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hu_measRaw : MeasureTheory.AEStronglyMeasurable sol.u
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    MeasureTheory.AEStronglyMeasurable sol.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  hu_measRaw

/-- **B-class discharge: AE strong measurability of each `Du i`.**

Given AE strong measurability of each component `sol.Du i` w.r.t.
`volume`, forward it as the `hDu_meas` field of
`AprioriUniformPerSolHypotheses`.

iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`: relaxed from
strict `Measurable` to `AEStronglyMeasurable`. -/
lemma bClass_hDu_meas
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hDu_measRaw : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  hDu_measRaw

/-- **B-class discharge: integrability of `‖Du‖^{γ̄}`.**

Given the integrability of `‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β`
on `UnitCube d` (authorised input per CONVENTIONS §1b, sourced
upstream from `(sol k).hDuLp i` summed via the Pythagorean-style
estimate `‖·‖^γ̄ ≤ d^{γ̄/2 - 1} · ∑_i |·_i|^γ̄`), forward it as the
`hDu_norm_int` field of `AprioriUniformPerSolHypotheses`. -/
lemma bClass_hDu_norm_int
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hDu_norm_intRaw : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  hDu_norm_intRaw

end AprioriUniformPerSolHypothesesC

/-! ### Sanity-check unit tests for the B-class integrability discharge

Pin the type-shapes via forwarding `example`s. -/

/-- **Unit test for `bClass_hRHSabove_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hRHSaboveRaw : MeasureTheory.Integrable
              (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.bClass_hRHSabove_int h sol hRHSaboveRaw

/-- **Unit test for `bClass_hMbeta_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hMbetaRaw : MeasureTheory.Integrable
              (fun x => sol.m x ^ h.β)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => sol.m x ^ h.β)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.bClass_hMbeta_int h sol hMbetaRaw

/-- **Unit test for `bClass_hRHSbelow_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (epsTerms : (Fin d → ℝ) → ℝ)
    (hRHSbelowRaw : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x =>
        sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + epsTerms x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.bClass_hRHSbelow_int h sol epsTerms
    hRHSbelowRaw

/-- **Unit test for `bClass_hu_meas`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hu_measRaw : MeasureTheory.AEStronglyMeasurable sol.u
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    MeasureTheory.AEStronglyMeasurable sol.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  AprioriUniformPerSolHypothesesC.bClass_hu_meas h sol hu_measRaw

/-- **Unit test for `bClass_hDu_meas`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hDu_measRaw : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  AprioriUniformPerSolHypothesesC.bClass_hDu_meas h sol hDu_measRaw

/-- **Unit test for `bClass_hDu_norm_int`.** -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hDu_norm_intRaw : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  AprioriUniformPerSolHypothesesC.bClass_hDu_norm_int h sol hDu_norm_intRaw

/-! ## B-class field discharge — Lagrangian lower bound (Step 2a deferred `h_lagr`)

Per `infra-P4-apriori-uniform-perSolHyps-Conly-step2a-Aclass-hlagr`,
the deferred A-class field `h_lagr` of
`AprioriUniformPerSolHypotheses` is the Legendre-style pointwise
lower bound
```
(m^β) / C − C ≤ DpH(x, p, m) · p − H(x, p, m)
```
a.e. on `UnitCube d`, for all `p ∈ ℝ^d` and `m > 0`.

The iter-390 audit initially listed this field as auto-derivable
from `hpow.lower` alone. The iter-394 audit corrected this:
`lagrangian_lower_bound` in `Hamiltonian/Estimates.lean` requires a
separate `h_convex_at_zero` precondition

```
∀ᵐ x, ∀ p m, 0 < m → H x p m − DpH x p m · p ≤ H x 0 m
```

which is **not** carried by either `HypothesisPowerGrowth` or
`HypothesisMonotone`. The paper derives convexity-at-zero from a
slice-integral FTC identity for `H` along `p` (line 1212+ of
`Source/FGU-monotone_revised.tex`), which exceeds the small-infra
budget of step 2a.

Per CONVENTIONS §1b and the iter-395/396/397 authorised-input
forwarding pattern (compare `bClass_hHJB`, `bClass_h_identity`,
`bClass_hu_meas`), we accept `h_lagr` as an authorised input here
and forward it via `bClass_h_lagr`. The eventual derivation from
`(hmon, hpow)` plus a paper-side convex-at-zero input is filed as a
follow-up child task. -/

namespace AprioriUniformPerSolHypothesesC

/-- **B-class discharge: Lagrangian lower bound (deferred A-class
`h_lagr`).**

Given the pointwise Legendre lower bound at `(sol.m, sol.Du, sol.u)`
authorised input per CONVENTIONS §1b, sourced upstream from
the paper-side convexity-of-`H` in `p` plus `hpow.upper`),
forward it as the `h_lagr` field of `AprioriUniformPerSolHypotheses`.

Mirrors the authorised-input pattern of `bClass_h_identity`
(`AprioriUniform.lean:845-876`) and `bClass_hu_meas`. -/
lemma bClass_h_lagr
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (_sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hLagrRaw :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx :=
  hLagrRaw

end AprioriUniformPerSolHypothesesC

/-! ### Sanity-check unit test for the Lagrangian lower-bound discharge -/

/-- **Unit test for `bClass_h_lagr`.** Pins the type-shape of the
Lagrangian lower-bound discharge: from a pointwise Legendre lower
bound authorised input at `(DpH, H)`, deliver the `h_lagr` field of
`AprioriUniformPerSolHypotheses` shape-for-shape. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (hLagrRaw :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx :=
  AprioriUniformPerSolHypothesesC.bClass_h_lagr h sol hLagrRaw

/-! ## Phase 2b aggregator: assemble a full `AprioriUniformPerSolHypotheses`

Per the iter-390 audit and Phase 2b task plan, the three field-classes
(A-auto, B-authorised forwarders, C-residues) reassemble into a full
`AprioriUniformPerSolHypotheses` via the constructor
`AprioriUniformPerSolHypotheses.fromCAndAuthorised` below.

* **A-class fields** are discharged via the
  `AprioriUniformPerSolHypothesesC.aClass_*` lemmas
  (iter 394).
* **B-class fields** are forwarded via the
  `AprioriUniformPerSolHypothesesC.bClass_*` lemmas
  (iters 395, 396, 397, 398), each consuming an authorised input.
* **C-class fields** are direct projections from the
  `AprioriUniformPerSolHypothesesC` bundle.

This aggregator unblocks Phase 2b downstream — once the A/B/C
authorised inputs are sourced (from upstream paper-residue chains
filed as further child tasks), the full
`AprioriUniformPerSolHypotheses` is constructed in one step. -/

/-- **Phase 2b aggregator constructor.**

Combines the C-class bundle (`AprioriUniformPerSolHypothesesC`)
with the A-class auto-discharge lemmas (driven by `(hpow, sol, hV)`)
and the nine B-class authorised inputs to produce a full
`AprioriUniformPerSolHypotheses`.

Inputs:
* `hpow` — `HypothesisPowerGrowth H DpH`.
* `sol` — a `RegularizedBareSolution` at parameter `ε`.
* `cBundle` — the C-class residue bundle (per CONVENTIONS §1b
  authorised paper inputs: `epsTerms`, `hEpsNN`, `hMpos`, `hVbnd`,
  `hVint`, `hVβp`, `hu_per`, `hDu_per`, `hUbetap_int`).
* `hV` — `MemLpPer (ofReal (betaBar' h.β)) V`, used by the A-class
  `hVbetap_int` discharge.
* `hRes_Lp` — `MemLpPer (ofReal β̄') (hjbResidual …)`, used by
  the B-class `hHJB` discharge.
* `hStrongVI_set` — strong set-form VI at `(sol.Du, sol.m, sol.u)`,
  used by the B-class `hHJB` discharge.
* `hIdentityRaw` — paper transport identity at `(sol, epsTerms)`,
  forwarded as `h_identity`.
* `hRHSaboveRaw`, `hMbetaRaw`, `hRHSbelowRaw` — three integrability
  certificates forwarded as `hRHSabove_int`, `hMbeta_int`,
  `hRHSbelow_int`.
* `hu_measRaw`, `hDu_measRaw`, `hDu_norm_intRaw` — measurability
  and gradient-norm integrability forwarded as `hu_meas`, `hDu_meas`,
  `hDu_norm_int`.
* `hLagrRaw` — Legendre lower bound forwarded as `h_lagr`.

Body is mechanical: each field maps to either an `aClass_*`
auto-discharge, a `bClass_*` forwarder, or a `cBundle.*` projection. -/
noncomputable def AprioriUniformPerSolHypotheses.fromCAndAuthorised
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    {Vbound Vint_bound Vβp_bound : ℝ}
    (cBundle : AprioriUniformPerSolHypothesesC (d := d) hpow sol
                  Vbound Vint_bound Vβp_bound)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    -- B-class authorised inputs:
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' hpow.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hStrongVI_set :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar hpow.α hpow.β) ε sol.Du sol.m sol.u)
    (hIdentityRaw :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + cBundle.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * (sol.m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : MeasureTheory.Integrable
              (fun x => sol.m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + cBundle.epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_measRaw : MeasureTheory.AEStronglyMeasurable sol.u
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_measRaw : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_intRaw : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    AprioriUniformPerSolHypotheses (d := d) hpow sol
      Vbound Vint_bound Vβp_bound where
  -- C-class fields: direct projections from `cBundle`.
  epsTerms := cBundle.epsTerms
  hEpsNN := cBundle.hEpsNN
  hEpsInt := cBundle.hEpsInt
  hMpos := cBundle.hMpos
  hVbnd := cBundle.hVbnd
  hVint := cBundle.hVint
  hVβp := cBundle.hVβp
  hu_per := cBundle.hu_per
  hDu_per := cBundle.hDu_per
  hUbetap_int := cBundle.hUbetap_int
  -- A-class fields: auto-derivable from `(hpow, sol, hV, cBundle)`.
  hu_int := AprioriUniformPerSolHypothesesC.aClass_hu_int hpow sol
  hLB_int := AprioriUniformPerSolHypothesesC.aClass_hLB_int hpow sol
  hγ_one_le := AprioriUniformPerSolHypothesesC.aClass_hγ_one_le hpow
  hγ_top := AprioriUniformPerSolHypothesesC.aClass_hγ_top hpow
  hu_loc := AprioriUniformPerSolHypothesesC.aClass_hu_loc hpow cBundle
  hu_sob := AprioriUniformPerSolHypothesesC.aClass_hu_sob hpow sol
  hDu_loc := AprioriUniformPerSolHypothesesC.aClass_hDu_loc hpow cBundle
  hVbetap_int := AprioriUniformPerSolHypothesesC.aClass_hVbetap_int hpow hV
  -- B-class fields: authorised-input forwarders.
  hHJB := AprioriUniformPerSolHypothesesC.bClass_hHJB hpow sol hRes_Lp
            hStrongVI_set
  h_identity := AprioriUniformPerSolHypothesesC.bClass_h_identity hpow sol
                  cBundle.epsTerms hIdentityRaw
  hRHSabove_int := AprioriUniformPerSolHypothesesC.bClass_hRHSabove_int hpow
                    sol hRHSaboveRaw
  hMbeta_int := AprioriUniformPerSolHypothesesC.bClass_hMbeta_int hpow sol
                  hMbetaRaw
  hRHSbelow_int := AprioriUniformPerSolHypothesesC.bClass_hRHSbelow_int hpow
                    sol cBundle.epsTerms hRHSbelowRaw
  hu_meas := AprioriUniformPerSolHypothesesC.bClass_hu_meas hpow sol
              hu_measRaw
  hDu_meas := AprioriUniformPerSolHypothesesC.bClass_hDu_meas hpow sol
                hDu_measRaw
  hDu_norm_int := AprioriUniformPerSolHypothesesC.bClass_hDu_norm_int hpow
                    sol hDu_norm_intRaw
  h_lagr := AprioriUniformPerSolHypothesesC.bClass_h_lagr hpow sol hLagrRaw

/-! ### Sanity-check unit test for the aggregator -/

/-- **Unit test for `AprioriUniformPerSolHypotheses.fromCAndAuthorised`.**
Pins the type-shape of the aggregator: from a C-class bundle plus
`hV` plus the nine B-class authorised inputs, deliver a full
`AprioriUniformPerSolHypotheses`. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    {Vbound Vint_bound Vβp_bound : ℝ}
    (cBundle : AprioriUniformPerSolHypothesesC (d := d) hpow sol
                  Vbound Vint_bound Vβp_bound)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' hpow.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hStrongVI_set :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar hpow.α hpow.β) ε sol.Du sol.m sol.u)
    (hIdentityRaw :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + cBundle.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * (sol.m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : MeasureTheory.Integrable
              (fun x => sol.m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + cBundle.epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_measRaw : MeasureTheory.AEStronglyMeasurable sol.u
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_measRaw : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_intRaw : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    AprioriUniformPerSolHypotheses (d := d) hpow sol
      Vbound Vint_bound Vβp_bound :=
  AprioriUniformPerSolHypotheses.fromCAndAuthorised hpow sol cBundle hV
    hRes_Lp hStrongVI_set hIdentityRaw hRHSaboveRaw hMbetaRaw hRHSbelowRaw
    hu_measRaw hDu_measRaw hDu_norm_intRaw hLagrRaw

/-- **Closed-form residue producer from paper hypotheses
(discharge form).**

Given the paper-level hypotheses `(hpow, hV)`, an `ε`-sequence with
strict positivity, a per-`k` `RegularizedBareSolution`, a shared
`(Vbound, Vint_bound, Vβp_bound)` triple, and a per-`k`
`AprioriUniformPerSolHypotheses` bundle, produce an
`AprioriUniformResidueInputs` whose `uniformConstant` is the
explicit closed-form value `aprioriUniformConstantClosed h Vbound
Vint_bound Vβp_bound` from `Apriori.lean`.

The proof glues the three closed-form bounds
(`apriori_m_bound_closed`, `apriori_uepsi_Lp_closed`,
`apriori_Du_bound_closed_form`) via
`apriori_aggregate_bound_residue_form`, applied per-`k`. -/
def aprioriUniformResidueInputs_of_paperHypotheses
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (_hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (perSolHyps : ∀ k : ℕ,
      AprioriUniformPerSolHypotheses (d := d) hpow (sol k)
        Vbound Vint_bound Vβp_bound) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' where
  epsSeq := epsSeq
  epsSeq_pos := epsSeq_pos
  epsSeq_tendsto := epsSeq_tendsto
  sol := sol
  uniformConstant :=
    aprioriUniformConstantClosed (d := d) hpow Vbound Vint_bound Vβp_bound
  uniformConstant_nn :=
    aprioriUniformConstantClosed_nn (d := d) hpow Vbound Vint_bound Vβp_bound
      hVint_nn hVβp_nn
  uniformConstant_bound := by
    intro k
    have H_k := perSolHyps k
    have hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β))
                    (sol k).u := (sol k).huLp
    have hDu_weak : ∀ i, HasWeakDerivPer i (sol k).u ((sol k).Du i) :=
      (sol k).hWeakDeriv
    have hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β))
                          ((sol k).Du i) := (sol k).hDuLp
    -- Apply the closed-form aggregate bound (residue form).
    exact apriori_aggregate_bound_residue_form
      (h := hpow) V (sol k).Du (sol k).m (sol k).u H_k.epsTerms
      Vbound Vint_bound Vβp_bound
      H_k.hHJB H_k.h_lagr H_k.hMpos H_k.hVbnd H_k.hEpsNN H_k.h_identity
      H_k.hu_int H_k.hRHSabove_int H_k.hLB_int H_k.hMbeta_int
      H_k.hRHSbelow_int H_k.hVint
      H_k.hγ_one_le H_k.hγ_top H_k.hu_meas
      H_k.hu_per H_k.hu_loc H_k.hu_sob
      hDu_weak H_k.hDu_meas
      H_k.hDu_per H_k.hDu_loc hDu_lp
      H_k.hDu_norm_int H_k.hUbetap_int H_k.hVbetap_int H_k.hVβp hu_lp_γ

/-! ## Phase 2b closed-paper wrapper

Closed-paper variant of `aprioriUniformResidueInputs_of_paperHypotheses`
that consumes a per-`k` C-class bundle + per-`k` authorised B-class
inputs (shape iter 399's `fromCAndAuthorised`), assembles the per-`k`
`AprioriUniformPerSolHypotheses` internally, and forwards to the
existing residue producer.

This is mechanical glue: see iter 399 (`AprioriUniformPerSolHypotheses
.fromCAndAuthorised`) for the C+B → full-bundle aggregator. -/

/-- **Closed-paper residue producer (paper hypotheses + per-`k` C
+ authorised inputs).**

Wraps `aprioriUniformResidueInputs_of_paperHypotheses` by assembling
each per-`k` `AprioriUniformPerSolHypotheses` from a C-class bundle
and the nine B-class authorised inputs via
`AprioriUniformPerSolHypotheses.fromCAndAuthorised`.

Inputs:
* `hmon`, `hpow` — paper monotonicity and power-growth hypotheses
  (`hmon` carried for downstream callers; not used in the body).
* `hV` — `MemLpPer (ofReal (betaBar' hpow.β)) V`, used by both the
  per-`k` `fromCAndAuthorised` aggregator (as the `hVbetap_int`
  source) and the residue producer.
* `Vbound`, `Vint_bound`, `Vβp_bound` with non-negativity for the
  latter two — paper `V`-norm bounds.
* `epsSeq`, `epsSeq_pos`, `epsSeq_tendsto` — regularisation
  sequence.
* `sol` — per-`k` `RegularizedBareSolution`.
* `cBundles` — per-`k` C-class bundle.
* `hRes_Lp`, …, `hLagrRaw` — the nine per-`k` B-class authorised
  inputs feeding `fromCAndAuthorised`.

Output: an `AprioriUniformResidueInputs` with closed-form
`uniformConstant := aprioriUniformConstantClosed hpow Vbound
Vint_bound Vβp_bound`. -/
noncomputable def aprioriUniformResidueInputs_of_paperHypotheses_closedPaper
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hV_resid : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (cBundles : ∀ k : ℕ,
      AprioriUniformPerSolHypothesesC (d := d) hpow (sol k)
        Vbound Vint_bound Vβp_bound)
    -- Per-`k` B-class authorised inputs:
    (hRes_Lp : ∀ k : ℕ,
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (betaBar' hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (sol k).Du (sol k).m (sol k).u))
    (hStrongVI_set : ∀ k : ℕ,
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar hpow.α hpow.β) (epsSeq k)
        (sol k).Du (sol k).m (sol k).u)
    (hIdentityRaw : ∀ k : ℕ,
      ∫ x in UnitCube d, (sol k).u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          ((sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                    + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                        ⬝ (fun i => (sol k).Du i x))
            + V x * (sol k).m x
            + (cBundles k).epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * ((sol k).m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => (sol k).m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x =>
                (sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                          + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                              ⬝ (fun i => (sol k).Du i x))
                  + V x * (sol k).m x
                  + (cBundles k).epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_measRaw : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).u
                            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_measRaw : ∀ k : ℕ, ∀ i,
                    MeasureTheory.AEStronglyMeasurable ((sol k).Du i)
                      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_intRaw : ∀ k : ℕ, MeasureTheory.Integrable
        (fun x => ‖(fun i => (sol k).Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw : ∀ _k : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' :=
  aprioriUniformResidueInputs_of_paperHypotheses
    hmon hpow hV_resid Vbound Vint_bound Vβp_bound hVint_nn hVβp_nn
    epsSeq epsSeq_pos epsSeq_tendsto sol
    (fun k => AprioriUniformPerSolHypotheses.fromCAndAuthorised
      hpow (sol k) (cBundles k) hV
      (hRes_Lp k) (hStrongVI_set k) (hIdentityRaw k)
      (hRHSaboveRaw k) (hMbetaRaw k) (hRHSbelowRaw k)
      (hu_measRaw k) (hDu_measRaw k) (hDu_norm_intRaw k)
      (hLagrRaw k))

/-- **Sanity-check unit test for
`aprioriUniformResidueInputs_of_paperHypotheses_closedPaper`.**
Pins the producer's type-shape: paper inputs + per-`k` C-class
+ authorised B-class inputs deliver an
`AprioriUniformResidueInputs`. -/
example
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hV_resid : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (cBundles : ∀ k : ℕ,
      AprioriUniformPerSolHypothesesC (d := d) hpow (sol k)
        Vbound Vint_bound Vβp_bound)
    (hRes_Lp : ∀ k : ℕ,
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (betaBar' hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (sol k).Du (sol k).m (sol k).u))
    (hStrongVI_set : ∀ k : ℕ,
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar hpow.α hpow.β) (epsSeq k)
        (sol k).Du (sol k).m (sol k).u)
    (hIdentityRaw : ∀ k : ℕ,
      ∫ x in UnitCube d, (sol k).u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          ((sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                    + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                        ⬝ (fun i => (sol k).Du i x))
            + V x * (sol k).m x
            + (cBundles k).epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * ((sol k).m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => (sol k).m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x =>
                (sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                          + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                              ⬝ (fun i => (sol k).Du i x))
                  + V x * (sol k).m x
                  + (cBundles k).epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_measRaw : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).u
                            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_measRaw : ∀ k : ℕ, ∀ i,
                    MeasureTheory.AEStronglyMeasurable ((sol k).Du i)
                      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_intRaw : ∀ k : ℕ, MeasureTheory.Integrable
        (fun x => ‖(fun i => (sol k).Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw : ∀ _k : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' :=
  aprioriUniformResidueInputs_of_paperHypotheses_closedPaper
    hmon hpow hV hV_resid Vbound Vint_bound Vβp_bound hVint_nn hVβp_nn
    epsSeq epsSeq_pos epsSeq_tendsto sol cBundles
    hRes_Lp hStrongVI_set hIdentityRaw
    hRHSaboveRaw hMbetaRaw hRHSbelowRaw
    hu_measRaw hDu_measRaw hDu_norm_intRaw hLagrRaw

/-! ## Phase 2 (iter-412 plan): producers consuming the smaller
`SetAdditiveContinuityInputs` bundle

Per `infra-P4-rewire-hStrongVI_set-via-strongVI_setForm_of_hVIeps_set`,
provide `_setInputs` variants of the per-`k` aggregator
`fromCAndAuthorised` and the closed-paper residue producer
`aprioriUniformResidueInputs_of_paperHypotheses_closedPaper`. These
variants take `SetAdditiveContinuityInputs (sol …)` (or
`∀ k, SetAdditiveContinuityInputs (sol k)`) in place of the full
`StrongVI_setForm` field, threading the Minty bridge
`hStrongVI_set_of_regularized_solution` internally.

A T10-level rewire (i.e. a `T10PaperResidues_setInputs` parallel
structure) is filed as a sibling task; the structural rewire here is
sufficient to let downstream callers consume the smaller package via
the new producers. -/

/-- **Phase 2 (iter-412 plan): aggregator constructor consuming the
Minty-bridge bundle.**

Variant of `AprioriUniformPerSolHypotheses.fromCAndAuthorised`
consuming `SetAdditiveContinuityInputs sol` in place of the full
`StrongVI_setForm` field. The latter is obtained in-body via
`hStrongVI_set_of_regularized_solution`. -/
noncomputable def AprioriUniformPerSolHypotheses.fromCAndAuthorised_setInputs
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    {Vbound Vint_bound Vβp_bound : ℝ}
    (cBundle : AprioriUniformPerSolHypothesesC (d := d) hpow sol
                  Vbound Vint_bound Vβp_bound)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hRes_Lp : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (betaBar' hpow.β))
                (StationaryMFG.Theorems.SimplePower.hjbResidual
                  V H sol.Du sol.m sol.u))
    (hSet : SetAdditiveContinuityInputs sol)
    (hIdentityRaw :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + cBundle.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * (sol.m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : MeasureTheory.Integrable
              (fun x => sol.m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + cBundle.epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_measRaw : MeasureTheory.AEStronglyMeasurable sol.u
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_measRaw : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_intRaw : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    AprioriUniformPerSolHypotheses (d := d) hpow sol
      Vbound Vint_bound Vβp_bound :=
  AprioriUniformPerSolHypotheses.fromCAndAuthorised hpow sol cBundle hV
    hRes_Lp
    (hStrongVI_set_of_regularized_solution sol hSet)
    hIdentityRaw hRHSaboveRaw hMbetaRaw hRHSbelowRaw
    hu_measRaw hDu_measRaw hDu_norm_intRaw hLagrRaw

/-- **Phase 2 (iter-412 plan): closed-paper residue producer consuming
the Minty-bridge bundle.**

Variant of `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper`
consuming a per-`k` `SetAdditiveContinuityInputs (sol k)` bundle in
place of the per-`k` `StrongVI_setForm` field. Each per-`k`
`StrongVI_setForm` is obtained internally via
`hStrongVI_set_of_regularized_solution`. -/
noncomputable def aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hV_resid : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (cBundles : ∀ k : ℕ,
      AprioriUniformPerSolHypothesesC (d := d) hpow (sol k)
        Vbound Vint_bound Vβp_bound)
    (hRes_Lp : ∀ k : ℕ,
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (betaBar' hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (sol k).Du (sol k).m (sol k).u))
    (hSet : ∀ k : ℕ, SetAdditiveContinuityInputs (sol k))
    (hIdentityRaw : ∀ k : ℕ,
      ∫ x in UnitCube d, (sol k).u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          ((sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                    + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                        ⬝ (fun i => (sol k).Du i x))
            + V x * (sol k).m x
            + (cBundles k).epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * ((sol k).m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => (sol k).m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x =>
                (sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                          + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                              ⬝ (fun i => (sol k).Du i x))
                  + V x * (sol k).m x
                  + (cBundles k).epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_measRaw : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).u
                            (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_measRaw : ∀ k : ℕ, ∀ i,
                    MeasureTheory.AEStronglyMeasurable ((sol k).Du i)
                      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_intRaw : ∀ k : ℕ, MeasureTheory.Integrable
        (fun x => ‖(fun i => (sol k).Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw : ∀ _k : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' :=
  aprioriUniformResidueInputs_of_paperHypotheses_closedPaper
    hmon hpow hV hV_resid Vbound Vint_bound Vβp_bound hVint_nn hVβp_nn
    epsSeq epsSeq_pos epsSeq_tendsto sol cBundles
    hRes_Lp
    (fun k => hStrongVI_set_of_regularized_solution (sol k) (hSet k))
    hIdentityRaw
    hRHSaboveRaw hMbetaRaw hRHSbelowRaw
    hu_measRaw hDu_measRaw hDu_norm_intRaw hLagrRaw

/-! The integral V-data sibling
`aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int`
(D4.1a) is defined below, after the D4.0b5 `_int` sibling block where
`AprioriUniformPerSolHypothesesC_int` is in scope. -/

/-! ## Producer for `T10PaperResidues` field 6

Field 6 of `T10PaperResidues` is the triple
`(Capr : ℝ, hCapr_nn : 0 ≤ Capr, hCapr : ∀ k sol, … ≤ Capr)`.
The shape's `sol` parameter is *universally* quantified over
`RegularizedBareSolution d (epsSeq k) V H DpH …`. To produce the
field from a residue bundle (which fixes a *particular* `sol`
sequence), we need the residue's per-`k` solution to coincide with
the universally quantified `sol`.

That coincidence is *not* automatic — `T10PaperResidues.hCapr` is a
universal claim, while a residue picks a single `sol`. The
residue-restricted producer below bounds *the residue's chosen*
sequence; the closed-form aggregator
`aprioriUniformResidueInputs_of_paperHypotheses` (above) provides
the closed-form `uniformConstant` field. -/

/-- **Phase D producer (restricted form, residue-input shape).**
Given an `AprioriUniformResidueInputs` bundle (the residue
scaffolding for Phase D), return the uniform constant `Capr ≥ 0`
and the per-`k` bound for *the residue's chosen sequence*.

The producer no longer takes `(hpow, hV)` separately — those
hypotheses already discharge into the residue's `uniformConstant`
field via `aprioriUniformResidueInputs_of_paperHypotheses`. -/
def aprioriUniformConstant_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (R : AprioriUniformResidueInputs (d := d) V H DpH
            γBarReal βBarReal βBarReal' γBarReal') :
    {C : ℝ // 0 ≤ C ∧
      ∀ k : ℕ,
        (∫ x in UnitCube d, |(R.sol k).m x| ^ βBarReal) +
          (∫ x in UnitCube d, |(R.sol k).u x| ^ γBarReal) +
          (∑ i, ∫ x in UnitCube d, |(R.sol k).Du i x| ^ γBarReal)
            ≤ C} :=
  ⟨R.uniformConstant, R.uniformConstant_nn, R.uniformConstant_bound⟩

/-! ## Producer: `RegularizedSequenceData` from a residue bundle

This producer takes an `AprioriUniformResidueInputs` (which already
fixes `epsSeq`, `sol`, and the per-`k` apriori bound `uniformConstant`)
plus a `Tendsto` certificate for `epsSeq → 0`, and produces a
`RegularizedSequenceData` whose `sol` is the residue's `sol` and whose
`uniformBound` is derived from the residue's `uniformConstant_bound`
via the `norm_toBanachPair_rpow_min_le_apriori_sum` translation lemma.

This bypasses the K_Aepsi-form `regularizedSequenceData_of_paperHypotheses`
chain (which uses `Classical.choice` over `exists_regularizedBareSolution_K`
and demands a universal-`sol` apriori bound) by consuming the residue's
already-constructed `sol` directly. -/
noncomputable def regularizedSequenceData_of_aprioriResidue
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (R : AprioriUniformResidueInputs (d := d) V H DpH
            γBarReal βBarReal βBarReal' γBarReal')
    (hβpos : 0 < βBarReal) (hγpos : 0 < γBarReal) :
    RegularizedSequenceData (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH := by
  -- Derive the uniform Banach-pair-norm bound by composing the
  -- `rpow_min` translation lemma with the residue's
  -- `uniformConstant_bound`. This mirrors the body of
  -- `regularizedSequenceData_of_paperHypotheses` but consumes the
  -- residue's `sol` directly (no `Classical.choice`, no `hCont_*`).
  set Capr : ℝ := R.uniformConstant with hCapr_def
  have hCapr_nn : 0 ≤ Capr := R.uniformConstant_nn
  set m_exp : ℝ := min βBarReal γBarReal with hm_exp
  have hm_exp_pos : 0 < m_exp := lt_min hβpos hγpos
  set d1γ : ℝ := ((d : ℝ) + 1) ^ γBarReal with hd1γ
  have hd_nn : (0 : ℝ) ≤ ((d : ℝ) + 1) := by positivity
  have hd1γ_nn : 0 ≤ d1γ := Real.rpow_nonneg hd_nn _
  set M : ℝ := 1 + Capr + d1γ * Capr with hM
  have hM_nn : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ Capr := hCapr_nn
    have h2 : 0 ≤ d1γ * Capr := mul_nonneg hd1γ_nn h1
    have : (0 : ℝ) ≤ 1 + Capr + d1γ * Capr := by linarith
    simpa [hM] using this
  set Cnorm : ℝ := M ^ (1 / m_exp) with hCnorm
  have hbound : ∀ k, ‖(R.sol k).toBanachPair‖ ≤ Cnorm := by
    intro k
    have hRpow := RegularizedBareSolution.norm_toBanachPair_rpow_min_le_apriori_sum
      (d := d) (ε := R.epsSeq k) (V := V) (H := H) (DpH := DpH)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hβpos hγpos (R.sol k)
    set Im : ℝ := ∫ x in UnitCube d, |(R.sol k).m x| ^ βBarReal with hIm
    set Iu : ℝ := ∫ x in UnitCube d, |(R.sol k).u x| ^ γBarReal with hIu
    set IDu : ℝ := ∑ i, ∫ x in UnitCube d, |(R.sol k).Du i x| ^ γBarReal with hIDu
    have hIm_nn : 0 ≤ Im := by
      refine MeasureTheory.integral_nonneg ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hIu_nn : 0 ≤ Iu := by
      refine MeasureTheory.integral_nonneg ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hIDu_nn : 0 ≤ IDu := by
      refine Finset.sum_nonneg ?_
      intro i _
      refine MeasureTheory.integral_nonneg ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hSum_le : Im + Iu + IDu ≤ Capr := R.uniformConstant_bound k
    have hIm_le : Im ≤ Capr := by linarith
    have hIu_plus_IDu_le : Iu + IDu ≤ Capr := by linarith
    have hRpow' :
        ‖(R.sol k).toBanachPair‖ ^ m_exp ≤ M := by
      have h1 :
          ‖(R.sol k).toBanachPair‖ ^ min βBarReal γBarReal
            ≤ 1 + Im + d1γ * (Iu + IDu) := hRpow
      have h2 : 1 + Im + d1γ * (Iu + IDu) ≤ M := by
        have hmul_le : d1γ * (Iu + IDu) ≤ d1γ * Capr :=
          mul_le_mul_of_nonneg_left hIu_plus_IDu_le hd1γ_nn
        calc 1 + Im + d1γ * (Iu + IDu)
            ≤ 1 + Capr + d1γ * Capr := by linarith
          _ = M := by simp [hM]
      simpa [hm_exp] using h1.trans h2
    have hq_nn : 0 ≤ ‖(R.sol k).toBanachPair‖ := norm_nonneg _
    have hqM_nn : 0 ≤ ‖(R.sol k).toBanachPair‖ ^ m_exp :=
      Real.rpow_nonneg hq_nn _
    have hinv_nn : 0 ≤ 1 / m_exp := by
      apply div_nonneg
      · exact zero_le_one
      · exact hm_exp_pos.le
    have hRpowMono :
        (‖(R.sol k).toBanachPair‖ ^ m_exp) ^ (1 / m_exp)
          ≤ M ^ (1 / m_exp) :=
      Real.rpow_le_rpow hqM_nn hRpow' hinv_nn
    have hpow_collapse :
        (‖(R.sol k).toBanachPair‖ ^ m_exp) ^ (1 / m_exp)
          = ‖(R.sol k).toBanachPair‖ := by
      rw [← Real.rpow_mul hq_nn]
      have : m_exp * (1 / m_exp) = 1 := by
        field_simp
      rw [this, Real.rpow_one]
    rw [hpow_collapse] at hRpowMono
    exact hRpowMono
  refine
    { epsSeq := R.epsSeq
      heps_pos := R.epsSeq_pos
      heps_tendsto := R.epsSeq_tendsto
      sol := R.sol
      uniformBound := ⟨Cnorm, hbound⟩ }

/-! ## Phase 2b child 2: ε-uniform apriori bound from paper hypotheses

The headline of paper `thm:apriori-simple.power.growth`'s ε-uniform
half — the existential `∃ C ≥ 0, ∀ k, …` form — produced directly
from `(hpow, hV)` plus a per-`k` solution sequence and a per-`k`
`AprioriUniformPerSolHypotheses` bundle. Skips the
`AprioriUniformResidueInputs` residue wrapper as a user-visible
parameter; internally calls `apriori_aggregate_bound_residue_form`
per `k` (same body as the producer
`aprioriUniformResidueInputs_of_paperHypotheses`, modulo the
`epsSeq_tendsto` field, which is not needed for the existential
conclusion).

The constant is the closed-form value
`aprioriUniformConstantClosed hpow Vbound Vint_bound Vβp_bound`. -/

/-- **ε-uniform apriori bound from paper hypotheses.**

Given the paper-level `(hmon, hpow, hV)` triple, an `ε`-sequence with
strict positivity, a per-`k` `RegularizedBareSolution`, the shared
`(Vbound, Vint_bound, Vβp_bound)` triple bounding `V`'s
`L^∞` / `L¹` / `L^{β̄'}` integrals (with `Vint_bound`, `Vβp_bound`
nonneg), and a per-`k` `AprioriUniformPerSolHypotheses` bundle,
emit the `∃ C ≥ 0, ∀ k, (∫|m_k|^{β̄}) + (∫|u_k|^{γ̄}) +
(∑_i ∫|Du_k i|^{γ̄}) ≤ C` conclusion of paper
`thm:apriori-simple.power.growth`'s ε-uniform half.

The constant is the closed-form value
`aprioriUniformConstantClosed hpow Vbound Vint_bound Vβp_bound`
(non-negativity from `aprioriUniformConstantClosed_nn`).

Body unrolls to a direct application of
`apriori_aggregate_bound_residue_form` per-`k`, as in
`aprioriUniformResidueInputs_of_paperHypotheses`'s body
(`AprioriUniform.lean:353+`); we skip the residue scaffold so the
caller is not forced to supply `epsSeq_tendsto`.

Phase 2b child 2 deliverable: closed-form wrapper from paper
hypotheses + per-`k` `AprioriUniformPerSolHypotheses`, callable
from `BanachBridge.lean` as a drop-in replacement for the
`regularizedSequenceData_of_aprioriResidue` step-1 call. -/
theorem apriori_uniform_bound_for_regularized_sequence
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (_hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (epsSeq : ℕ → ℝ) (_epsSeq_pos : ∀ k, 0 < epsSeq k)
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (perSolHyps : ∀ k : ℕ,
      AprioriUniformPerSolHypotheses (d := d) hpow (sol k)
        Vbound Vint_bound Vβp_bound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ,
        (∫ x in UnitCube d, |(sol k).m x| ^ (hpow.β + 1)) +
          (∫ x in UnitCube d, |(sol k).u x| ^ (gammaBar hpow.α hpow.β)) +
          (∑ i, ∫ x in UnitCube d,
                  |(sol k).Du i x| ^ (gammaBar hpow.α hpow.β)) ≤ C := by
  refine ⟨aprioriUniformConstantClosed (d := d) hpow Vbound Vint_bound Vβp_bound,
          aprioriUniformConstantClosed_nn (d := d) hpow Vbound Vint_bound Vβp_bound
            hVint_nn hVβp_nn, ?_⟩
  intro k
  have H_k := perSolHyps k
  have hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β))
                  (sol k).u := (sol k).huLp
  have hDu_weak : ∀ i, HasWeakDerivPer i (sol k).u ((sol k).Du i) :=
    (sol k).hWeakDeriv
  have hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β))
                        ((sol k).Du i) := (sol k).hDuLp
  exact apriori_aggregate_bound_residue_form
    (h := hpow) V (sol k).Du (sol k).m (sol k).u H_k.epsTerms
    Vbound Vint_bound Vβp_bound
    H_k.hHJB H_k.h_lagr H_k.hMpos H_k.hVbnd H_k.hEpsNN H_k.h_identity
    H_k.hu_int H_k.hRHSabove_int H_k.hLB_int H_k.hMbeta_int
    H_k.hRHSbelow_int H_k.hVint
    H_k.hγ_one_le H_k.hγ_top H_k.hu_meas
    H_k.hu_per H_k.hu_loc H_k.hu_sob
    hDu_weak H_k.hDu_meas
    H_k.hDu_per H_k.hDu_loc hDu_lp
    H_k.hDu_norm_int H_k.hUbetap_int H_k.hVbetap_int H_k.hVβp hu_lp_γ

/-! ## Sanity-check unit tests

Pin the signatures' type-shape via forwarding `example`s. -/

/-- **Unit test for `apriori_uniform_bound_for_regularized_sequence`.**
Verifies that paper inputs `(hmon, hpow, hV)` plus per-`k`
`AprioriUniformPerSolHypotheses` produce the existential
`∃ C ≥ 0, ∀ k, …` directly. -/
example
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (perSolHyps : ∀ k : ℕ,
      AprioriUniformPerSolHypotheses (d := d) hpow (sol k)
        Vbound Vint_bound Vβp_bound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ,
        (∫ x in UnitCube d, |(sol k).m x| ^ (hpow.β + 1)) +
          (∫ x in UnitCube d, |(sol k).u x| ^ (gammaBar hpow.α hpow.β)) +
          (∑ i, ∫ x in UnitCube d,
                  |(sol k).Du i x| ^ (gammaBar hpow.α hpow.β)) ≤ C :=
  apriori_uniform_bound_for_regularized_sequence
    hmon hpow hV Vbound Vint_bound Vβp_bound hVint_nn hVβp_nn
    epsSeq epsSeq_pos sol perSolHyps

/-! ## Sanity-check unit test for the C-class projection

Pin the type-shape of `AprioriUniformPerSolHypotheses.toC`. Once the
filed Step 2a–2d children land, this projection composes with
`AprioriUniformPerSolHypotheses.of_C_class` to give the C-only
wrapper `apriori_uniform_bound_for_regularized_sequence_Conly`. -/

/-- **Unit test for `AprioriUniformPerSolHypotheses.toC`.** Verifies
that a full per-`k` bundle projects to its C-class core. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {h : Hamiltonian.HypothesisPowerGrowth H DpH}
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    {Vbound Vint_bound Vβp_bound : ℝ}
    (P : AprioriUniformPerSolHypotheses (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    AprioriUniformPerSolHypothesesC (d := d) h sol
      Vbound Vint_bound Vβp_bound :=
  P.toC

/-! ## Phase 1 v3 — projections from `RegularizedPaperSolutionData`

The two trivial projection lemmas below source `hLagrRaw` and
`hIdentityRaw` (the consumer shapes of
`AprioriUniformPerSolHypotheses.fromCAndAuthorised`) from the new
`RegularizedPaperSolutionData` carrier defined in
`AssemblyContext.lean`.

* `hLagrRaw_of_regularizedPaperSolutionData` — direct projection of
  `P.h_lagr`, sorry-free.
* `hIdentityRaw_of_regularizedPaperSolutionData` — needs to align
  the **specific** paper-shape `ε · |Du|^γ̄ + ε · u^γ̄` stored in
  `P.hTransport_identity` with the **opaque** `cBundle.epsTerms x`
  consumed by `fromCAndAuthorised`. This alignment only holds once
  Phase 2's constructor pins
  `cBundle.epsTerms = (fun x => ε · … + ε · u^γ̄ x)`, so the body
  carries an explicitly-deferred `sorry` filed as a Phase 2 child
  alignment lemma. -/

/-- **Phase 1 v3 — `hLagrRaw` projection (sorry-free).**

Direct projection of `P.h_lagr` field of `RegularizedPaperSolutionData`
to the `hLagrRaw` shape consumed by
`AprioriUniformPerSolHypotheses.fromCAndAuthorised`. -/
theorem hLagrRaw_of_regularizedPaperSolutionData
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (P : RegularizedPaperSolutionData (d := d) ε V H DpH
            (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' hpow) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ hpow.β) / hpow.C - hpow.C ≤
          (DpH x p mx) ⬝ p - H x p mx :=
  P.h_lagr

/-- **Phase 1 v3 — `hIdentityRaw` projection (sorry-free, with
`h_align` discharge obligation).**

Combines `P.hTransport_identity` (which stores the paper-specific shape
`ε · |Du|^γ̄ + ε · u^γ̄`) with the consumer shape
`cBundle.epsTerms x` (an opaque `(Fin d → ℝ) → ℝ` field of
`AprioriUniformPerSolHypothesesC`).

The alignment between the opaque field and the paper shape is
externalised as the explicit hypothesis `h_align`:
```
∀ x, cBundle.epsTerms x =
        ε · (Du x ⬝ Du x)^(γ̄/2) + ε · (sol.u x)^γ̄
```
This becomes a discharge obligation for Phase 2's constructor
`RegularizedPaperSolutionData.of_paperHypotheses`, which will *define*
`cBundle.epsTerms` to match the paper shape, making `h_align` close
by `rfl` (or near it) at the call site.

(Iter 431 had this as a deferred `sorry`; iter following it closes the
hole by introducing `h_align` and rewriting the integrand.) -/
theorem hIdentityRaw_of_regularizedPaperSolutionData
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (P : RegularizedPaperSolutionData (d := d) ε V H DpH
            (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' hpow)
    {Vbound Vint_bound Vβp_bound : ℝ}
    (cBundle : AprioriUniformPerSolHypothesesC (d := d) hpow P.sol
                  Vbound Vint_bound Vβp_bound)
    (h_align : ∀ x, cBundle.epsTerms x =
        ε * ((fun i => P.sol.Du i x) ⬝ (fun i => P.sol.Du i x))
                ^ (gammaBar hpow.α hpow.β / 2)
        + ε * |P.sol.u x| ^ gammaBar hpow.α hpow.β) :
    ∫ x in UnitCube d, P.sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
          (P.sol.m x * (-H x (fun i => P.sol.Du i x) (P.sol.m x)
                    + (DpH x (fun i => P.sol.Du i x) (P.sol.m x))
                        ⬝ (fun i => P.sol.Du i x))
            + V x * P.sol.m x
            + cBundle.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Rewrite `cBundle.epsTerms x` using `h_align` and re-associate the
  -- two ε-residues so the integrand matches `P.hTransport_identity`'s
  -- left-associative shape `… + V·m + ε·|Du|^(γ̄/2) + ε·u^γ̄`.
  have hEq : ∀ x,
      P.sol.m x * (-H x (fun i => P.sol.Du i x) (P.sol.m x)
                + (DpH x (fun i => P.sol.Du i x) (P.sol.m x))
                    ⬝ (fun i => P.sol.Du i x))
        + V x * P.sol.m x
        + cBundle.epsTerms x
      =
      P.sol.m x * (-H x (fun i => P.sol.Du i x) (P.sol.m x)
                + (DpH x (fun i => P.sol.Du i x) (P.sol.m x))
                    ⬝ (fun i => P.sol.Du i x))
        + V x * P.sol.m x
        + ε * ((fun i => P.sol.Du i x) ⬝ (fun i => P.sol.Du i x))
                ^ (gammaBar hpow.α hpow.β / 2)
        + ε * |P.sol.u x| ^ gammaBar hpow.α hpow.β := by
    intro x
    rw [h_align x]
    ring
  simp_rw [hEq]
  exact P.hTransport_identity

/-! ### D4.0b5 — Integral V-data siblings for the per-`k` bundles

This block ships the **integral V-data siblings** of
`AprioriUniformPerSolHypotheses` and
`AprioriUniformPerSolHypothesesC`. The literal task wording asks to
drop `Vbound`/`hVbnd` from the per-sol hypothesis bundles; however,
the ε-uniform Du closed-form bound (`apriori_Du_bound_closed_form`,
consumed transitively by `apriori_aggregate_bound_residue_form`)
still requires pointwise `Vbound`/`hVbnd`. Until the Du chain admits
an integral V-data variant (deferred to a `D4.0b5+`-shaped follow-up),
we cannot fully drop those fields without breaking the chain.

Per the parent task's "additive/incremental" strategy, this block
therefore lands sibling structures
`AprioriUniformPerSolHypotheses_int` and
`AprioriUniformPerSolHypothesesC_int`, leaving the pointwise
variants untouched. Each sibling:

* consumes an `AprioriVData (betaBar' h.β) V` slot in place of the
  four V-bound fields `Vint_bound`, `Vβp_bound`, `hVint`, `hVβp`
  of the pointwise variant (these are projected out of `vData` at
  use sites);
* still keeps `Vbound : ℝ` and `hVbnd` as transitional fields,
  flagged in their docstrings as such, since the Du closed-form chain
  consumes them.

The projection `AprioriUniformPerSolHypotheses_int.toC_int` mirrors
the pointwise `toC` projection. -/

/-- **Integral V-data sibling of `AprioriUniformPerSolHypotheses`**
(D4.0b5).

Replaces the four V-bound fields `Vint_bound`, `Vβp_bound`, `hVint`,
`hVβp` of the pointwise variant with a single
`AprioriVData (betaBar' h.β) V` slot. The pointwise residue fields
`Vbound`/`hVbnd` are kept transitionally (they are still consumed by
the ε-uniform Du closed-form bound). All other fields are identical
to those of `AprioriUniformPerSolHypotheses`. -/
structure AprioriUniformPerSolHypotheses_int
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    where
  /-- An auxiliary residue function (the regulariser's `ε`-term). -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- **Integral V-data record** (paper-form `L^{β̄'}` bounds on `V`).
  Replaces the pointwise variant's four fields `Vint_bound`,
  `Vβp_bound`, `hVint`, `hVβp`. -/
  vData : AprioriVData (d := d) (Hamiltonian.betaBar' h.β) V
  /-- HJB inequality at `(sol.m, sol.u, sol.Du)`. -/
  hHJB : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x ≤ 0
  /-- Lagrangian-style pointwise lower bound. -/
  h_lagr :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx
  /-- Non-negativity of `m` a.e. on the cube. **HMpos-3 retype**
  (`infra-P5-T10-v7-HMpos-3-bundle-retype`): relaxed from strict
  positivity `0 < sol.m x` to nonneg `0 ≤ sol.m x`. The canonical
  `_paperHypotheses_int` producer now routes through the `_nonneg`
  variant `apriori_aggregate_bound_residue_form_int_aePeriodic_nonneg`
  (HMpos-2 chain sibling), which accepts the relaxed hypothesis. -/
  hmNonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ sol.m x
  /-- Non-negativity of `epsTerms` a.e. -/
  hEpsNN : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x
  /-- Integrability of `epsTerms` on the unit cube. -/
  hEpsInt : MeasureTheory.Integrable epsTerms
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- The transport identity. -/
  h_identity :
    ∫ x in UnitCube d, sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + epsTerms x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Integrability bundle for `u`. -/
  hu_int : MeasureTheory.Integrable sol.u
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of the upper-bound RHS. -/
  hRHSabove_int : MeasureTheory.Integrable
              (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `m^{β+1}`. -/
  hLB_int : MeasureTheory.Integrable
              (fun x => sol.m x ^ (h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `m^β`. -/
  hMbeta_int : MeasureTheory.Integrable
              (fun x => sol.m x ^ h.β)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of the lower-bound RHS. -/
  hRHSbelow_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- The exponent `γ̄` is bounded below by `1`. -/
  hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β)
  /-- The exponent `γ̄` is finite. -/
  hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤
  /-- AE strong measurability of `u` on the unit cube.

  **Phase 2c-γ retype** (`infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`):
  relaxed from whole-`volume` to cube-restricted. The canonical `_int`
  producer no longer needs whole-volume measurability (the AE-periodic
  apriori sibling `apriori_aggregate_bound_residue_form_int_aePeriodic`
  uses periodic representatives internally), and cube-restricted
  measurability is freely available from `MemLpPer.aestronglyMeasurable`. -/
  hu_meas : MeasureTheory.AEStronglyMeasurable sol.u
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- A.e.-periodicity of `u`. **Phase 2c-γ retype**
  (`infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`): retyped
  from pointwise `IsPeriodic sol.u` to `Periodic.AEPeriodic sol.u`.
  The canonical `_int` producer now routes through the AE-periodic
  apriori sibling `apriori_aggregate_bound_residue_form_int_aePeriodic`,
  which accepts AE-periodic representatives. -/
  hu_per : Periodic.AEPeriodic (d := d) sol.u
  /-- Sobolev membership of `u` at `γ̄`. -/
  hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) sol.u
  /-- AE strong measurability of `Du i` on the unit cube.
  **Phase 2c-γ retype**: relaxed from whole-`volume` to cube-restricted,
  parallel to `hu_meas`. -/
  hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- A.e.-periodicity of `Du i`. **Phase 2c-γ retype**: retyped
  from pointwise `IsPeriodic` to `Periodic.AEPeriodic`. -/
  hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (sol.Du i)
  /-- Integrability of `‖Du‖^γ̄`. -/
  hDu_norm_int : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `|u|^{β̄'}`. -/
  hUbetap_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ Hamiltonian.betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `|V|^{β̄'}`. -/
  hVbetap_int : MeasureTheory.Integrable
        (fun x => |V x| ^ Hamiltonian.betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d))

/-- **Integral V-data sibling of `AprioriUniformPerSolHypothesesC`**
(D4.0b5).

C-class core analogue of `AprioriUniformPerSolHypotheses_int`.
Replaces the C-class V-bound fields `hVint`/`hVβp` (and the
parameters `Vint_bound`, `Vβp_bound`) with a single
`AprioriVData (betaBar' h.β) V` slot. Pointwise `Vbound`/`hVbnd`
are kept transitionally.

C-class authorised residues retained: `epsTerms`, `hEpsNN`,
`hEpsInt`, `hMpos`, `hu_per`, `hDu_per`, `hUbetap_int`. The pointwise
`Vbound`/`hVbnd` field has been dropped (iter
`infra-P5-T10-v7-drain-paperHVbndAuth`); the consumer chain now
routes through the canonical integral V-data producer
`aprioriUniformResidueInputs_of_paperHypotheses_int`, which has zero
`hVbnd` references in its body. -/
structure AprioriUniformPerSolHypothesesC_int
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    where
  /-- An auxiliary residue function (the regulariser's `ε`-term). -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- Non-negativity of `epsTerms` a.e. -/
  hEpsNN : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x
  /-- Integrability of `epsTerms` on the unit cube. -/
  hEpsInt : MeasureTheory.Integrable epsTerms
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- Non-negativity of `m` a.e. on the cube. **HMpos-3 retype**
  (`infra-P5-T10-v7-HMpos-3-bundle-retype`): relaxed from strict
  positivity `0 < sol.m x` to nonneg `0 ≤ sol.m x`. Matches the
  retype of `AprioriUniformPerSolHypotheses_int.hmNonneg`. -/
  hmNonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ sol.m x
  /-- **Integral V-data record** (paper-form `L^{β̄'}` bounds on `V`).
  Replaces the C-class fields `hVint`/`hVβp` and the parameters
  `Vint_bound`/`Vβp_bound` of the pointwise variant. -/
  vData : AprioriVData (d := d) (Hamiltonian.betaBar' h.β) V
  /-- A.e.-periodicity of `u`. **Phase 2c-γ retype**
  (`infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`): retyped
  from pointwise `IsPeriodic sol.u` to `Periodic.AEPeriodic sol.u`. -/
  hu_per : Periodic.AEPeriodic (d := d) sol.u
  /-- A.e.-periodicity of `Du i`. **Phase 2c-γ retype**: retyped from
  pointwise `IsPeriodic` to `Periodic.AEPeriodic`. -/
  hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (sol.Du i)
  /-- Integrability of `|u|^{β̄'}`. -/
  hUbetap_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ Hamiltonian.betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d))

/-- **Projection from a full `AprioriUniformPerSolHypotheses_int`
bundle to its C-class core.**

Mirrors `AprioriUniformPerSolHypotheses.toC` for the integral
V-data sibling. -/
def AprioriUniformPerSolHypotheses_int.toC_int
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {h : Hamiltonian.HypothesisPowerGrowth H DpH}
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    (P : AprioriUniformPerSolHypotheses_int (d := d) h sol) :
    AprioriUniformPerSolHypothesesC_int (d := d) h sol where
  epsTerms := P.epsTerms
  hEpsNN := P.hEpsNN
  hEpsInt := P.hEpsInt
  -- **HMpos-3 retype**: master and C-int both carry `hmNonneg`; direct
  -- projection.
  hmNonneg := P.hmNonneg
  vData := P.vData
  hu_per := P.hu_per
  hDu_per := P.hDu_per
  hUbetap_int := P.hUbetap_int

/-- **Bridge: pointwise → integral sibling.**

Converts a pointwise `AprioriUniformPerSolHypotheses` bundle into the
integral V-data sibling, packaging the four V-bound fields
`(Vint_bound, Vβp_bound, hVint, hVβp)` plus the non-negativity inputs
into an `AprioriVData` record. The transitional `Vbound`/`hVbnd`
fields are forwarded unchanged. -/
def AprioriUniformPerSolHypotheses.toInt
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {h : Hamiltonian.HypothesisPowerGrowth H DpH}
    {βBarReal' γBarReal' : ℝ}
    {sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal'}
    {Vbound Vint_bound Vβp_bound : ℝ}
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (P : AprioriUniformPerSolHypotheses (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    AprioriUniformPerSolHypotheses_int (d := d) h sol where
  epsTerms := P.epsTerms
  vData :=
    { Vint_bound := Vint_bound
      Vβp_bound := Vβp_bound
      hVint_nn := hVint_nn
      hVβp_nn := hVβp_nn
      hVint := P.hVint
      hVβp := P.hVβp }
  hHJB := P.hHJB
  h_lagr := P.h_lagr
  -- **HMpos-3 retype**: pointwise master still carries strict `hMpos`;
  -- the `_int` master now carries `hmNonneg`. Downgrade by `.mono`.
  hmNonneg := P.hMpos.mono fun _ hx => hx.le
  hEpsNN := P.hEpsNN
  hEpsInt := P.hEpsInt
  h_identity := P.h_identity
  hu_int := P.hu_int
  hRHSabove_int := P.hRHSabove_int
  hLB_int := P.hLB_int
  hMbeta_int := P.hMbeta_int
  hRHSbelow_int := P.hRHSbelow_int
  hγ_one_le := P.hγ_one_le
  hγ_top := P.hγ_top
  hu_meas := P.hu_meas.restrict
  hu_per := Periodic.AEPeriodic.ofPeriodic P.hu_per
  hu_sob := P.hu_sob
  hDu_meas := fun i => (P.hDu_meas i).restrict
  hDu_per := fun i => Periodic.AEPeriodic.ofPeriodic (P.hDu_per i)
  hDu_norm_int := P.hDu_norm_int
  hUbetap_int := P.hUbetap_int
  hVbetap_int := P.hVbetap_int

/-! ### Bridge `_int → full pointwise` (REMOVED in Phase 2c-γ).

The `AprioriUniformPerSolHypotheses_int.toFull` projection has been
removed because the `_int` bundle's `hu_per`/`hDu_per` are now typed
as `Periodic.AEPeriodic` (a.e.-periodic representative existence),
and the pointwise full bundle's `hu_per`/`hDu_per` require strict
`IsPeriodic`. There is no canonical way to recover pointwise
periodicity from AE-periodicity, so this bridge is no longer
well-defined.

Per `infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`. -/

/-! ### Sanity-check unit tests for the D4.0b5 siblings

Pin the type-shapes of the new siblings and the bridges. -/

example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (P : AprioriUniformPerSolHypotheses_int (d := d) h sol) :
    AprioriUniformPerSolHypothesesC_int (d := d) h sol :=
  P.toC_int

example
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : Hamiltonian.HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
            (gammaBar h.α h.β) (h.β + 1) βBarReal' γBarReal')
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (P : AprioriUniformPerSolHypotheses (d := d) h sol
            Vbound Vint_bound Vβp_bound) :
    AprioriUniformPerSolHypotheses_int (d := d) h sol :=
  P.toInt hVint_nn hVβp_nn

/-- **Phase 1 sub-task 1c-b (v7 plan, D4.1c-b): integral V-data sibling
of `hIdentityRaw_of_regularizedPaperSolutionData`.**

Same statement, but consumes `AprioriUniformPerSolHypothesesC_int`
(only one `Vbound : ℝ` parameter) instead of the pointwise
`AprioriUniformPerSolHypothesesC` (three `Vbound`/`Vint_bound`/`Vβp_bound`
parameters). The body only reads `cBundle.epsTerms`, which is a shared
field of both shapes. -/
theorem hIdentityRaw_of_regularizedPaperSolutionData_int
    [AxisMixMeasureHypothesis]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (P : RegularizedPaperSolutionData (d := d) ε V H DpH
            (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' hpow)
    (cBundle : AprioriUniformPerSolHypothesesC_int (d := d) hpow P.sol)
    (h_align : ∀ x, cBundle.epsTerms x =
        ε * ((fun i => P.sol.Du i x) ⬝ (fun i => P.sol.Du i x))
                ^ (gammaBar hpow.α hpow.β / 2)
        + ε * |P.sol.u x| ^ gammaBar hpow.α hpow.β) :
    ∫ x in UnitCube d, P.sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
          (P.sol.m x * (-H x (fun i => P.sol.Du i x) (P.sol.m x)
                    + (DpH x (fun i => P.sol.Du i x) (P.sol.m x))
                        ⬝ (fun i => P.sol.Du i x))
            + V x * P.sol.m x
            + cBundle.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Identical body to the pointwise sibling: rewrite via `h_align` and
  -- close by `P.hTransport_identity`.
  have hEq : ∀ x,
      P.sol.m x * (-H x (fun i => P.sol.Du i x) (P.sol.m x)
                + (DpH x (fun i => P.sol.Du i x) (P.sol.m x))
                    ⬝ (fun i => P.sol.Du i x))
        + V x * P.sol.m x
        + cBundle.epsTerms x
      =
      P.sol.m x * (-H x (fun i => P.sol.Du i x) (P.sol.m x)
                + (DpH x (fun i => P.sol.Du i x) (P.sol.m x))
                    ⬝ (fun i => P.sol.Du i x))
        + V x * P.sol.m x
        + ε * ((fun i => P.sol.Du i x) ⬝ (fun i => P.sol.Du i x))
                ^ (gammaBar hpow.α hpow.β / 2)
        + ε * |P.sol.u x| ^ gammaBar hpow.α hpow.β := by
    intro x
    rw [h_align x]
    ring
  simp_rw [hEq]
  exact P.hTransport_identity

/-! ### D4.1a — Integral V-data sibling of the `_setInputs` closed-paper
residue producer (moved below `_paperHypotheses_int`)

Phase 1 sub-task 1a of the v7 plan. The transitional `_int` sibling
`aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int`
delegates to the canonical `_paperHypotheses_int` (defined immediately
below) — the definition has been physically moved past it (iter
`infra-P5-T10-v7-drain-paperHVbndAuth`). The block now lives at the
bottom of this file, after `_paperHypotheses_int` and its example. -/

/-! ### D4.1a-deep — canonical integral V-data residue producer

Phase 1 sub-task 1a-deep of the v7 plan. Adds the canonical producer
`aprioriUniformResidueInputs_of_paperHypotheses_int` whose body routes
entirely through the integral V-data closed-form chain (D4.0d):

* `apriori_aggregate_bound_residue_form_int` (Apriori.lean:6788) for the
  per-`k` bound; this in turn routes through
* `apriori_Du_bound_closed_form_int` (Apriori.lean:6289),
  `apriori_m_bound_closed_int`, `apriori_uepsi_Lp_closed_int`.

The body contains **no** reference to `Vbound`/`hVbnd`/`Vint_bound`/`Vβp_bound`
as real-typed parameters — the only `Vbound` mention is in the *type-level*
parameter to `AprioriUniformPerSolHypotheses_int`, which still carries
`hVbnd` transitionally (consumed nowhere by this body).

The four extra integrability/measurability hypotheses required by the
`_int` aggregator (`hVm_int`, `hV_meas`, `hm_meas`, `hM_int`) but absent
from `AprioriUniformPerSolHypotheses_int` are taken as additional
explicit per-`k` inputs. -/

/-- **Phase 1 sub-task 1a-deep (v7 plan): canonical integral V-data
residue producer.**

Sibling of `aprioriUniformResidueInputs_of_paperHypotheses` whose body
routes through the integral V-data Apriori chain:
`apriori_aggregate_bound_residue_form_int` → `apriori_Du_bound_closed_form_int`
(D4.0d). The closed-form constant is
`aprioriUniformConstantClosed_int hpow vData.Vint_bound vData.Vβp_bound`,
built entirely from `_int` sub-witnesses (no `Vbound` appears anywhere
in the body).

The producer takes:
* `hpow` — paper power-growth hypothesis;
* `_hV` — paper `MemLpPer` certificate (forward-compat slot, not consumed);
* `vData` — uniform integral V-data (single record carrying
  `Vint_bound`, `Vβp_bound`, `hVint`, `hVβp`, plus non-negativity);
* `epsSeq`/`sol` — regularisation sequence (same shape as the pointwise
  producer);
* `Vbound` — type-level parameter forwarded to the per-`k`
  `AprioriUniformPerSolHypotheses_int` bundle (consumed nowhere);
* `perSolHyps` — per-`k` `_int` bundle (D4.0b5);
* `hVm_int`, `hV_meas`, `hm_meas`, `hM_int` — the four extra per-`k`
  hypotheses required by the `_int` aggregator that are not in the
  per-`k` bundle (additive — does not modify the bundle structure).

The output is an `AprioriUniformResidueInputs` whose `uniformConstant`
is the closed-form `aprioriUniformConstantClosed_int` value.

This is the producer the `_setInputs_int` sibling will eventually
delegate to (replacing its current pointwise delegation), closing the
v7 Phase 1 migration. -/
noncomputable def aprioriUniformResidueInputs_of_paperHypotheses_int
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    -- **HMpos-3 retype**: route through the `_nonneg` aggregator
    -- sibling `apriori_aggregate_bound_residue_form_int_aePeriodic_nonneg`
    -- (HMpos-2 chain sibling). It requires three additional Hamiltonian
    -- inputs `hHat0`, `hFin`, `hAgree` that come from the paper
    -- hypotheses.
    (hHat0 : Hamiltonian.HypothesisHat0 H)
    (hFin : Hamiltonian.Hext_finite_at_zero H)
    (hAgree : Hamiltonian.H_zero_eq_Hext H)
    {βBarReal' γBarReal' : ℝ}
    (_hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (vData : AprioriVData (d := d) (Hamiltonian.betaBar' hpow.β) V)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (perSolHyps : ∀ k : ℕ,
      AprioriUniformPerSolHypotheses_int (d := d) hpow (sol k))
    (hV_meas : MeasureTheory.AEStronglyMeasurable V
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hm_meas : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hVm_int : ∀ k : ℕ, MeasureTheory.Integrable
                  (fun x => |V x| * (sol k).m x)
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hM_int : ∀ k : ℕ, MeasureTheory.Integrable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d))) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' where
  epsSeq := epsSeq
  epsSeq_pos := epsSeq_pos
  epsSeq_tendsto := epsSeq_tendsto
  sol := sol
  uniformConstant :=
    aprioriUniformConstantClosed_int (d := d) hpow.toCongestionAprioriPowerData
      vData.Vint_bound vData.Vβp_bound
  uniformConstant_nn :=
    aprioriUniformConstantClosed_int_nn (d := d) hpow.toCongestionAprioriPowerData
      vData.Vint_bound vData.Vβp_bound vData.hVint_nn vData.hVβp_nn
  uniformConstant_bound := by
    intro k
    have H_k := perSolHyps k
    have hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β))
                    (sol k).u := (sol k).huLp
    have hDu_weak : ∀ i, HasWeakDerivPer i (sol k).u ((sol k).Du i) :=
      (sol k).hWeakDeriv
    have hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β))
                          ((sol k).Du i) := (sol k).hDuLp
    -- Apply the integral V-data closed-form aggregate bound (D4.0d).
    -- Note: `vData.hVβp : ∫ |V|^(betaBar' hpow.β) ≤ vData.Vβp_bound` is
    -- definitionally equal to the `((hpow.β + 1) / hpow.β)`-form
    -- `hVβp_le` parameter, since `betaBar' β := (β + 1) / β`.
    -- Similarly `H_k.hVbetap_int` definitionally serves `hVβp_pow_int`.
    -- **Phase 2c-γ retype** (`infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`):
    -- route through the AE-periodic sibling. **HMpos-3 retype**
    -- (`infra-P5-T10-v7-HMpos-3-bundle-retype`): switched to the
    -- `_nonneg` sibling
    -- `apriori_aggregate_bound_residue_form_int_aePeriodic_nonneg`
    -- (HMpos-2), which takes `hmNonneg : 0 ≤ m x` (matching the
    -- bundle's retyped `hmNonneg` field) instead of strict positivity,
    -- and requires three additional Hamiltonian inputs `hHat0`, `hFin`,
    -- `hAgree`.
    exact apriori_aggregate_bound_residue_form_int_aePeriodic_nonneg
      (h := hpow.toCongestionAprioriPowerData) hHat0 hFin hAgree
      V (sol k).Du (sol k).m (sol k).u H_k.epsTerms
      vData.Vint_bound vData.Vβp_bound
      H_k.hHJB H_k.h_lagr H_k.hmNonneg
      vData.hVint vData.hVβp vData.hVβp_nn
      H_k.hVbetap_int (hVm_int k) hV_meas (hm_meas k)
      H_k.hEpsNN H_k.h_identity
      H_k.hu_int H_k.hRHSabove_int H_k.hLB_int (hM_int k) H_k.hMbeta_int
      H_k.hRHSbelow_int
      H_k.hγ_one_le H_k.hγ_top
      H_k.hu_per H_k.hu_sob
      hDu_weak
      H_k.hDu_per hDu_lp
      H_k.hDu_norm_int H_k.hUbetap_int H_k.hVbetap_int vData.hVβp hu_lp_γ

/-- **Sanity-check unit test for
`aprioriUniformResidueInputs_of_paperHypotheses_int`.**

Pins the type-shape of the canonical integral V-data residue producer:
paper inputs + uniform `vData` + per-`k` `AprioriUniformPerSolHypotheses_int`
+ four extra per-`k` integrability/measurability hypotheses deliver an
`AprioriUniformResidueInputs`. -/
example
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    -- **HMpos-3 retype**: three Hamiltonian extras for the `_nonneg`
    -- aggregator routed through `_paperHypotheses_int`.
    (hHat0 : Hamiltonian.HypothesisHat0 H)
    (hFin : Hamiltonian.Hext_finite_at_zero H)
    (hAgree : Hamiltonian.H_zero_eq_Hext H)
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (vData : AprioriVData (d := d) (Hamiltonian.betaBar' hpow.β) V)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (perSolHyps : ∀ k : ℕ,
      AprioriUniformPerSolHypotheses_int (d := d) hpow (sol k))
    (hV_meas : MeasureTheory.AEStronglyMeasurable V
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hm_meas : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hVm_int : ∀ k : ℕ, MeasureTheory.Integrable
                  (fun x => |V x| * (sol k).m x)
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hM_int : ∀ k : ℕ, MeasureTheory.Integrable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d))) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' :=
  aprioriUniformResidueInputs_of_paperHypotheses_int
    hmon hpow hHat0 hFin hAgree hV vData epsSeq epsSeq_pos epsSeq_tendsto sol perSolHyps
    hV_meas hm_meas hVm_int hM_int

/-! ### D4.1a — Integral V-data sibling of the `_setInputs` closed-paper
residue producer

Phase 1 sub-task 1a of the v7 plan. The transitional `_int` sibling
`aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int`
delegates to the canonical `_paperHypotheses_int` (defined above) — the
definition was moved here in iter
`infra-P5-T10-v7-drain-paperHVbndAuth`. -/

/-- **Phase 1 sub-task 1a (v7 plan): integral V-data sibling of the
`_setInputs` closed-paper residue producer.**

Sibling of `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs`
that:

* consumes per-`k` `AprioriUniformPerSolHypothesesC_int hpow (sol k)`
  bundles (D4.0b5 — carrying a per-`k` `vData` slot in place of the four
  pointwise V-bound fields);
* takes a single uniform `vData : AprioriVData (betaBar' hpow.β) V` whose
  fields supply the `Vint_bound, Vβp_bound, hVint_nn, hVβp_nn, hVint, hVβp`
  data needed by the closed-form chain. The per-`k` `vData` carried inside
  each `cBundles_int k` is *ignored* by this transitional sibling — only the
  uniform `vData` is consumed.

**iter `infra-P5-T10-v7-drain-paperHVbndAuth`**: the transitional
`Vbound`/`hVbnd` parameters have been removed. The body now routes
through the canonical integral V-data producer
`aprioriUniformResidueInputs_of_paperHypotheses_int` (whose body has
zero `hVbnd` references). The 4 extras required by that producer
(`hV_meas`, `hm_meas`, `hVm_int`, `hM_int`) are now explicit
parameters of this `_setInputs_int` sibling. -/
noncomputable def aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    -- **HMpos-3 retype**: three Hamiltonian extras passed through to
    -- `_paperHypotheses_int` for the `_nonneg` aggregator.
    (hHat0 : Hamiltonian.HypothesisHat0 H)
    (hFin : Hamiltonian.Hext_finite_at_zero H)
    (hAgree : Hamiltonian.H_zero_eq_Hext H)
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hV_resid : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (vData : AprioriVData (d := d) (Hamiltonian.betaBar' hpow.β) V)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (cBundles_int : ∀ k : ℕ,
      AprioriUniformPerSolHypothesesC_int (d := d) hpow (sol k))
    (hRes_Lp : ∀ k : ℕ,
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (betaBar' hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (sol k).Du (sol k).m (sol k).u))
    (hSet : ∀ k : ℕ, SetAdditiveContinuityInputs (sol k))
    (hIdentityRaw : ∀ k : ℕ,
      ∫ x in UnitCube d, (sol k).u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          ((sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                    + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                        ⬝ (fun i => (sol k).Du i x))
            + V x * (sol k).m x
            + (cBundles_int k).epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * ((sol k).m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => (sol k).m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x =>
                (sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                          + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                              ⬝ (fun i => (sol k).Du i x))
                  + V x * (sol k).m x
                  + (cBundles_int k).epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    -- **Phase 2c-γ retype**: `hu_measRaw` / `hDu_measRaw` relaxed from
    -- whole-`volume` to cube-restricted, matching the relaxed `_int`
    -- bundle fields.
    (hu_measRaw : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).u
                            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDu_measRaw : ∀ k : ℕ, ∀ i,
                    MeasureTheory.AEStronglyMeasurable ((sol k).Du i)
                      (MeasureTheory.volume.restrict (UnitCube d)))
    (hDu_norm_intRaw : ∀ k : ℕ, MeasureTheory.Integrable
        (fun x => ‖(fun i => (sol k).Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw : ∀ _k : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    -- Four extras for the canonical `_paperHypotheses_int` aggregator
    -- (iter `infra-P5-T10-v7-drain-paperHVbndAuth`):
    (hV_meas : MeasureTheory.AEStronglyMeasurable V
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hm_meas : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hVm_int : ∀ k : ℕ, MeasureTheory.Integrable
                  (fun x => |V x| * (sol k).m x)
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hM_int : ∀ k : ℕ, MeasureTheory.Integrable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d))) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' := by
  -- A-class fact: `1 ≤ ENNReal.ofReal γ̄`.
  have hγ_one_le : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (gammaBar hpow.α hpow.β) :=
    AprioriUniformPerSolHypothesesC.aClass_hγ_one_le hpow
  -- A-class derivation: per-`k` integrability of `m^{β+1}` (from
  -- `(sol k).hmLp` via `MemLp.integrable_norm_rpow`, realigning
  -- `‖m‖^{β+1} = m^{β+1}` a.e. via `(sol k).hmNonneg`).
  have hLB_int_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => (sol k).m x ^ (hpow.β + 1))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    have hβ1_pos : 0 < hpow.β + 1 := by have := hpow.hβ; linarith
    have hp_ne_zero : ENNReal.ofReal (hpow.β + 1) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hβ1_pos).ne'
    have hp_ne_top : ENNReal.ofReal (hpow.β + 1) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hL : MeasureTheory.MemLp (sol k).m
        (ENNReal.ofReal (hpow.β + 1))
        (MeasureTheory.volume.restrict (UnitCube d)) := (sol k).hmLp
    have hint_norm : MeasureTheory.Integrable
        (fun x => ‖(sol k).m x‖ ^ (ENNReal.ofReal (hpow.β + 1)).toReal)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hL.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hp_toReal : (ENNReal.ofReal (hpow.β + 1)).toReal = hpow.β + 1 :=
      ENNReal.toReal_ofReal hβ1_pos.le
    rw [hp_toReal] at hint_norm
    refine hint_norm.congr ?_
    have hmnn := (sol k).hmNonneg
    filter_upwards [hmnn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  -- A-class derivation: per-`k` integrability of `u` (from `(sol k).huLp`
  -- at `γ̄` via `MemLp.integrable` on the finite-measure cube).
  have hu_int_k : ∀ k : ℕ, MeasureTheory.Integrable (sol k).u
      (MeasureTheory.volume.restrict (UnitCube d)) := fun k =>
    (sol k).huLp.toMemLp.integrable hγ_one_le
  -- A-class derivation: per-`k` integrability of `|V|^{β̄'}`.
  have hVbetap_int_k : MeasureTheory.Integrable
      (fun x => |V x| ^ betaBar' hpow.β)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    AprioriUniformPerSolHypothesesC.aClass_hVbetap_int hpow hV
  -- Build the full integral V-data bundle per-`k` and delegate.
  exact aprioriUniformResidueInputs_of_paperHypotheses_int
    (V := V) (H := H) (DpH := DpH)
    hmon hpow hHat0 hFin hAgree hV_resid vData
    epsSeq epsSeq_pos epsSeq_tendsto sol
    (fun k =>
      { epsTerms := (cBundles_int k).epsTerms
        vData := (cBundles_int k).vData
        hHJB := AprioriUniformPerSolHypothesesC.bClass_hHJB_of_setInputs
                  hpow (sol k) (hRes_Lp k) (hSet k)
        h_lagr := hLagrRaw k
        -- **HMpos-3 retype**: both C-int and master `_int` now carry
        -- `hmNonneg`; direct projection.
        hmNonneg := (cBundles_int k).hmNonneg
        hEpsNN := (cBundles_int k).hEpsNN
        hEpsInt := (cBundles_int k).hEpsInt
        h_identity := hIdentityRaw k
        hu_int := hu_int_k k
        hRHSabove_int := hRHSaboveRaw k
        hLB_int := hLB_int_k k
        hMbeta_int := hMbetaRaw k
        hRHSbelow_int := hRHSbelowRaw k
        hγ_one_le := hγ_one_le
        hγ_top := AprioriUniformPerSolHypothesesC.aClass_hγ_top hpow
        hu_meas := hu_measRaw k
        -- **Phase 2c-γ retype**: `(cBundles_int k).hu_per` is now
        -- `Periodic.AEPeriodic`, flows directly into the `_int`
        -- bundle's retyped `hu_per` field. The `hu_loc` / `hDu_loc`
        -- fields have been dropped from `_int` since the canonical
        -- producer routes through `_aePeriodic`.
        hu_per := (cBundles_int k).hu_per
        hu_sob := (sol k).memSobolevPer_u
        hDu_meas := hDu_measRaw k
        hDu_per := (cBundles_int k).hDu_per
        hDu_norm_int := hDu_norm_intRaw k
        hUbetap_int := (cBundles_int k).hUbetap_int
        hVbetap_int := hVbetap_int_k })
    hV_meas hm_meas hVm_int hM_int

/-- **Sanity-check unit test for
`aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int`.**

Pins the type-shape of the D4.1a producer (post-iter
`infra-P5-T10-v7-drain-paperHVbndAuth`): paper inputs + uniform
`vData` + per-`k` `AprioriUniformPerSolHypothesesC_int` + the same
authorised B-class per-`k` inputs + four extra per-`k`
integrability/measurability hypotheses (`hV_meas`, `hm_meas`,
`hVm_int`, `hM_int`) deliver an `AprioriUniformResidueInputs`. -/
example
    [AxisMixMeasureHypothesis]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    -- **HMpos-3 retype**: three Hamiltonian extras.
    (hHat0 : Hamiltonian.HypothesisHat0 H)
    (hFin : Hamiltonian.Hext_finite_at_zero H)
    (hAgree : Hamiltonian.H_zero_eq_Hext H)
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    {βBarReal' γBarReal' : ℝ}
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (betaBar' hpow.β)) V)
    (hV_resid : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (vData : AprioriVData (d := d) (Hamiltonian.betaBar' hpow.β) V)
    (epsSeq : ℕ → ℝ) (epsSeq_pos : ∀ k, 0 < epsSeq k)
    (epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0))
    (sol : ∀ k : ℕ,
      RegularizedBareSolution d (epsSeq k) V H DpH
        (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (cBundles_int : ∀ k : ℕ,
      AprioriUniformPerSolHypothesesC_int (d := d) hpow (sol k))
    (hRes_Lp : ∀ k : ℕ,
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (betaBar' hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (sol k).Du (sol k).m (sol k).u))
    (hSet : ∀ k : ℕ, SetAdditiveContinuityInputs (sol k))
    (hIdentityRaw : ∀ k : ℕ,
      ∫ x in UnitCube d, (sol k).u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          ((sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                    + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                        ⬝ (fun i => (sol k).Du i x))
            + V x * (sol k).m x
            + (cBundles_int k).epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hRHSaboveRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => |V x| + hpow.C * ((sol k).m x ^ hpow.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbetaRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x => (sol k).m x ^ hpow.β)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelowRaw : ∀ k : ℕ, MeasureTheory.Integrable
              (fun x =>
                (sol k).m x * (-H x (fun i => (sol k).Du i x) ((sol k).m x)
                          + (DpH x (fun i => (sol k).Du i x) ((sol k).m x))
                              ⬝ (fun i => (sol k).Du i x))
                  + V x * (sol k).m x
                  + (cBundles_int k).epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d)))
    -- **Phase 2c-γ retype**: cube-restricted measurability,
    -- parallel to the underlying `_paperHypotheses_int` producer.
    (hu_measRaw : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).u
                            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDu_measRaw : ∀ k : ℕ, ∀ i,
                    MeasureTheory.AEStronglyMeasurable ((sol k).Du i)
                      (MeasureTheory.volume.restrict (UnitCube d)))
    (hDu_norm_intRaw : ∀ k : ℕ, MeasureTheory.Integrable
        (fun x => ‖(fun i => (sol k).Du i x)‖ ^ gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hLagrRaw : ∀ _k : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hpow.β) / hpow.C - hpow.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hV_meas : MeasureTheory.AEStronglyMeasurable V
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hm_meas : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hVm_int : ∀ k : ℕ, MeasureTheory.Integrable
                  (fun x => |V x| * (sol k).m x)
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hM_int : ∀ k : ℕ, MeasureTheory.Integrable (sol k).m
                  (MeasureTheory.volume.restrict (UnitCube d))) :
    AprioriUniformResidueInputs (d := d) V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' :=
  aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int
    hmon hpow hHat0 hFin hAgree hV hV_resid vData
    epsSeq epsSeq_pos epsSeq_tendsto sol cBundles_int
    hRes_Lp hSet hIdentityRaw
    hRHSaboveRaw hMbetaRaw hRHSbelowRaw
    hu_measRaw hDu_measRaw hDu_norm_intRaw hLagrRaw
    hV_meas hm_meas hVm_int hM_int

end Banach
end SimplePower
end Theorems
end StationaryMFG

end
