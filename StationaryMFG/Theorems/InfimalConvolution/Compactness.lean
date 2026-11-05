module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Periodic.WeakCompactness
public import StationaryMFG.Periodic.Reflexive
public import StationaryMFG.Periodic.LpReflexive
public import StationaryMFG.Periodic.Separability
public import StationaryMFG.Theorems.SimplePower.Banach.WeakLimit

@[expose] public section

/-!
# Weak compactness extraction for `(m_ε, u_ε)` (paper `eq:compactness.delta`)

This module formalizes the paper's compactness step at line 1979 of
`Source/FGU-monotone_revised.tex`, equation `eq:compactness.delta`, the
Phase-6 / Theorem-3 counterpart of Phase-4's `eq:compactness`.

## Paper restatement (lines 1978–1984)

By Theorem `thm:apriori-weak.power.growth`, the regularized family
`(m_{ε_k}, u_{ε_k})` is uniformly bounded in `L^{β̄}(𝕋^d; ℝ⁺_0) ×
W^{1,γ̄}(𝕋^d)`. By Banach–Alaoglu and the reflexivity of `L^{β̄}` and
`W^{1,γ̄}`, up to a (non-relabelled) subsequence,
```
(m_{ε_k}, u_{ε_k}) ⇀ (m, u)   weakly in
      L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d).
```
The limit `m` is non-negative because the cone `L^{β̄}(𝕋^d; ℝ⁺_0)` is
convex and closed, hence weakly closed.

## Lean strategy

We re-derive the Phase-6 statement directly on top of the abstract
Phase-1 reflexivity primitive
`StationaryMFG.Periodic.WeakCompactness.weakSeqCompact_of_bounded_reflexive`,
rather than importing the Phase-4 sibling
`StationaryMFG.Theorems.SimplePower.Compactness`. This keeps the
dependency graph straight and allows Phase-6 to evolve with distinct
`(β̄, γ̄)` exponents independently of Phase-4. The note in the paper
(line 1894) — "follow the proof of `thm:apriori-simple.power.growth`
line by line, replacing `H ↦ H^ε`" — captures the conceptual reuse,
which is here realised by sharing the same Phase-1 primitive.

## Main results

* `exists_weak_limit_sequence` — abstract extraction: bounded sequence
  in a reflexive real normed space, with all terms in a sequentially
  weakly closed set `S`, admits a weakly convergent subsequence with
  limit in `S`. This is the Phase-6 statement of paper
  `eq:compactness.delta` once specialised to
  `X := L^{β̄}_per × W^{1,γ̄}_per`.
* `exists_weak_limit_sequence_pair` — pair-shaped specialisation: when
  `X = Y × Z`, the cone constraint on the first coordinate is enough.

## References

* Paper: `Source/FGU-monotone_revised.tex`, lines 1978–1984, equation
  `eq:compactness.delta`.
* Phase-4 sibling: `StationaryMFG.Theorems.SimplePower.Compactness`
  (paper `eq:compactness`, line 1292) — parallel structure, not imported.
* Project dependencies:
  - `StationaryMFG.Periodic.WeakCompactness.weakSeqCompact_of_bounded_reflexive`
  - `StationaryMFG.Periodic.Reflexive.IsReflexiveNormedSpace`
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace InfimalConvolution

open MeasureTheory NormedSpace
open Bornology Filter Topology
open scoped ENNReal
open StationaryMFG.Periodic
  (IsReflexiveNormedSpace weakSeqCompact_of_bounded_reflexive
    lpSobolev_product_isReflexive_two SobolevPerLp UnitCube)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Abstract extraction (Phase-6 statement) -/

/-- **Weak limit extraction with a sequentially weakly closed constraint.**

Given:
* a reflexive real normed space `X` with separable strong dual,
* a sequence `z_n : ℕ → X` whose range is norm-bounded,
* a sequentially weakly closed set `S : Set (WeakSpace ℝ X)` such that
  `(toWeakSpace ℝ X) (z_n n) ∈ S` for every `n`,

there exists a strictly increasing index function `φ` and a weak limit
`z ∈ S` with `(toWeakSpace ℝ X) (z_n (φ k)) → z` in `WeakSpace ℝ X`.

This is the Phase-6 form of paper `eq:compactness.delta` (line 1979),
the regularized analogue of `eq:compactness` (line 1292). The proof
delegates to the Phase-1 primitive
`weakSeqCompact_of_bounded_reflexive` and uses sequential closedness of
`S` to retain the constraint at the limit. -/
theorem exists_weak_limit_sequence
    [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
    (hX : IsReflexiveNormedSpace X)
    (z_n : ℕ → X) (hb : IsBounded (Set.range z_n))
    {S : Set (WeakSpace ℝ X)} (hS : IsSeqClosed S)
    (hmem : ∀ n, (toWeakSpace ℝ X) (z_n n) ∈ S) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ X),
      StrictMono φ ∧ z ∈ S ∧
        Tendsto (fun k => (toWeakSpace ℝ X) (z_n (φ k))) atTop (𝓝 z) := by
  obtain ⟨φ, hφ_mono, z, hz⟩ :=
    weakSeqCompact_of_bounded_reflexive hX z_n hb
  refine ⟨φ, z, hφ_mono, ?_, hz⟩
  -- The subsequence `(toWeakSpace ℝ X) (z_n (φ k))` lies in `S` for every `k`,
  -- and converges to `z`; sequential closedness gives `z ∈ S`.
  exact hS (fun k => hmem (φ k)) hz

/-! ## Pair-shaped specialisation

In the paper, the ambient reflexive space is the *product*
`L^{β̄}_per × W^{1,γ̄}_per`, and the cone constraint `m ≥ 0 a.e.` only
involves the first factor. The pair-shaped lemma below isolates that
factor: the user supplies a sequentially weakly closed subset
`S₁ ⊆ WeakSpace ℝ Y` controlling the `m_n` component, and we lift it to
a sequentially weakly closed subset of `WeakSpace ℝ (Y × Z)` via the
first-coordinate projection.
-/

variable {Y Z : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The first-coordinate projection `WeakSpace ℝ (Y × Z) → WeakSpace ℝ Y`,
defined as `WeakSpace.map (ContinuousLinearMap.fst ℝ Y Z)`. As
`WeakSpace ℝ E` is a type synonym for `E` carrying the weak topology,
this is the underlying projection `Prod.fst` viewed between weak spaces.

(Local re-definition to keep this module independent of
`Theorems/SimplePower/Compactness.lean`; structurally identical to the
Phase-4 `SimplePower.weakProdFst`.) -/
def weakProdFst :
    WeakSpace ℝ (Y × Z) → WeakSpace ℝ Y :=
  WeakSpace.map (ContinuousLinearMap.fst ℝ Y Z)

/-- Continuity of `weakProdFst` between weak topologies; immediate from
`WeakSpace.map` being a continuous linear map. -/
lemma continuous_weakProdFst :
    Continuous (weakProdFst (Y := Y) (Z := Z)) :=
  (WeakSpace.map (ContinuousLinearMap.fst ℝ Y Z)).continuous

/-- Pull back a sequentially closed subset of `WeakSpace ℝ Y` along the
first-coordinate projection to a sequentially closed subset of
`WeakSpace ℝ (Y × Z)`. -/
lemma isSeqClosed_preimage_weakProdFst
    {S₁ : Set (WeakSpace ℝ Y)} (hS₁ : IsSeqClosed S₁) :
    IsSeqClosed ((weakProdFst (Y := Y) (Z := Z)) ⁻¹' S₁) := by
  intro w wlim hmem hconv
  -- `weakProdFst` is continuous, so `weakProdFst ∘ w → weakProdFst wlim`.
  have hcont : Continuous (weakProdFst (Y := Y) (Z := Z)) :=
    continuous_weakProdFst
  have htend : Tendsto (fun n => weakProdFst (w n)) atTop
      (𝓝 (weakProdFst wlim)) := hcont.tendsto wlim |>.comp hconv
  exact hS₁ (fun n => hmem n) htend

/-- **Pair-shaped weak limit extraction (Phase-6).**

Bounded sequence `(m_n, u_n)` in a reflexive product `Y × Z` (with
separable strong dual), with the first coordinate trapped in a
sequentially weakly closed set `S₁ ⊆ WeakSpace ℝ Y`: extract a weakly
convergent subsequence whose first-coordinate limit lies in `S₁`. The
intended application is `Y := L^{β̄}_per`, `Z := W^{1,γ̄}_per`, and
`S₁ := {m | m ≥ 0 a.e.}`. -/
theorem exists_weak_limit_sequence_pair
    [TopologicalSpace.SeparableSpace (StrongDual ℝ (Y × Z))]
    (hYZ : IsReflexiveNormedSpace (Y × Z))
    (z_n : ℕ → Y × Z) (hb : IsBounded (Set.range z_n))
    {S₁ : Set (WeakSpace ℝ Y)} (hS₁ : IsSeqClosed S₁)
    (hmem₁ : ∀ n,
      weakProdFst ((toWeakSpace ℝ (Y × Z)) (z_n n)) ∈ S₁) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ (Y × Z)),
      StrictMono φ ∧ weakProdFst z ∈ S₁ ∧
        Tendsto (fun k => (toWeakSpace ℝ (Y × Z)) (z_n (φ k))) atTop (𝓝 z) := by
  -- Lift `S₁` to a sequentially weakly closed subset of the product, and
  -- apply `exists_weak_limit_sequence`.
  set S : Set (WeakSpace ℝ (Y × Z)) :=
    (weakProdFst (Y := Y) (Z := Z)) ⁻¹' S₁ with hS_def
  have hS_closed : IsSeqClosed S :=
    isSeqClosed_preimage_weakProdFst hS₁
  have hmem : ∀ n, (toWeakSpace ℝ (Y × Z)) (z_n n) ∈ S := fun n => hmem₁ n
  obtain ⟨φ, z, hmono, hzS, hzlim⟩ :=
    exists_weak_limit_sequence hYZ z_n hb hS_closed hmem
  exact ⟨φ, z, hmono, hzS, hzlim⟩

/-! ## Non-negativity preservation under weak limits

Closedness of the positive cone in `L^{β̄}` under weak convergence is the
content of the paper's "convex closed set ⇒ weakly closed" step (paper
line 1982). We expose that closedness as a hypothesis
`IsSeqClosed S₁`; concrete applications supply it from the convex-cone
argument (a separate Phase-1 follow-up will provide this for the
specific cone `{m ≥ 0 a.e.}` in `L^p_per`).
-/

/-! ## Sanity check

A worked instance at the project's `(p = 2)` calibration, where
reflexivity is provided by `lpSobolev_product_isReflexive_two`. The
example mirrors the Phase-4 sanity check in
`Theorems/SimplePower/Compactness.lean`, but routes through the local
`weakProdFst` rather than the Phase-4 definition. -/

/-- **Paper compactness target (Phase-6 shape).** Every bounded
sequence `(m_n, u_n)` in `L^2_per × W^{1,2}_per` whose first-coordinate
weak images stay in a sequentially weakly closed set admits a weakly
convergent subsequence with first-coordinate limit in the constraint
set. This is the structural shape of paper `eq:compactness.delta`. -/
example (d : ℕ)
    [TopologicalSpace.SeparableSpace
      (StrongDual ℝ
        ((MeasureTheory.Lp ℝ 2
            (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
          SobolevPerLp 1 2 d))]
    (z_n : ℕ →
      ((MeasureTheory.Lp ℝ 2
          (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
        SobolevPerLp 1 2 d))
    (hb : IsBounded (Set.range z_n))
    {S₁ : Set (WeakSpace ℝ
      (MeasureTheory.Lp ℝ 2
        (MeasureTheory.Measure.restrict (volume) (UnitCube d))))}
    (hS₁ : IsSeqClosed S₁)
    (hmem₁ : ∀ n,
      weakProdFst ((toWeakSpace ℝ _) (z_n n)) ∈ S₁) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ _),
      StrictMono φ ∧ weakProdFst z ∈ S₁ ∧
        Tendsto (fun k => (toWeakSpace ℝ _) (z_n (φ k))) atTop (𝓝 z) :=
  exists_weak_limit_sequence_pair
    (lpSobolev_product_isReflexive_two (d := d)) z_n hb hS₁ hmem₁

/-! ## Phase 7 T3 drain — sub-task A3 — closed weak-compactness producer

Paper reference: `Source/FGU-monotone_revised.tex`, line 1979,
`eq:compactness.delta`.

This section is the Theorem-3 analogue of the Theorem-2 producer
`Theorems.Congestion.Compactness.congestionWeakLimit_of_paperHypotheses`.
It assembles, from the uniform-in-`ε` a-priori bound (the output of
sub-task A2, the `AprioriDrain` weak-power-growth coercive engine)
realised as a *uniform-in-`n`* bound on a Banach lift of the
regularised sequence, the weak-limit data
`(m, u, Du)` in `L^{β̄}_per × W^{1,γ̄}_per` with the cone constraint
`0 ≤ m` a.e. preserved.

### Genuinely proved here (not deferred)

* the **weak-compactness extraction** itself, via
  `exists_weak_limit_sequence_pair` applied to the supplied bounded
  Banach sequence `pack.vEps` with `pack.hBound`, taking the constraint
  set `S₁ := (toWeakSpace ℝ _) '' nonNegConeLpPer βBar d` and sealing
  it sequentially-weakly-closed by `nonNegConeLpPer_isSeqClosedW`
  (Mazur: convex + norm-closed ⇒ weakly closed; paper line 1982);
* the **per-`n` cone membership** `(pack.vEps n).1 ∈ nonNegConeLpPer …`,
  derived in-body from the supplied per-`n` non-negativity `pack.hMnn`
  and the a.e.-bridge `pack.haeM`;
* the output **`m_nonneg`** (`0 ≤ m` a.e.), genuinely derived by
  transporting the named-representative cone membership
  `pack.hMLimBanach_nn` across the periodic-representative bridge
  `pack.haeMLim` (`filter_upwards`).

### Bridge-deferred (carried as pack fields, mirroring T2)

The Banach lift `vEps` of the bare regularised triple, the
uniform-in-`n` bound `hBound`, generic-exponent reflexivity `hRefl` and
strong-dual separability `hSep`, the named Banach representatives, and
the periodic-representative bridges. These are exactly the
Path-A / generic-`Lᵖ`-infrastructure items the T2 pack also defers
(see `CongestionWeakCompactnessUpstreamPack`); they are upstream of the
compactness extraction, not produced by it.

### Scope

A3 produces the `(m, u, Du, mLp, uSob, m_nonneg)` cluster of
`H6WeakGrowthUpstreamPack`. The remaining field `hWeakVI`
(`IsWeakSolution …`) is the *limit-passage* arrow handled by sub-task
A4; it is not part of the compactness step. -/

open StationaryMFG.Periodic
  (LpPer SobolevPerLp MemLpPer MemSobolevPer IsPeriodic HasWeakDerivPer)
open StationaryMFG.Theorems.SimplePower.Banach
  (nonNegConeLpPer nonNegConeLpPer_isSeqClosedW)

variable {d : ℕ}

/-- **T3 upstream Banach-realisation pack** (paper `eq:compactness.delta`).

Bridge-deferred Banach items consumed by the A3 weak-compactness
producer `t3WeakCompactness_of_uniformBound`. The layout mirrors the
T2 `CongestionWeakCompactnessUpstreamPack` (same Path-A obstructions):
the per-`n` Banach lift `vEps` of the bare regularised triple, the
uniform-in-`n` norm bound `hBound` (discharged from the A2 uniform
a-priori constant), generic reflexivity / separability of the product,
the per-`n` a.e.-bridge `haeM` and non-negativity `hMnn`, and the named
Banach representative `mLimBanach` with its cone membership
`hMLimBanach_nn`, together with the chosen periodic representatives
`mLim/uLim/DuLim` and their regularity certificates. -/
structure T3WeakCompactnessUpstreamPack
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (betaBar gammaBar : ℝ≥0∞) where
  /-- `1 ≤ β̄` (Mathlib `Lp` infrastructure requirement). -/
  hβFact : Fact (1 ≤ betaBar)
  /-- `1 ≤ γ̄` (Mathlib `Lp` infrastructure requirement). -/
  hγFact : Fact (1 ≤ gammaBar)
  /-- The per-`n` Banach realisation of the regularised triple
  `(m_{ε_n}, u_{ε_n}, Du_{ε_n})` in the reflexive product. -/
  vEps : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d
  /-- Uniform-in-`n` norm bound, discharged from the A2 uniform
  a-priori constant. -/
  hBound : IsBounded (Set.range vEps)
  /-- Reflexivity of the product Banach space. -/
  hRefl : IsReflexiveNormedSpace (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
  /-- Strong-dual separability of the product. -/
  hSep : TopologicalSpace.SeparableSpace
    (StrongDual ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d))
  /-- Per-`n` non-negativity of the `m`-component representative
  (paper cone constraint, surviving from the regularised sequence). -/
  hMnn : ∀ n,
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑(vEps n).1 : (Fin d → ℝ) → ℝ)
  /-- Named Banach representative for the `m`-limit. -/
  mLimBanach : LpPer betaBar d
  /-- Cone membership of the named `m`-limit representative. -/
  hMLimBanach_nn :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- Chosen bare-function `m`-limit (periodic representative). -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen bare-function `u`-limit. -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen bare-function weak-derivative family. -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- `mLim ∈ L^{β̄}_per`. -/
  hMlim_memLp : MemLpPer betaBar mLim
  /-- `uLim ∈ W^{1,γ̄}_per`. -/
  hUlim_sob : MemSobolevPer gammaBar uLim
  /-- Weak-derivative relation between `uLim` and `DuLim`. -/
  hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i)
  /-- Each weak-derivative component lives in `L^{γ̄}_per`. -/
  hDuLim_memGamma : ∀ i, MemLpPer gammaBar (DuLim i)
  /-- Periodic-representative bridge for `mLimBanach`: the chosen
  periodic `mLim` is a.e.-equal to the named Banach representative. -/
  haeMLim :
    mLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ)

/-- **T3 weak-limit output record** (paper `eq:compactness.delta`).

Records the outcome of the A3 compactness extraction: the strictly
monotone subsequence `φ`, the chosen bare-function limits
`(m, u, Du)`, their `Lᵖ` / Sobolev regularity, the weak-derivative
relation, the cone-preservation `0 ≤ m` a.e., and the abstract
weak-convergence-with-cone statement on the Banach pair sequence
`pack.vEps`. -/
structure T3WeakLimitData
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {betaBar gammaBar : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    (pack : T3WeakCompactnessUpstreamPack V H DpH betaBar gammaBar) where
  /-- Strictly monotone subsequence index. -/
  φ : ℕ → ℕ
  /-- The subsequence index is strictly increasing. -/
  hMono : StrictMono φ
  /-- Bare-function `m`-limit. -/
  m : (Fin d → ℝ) → ℝ
  /-- Bare-function `u`-limit. -/
  u : (Fin d → ℝ) → ℝ
  /-- Bare-function weak-derivative family for `u`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `0 ≤ m` a.e. (paper cone-preservation step, derived in-body via
  the named-representative cone membership transported across the
  periodic-representative bridge). -/
  m_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] m
  /-- `m ∈ L^{β̄}_per`. -/
  mLp : MemLpPer betaBar m
  /-- `u ∈ W^{1,γ̄}_per`. -/
  uSob : MemSobolevPer gammaBar u
  /-- Weak-derivative relation between `u` and `Du`. -/
  hDuWeak : ∀ i, HasWeakDerivPer i u (Du i)
  /-- Each weak-derivative component lives in `L^{γ̄}_per`. -/
  hDu_memGamma : ∀ i, MemLpPer gammaBar (Du i)
  /-- **Abstract weak convergence with cone preservation.** The Banach
  pair sequence along the extracted subsequence `φ` converges weakly to
  a cluster point `z` whose first projection lies in the (image of the)
  non-negativity cone `nonNegConeLpPer betaBar d`. This output field
  materially exercises both the per-`n` cone membership and the
  weak-compactness extraction with Mazur sequential closedness. -/
  hWeakConvCone :
    ∃ z : WeakSpace ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d),
      weakProdFst z ∈ (toWeakSpace ℝ (LpPer betaBar d)) ''
          nonNegConeLpPer betaBar d
        ∧ Tendsto (fun k => (toWeakSpace ℝ
            (LpPer betaBar d × SobolevPerLp 1 gammaBar d))
            (pack.vEps (φ k))) atTop (𝓝 z)

/-- **Phase 7 T3 producer (sub-task A3)** (paper `eq:compactness.delta`,
line 1979).

Given the upstream Banach-realisation pack
`T3WeakCompactnessUpstreamPack` (whose `hBound` is discharged from the
A2 uniform a-priori bound), produce a `T3WeakLimitData` recording the
extracted subsequence, the bare-function weak limits, their regularity,
and the cone-preservation `0 ≤ m` a.e.

The producer GENUINELY runs the weak-compactness extraction:

1. seal the non-negativity cone sequentially-weakly-closed via
   `nonNegConeLpPer_isSeqClosedW` (Mazur);
2. certify per-`n` cone membership of `(pack.vEps n).1` from
   `pack.hMnn`;
3. invoke `exists_weak_limit_sequence_pair` on `pack.vEps`,
   `pack.hBound`, with reflexivity `pack.hRefl` and separability
   `pack.hSep`, producing `(φ, z, hMono, hzS, hzLim)`;
4. derive `m_nonneg` by transporting `pack.hMLimBanach_nn` across
   `pack.haeMLim`. -/
noncomputable def t3WeakCompactness_of_uniformBound
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar gammaBar : ℝ≥0∞}
    (pack : T3WeakCompactnessUpstreamPack V H DpH betaBar gammaBar) :
    haveI : Fact (1 ≤ betaBar) := pack.hβFact
    haveI : Fact (1 ≤ gammaBar) := pack.hγFact
    T3WeakLimitData V H DpH pack := by
  haveI : Fact (1 ≤ betaBar) := pack.hβFact
  haveI : Fact (1 ≤ gammaBar) := pack.hγFact
  haveI : TopologicalSpace.SeparableSpace
            (StrongDual ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) :=
    pack.hSep
  -- (1) The non-negativity cone is sequentially weakly closed (Mazur).
  have hS_closed :
      IsSeqClosed
        ((toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d) :=
    nonNegConeLpPer_isSeqClosedW
  -- (2) Per-`n` cone membership of the `m`-component, lifted to the
  -- weak image.
  have hmem₁ : ∀ n,
      weakProdFst ((toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) (pack.vEps n)) ∈
        (toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d := by
    intro n
    refine ⟨(pack.vEps n).1, pack.hMnn n, ?_⟩
    -- `weakProdFst (toWeakSpace _ v) = toWeakSpace _ v.1` definitionally
    -- (`weakProdFst = WeakSpace.map (fst)` and `toWeakSpace` is the
    -- identity on the underlying type).
    rfl
  -- (3) Run the genuine weak-compactness extraction. The extraction
  -- theorem returns a `Prop`-valued existential, so the data
  -- `φ` is selected via `Classical.choose` (the structure's `φ`
  -- field is `Type`-valued; we cannot `obtain` from a `Prop` `∃`
  -- into a `Type` goal). The `Prop`-valued fields `hMono` and
  -- `hWeakConvCone` are then derived from the choose-spec.
  have hex :
      ∃ (φ : ℕ → ℕ)
        (z : WeakSpace ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d)),
        StrictMono φ ∧
          weakProdFst z ∈
              (toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d ∧
          Tendsto (fun k => (toWeakSpace ℝ
              (LpPer betaBar d × SobolevPerLp 1 gammaBar d))
              (pack.vEps (φ k))) atTop (𝓝 z) :=
    exists_weak_limit_sequence_pair (Y := LpPer betaBar d)
      (Z := SobolevPerLp 1 gammaBar d)
      pack.hRefl pack.vEps pack.hBound hS_closed hmem₁
  -- (4) Cone preservation for the chosen bare `m`-limit, transported
  -- across the periodic-representative bridge.
  have hMlim_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        pack.mLim := by
    filter_upwards [pack.hMLimBanach_nn, pack.haeMLim] with x hxnn hxeq
    rw [hxeq]
    exact hxnn
  refine
    { φ := hex.choose
      hMono := ?_
      m := pack.mLim
      u := pack.uLim
      Du := pack.DuLim
      m_nonneg := hMlim_nn
      mLp := pack.hMlim_memLp
      uSob := pack.hUlim_sob
      hDuWeak := pack.hDuLimWeak
      hDu_memGamma := pack.hDuLim_memGamma
      hWeakConvCone := ?_ }
  · -- `StrictMono (hex.choose)` from the choose-spec.
    obtain ⟨z, hMono, _, _⟩ := hex.choose_spec
    exact hMono
  · -- Abstract weak-convergence-with-cone over the chosen subsequence.
    obtain ⟨z, _, hzS, hzLim⟩ := hex.choose_spec
    exact ⟨z, hzS, hzLim⟩

/-- **Sanity-check `example` for the A3 producer.** A pure type-check
that the producer turns a `T3WeakCompactnessUpstreamPack` into a
`T3WeakLimitData`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar gammaBar : ℝ≥0∞}
    (pack : T3WeakCompactnessUpstreamPack V H DpH betaBar gammaBar) :
    haveI : Fact (1 ≤ betaBar) := pack.hβFact
    haveI : Fact (1 ≤ gammaBar) := pack.hγFact
    T3WeakLimitData V H DpH pack :=
  t3WeakCompactness_of_uniformBound pack

/-! ## Phase 7 T3 drain — sub-task A3b — Banach-realisation producer

Paper reference: `Source/FGU-monotone_revised.tex`, line 1979,
`eq:compactness.delta`.

This section discharges the **genuinely paper-derivable** Banach-realisation
fields of `T3WeakCompactnessUpstreamPack` from the A2 uniform-in-`ε`
a-priori bound (the `AprioriDrain` weak-power-growth coercive engine):

* `vEps` — the per-`n` Banach lift `(m_n, u_n, Du_n) ↦ (toLp, toLpSobolev)`
  of the regularised triple, built directly from per-`n` `MemLpPer` /
  `MemSobolevPer` certificates (no Banach–Alaoglu / weak-limit input);
* `hMnn` — per-`n` cone membership `0 ≤ᵐ ⇑(vEps n).1`, transported from
  the bare-function nonnegativity `0 ≤ᵐ m n` across the `MemLp.coeFn_toLp`
  a.e.-bridge;
* `hBound` — the uniform-in-`n` norm bound, derived from the A2 uniform
  constant via the product-pair-norm translation
  `MemLpPer.norm_pair_rpow_le` (Sobolev.lean).

These are the T3 analogues of the T2 producers
`congestionBanachRealisation_vEps_of_paperHypotheses` /
`congestionWeakCompactness_hBound_of_aprioriBounds`. The remaining fields
(`hRefl`/`hSep` reflexivity & separability, and the limit-selector group
`mLimBanach`/`hMLimBanach_nn`/periodic reps/regularity/`haeMLim`) are the
generic-exponent Path-A residue: at the **free** exponents `betaBar`,
`gammaBar` of this pack they cannot be pinned to the paper-canonical
conjugate values, so they are carried as honest inputs to the assembling
producer — exactly the T2 pattern where the generic-exponent oracle fed
those slots (`CongestionPack4BanachRealisationOracle`). This task drains
the three derivable fields; the limit-selector residue is a follow-up. -/

open MeasureTheory

/-- **T3 per-`n` Banach realisation (A3b, derivable).** The per-`n` lift
`(m_n, u_n, Du_n) ↦ ((hmLp n).toLp, (huSob n).toLpSobolev (hDuLp n))`
of the regularised triple into the reflexive product
`LpPer betaBar d × SobolevPerLp 1 gammaBar d`. T3 analogue of T2's
`congestionBanachRealisation_vEps_of_paperHypotheses`. -/
noncomputable def t3WeakCompactness_vEps_of_certs
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {m : ℕ → (Fin d → ℝ) → ℝ}
    {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    (n : ℕ) :
    LpPer betaBar d × SobolevPerLp 1 gammaBar d :=
  ((hmLp n).toLp, (huSob n).toLpSobolev (fun i => hDuLp n i))

/-- The `m`-component of `t3WeakCompactness_vEps_of_certs` is a.e.-equal
to the bare density `m n`. -/
lemma t3WeakCompactness_haeM_of_certs
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {m : ℕ → (Fin d → ℝ) → ℝ}
    {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    (n : ℕ) :
    m n
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).1
          : (Fin d → ℝ) → ℝ) :=
  (MeasureTheory.MemLp.coeFn_toLp (hmLp n)).symm

/-- **T3 per-`n` cone membership (A3b, derivable).** From bare-function
nonnegativity `0 ≤ᵐ m n` and the `MemLp.coeFn_toLp` a.e.-bridge,
`0 ≤ᵐ ⇑(vEps n).1`. -/
lemma t3WeakCompactness_hMnn_of_certs
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {m : ℕ → (Fin d → ℝ) → ℝ}
    {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    (hMnonneg : ∀ n,
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (m n))
    (n : ℕ) :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).1
        : (Fin d → ℝ) → ℝ) := by
  filter_upwards [hMnonneg n,
    t3WeakCompactness_haeM_of_certs hmLp huSob hDuLp n] with x hx hxeq
  rw [← hxeq]; exact hx

/-- **Discharge of `T3WeakCompactnessUpstreamPack.hBound` from the A2
uniform a-priori constant** (paper `eq:compactness.delta`, line 1979).

Given a uniform-in-`n` integrated bound of the A2 shape
`∫|m n|^{β̄.toReal} + ∫|u n|^{γ̄.toReal} + ∑ᵢ ∫|Du n i|^{γ̄.toReal} ≤ C`
(with `0 ≤ C`) at the **pack exponents** `betaBar`, `gammaBar`, the range
of the per-`n` Banach lift `vEps = t3WeakCompactness_vEps_of_certs …` is
norm-bounded.

The chain mirrors T2's `congestionWeakCompactness_hBound_of_aprioriBounds`:
`MemLpPer.norm_pair_rpow_le` translates each per-`n` Banach factor norm to
the integrated quantity the bound controls; `Prod.norm_def` combines the
two factors; dropping nonnegative summands isolates each factor `≤ C`. -/
lemma t3WeakCompactness_hBound_of_uniformBound
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    (hβ_zero : betaBar ≠ 0) (hβ_top : betaBar ≠ (⊤ : ℝ≥0∞))
    (hγ_zero : gammaBar ≠ 0) (hγ_top : gammaBar ≠ (⊤ : ℝ≥0∞))
    {m : ℕ → (Fin d → ℝ) → ℝ}
    {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hbound : ∀ n,
      (∫ x in UnitCube d, |m n x| ^ betaBar.toReal)
        + (∫ x in UnitCube d, |u n x| ^ gammaBar.toReal)
        + (∑ i, ∫ x in UnitCube d, |Du n i x| ^ gammaBar.toReal)
          ≤ C) :
    IsBounded (Set.range
      (t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp)) := by
  -- Real exponents are positive.
  have hβpos : 0 < betaBar.toReal := ENNReal.toReal_pos hβ_zero hβ_top
  have hγpos : 0 < gammaBar.toReal := ENNReal.toReal_pos hγ_zero hγ_top
  -- The two candidate uniform Banach-norm radii.
  set Dconst : ℝ := ((d : ℝ) + 1) ^ gammaBar.toReal with hDconst
  have hDconst_nn : 0 ≤ Dconst := Real.rpow_nonneg (by positivity) _
  set Rβ : ℝ := C ^ (betaBar.toReal⁻¹) with hRβ
  set Rγ : ℝ := (Dconst * C) ^ (gammaBar.toReal⁻¹) with hRγ
  have hRβ_nn : 0 ≤ Rβ := Real.rpow_nonneg hC_nn _
  have hDC_nn : 0 ≤ Dconst * C := mul_nonneg hDconst_nn hC_nn
  have hRγ_nn : 0 ≤ Rγ := Real.rpow_nonneg hDC_nn _
  refine isBounded_iff_forall_norm_le.mpr ⟨max Rβ Rγ, ?_⟩
  rintro x ⟨n, rfl⟩
  -- Nonnegativity of the three integrated summands.
  have hA_nn : 0 ≤ ∫ x in UnitCube d, |m n x| ^ betaBar.toReal :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hB_nn : 0 ≤ ∫ x in UnitCube d, |u n x| ^ gammaBar.toReal :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hC_nn' : 0 ≤ ∑ i, ∫ x in UnitCube d, |Du n i x| ^ gammaBar.toReal :=
    Finset.sum_nonneg (fun i _ =>
      integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))
  -- The product-pair-norm translation.
  obtain ⟨hpair_m, hpair_u⟩ :=
    MemLpPer.norm_pair_rpow_le (d := d) hβ_zero hβ_top hγ_zero hγ_top
      (hmLp n) (huSob n) (fun i => hDuLp n i)
  -- m-component: `‖(vEps n).1‖ ≤ Rβ`.
  have hm_bound :
      ‖(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).1‖ ≤ Rβ := by
    have hnn : 0 ≤ ‖(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).1‖ :=
      norm_nonneg _
    have h_pow_le :
        ‖(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).1‖ ^ betaBar.toReal
          ≤ C := by
      rw [show (t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).1
            = (hmLp n).toLp from rfl, hpair_m]
      linarith [hbound n, hB_nn, hC_nn']
    rw [hRβ]
    exact (Real.le_rpow_inv_iff_of_pos hnn hC_nn hβpos).mpr h_pow_le
  -- (u, Du)-component: `‖(vEps n).2‖ ≤ Rγ`.
  have hu_bound :
      ‖(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).2‖ ≤ Rγ := by
    have hnn : 0 ≤ ‖(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).2‖ :=
      norm_nonneg _
    have h_pow_le :
        ‖(t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).2‖ ^ gammaBar.toReal
          ≤ Dconst * C := by
      have h2 : (t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp n).2
          = (huSob n).toLpSobolev (fun i => hDuLp n i) := rfl
      rw [h2]
      calc ‖(huSob n).toLpSobolev (fun i => hDuLp n i)‖ ^ gammaBar.toReal
          ≤ Dconst *
              ((∫ x in UnitCube d, |u n x| ^ gammaBar.toReal)
                + ∑ i, ∫ x in UnitCube d, |Du n i x| ^ gammaBar.toReal) := by
              rw [hDconst]; exact hpair_u
        _ ≤ Dconst * C := by
              apply mul_le_mul_of_nonneg_left _ hDconst_nn
              linarith [hbound n, hA_nn]
    rw [hRγ]
    exact (Real.le_rpow_inv_iff_of_pos hnn hDC_nn hγpos).mpr h_pow_le
  -- Combine via the product norm.
  rw [Prod.norm_def]
  exact max_le (le_trans hm_bound (le_max_left _ _))
    (le_trans hu_bound (le_max_right _ _))

/-! ### Reflexivity / separability of the T3 product space at pinned exponents

Mirrors T2's `congestionOracle_hRefl`/`congestionOracle_hSep`: fed the
conjugate-exponent data (`ENNReal.HolderConjugate` instances + `1 < · < ∞`),
delegate to the project product lemmas
`Periodic.lpSobolev_product_isReflexive` /
`Periodic.lpSobolev_product_strongDual_separable`. No `0 < m`. -/

/-- **Reflexivity of the T3 product space at pinned exponents.** Mirrors
T2's `congestionOracle_hRefl`: fed the Hölder-conjugate data and
`1 < · < ∞`, delegates to `Periodic.lpSobolev_product_isReflexive`. -/
theorem t3WeakCompactness_hRefl_pinned
    {betaBar betaBar' gammaBar gammaBar' : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ betaBar')]
    [Fact (1 ≤ gammaBar)] [Fact (1 ≤ gammaBar')]
    [ENNReal.HolderConjugate betaBar betaBar']
    [ENNReal.HolderConjugate gammaBar gammaBar']
    (hβ_gt_one : 1 < betaBar) (hβ_ne_top : betaBar ≠ ∞)
    (hγ_gt_one : 1 < gammaBar) (hγ_ne_top : gammaBar ≠ ∞) :
    IsReflexiveNormedSpace
      (LpPer betaBar d × SobolevPerLp 1 gammaBar d) :=
  Periodic.lpSobolev_product_isReflexive (d := d)
    betaBar betaBar' gammaBar gammaBar'
    hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top

/-- **Strong-dual separability of the T3 product space at pinned
exponents.** Mirrors T2's `congestionOracle_hSep`: fed the
Hölder-conjugate data and `1 < · < ∞`, delegates to
`Periodic.lpSobolev_product_strongDual_separable`. -/
theorem t3WeakCompactness_hSep_pinned
    {betaBar betaBar' gammaBar gammaBar' : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ betaBar')]
    [Fact (1 ≤ gammaBar)] [Fact (1 ≤ gammaBar')]
    [ENNReal.HolderConjugate betaBar betaBar']
    [ENNReal.HolderConjugate gammaBar gammaBar']
    (hβ_gt_one : 1 < betaBar) (hβ_ne_top : betaBar ≠ ∞)
    (hγ_gt_one : 1 < gammaBar) (hγ_ne_top : gammaBar ≠ ∞) :
    TopologicalSpace.SeparableSpace
      (StrongDual ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) :=
  Periodic.lpSobolev_product_strongDual_separable (d := d)
    betaBar betaBar' gammaBar gammaBar'
    hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top

/-! ## Phase 7 T3 drain — sub-task A3c — component weak-pairing certs

Paper reference: `Source/FGU-monotone_revised.tex`, line 1979,
`eq:compactness.delta`.

The keystone limit-passage
`limit_passage_to_weak_VI_of_paperHypotheses`
(`LimitPassage.lean:879`) consumes, for each test pair, three
bare-function `WeakConvPairing_universal` certificates — for the
`m`-component, the gradient family `∂_i u`, and the `u`-component —
along the extracted subsequence. The A3 compactness output
`T3WeakLimitData.hWeakConvCone` exposes only an abstract weak cluster
point `z`; it carries no named `u`/`Du` Banach representatives and no
product `Tendsto` to a *named* tuple, so the keystone-shaped
certificates cannot be read off it directly.

This section provides the bridge producers, mirroring the T2 trio
`congestionWeakCert{M,U,Du}_of_banachLimit`
(`Congestion/Compactness.lean:2110-2300`). Each producer takes the A3b
realisation `vEps`, the extracted subsequence `φ`, the named Banach
limit representatives `(mLimBanach, uLimBanach, DuLimBanach)`, the
product weak-convergence `hWeakConv` of `vEps ∘ φ` to the named tuple,
and the periodic-representative a.e.-bridges, and yields the
keystone-shaped `WeakConvPairing_universal` certificate at the paper
real exponents `(βBar, βBar')` / `(γBar, γBar')`.

The substantive Mathlib-`Lp` → bare-function bridge is
`weakConvPairing_universal_of_toWeakSpace_conv`; the component
projection is performed by `t3WeakSpaceProj` (re-derived analogue of
the private T2 `congestionWeakSpaceProj`), and `hoelderPairing`
supplies the integral-pairing CLM.

`SobolevPerLp 1 p d = LpPer p d × (Fin d → LpPer p d)` (Sobolev.lean),
so the `u`-value and `∂_i u`-gradient projections of the product
`LpPer βBar d × SobolevPerLp 1 γBar d` are the standard `fst`/`snd`/
`proj` CLM composites, identical in shape to the T2 design. -/

/-- **Project a product `WeakSpace`-tendsto onto a component via a CLM.**

Re-derived analogue of the private T2 `congestionWeakSpaceProj`
(`Congestion/Compactness.lean`). Given a weak-convergence
`toWeakSpace _ (z_n n) → toWeakSpace _ z` in the product space
`LpPer betaBar d × SobolevPerLp 1 gammaBar d` and a continuous linear
projection `T` onto a single `LpPer p d` factor, push the weak limit
forward to `toWeakSpace _ (T (z_n n)) → toWeakSpace _ (T z)`. This is
the `WeakBilin.tendsto_iff_forall_eval_tendsto` round-trip shared by
the three component certificates. -/
private theorem t3WeakSpaceProj
    {betaBar gammaBar : ℝ≥0∞} {p : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)] [Fact (1 ≤ p)]
    (z_n : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d)
    (z : LpPer betaBar d × SobolevPerLp 1 gammaBar d)
    (T : (LpPer betaBar d × SobolevPerLp 1 gammaBar d) →L[ℝ] LpPer p d)
    (h : Tendsto
            (fun n => toWeakSpace ℝ
              (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (z_n n))
            atTop
            (𝓝 (toWeakSpace ℝ
              (LpPer betaBar d × SobolevPerLp 1 gammaBar d) z))) :
    Tendsto
      (fun n => toWeakSpace ℝ (LpPer p d) (T (z_n n)))
      atTop
      (𝓝 (toWeakSpace ℝ (LpPer p d) (T z))) := by
  -- Injectivity of the flipped top-dual pairing on both spaces.
  have h_inj_prod :
      Function.Injective
        ⇑(topDualPairing ℝ
            (LpPer betaBar d × SobolevPerLp 1 gammaBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : ((LpPer betaBar d × SobolevPerLp 1 gammaBar d)
                  →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  have h_inj :
      Function.Injective
        ⇑(topDualPairing ℝ (LpPer p d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : (LpPer p d →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  -- Universal-Λ form of the product tendsto.
  have hΛ_prod : ∀ Λ : (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
                          →L[ℝ] ℝ,
      Tendsto (fun n => Λ (z_n n)) atTop (𝓝 (Λ z)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ
              (LpPer betaBar d × SobolevPerLp 1 gammaBar d)).flip)
      h_inj_prod).mp h Λ
    change Tendsto (fun n => Λ (z_n n)) atTop (𝓝 (Λ z)) at hh
    exact hh
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := (topDualPairing ℝ (LpPer p d)).flip)
        h_inj).mpr ?_
  intro Λ
  have h_compose : Tendsto (fun n => Λ (T (z_n n))) atTop (𝓝 (Λ (T z))) := by
    have := hΛ_prod (Λ.comp T)
    simpa using this
  change Tendsto (fun n => Λ (T (z_n n))) atTop (𝓝 (Λ (T z)))
  exact h_compose

/-- **The integral-pairing CLM action against an `L^q` test (T3).**
Shared `Λφ_apply` discharge: the `hoelderPairing` CLM acts as
`∫ G · φ` once the `toLp`-representative is replaced by `φ` a.e. -/
private theorem t3Λφ_apply
    {p q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    [ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q)]
    (φ : (Fin d → ℝ) → ℝ) (hφ : MemLpPer (ENNReal.ofReal q) φ)
    (G : LpPer (ENNReal.ofReal p) d) :
    (StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing
        (p := p) (q := q) (φ := MemLpPer.toLp hφ)) G
      = ∫ x, (G x) * (φ x)
          ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  rw [StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing_apply]
  refine integral_congr_ae ?_
  have h_ae :
      ⇑(MemLpPer.toLp hφ) =ᵐ[MeasureTheory.Measure.restrict
          MeasureTheory.volume (UnitCube d)] φ :=
    MeasureTheory.MemLp.coeFn_toLp hφ
  filter_upwards [h_ae] with x hx
  rw [hx]

/-- **T3 `m`-component weak-pairing certificate (A3c).**

From the realisation sequence `vEps`, the extracted subsequence `φ`,
the named Banach reps, the product weak-convergence `hWeakConv` of
`vEps ∘ φ` to the named tuple, the per-`k` a.e.-bridge `haeM_n` and the
limit a.e.-bridge `haeM`, produce
`WeakConvPairing_universal hpqβ (fun k => m_n (φ k)) mLim` at the paper
exponents `(βBar, βBar')`. T3 analogue of
`congestionWeakCertM_of_banachLimit`. -/
theorem t3WeakCertM_of_banachWeakConv
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {βBar βBar' : ℝ} (hpqβ : βBar.HolderConjugate βBar')
    [Fact (1 ≤ ENNReal.ofReal βBar')]
    (hβBar_eq : ENNReal.ofReal βBar = betaBar)
    (vEps : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d)
    (φ : ℕ → ℕ)
    (mLimBanach : LpPer betaBar d)
    (uLimBanach : LpPer gammaBar d)
    (DuLimBanach : Fin d → LpPer gammaBar d)
    (hWeakConv :
      Tendsto
        (fun k => toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (vEps (φ k)))
        atTop
        (𝓝 (toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
          (mLimBanach, (uLimBanach, DuLimBanach)))))
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {mLim : (Fin d → ℝ) → ℝ}
    (haeM_n : ∀ k,
      m_n (φ k)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps (φ k)).1 : (Fin d → ℝ) → ℝ))
    (haeM :
      mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑mLimBanach : (Fin d → ℝ) → ℝ)) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqβ (fun k => m_n (φ k)) mLim := by
  classical
  subst hβBar_eq
  haveI : Fact (1 ≤ ENNReal.ofReal βBar) := ‹Fact (1 ≤ ENNReal.ofReal βBar)›
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBar)
            (ENNReal.ofReal βBar') :=
    Real.HolderConjugate.ennrealOfReal hpqβ
  -- The `fst` projection CLM onto the `m`-factor.
  set fst_clm : (LpPer (ENNReal.ofReal βBar) d × SobolevPerLp 1 gammaBar d)
                  →L[ℝ] LpPer (ENNReal.ofReal βBar) d :=
    ContinuousLinearMap.fst ℝ _ _ with hfst_def
  have hProj :
      Tendsto
        (fun k => toWeakSpace ℝ (LpPer (ENNReal.ofReal βBar) d)
          (fst_clm (vEps (φ k))))
        atTop
        (𝓝 (toWeakSpace ℝ (LpPer (ENNReal.ofReal βBar) d)
          (fst_clm (mLimBanach, (uLimBanach, DuLimBanach))))) :=
    t3WeakSpaceProj (fun k => vEps (φ k))
      (mLimBanach, (uLimBanach, DuLimBanach)) fst_clm hWeakConv
  refine StationaryMFG.Theorems.SimplePower.Banach.weakConvPairing_universal_of_toWeakSpace_conv
    (d := d) hpqβ
    (f_n := fun k => m_n (φ k)) (f := mLim)
    (fun k => (vEps (φ k)).1) mLimBanach
    haeM_n haeM hProj
    (fun φ hφ => StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing
      (φ := MemLpPer.toLp hφ))
    (fun φ hφ G => t3Λφ_apply φ hφ G)

/-- **T3 `u`-component weak-pairing certificate (A3c).** Projects
`hWeakConv` onto the value factor of the `SobolevPerLp` component
(`fst ∘ snd`) and feeds it through the bare-function bridge, producing
`WeakConvPairing_universal hpqγ (fun k => u_n (φ k)) uLim`. T3 analogue
of `congestionWeakCertU_of_banachLimit`. -/
theorem t3WeakCertU_of_banachWeakConv
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {γBar γBar' : ℝ} (hpqγ : γBar.HolderConjugate γBar')
    [Fact (1 ≤ ENNReal.ofReal γBar')]
    (hγBar_eq : ENNReal.ofReal γBar = gammaBar)
    (vEps : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d)
    (φ : ℕ → ℕ)
    (mLimBanach : LpPer betaBar d)
    (uLimBanach : LpPer gammaBar d)
    (DuLimBanach : Fin d → LpPer gammaBar d)
    (hWeakConv :
      Tendsto
        (fun k => toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (vEps (φ k)))
        atTop
        (𝓝 (toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
          (mLimBanach, (uLimBanach, DuLimBanach)))))
    {u_n : ℕ → (Fin d → ℝ) → ℝ} {uLim : (Fin d → ℝ) → ℝ}
    (haeU_n : ∀ k,
      u_n (φ k)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps (φ k)).2.1 : (Fin d → ℝ) → ℝ))
    (haeU :
      uLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑uLimBanach : (Fin d → ℝ) → ℝ)) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqγ (fun k => u_n (φ k)) uLim := by
  classical
  subst hγBar_eq
  haveI : Fact (1 ≤ ENNReal.ofReal γBar) := ‹Fact (1 ≤ ENNReal.ofReal γBar)›
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBar)
            (ENNReal.ofReal γBar') :=
    Real.HolderConjugate.ennrealOfReal hpqγ
  -- `fst ∘ snd` picks the value-component of the `SobolevPerLp` factor.
  set proj_clm : (LpPer betaBar d × SobolevPerLp 1 (ENNReal.ofReal γBar) d)
                  →L[ℝ] LpPer (ENNReal.ofReal γBar) d :=
    (ContinuousLinearMap.fst ℝ (LpPer (ENNReal.ofReal γBar) d)
        (Fin d → LpPer (ENNReal.ofReal γBar) d)).comp
      (ContinuousLinearMap.snd ℝ _ _) with hproj_def
  have hProj :
      Tendsto
        (fun k => toWeakSpace ℝ (LpPer (ENNReal.ofReal γBar) d)
          (proj_clm (vEps (φ k))))
        atTop
        (𝓝 (toWeakSpace ℝ (LpPer (ENNReal.ofReal γBar) d)
          (proj_clm (mLimBanach, (uLimBanach, DuLimBanach))))) :=
    t3WeakSpaceProj (fun k => vEps (φ k))
      (mLimBanach, (uLimBanach, DuLimBanach)) proj_clm hWeakConv
  refine StationaryMFG.Theorems.SimplePower.Banach.weakConvPairing_universal_of_toWeakSpace_conv
    (d := d) hpqγ
    (f_n := fun k => u_n (φ k)) (f := uLim)
    (fun k => (vEps (φ k)).2.1) uLimBanach
    haeU_n haeU hProj
    (fun φ hφ => StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing
      (φ := MemLpPer.toLp hφ))
    (fun φ hφ G => t3Λφ_apply φ hφ G)

/-- **T3 gradient-family weak-pairing certificates (A3c).** For each
direction `i`, projects `hWeakConv` onto the `i`-th gradient slot of the
`SobolevPerLp` component (`proj i ∘ snd ∘ snd`) and feeds it through the
bare-function bridge, producing
`WeakConvPairing_universal hpqγ (fun k => Du_n (φ k) i) (DuLim i)`. T3
analogue of `congestionWeakCertDu_of_banachLimit`. -/
theorem t3WeakCertDu_of_banachWeakConv
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {γBar γBar' : ℝ} (hpqγ : γBar.HolderConjugate γBar')
    [Fact (1 ≤ ENNReal.ofReal γBar')]
    (hγBar_eq : ENNReal.ofReal γBar = gammaBar)
    (vEps : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d)
    (φ : ℕ → ℕ)
    (mLimBanach : LpPer betaBar d)
    (uLimBanach : LpPer gammaBar d)
    (DuLimBanach : Fin d → LpPer gammaBar d)
    (hWeakConv :
      Tendsto
        (fun k => toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (vEps (φ k)))
        atTop
        (𝓝 (toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
          (mLimBanach, (uLimBanach, DuLimBanach)))))
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (haeDu_n : ∀ k i,
      Du_n (φ k) i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((vEps (φ k)).2.2 i) : (Fin d → ℝ) → ℝ))
    (haeDu : ∀ i,
      DuLim i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ)) :
    ∀ i, StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqγ (fun k => Du_n (φ k) i) (DuLim i) := by
  classical
  intro i
  subst hγBar_eq
  haveI : Fact (1 ≤ ENNReal.ofReal γBar) := ‹Fact (1 ≤ ENNReal.ofReal γBar)›
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBar)
            (ENNReal.ofReal γBar') :=
    Real.HolderConjugate.ennrealOfReal hpqγ
  -- `(proj i) ∘ snd ∘ snd` picks the `i`-th gradient component.
  set grad_clm : (LpPer betaBar d × SobolevPerLp 1 (ENNReal.ofReal γBar) d)
                  →L[ℝ] LpPer (ENNReal.ofReal γBar) d :=
    (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => LpPer (ENNReal.ofReal γBar) d) i).comp
      ((ContinuousLinearMap.snd ℝ (LpPer (ENNReal.ofReal γBar) d)
          (Fin d → LpPer (ENNReal.ofReal γBar) d)).comp
        (ContinuousLinearMap.snd ℝ _ _)) with hgrad_def
  have hProj :
      Tendsto
        (fun k => toWeakSpace ℝ (LpPer (ENNReal.ofReal γBar) d)
          (grad_clm (vEps (φ k))))
        atTop
        (𝓝 (toWeakSpace ℝ (LpPer (ENNReal.ofReal γBar) d)
          (grad_clm (mLimBanach, (uLimBanach, DuLimBanach))))) :=
    t3WeakSpaceProj (fun k => vEps (φ k))
      (mLimBanach, (uLimBanach, DuLimBanach)) grad_clm hWeakConv
  refine StationaryMFG.Theorems.SimplePower.Banach.weakConvPairing_universal_of_toWeakSpace_conv
    (d := d) hpqγ
    (f_n := fun k => Du_n (φ k) i) (f := DuLim i)
    (fun k => (vEps (φ k)).2.2 i) (DuLimBanach i)
    (fun k => haeDu_n k i) (haeDu i) hProj
    (fun φ hφ => StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing
      (φ := MemLpPer.toLp hφ))
    (fun φ hφ G => t3Λφ_apply φ hφ G)

/-! ## Sub-task A3e — named `u`/`Du` Banach reps + product tendsto

The A3c bridges `t3WeakCert{M,U,Du}_of_banachWeakConv` consume the named
Banach limit representatives `(mLimBanach, uLimBanach, DuLimBanach)`, the
extracted subsequence `φ`, the realisation sequence `vEps`, and the
product weak-convergence `hWeakConv` of `vEps ∘ φ` to the named tuple.

`T3WeakCompactnessUpstreamPack` and the pinned pack producers run the
genuine Banach–Alaoglu / Eberlein–Šmulian extraction
(`exists_weak_limit_sequence_pair` + Mazur `nonNegConeLpPer_isSeqClosedW`),
but read off only the `m`-component `z.1 = mLimBanach` and *discard*
`z.2.1`, `z.2.2`, and the cluster tendsto `hzLim`. This section exposes
those, mirroring T2's `CongestionBanachLimitResult`
(`Congestion/Compactness.lean:1433`) and its producer (~1508).

Because `SobolevPerLp 1 γ̄ d = LpPer γ̄ d × (Fin d → LpPer γ̄ d)`, the
cluster point `z : WeakSpace ℝ (LpPer β̄ d × SobolevPerLp 1 γ̄ d)` (defeq
to the product itself) decomposes as
`z.1 : LpPer β̄ d`, `z.2.1 : LpPer γ̄ d`, `z.2.2 : Fin d → LpPer γ̄ d`,
which are exactly the A3c bridge input types. -/

/-- **T3 Banach weak-limit result (A3e)** — the T3 analogue of T2's
`CongestionBanachLimitResult` (`Congestion/Compactness.lean:1433`).

Packages the extracted subsequence index `φ`, the named Banach
representatives `(mLimBanach, uLimBanach, DuLimBanach)` of the weak
limit of `(m_{ε_k}, u_{ε_k}, Du_{ε_k})`, the product weak-convergence
`hWeakConv` of the realisation subsequence `vEps ∘ φ` to the named tuple,
and the cone-preservation `hMLimBanach_nn`. Directly consumable by the
A3c bridges `t3WeakCert{M,U,Du}_of_banachWeakConv`. -/
structure T3BanachLimitResult
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (betaBar gammaBar : ℝ≥0∞)
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)] where
  /-- The per-`n` Banach realisation of the regularised triple. -/
  vEps : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d
  /-- Strictly monotone subsequence index of the extracted weakly
  convergent subsequence. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  hMono : StrictMono φ
  /-- Named Banach representative for the `m`-limit (`z.1`). -/
  mLimBanach : LpPer betaBar d
  /-- Named Banach representative for the `u`-limit (`z.2.1`). -/
  uLimBanach : LpPer gammaBar d
  /-- Named Banach representatives for the weak-derivative family
  (`z.2.2`). -/
  DuLimBanach : Fin d → LpPer gammaBar d
  /-- Product weak-convergence of the realisation subsequence to the
  named cluster point `(mLimBanach, (uLimBanach, DuLimBanach))`. -/
  hWeakConv :
    Tendsto
      (fun k => toWeakSpace ℝ
        (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (vEps (φ k)))
      atTop
      (𝓝 (toWeakSpace ℝ
        (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
        (mLimBanach, (uLimBanach, DuLimBanach))))
  /-- Cone-membership of the named Banach `m`-limit representative,
  preserved through the weak limit (Mazur). -/
  hMLimBanach_nn :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑mLimBanach : (Fin d → ℝ) → ℝ)

/-- **Composability witness (anti-sham) for A3e.** The named reps and
product tendsto of a `T3BanachLimitResult` feed directly into the A3c
bridge `t3WeakCertM_of_banachWeakConv`: given a `T3BanachLimitResult`,
the paper-exponent Hölder data and the periodic-representative bridges,
the keystone-shaped `WeakConvPairing_universal` certificate is produced
without re-assuming any of `vEps`/`φ`/`uLimBanach`/`DuLimBanach`/
`hWeakConv`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    (res : T3BanachLimitResult V H DpH betaBar gammaBar)
    {βBar βBar' : ℝ} (hpqβ : βBar.HolderConjugate βBar')
    [Fact (1 ≤ ENNReal.ofReal βBar')]
    (hβBar_eq : ENNReal.ofReal βBar = betaBar)
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {mLim : (Fin d → ℝ) → ℝ}
    (haeM_n : ∀ k,
      m_n (res.φ k)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(res.vEps (res.φ k)).1 : (Fin d → ℝ) → ℝ))
    (haeM :
      mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑res.mLimBanach : (Fin d → ℝ) → ℝ)) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqβ (fun k => m_n (res.φ k)) mLim :=
  t3WeakCertM_of_banachWeakConv hpqβ hβBar_eq res.vEps res.φ
    res.mLimBanach res.uLimBanach res.DuLimBanach res.hWeakConv
    haeM_n haeM

/-! ## Sub-task A3f — fully-closed pinned compactness pack producer

The earlier (now-inlined) A3d pinned pack still carried the Sobolev-side
limit-selector (`uLim`/`DuLim`/`hUlim_sob`/`hDuLimWeak`) as honest inputs.
This section discharges those four fields from the named Banach `u`-limit
representatives read off the Banach–Alaoglu / Eberlein–Šmulian extraction
(run inline below), mirroring the T2 plumbing
`congestionPeriodicReps_of_banachLimit` /
`congestionSobolevLimit_of_banachLimit`:

* periodic representatives `uLim`/`DuLim` of `uLimBanach`/`DuLimBanach`
  via `bareCoeFnOfLpPer`;
* `MemSobolevPer γ̄ uLim` and `HasWeakDerivPer i uLim (DuLim i)` via
  `Periodic.hasWeakDerivPer_of_weak_limit`, fed with
    - the per-`k` weak-derivative witnesses `hDuWeak_n (φ k) i` (a per-`ε_k`
      cert, allowed by the acceptance criterion);
    - smooth-tester convergence from the product `hWeakConv` via the
      SimplePower corollaries
      `tendsto_smoothTester_of_banachWeak_pair_snd_{val,grad}`, rewritten
      through the per-`k` and limit ae-bridges.

The remaining `m`-side fields are filled exactly as in A3d. The result is
a pinned producer with NO `uLim`/`DuLim`/`hUlim_sob`/`hDuLimWeak` inputs:
every `T3WeakCompactnessUpstreamPack` field is discharged from the
per-`ε_k` certs (`hmLp`/`huSob`/`hDuLp`/`hMnonneg`/`hDuWeak_n`), the A2
uniform bound, and the conjugate-exponent data. No `0 < m`, no oracle. -/

set_option maxHeartbeats 1000000 in
/-- **Phase 7 T3 fully-closed pinned compactness pack producer
(sub-task A3f)** (paper `eq:compactness.delta`, line 1979).

Assembles a `T3WeakCompactnessUpstreamPack` at the pinned paper exponents
`1 < β̄, γ̄ < ∞` with **no** Sobolev-side limit-selector inputs. Beyond the
A3d-discharged fields (`hRefl`/`hSep`/`vEps`/`hBound`/`hMnn`/`mLimBanach`/
`hMLimBanach_nn`/`mLim`/`hMlim_memLp`/`haeMLim`), it discharges
`uLim`/`DuLim`/`hUlim_sob`/`hDuLimWeak` from the named Banach `u`-limit
representatives of the Banach–Alaoglu / Eberlein–Šmulian extraction (run
inline), the periodization primitive `bareCoeFnOfLpPer`, and
`Periodic.hasWeakDerivPer_of_weak_limit` fed with the per-`ε_k`
weak-derivative certs and the SimplePower smooth-tester corollaries.

The only extra input over A3d is the per-`n` weak-derivative cert
`hDuWeak_n : ∀ n i, HasWeakDerivPer i (u n) (Du n i)` (the T3 analogue of
T2's `seq.hDu_weak`); the conjugate exponent `γ̄'` and its
`ENNReal.HolderConjugate γ̄ γ̄'` instance — already required by A3d for the
pinned reflexivity/separability — also drive the smooth-tester
corollaries. No `0 < m`, no oracle. -/
noncomputable def t3WeakCompactnessUpstreamPack_of_uniformBound_pinned_full
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar betaBar' gammaBar gammaBar' : ℝ≥0∞}
    (hβFact : Fact (1 ≤ betaBar)) (hγFact : Fact (1 ≤ gammaBar))
    [Fact (1 ≤ betaBar')] [Fact (1 ≤ gammaBar')]
    [ENNReal.HolderConjugate betaBar betaBar']
    [ENNReal.HolderConjugate gammaBar gammaBar']
    (hβ_gt_one : 1 < betaBar) (hβ_ne_top : betaBar ≠ ∞)
    (hγ_gt_one : 1 < gammaBar) (hγ_ne_top : gammaBar ≠ ∞)
    -- Per-`n` Banach-buildable certificates of the regularised triple.
    {m : ℕ → (Fin d → ℝ) → ℝ}
    {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    -- Per-`n` weak-derivative cert: `Du n` is the weak gradient of `u n`
    -- (the T3 analogue of T2's `seq.hDu_weak`; a per-`ε_k` cert).
    (hDuWeak_n : ∀ n i, HasWeakDerivPer i (u n) (Du n i))
    -- Per-`n` cone constraint (NONNEG track; NOT `0 < m`).
    (hMnonneg : ∀ n,
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (m n))
    -- A2 uniform-in-`n` integrated bound at the pack exponents.
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hbound : ∀ n,
      (∫ x in UnitCube d, |m n x| ^ betaBar.toReal)
        + (∫ x in UnitCube d, |u n x| ^ gammaBar.toReal)
        + (∑ i, ∫ x in UnitCube d, |Du n i x| ^ gammaBar.toReal)
          ≤ C) :
    T3WeakCompactnessUpstreamPack V H DpH betaBar gammaBar := by
  classical
  haveI := hβFact
  haveI := hγFact
  -- Reflexivity / separability at the pinned exponents.
  have hRefl : IsReflexiveNormedSpace
      (LpPer betaBar d × SobolevPerLp 1 gammaBar d) :=
    t3WeakCompactness_hRefl_pinned (d := d)
      (betaBar' := betaBar') (gammaBar' := gammaBar')
      hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top
  haveI hSep : TopologicalSpace.SeparableSpace
      (StrongDual ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) :=
    t3WeakCompactness_hSep_pinned (d := d)
      (betaBar' := betaBar') (gammaBar' := gammaBar')
      hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top
  -- Exponents are nonzero / finite (from `1 < · < ∞`).
  have hβ_zero : betaBar ≠ 0 := ne_of_gt (lt_trans zero_lt_one hβ_gt_one)
  have hγ_zero : gammaBar ≠ 0 := ne_of_gt (lt_trans zero_lt_one hγ_gt_one)
  -- The A3b-derivable per-`n` realisation, its uniform bound and cone.
  set vEps := t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp with hvEps_def
  have hBound : IsBounded (Set.range vEps) :=
    t3WeakCompactness_hBound_of_uniformBound hβ_zero hβ_ne_top hγ_zero hγ_ne_top
      hmLp huSob hDuLp hC_nn hbound
  have hMnn : ∀ n,
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps n).1 : (Fin d → ℝ) → ℝ) :=
    t3WeakCompactness_hMnn_of_certs hmLp huSob hDuLp hMnonneg
  -- Mazur: the non-negativity cone is sequentially weakly closed.
  have hS_closed :
      IsSeqClosed
        ((toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d) :=
    nonNegConeLpPer_isSeqClosedW
  have hmem₁ : ∀ n,
      weakProdFst ((toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) (vEps n)) ∈
        (toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d :=
    fun n => ⟨(vEps n).1, hMnn n, rfl⟩
  -- Run the genuine Banach–Alaoglu / Eberlein–Šmulian extraction.
  set hex :=
    exists_weak_limit_sequence_pair (Y := LpPer betaBar d)
      (Z := SobolevPerLp 1 gammaBar d) hRefl vEps hBound hS_closed hmem₁
    with hex_def
  let φ : ℕ → ℕ := hex.choose
  have hex2 := hex.choose_spec
  let z : WeakSpace ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d) :=
    hex2.choose
  obtain ⟨hMono, hzS, hzLim⟩ := hex2.choose_spec
  -- Named Banach representatives (`WeakSpace ℝ X` defeq `X`).
  set mLimBanach : LpPer betaBar d := z.1 with hmLimBanach_def
  set uLimBanach : LpPer gammaBar d := z.2.1 with huLimBanach_def
  set DuLimBanach : Fin d → LpPer gammaBar d := z.2.2 with hDuLimBanach_def
  -- Cone membership of the named `m`-limit representative (Mazur).
  have hMLimBanach_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ) := by
    obtain ⟨w, hw_mem, hw_eq⟩ := hzS
    have hw_eq' : w = mLimBanach := hw_eq
    exact hw_eq' ▸ hw_mem
  -- Periodic representatives of the named Banach reps.
  set mRep := StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) mLimBanach
    with hmRep_def
  set uRep := StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) uLimBanach
    with huRep_def
  -- `m`-side periodic bridges (mirror A3d).
  have haeMLim :
      mRep.rep
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑mLimBanach : (Fin d → ℝ) → ℝ) := mRep.ae_eq
  have hMlim_memLp : MemLpPer betaBar mRep.rep :=
    MeasureTheory.MemLp.ae_eq haeMLim.symm (MeasureTheory.Lp.memLp mLimBanach)
  -- `u`-side periodic representatives and ae-bridges.
  set uLim : (Fin d → ℝ) → ℝ := uRep.rep with huLim_def
  set DuLim : Fin d → (Fin d → ℝ) → ℝ :=
    fun i =>
      (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).rep
    with hDuLim_def
  have haeULim :
      uLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑uLimBanach : (Fin d → ℝ) → ℝ) := uRep.ae_eq
  have haeDuLim : ∀ i,
      DuLim i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ) := fun i =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).ae_eq
  -- The realisation sequence along `φ`, packaged for the tester corollaries.
  set zn : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d :=
    fun k => vEps (φ k) with hzn_def
  have hWeak' :
      Tendsto
        (fun k => toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (zn k))
        atTop
        (𝓝 (toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
          (mLimBanach, (uLimBanach, DuLimBanach)))) := hzLim
  -- Smooth-tester convergence on the `u`-value slot and the gradient slots.
  have hTestU :
      ∀ ψ : Periodic.SmoothPeriodic d,
        Tendsto
          (fun k => Periodic.periodicIntegral
            (fun x => (⇑(zn k).2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))
          atTop
          (𝓝 (Periodic.periodicIntegral
            (fun x => (⇑uLimBanach) x * (ψ : (Fin d → ℝ) → ℝ) x))) :=
    StationaryMFG.Theorems.SimplePower.Banach.tendsto_smoothTester_of_banachWeak_pair_snd_val
      (βBar := betaBar) (γBar := gammaBar) (γBar' := gammaBar')
      ‹ENNReal.HolderConjugate gammaBar gammaBar'› hγ_ne_top zn
      (mLimBanach, (uLimBanach, DuLimBanach)) hWeak'
  have hTestG :
      ∀ (i : Fin d) (ψ : Periodic.SmoothPeriodic d),
        Tendsto
          (fun k => Periodic.periodicIntegral
            (fun x => (⇑((zn k).2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x))
          atTop
          (𝓝 (Periodic.periodicIntegral
            (fun x => (⇑(DuLimBanach i)) x * (ψ : (Fin d → ℝ) → ℝ) x))) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.tendsto_smoothTester_of_banachWeak_pair_snd_grad
        (βBar := betaBar) (γBar := gammaBar) (γBar' := gammaBar')
        ‹ENNReal.HolderConjugate gammaBar gammaBar'› hγ_ne_top zn
        (mLimBanach, (uLimBanach, DuLimBanach)) hWeak' i
  -- Per-`k` ae-bridges to the bare functions (from `MemLp.coeFn_toLp`).
  have haeUk : ∀ k,
      u (φ k)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(zn k).2.1 : (Fin d → ℝ) → ℝ) :=
    fun k => (MeasureTheory.MemLp.coeFn_toLp (huSob (φ k)).1).symm
  have haeDuk : ∀ (k : ℕ) (i : Fin d),
      Du (φ k) i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((zn k).2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun k i => (MeasureTheory.MemLp.coeFn_toLp (hDuLp (φ k) i)).symm
  -- `MemLpPer γ̄ uLim` and per-`i` `MemLpPer 1 (DuLim i)`.
  have hUlim_memLp : MemLpPer gammaBar uLim :=
    MeasureTheory.MemLp.ae_eq haeULim.symm (MeasureTheory.Lp.memLp uLimBanach)
  have h1le_γ : (1 : ℝ≥0∞) ≤ gammaBar := le_of_lt hγ_gt_one
  have hDuLim_memLpγ : ∀ i, MemLpPer gammaBar (DuLim i) :=
    fun i => MeasureTheory.MemLp.ae_eq (haeDuLim i).symm
      (MeasureTheory.Lp.memLp (DuLimBanach i))
  have hDuLim_memLp1 : ∀ i, MemLpPer 1 (DuLim i) := fun i =>
    StationaryMFG.Periodic.MemLp.toMemLpPer
      ((hDuLim_memLpγ i).toMemLp.mono_exponent h1le_γ)
  -- Assemble `hDuLimWeak i` via the abstract weak-limit lemma.
  have hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i) := by
    intro i
    refine Periodic.hasWeakDerivPer_of_weak_limit
      (i := i) (u := uLim) (g := DuLim i)
      (uSeq := fun k => u (φ k))
      (gSeq := fun k => Du (φ k) i)
      (hDuLim_memLp1 i)
      (fun k => hDuWeak_n (φ k) i)
      ?_ ?_
    · -- `hConvU`: rewrite the tester convergence through the ae-bridges.
      intro ψ
      have hT := hTestU ψ
      have hfun : (fun k => Periodic.periodicIntegral
            (fun x => (⇑(zn k).2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x => u (φ k) x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeUk k] with x hx
        rw [hx]
      have hpt : Periodic.periodicIntegral
            (fun x => (⇑uLimBanach) x * (ψ : (Fin d → ℝ) → ℝ) x)
          = Periodic.periodicIntegral
            (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x) := by
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeULim] with x hx
        rw [hx]
      rw [hfun, hpt] at hT
      exact hT
    · -- `hConvG`: same, on the gradient slot.
      intro ψ
      have hT := hTestG i ψ
      have hfun : (fun k => Periodic.periodicIntegral
            (fun x => (⇑((zn k).2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x => Du (φ k) i x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeDuk k i] with x hx
        rw [hx]
      have hpt : Periodic.periodicIntegral
            (fun x => (⇑(DuLimBanach i)) x * (ψ : (Fin d → ℝ) → ℝ) x)
          = Periodic.periodicIntegral
            (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x) := by
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeDuLim i] with x hx
        rw [hx]
      rw [hfun, hpt] at hT
      exact hT
  -- Assemble the pack.
  exact
    { hβFact := hβFact
      hγFact := hγFact
      vEps := vEps
      hBound := hBound
      hRefl := hRefl
      hSep := hSep
      hMnn := hMnn
      mLimBanach := mLimBanach
      hMLimBanach_nn := hMLimBanach_nn
      mLim := mRep.rep
      uLim := uLim
      DuLim := DuLim
      hMlim_memLp := hMlim_memLp
      hUlim_sob := ⟨hUlim_memLp, DuLim, hDuLimWeak⟩
      hDuLimWeak := hDuLimWeak
      hDuLim_memGamma := hDuLim_memLpγ
      haeMLim := haeMLim }

/-- **Composability witness (anti-sham) for A3f.** Feed the fully-closed
pinned producer into the genuine weak-compactness extractor
`t3WeakCompactness_of_uniformBound`: certifies that the entirely
in-body-discharged pack (including the Sobolev-side limit-selector) is
accepted without re-assuming any `uLim`/`DuLim`/`hUlim_sob`/`hDuLimWeak`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar betaBar' gammaBar gammaBar' : ℝ≥0∞}
    (hβFact : Fact (1 ≤ betaBar)) (hγFact : Fact (1 ≤ gammaBar))
    [Fact (1 ≤ betaBar')] [Fact (1 ≤ gammaBar')]
    [ENNReal.HolderConjugate betaBar betaBar']
    [ENNReal.HolderConjugate gammaBar gammaBar']
    (hβ_gt_one : 1 < betaBar) (hβ_ne_top : betaBar ≠ ∞)
    (hγ_gt_one : 1 < gammaBar) (hγ_ne_top : gammaBar ≠ ∞)
    {m : ℕ → (Fin d → ℝ) → ℝ} {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    (hDuWeak_n : ∀ n i, HasWeakDerivPer i (u n) (Du n i))
    (hMnonneg : ∀ n,
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)] (m n))
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hbound : ∀ n,
      (∫ x in UnitCube d, |m n x| ^ betaBar.toReal)
        + (∫ x in UnitCube d, |u n x| ^ gammaBar.toReal)
        + (∑ i, ∫ x in UnitCube d, |Du n i x| ^ gammaBar.toReal) ≤ C) :
    haveI : Fact (1 ≤ betaBar) := hβFact
    haveI : Fact (1 ≤ gammaBar) := hγFact
    T3WeakLimitData V H DpH
      (t3WeakCompactnessUpstreamPack_of_uniformBound_pinned_full (V := V) (H := H)
        (DpH := DpH) (betaBar' := betaBar') (gammaBar' := gammaBar')
        hβFact hγFact hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top
        hmLp huSob hDuLp hDuWeak_n hMnonneg hC_nn hbound) :=
  haveI := hβFact
  haveI := hγFact
  t3WeakCompactness_of_uniformBound _

/-! ## Sub-task B2 (crux) — single shared weak-limit extraction

The keystone `LimitPassage.limit_passage_to_weak_VI_of_paperHypotheses`
needs, *for the SAME subsequence `φ` and the SAME limits*, both:

* the six geometric `T3WeakLimitData` fields (`m`/`u`/`Du` + regularity +
  `m_nonneg`), and
* the three `WeakConvPairing_universal` certs, which the A3c bridges
  `t3WeakCert{M,U,Du}_of_banachWeakConv` produce from the named Banach
  reps `(mLimBanach, uLimBanach, DuLimBanach)` + the product `hWeakConv`
  along `φ`, with the per-`k` ae-bridges
  `m_n (φ k) =ᵐ (vEps (φ k)).1`, etc.

The A3f `_full` producer runs its OWN `exists_weak_limit_sequence_pair`,
so its `φ`/limits are unrelated to any separate extraction and the certs
cannot be proved about `ld.m/u/Du` along `ld.φ`. `T3SharedExtraction`
fixes this: it runs the extraction ONCE and exposes every field downstream
needs, all about the one `φ`. The body is the merge of the (already green)
`_full` body with the named-Banach-rep extraction. No `0 < m`, no oracle. -/

/-- **Shared weak-limit extraction record (B2 crux).**

Packages, from a SINGLE `exists_weak_limit_sequence_pair` call: the
strictly-monotone subsequence index `φ`, the per-`n` Banach realisation
`vEps`, the named Banach limit reps `(mLimBanach, uLimBanach,
DuLimBanach)` with the product weak-convergence `hWeakConv` *along `φ`*,
the chosen periodic bare-function limits `(m, u, Du)` with their
`Lᵖ`/Sobolev regularity, weak-derivative relation, and cone preservation
`0 ≤ m`, AND the per-`k` ae-bridges linking the original sequences
`m_n/u_n/Du_n` (along `φ`) and the limits to the Banach
realisations/reps. The per-`k` ae-bridges + named reps + `hWeakConv` are
exactly the inputs the A3c certs require, so the certs are guaranteed to
be about `m`/`u`/`Du` along `φ`. -/
structure T3SharedExtraction
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (betaBar gammaBar : ℝ≥0∞)
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    (mSeq : ℕ → (Fin d → ℝ) → ℝ)
    (uSeq : ℕ → (Fin d → ℝ) → ℝ)
    (DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ) where
  /-- Strictly monotone subsequence index. -/
  φ : ℕ → ℕ
  /-- `φ` is strictly increasing. -/
  hMono : StrictMono φ
  /-- Per-`n` Banach realisation of the regularised triple. -/
  vEps : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d
  /-- Named Banach `m`-limit representative. -/
  mLimBanach : LpPer betaBar d
  /-- Named Banach `u`-limit representative. -/
  uLimBanach : LpPer gammaBar d
  /-- Named Banach weak-derivative limit representatives. -/
  DuLimBanach : Fin d → LpPer gammaBar d
  /-- Product weak-convergence of `vEps ∘ φ` to the named cluster. -/
  hWeakConv :
    Tendsto
      (fun k => toWeakSpace ℝ
        (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (vEps (φ k)))
      atTop
      (𝓝 (toWeakSpace ℝ
        (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
        (mLimBanach, (uLimBanach, DuLimBanach))))
  /-- Chosen periodic bare-function `m`-limit. -/
  m : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function `u`-limit. -/
  u : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function weak-derivative family. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `m ∈ L^{β̄}_per`. -/
  mLp : MemLpPer betaBar m
  /-- `u ∈ W^{1,γ̄}_per`. -/
  uSob : MemSobolevPer gammaBar u
  /-- Weak-derivative relation between `u` and `Du`. -/
  hDuWeak : ∀ i, HasWeakDerivPer i u (Du i)
  /-- Each weak-derivative component lives in `L^{γ̄}_per`. -/
  hDu_memGamma : ∀ i, MemLpPer gammaBar (Du i)
  /-- Cone preservation `0 ≤ m` a.e. -/
  m_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] m
  /-- Per-`k` ae-bridge for `mSeq` along `φ` (A3c cert input). -/
  haeM_n : ∀ k,
    mSeq (φ k)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps (φ k)).1 : (Fin d → ℝ) → ℝ)
  /-- Per-`k` ae-bridge for `uSeq` along `φ` (A3c cert input). -/
  haeU_n : ∀ k,
    uSeq (φ k)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps (φ k)).2.1 : (Fin d → ℝ) → ℝ)
  /-- Per-`k` ae-bridge for `DuSeq` along `φ` (A3c cert input). -/
  haeDu_n : ∀ (k : ℕ) (i : Fin d),
    DuSeq (φ k) i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑((vEps (φ k)).2.2 i) : (Fin d → ℝ) → ℝ)
  /-- Limit ae-bridge for `m` (A3c cert input). -/
  haeM :
    m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- Limit ae-bridge for `u` (A3c cert input). -/
  haeU :
    u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑uLimBanach : (Fin d → ℝ) → ℝ)
  /-- Limit ae-bridge for `Du` (A3c cert input). -/
  haeDu : ∀ i,
    Du i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ)

set_option maxHeartbeats 1000000 in
/-- **B2 crux producer — single shared weak-limit extraction.**

Runs `exists_weak_limit_sequence_pair` ONCE on `vEps := toLp` of the
regularised triple and reads off everything `T3SharedExtraction`
requires: the named Banach reps, the product `hWeakConv` along the
extracted `φ`, the periodic bare-function limits and their regularity,
the cone preservation, and all per-`k`/limit ae-bridges. Merges the
body of `t3WeakCompactnessUpstreamPack_of_uniformBound_pinned_full`
with the named-Banach-rep extraction so that the six geometric
fields and the A3c cert inputs come from the SAME extraction. -/
noncomputable def t3SharedExtraction_of_uniformBound_pinned
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar betaBar' gammaBar gammaBar' : ℝ≥0∞}
    (hβFact : Fact (1 ≤ betaBar)) (hγFact : Fact (1 ≤ gammaBar))
    [Fact (1 ≤ betaBar')] [Fact (1 ≤ gammaBar')]
    [ENNReal.HolderConjugate betaBar betaBar']
    [ENNReal.HolderConjugate gammaBar gammaBar']
    (hβ_gt_one : 1 < betaBar) (hβ_ne_top : betaBar ≠ ∞)
    (hγ_gt_one : 1 < gammaBar) (hγ_ne_top : gammaBar ≠ ∞)
    {m : ℕ → (Fin d → ℝ) → ℝ}
    {u : ℕ → (Fin d → ℝ) → ℝ}
    {Du : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : ∀ n, MemLpPer betaBar (m n))
    (huSob : ∀ n, MemSobolevPer gammaBar (u n))
    (hDuLp : ∀ n i, MemLpPer gammaBar (Du n i))
    (hDuWeak_n : ∀ n i, HasWeakDerivPer i (u n) (Du n i))
    (hMnonneg : ∀ n,
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (m n))
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hbound : ∀ n,
      (∫ x in UnitCube d, |m n x| ^ betaBar.toReal)
        + (∫ x in UnitCube d, |u n x| ^ gammaBar.toReal)
        + (∑ i, ∫ x in UnitCube d, |Du n i x| ^ gammaBar.toReal)
          ≤ C) :
    haveI : Fact (1 ≤ betaBar) := hβFact
    haveI : Fact (1 ≤ gammaBar) := hγFact
    T3SharedExtraction V H DpH betaBar gammaBar
      m u (fun n i => Du n i) := by
  classical
  haveI := hβFact
  haveI := hγFact
  -- Reflexivity / separability at the pinned exponents.
  have hRefl : IsReflexiveNormedSpace
      (LpPer betaBar d × SobolevPerLp 1 gammaBar d) :=
    t3WeakCompactness_hRefl_pinned (d := d)
      (betaBar' := betaBar') (gammaBar' := gammaBar')
      hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top
  haveI hSep : TopologicalSpace.SeparableSpace
      (StrongDual ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) :=
    t3WeakCompactness_hSep_pinned (d := d)
      (betaBar' := betaBar') (gammaBar' := gammaBar')
      hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top
  have hβ_zero : betaBar ≠ 0 := ne_of_gt (lt_trans zero_lt_one hβ_gt_one)
  have hγ_zero : gammaBar ≠ 0 := ne_of_gt (lt_trans zero_lt_one hγ_gt_one)
  set vEps := t3WeakCompactness_vEps_of_certs hmLp huSob hDuLp with hvEps_def
  have hBound : IsBounded (Set.range vEps) :=
    t3WeakCompactness_hBound_of_uniformBound hβ_zero hβ_ne_top hγ_zero hγ_ne_top
      hmLp huSob hDuLp hC_nn hbound
  have hMnn : ∀ n,
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps n).1 : (Fin d → ℝ) → ℝ) :=
    t3WeakCompactness_hMnn_of_certs hmLp huSob hDuLp hMnonneg
  have hS_closed :
      IsSeqClosed
        ((toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d) :=
    nonNegConeLpPer_isSeqClosedW
  have hmem₁ : ∀ n,
      weakProdFst ((toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)) (vEps n)) ∈
        (toWeakSpace ℝ (LpPer betaBar d)) '' nonNegConeLpPer betaBar d :=
    fun n => ⟨(vEps n).1, hMnn n, rfl⟩
  -- THE single extraction.
  set hex :=
    exists_weak_limit_sequence_pair (Y := LpPer betaBar d)
      (Z := SobolevPerLp 1 gammaBar d) hRefl vEps hBound hS_closed hmem₁
    with hex_def
  let φ : ℕ → ℕ := hex.choose
  have hex2 := hex.choose_spec
  let z : WeakSpace ℝ (LpPer betaBar d × SobolevPerLp 1 gammaBar d) :=
    hex2.choose
  obtain ⟨hMono, hzS, hzLim⟩ := hex2.choose_spec
  set mLimBanach : LpPer betaBar d := z.1 with hmLimBanach_def
  set uLimBanach : LpPer gammaBar d := z.2.1 with huLimBanach_def
  set DuLimBanach : Fin d → LpPer gammaBar d := z.2.2 with hDuLimBanach_def
  have hMLimBanach_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ) := by
    obtain ⟨w, hw_mem, hw_eq⟩ := hzS
    have hw_eq' : w = mLimBanach := hw_eq
    exact hw_eq' ▸ hw_mem
  -- Periodic representatives of the named Banach reps.
  set mRep := StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) mLimBanach
    with hmRep_def
  set uRep := StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) uLimBanach
    with huRep_def
  have haeMLim :
      mRep.rep
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑mLimBanach : (Fin d → ℝ) → ℝ) := mRep.ae_eq
  have hMlim_memLp : MemLpPer betaBar mRep.rep :=
    MeasureTheory.MemLp.ae_eq haeMLim.symm (MeasureTheory.Lp.memLp mLimBanach)
  set uLim : (Fin d → ℝ) → ℝ := uRep.rep with huLim_def
  set DuLim : Fin d → (Fin d → ℝ) → ℝ :=
    fun i =>
      (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).rep
    with hDuLim_def
  have haeULim :
      uLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑uLimBanach : (Fin d → ℝ) → ℝ) := uRep.ae_eq
  have haeDuLim : ∀ i,
      DuLim i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ) := fun i =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).ae_eq
  set zn : ℕ → LpPer betaBar d × SobolevPerLp 1 gammaBar d :=
    fun k => vEps (φ k) with hzn_def
  have hWeak' :
      Tendsto
        (fun k => toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d) (zn k))
        atTop
        (𝓝 (toWeakSpace ℝ
          (LpPer betaBar d × SobolevPerLp 1 gammaBar d)
          (mLimBanach, (uLimBanach, DuLimBanach)))) := hzLim
  have hTestU :
      ∀ ψ : Periodic.SmoothPeriodic d,
        Tendsto
          (fun k => Periodic.periodicIntegral
            (fun x => (⇑(zn k).2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))
          atTop
          (𝓝 (Periodic.periodicIntegral
            (fun x => (⇑uLimBanach) x * (ψ : (Fin d → ℝ) → ℝ) x))) :=
    StationaryMFG.Theorems.SimplePower.Banach.tendsto_smoothTester_of_banachWeak_pair_snd_val
      (βBar := betaBar) (γBar := gammaBar) (γBar' := gammaBar')
      ‹ENNReal.HolderConjugate gammaBar gammaBar'› hγ_ne_top zn
      (mLimBanach, (uLimBanach, DuLimBanach)) hWeak'
  have hTestG :
      ∀ (i : Fin d) (ψ : Periodic.SmoothPeriodic d),
        Tendsto
          (fun k => Periodic.periodicIntegral
            (fun x => (⇑((zn k).2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x))
          atTop
          (𝓝 (Periodic.periodicIntegral
            (fun x => (⇑(DuLimBanach i)) x * (ψ : (Fin d → ℝ) → ℝ) x))) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.tendsto_smoothTester_of_banachWeak_pair_snd_grad
        (βBar := betaBar) (γBar := gammaBar) (γBar' := gammaBar')
        ‹ENNReal.HolderConjugate gammaBar gammaBar'› hγ_ne_top zn
        (mLimBanach, (uLimBanach, DuLimBanach)) hWeak' i
  -- Per-`k` ae-bridges to the bare functions.
  have haeMk : ∀ k,
      m (φ k)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps (φ k)).1 : (Fin d → ℝ) → ℝ) :=
    fun k => (MeasureTheory.MemLp.coeFn_toLp (hmLp (φ k))).symm
  have haeUk : ∀ k,
      u (φ k)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(zn k).2.1 : (Fin d → ℝ) → ℝ) :=
    fun k => (MeasureTheory.MemLp.coeFn_toLp (huSob (φ k)).1).symm
  have haeDuk : ∀ (k : ℕ) (i : Fin d),
      Du (φ k) i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((zn k).2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun k i => (MeasureTheory.MemLp.coeFn_toLp (hDuLp (φ k) i)).symm
  have hUlim_memLp : MemLpPer gammaBar uLim :=
    MeasureTheory.MemLp.ae_eq haeULim.symm (MeasureTheory.Lp.memLp uLimBanach)
  have h1le_γ : (1 : ℝ≥0∞) ≤ gammaBar := le_of_lt hγ_gt_one
  have hDuLim_memLpγ : ∀ i, MemLpPer gammaBar (DuLim i) :=
    fun i => MeasureTheory.MemLp.ae_eq (haeDuLim i).symm
      (MeasureTheory.Lp.memLp (DuLimBanach i))
  have hDuLim_memLp1 : ∀ i, MemLpPer 1 (DuLim i) := fun i =>
    StationaryMFG.Periodic.MemLp.toMemLpPer
      ((hDuLim_memLpγ i).toMemLp.mono_exponent h1le_γ)
  have hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i) := by
    intro i
    refine Periodic.hasWeakDerivPer_of_weak_limit
      (i := i) (u := uLim) (g := DuLim i)
      (uSeq := fun k => u (φ k))
      (gSeq := fun k => Du (φ k) i)
      (hDuLim_memLp1 i)
      (fun k => hDuWeak_n (φ k) i)
      ?_ ?_
    · intro ψ
      have hT := hTestU ψ
      have hfun : (fun k => Periodic.periodicIntegral
            (fun x => (⇑(zn k).2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x => u (φ k) x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeUk k] with x hx
        rw [hx]
      have hpt : Periodic.periodicIntegral
            (fun x => (⇑uLimBanach) x * (ψ : (Fin d → ℝ) → ℝ) x)
          = Periodic.periodicIntegral
            (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x) := by
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeULim] with x hx
        rw [hx]
      rw [hfun, hpt] at hT
      exact hT
    · intro ψ
      have hT := hTestG i ψ
      have hfun : (fun k => Periodic.periodicIntegral
            (fun x => (⇑((zn k).2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x => Du (φ k) i x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeDuk k i] with x hx
        rw [hx]
      have hpt : Periodic.periodicIntegral
            (fun x => (⇑(DuLimBanach i)) x * (ψ : (Fin d → ℝ) → ℝ) x)
          = Periodic.periodicIntegral
            (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x) := by
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeDuLim i] with x hx
        rw [hx]
      rw [hfun, hpt] at hT
      exact hT
  -- Cone preservation transported to the chosen periodic `m`-limit.
  have hMlim_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        mRep.rep := by
    filter_upwards [hMLimBanach_nn, haeMLim] with x hxnn hxeq
    rw [hxeq]; exact hxnn
  exact
    { φ := φ
      hMono := hMono
      vEps := vEps
      mLimBanach := mLimBanach
      uLimBanach := uLimBanach
      DuLimBanach := DuLimBanach
      hWeakConv := hzLim
      m := mRep.rep
      u := uLim
      Du := DuLim
      mLp := hMlim_memLp
      uSob := ⟨hUlim_memLp, DuLim, hDuLimWeak⟩
      hDuWeak := hDuLimWeak
      hDu_memGamma := hDuLim_memLpγ
      m_nonneg := hMlim_nn
      haeM_n := haeMk
      haeU_n := haeUk
      haeDu_n := haeDuk
      haeM := haeMLim
      haeU := haeULim
      haeDu := haeDuLim }

/-- **B2 cert producers from the shared extraction (A3c bridges).** The
three `WeakConvPairing_universal` certs about the shared `φ`/limits,
proved by feeding the named Banach reps + product `hWeakConv` + per-`k`
ae-bridges of a `T3SharedExtraction` into the A3c bridges. This is the
anti-sham witness that the shared extraction's data is the right shape
for the keystone: the certs are about `ext.m`/`ext.u`/`ext.Du` along the
same `ext.φ` as the six geometric fields. -/
theorem t3SharedExtraction_weakCertM
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {mSeq uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (ext : T3SharedExtraction V H DpH betaBar gammaBar mSeq uSeq DuSeq)
    {βBar βBar' : ℝ} (hpqβ : βBar.HolderConjugate βBar')
    [Fact (1 ≤ ENNReal.ofReal βBar')]
    (hβBar_eq : ENNReal.ofReal βBar = betaBar) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqβ (fun k => mSeq (ext.φ k)) ext.m :=
  t3WeakCertM_of_banachWeakConv hpqβ hβBar_eq ext.vEps ext.φ
    ext.mLimBanach ext.uLimBanach ext.DuLimBanach ext.hWeakConv
    ext.haeM_n ext.haeM

/-- `u`-component cert from the shared extraction (A3c bridge). -/
theorem t3SharedExtraction_weakCertU
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {mSeq uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (ext : T3SharedExtraction V H DpH betaBar gammaBar mSeq uSeq DuSeq)
    {γBar γBar' : ℝ} (hpqγ : γBar.HolderConjugate γBar')
    [Fact (1 ≤ ENNReal.ofReal γBar')]
    (hγBar_eq : ENNReal.ofReal γBar = gammaBar) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqγ (fun k => uSeq (ext.φ k)) ext.u :=
  t3WeakCertU_of_banachWeakConv hpqγ hγBar_eq ext.vEps ext.φ
    ext.mLimBanach ext.uLimBanach ext.DuLimBanach ext.hWeakConv
    ext.haeU_n ext.haeU

/-- gradient-family cert from the shared extraction (A3c bridge). -/
theorem t3SharedExtraction_weakCertDu
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {mSeq uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (ext : T3SharedExtraction V H DpH betaBar gammaBar mSeq uSeq DuSeq)
    {γBar γBar' : ℝ} (hpqγ : γBar.HolderConjugate γBar')
    [Fact (1 ≤ ENNReal.ofReal γBar')]
    (hγBar_eq : ENNReal.ofReal γBar = gammaBar) (i : Fin d) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) hpqγ (fun k => DuSeq (ext.φ k) i) (ext.Du i) :=
  t3WeakCertDu_of_banachWeakConv hpqγ hγBar_eq ext.vEps ext.φ
    ext.mLimBanach ext.uLimBanach ext.DuLimBanach ext.hWeakConv
    ext.haeDu_n ext.haeDu i

end InfimalConvolution
end Theorems
end StationaryMFG
