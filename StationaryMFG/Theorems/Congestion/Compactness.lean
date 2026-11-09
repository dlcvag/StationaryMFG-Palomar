module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.SimplePower.Compactness
public import StationaryMFG.Theorems.SimplePower.Banach.WeakLimit
public import StationaryMFG.Theorems.Congestion.AprioriBounds
public import StationaryMFG.Periodic.Separability

@[expose] public section

/-!
# Weak compactness extraction for `(m_ε, u_ε)` — congestion variant

Paper reference: `Source/FGU-monotone_revised.tex`, line 1597, equation
`eq:compactness.congestion`.

## Paper restatement

Under the ε-uniform a priori bound of paper
`thm:apriori-congestion.growth` (line 1571), the sequence
`(m_{ε_k}, u_{ε_k})_k` is bounded in the reflexive product space
`L^{β̄}_per × W^{1,γ̄}_per`. Sequential Banach–Alaoglu /
Eberlein–Smulian then extracts a weakly convergent subsequence
```
(m_{ε_k}, u_{ε_k}) ⇀ (m, u),
```
and the constraint `m ≥ 0 a.e.` is preserved because the cone
`{m ≥ 0 a.e.}` is norm-closed convex, hence weakly closed
(Hahn–Banach), hence sequentially weakly closed.

## Lean implementation strategy

Compared with paper `eq:compactness` (line 1292), the only datum that
changes is the *source* of the uniform a priori bound:
`thm:apriori-simple.power.growth` (line 1206) is replaced by
`thm:apriori-congestion.growth` (line 1571). The compactness step
itself is identical. The abstract pair-extractor
`Theorems.SimplePower.exists_weak_cluster_point_pair` is therefore
verbatim reusable here, exactly as the task spec
(`infra-P5-weak-compactness`) requests:

> Verbatim reuse of `infra:P4-weak-compactness` (and its
> `infra:P4-weak-seq-compact-reflexive` child) — same Banach–Alaoglu
> / closed-cone argument.

## Main results

* `weak_compactness_congestion` — pair-shaped weak cluster-point
  extraction phrased so it can consume the output of
  `Theorems.Congestion.Apriori` directly.

## References

* Paper: `Source/FGU-monotone_revised.tex`, line 1597, equation
  `eq:compactness.congestion`.
* Project dependencies:
  - `StationaryMFG.Theorems.SimplePower.exists_weak_cluster_point_pair`
    (Phase 4 reusable extractor).
  - `StationaryMFG.Periodic.WeakCompactness.weakSeqCompact_of_bounded_reflexive`
    (transitively).
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace Congestion

open MeasureTheory NormedSpace
open Bornology Filter Topology
open scoped ENNReal
open StationaryMFG.Periodic
  (IsReflexiveNormedSpace SobolevPerLp UnitCube
    lpSobolev_product_isReflexive_two)
open StationaryMFG.Theorems.SimplePower
  (exists_weak_cluster_point exists_weak_cluster_point_pair weakProdFst)

variable {Y Z : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Weak compactness extraction (congestion variant).**

Pair-shaped sequential weak compactness for the congestion calibration
of the paper. Given:

* a reflexive product space `Y × Z` with separable strong dual
  (instantiated as `L^{β̄}_per × W^{1,γ̄}_per` in the paper),
* a sequence `z_n = (m_n, u_n) : ℕ → Y × Z` whose range is
  norm-bounded (supplied by `Theorems.Congestion.Apriori`,
  paper `thm:apriori-congestion.growth`),
* a sequentially weakly closed first-coordinate constraint set
  `S₁ ⊆ WeakSpace ℝ Y` containing every `m_n` (in the paper,
  `S₁ = {m ≥ 0 a.e.}`, which is a norm-closed convex cone),

there exist a strictly monotone `φ : ℕ → ℕ` and a weak limit
`z ∈ WeakSpace ℝ (Y × Z)` such that the subsequence
`(m_{ε_{φ k}}, u_{ε_{φ k}})` converges weakly to `z`, and the
first-coordinate projection of `z` lies in `S₁`. This is paper
`eq:compactness.congestion` (line 1597).

The proof is a direct delegation to
`Theorems.SimplePower.exists_weak_cluster_point_pair` — the abstract
pair-extractor is indifferent to whether the bound comes from
`thm:apriori-simple.power.growth` or
`thm:apriori-congestion.growth`. -/
theorem weak_compactness_congestion
    [TopologicalSpace.SeparableSpace (StrongDual ℝ (Y × Z))]
    (hYZ : IsReflexiveNormedSpace (Y × Z))
    (z_n : ℕ → Y × Z) (hb : IsBounded (Set.range z_n))
    {S₁ : Set (WeakSpace ℝ Y)} (hS₁ : IsSeqClosed S₁)
    (hmem₁ : ∀ n, weakProdFst ((toWeakSpace ℝ (Y × Z)) (z_n n)) ∈ S₁) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ (Y × Z)),
      StrictMono φ ∧ weakProdFst z ∈ S₁ ∧
        Tendsto (fun k => (toWeakSpace ℝ (Y × Z)) (z_n (φ k))) atTop (𝓝 z) :=
  exists_weak_cluster_point_pair hYZ z_n hb hS₁ hmem₁

/-! ## Sanity-check example

Targeting the same paper calibration as
`Theorems.SimplePower.Compactness`: `Y = L^2(𝕋^d; ℝ)`,
`Z = W^{1,2}_per(𝕋^d)`. Reflexivity is supplied by
`lpSobolev_product_isReflexive_two`. -/

/-- **Paper compactness target (congestion variant).** A bounded
sequence `(m_n, u_n)` in `L^2_per × W^{1,2}_per`, with first
coordinates trapped in a sequentially weakly closed set, admits a
weakly convergent subsequence whose first-coordinate limit lies in
the constraint set. -/
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
  weak_compactness_congestion
    (lpSobolev_product_isReflexive_two (d := d)) z_n hb hS₁ hmem₁

/-! ## Phase 7 T2 Phase 4 — closed weak-compactness producer

Paper reference: `Source/FGU-monotone_revised.tex`, line 1597,
`eq:compactness.congestion`.

### Phase 4 — three-record decomposition

* `CongestionRegularizedSequenceData` (Phase 3 input) — already in
  `Theorems.Congestion.Apriori`. Carries per-ε bare-function fields.
* `CongestionAprioriBoundData` (Phase 3 output) — already in
  `Theorems.Congestion.Apriori`. Per-ε apriori existential bound.
* `CongestionWeakCompactnessUpstreamPack` — pack of **bridge-deferred**
  Banach-realisation / generic-reflexivity / uniform-in-n items.
* `CongestionWeakLimitData` — Phase 4 output record carrying the
  subsequence, the bare-function weak limits, and their certificates.

The producer `congestionWeakLimit_of_paperHypotheses` takes
`(V, h, seq, pack)` and:

1. Invokes `weak_compactness_congestion` on `pack.vEps` with
   `pack.hBound` and `S₁ := image of nonNegConeLpPer βBar d` under
   `toWeakSpace ℝ _`. Cone membership for each `n` follows from
   `seq.mε_pos (pack.εSeq n)` transported into the Banach realisation
   via `pack.haeM`.
2. Outputs a strictly monotone `φ`, the abstract weak-convergence
   statement `hWeakConvCone` (with cone preservation at the cluster
   point — materially using `seq.mε_pos` and Mazur).
3. Packages the paper-supplied bare limits `mLim, uLim, DuLim` from
   the pack, with `m_nonneg` derived from the pack's named-representative
   cone membership `hMLimBanach_nn` transported via `pack.haeMLim`.
4. **No `bounds` argument** (iter-2 reviewer fix): Phase 4's job is
   weakly-convergent subsequence extraction, which only consumes the
   uniform bound `pack.hBound`. The Phase 3 per-ε apriori `bounds`
   enters analytically in Phase 5 (limit-passage).

### Paper-derivable vs bridge-deferred split

**Paper-derivable in the body, used materially:**

* `seq.mε_pos (pack.εSeq n)` — per-n bare-function non-negativity,
  transported into the Banach realisation via `pack.haeM n` and
  threaded into the cone-membership argument that feeds
  `hWeakConvCone`.
* `weak_compactness_congestion` — applied in the body to extract
  `(φ, z, hmono, hmem, hlim)` from the bounded sequence and the
  cone constraint.
* The output `hWeakConvCone` records the cluster-point cone
  preservation `weakProdFst z ∈ image(nonNegConeLpPer)`, which is
  derived in-body via `nonNegConeLpPer_isSeqClosedW` (Mazur).
* `m_nonneg` is derived from the named-representative cone membership
  `pack.hMLimBanach_nn` transported via `pack.haeMLim`.

**Bridge-deferred (in pack), with paper justification:**

* `εSeq, εSeq_pos`: paper says "pick `ε_k → 0`". The actual choice
  (`εSeq n = 1/(n+1)`, say) is a paper-level *input* — any null
  sequence works for the compactness extraction. Honestly carried
  as a pack field.
* `βBar, γBar`: the paper-pinned exponents in `ℝ≥0∞`. These are
  derivable from `h.α, h.β` via `gammaBar, betaBar`, but carrying
  them as pack fields avoids the `ENNReal.ofReal`-vs-`Fact (1 ≤ ·)`
  bookkeeping inside the producer signature.
* `vEps : ℕ → LpPer βBar d × SobolevPerLp 1 γBar d`: the per-n
  Banach lift of `(m_{εSeq n}, u_{εSeq n}, Du_{εSeq n})`. Requires
  `MemLpPer βBar (m ε)` (not in `seq` — `seq` has `hMbeta_int`),
  plus the bare-to-Lp coercion bookkeeping. Documented Phase 7
  micro-task.
* `hBound : IsBounded (Set.range vEps)`: the **uniform-in-n** norm
  bound. This is exactly the gap Phase 3's review acknowledged.
  The per-ε existential `∃ Cε, ... ≤ Cε` does not directly give a
  uniform-in-n bound without exposing the closed form of
  `apriori_aggregate_bound`. Discharged by the documented
  `infra-P7-sigfix-T2-phase3-uniform-C-promotion` follow-up.
* `hRefl, hSep`: generic-`(βBar, γBar)` reflexivity and dual
  separability — Mathlib + project-level infrastructure for
  arbitrary `1 < p < ∞` requires Clarkson; documented Phase 7
  follow-up. (The `lpSobolev_product_isReflexive_two` covers only
  `p = 2`.)
* `haeM, haeU, haeDu`: per-n a.e.-equality bridges between the
  bare functions `(m, u, Du)` from `seq` and the Banach
  representatives `⇑(vEps n).1, ⇑(vEps n).2.1, ⇑(vEps n).2.2 i`.
  Needed to transport `mε_pos` into cone membership.
* `mLimBanach, uLimBanach, DuLimBanach` (named Banach representatives)
  + `mLim, uLim, DuLim` (chosen periodic representatives) + their
  regularity certificates + `haeMLim, haeULim, haeDuLim` (direct
  non-universal a.e.-equality bridges): the periodic-representative
  selector for `Lp.coeFn` is the residual Path-A obstruction. The
  iter-2 review (this file) rejected the iter-1 universally-quantified
  `haeM_lim : ∀ w, …` pattern as structurally unsatisfiable; the
  current shape (named representatives + direct equalities) is the
  honest replacement.
* `hMLimBanach_nn`: pack pre-commits to a non-negative Banach
  representative for `m`. Body uses this to derive `m_nonneg` via
  `haeMLim`.

This split is precisely the iter-0828/0829 anti-sham discipline
applied to Phase 4: the pack carries ONLY genuinely bridge-deferred
items, and the producer body derives everything else — including
the cone-preservation `m_nonneg` step. -/

variable {d : ℕ}

open StationaryMFG.Hamiltonian
  (HypothesisPowerGrowth betaBar gammaBar
    fact_one_le_ofReal_betaBar fact_one_le_ofReal_gammaBar)
open StationaryMFG.Periodic
  (LpPer MemLpPer MemSobolevPer IsPeriodic HasWeakDerivPer lpNormPer)
open StationaryMFG.Theorems.SimplePower.Banach
  (nonNegConeLpPer nonNegConeLpPer_isSeqClosedW)
open StationaryMFG.Congestion
  (CongestionRegularizedSequenceData CongestionAprioriBoundData)
-- The Euclidean dot-product notation `⬝` (scoped in `StationaryMFG.Hamiltonian`)
-- is needed for the `mfgOperatorPair` transport summand below.
open scoped StationaryMFG.Hamiltonian

/-! ### Hölder-conjugate witnesses for the paper exponents (P3a5)

The two private lemmas below package the conjugate-exponent recipe used
by `compactness_congestionOracle_hRefl` (β-side: `(β+1, (β+1)/β)`; γ-side:
`(γ̄, γ̄/(γ̄-1))`) so the three weak-pairing certificates carried on
`CongestionWeakCompactnessUpstreamPack` / `CongestionWeakLimitData` can
be stated against a single fixed conjugate exponent. -/

/-- β-side Hölder conjugacy at the paper exponents: `(β+1).HolderConjugate
((β+1)/β)`. Inlined from `compactness_congestionOracle_hRefl`. -/
lemma compactness_congestion_hpqβ
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH) :
    Real.HolderConjugate (h.β + 1) ((h.β + 1) / h.β) := by
  have hβ : 0 < h.β := h.hβ
  rw [Real.holderConjugate_iff]
  refine ⟨by linarith, ?_⟩
  have hβ1 : (0 : ℝ) < h.β + 1 := by linarith
  have hβ1ne : h.β + 1 ≠ 0 := ne_of_gt hβ1
  have hβne : h.β ≠ 0 := ne_of_gt hβ
  have hdiv : ((h.β + 1) / h.β)⁻¹ = h.β / (h.β + 1) := by field_simp
  rw [hdiv]; field_simp; ring

/-- γ-side Hölder conjugacy at the paper exponents:
`(gammaBar α β).HolderConjugate (gammaBar α β / (gammaBar α β - 1))`.
Inlined from `compactness_congestionOracle_hRefl`. -/
lemma compactness_congestion_hpqγ
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH) :
    Real.HolderConjugate (gammaBar h.α h.β)
      (gammaBar h.α h.β / (gammaBar h.α h.β - 1)) := by
  have hβ : 0 < h.β := h.hβ
  have hα : 1 < h.α := h.hα
  have h_one_lt_γBarReal : (1 : ℝ) < gammaBar h.α h.β :=
    StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β hα hβ
  have := Real.HolderConjugate.conjExponent
    (p := gammaBar h.α h.β) h_one_lt_γBarReal
  rwa [Real.conjExponent] at this

/-- **Phase 7 upstream pack for T2 Phase 4** (paper line 1597,
`eq:compactness.congestion`).

This pack carries the **bridge-deferred** items the Phase 4 producer
cannot derive from `(seq, bounds)` alone in the current Lean
encoding:

* `βBar, γBar` — the paper-pinned exponents (one-line derivable
  from `h.α, h.β` but carried as pack fields to avoid the
  `ENNReal.ofReal` / `Fact (1 ≤ ·)` bookkeeping at the producer
  signature).
* `εSeq, εSeq_pos` — the ε-discretisation `ε_k → 0`. Paper-level
  input.
* `vEps` — the per-n Banach realisation of
  `(m_{εSeq n}, u_{εSeq n}, Du_{εSeq n})`. Requires `MemLpPer βBar`
  lifting that's not in `seq`. Phase 7 micro-task.
* `hBound` — the **uniform-in-n** norm bound. Phase 3 promotes the
  per-ε existential to uniform-in-n via the documented
  `infra-P7-sigfix-T2-phase3-uniform-C-promotion` follow-up.
* `haeM, haeU, haeDu` — per-n a.e.-equalities bridging `seq` bare
  functions to `vEps` Banach representatives.
* `hRefl, hSep` — generic-exponent reflexivity / dual separability
  (Clarkson — Phase 7 follow-up).
* `mLimBanach, uLimBanach, DuLimBanach` — named Banach representatives
  for the weak limit (reviewer-mandated iter-2 fix replacing the
  iter-1 universally-quantified `haeM_lim/haeU_lim/haeDu_lim` sham).
* `mLim, uLim, DuLim` and their certificates plus `haeMLim, haeULim,
  haeDuLim` — chosen periodic-representative bridges to the named
  Banach representatives (the residual Path-A obstruction;
  see `WeakLimit.lean`).
* `hMLimBanach_nn` — cone membership of the named `mLimBanach`. The
  pack pre-commits to a non-negative Banach representative for `m`. -/
structure CongestionWeakCompactnessUpstreamPack
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ) where
  /-- Paper exponent `β̄` as an extended real. -/
  βBar : ℝ≥0∞
  /-- Paper exponent `γ̄` as an extended real. -/
  γBar : ℝ≥0∞
  /-- `1 ≤ β̄` (Mathlib `Lp` infrastructure requirement). -/
  hβFact : Fact (1 ≤ βBar)
  /-- `1 ≤ γ̄` (Mathlib `Lp` infrastructure requirement). -/
  hγFact : Fact (1 ≤ γBar)
  /-- The ε-discretisation `ε_k`. -/
  εSeq : ℕ → ℝ
  /-- Each `ε_k > 0`. -/
  εSeq_pos : ∀ n, 0 < εSeq n
  /-- The per-n Banach realisation of `(m_{εSeq n}, u_{εSeq n},
  Du_{εSeq n})` in the reflexive product
  `LpPer βBar d × SobolevPerLp 1 γBar d`. -/
  vEps : ℕ → LpPer βBar d × SobolevPerLp 1 γBar d
  /-- Uniform-in-n norm bound on the Banach sequence. Discharged from the
  uniform-in-ε apriori constant `CongestionAprioriBoundData.C` via
  `congestionWeakCompactness_hBound_of_aprioriBounds` (no longer a deferred
  oracle once that producer is composed). -/
  hBound : IsBounded (Set.range vEps)
  /-- Reflexivity of the product Banach space. -/
  hRefl : IsReflexiveNormedSpace (LpPer βBar d × SobolevPerLp 1 γBar d)
  /-- Strong-dual separability of the product (required by
  `weak_compactness_congestion`). -/
  hSep : TopologicalSpace.SeparableSpace
    (StrongDual ℝ (LpPer βBar d × SobolevPerLp 1 γBar d))
  /-- Per-n a.e.-equality between the bare-function `m_{εSeq n}` and
  the Banach representative `⇑(vEps n).1`. Used to transport
  `seq.mε_pos` into cone membership. -/
  haeM : ∀ n,
    seq.m (εSeq n)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps n).1 : (Fin d → ℝ) → ℝ)
  /-- Per-n a.e.-equality between the bare-function `u_{εSeq n}` and
  the Banach representative `⇑(vEps n).2.1`. -/
  haeU : ∀ n,
    seq.u (εSeq n)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps n).2.1 : (Fin d → ℝ) → ℝ)
  /-- Per-n, per-axis a.e.-equality between the bare-function
  derivative `Du_{εSeq n} i` and the Banach representative
  `⇑((vEps n).2.2 i)`. -/
  haeDu : ∀ n i,
    seq.Du (εSeq n) i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑((vEps n).2.2 i) : (Fin d → ℝ) → ℝ)
  /-- **Named Banach representative for the `m`-limit** (replaces the
  iter-1 universally-quantified `haeM_lim` sham per reviewer Option B).
  This is a concrete `Lp` element supplied by the pack; the producer
  body uses the direct a.e.-equality `haeMLim` below to transport
  pack-supplied properties of `mLimBanach` (notably the cone membership
  `hMLimBanach_nn`) to the chosen bare-function `mLim`. -/
  mLimBanach : LpPer βBar d
  /-- **Named Banach representative for the `u`-limit.** -/
  uLimBanach : MeasureTheory.Lp ℝ γBar
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- **Named Banach representatives for the weak-derivative family.** -/
  DuLimBanach : Fin d → MeasureTheory.Lp ℝ γBar
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Chosen bare-function `m`-limit (paper-supplied, residual Path-A
  obstruction; a periodic representative of `mLimBanach`). -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen bare-function `u`-limit (periodic representative of
  `uLimBanach`). -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen bare-function weak-derivative family (periodic
  representatives of `DuLimBanach i`). -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- Periodicity of `mLim`. -/
  hMlimPer : IsPeriodic mLim
  /-- Periodicity of `uLim`. -/
  hUlimPer : IsPeriodic uLim
  /-- Periodicity of each `DuLim i`. The concrete pack4 producer picks
  `DuLim i := (bareCoeFnOfLpPer (DuLimBanach i)).rep`, a genuinely periodic
  representative (`.rep.periodic`), so this is honestly fillable. Needed by
  the abstract-VI weak-is-strong entry point
  (`weak_is_strong_HJB_le_of_abstractPeriodicVI_aesm`) to certify the
  truncated `muAux` test pair is periodic-admissible. -/
  hDuLimPer : ∀ i, IsPeriodic (DuLim i)
  /-- `mLim ∈ L^{β̄}_per`. -/
  hMlim_memLp : MemLpPer βBar mLim
  /-- `uLim ∈ W^{1,γ̄}_per`. -/
  hUlim_sob : MemSobolevPer γBar uLim
  /-- Weak-derivative relation between the chosen `uLim` and `DuLim`. -/
  hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i)
  /-- **Periodic-representative bridge for `mLimBanach`**: the chosen
  periodic representative `mLim` is a.e.-equal to the coercion of the
  named Banach element. This is the residual Path-A obstruction (a
  *single* a.e.-equality, not the iter-1 universal-`w` sham). A
  trivial supplier can pick `mLim := ⇑mLimBanach` for which the
  a.e.-equality is `EventuallyEq.refl`. -/
  haeMLim :
    mLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- Periodic-representative bridge for `uLimBanach`. -/
  haeULim :
    uLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑uLimBanach : (Fin d → ℝ) → ℝ)
  /-- Periodic-representative bridge for each `DuLimBanach i`. -/
  haeDuLim : ∀ i,
    DuLim i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ)
  /-- **Cone-membership of the named representative.** The pack
  pre-commits to a non-negative Banach representative for the
  bare-function `m`-limit. This is honestly satisfiable (a supplier
  picks `mLimBanach := 0` or any non-negative element). The body uses
  this together with `haeMLim` to derive the output `m_nonneg`. -/
  hMLimBanach_nn :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- **(P3a5) The concrete extracted subsequence index** matching the
  one used to build the three weak-pairing certs below and the abstract
  cone-cluster `hWeakConvConeSub`. Pinned to the underlying `blim.φ` in
  the producer (NOT a fresh `Classical.choose`), so the downstream
  `lim.φ` coincides with the cert subsequence. -/
  subseqφ : ℕ → ℕ
  /-- Strict monotonicity of `subseqφ`. -/
  hSubseqMono : StrictMono subseqφ
  /-- **(P3a5) Concrete `m`-component weak-pairing cert** for the
  extracted subsequence `subseqφ` against the chosen bare limit `mLim`,
  at the paper exponents. Built from `blim`'s combined `hWeakConv` via
  `congestionWeakCertM_of_banachLimit` inside the producer. -/
  weakCertM :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqβ h)
      (fun k => seq.m (1 / ((subseqφ k : ℝ) + 1))) mLim
  /-- **(P3a5) Concrete `u`-component weak-pairing cert.** -/
  weakCertU :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqγ h)
      (fun k => seq.u (1 / ((subseqφ k : ℝ) + 1))) uLim
  /-- **(P3a5) Concrete gradient-family weak-pairing certs.** -/
  weakCertDu : ∀ i,
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqγ h)
      (fun k => seq.Du (1 / ((subseqφ k : ℝ) + 1)) i) (DuLim i)
  /-- **(P3a5) Abstract cone-cluster weak convergence over `subseqφ`.**
  Carries the `hWeakConvCone`-shaped existential keyed to the SAME
  subsequence `subseqφ`, built from `blim.hWeakConv` + `blim.hMLimBanach_nn`
  in the producer. Forwarded directly into the output record so that
  `CongestionWeakLimitData.φ = subseqφ` stays consistent with
  `hWeakConvCone`. -/
  hWeakConvConeSub :
    ∃ z : WeakSpace ℝ (LpPer βBar d × SobolevPerLp 1 γBar d),
      weakProdFst z ∈ (toWeakSpace ℝ (LpPer βBar d)) ''
          StationaryMFG.Theorems.SimplePower.Banach.nonNegConeLpPer βBar d
        ∧ Tendsto (fun k => (toWeakSpace ℝ
            (LpPer βBar d × SobolevPerLp 1 γBar d))
            (vEps (subseqφ k))) atTop (𝓝 z)

/-- **Phase 7 output record for T2 Phase 4** (paper line 1597,
`eq:compactness.congestion`).

Records the outcome of the weak-compactness extraction: a strictly
monotone subsequence `φ`, the chosen bare-function limits
`(mLim, uLim, DuLim)`, their `Lp` / `Sobolev` regularity, periodicity,
weak-derivative relation, the non-negativity `0 ≤ mLim` a.e., and the
abstract weak-convergence statement on the underlying Banach pair
sequence `vEps`.

The `pack` parameter is held in the structure header to keep the
fields self-contained — every certificate refers back to `pack`'s
exponents and Banach realisations. -/
structure CongestionWeakLimitData
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    [Fact (1 ≤ pack.βBar)] [Fact (1 ≤ pack.γBar)] where
  /-- Strictly monotone subsequence index. -/
  φ : ℕ → ℕ
  /-- The subsequence index is strictly increasing. -/
  hMono : StrictMono φ
  /-- Bare-function `m`-limit (paper line 1597 `m`). -/
  m : (Fin d → ℝ) → ℝ
  /-- Bare-function `u`-limit (paper line 1597 `u`). -/
  u : (Fin d → ℝ) → ℝ
  /-- Bare-function weak-derivative family for `u`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `0 ≤ m` a.e. (paper cone-preservation step, derived in-body via
  `nonNegConeLpPer_isSeqClosedW` + `pack.haeM` + `seq.mε_pos`). -/
  m_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] m
  /-- `m ∈ L^{β̄}_per` (paper line 1597 `m ∈ L^{β̄}`). -/
  mLp : MemLpPer pack.βBar m
  /-- `u ∈ W^{1,γ̄}_per` (paper line 1597 `u ∈ W^{1,γ̄}`). -/
  uSob : MemSobolevPer pack.γBar u
  /-- Periodicity of `m`. -/
  hMper : IsPeriodic m
  /-- Periodicity of `u`. -/
  hUper : IsPeriodic u
  /-- Periodicity of each `Du i`. Forwarded from `pack.hDuLimPer`. Needed by
  the abstract-VI weak-is-strong entry point to certify the truncated `muAux`
  test pair is periodic-admissible. -/
  hDuPer : ∀ i, IsPeriodic (Du i)
  /-- Weak-derivative relation between `u` and `Du`. -/
  hDuWeak : ∀ i, HasWeakDerivPer i u (Du i)
  /-- **Abstract weak convergence with cone preservation.** The Banach
  pair sequence along the extracted subsequence converges weakly to a
  cluster point `z` whose first projection is in the (image of the)
  non-negativity cone `nonNegConeLpPer pack.βBar d`. This single
  output field materially exercises both `seq.mε_pos` (per-n cone
  membership) and `weak_compactness_congestion` (extraction +
  sequential closedness via Mazur). -/
  hWeakConvCone : ∃ z : WeakSpace ℝ (LpPer pack.βBar d ×
                    SobolevPerLp 1 pack.γBar d),
    weakProdFst z ∈ (toWeakSpace ℝ (LpPer pack.βBar d)) ''
        StationaryMFG.Theorems.SimplePower.Banach.nonNegConeLpPer
          pack.βBar d
      ∧ Tendsto (fun k => (toWeakSpace ℝ
          (LpPer pack.βBar d × SobolevPerLp 1 pack.γBar d))
          (pack.vEps (φ k))) atTop (𝓝 z)
  /-- **(P3a5) `m`-component weak-pairing cert** for the SAME extracted
  subsequence `φ` against the bare limit `m`, at the paper exponents.
  Forwarded from `pack.weakCertM` (which is against `pack.mLim = m` and
  `pack.subseqφ = φ`). This is the field P3a6 feeds to
  `congestionPairConv_combine` to remove `pack5_pairConvOracle`. -/
  weakCertM :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqβ h)
      (fun k => seq.m (1 / ((φ k : ℝ) + 1))) m
  /-- **(P3a5) `u`-component weak-pairing cert.** -/
  weakCertU :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqγ h)
      (fun k => seq.u (1 / ((φ k : ℝ) + 1))) u
  /-- **(P3a5) gradient-family weak-pairing certs.** -/
  weakCertDu : ∀ i,
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqγ h)
      (fun k => seq.Du (1 / ((φ k : ℝ) + 1)) i) (Du i)
  /-- **(P3a7b) gradient-family `L^{γ̄}_per` membership** of the limit
  weak-derivative family `Du`. Forwarded in the producer from the named
  Banach representatives `pack.DuLimBanach i ∈ Lp ℝ γBar` across the
  periodic-representative bridge `pack.haeDuLim`. This is the limit
  counterpart of `CongestionLimitVITestPair.hDυ_memGamma`; it is the
  `hDu_lim_memGamma` certificate consumed by
  `congestionPairConv_of_weakLimit` when sourcing `hpair_conv` internally
  (drains `pack5_pairConvOracle`). -/
  hDu_memGamma : ∀ i, MemLpPer pack.γBar (Du i)

/-- **Phase 7 producer for T2 Phase 4** (paper line 1597,
`eq:compactness.congestion`).

Given the Phase 3 regularised-sequence input `seq` and the Phase 4
upstream pack carrying the Banach-realisation / uniform-in-n /
generic-reflexivity / periodic-representative items, produce a
`CongestionWeakLimitData` recording the subsequence, the bare-function
limits, the cone-preservation `0 ≤ m` a.e., and an abstract
weak-convergence-with-cone statement.

**Note on `bounds`.** The producer no longer takes a
`CongestionAprioriBoundData` argument. Phase 4's job is to extract a
weakly-convergent subsequence FROM a uniform bound; the uniform bound
itself (`pack.hBound`) is the Banach-bridge-deferred content. The
Phase 3 per-ε existential `bounds` will enter analytically in
**Phase 5 (limit-passage)** — see the iter-2 reviewer note rejecting
the iter-1 `bounds`-as-pass-through pattern. Phase 5 will introduce
`bounds` directly as a consumer.

**Paper-derivable in the body** (uses `seq` and pack fields
materially):

1. Pull reflexivity and separability via `pack.hRefl, pack.hSep`.
2. **Cone-membership of each `vEps n`.** Combine
   `seq.mε_pos (pack.εSeq n)` (per-n bare-function non-negativity)
   with `pack.haeM n` (a.e.-equality bridge) to deduce
   `0 ≤ ⇑(vEps n).1` a.e., i.e. `(vEps n).1 ∈ nonNegConeLpPer βBar d`.
3. Invoke `weak_compactness_congestion` on `pack.vEps`, `pack.hBound`,
   with `S₁ := image of nonNegConeLpPer` under `toWeakSpace`, sealed
   sequentially-closed by `nonNegConeLpPer_isSeqClosedW`. Out comes
   `(φ, z, hMono, hzS, hzLim)`. This is the output's `hWeakConvCone`.
4. **Transport `0 ≤ ⇑pack.mLimBanach` to `0 ≤ pack.mLim` a.e.** via
   `pack.haeMLim`. The cone membership at the named Banach
   representative `mLimBanach` is supplied directly by
   `pack.hMLimBanach_nn` — this avoids the iter-1 universal-`w` sham,
   per reviewer Option B (named representative + body-side
   identification).
5. Assemble all the certificates.

**Bridge-deferred** (from pack — see structure docstring for full
list and paper justification): Banach lifting (`vEps`), uniform-in-n
bound (`hBound`), generic-exponent reflexivity / separability, and
the periodic-representative bridges `haeMLim/haeULim/haeDuLim` keyed
to the named Banach representatives `mLimBanach/uLimBanach/DuLimBanach`. -/
noncomputable def congestionWeakLimit_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq) :
    haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
    haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
    CongestionWeakLimitData V H DpH J h seq pack := by
  -- Pull Banach infrastructure into local context.
  haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
  haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
  haveI : TopologicalSpace.SeparableSpace
            (StrongDual ℝ (LpPer pack.βBar d ×
              SobolevPerLp 1 pack.γBar d)) := pack.hSep
  -- **Transport `0 ≤ ⇑pack.mLimBanach` to `0 ≤ pack.mLim` a.e.** via
  -- the periodic-representative bridge `pack.haeMLim`.
  -- (Reviewer Option B: named Banach representative + direct
  -- non-universal a.e.-equality. The pack-supplied cone membership
  -- `pack.hMLimBanach_nn` is what underlies the output.)
  have hMlim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict
                          MeasureTheory.volume (UnitCube d)] pack.mLim := by
    filter_upwards [pack.hMLimBanach_nn, pack.haeMLim] with x hxnn hxeq
    -- `hxeq : pack.mLim x = ⇑pack.mLimBanach x`, `hxnn : 0 ≤ ⇑mLimBanach x`.
    exact hxeq.symm ▸ hxnn
  -- **(P3a5) Assemble the output, pinning the subsequence `φ` to the
  -- pack's concrete `subseqφ`** (NOT a fresh `Classical.choose`). The
  -- abstract weak-convergence-with-cone field `hWeakConvCone` is taken
  -- from `pack.hWeakConvConeSub` (keyed to the SAME `subseqφ`, built in
  -- the pack4 producer from the concrete Banach weak limit `blim`,
  -- which itself runs `weak_compactness_congestion` + Mazur). The three
  -- new weak-pairing certs are forwarded from the pack; because
  -- `pack.subseqφ = φ` and `pack.mLim/uLim/DuLim = m/u/Du`, they have
  -- exactly the per-`T` shape `pack5_pairConvOracle` consumes (P3a6).
  refine
    { φ := pack.subseqφ
      hMono := pack.hSubseqMono
      m := pack.mLim
      u := pack.uLim
      Du := pack.DuLim
      m_nonneg := hMlim_nn
      mLp := pack.hMlim_memLp
      uSob := pack.hUlim_sob
      hMper := pack.hMlimPer
      hUper := pack.hUlimPer
      hDuPer := pack.hDuLimPer
      hDuWeak := pack.hDuLimWeak
      hWeakConvCone := pack.hWeakConvConeSub
      weakCertM := pack.weakCertM
      weakCertU := pack.weakCertU
      weakCertDu := pack.weakCertDu
      -- (P3a7b) `MemLpPer γ̄ (DuLim i)` from the Banach `Lp` membership of
      -- `pack.DuLimBanach i` across the periodic-representative bridge
      -- `pack.haeDuLim i`. Same derivation as `hDuLim_memLpγ` inside the
      -- pack4 Banach-realisation oracle producer.
      hDu_memGamma := fun i =>
        MeasureTheory.MemLp.ae_eq (pack.haeDuLim i).symm
          (MeasureTheory.Lp.memLp (pack.DuLimBanach i)) }

/-! ### Sanity-check `example` for the Phase 7 T2 Phase 4 producer

A pure type-check that the iter-2 producer signature is
`(V, h, seq, pack)` — `bounds` no longer appears (per reviewer
Option A: Phase 5 will introduce `bounds` directly as a consumer). -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq) :
    haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
    haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
    CongestionWeakLimitData V H DpH J h seq pack :=
  congestionWeakLimit_of_paperHypotheses V h seq pack

/-! ## Phase 7 T2 sub-task A3 — `pack4` Banach-realisation oracle

The pack4 producer `congestionWeakCompactnessUpstreamPack_of_paperHypotheses`
below derives the paper-derivable scaffolding fields of
`CongestionWeakCompactnessUpstreamPack` (`βBar, γBar, hβFact, hγFact,
εSeq, εSeq_pos`) from `(pack3.hPower)` and forwards the genuine
Banach-realisation Mathlib-gap fields (`vEps, hBound, hRefl, hSep, haeM,
haeU, haeDu, mLimBanach, uLimBanach, DuLimBanach, mLim, uLim, DuLim,
hMlimPer, hUlimPer, hMlim_memLp, hUlim_sob, hDuLimWeak, haeMLim, haeULim,
haeDuLim, hMLimBanach_nn`) from a single oracle bundle
`CongestionPack4BanachRealisationOracle`.

This oracle is the **honestly named** residue of the Phase 4 Banach
realisation step. The user audit (2026-05-24, recorded in the task
file's "CRITICAL discipline" section) requires that the oracle remain a
visible, named parameter of the downstream Phase 7 top-pack producer
and of the public H5 producer — it must NOT be absorbed into a generic
`topPack` field. The exponents `(βBar, γBar)` are pinned to the
paper-canonical values `ENNReal.ofReal (h.β + 1)` and
`ENNReal.ofReal (gammaBar h.α h.β)` so the oracle aligns with the
A1 (`pack3`) and A2 (`seq`) producers.

Per-field paper-derivable vs bridge-deferred audit:

* `βBar, γBar, hβFact, hγFact, εSeq, εSeq_pos` — **paper-derivable**.
  Derived in-body from `h.α, h.β` and a trivial null sequence
  `εSeq n := 1/(n+1)`.
* `vEps, hRefl, hSep, hBound, haeM, haeU, haeDu` — **genuine Mathlib
  gap** (Path-A `toLp` injection from bare to equivalence-class `Lp`,
  generic-exponent reflexivity / dual separability, uniform-in-n
  bookkeeping). Honestly deferred via the oracle.
* `mLimBanach, uLimBanach, DuLimBanach, mLim, uLim, DuLim, hMlimPer,
  hUlimPer, hMlim_memLp, hUlim_sob, hDuLimWeak, haeMLim, haeULim,
  haeDuLim, hMLimBanach_nn` — **genuine Mathlib gap** (residual Path-A
  periodic-representative selection for the limit; documented in
  `WeakLimit.lean`). Honestly deferred via the oracle.
-/

/-- **Banach-realisation oracle for pack4** (T2 Phase 7 sub-task A3).

Carries the genuine Banach-realisation Mathlib gaps that the pack4
producer `congestionWeakCompactnessUpstreamPack_of_paperHypotheses`
cannot derive from `(pack3.hPower, seq)`. The exponents are pinned to
the paper-canonical values `(ENNReal.ofReal (h.β + 1),
ENNReal.ofReal (gammaBar h.α h.β))` so they align with the A1/A2
producer output. -/
structure CongestionPack4BanachRealisationOracle
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (εSeq : ℕ → ℝ) (εSeq_pos : ∀ n, 0 < εSeq n)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] where
  /-- Per-n Banach realisation of `(m_{εSeq n}, u_{εSeq n},
  Du_{εSeq n})` in the reflexive product space at the paper exponents. -/
  vEps : ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
                × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d
  /-- Per-n a.e.-equality bridges `seq.m (εSeq n) ≈ ⇑(vEps n).1`. -/
  haeM : ∀ n,
    seq.m (εSeq n)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps n).1 : (Fin d → ℝ) → ℝ)
  /-- Per-n a.e.-equality bridges `seq.u (εSeq n) ≈ ⇑(vEps n).2.1`. -/
  haeU : ∀ n,
    seq.u (εSeq n)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(vEps n).2.1 : (Fin d → ℝ) → ℝ)
  /-- Per-n, per-axis a.e.-equality bridges `seq.Du (εSeq n) i ≈
  ⇑((vEps n).2.2 i)`. -/
  haeDu : ∀ n i,
    seq.Du (εSeq n) i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑((vEps n).2.2 i) : (Fin d → ℝ) → ℝ)
  /-- Named Banach representative for the `m`-limit. -/
  mLimBanach : LpPer (ENNReal.ofReal (h.β + 1)) d
  /-- Named Banach representative for the `u`-limit. -/
  uLimBanach : MeasureTheory.Lp ℝ (ENNReal.ofReal (gammaBar h.α h.β))
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Named Banach representatives for the weak-derivative family. -/
  DuLimBanach : Fin d → MeasureTheory.Lp ℝ
    (ENNReal.ofReal (gammaBar h.α h.β))
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Chosen periodic representative for the `m`-limit. -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic representative for the `u`-limit. -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic representatives for the weak-derivative family. -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- Periodicity of `mLim`. -/
  hMlimPer : IsPeriodic mLim
  /-- Periodicity of `uLim`. -/
  hUlimPer : IsPeriodic uLim
  /-- Periodicity of each `DuLim i` (the `.rep` representative is periodic). -/
  hDuLimPer : ∀ i, IsPeriodic (DuLim i)
  /-- `mLim ∈ L^{β̄}_per`. -/
  hMlim_memLp : MemLpPer (ENNReal.ofReal (h.β + 1)) mLim
  /-- `uLim ∈ W^{1,γ̄}_per`. -/
  hUlim_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) uLim
  /-- Weak-derivative relation between `uLim` and `DuLim`. -/
  hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i)
  /-- Periodic-representative bridge for `mLimBanach`. -/
  haeMLim :
    mLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- Periodic-representative bridge for `uLimBanach`. -/
  haeULim :
    uLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑uLimBanach : (Fin d → ℝ) → ℝ)
  /-- Periodic-representative bridges for each `DuLimBanach i`. -/
  haeDuLim : ∀ i,
    DuLim i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ)
  /-- Cone-membership of the named Banach `m`-limit representative. -/
  hMLimBanach_nn :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- **(P3a5) Concrete extracted subsequence index.** Pinned to the
  underlying Banach weak-limit's `blim.φ` in the producer. -/
  subseqφ : ℕ → ℕ
  /-- Strict monotonicity of `subseqφ`. -/
  hSubseqMono : StrictMono subseqφ
  /-- **(P3a5) `m`-component weak-pairing cert** against `mLim` and the
  running data along `subseqφ`. -/
  weakCertM :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqβ h)
      (fun k => seq.m (1 / ((subseqφ k : ℝ) + 1))) mLim
  /-- **(P3a5) `u`-component weak-pairing cert.** -/
  weakCertU :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqγ h)
      (fun k => seq.u (1 / ((subseqφ k : ℝ) + 1))) uLim
  /-- **(P3a5) gradient-family weak-pairing certs.** -/
  weakCertDu : ∀ i,
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
      (d := d) (compactness_congestion_hpqγ h)
      (fun k => seq.Du (1 / ((subseqφ k : ℝ) + 1)) i) (DuLim i)
  /-- **(P3a5) Abstract cone-cluster weak convergence over `subseqφ`.** -/
  hWeakConvConeSub :
    ∃ z : WeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d),
      weakProdFst z ∈ (toWeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d)) ''
          StationaryMFG.Theorems.SimplePower.Banach.nonNegConeLpPer
            (ENNReal.ofReal (h.β + 1)) d
        ∧ Tendsto (fun k => (toWeakSpace ℝ
            (LpPer (ENNReal.ofReal (h.β + 1)) d
              × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
            (vEps (subseqφ k))) atTop (𝓝 z)

/-! ## Step 1 — Banach realisation of the per-`n` sequence `vEps`

The four oracle fields `vEps`, `haeM`, `haeU`, `haeDu` are **genuinely
paper-derivable** from the regularised-sequence data `seq` alone (they
do not need any Banach–Alaoglu / weak-limit input). The lemma below
discharges them.

For each `n`, write `ε_n := 1/(n+1) > 0` and use:

* `seq.hm_lp ε_n` : `MemLpPer (ofReal (β+1)) (m ε_n)` → `MemLpPer.toLp`
  gives the `LpPer (β+1) d` first component, ae-equal to `m ε_n`
  (`MemLp.coeFn_toLp`).
* `seq.hu_sob ε_n` : `MemSobolevPer (ofReal γ̄) (u ε_n)` together with
  `seq.hDu_lp ε_n · i` : `MemLpPer (ofReal γ̄) (Du ε_n i)` →
  `MemSobolevPer.toLpSobolev` gives the `SobolevPerLp 1 γ̄ d` second
  component. Its first sub-component is `(hu_sob).1.toLp`, ae-equal to
  `u ε_n`; its `i`-th derivative sub-component is `(hDu_lp i).toLp`,
  ae-equal to `Du ε_n i`.

This is the standard bare-to-quotient `toLp` injection (CONVENTIONS §1b
bridge); no analysis beyond the membership certificates already carried
by `seq`. -/

/-- **Step 1 producer (derivable).** The per-`n` Banach realisation of
`(m_{ε_n}, u_{ε_n}, Du_{ε_n})` at the paper exponents, together with the
three a.e.-equality bridges to the bare functions. The εSeq is pinned to
`1/(n+1)`, matching `CongestionPack4BanachRealisationOracle`. -/
noncomputable def congestionBanachRealisation_vEps_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (n : ℕ) :
    LpPer (ENNReal.ofReal (h.β + 1)) d
      × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  ((seq.hm_lp _ hε).toLp,
    (seq.hu_sob _ hε).toLpSobolev (fun i => seq.hDu_lp _ hε i))

/-- The `m`-component of `congestionBanachRealisation_vEps_of_paperHypotheses`
is a.e.-equal to the bare density `seq.m (1/(n+1))`. -/
lemma congestionBanachRealisation_haeM_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (n : ℕ) :
    seq.m (1 / ((n : ℝ) + 1))
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(congestionBanachRealisation_vEps_of_paperHypotheses h seq n).1
          : (Fin d → ℝ) → ℝ) := by
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact (MeasureTheory.MemLp.coeFn_toLp (seq.hm_lp _ hε)).symm

/-- The `u`-component of `congestionBanachRealisation_vEps_of_paperHypotheses`
is a.e.-equal to the bare value function `seq.u (1/(n+1))`. -/
lemma congestionBanachRealisation_haeU_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (n : ℕ) :
    seq.u (1 / ((n : ℝ) + 1))
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(congestionBanachRealisation_vEps_of_paperHypotheses h seq n).2.1
          : (Fin d → ℝ) → ℝ) := by
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact (MeasureTheory.MemLp.coeFn_toLp (seq.hu_sob _ hε).1).symm

/-- The `i`-th weak-derivative component of
`congestionBanachRealisation_vEps_of_paperHypotheses` is a.e.-equal to the
bare derivative `seq.Du (1/(n+1)) i`. -/
lemma congestionBanachRealisation_haeDu_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (n : ℕ) (i : Fin d) :
    seq.Du (1 / ((n : ℝ) + 1)) i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑((congestionBanachRealisation_vEps_of_paperHypotheses h seq n).2.2 i)
          : (Fin d → ℝ) → ℝ) := by
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact (MeasureTheory.MemLp.coeFn_toLp (seq.hDu_lp _ hε i)).symm

/-! ## Discharging `hBound` from the uniform a priori constant

The pack field `CongestionWeakCompactnessUpstreamPack.hBound`
(line 319) — the uniform-in-`n` norm bound on the Banach realisation
sequence `vEps` — was historically carried as a bridge-deferred
oracle field (see `CongestionPack4BanachRealisationOracle.hBound`,
line 696). Iter-0876 promoted the T2 a priori bound to a single
uniform-in-`ε` constant `C` (`CongestionAprioriBoundData`, paper line
1581, `rmk:onC`). The lemma below genuinely discharges `hBound` from
that constant, chaining `bounds.bound (εSeq n) (εSeq_pos n)` through
the per-`n` a.e.-equality bridges `haeM`/`haeU`/`haeDu` already in the
pack/oracle.

The exponents of the Banach realisations are pinned to the paper
values `(ENNReal.ofReal (h.β + 1), ENNReal.ofReal (gammaBar h.α h.β))`
— exactly the exponents in which `bounds.bound` is stated
(`betaBar h.β = h.β + 1`, `gammaBar h.α h.β`). No exponent-equation
rider is needed; the alignment is definitional. -/

/-- **Banach `Lp`-norm from an integrated `p`-th-power bound on an
a.e.-equal bare function.** For a raw Mathlib `Lp` element `g : Lp ℝ p μ`
with finite exponent (`p ≠ 0`, `p ≠ ∞`) and a bound
`∫ x, ‖g x‖^{p.toReal} ∂μ ≤ C` (with `0 ≤ C`), the Banach norm satisfies
`‖g‖ ≤ C^{p.toReal⁻¹}`.

This is the raw-`Lp` analogue of `Periodic.lpNormPer_le_of_apriori`
(which works on bare `MemLpPer` functions). It is the load-bearing
transport for the `hBound` discharge: the clients supply the bare
integral bound (via the a.e.-equality bridges) and read back a uniform
Banach-norm bound. -/
lemma norm_lp_le_of_integral_rpow_le
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    {μ : MeasureTheory.Measure (Fin d → ℝ)}
    (g : MeasureTheory.Lp ℝ p μ) {C : ℝ} (_hC : 0 ≤ C)
    (hint : (∫ x, ‖(g : (Fin d → ℝ) → ℝ) x‖ ^ p.toReal ∂μ) ≤ C) :
    ‖g‖ ≤ C ^ (p.toReal⁻¹) := by
  have hg_aesm : MeasureTheory.AEStronglyMeasurable
      (g : (Fin d → ℝ) → ℝ) μ := (MeasureTheory.Lp.aestronglyMeasurable g)
  -- `‖g‖ = lpNorm (⇑g) p μ`.
  have h_norm_eq : ‖g‖ = MeasureTheory.lpNorm (g : (Fin d → ℝ) → ℝ) p μ := by
    rw [MeasureTheory.Lp.norm_def]
    exact MeasureTheory.toReal_eLpNorm
  -- `lpNorm (⇑g) p μ = (∫ ‖g‖^{p.toReal})^{p.toReal⁻¹}`.
  have h_lpnorm :
      MeasureTheory.lpNorm (g : (Fin d → ℝ) → ℝ) p μ
        = (∫ x, ‖(g : (Fin d → ℝ) → ℝ) x‖ ^ p.toReal ∂μ) ^ (p.toReal⁻¹) :=
    MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hp0 hp_top hg_aesm
  -- The integrand is pointwise nonnegative, so the integral is too.
  have h_int_nonneg :
      0 ≤ ∫ x, ‖(g : (Fin d → ℝ) → ℝ) x‖ ^ p.toReal ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [h_norm_eq, h_lpnorm]
  exact Real.rpow_le_rpow h_int_nonneg hint (by positivity)

/-- **Discharge of `CongestionWeakCompactnessUpstreamPack.hBound` from
the uniform a priori constant.** (Paper line 1597,
`eq:compactness.congestion`: the sequential Banach–Alaoglu extraction
requires the realisation sequence `vEps` to be norm-bounded; this lemma
supplies that bound from the uniform-in-`ε` apriori constant `bounds.C`,
paper line 1581.)

Given the iter-0876 uniform apriori bound `bounds`
(`CongestionAprioriBoundData`), the Banach realisation sequence `vEps`,
the null sequence `(εSeq, εSeq_pos)`, the per-`n` positivity of
`seq.m (εSeq n)`, and the per-`n` a.e.-equality bridges
`haeM`/`haeU`/`haeDu` (all already carried by the pack/oracle), the
range of `vEps` is bounded.

The chain is: `bounds.bound (εSeq n) (εSeq_pos n)` gives a sum of three
nonnegative summands `≤ bounds.C`; dropping the other two leaves each
summand `≤ bounds.C`; the a.e.-equality bridges transport each summand
to an integrated `p`-th-power bound on the corresponding `vEps`
component; `norm_lp_le_of_integral_rpow_le` reads back a uniform Banach
norm bound; `Prod.norm_def` and the `Fin d` pi-norm combine these. -/
lemma congestionWeakCompactness_hBound_of_aprioriBounds
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    {h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH}
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (εSeq : ℕ → ℝ) (εSeq_pos : ∀ n, 0 < εSeq n)
    (vEps : ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
              × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)
    (haeM : ∀ n,
      seq.m (εSeq n)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps n).1 : (Fin d → ℝ) → ℝ))
    (haeU : ∀ n,
      seq.u (εSeq n)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps n).2.1 : (Fin d → ℝ) → ℝ))
    (haeDu : ∀ n i,
      seq.Du (εSeq n) i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((vEps n).2.2 i) : (Fin d → ℝ) → ℝ)) :
    IsBounded (Set.range vEps) := by
  -- Cube-restricted measure (matches the `Lp` types of `vEps`).
  let μ : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)
  -- Exponent bookkeeping.
  have hβ_eq : betaBar h.β = h.β + 1 := rfl
  have hβ_pos : 0 < betaBar h.β := by
    have : 0 < h.β := h.hβ; rw [hβ_eq]; linarith
  have hγ_pos : 0 < gammaBar h.α h.β := by
    have hγfact : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β) :=
      (inferInstance : Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))).out
    by_contra hle
    rw [not_lt] at hle
    have hz : ENNReal.ofReal (gammaBar h.α h.β) = 0 :=
      ENNReal.ofReal_eq_zero.mpr hle
    rw [hz] at hγfact
    exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hγfact
  have hβzero : ENNReal.ofReal (h.β + 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by rw [← hβ_eq]; exact hβ_pos)).ne'
  have hβtop : ENNReal.ofReal (h.β + 1) ≠ ∞ := ENNReal.ofReal_ne_top
  have hβtoReal : (ENNReal.ofReal (h.β + 1)).toReal = betaBar h.β := by
    rw [hβ_eq]; exact ENNReal.toReal_ofReal (by rw [← hβ_eq]; exact hβ_pos.le)
  have hγzero : ENNReal.ofReal (gammaBar h.α h.β) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hγ_pos).ne'
  have hγtop : ENNReal.ofReal (gammaBar h.α h.β) ≠ ∞ := ENNReal.ofReal_ne_top
  have hγtoReal : (ENNReal.ofReal (gammaBar h.α h.β)).toReal = gammaBar h.α h.β :=
    ENNReal.toReal_ofReal hγ_pos.le
  -- The two candidate uniform Banach-norm radii.
  have hC_nn : 0 ≤ bounds.C := bounds.C_nn
  set Rβ : ℝ := bounds.C ^ ((betaBar h.β)⁻¹) with hRβ
  set Rγ : ℝ := bounds.C ^ ((gammaBar h.α h.β)⁻¹) with hRγ
  have hRβ_nn : 0 ≤ Rβ := Real.rpow_nonneg hC_nn _
  have hRγ_nn : 0 ≤ Rγ := Real.rpow_nonneg hC_nn _
  have hR_nn : 0 ≤ max Rβ Rγ := le_trans hRβ_nn (le_max_left _ _)
  refine isBounded_iff_forall_norm_le.mpr ⟨max Rβ Rγ, ?_⟩
  rintro x ⟨n, rfl⟩
  -- The per-n apriori bound: `A + Bterm + Cterm ≤ bounds.C`.
  have hbound := bounds.bound (εSeq n) (εSeq_pos n)
  -- `m_ε ≥ 0` a.e. on the cube (two-track positivity: nonneg track only).
  have hmnn : ∀ᵐ y ∂μ, 0 ≤ seq.m (εSeq n) y := seq.mε_nonneg (εSeq n) (εSeq_pos n)
  -- Nonnegativity of the three summands of `hbound`.
  have hA_nn : 0 ≤ ∫ y in UnitCube d, seq.m (εSeq n) y ^ betaBar h.β
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmnn] with y hy
    exact Real.rpow_nonneg hy _
  have hB_nn : 0 ≤ lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) (seq.u (εSeq n))
      ^ gammaBar h.α h.β :=
    Real.rpow_nonneg (Periodic.lpNormPer_nonneg _ _) _
  have hC_term_nn : 0 ≤ ∫ y in UnitCube d,
      ‖(fun i => seq.Du (εSeq n) i y)‖ ^ gammaBar h.α h.β
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    refine integral_nonneg ?_
    intro y; exact Real.rpow_nonneg (norm_nonneg _) _
  -- Drop two summands at a time to isolate each summand `≤ bounds.C`.
  have hA_le : (∫ y in UnitCube d, seq.m (εSeq n) y ^ betaBar h.β
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) ≤ bounds.C :=
    le_trans (by linarith) hbound
  have hB_le : lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) (seq.u (εSeq n))
      ^ gammaBar h.α h.β ≤ bounds.C := le_trans (by linarith) hbound
  have hC_le : (∫ y in UnitCube d,
      ‖(fun i => seq.Du (εSeq n) i y)‖ ^ gammaBar h.α h.β
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) ≤ bounds.C :=
    le_trans (by linarith) hbound
  ------------------------------------------------------------------
  -- m-component: `‖(vEps n).1‖ ≤ Rβ`.
  ------------------------------------------------------------------
  have hm_bound : ‖(vEps n).1‖ ≤ Rβ := by
    -- Transport `∫ ‖⇑(vEps n).1‖^β ∂μ ≤ bounds.C` via `haeM` + `m_ε > 0`.
    have hint_le :
        (∫ y, ‖((vEps n).1 : (Fin d → ℝ) → ℝ) y‖
            ^ (ENNReal.ofReal (h.β + 1)).toReal ∂μ) ≤ bounds.C := by
      have heq :
          (∫ y, ‖((vEps n).1 : (Fin d → ℝ) → ℝ) y‖
              ^ (ENNReal.ofReal (h.β + 1)).toReal ∂μ)
            = ∫ y in UnitCube d, seq.m (εSeq n) y ^ betaBar h.β
                ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
        rw [hβtoReal]
        refine integral_congr_ae ?_
        filter_upwards [haeM n, hmnn] with y hy hnn
        rw [Real.norm_eq_abs, ← hy, abs_of_nonneg hnn]
      rw [heq]; exact hA_le
    have := norm_lp_le_of_integral_rpow_le hβzero hβtop (vEps n).1 hC_nn hint_le
    rwa [hβtoReal, ← hRβ] at this
  ------------------------------------------------------------------
  -- u-component: `‖(vEps n).2.1‖ ≤ Rγ`.
  ------------------------------------------------------------------
  have hu_bound : ‖(vEps n).2.1‖ ≤ Rγ := by
    -- `‖(vEps n).2.1‖ = lpNormPer γ̄ (u_ε)` via `haeU`.
    have h_norm_eq :
        ‖(vEps n).2.1‖ = lpNormPer (ENNReal.ofReal (gammaBar h.α h.β))
          (seq.u (εSeq n)) := by
      rw [MeasureTheory.Lp.norm_def]
      change (MeasureTheory.eLpNorm ((vEps n).2.1 : (Fin d → ℝ) → ℝ)
          (ENNReal.ofReal (gammaBar h.α h.β)) μ).toReal
        = (Periodic.eLpNormPer (ENNReal.ofReal (gammaBar h.α h.β))
            (seq.u (εSeq n))).toReal
      rw [Periodic.eLpNormPer, MeasureTheory.eLpNorm_congr_ae (haeU n).symm]
    have hu_nn : 0 ≤ ‖(vEps n).2.1‖ := norm_nonneg _
    have h_pow_le : ‖(vEps n).2.1‖ ^ gammaBar h.α h.β ≤ bounds.C := by
      rw [h_norm_eq]; exact hB_le
    rw [hRγ]
    exact (Real.le_rpow_inv_iff_of_pos hu_nn hC_nn hγ_pos).mpr h_pow_le
  ------------------------------------------------------------------
  -- Du-component: `‖(vEps n).2.2 i‖ ≤ Rγ` for each axis `i`.
  ------------------------------------------------------------------
  have hDu_bound : ∀ i, ‖(vEps n).2.2 i‖ ≤ Rγ := by
    intro i
    -- Integrability of `|Du_ε i|^γ` from `MemLpPer γ̄ (Du_ε i)`.
    have hDu_memLp : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β))
        (seq.Du (εSeq n) i) := seq.hDu_lp (εSeq n) (εSeq_pos n) i
    have hint_DuI : Integrable
        (fun y => |seq.Du (εSeq n) i y| ^ gammaBar h.α h.β) μ := by
      have hmem := (hDu_memLp.toMemLp.integrable_norm_rpow hγzero hγtop)
      rw [hγtoReal] at hmem
      refine (integrable_congr ?_).mpr hmem
      filter_upwards [] with y; rw [Real.norm_eq_abs]
    -- Integrability of `‖vec‖^γ` from `seq.hDu_norm_int`.
    have hint_vec : Integrable
        (fun y => ‖(fun j => seq.Du (εSeq n) j y)‖ ^ gammaBar h.α h.β) μ :=
      seq.hDu_norm_int (εSeq n) (εSeq_pos n)
    have hint_le :
        (∫ y, ‖(((vEps n).2.2 i) : (Fin d → ℝ) → ℝ) y‖
            ^ (ENNReal.ofReal (gammaBar h.α h.β)).toReal ∂μ) ≤ bounds.C := by
      have heq :
          (∫ y, ‖(((vEps n).2.2 i) : (Fin d → ℝ) → ℝ) y‖
              ^ (ENNReal.ofReal (gammaBar h.α h.β)).toReal ∂μ)
            = ∫ y, |seq.Du (εSeq n) i y| ^ gammaBar h.α h.β ∂μ := by
        rw [hγtoReal]
        refine integral_congr_ae ?_
        filter_upwards [haeDu n i] with y hy
        rw [Real.norm_eq_abs, ← hy]
      have hcomp_le :
          (∫ y, |seq.Du (εSeq n) i y| ^ gammaBar h.α h.β ∂μ)
            ≤ ∫ y in UnitCube d, ‖(fun j => seq.Du (εSeq n) j y)‖
                ^ gammaBar h.α h.β
                ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
        refine integral_mono_ae hint_DuI hint_vec ?_
        filter_upwards [] with y
        have hle : |seq.Du (εSeq n) i y|
            ≤ ‖(fun j => seq.Du (εSeq n) j y)‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (fun j => seq.Du (εSeq n) j y) i
        exact Real.rpow_le_rpow (abs_nonneg _) hle hγ_pos.le
      rw [heq]; exact le_trans hcomp_le hC_le
    have := norm_lp_le_of_integral_rpow_le hγzero hγtop ((vEps n).2.2 i) hC_nn hint_le
    rwa [hγtoReal, ← hRγ] at this
  ------------------------------------------------------------------
  -- Combine via the product / pi norm structure.
  ------------------------------------------------------------------
  rw [Prod.norm_def]
  refine max_le (le_trans hm_bound (le_max_left _ _)) ?_
  rw [Prod.norm_def]
  refine max_le (le_trans hu_bound (le_max_right _ _)) ?_
  rw [pi_norm_le_iff_of_nonneg hR_nn]
  exact fun i => le_trans (hDu_bound i) (le_max_right _ _)

/-! ## Discharging `hRefl` and `hSep` from the paper exponents

The two abstract Banach-space hypotheses
`hRefl` (reflexivity of `L^{β̄}_per × W^{1,γ̄}_per`) and `hSep`
(separability of its strong dual) were historically carried as
bridge-deferred oracle fields. They are in fact *fully paper-derivable*:
given only the Hamiltonian growth parameters `1 < α` (`h.hα`) and
`0 < β` (`h.hβ`) of `HypothesisPowerGrowth`, the exponents
`β̄ = β + 1` and `γ̄ = α(β+1)/β` are strictly between `1` and `∞`,
with explicit Hölder conjugates `β̄' = (β+1)/β` and
`γ̄' = γ̄/(γ̄-1)`. The two lemmas below feed this conjugate-exponent
data to the project's general-`p` product lemmas
`Periodic.lpSobolev_product_isReflexive` (LpReflexive.lean) and
`Periodic.lpSobolev_product_strongDual_separable` (Separability.lean).

The derivation consumes only `h.hα`/`h.hβ` — it does not re-assume the
conclusion — so the corresponding oracle fields are removed
(`CongestionPack4BanachRealisationOracle`: 20 → 18 fields). The recipe
mirrors `SimplePower/Banach/AssemblyContext.lean` lines 7072–7121. -/

/-- **Reflexivity of the paper product space, derived from `h.hα`/`h.hβ`.**
The conjugate exponents `β̄' = (β+1)/β` and `γ̄' = γ̄/(γ̄-1)` are
computed in-body and fed to `Periodic.lpSobolev_product_isReflexive`. -/
lemma compactness_congestionOracle_hRefl
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] :
    IsReflexiveNormedSpace
      (LpPer (ENNReal.ofReal (h.β + 1)) d
        × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) := by
  classical
  -- β-side: βBarReal = β + 1, conjugate βBarReal' = (β+1)/β.
  have hβ : 0 < h.β := h.hβ
  have hα : 1 < h.α := h.hα
  set βBarReal : ℝ := h.β + 1 with hβBar_def
  set βBarReal' : ℝ := (h.β + 1) / h.β with hβBar'_def
  have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by rw [hβBar_def]; linarith
  have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
    rw [hβBar'_def]; positivity
  have h_one_lt_βBarReal' : (1 : ℝ) < βBarReal' := by
    rw [hβBar'_def, lt_div_iff₀ hβ, one_mul]; linarith
  have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
    rw [hβBar_def, hβBar'_def, Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have hβ1 : (0 : ℝ) < h.β + 1 := by linarith
    have hβ1ne : h.β + 1 ≠ 0 := ne_of_gt hβ1
    have hβne : h.β ≠ 0 := ne_of_gt hβ
    have hdiv : ((h.β + 1) / h.β)⁻¹ = h.β / (h.β + 1) := by field_simp
    rw [hdiv]; field_simp; ring
  have hβConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
        (ENNReal.ofReal βBarReal') :=
    Real.HolderConjugate.ennrealOfReal hβConj_real
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBarReal') := hβConj_enn
  haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_βBarReal'.le⟩
  -- γ-side: γBarReal = γ̄, conjugate γBarReal' = γ̄/(γ̄-1).
  have h_one_lt_γBarReal : (1 : ℝ) < gammaBar h.α h.β :=
    StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β hα hβ
  set γBarReal : ℝ := gammaBar h.α h.β with hγBar_def
  set γBarReal' : ℝ := γBarReal / (γBarReal - 1) with hγBar'_def
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by
    rw [hγBar_def]; linarith
  have h_one_lt_γBarReal' : (1 : ℝ) < γBarReal' := by
    rw [hγBar'_def, lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
    rw [hγBar_def] at h_γBar_minus_one_pos ⊢; linarith
  have hγConj_real : Real.HolderConjugate γBarReal γBarReal' := by
    have := Real.HolderConjugate.conjExponent
      (p := γBarReal) (by rw [hγBar_def] at h_one_lt_γBarReal ⊢; exact h_one_lt_γBarReal)
    rwa [Real.conjExponent, ← hγBar'_def] at this
  have hγConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal γBarReal') :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarReal') := hγConj_enn
  haveI : Fact (1 ≤ ENNReal.ofReal γBarReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_γBarReal'.le⟩
  -- `1 < ofReal _` and `ofReal _ ≠ ∞` for both exponents.
  have h_βBar_one_lt : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr h_one_lt_βBarReal
  have h_γBar_one_lt : (1 : ℝ≥0∞) < ENNReal.ofReal γBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr ?_
    rw [hγBar_def] at h_one_lt_γBarReal ⊢; exact h_one_lt_γBarReal
  exact Periodic.lpSobolev_product_isReflexive (d := d)
    (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
    (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarReal')
    h_βBar_one_lt ENNReal.ofReal_ne_top h_γBar_one_lt ENNReal.ofReal_ne_top

/-- **Strong-dual separability of the paper product space, derived from
`h.hα`/`h.hβ`.** Same conjugate-exponent setup as
`compactness_congestionOracle_hRefl`, fed to
`Periodic.lpSobolev_product_strongDual_separable`. -/
lemma compactness_congestionOracle_hSep
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] :
    TopologicalSpace.SeparableSpace
      (StrongDual ℝ
        (LpPer (ENNReal.ofReal (h.β + 1)) d
          × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)) := by
  classical
  have hβ : 0 < h.β := h.hβ
  have hα : 1 < h.α := h.hα
  set βBarReal : ℝ := h.β + 1 with hβBar_def
  set βBarReal' : ℝ := (h.β + 1) / h.β with hβBar'_def
  have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by rw [hβBar_def]; linarith
  have h_one_lt_βBarReal' : (1 : ℝ) < βBarReal' := by
    rw [hβBar'_def, lt_div_iff₀ hβ, one_mul]; linarith
  have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
    rw [hβBar_def, hβBar'_def, Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have hβ1 : (0 : ℝ) < h.β + 1 := by linarith
    have hβ1ne : h.β + 1 ≠ 0 := ne_of_gt hβ1
    have hβne : h.β ≠ 0 := ne_of_gt hβ
    have hdiv : ((h.β + 1) / h.β)⁻¹ = h.β / (h.β + 1) := by field_simp
    rw [hdiv]; field_simp; ring
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBarReal') :=
    Real.HolderConjugate.ennrealOfReal hβConj_real
  haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_βBarReal'.le⟩
  have h_one_lt_γBarReal : (1 : ℝ) < gammaBar h.α h.β :=
    StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β hα hβ
  set γBarReal : ℝ := gammaBar h.α h.β with hγBar_def
  set γBarReal' : ℝ := γBarReal / (γBarReal - 1) with hγBar'_def
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by
    rw [hγBar_def]; linarith
  have h_one_lt_γBarReal' : (1 : ℝ) < γBarReal' := by
    rw [hγBar'_def, lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
    rw [hγBar_def] at h_γBar_minus_one_pos ⊢; linarith
  have hγConj_real : Real.HolderConjugate γBarReal γBarReal' := by
    have := Real.HolderConjugate.conjExponent
      (p := γBarReal) (by rw [hγBar_def] at h_one_lt_γBarReal ⊢; exact h_one_lt_γBarReal)
    rwa [Real.conjExponent, ← hγBar'_def] at this
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarReal') :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI : Fact (1 ≤ ENNReal.ofReal γBarReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_γBarReal'.le⟩
  have h_βBar_one_lt : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr h_one_lt_βBarReal
  have h_γBar_one_lt : (1 : ℝ≥0∞) < ENNReal.ofReal γBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr ?_
    rw [hγBar_def] at h_one_lt_γBarReal ⊢; exact h_one_lt_γBarReal
  exact Periodic.lpSobolev_product_strongDual_separable (d := d)
    (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
    (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarReal')
    h_βBar_one_lt ENNReal.ofReal_ne_top h_γBar_one_lt ENNReal.ofReal_ne_top

/-! ## Group 2 — Banach–Alaoglu weak-limit extraction

The Step-1 producer (`congestionBanachRealisation_vEps_of_paperHypotheses`,
parent task P2) supplies a per-`n` realisation sequence `vEps` in the
reflexive product space, bounded uniformly via
`congestionWeakCompactness_hBound_of_aprioriBounds`. This section runs the
sequential Banach–Alaoglu / Eberlein–Smulian extraction
(`weak_compactness_congestion`) on that sequence with the non-negativity
cone `nonNegConeLpPer (β+1) d` as the sequentially-weakly-closed
first-coordinate constraint (Mazur, `nonNegConeLpPer_isSeqClosedW`), and
reads out the named Banach representatives of the weak limit:

* `mLimBanach : LpPer (ofReal (β+1)) d`  (the limit's first coordinate),
* `uLimBanach`, `DuLimBanach`  (the `SobolevPerLp` second coordinate,
  which is definitionally `Lp γ̄ × (Fin d → Lp γ̄)`),

together with cone preservation `hMLimBanach_nn : 0 ≤ᵐ ⇑mLimBanach`,
transported from the cone membership of the cluster point's first
projection (the image-under-`toWeakSpace` membership `hzS` of
`weak_compactness_congestion`).

This discharges the four Group-2 fields of
`CongestionPack4BanachRealisationOracle` (`mLimBanach`, `uLimBanach`,
`DuLimBanach`, `hMLimBanach_nn`). The public-signature rewire (consuming
these into the oracle/top-pack) is the job of P2e; here we only build the
producer pieces. -/

/-- **Output bundle of the Banach–Alaoglu weak-limit extraction**
(Group 2). Packages the extracted subsequence index `φ`, the named Banach
representatives of the weak limit `(mLimBanach, uLimBanach, DuLimBanach)`,
the weak-convergence statement, and the cone-preservation
`hMLimBanach_nn`. The exponents are pinned to the paper-canonical values
`ENNReal.ofReal (h.β + 1)` and `ENNReal.ofReal (gammaBar h.α h.β)`. -/
structure CongestionBanachLimitResult
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] where
  /-- Strictly monotone subsequence index of the extracted weakly
  convergent subsequence. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  hMono : StrictMono φ
  /-- Named Banach representative for the `m`-limit. -/
  mLimBanach : LpPer (ENNReal.ofReal (h.β + 1)) d
  /-- Named Banach representative for the `u`-limit. -/
  uLimBanach : MeasureTheory.Lp ℝ (ENNReal.ofReal (gammaBar h.α h.β))
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Named Banach representatives for the weak-derivative family. -/
  DuLimBanach : Fin d → MeasureTheory.Lp ℝ
    (ENNReal.ofReal (gammaBar h.α h.β))
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Weak convergence of the realisation subsequence to the cluster
  point `(mLimBanach, (uLimBanach, DuLimBanach))`. -/
  hWeakConv :
    Tendsto
      (fun k => (toWeakSpace ℝ
          (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
        (congestionBanachRealisation_vEps_of_paperHypotheses h seq (φ k)))
      atTop
      (𝓝 ((toWeakSpace ℝ
          (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
        (mLimBanach, (uLimBanach, DuLimBanach))))
  /-- Cone-membership of the named Banach `m`-limit representative,
  preserved through the weak limit (Mazur). -/
  hMLimBanach_nn :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑mLimBanach : (Fin d → ℝ) → ℝ)

/-- **Banach–Alaoglu weak-limit extraction (Group 2 producer).**

Given the congestion regularised-sequence data `seq` and the uniform
a priori bound `bounds`, extract a weakly convergent subsequence of the
per-`n` realisation sequence
`congestionBanachRealisation_vEps_of_paperHypotheses h seq` and read out
the named Banach representatives `mLimBanach/uLimBanach/DuLimBanach` of the
weak limit together with the cone-preservation `hMLimBanach_nn`.

The proof:
1. takes `vEps := congestionBanachRealisation_vEps_of_paperHypotheses h seq`
   with its a.e.-equality bridges (parent lemmas `haeM/haeU/haeDu`);
2. obtains the uniform bound via
   `congestionWeakCompactness_hBound_of_aprioriBounds`;
3. builds per-`n` cone membership from `seq.mε_nonneg` + the `haeM`
   bridge;
4. invokes `weak_compactness_congestion` with reflexivity
   `compactness_congestionOracle_hRefl h`, separability `compactness_congestionOracle_hSep h`, and
   the Mazur-closed cone (`nonNegConeLpPer_isSeqClosedW`);
5. reads `(mLimBanach, uLimBanach, DuLimBanach) := z` (`WeakSpace ℝ X`
   defeq `X`; `SobolevPerLp 1 γ̄ d = Lp γ̄ × (Fin d → Lp γ̄)`);
6. transports the cluster-point cone membership `hzS` to
   `0 ≤ᵐ ⇑mLimBanach`. -/
noncomputable def congestionBanachRealisation_limit_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] :
    CongestionBanachLimitResult h seq := by
  classical
  -- Banach instances for the product space.
  haveI : TopologicalSpace.SeparableSpace
            (StrongDual ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d ×
              SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)) :=
    compactness_congestionOracle_hSep h
  -- The per-`n` realisation sequence and its a.e.-equality bridges.
  set vEps :
      ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    fun n => congestionBanachRealisation_vEps_of_paperHypotheses h seq n
      with hvEps_def
  have haeM : ∀ n : ℕ,
      seq.m (1 / ((n : ℝ) + 1))
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps n).1 : (Fin d → ℝ) → ℝ) := fun n =>
    congestionBanachRealisation_haeM_of_paperHypotheses h seq n
  have haeU : ∀ n : ℕ,
      seq.u (1 / ((n : ℝ) + 1))
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(vEps n).2.1 : (Fin d → ℝ) → ℝ) := fun n =>
    congestionBanachRealisation_haeU_of_paperHypotheses h seq n
  have haeDu : ∀ (n : ℕ) (i : Fin d),
      seq.Du (1 / ((n : ℝ) + 1)) i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((vEps n).2.2 i) : (Fin d → ℝ) → ℝ) := fun n i =>
    congestionBanachRealisation_haeDu_of_paperHypotheses h seq n i
  -- The null sequence `εSeq n := 1/(n+1)` and its positivity.
  set εSeq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεSeq_def
  have εSeq_pos : ∀ n, 0 < εSeq n := fun n => by rw [hεSeq_def]; positivity
  -- Uniform bound on the realisation sequence.
  have hBound : IsBounded (Set.range vEps) :=
    congestionWeakCompactness_hBound_of_aprioriBounds seq bounds εSeq εSeq_pos
      vEps haeM haeU haeDu
  -- Per-`n` cone membership (nonneg track + a.e.-equality bridge).
  have hCone_mem : ∀ n,
      (vEps n).1 ∈ nonNegConeLpPer (ENNReal.ofReal (h.β + 1)) d := by
    intro n
    change 0 ≤ᵐ[MeasureTheory.Measure.restrict
                    MeasureTheory.volume (UnitCube d)]
            (⇑(vEps n).1 : (Fin d → ℝ) → ℝ)
    have hMε_nn :
        0 ≤ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] seq.m (εSeq n) :=
      seq.mε_nonneg (εSeq n) (εSeq_pos n)
    filter_upwards [hMε_nn, haeM n] with x hxnn hxeq
    exact hxeq ▸ hxnn
  -- Cone membership at the weak-image level.
  have hCone_imgmem : ∀ n,
      weakProdFst ((toWeakSpace ℝ
          (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
          (vEps n))
        ∈ (toWeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d)) ''
            nonNegConeLpPer (ENNReal.ofReal (h.β + 1)) d := by
    intro n
    exact ⟨(vEps n).1, hCone_mem n, rfl⟩
  -- Cone constraint set is sequentially weakly closed (Mazur).
  have hS_closed :
      IsSeqClosed ((toWeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d)) ''
        nonNegConeLpPer (ENNReal.ofReal (h.β + 1)) d) :=
    StationaryMFG.Theorems.SimplePower.Banach.nonNegConeLpPer_isSeqClosedW
  -- **Apply `weak_compactness_congestion`.** Route through `Classical.choose`
  -- because the goal is a `Type`-valued structure.
  set hExt :=
    weak_compactness_congestion
      (Y := LpPer (ENNReal.ofReal (h.β + 1)) d)
      (Z := SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)
      (compactness_congestionOracle_hRefl h) vEps hBound hS_closed hCone_imgmem
      with hExt_def
  let φ : ℕ → ℕ := Classical.choose hExt
  have hExt2 := Classical.choose_spec hExt
  let z : WeakSpace ℝ
            (LpPer (ENNReal.ofReal (h.β + 1)) d
              × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) :=
    Classical.choose hExt2
  have hExt3 := Classical.choose_spec hExt2
  obtain ⟨hMono, hzS, hzLim⟩ := hExt3
  -- Read out the named Banach representatives. `WeakSpace ℝ X` is defeq
  -- to `X`; `SobolevPerLp 1 γ̄ d = Lp γ̄ × (Fin d → Lp γ̄)`.
  -- `z.1 : LpPer (β+1) d`, `z.2.1 : Lp γ̄`, `z.2.2 : Fin d → Lp γ̄`.
  -- Transport the cluster-point cone membership to `0 ≤ᵐ ⇑z.1`. The
  -- image membership `hzS` is a `Prop`, but the surrounding goal is the
  -- `Type`-valued structure, so the `Exists` destructuring must happen
  -- inside the `Prop`-valued `hMLim_nn` proof block.
  -- `hzS : weakProdFst z ∈ (toWeakSpace _) '' nonNegConeLpPer …`.
  have hMLim_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(z.1 : LpPer (ENNReal.ofReal (h.β + 1)) d) : (Fin d → ℝ) → ℝ) := by
    obtain ⟨w, hw_mem, hw_eq⟩ := hzS
    -- `hw_eq : toWeakSpace ℝ _ w = weakProdFst z`. Both sides are defeq
    -- to `w` and `z.1` respectively, so `w = z.1`.
    have hw_eq' : w = z.1 := hw_eq
    have : z.1 ∈ nonNegConeLpPer (ENNReal.ofReal (h.β + 1)) d :=
      hw_eq' ▸ hw_mem
    exact this
  exact
    { φ := φ
      hMono := hMono
      mLimBanach := z.1
      uLimBanach := z.2.1
      DuLimBanach := z.2.2
      hWeakConv := hzLim
      hMLimBanach_nn := hMLim_nn }

/-! ## Step 3 — periodic representatives of the Banach weak limit (Group 3)

Paper `eq:compactness.congestion` (line 1599) states the weak limit
`(m, u)` as a *concrete periodic function* on the torus. P2b
(`congestionBanachRealisation_limit_of_paperHypotheses`) produced the
abstract Banach (quotient `Lp`) representatives
`mLimBanach/uLimBanach/DuLimBanach`. This step selects, for each of those
quotient elements, a concrete *periodic* bare function via the Path-A
primitive `bareCoeFnOfLpPer` (Periodic/Lp.lean): `rep x := (⇑f) (fracVec x)`
is pointwise periodic and a.e.-equal to `⇑f` on the unit cube.

This discharges the nine Group-3 fields of
`CongestionPack4BanachRealisationOracle`:
`mLim/uLim/DuLim`, `hMlimPer/hUlimPer`, `hMlim_memLp`, and
`haeMLim/haeULim/haeDuLim`. The Sobolev-side fields
`hUlim_sob/hDuLimWeak` are deferred to `P2d-sobolev-limit`. The
public-signature rewire (consuming these into the oracle/top-pack) is the
job of P2e; here we only build the producer pieces. -/

/-- **Output bundle of the periodic-representative selection** (Group 3).
Given the named Banach weak-limit representatives
`(mLimBanach, uLimBanach, DuLimBanach)`, this packages the chosen
*concrete periodic* bare functions `mLim/uLim/DuLim`, their periodicity
`hMlimPer/hUlimPer`, the periodic-`L^{β̄}` membership `hMlim_memLp` of the
`m`-limit, and the a.e.-equality bridges `haeMLim/haeULim/haeDuLim` to the
Banach representatives. The exponents are pinned to the paper-canonical
values `ENNReal.ofReal (h.β + 1)` and `ENNReal.ofReal (gammaBar h.α h.β)`.

The Banach representatives are taken as explicit parameters (not re-derived
here), so P2e can feed in the `mLimBanach/uLimBanach/DuLimBanach` produced
by `congestionBanachRealisation_limit_of_paperHypotheses`. -/
structure CongestionPeriodicRepResult
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (mLimBanach : LpPer (ENNReal.ofReal (h.β + 1)) d)
    (uLimBanach : MeasureTheory.Lp ℝ (ENNReal.ofReal (gammaBar h.α h.β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (DuLimBanach : Fin d → MeasureTheory.Lp ℝ
      (ENNReal.ofReal (gammaBar h.α h.β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] where
  /-- Chosen periodic representative for the `m`-limit. -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic representative for the `u`-limit. -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic representatives for the weak-derivative family. -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- Periodicity of `mLim`. -/
  hMlimPer : IsPeriodic mLim
  /-- Periodicity of `uLim`. -/
  hUlimPer : IsPeriodic uLim
  /-- Periodicity of each `DuLim i` (the `.rep` representative is periodic). -/
  hDuLimPer : ∀ i, IsPeriodic (DuLim i)
  /-- `mLim ∈ L^{β̄}_per`. -/
  hMlim_memLp : MemLpPer (ENNReal.ofReal (h.β + 1)) mLim
  /-- Periodic-representative bridge for `mLimBanach`. -/
  haeMLim :
    mLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑mLimBanach : (Fin d → ℝ) → ℝ)
  /-- Periodic-representative bridge for `uLimBanach`. -/
  haeULim :
    uLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑uLimBanach : (Fin d → ℝ) → ℝ)
  /-- Periodic-representative bridges for each `DuLimBanach i`. -/
  haeDuLim : ∀ i,
    DuLim i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ)

/-- **Periodic-representative selection (Group 3 producer).**

Given named Banach weak-limit representatives
`(mLimBanach, uLimBanach, DuLimBanach)`, select concrete *periodic* bare
functions for each and bundle them with their periodicity, the
periodic-`L^{β̄}` membership of the `m`-limit, and the a.e.-equality
bridges.

The proof:
1. applies the Path-A primitive `bareCoeFnOfLpPer` to each Banach
   representative (this works for any exponent `p` since
   `LpPer p d = Lp ℝ p (restrict volume (UnitCube d))` definitionally);
   each gives a periodic `rep` together with `rep =ᵐ ⇑f` on the cube
   (already the oracle direction `mLim =ᵐ ⇑mLimBanach`, so no `.symm`);
2. transfers `MemLp ⇑mLimBanach … = MemLpPer (β+1) ⇑mLimBanach` (the
   coercion of a quotient `Lp` element, `Lp.memLp`) across the
   a.e.-equality `⇑mLimBanach =ᵐ mLim` (i.e. `haeMLim.symm`) via
   `MemLp.ae_eq` to obtain `hMlim_memLp : MemLpPer (β+1) mLim`. -/
noncomputable def congestionPeriodicReps_of_banachLimit
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (mLimBanach : LpPer (ENNReal.ofReal (h.β + 1)) d)
    (uLimBanach : MeasureTheory.Lp ℝ (ENNReal.ofReal (gammaBar h.α h.β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (DuLimBanach : Fin d → MeasureTheory.Lp ℝ
      (ENNReal.ofReal (gammaBar h.α h.β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] :
    CongestionPeriodicRepResult h seq mLimBanach uLimBanach DuLimBanach := by
  classical
  -- Periodic representatives of each Banach quotient element.
  set mRep := StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) mLimBanach with hmRep_def
  set uRep := StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) uLimBanach with huRep_def
  -- `mRep.ae_eq : mRep.rep =ᵐ ⇑mLimBanach` — the oracle direction.
  have haeMLim :
      mRep.rep
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑mLimBanach : (Fin d → ℝ) → ℝ) := mRep.ae_eq
  -- Transfer `MemLp ⇑mLimBanach` across `⇑mLimBanach =ᵐ mRep.rep`.
  have hMlim_memLp : MemLpPer (ENNReal.ofReal (h.β + 1)) mRep.rep :=
    MeasureTheory.MemLp.ae_eq haeMLim.symm (MeasureTheory.Lp.memLp mLimBanach)
  exact
    { mLim := mRep.rep
      uLim := uRep.rep
      DuLim := fun i => (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).rep
      hMlimPer := mRep.periodic
      hUlimPer := uRep.periodic
      hDuLimPer := fun i =>
        (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).periodic
      hMlim_memLp := hMlim_memLp
      haeMLim := haeMLim
      haeULim := uRep.ae_eq
      haeDuLim := fun i => (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (DuLimBanach i)).ae_eq }

/-! ## Step 4 — Sobolev regularity of the weak limit (Group 4, P2d/P2d₂)

Paper `eq:compactness.congestion` (line 1599) asserts not only that
`(m_{ε_k}, u_{ε_k}) ⇀ (m,u)` weakly in `L^{β̄}_per × W^{1,γ̄}_per`, but that
the limit `u` is *itself* in `W^{1,γ̄}_per` with weak gradient the weak
limit of `∇u_{ε_k}`. This step discharges the two Sobolev-side fields of
`CongestionPack4BanachRealisationOracle`:

* `hDuLimWeak i : HasWeakDerivPer i uLim (DuLim i)`,
* `hUlim_sob   : MemSobolevPer γ̄ uLim`.

The analysis is **already done** upstream:

1. `StationaryMFG.Periodic.hasWeakDerivPer_of_weak_limit` (Sobolev.lean,
   P2d): the weak derivative passes to a weak limit, given per-`k`
   `HasWeakDerivPer i (uSeq k) (gSeq k)` plus smooth-tester convergence of
   `uSeq` and `gSeq`.
2. The smooth-tester convergence is supplied by the SimplePower Banach
   corollaries `tendsto_smoothTester_of_banachWeak_pair_snd_val` /
   `…_pair_snd_grad`, applied to the product weak convergence `hWeakConv`.

This producer is therefore pure plumbing: feed the tester corollaries
from `hWeakConv` (rewritten through the per-`n` ae-bridges `haeU/haeDu`
and the periodic-rep bridges `haeULim/haeDuLim`) into the abstract
weak-limit lemma. No new analysis, no oracle. -/

/-- **Output bundle of the Sobolev-regularity step** (Group 4). Given the
named Banach weak-limit `u`-representatives `uLimBanach/DuLimBanach`
(produced by `congestionBanachRealisation_limit_of_paperHypotheses`) along
the subsequence index `φ`, together with the chosen periodic
representatives `uLim/DuLim` and their ae-bridges (produced by
`congestionPeriodicReps_of_banachLimit`), this packages the two
Sobolev-side facts `hUlim_sob` and `hDuLimWeak` that the public oracle
still needs. -/
structure CongestionSobolevLimitResult
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] where
  /-- `uLim ∈ W^{1,γ̄}_per`, with weak gradient family `DuLim`. -/
  hUlim_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) uLim
  /-- Each `DuLim i` is the `i`-th weak derivative of `uLim`. -/
  hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i)

/-- **Sobolev-regularity of the weak limit (Group 4 producer).**

Given the named Banach `u`-limit representatives `uLimBanach/DuLimBanach`,
the extracted subsequence index `φ` with the product weak convergence
`hWeakConv` of `congestionBanachRealisation_vEps_of_paperHypotheses` along
`φ`, and the chosen periodic representatives `uLim/DuLim` with their
ae-bridges `haeULim/haeDuLim`, derive

* `hDuLimWeak i : HasWeakDerivPer i uLim (DuLim i)`,
* `hUlim_sob   : MemSobolevPer γ̄ uLim`.

The proof feeds `hasWeakDerivPer_of_weak_limit` (P2d) with the per-`k`
weak-derivative witnesses `seq.hDu_weak (1/(φ k + 1))` and the
smooth-tester convergence extracted from `hWeakConv` via the SimplePower
Banach corollaries, rewritten through the ae-bridges. -/
noncomputable def congestionSobolevLimit_of_banachLimit
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (φ : ℕ → ℕ)
    (uLimBanach : MeasureTheory.Lp ℝ (ENNReal.ofReal (gammaBar h.α h.β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (DuLimBanach : Fin d → MeasureTheory.Lp ℝ
      (ENNReal.ofReal (gammaBar h.α h.β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (mLimBanach : LpPer (ENNReal.ofReal (h.β + 1)) d)
    (hWeakConv :
      Tendsto
        (fun k => (toWeakSpace ℝ
            (LpPer (ENNReal.ofReal (h.β + 1)) d
              × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
          (congestionBanachRealisation_vEps_of_paperHypotheses h seq (φ k)))
        atTop
        (𝓝 ((toWeakSpace ℝ
            (LpPer (ENNReal.ofReal (h.β + 1)) d
              × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
          (mLimBanach, (uLimBanach, DuLimBanach)))))
    (uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (haeULim :
      uLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑uLimBanach : (Fin d → ℝ) → ℝ))
    (haeDuLim : ∀ i,
      DuLim i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(DuLimBanach i) : (Fin d → ℝ) → ℝ)) :
    CongestionSobolevLimitResult h seq uLim DuLim := by
  classical
  -- Conjugate exponent `γ̄'` and its `HolderConjugate` instance (cf.
  -- Coercivity.lean). We deliberately do NOT `set` `γReal := gammaBar …`,
  -- since that would revert/reintroduce the `Lp (ofReal (gammaBar …))`-typed
  -- hypotheses and create spurious shadow binders.
  have h_one_lt_γ : (1 : ℝ) < gammaBar h.α h.β :=
    StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β h.hα h.hβ
  have h_γ_minus_one_pos : (0 : ℝ) < gammaBar h.α h.β - 1 := by linarith
  set γReal' : ℝ := gammaBar h.α h.β / (gammaBar h.α h.β - 1) with hγReal'_def
  have h_one_lt_γReal' : (1 : ℝ) < γReal' := by
    rw [hγReal'_def, lt_div_iff₀ h_γ_minus_one_pos, one_mul]; linarith
  have hγConj_real : Real.HolderConjugate (gammaBar h.α h.β) γReal' := by
    have := Real.HolderConjugate.conjExponent (p := gammaBar h.α h.β) h_one_lt_γ
    rwa [Real.conjExponent, ← hγReal'_def] at this
  haveI hHC : ENNReal.HolderConjugate (ENNReal.ofReal (gammaBar h.α h.β))
                (ENNReal.ofReal γReal') :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI : Fact (1 ≤ ENNReal.ofReal γReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_γReal'.le⟩
  have hγ_ne_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ∞ := ENNReal.ofReal_ne_top
  -- The full realisation sequence and its weak convergence along `φ`,
  -- packaged for the SimplePower tester corollaries with `z_n := vEps ∘ φ`.
  set vEps :
      ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    fun n => congestionBanachRealisation_vEps_of_paperHypotheses h seq n
      with hvEps_def
  set zn :
      ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    fun k => vEps (φ k) with hzn_def
  have hWeak' :
      Tendsto
        (fun k => toWeakSpace ℝ
          (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) (zn k))
        atTop
        (𝓝 (toWeakSpace ℝ
          (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)
          (mLimBanach, (uLimBanach, DuLimBanach)))) :=
    hWeakConv
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
      (βBar := ENNReal.ofReal (h.β + 1))
      (γBar := ENNReal.ofReal (gammaBar h.α h.β)) (γBar' := ENNReal.ofReal γReal')
      hHC hγ_ne_top zn (mLimBanach, (uLimBanach, DuLimBanach)) hWeak'
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
        (βBar := ENNReal.ofReal (h.β + 1))
        (γBar := ENNReal.ofReal (gammaBar h.α h.β)) (γBar' := ENNReal.ofReal γReal')
        hHC hγ_ne_top zn (mLimBanach, (uLimBanach, DuLimBanach)) hWeak' i
  -- Per-`k` ε index, positivity, and ae-bridges to the bare functions.
  have hεk_pos : ∀ k, (0 : ℝ) < 1 / ((φ k : ℝ) + 1) := fun k => by positivity
  have haeUk : ∀ k,
      seq.u (1 / ((φ k : ℝ) + 1))
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(zn k).2.1 : (Fin d → ℝ) → ℝ) :=
    fun k => congestionBanachRealisation_haeU_of_paperHypotheses h seq (φ k)
  have haeDuk : ∀ (k : ℕ) (i : Fin d),
      seq.Du (1 / ((φ k : ℝ) + 1)) i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((zn k).2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun k i => congestionBanachRealisation_haeDu_of_paperHypotheses h seq (φ k) i
  -- `MemLpPer γ̄ uLim` from the Banach `Lp` membership across `haeULim`.
  have hUlim_memLp : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) uLim :=
    MeasureTheory.MemLp.ae_eq haeULim.symm (MeasureTheory.Lp.memLp uLimBanach)
  -- Per-`i`: `MemLpPer γ̄ (DuLim i)`, then downgrade to `MemLpPer 1` on the
  -- finite cube measure, for the `hg` premise of the abstract lemma.
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    inferInstance
  have hDuLim_memLpγ : ∀ i,
      MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (DuLim i) :=
    fun i => MeasureTheory.MemLp.ae_eq (haeDuLim i).symm
      (MeasureTheory.Lp.memLp (DuLimBanach i))
  have hDuLim_memLp1 : ∀ i, MemLpPer 1 (DuLim i) := by
    intro i
    have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_γ.le
    exact StationaryMFG.Periodic.MemLp.toMemLpPer
      ((hDuLim_memLpγ i).toMemLp.mono_exponent h1le)
  -- Assemble `hDuLimWeak i` via the abstract weak-limit lemma.
  have hDuLimWeak : ∀ i, HasWeakDerivPer i uLim (DuLim i) := by
    intro i
    refine Periodic.hasWeakDerivPer_of_weak_limit
      (i := i) (u := uLim) (g := DuLim i)
      (uSeq := fun k => seq.u (1 / ((φ k : ℝ) + 1)))
      (gSeq := fun k => seq.Du (1 / ((φ k : ℝ) + 1)) i)
      (hDuLim_memLp1 i)
      (fun k => seq.hDu_weak (1 / ((φ k : ℝ) + 1)) (hεk_pos k) i)
      ?_ ?_
    · -- `hConvU`: rewrite the tester convergence through the ae-bridges.
      intro ψ
      have hT := hTestU ψ
      -- LHS function equality (every `k`).
      have hfun : (fun k => Periodic.periodicIntegral
            (fun x => (⇑(zn k).2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x => seq.u (1 / ((φ k : ℝ) + 1)) x
              * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        simp only [Periodic.periodicIntegral]
        refine integral_congr_ae ?_
        filter_upwards [haeUk k] with x hx
        rw [hx]
      -- RHS limit-point equality.
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
            (fun x => seq.Du (1 / ((φ k : ℝ) + 1)) i x
              * (ψ : (Fin d → ℝ) → ℝ) x)) := by
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
  exact
    { hUlim_sob := ⟨hUlim_memLp, DuLim, hDuLimWeak⟩
      hDuLimWeak := hDuLimWeak }

/-! ## Step 4b — component weak-pairing certificates (P3a1)

Paper `eq:existweaksol.congestion` (line 1604): the Hölder-duality
limit-passage step needs, for each of the three `mfgOperatorPair`
summands, a *component* weak-convergence certificate phrased as a
bare-function `WeakConvPairing_universal` predicate (the universal layer
of `Banach/WeakPairing.lean`). The single weak datum available is the
combined product `WeakSpace`-tendsto
`CongestionBanachLimitResult.hWeakConv` in
`L^{β̄}_per × W^{1,γ̄}_per`. This step projects that product tendsto onto
each factor (`m` / `u` / `∂_i u`) via the continuous-linear projection
CLMs and feeds the projected component tendsto into
`weakConvPairing_universal_of_toWeakSpace_conv` (the substantive
Mathlib-`Lp` → bare-function bridge), with `hoelderPairing` supplying the
integral-pairing CLM and the periodic-representative ae-bridges
(`haeMLim/haeULim/haeDuLim`) closing the loop to the bare limits.

`LpPer p d := Lp ℝ p (volume.restrict (UnitCube d))` is definitionally
the type of the Banach `u`/`Du` representatives, so no `Lp`↔`LpPer`
coe-bridge is required (Fork B resolved). -/

/-- **Project a product `WeakSpace`-tendsto onto a component via a CLM.**

Given a weak-convergence `toWeakSpace _ (z_n n) → toWeakSpace _ z` in the
product space `LpPer βBar d × SobolevPerLp 1 γBar d` and a continuous
linear projection `T` onto a single `LpPer p d` factor, push the weak
limit forward to obtain `toWeakSpace _ (T (z_n n)) → toWeakSpace _ (T z)`.
This is the abstract content shared by the three component certificates;
it is the same `WeakBilin.tendsto_iff_forall_eval_tendsto` round-trip used
by the `tendsto_smoothTester_of_banachWeak_pair_*` corollaries. -/
private theorem congestionWeakSpaceProj
    {βBar γBar : ℝ≥0∞} {p : ℝ≥0∞}
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] [Fact (1 ≤ p)]
    (z_n : ℕ → LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (z : LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (T : (LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) →L[ℝ] LpPer p d)
    (h : Tendsto
            (fun n => toWeakSpace ℝ
              (LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) (z_n n))
            atTop
            (𝓝 (toWeakSpace ℝ
              (LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) z))) :
    Tendsto
      (fun n => toWeakSpace ℝ (LpPer p d) (T (z_n n)))
      atTop
      (𝓝 (toWeakSpace ℝ (LpPer p d) (T z))) := by
  -- Injectivity of the flipped top-dual pairing on both spaces (the
  -- standard `SeparatingDual` boilerplate).
  have h_inj_prod :
      Function.Injective
        ⇑(topDualPairing ℝ
            (LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : ((LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
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
  have hΛ_prod : ∀ Λ : (LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                          →L[ℝ] ℝ,
      Tendsto (fun n => Λ (z_n n)) atTop (𝓝 (Λ z)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ
              (LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip)
      h_inj_prod).mp h Λ
    simpa using! hh
  -- Reassemble the component tendsto via the `.mpr` direction.
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := (topDualPairing ℝ (LpPer p d)).flip)
        h_inj).mpr ?_
  intro Λ
  have h_compose : Tendsto (fun n => Λ (T (z_n n))) atTop (𝓝 (Λ (T z))) := by
    have := hΛ_prod (Λ.comp T)
    simpa using this
  simpa using! h_compose

/-- **Component weak-pairing certificate for the `m`-limit (P3a1).**

From the Banach weak-limit `blim` (carrying the combined product
`WeakSpace`-tendsto `hWeakConv`) and the periodic-representative
ae-bridge `haeMLim : mLim =ᵐ ⇑blim.mLimBanach`, produce the bare-function
`WeakConvPairing_universal` certificate for the `m`-component:
`∫ m_{ε_{φk}}·φ → ∫ mLim·φ` for every `L^{β̄'}` test `φ`. -/
noncomputable def congestionWeakCertM_of_banachLimit
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (blim : CongestionBanachLimitResult h seq)
    {βBarReal' : ℝ}
    (hpqβ : Real.HolderConjugate (h.β + 1) βBarReal')
    [Fact (1 ≤ ENNReal.ofReal βBarReal')]
    (mLim : (Fin d → ℝ) → ℝ)
    (haeMLim :
      mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑blim.mLimBanach : (Fin d → ℝ) → ℝ)) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal (d := d) hpqβ
      (fun k => seq.m (1 / ((blim.φ k : ℝ) + 1))) mLim := by
  classical
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal (h.β + 1))
            (ENNReal.ofReal βBarReal') :=
    Real.HolderConjugate.ennrealOfReal hpqβ
  -- The realisation sequence and the `fst` projection CLM.
  set vEps :
      ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    fun n => congestionBanachRealisation_vEps_of_paperHypotheses h seq n
      with hvEps_def
  set fst_clm : (LpPer (ENNReal.ofReal (h.β + 1)) d
                  × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)
                  →L[ℝ] LpPer (ENNReal.ofReal (h.β + 1)) d :=
    ContinuousLinearMap.fst ℝ _ _ with hfst_def
  -- Projected component `WeakSpace`-tendsto on `LpPer βBar d`.
  have hProj :
      Tendsto
        (fun k => toWeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d)
          (fst_clm (vEps (blim.φ k))))
        atTop
        (𝓝 (toWeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d)
          (fst_clm (blim.mLimBanach,
            (blim.uLimBanach, blim.DuLimBanach))))) :=
    congestionWeakSpaceProj (fun k => vEps (blim.φ k))
      (blim.mLimBanach, (blim.uLimBanach, blim.DuLimBanach)) fst_clm
      blim.hWeakConv
  -- Apply the substantive Mathlib-`Lp` → bare-function bridge.
  refine StationaryMFG.Theorems.SimplePower.Banach.weakConvPairing_universal_of_toWeakSpace_conv (d := d) hpqβ
    (f_n := fun k => seq.m (1 / ((blim.φ k : ℝ) + 1)))
    (f := mLim)
    (fun k => (vEps (blim.φ k)).1) blim.mLimBanach
    (fun k => congestionBanachRealisation_haeM_of_paperHypotheses h seq (blim.φ k))
    haeMLim hProj
    (fun φ hφ => StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing (φ := MemLpPer.toLp hφ))
    ?_
  -- `Λφ_apply`: the pairing CLM action is the integral against `φ`.
  intro φ hφ G
  rw [StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing_apply]
  refine integral_congr_ae ?_
  have h_ae :
      ⇑(MemLpPer.toLp hφ) =ᵐ[MeasureTheory.Measure.restrict
          MeasureTheory.volume (UnitCube d)] φ :=
    MeasureTheory.MemLp.coeFn_toLp hφ
  filter_upwards [h_ae] with x hx
  change (G x) * (⇑(MemLpPer.toLp hφ) x) = (G x) * (φ x)
  rw [hx]

/-- **Component weak-pairing certificate for the `u`-limit (P3a1).**

Projects `hWeakConv` onto the value factor of the `SobolevPerLp 1 γBar d`
component (`snd` then `fst`) and feeds it through the bare-function
bridge, producing `∫ u_{ε_{φk}}·φ → ∫ uLim·φ` for every `L^{γ̄'}` test. -/
noncomputable def congestionWeakCertU_of_banachLimit
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (blim : CongestionBanachLimitResult h seq)
    {γBarReal' : ℝ}
    (hpqγ : Real.HolderConjugate (gammaBar h.α h.β) γBarReal')
    [Fact (1 ≤ ENNReal.ofReal γBarReal')]
    (uLim : (Fin d → ℝ) → ℝ)
    (haeULim :
      uLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑blim.uLimBanach : (Fin d → ℝ) → ℝ)) :
    StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal (d := d) hpqγ
      (fun k => seq.u (1 / ((blim.φ k : ℝ) + 1))) uLim := by
  classical
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal (gammaBar h.α h.β))
            (ENNReal.ofReal γBarReal') :=
    Real.HolderConjugate.ennrealOfReal hpqγ
  set vEps :
      ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    fun n => congestionBanachRealisation_vEps_of_paperHypotheses h seq n
      with hvEps_def
  -- `snd ∘ fst` picks the value-component of the `SobolevPerLp` factor.
  set proj_clm : (LpPer (ENNReal.ofReal (h.β + 1)) d
                  × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)
                  →L[ℝ] LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    (ContinuousLinearMap.fst ℝ (LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)
        (Fin d → LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)).comp
      (ContinuousLinearMap.snd ℝ _ _) with hproj_def
  have hProj :
      Tendsto
        (fun k => toWeakSpace ℝ (LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)
          (proj_clm (vEps (blim.φ k))))
        atTop
        (𝓝 (toWeakSpace ℝ (LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)
          (proj_clm (blim.mLimBanach,
            (blim.uLimBanach, blim.DuLimBanach))))) :=
    congestionWeakSpaceProj (fun k => vEps (blim.φ k))
      (blim.mLimBanach, (blim.uLimBanach, blim.DuLimBanach)) proj_clm
      blim.hWeakConv
  refine StationaryMFG.Theorems.SimplePower.Banach.weakConvPairing_universal_of_toWeakSpace_conv (d := d) hpqγ
    (f_n := fun k => seq.u (1 / ((blim.φ k : ℝ) + 1)))
    (f := uLim)
    (fun k => (vEps (blim.φ k)).2.1) blim.uLimBanach
    (fun k => congestionBanachRealisation_haeU_of_paperHypotheses h seq (blim.φ k))
    haeULim hProj
    (fun φ hφ => StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing (φ := MemLpPer.toLp hφ))
    ?_
  intro φ hφ G
  rw [StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing_apply]
  refine integral_congr_ae ?_
  have h_ae :
      ⇑(MemLpPer.toLp hφ) =ᵐ[MeasureTheory.Measure.restrict
          MeasureTheory.volume (UnitCube d)] φ :=
    MeasureTheory.MemLp.coeFn_toLp hφ
  filter_upwards [h_ae] with x hx
  change (G x) * (⇑(MemLpPer.toLp hφ) x) = (G x) * (φ x)
  rw [hx]

/-- **Component weak-pairing certificates for the gradient family (P3a1).**

For each direction `i`, projects `hWeakConv` onto the `i`-th gradient
slot of the `SobolevPerLp 1 γBar d` component (`snd ∘ snd ∘ proj i`) and
feeds it through the bare-function bridge, producing
`∫ ∂_i u_{ε_{φk}}·φ → ∫ Du_i·φ` for every `L^{γ̄'}` test. -/
noncomputable def congestionWeakCertDu_of_banachLimit
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (blim : CongestionBanachLimitResult h seq)
    {γBarReal' : ℝ}
    (hpqγ : Real.HolderConjugate (gammaBar h.α h.β) γBarReal')
    [Fact (1 ≤ ENNReal.ofReal γBarReal')]
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (haeDuLim : ∀ i,
      DuLim i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(blim.DuLimBanach i) : (Fin d → ℝ) → ℝ)) :
    ∀ i, StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal (d := d) hpqγ
      (fun k => seq.Du (1 / ((blim.φ k : ℝ) + 1)) i) (DuLim i) := by
  classical
  intro i
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal (gammaBar h.α h.β))
            (ENNReal.ofReal γBarReal') :=
    Real.HolderConjugate.ennrealOfReal hpqγ
  set vEps :
      ℕ → LpPer (ENNReal.ofReal (h.β + 1)) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    fun n => congestionBanachRealisation_vEps_of_paperHypotheses h seq n
      with hvEps_def
  -- `(proj i) ∘ snd ∘ snd` picks the `i`-th gradient component.
  set grad_clm : (LpPer (ENNReal.ofReal (h.β + 1)) d
                  × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d)
                  →L[ℝ] LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d :=
    (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d) i).comp
      ((ContinuousLinearMap.snd ℝ (LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)
          (Fin d → LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)).comp
        (ContinuousLinearMap.snd ℝ _ _)) with hgrad_def
  have hProj :
      Tendsto
        (fun k => toWeakSpace ℝ (LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)
          (grad_clm (vEps (blim.φ k))))
        atTop
        (𝓝 (toWeakSpace ℝ (LpPer (ENNReal.ofReal (gammaBar h.α h.β)) d)
          (grad_clm (blim.mLimBanach,
            (blim.uLimBanach, blim.DuLimBanach))))) :=
    congestionWeakSpaceProj (fun k => vEps (blim.φ k))
      (blim.mLimBanach, (blim.uLimBanach, blim.DuLimBanach)) grad_clm
      blim.hWeakConv
  refine StationaryMFG.Theorems.SimplePower.Banach.weakConvPairing_universal_of_toWeakSpace_conv (d := d) hpqγ
    (f_n := fun k => seq.Du (1 / ((blim.φ k : ℝ) + 1)) i)
    (f := DuLim i)
    (fun k => (vEps (blim.φ k)).2.2 i) (blim.DuLimBanach i)
    (fun k => congestionBanachRealisation_haeDu_of_paperHypotheses h seq (blim.φ k) i)
    (haeDuLim i) hProj
    (fun φ hφ => StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing (φ := MemLpPer.toLp hφ))
    ?_
  intro φ hφ G
  rw [StationaryMFG.Theorems.SimplePower.Banach.hoelderPairing_apply]
  refine integral_congr_ae ?_
  have h_ae :
      ⇑(MemLpPer.toLp hφ) =ᵐ[MeasureTheory.Measure.restrict
          MeasureTheory.volume (UnitCube d)] φ :=
    MeasureTheory.MemLp.coeFn_toLp hφ
  filter_upwards [h_ae] with x hx
  change (G x) * (⇑(MemLpPer.toLp hφ) x) = (G x) * (φ x)
  rw [hx]

/-- **Phase 7 T2 public-signature drain (P2e).** Assemble the full
`CongestionPack4BanachRealisationOracle` from the paper hypotheses —
i.e. from the regularised-sequence data `seq` and the uniform a priori
bound `bounds` alone, with **no** Banach-realisation oracle input.

The 16 fields are populated by chaining the four group producers
(P2a-vEps → P2b-limit → P2c-periodicReps → P2d-sobolevLimit):

* `vEps/haeM/haeU/haeDu` (Group 1) ←
  `congestionBanachRealisation_vEps_of_paperHypotheses` and its three
  a.e.-equality bridge lemmas;
* `mLimBanach/uLimBanach/DuLimBanach/hMLimBanach_nn` (Group 2) ←
  `congestionBanachRealisation_limit_of_paperHypotheses` (Banach–Alaoglu
  weak-limit extraction + Mazur cone preservation);
* `mLim/uLim/DuLim/hMlimPer/hUlimPer/hMlim_memLp/haeMLim/haeULim/haeDuLim`
  (Group 3) ← `congestionPeriodicReps_of_banachLimit` (periodic-rep
  selection);
* `hUlim_sob/hDuLimWeak` (Group 4) ←
  `congestionSobolevLimit_of_banachLimit` (Sobolev regularity of the weak
  limit).

This is the producer that removes `banachOracle` from the public theorem
`thm_main_congestion_growth_paper`. The `εSeq` is pinned to `1/(n+1)`,
matching the structure's rate-sequence convention. -/
noncomputable def CongestionPack4BanachRealisationOracle.of_paperHypotheses
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] :
    CongestionPack4BanachRealisationOracle V H DpH J h seq
      (fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity) := by
  classical
  -- **(P3a5)** `Fact (1 ≤ ofReal _')` instances for the conjugate
  -- exponents, needed by the three weak-cert producers.
  haveI : Fact (1 ≤ ENNReal.ofReal ((h.β + 1) / h.β)) :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal (compactness_congestion_hpqβ h).symm.lt.le⟩
  haveI : Fact (1 ≤ ENNReal.ofReal
            (gammaBar h.α h.β / (gammaBar h.α h.β - 1))) :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal (compactness_congestion_hpqγ h).symm.lt.le⟩
  -- Group 2: Banach–Alaoglu weak-limit extraction.
  set lim := congestionBanachRealisation_limit_of_paperHypotheses h seq bounds
    with hlim_def
  -- Group 3: periodic-representative selection from the named Banach limits.
  set reps := congestionPeriodicReps_of_banachLimit h seq
      lim.mLimBanach lim.uLimBanach lim.DuLimBanach with hreps_def
  -- Group 4: Sobolev regularity of the weak limit.
  set sob := congestionSobolevLimit_of_banachLimit h seq lim.φ
      lim.uLimBanach lim.DuLimBanach lim.mLimBanach lim.hWeakConv
      reps.uLim reps.DuLim reps.haeULim reps.haeDuLim with hsob_def
  exact
    { vEps := fun n => congestionBanachRealisation_vEps_of_paperHypotheses h seq n
      haeM := fun n => congestionBanachRealisation_haeM_of_paperHypotheses h seq n
      haeU := fun n => congestionBanachRealisation_haeU_of_paperHypotheses h seq n
      haeDu := fun n i => congestionBanachRealisation_haeDu_of_paperHypotheses h seq n i
      mLimBanach := lim.mLimBanach
      uLimBanach := lim.uLimBanach
      DuLimBanach := lim.DuLimBanach
      mLim := reps.mLim
      uLim := reps.uLim
      DuLim := reps.DuLim
      hMlimPer := reps.hMlimPer
      hUlimPer := reps.hUlimPer
      hDuLimPer := reps.hDuLimPer
      hMlim_memLp := reps.hMlim_memLp
      hUlim_sob := sob.hUlim_sob
      hDuLimWeak := sob.hDuLimWeak
      haeMLim := reps.haeMLim
      haeULim := reps.haeULim
      haeDuLim := reps.haeDuLim
      hMLimBanach_nn := lim.hMLimBanach_nn
      -- **(P3a5)** Pin the subsequence to the concrete Banach
      -- weak-limit `lim.φ` and build the three weak-pairing certs +
      -- the abstract cone-cluster from `lim` (= `blim`), now in scope.
      subseqφ := lim.φ
      hSubseqMono := lim.hMono
      weakCertM :=
        congestionWeakCertM_of_banachLimit h seq lim (compactness_congestion_hpqβ h)
          reps.mLim reps.haeMLim
      weakCertU :=
        congestionWeakCertU_of_banachLimit h seq lim (compactness_congestion_hpqγ h)
          reps.uLim reps.haeULim
      weakCertDu :=
        congestionWeakCertDu_of_banachLimit h seq lim (compactness_congestion_hpqγ h)
          reps.DuLim reps.haeDuLim
      hWeakConvConeSub :=
        ⟨(toWeakSpace ℝ (LpPer (ENNReal.ofReal (h.β + 1)) d
            × SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d))
            (lim.mLimBanach, (lim.uLimBanach, lim.DuLimBanach)),
          ⟨lim.mLimBanach, lim.hMLimBanach_nn, rfl⟩,
          lim.hWeakConv⟩ }

/-- **Phase 7 T2 sub-task A3 producer**: assemble pack4
(`CongestionWeakCompactnessUpstreamPack`) from `(pack3.hPower, seq)`
plus the Banach-realisation oracle. The εSeq is pinned to
`1/(n+1)`. The pack `hBound` field is now DERIVED in-body (not an
oracle field) from the uniform apriori constant `bounds.C` via
`congestionWeakCompactness_hBound_of_aprioriBounds`. -/
noncomputable def congestionWeakCompactnessUpstreamPack_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (oracle :
      haveI : Fact (1 ≤ ENNReal.ofReal (h.β + 1)) :=
        fact_one_le_ofReal_betaBar h.hβ
      haveI : Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β)) :=
        fact_one_le_ofReal_gammaBar h.hα h.hβ
      CongestionPack4BanachRealisationOracle V H DpH J h seq
                (fun n => 1 / ((n : ℝ) + 1))
                (fun n => by positivity)) :
    CongestionWeakCompactnessUpstreamPack V H DpH J h seq := by
  haveI hfb : Fact (1 ≤ ENNReal.ofReal (h.β + 1)) :=
    fact_one_le_ofReal_betaBar h.hβ
  haveI hfg : Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β)) :=
    fact_one_le_ofReal_gammaBar h.hα h.hβ
  exact
  { βBar := ENNReal.ofReal (h.β + 1)
    γBar := ENNReal.ofReal (gammaBar h.α h.β)
    hβFact := fact_one_le_ofReal_betaBar h.hβ
    hγFact := fact_one_le_ofReal_gammaBar h.hα h.hβ
    εSeq := fun n => 1 / ((n : ℝ) + 1)
    εSeq_pos := fun n => by positivity
    vEps := oracle.vEps
    -- `hBound` is now DERIVED (not an oracle field) from the uniform
    -- apriori constant `bounds.C` via the iter-0877 discharge lemma,
    -- fed the oracle's own `vEps`/`haeM`/`haeU`/`haeDu`.
    hBound :=
      congestionWeakCompactness_hBound_of_aprioriBounds seq bounds
        (fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
        oracle.vEps oracle.haeM oracle.haeU oracle.haeDu
    -- `hRefl`/`hSep` are now DERIVED in-body (not oracle fields) from
    -- `h.hα`/`h.hβ` via the conjugate-exponent recipe + the project
    -- product lemmas `lpSobolev_product_isReflexive` /
    -- `lpSobolev_product_strongDual_separable`.
    hRefl := compactness_congestionOracle_hRefl h
    hSep := compactness_congestionOracle_hSep h
    haeM := oracle.haeM
    haeU := oracle.haeU
    haeDu := oracle.haeDu
    mLimBanach := oracle.mLimBanach
    uLimBanach := oracle.uLimBanach
    DuLimBanach := oracle.DuLimBanach
    mLim := oracle.mLim
    uLim := oracle.uLim
    DuLim := oracle.DuLim
    hMlimPer := oracle.hMlimPer
    hUlimPer := oracle.hUlimPer
    hDuLimPer := oracle.hDuLimPer
    hMlim_memLp := oracle.hMlim_memLp
    hUlim_sob := oracle.hUlim_sob
    hDuLimWeak := oracle.hDuLimWeak
    haeMLim := oracle.haeMLim
    haeULim := oracle.haeULim
    haeDuLim := oracle.haeDuLim
    hMLimBanach_nn := oracle.hMLimBanach_nn
    -- **(P3a5)** Forward the concrete subsequence + the three weak
    -- certs + the abstract cone-cluster, keyed to `oracle.subseqφ`.
    subseqφ := oracle.subseqφ
    hSubseqMono := oracle.hSubseqMono
    weakCertM := oracle.weakCertM
    weakCertU := oracle.weakCertU
    weakCertDu := oracle.weakCertDu
    hWeakConvConeSub := oracle.hWeakConvConeSub }

/-- Sanity-check `example` for the pack4 producer. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (oracle :
      haveI : Fact (1 ≤ ENNReal.ofReal (h.β + 1)) :=
        fact_one_le_ofReal_betaBar h.hβ
      haveI : Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β)) :=
        fact_one_le_ofReal_gammaBar h.hα h.hβ
      CongestionPack4BanachRealisationOracle V H DpH J h seq
                (fun n => 1 / ((n : ℝ) + 1))
                (fun n => by positivity)) :
    CongestionWeakCompactnessUpstreamPack V H DpH J h seq :=
  congestionWeakCompactnessUpstreamPack_of_paperHypotheses V h seq bounds oracle

/-- **Composability witness (anti-sham).** The `hBound` field of the
Banach-realisation oracle (`CongestionPack4BanachRealisationOracle`),
historically the deferred uniform-in-`n` boundedness, is now a genuine
*consequence* of the uniform-in-ε apriori constant: it is exactly the
output of `congestionWeakCompactness_hBound_of_aprioriBounds` fed the
oracle's own `vEps`/`haeM`/`haeU`/`haeDu`. This `example` certifies the
discharge is non-circular (it does not assume `oracle.hBound`). -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    {h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH}
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (εSeq : ℕ → ℝ) (εSeq_pos : ∀ n, 0 < εSeq n)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (oracle :
      CongestionPack4BanachRealisationOracle V H DpH J h seq εSeq εSeq_pos) :
    IsBounded (Set.range oracle.vEps) :=
  congestionWeakCompactness_hBound_of_aprioriBounds seq bounds εSeq εSeq_pos
    oracle.vEps oracle.haeM oracle.haeU oracle.haeDu

/-! ## Phase 3a — `pack5_pairConvOracle` drain: combine backbone

This section provides the **fork-free combine backbone** for the
`pack5_pairConvOracle` drain (task `infra-P7-sigfix-T2-pub-P3a-pack5-pairConv`).

The oracle's per-test-pair statement is a `Tendsto` of `mfgOperatorPair`
at the extracted subsequence to its limit value. Paper line 1604
(`eq:existweaksol.congestion`) deduces it from Hölder's inequality
applied to each of the three integral summands of `mfgOperatorPair`
(HJB, transport, regularisation). The algebraic split
`Solutions.MFG.mfgOperatorPair_split` already exposes those three
summands as separate integrals; this lemma supplies the **final
assembly step**: given convergence of each of the three summand
integrals (the genuine Hölder/weak-convergence content, deferred to the
Phase-3a child tasks), it combines them via `Tendsto.add` into
convergence of the full `mfgOperatorPair`.

The lemma is **fork-free**: it takes the per-summand convergences and
the per-summand integrabilities (at every `n` and at the limit) as
hypotheses, performs no analysis of `H`/`DpH` growth, and reassembles
the pairing purely algebraically. The three component tendstos and
their integrability witnesses are produced by the follow-up child tasks
`...-P3a1` (HJB summand), `...-P3a2` (transport summand), `...-P3a3`
(regularisation summand). -/

/-- **Combine backbone for the `pack5_pairConvOracle` drain.**

Given, for a fixed test pair, the convergence of each of the three
`mfgOperatorPair` summand integrals to its limit value, together with
the per-summand integrability at every index `n` and at the limit,
combine them into convergence of the full `mfgOperatorPair` pairing.

The three summands match `Solutions.MFG.mfgOperatorPair_split`:
* `summand1` — HJB term `∫ (-υ - H(·,Dυ,μ) + V) · η`;
* `summand2` — transport term `∫ μ · (D_pH(·,Dυ,μ) ⬝ Dν)`;
* `summand3` — regularisation term `∫ (μ - 1) · ν`.

This is the algebraic backbone of paper line 1604's Hölder passage to
the weak limit; the per-summand convergences carry the analytic
content. -/
theorem mfgOperatorPair_tendsto_of_summands
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    -- the running (subsequenced) test-pair data
    (Dν : ℕ → Fin d → (Fin d → ℝ) → ℝ)
    (η ν : ℕ → (Fin d → ℝ) → ℝ)
    -- the limit test-pair data
    (DνLim : Fin d → (Fin d → ℝ) → ℝ)
    (ηLim νLim : (Fin d → ℝ) → ℝ)
    -- per-summand integrability at every index `n`
    (h_int1 : ∀ n, MeasureTheory.Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η n x)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (h_int2 : ∀ n, MeasureTheory.Integrable (fun x =>
        μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν n i x)))
        (MeasureTheory.volume.restrict (UnitCube d)))
    (h_int3 : ∀ n, MeasureTheory.Integrable (fun x => (μ x - 1) * ν n x)
        (MeasureTheory.volume.restrict (UnitCube d)))
    -- per-summand integrability at the limit
    (h_int1Lim : MeasureTheory.Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ηLim x)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (h_int2Lim : MeasureTheory.Integrable (fun x =>
        μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => DνLim i x)))
        (MeasureTheory.volume.restrict (UnitCube d)))
    (h_int3Lim : MeasureTheory.Integrable (fun x => (μ x - 1) * νLim x)
        (MeasureTheory.volume.restrict (UnitCube d)))
    -- the three per-summand convergences (analytic content, deferred)
    (h_sum1 : Filter.Tendsto
      (fun n => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η n x)
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ηLim x)))
    (h_sum2 : Filter.Tendsto
      (fun n => ∫ x in UnitCube d,
          μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν n i x)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
          μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => DνLim i x)))))
    (h_sum3 : Filter.Tendsto
      (fun n => ∫ x in UnitCube d, (μ x - 1) * ν n x)
      Filter.atTop
      (𝓝 (∫ x in UnitCube d, (μ x - 1) * νLim x))) :
    Filter.Tendsto
      (fun n => StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ (Dν n) (η n) (ν n))
      Filter.atTop
      (𝓝 (StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ DνLim ηLim νLim)) := by
  -- Rewrite every `mfgOperatorPair` (running and limit) via the
  -- algebraic split into the sum of its three summand integrals.
  have h_split_n : ∀ n,
      StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ (Dν n) (η n) (ν n)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η n x)
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν n i x)))
          + (∫ x in UnitCube d, (μ x - 1) * ν n x) := by
    intro n
    exact StationaryMFG.Solutions.MFG.mfgOperatorPair_split
      (V := V) (H := H) (DpH := DpH)
      Dυ μ υ (Dν n) (η n) (ν n) (h_int1 n) (h_int2 n) (h_int3 n)
  have h_split_lim :
      StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ DνLim ηLim νLim
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ηLim x)
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => DνLim i x)))
          + (∫ x in UnitCube d, (μ x - 1) * νLim x) :=
    StationaryMFG.Solutions.MFG.mfgOperatorPair_split
      (V := V) (H := H) (DpH := DpH)
      Dυ μ υ DνLim ηLim νLim h_int1Lim h_int2Lim h_int3Lim
  -- Combine the three component limits via `Tendsto.add`.
  have h_combined :
      Filter.Tendsto
        (fun n =>
          (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η n x)
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν n i x)))
          + (∫ x in UnitCube d, (μ x - 1) * ν n x))
        Filter.atTop
        (𝓝 ((∫ x in UnitCube d,
              (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ηLim x)
            + (∫ x in UnitCube d,
                μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => DνLim i x)))
            + (∫ x in UnitCube d, (μ x - 1) * νLim x))) :=
    (h_sum1.add h_sum2).add h_sum3
  -- Transport the combined limit back through the splits.
  have h_funext :
      (fun n =>
        (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η n x)
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν n i x)))
        + (∫ x in UnitCube d, (μ x - 1) * ν n x))
      = (fun n => StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ (Dν n) (η n) (ν n)) := by
    funext n; exact (h_split_n n).symm
  rw [h_funext] at h_combined
  rw [h_split_lim]
  exact h_combined

/-! ## Phase 3a2 — per-summand strong-test-function `MemLpPer` regularity

This section exposes, under stable `Compactness`-layer names, the three
per-summand test-function regularity certificates that the Hölder
pairing of paper line 1604 (`eq:existweaksol.congestion`) needs in order
to feed `mfgOperatorPair_tendsto_of_summands` (the P3a combine backbone)
through the SimplePower template lemmas `limit_passage_summand1/2/3`:

* **HJB summand multiplier** `g_m = −υ − H(·,Dυ,μ) + V ∈ L^{β̄'}_per`
  (consumed by `limit_passage_summand1`);
* **transport summand multiplier** `μ · D_pH(·,Dυ,μ)_i ∈ L^{γ̄'}_per`
  per coordinate (consumed by `limit_passage_summand2`);
* **regularisation summand multiplier** `μ − 1 ∈ L^{γ̄'}_per`
  (consumed by `limit_passage_summand3`).

The substantive analysis for each membership is already discharged in
the congestion well-definedness layer; these wrappers re-export it at the
`Theorems.Congestion` layer where the `pack5_pairConvOracle` drain is
assembled. Specifically:

* HJB: `StationaryMFG.Congestion.aEpsi_congestion_HJB_memLp` (AC1),
  whose two-sided `|H|`-growth input is
  `H_two_sided_congestion_of_hmon`;
* transport: `StationaryMFG.Congestion.mDpH_at_perturbed_memLp_gammaBar'`
  (the δ-truncated `m_δ = max(m, δ)` flux multiplier, the route that
  keeps `D_pH`'s `m > 0` growth bound applicable; the unperturbed `μ`
  multiplier at the weak limit, where `μ` may vanish, is the
  `m = 0`-extension design fork deferred to the child task);
* regularisation: `StationaryMFG.Congestion.mass_memLp_gammaBar'`
  (`μ − 1 ∈ L^{γ̄'}` via `γ̄' ≤ β̄` on the finite cube).

These are the strong-test slots of `weakConvPairing_universal` /
`tendsto_integral_of_weakConvUniversal_strongTest`; the P3a3 rewire
threads them, together with the P3a1 weak certificates, into the
`pack5_pairConvOracle` producer. -/

set_option maxHeartbeats 800000 in
-- The product-space coercions require more elaboration than the default budget.
/-- **Regularisation summand multiplier `μ − 1 ∈ L^{γ̄'}_per` (P3a2).**

`Compactness`-layer re-export of `mass_memLp_gammaBar'`: the
regularisation test multiplier `μ − 1` for `limit_passage_summand3`. For
the weak-limit density `μ ∈ L^{β̄}_per` (`β̄ = β + 1`), `μ − 1` lies in
`L^{γ̄'}_per` (`γ̄ = α(β+1)/β`) via the finite-cube inclusion
`γ̄' ≤ β̄`. -/
theorem congestion_massDefect_memLp_gammaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {μ : (Fin d → ℝ) → ℝ}
    (hμ : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ) :
    MemLpPer (d := d)
      (ENNReal.ofReal ((α * (β + 1) / β) / (α * (β + 1) / β - 1)))
      (fun x => μ x - 1) :=
  StationaryMFG.Congestion.mass_memLp_gammaBar' hα hβ hμ

/-- **Transport summand multiplier `μ · D_pH(·,Dυ,μ)_i ∈ L^{γ̄'}_per`,
per coordinate, at the δ-truncated density (P3a2).**

`Compactness`-layer re-export of `mDpH_at_perturbed_memLp_gammaBar'`:
the transport test multiplier for `limit_passage_summand2`, evaluated at
the truncated density `m_δ = max(μ, δ)` so that the congestion
`D_pH`-growth bound (valid for `m > 0`) applies. For `μ ∈ L^{β̄}_per`,
`μ ≥ 0` a.e., gradient family `Dυ_i ∈ L^{γ̄}_per`, and `δ > 0`, the
flux multiplier `max(μ, δ) · D_pH(·, Dυ, max(μ, δ))_i ∈ L^{γ̄'}_per`.

(The unperturbed multiplier `μ · D_pH(·, Dυ, μ)_i`, where `μ` may vanish
on a positive set, requires the `J = m • D_pH` `m = 0`-extension and is
the deferred design-fork child of this task.) -/
theorem congestion_transport_flux_coord_memLp_gammaBar'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore
        (d := d) H DpH J)
    {μ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ)
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hDυ_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dυ i))
    {δ : ℝ} (hδ : 0 < δ) (i : Fin d) :
    MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (fun x => max (μ x) δ * DpH x (fun j => Dυ j x) (max (μ x) δ) i) :=
  StationaryMFG.Congestion.mDpH_at_perturbed_memLp_gammaBar'
    hcong hμ_mem hμ_nn hDυ_memGamma hδ i

/-- **Transport summand multiplier `μ · D_pH(·,Dυ,μ)_i ∈ L^{γ̄'}_per`,
per coordinate, at the unperturbed weak-limit density (P3a2a).**

Unlike the δ-truncated sibling
`congestion_transport_flux_coord_memLp_gammaBar'`, this evaluates the
flux multiplier at the **raw** weak-limit density `μ`, which may vanish
on a positive-measure set. The congestion `D_pH`-growth bound
`hcong.DpH_upper` is only valid for `m > 0`, so we route through the
paper's `(a:mDpHat0)` flux extension `J = m·D_pH` (`hcong.mDpHat0`,
Remark `rmk:implied-a` claim 2):

* `‖J x (Dυ x) μ_x‖` is dominated by the congestion flux dominator for
  ALL `μ_x ≥ 0` (`mDpH_pointwise_bound_congestion`), so the coordinate
  `J(·,Dυ,μ)_i ∈ L^{γ̄'}_per` via `MemLp.of_le_mul` against
  `congestion_flux_dominator_memLp_gammaBar'_le`;
* on `{μ > 0}`, `J = μ·D_pH` (`mDpHat0.J_of_pos`); on `{μ = 0}` (the
  complement, using `μ ≥ 0` a.e.), `μ·D_pH = 0 = J` (`J_zero_at_zero`),
  so `μ·D_pH(·,Dυ,μ)_i =ᵐ J(·,Dυ,μ)_i`;
* `MemLpPer.congr_ae_unitCube` transports the membership back to the raw
  product multiplier `μ · D_pH(·,Dυ,μ)_i`.

This is the multiplier fed to `limit_passage_summand2` at the
unperturbed limit; it discharges the last summand-regularity piece for
the P3a3 pack5 `pairConv` rewire. -/
theorem congestion_transport_flux_coord_memLp_gammaBar'_atLimit
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : StationaryMFG.Hamiltonian.HypothesisCongestionGrowth
        (d := d) H DpH J)
    {μ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ)
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hDυ_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dυ i))
    (i : Fin d) :
    MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  -- Abbreviation for the gradient family evaluated at `x`.
  set p : (Fin d → ℝ) → (Fin d → ℝ) := fun x => (fun j => Dυ j x) with hpdef
  have hμ_nn' : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] μ := hμ_nn
  -- The flux dominator membership at `m = μ`, `Du = Dυ`, `K = C`.
  have hflux_dom := StationaryMFG.Hamiltonian.congestion_flux_dominator_memLp_gammaBar'_le
    (d := d) (α := α) (β := β) (τ := τ) (K := hcong.C)
    hα hβ hτ_nn hτ_le (m := μ) (Du := fun j x => Dυ j x)
    (by rw [hβdef]; exact hμ_mem) hμ_nn'
    (fun j => by rw [hαdef, hβdef]; exact hDυ_memGamma j)
  -- AE-strong-measurability of the coordinate `x ↦ J(x, p x, μ x)_i`.
  have hp_aem : AEMeasurable p (volume.restrict (UnitCube d)) := by
    rw [hpdef, aemeasurable_pi_iff]; intro j
    exact aestronglyMeasurable_iff_aemeasurable.mp
      (hDυ_memGamma j).aestronglyMeasurable
  have hμ_aem : AEMeasurable μ (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hμ_mem.aestronglyMeasurable
  have hJvec_aem : AEMeasurable (fun x => J x (p x) (μ x))
      (volume.restrict (UnitCube d)) :=
    hcong.mDpHat0.aemeasurable_J_comp hp_aem hμ_aem
  have hJi_aem : AEMeasurable (fun x => J x (p x) (μ x) i)
      (volume.restrict (UnitCube d)) :=
    (measurable_pi_apply i).comp_aemeasurable hJvec_aem
  have hJi_meas : AEStronglyMeasurable (fun x => J x (p x) (μ x) i)
      (volume.restrict (UnitCube d)) := hJi_aem.aestronglyMeasurable
  -- Pointwise domination `|J(·)_i| ≤ flux dominator`, valid for all μ ≥ 0.
  have hJbnd := StationaryMFG.Hamiltonian.mDpH_pointwise_bound_congestion hcong.toCongestionGrowthCore p
  have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖J x (p x) (μ x) i‖
        ≤ hcong.C * (1 + μ x ^ (1 - τ))
              * ‖fun j => Dυ j x‖ ^ (α * (1 + τ / β) - 1)
            + hcong.C * (μ x ^ (β + 1 - β / α) + 1) := by
    filter_upwards [hμ_nn, hJbnd] with x hxnn hxJ
    have hCb := hxJ (μ x) hxnn
    have hpi_le : ‖J x (p x) (μ x) i‖ ≤ ‖J x (p x) (μ x)‖ := by
      have := norm_le_pi_norm (J x (p x) (μ x)) i
      simpa using this
    rw [hαdef, hβdef, hτdef]
    exact le_trans hpi_le hCb
  -- `J(·)_i ∈ L^{γ̄'}_per` via `MemLp.of_le_mul` against the dominator.
  have hJi_mem : MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1)))
      (fun x => J x (p x) (μ x) i) := by
    apply Periodic.MemLp.toMemLpPer
    apply MemLp.of_le_mul (c := 1) hflux_dom.toMemLp hJi_meas
    filter_upwards [hbound] with x hx
    -- The dominator is `≥ 0` because it bounds the (nonneg) norm `‖J·‖`.
    have hdom_nn : 0 ≤ hcong.C * (1 + μ x ^ (1 - τ))
              * ‖fun j => Dυ j x‖ ^ (α * (1 + τ / β) - 1)
            + hcong.C * (μ x ^ (β + 1 - β / α) + 1) :=
      le_trans (norm_nonneg _) hx
    rw [one_mul, Real.norm_eq_abs (J x (p x) (μ x) i),
      Real.norm_eq_abs (hcong.C * (1 + μ x ^ (1 - τ))
              * ‖fun j => Dυ j x‖ ^ (α * (1 + τ / β) - 1)
            + hcong.C * (μ x ^ (β + 1 - β / α) + 1)),
      abs_of_nonneg hdom_nn]
    rw [Real.norm_eq_abs] at hx
    exact hx
  -- `μ·D_pH(·,Dυ,μ)_i =ᵐ J(·,Dυ,μ)_i`: pos via `J_of_pos`, zero via
  -- `J_zero_at_zero` + `μ = 0`.
  have hae_eq : (fun x => J x (p x) (μ x) i)
      =ᵐ[Measure.restrict volume (UnitCube d)]
      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) := by
    filter_upwards [hμ_nn, hcong.mDpHat0.J_zero_at_zero] with x hxnn hxz
    rcases lt_or_eq_of_le hxnn with hpos | hzero
    · have hJp := hcong.mDpHat0.J_of_pos x (p x) (μ x) hpos
      rw [hJp, Pi.smul_apply, smul_eq_mul]
    · -- `μ x = 0`: LHS `= J x (p x) 0 _i = 0`, RHS `= 0 * _ = 0`.
      have hμ0 : μ x = 0 := hzero.symm
      rw [hμ0, zero_mul, hxz (p x), Pi.zero_apply]
  -- Transport the membership across the a.e. equality.
  have hfinal : MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1)))
      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) :=
    hJi_mem.congr_ae_unitCube hae_eq
  rw [hαdef, hβdef]; exact hfinal

/-! ## Phase 3a3 — `pack5_pairConvOracle` producer (fork-free combine)

This section assembles the **per-test-pair `mfgOperatorPair`
convergence** that is the content of `pack5_pairConvOracle` (paper line
1604, `eq:existweaksol.congestion`, "combined with Hölder's
inequality"). It is the design-fork-free first piece of the P3a3
public-signature drain.

The producer `congestionPairConv_combine` threads:
* the three **component weak certificates** (P3a1 outputs:
  `m_n ⇀ m`, `u_n ⇀ u`, `Du_n i ⇀ Du i` against the strong tests);
* the three **multiplier `MemLpPer` regularities** (P3a2 outputs:
  the HJB multiplier `g = −υ − H(·,Dυ,μ) + V ∈ L^{β̄'}_per`, the
  per-coordinate transport flux `μ · D_pH(·,Dυ,μ)_i ∈ L^{γ̄'}_per`,
  and the mass-defect multiplier `μ − 1 ∈ L^{γ̄'}_per`);
* the per-`k` and limit **`Lᵖ` regularities** of the running and
  limit data,

into convergence of the full `mfgOperatorPair` pairing, via the local
combine backbone `mfgOperatorPair_tendsto_of_summands`. Each of the
three summand convergences is re-derived from its weak certificate and
multiplier regularity using
`tendsto_integral_of_weakConvUniversal_strongTest` (the bare-function
weak-pairing tendsto), since the SimplePower template lemmas
`limit_passage_summand1/2/3` live in `Banach.LimitPassage`, which is
NOT in this module's import tree (the same reason the P3a combine
backbone was re-derived locally here).

The lemma takes the limit data `m`, `u`, `Du` and the running data
`m_n`, `u_n`, `Du_n` as explicit functions, plus the test data
`μ`, `υ`, `Dυ`: it is **independent of how the weak limit was
extracted** (no `lim`/`blim` dependency), so it composes with either
the `pack4`/`lim` Phase-4 path or a freshly-built
`CongestionBanachLimitResult`. Reconciling those two extraction paths
(matching the subsequence and the limit reps) is the deferred design
fork of the Main.lean rewire child task. -/

/-- **`pack5_pairConvOracle` content (fork-free combine, P3a3).**

For a fixed test pair `(μ, υ, Dυ)` and running/limit data, given the
three component weak certificates, the three multiplier `MemLpPer`
regularities, and the per-`k`/limit `Lᵖ` regularities of the data,
produce convergence of `mfgOperatorPair` at the running difference
test pair to its value at the limit difference test pair.

This is the analytic content of paper line 1604's Hölder passage to
the weak limit, assembled summand-by-summand and combined via
`mfgOperatorPair_tendsto_of_summands`. -/
theorem congestionPairConv_combine
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    (hpqγ : γBar.HolderConjugate γBar')
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    -- running (subsequenced) data
    (m_n u_n : ℕ → (Fin d → ℝ) → ℝ)
    (Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ)
    -- limit data
    (m u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    -- per-`k` Lᵖ regularity
    (hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar) (m_n k))
    (hu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (u_n k))
    (hDu_n : ∀ k i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du_n k i))
    -- limit Lᵖ regularity
    (hm : MemLpPer (d := d) (ENNReal.ofReal βBar) m)
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    -- test data Lᵖ regularity
    (hμ : MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hυ : MemLpPer (d := d) (ENNReal.ofReal γBar) υ)
    (hDυ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
    -- multiplier regularities (P3a2)
    (hg : MemLpPer (d := d) (ENNReal.ofReal βBar')
            (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
    (hflux : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
    (hmass : MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
    -- component weak certificates (P3a1)
    (h_weak_m :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqβ m_n m)
    (h_weak_u :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ u_n u)
    (h_weak_Du : ∀ i,
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ (fun k => Du_n k i) (Du i)) :
    Filter.Tendsto
      (fun k => StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - Du_n k i x)
          (fun x => μ x - m_n k x) (fun x => υ x - u_n k x))
      Filter.atTop
      (𝓝 (StationaryMFG.Solutions.MFG.mfgOperatorPair
          (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - Du i x)
          (fun x => μ x - m x) (fun x => υ x - u x))) := by
  classical
  have hpqβ' : βBar'.HolderConjugate βBar := hpqβ.symm
  have hpqγ' : γBar'.HolderConjugate γBar := hpqγ.symm
  -- Abbreviations for the three multipliers.
  set g : (Fin d → ℝ) → ℝ :=
    fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x with hgdef
  set fluxV : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x => DpH x (fun j => Dυ j x) (μ x) with hfluxVdef
  -- ===== Summand 1 (HJB) convergence: `∫ g·(μ − m_n) → ∫ g·(μ − m)`. =====
  -- Weak pairing gives `∫ m_n·g → ∫ m·g`; rewrite to `∫ g·m_n`.
  have hpair_m :
      Filter.Tendsto (fun k => ∫ x in UnitCube d, g x * m_n k x)
        Filter.atTop (𝓝 (∫ x in UnitCube d, g x * m x)) := by
    have h0 :=
      StationaryMFG.Theorems.SimplePower.Banach.tendsto_integral_of_weakConvUniversal_strongTest
        hpqβ hm_n hm hg h_weak_m
    have e1 : (fun k => ∫ x in UnitCube d, m_n k x * g x)
            = (fun k => ∫ x in UnitCube d, g x * m_n k x) := by
      funext k; refine integral_congr_ae ?_
      filter_upwards with x; ring
    have e2 : (∫ x in UnitCube d, m x * g x)
            = (∫ x in UnitCube d, g x * m x) := by
      refine integral_congr_ae ?_; filter_upwards with x; ring
    rw [e1, e2] at h0; exact h0
  have hsum1 :
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d, g x * (μ x - m_n k x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, g x * (μ x - m x))) := by
    have hIgμ : IntegrableOn (fun x => g x * μ x) (UnitCube d) :=
      MemLpPer.integrable_mul hpqβ' hg hμ
    have hIgm_n : ∀ k, IntegrableOn (fun x => g x * m_n k x) (UnitCube d) :=
      fun k => MemLpPer.integrable_mul hpqβ' hg (hm_n k)
    have hIgm : IntegrableOn (fun x => g x * m x) (UnitCube d) :=
      MemLpPer.integrable_mul hpqβ' hg hm
    have hconst :
        Filter.Tendsto (fun _ : ℕ => ∫ x in UnitCube d, g x * μ x)
          Filter.atTop (𝓝 (∫ x in UnitCube d, g x * μ x)) :=
      tendsto_const_nhds
    have hdiff := hconst.sub hpair_m
    have efun : (fun k => (∫ x in UnitCube d, g x * μ x)
                          - ∫ x in UnitCube d, g x * m_n k x)
              = (fun k => ∫ x in UnitCube d, g x * (μ x - m_n k x)) := by
      funext k
      rw [← MeasureTheory.integral_sub hIgμ (hIgm_n k)]
      refine integral_congr_ae ?_; filter_upwards with x; ring
    have elim : (∫ x in UnitCube d, g x * μ x)
                  - ∫ x in UnitCube d, g x * m x
                = ∫ x in UnitCube d, g x * (μ x - m x) := by
      rw [← MeasureTheory.integral_sub hIgμ hIgm]
      refine integral_congr_ae ?_; filter_upwards with x; ring
    rw [efun, elim] at hdiff; exact hdiff
  -- ===== Summand 3 (regularisation) convergence. =====
  have hpair_u :
      Filter.Tendsto (fun k => ∫ x in UnitCube d, (μ x - 1) * u_n k x)
        Filter.atTop (𝓝 (∫ x in UnitCube d, (μ x - 1) * u x)) := by
    have h0 :=
      StationaryMFG.Theorems.SimplePower.Banach.tendsto_integral_of_weakConvUniversal_strongTest
        hpqγ hu_n hu hmass h_weak_u
    have e1 : (fun k => ∫ x in UnitCube d, u_n k x * (μ x - 1))
            = (fun k => ∫ x in UnitCube d, (μ x - 1) * u_n k x) := by
      funext k; refine integral_congr_ae ?_
      filter_upwards with x; ring
    have e2 : (∫ x in UnitCube d, u x * (μ x - 1))
            = (∫ x in UnitCube d, (μ x - 1) * u x) := by
      refine integral_congr_ae ?_; filter_upwards with x; ring
    rw [e1, e2] at h0; exact h0
  have hsum3 :
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d, (μ x - 1) * (υ x - u_n k x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (μ x - 1) * (υ x - u x))) := by
    have hImυ : IntegrableOn (fun x => (μ x - 1) * υ x) (UnitCube d) :=
      MemLpPer.integrable_mul hpqγ' hmass hυ
    have hImu_n : ∀ k, IntegrableOn (fun x => (μ x - 1) * u_n k x)
        (UnitCube d) := fun k => MemLpPer.integrable_mul hpqγ' hmass (hu_n k)
    have hImu : IntegrableOn (fun x => (μ x - 1) * u x) (UnitCube d) :=
      MemLpPer.integrable_mul hpqγ' hmass hu
    have hconst :
        Filter.Tendsto (fun _ : ℕ => ∫ x in UnitCube d, (μ x - 1) * υ x)
          Filter.atTop (𝓝 (∫ x in UnitCube d, (μ x - 1) * υ x)) :=
      tendsto_const_nhds
    have hdiff := hconst.sub hpair_u
    have efun : (fun k => (∫ x in UnitCube d, (μ x - 1) * υ x)
                          - ∫ x in UnitCube d, (μ x - 1) * u_n k x)
              = (fun k => ∫ x in UnitCube d, (μ x - 1) * (υ x - u_n k x)) := by
      funext k
      rw [← MeasureTheory.integral_sub hImυ (hImu_n k)]
      refine integral_congr_ae ?_; filter_upwards with x; ring
    have elim : (∫ x in UnitCube d, (μ x - 1) * υ x)
                  - ∫ x in UnitCube d, (μ x - 1) * u x
                = ∫ x in UnitCube d, (μ x - 1) * (υ x - u x) := by
      rw [← MeasureTheory.integral_sub hImυ hImu]
      refine integral_congr_ae ?_; filter_upwards with x; ring
    rw [efun, elim] at hdiff; exact hdiff
  -- ===== Summand 2 (transport) convergence, per coordinate then summed. =====
  have hsum2_coord : ∀ i,
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d,
          (μ x * fluxV x i) * (Dυ i x - Du_n k i x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (μ x * fluxV x i) * (Dυ i x - Du i x))) := by
    intro i
    have hpair_Du :
        Filter.Tendsto (fun k => ∫ x in UnitCube d, (μ x * fluxV x i) * Du_n k i x)
          Filter.atTop (𝓝 (∫ x in UnitCube d, (μ x * fluxV x i) * Du i x)) := by
      have h0 :=
        StationaryMFG.Theorems.SimplePower.Banach.tendsto_integral_of_weakConvUniversal_strongTest
          hpqγ (fun k => hDu_n k i) (hDu i) (hflux i) (h_weak_Du i)
      have e1 : (fun k => ∫ x in UnitCube d,
                  Du_n k i x * (μ x * fluxV x i))
              = (fun k => ∫ x in UnitCube d,
                  (μ x * fluxV x i) * Du_n k i x) := by
        funext k; refine integral_congr_ae ?_; filter_upwards with x; ring
      have e2 : (∫ x in UnitCube d, Du i x * (μ x * fluxV x i))
              = (∫ x in UnitCube d, (μ x * fluxV x i) * Du i x) := by
        refine integral_congr_ae ?_; filter_upwards with x; ring
      rw [e1, e2] at h0; exact h0
    have hIfDυ : IntegrableOn (fun x => (μ x * fluxV x i) * Dυ i x)
        (UnitCube d) := MemLpPer.integrable_mul hpqγ' (hflux i) (hDυ i)
    have hIfDu_n : ∀ k, IntegrableOn (fun x => (μ x * fluxV x i) * Du_n k i x)
        (UnitCube d) := fun k => MemLpPer.integrable_mul hpqγ' (hflux i) (hDu_n k i)
    have hIfDu : IntegrableOn (fun x => (μ x * fluxV x i) * Du i x)
        (UnitCube d) := MemLpPer.integrable_mul hpqγ' (hflux i) (hDu i)
    have hconst :
        Filter.Tendsto (fun _ : ℕ => ∫ x in UnitCube d, (μ x * fluxV x i) * Dυ i x)
          Filter.atTop (𝓝 (∫ x in UnitCube d, (μ x * fluxV x i) * Dυ i x)) :=
      tendsto_const_nhds
    have hdiff := hconst.sub hpair_Du
    have efun : (fun k => (∫ x in UnitCube d, (μ x * fluxV x i) * Dυ i x)
                          - ∫ x in UnitCube d, (μ x * fluxV x i) * Du_n k i x)
              = (fun k => ∫ x in UnitCube d,
                  (μ x * fluxV x i) * (Dυ i x - Du_n k i x)) := by
      funext k
      rw [← MeasureTheory.integral_sub hIfDυ (hIfDu_n k)]
      refine integral_congr_ae ?_; filter_upwards with x; ring
    have elim : (∫ x in UnitCube d, (μ x * fluxV x i) * Dυ i x)
                  - ∫ x in UnitCube d, (μ x * fluxV x i) * Du i x
                = ∫ x in UnitCube d, (μ x * fluxV x i) * (Dυ i x - Du i x) := by
      rw [← MeasureTheory.integral_sub hIfDυ hIfDu]
      refine integral_congr_ae ?_; filter_upwards with x; ring
    rw [efun, elim] at hdiff; exact hdiff
  -- Sum the per-coordinate transport convergences and re-fold the dot product.
  have hsum2 :
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d,
          μ x * (fluxV x ⬝ (fun i => Dυ i x - Du_n k i x)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          μ x * (fluxV x ⬝ (fun i => Dυ i x - Du i x)))) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => hsum2_coord i)
    -- Per-coordinate integrabilities of the summed integrand.
    have hIcoord_n : ∀ k i,
        IntegrableOn (fun x => (μ x * fluxV x i) * (Dυ i x - Du_n k i x))
          (UnitCube d) := by
      intro k i
      have hd : MemLpPer (d := d) (ENNReal.ofReal γBar)
          (fun x => Dυ i x - Du_n k i x) :=
        by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu_n k i).toMemLp)
      exact MemLpPer.integrable_mul hpqγ' (hflux i) hd
    have hIcoord_lim : ∀ i,
        IntegrableOn (fun x => (μ x * fluxV x i) * (Dυ i x - Du i x))
          (UnitCube d) := by
      intro i
      have hd : MemLpPer (d := d) (ENNReal.ofReal γBar)
          (fun x => Dυ i x - Du i x) :=
        by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu i).toMemLp)
      exact MemLpPer.integrable_mul hpqγ' (hflux i) hd
    have eint_n : ∀ k,
        ∫ x in UnitCube d, μ x * (fluxV x ⬝ (fun i => Dυ i x - Du_n k i x))
          = ∑ i : Fin d, ∫ x in UnitCube d,
              (μ x * fluxV x i) * (Dυ i x - Du_n k i x) := by
      intro k
      have hpt : (fun x => μ x * (fluxV x ⬝ (fun i => Dυ i x - Du_n k i x)))
          = (fun x => ∑ i : Fin d, (μ x * fluxV x i) * (Dυ i x - Du_n k i x)) := by
        funext x
        unfold dotProduct
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro i _; ring
      rw [hpt, MeasureTheory.integral_finset_sum _ (fun i _ => hIcoord_n k i)]
    have eint_lim :
        ∫ x in UnitCube d, μ x * (fluxV x ⬝ (fun i => Dυ i x - Du i x))
          = ∑ i : Fin d, ∫ x in UnitCube d,
              (μ x * fluxV x i) * (Dυ i x - Du i x) := by
      have hpt : (fun x => μ x * (fluxV x ⬝ (fun i => Dυ i x - Du i x)))
          = (fun x => ∑ i : Fin d, (μ x * fluxV x i) * (Dυ i x - Du i x)) := by
        funext x
        unfold dotProduct
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro i _; ring
      rw [hpt, MeasureTheory.integral_finset_sum _ (fun i _ => hIcoord_lim i)]
    have efun : (fun k => ∑ i : Fin d, ∫ x in UnitCube d,
                  (μ x * fluxV x i) * (Dυ i x - Du_n k i x))
              = (fun k => ∫ x in UnitCube d,
                  μ x * (fluxV x ⬝ (fun i => Dυ i x - Du_n k i x))) := by
      funext k; exact (eint_n k).symm
    rw [efun, ← eint_lim] at hsum
    exact hsum
  -- ===== Per-summand integrabilities for the backbone (running + limit). =====
  have hmd_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar)
      (fun x => μ x - m_n k x) :=
    fun k => by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hμ.toMemLp (hm_n k).toMemLp)
  have hmd : MemLpPer (d := d) (ENNReal.ofReal βBar) (fun x => μ x - m x) :=
    by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hμ.toMemLp hm.toMemLp)
  have hud_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar)
      (fun x => υ x - u_n k x) :=
    fun k => by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hυ.toMemLp (hu_n k).toMemLp)
  have hud : MemLpPer (d := d) (ENNReal.ofReal γBar) (fun x => υ x - u x) :=
    by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hυ.toMemLp hu.toMemLp)
  have hint1 : ∀ k, MeasureTheory.Integrable (fun x =>
      (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun k => MemLpPer.integrable_mul hpqβ' hg (hmd_n k)
  have hint1Lim : MeasureTheory.Integrable (fun x =>
      (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hpqβ' hg hmd
  have hint3 : ∀ k, MeasureTheory.Integrable
      (fun x => (μ x - 1) * (υ x - u_n k x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun k => MemLpPer.integrable_mul hpqγ' hmass (hud_n k)
  have hint3Lim : MeasureTheory.Integrable
      (fun x => (μ x - 1) * (υ x - u x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hpqγ' hmass hud
  -- Transport integrability via the per-coordinate dot-product split.
  have hint2 : ∀ k, MeasureTheory.Integrable (fun x =>
      μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du_n k i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    have hcoord : ∀ i, MeasureTheory.Integrable
        (fun x => (μ x * fluxV x i) * (Dυ i x - Du_n k i x))
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      intro i
      have hd : MemLpPer (d := d) (ENNReal.ofReal γBar)
          (fun x => Dυ i x - Du_n k i x) :=
        by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu_n k i).toMemLp)
      exact MemLpPer.integrable_mul hpqγ' (hflux i) hd
    have hpt : (fun x => μ x *
          (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du_n k i x)))
        = (fun x => ∑ i : Fin d, (μ x * fluxV x i) * (Dυ i x - Du_n k i x)) := by
      funext x
      unfold dotProduct
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro i _; rw [hfluxVdef]; ring
    rw [hpt]
    exact MeasureTheory.integrable_finset_sum _ (fun i _ => hcoord i)
  have hint2Lim : MeasureTheory.Integrable (fun x =>
      μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have hcoord : ∀ i, MeasureTheory.Integrable
        (fun x => (μ x * fluxV x i) * (Dυ i x - Du i x))
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      intro i
      have hd : MemLpPer (d := d) (ENNReal.ofReal γBar)
          (fun x => Dυ i x - Du i x) :=
        by simpa only [Pi.sub_def] using Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu i).toMemLp)
      exact MemLpPer.integrable_mul hpqγ' (hflux i) hd
    have hpt : (fun x => μ x *
          (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du i x)))
        = (fun x => ∑ i : Fin d, (μ x * fluxV x i) * (Dυ i x - Du i x)) := by
      funext x
      unfold dotProduct
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro i _; rw [hfluxVdef]; ring
    rw [hpt]
    exact MeasureTheory.integrable_finset_sum _ (fun i _ => hcoord i)
  -- ===== Assemble via the local combine backbone. =====
  -- Bring the three summand convergences to the exact backbone shape.
  have hsum1' : Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x))) := by
    have e1 : (fun k => ∫ x in UnitCube d, g x * (μ x - m_n k x))
            = (fun k => ∫ x in UnitCube d,
                (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)) := by
      funext k; rw [hgdef]
    have e2 : (∫ x in UnitCube d, g x * (μ x - m x))
            = (∫ x in UnitCube d,
                (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)) := by
      rw [hgdef]
    rw [e1, e2] at hsum1; exact hsum1
  have hsum2' : Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du_n k i x)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du i x)))) := by
    have e1 : (fun k => ∫ x in UnitCube d,
                μ x * (fluxV x ⬝ (fun i => Dυ i x - Du_n k i x)))
            = (fun k => ∫ x in UnitCube d,
                μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du_n k i x))) := by
      funext k; rw [hfluxVdef]
    have e2 : (∫ x in UnitCube d, μ x * (fluxV x ⬝ (fun i => Dυ i x - Du i x)))
            = (∫ x in UnitCube d,
                μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dυ i x - Du i x))) := by
      rw [hfluxVdef]
    rw [e1, e2] at hsum2; exact hsum2
  exact mfgOperatorPair_tendsto_of_summands
    (V := V) (H := H) (DpH := DpH)
    Dυ μ υ
    (fun k i x => Dυ i x - Du_n k i x)
    (fun k x => μ x - m_n k x) (fun k x => υ x - u_n k x)
    (fun i x => Dυ i x - Du i x)
    (fun x => μ x - m x) (fun x => υ x - u x)
    hint1 hint2 hint3 hint1Lim hint2Lim hint3Lim
    hsum1' hsum2' hsum3

end Congestion
end Theorems
end StationaryMFG
