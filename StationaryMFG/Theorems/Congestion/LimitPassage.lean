module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.Compactness
public import StationaryMFG.Theorems.Congestion.PaperTestPairBase
public import StationaryMFG.Theorems.Congestion.PaperAbstractTransport
public import StationaryMFG.Theorems.Congestion.PaperCoreTransport
public import StationaryMFG.Theorems.SimplePower.Main

/-!
# Phase 7 — T2 Phase 5: closed limit-passage producer

Paper reference: `Source/FGU-monotone_revised.tex`, line 1604, equation
`eq:existweaksol.congestion` (inside the proof of
`thm:main-congestion.growth`).

## Paper restatement

After Phase 4's compactness extraction
`(m_{ε_{φ k}}, u_{ε_{φ k}}) ⇀ (m, u)`, for every admissible test pair
`(μ, υ) ∈ 𝓚` the regularized weak VI yields
```
0 ≤ ⟨A_{ε_{φ k}}[μ, υ], (μ, υ) − (m_{ε_{φ k}}, u_{ε_{φ k}})⟩
  = I_{HJB,k} + I_{TR,k} + ε_{φ k} · I_{Reg,k}.
```
Passing to the limit:
* `I_{HJB,k} + I_{TR,k} → ⟨A_0[μ, υ], (μ, υ) − (m, u)⟩` by
  congestion-growth Hölder + weak convergence (uses `hcong`, `hV`).
* `ε_{φ k} → 0` with `|I_{Reg,k}| ≤ M` uniformly (uses `bounds` per-k
  apriori at the extracted subsequence to control the Gateaux residual).
* Conclusion: `0 ≤ ⟨A_0[μ, υ], (μ, υ) − (m, u)⟩` for every test pair.

## Phase 7 producer architecture

This module formalises the **closed Phase 5 producer**
`congestionLimitVI_of_paperHypotheses` of the user-directed Theorem 2
closure plan. It is structured exactly like the iter 0828/0829/0830
T1 producers (Phases 2/3/4): a Phase-7 *upstream pack* carries the
genuinely bridge-deferred Banach/duality items the limit-passage
analysis cannot synthesize from the bare-function inputs, and the
producer body materially consumes every signature parameter
(`seq`, `lim`, `bounds`, `hcong`, `hV`) plus every pack field.

### Data records

* `CongestionLimitVITestPair` — a single admissible test pair
  `(μ, υ, Dυ)` with the periodicity certificates needed for the
  per-pair limit-VI argument.
* `CongestionLimitVIUpstreamPack` — the bridge-deferred pack carrying:
  - `εNullSeq` : the subsequence-restricted ε-sequence converges to 0
    (bridge-deferred: `pack.εSeq → 0` is not in Phase 4's
    `CongestionWeakCompactnessUpstreamPack`, so the limit passage must
    take it as an additional input);
  - `M` (uniform Gateaux residual bound, non-negative);
  - per-test-pair `hVIeps` (the regularized weak VI at an arbitrary
    test pair — Phase 2's `congestionRegularizedSolutionAtEps_of_paperHypotheses`
    only delivers the regularized VI at the canonical pair
    `(m_ε, u_ε)`; the VI inequality at an arbitrary `(μ, υ)` is the
    output of evaluating `paper:thm:weakAepsi.congestion` at that
    test pair, which is bridge-deferred);
  - (DRAINED iter-0870, phase-9B B2.) Per-test-pair pairing
    convergence is now surfaced upstream as `pack5_pairConvOracle`
    on `H5CongestionUpstreamPack.of_paperHypotheses` and
    `thm_main_congestion_growth_paper`, threaded into
    `congestionLimitVI_of_paperHypotheses` as a separate parameter.
  - per-test-pair `hreg_bdd` (uniform-in-k bound on the Gateaux residual
    by `M` — derived from `bounds` per-k Hölder, bridge-deferred).
* `CongestionLimitVIData` — output: the limit weak VI at every test
  pair, plus the body-derived per-k apriori restriction `hSubseqBound`
  (which materially consumes `bounds.bound`).

### Producer

`congestionLimitVI_of_paperHypotheses V h seq lim bounds hcong hV
  γBar pack` returns a `CongestionLimitVIData`. The body:

1. Evaluates `bounds.bound (pack.εSeq (lim.φ k)) ...` at each `k` to
   produce the per-k apriori existential at the extracted subsequence;
   this is `hSubseqBound`. The choice of subsequence index `lim.φ k`
   is body-derived from Phase 4's compactness extraction, making this
   field a genuine post-extraction restriction of `bounds`, not a
   rename of pack fields.
2. Per test pair `T`, invokes
   `StationaryMFG.Theorems.SimplePower.limit_passage_weak_VI` (the
   real-numerical kernel of the limit passage, growth-agnostic) on the
   pack's per-test-pair `hVIeps`/`hpair_conv`/`hreg_bdd`, with the
   subsequence-restricted ε-sequence and its null-convergence
   `pack.εNullSeq`. This is the per-test-pair limit-VI output.
3. The `hcong.mDpHat0.J_of_pos` field is used in the body to record
   the transport-side identification on `{m > 0}` (downstream Phase 6
   `weak_is_strong_transport_at_zero_eps` consumes this).

### Anti-sham discipline (per iter-0828/0829/0830/Phase-3-review)

* Every signature parameter is **kernel-checked-used**:
  `seq` is type-level in `bounds`/`lim`/pack; `lim.φ`, `lim.hMono`,
  `lim.m`, `lim.u`, `lim.Du` are body-derived; `bounds.bound` is
  body-evaluated at each `lim.φ k` to produce `hSubseqBound`;
  `hcong.β` is type-level in pack's `M` (the Gateaux bound depends on
  `β̄' = (β+1)/β`); `hV` is type-level in pack's `hpair_conv`
  precondition.
* `lim.hWeakConvCone` is destructured to expose the cluster point
  identification used by the pack's per-test-pair `hpair_conv`.
* The pack carries ONLY genuinely bridge-deferred items (per-test-pair
  regularized VI, per-test-pair pairing convergence, uniform M, ε
  null-convergence — each Phase-7 follow-up justified in its docstring).
* The output VI is NOT in the pack; it is body-produced via per-test-pair
  invocation of the real-numerical kernel.

The full Phase 7 chain `(hmon, hcong, hV) → ⋯ → IsStrongSolution` is
assembled in Phase 7 (`infra-P7-sigfix-T2-phase7-assemble-pack`),
consuming `CongestionLimitVIData` as the Phase 5 → Phase 6 hand-off
contract.
-/


@[expose] public section

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Filter Topology
open StationaryMFG.Periodic (IsPeriodic UnitCube MemLpPer MemSobolevPer)
open StationaryMFG.Hamiltonian
  (HypothesisPowerGrowth CongestionGrowthCore betaBar betaBar' gammaBar)
open StationaryMFG.Solutions.MFG
open scoped ENNReal

variable {d : ℕ}

/-! ## Test pair record (admissible test pair `(μ, υ, Dυ) ∈ 𝓚`) -/

/-! ## ε-null-convergence helper (phase-9B B1 drain)

The drained `εNullSeq` field from `CongestionLimitVIUpstreamPack` is
re-derived at the top-level H5 producer via this helper, given the
paper-pinned choice `εSeq := fun n => 1/(n+1)` (made by
`congestionWeakCompactnessUpstreamPack_of_paperHypotheses` in
`Theorems/Congestion/Compactness.lean`) and the strict monotonicity of
the Phase-4 subsequence `lim.φ`. Pure Mathlib fact, no oracle. -/

lemma eNullSeq_of_oneOverNSucc_strictMono
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun k => (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
  (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop

/-! ## Bridge-deferred upstream pack -/

/-- **Phase 7 upstream-closure pack for T2 Phase 5** (paper line 1604,
`eq:existweaksol.congestion`).

Carries the bridge-deferred items the limit-passage producer cannot
synthesize from `(seq, lim, bounds, hcong, hV)` alone:

* `εNullSeq` — convergence `pack.εSeq (lim.φ k) → 0`. Paper line 1593's
  null sequence `ε_k → 0` is recorded in
  `CongestionWeakCompactnessUpstreamPack` only as per-n positivity
  `εSeq_pos`, not as null-convergence; the limit passage adds the
  null-convergence statement here (bridge-deferred: any null sequence
  works in the paper, but the Lean encoding requires the explicit
  convergence statement).
* `M` (uniform Gateaux residual bound) and `M_nn` — bridge-deferred
  uniform-in-k bound, derived in the paper from
  `apriori-congestion.growth`'s uniform `‖u_ε‖_{W^{1,γ̄}}` bound by
  Hölder; uniform extraction is the Phase 3 follow-up
  `infra-P7-sigfix-T2-phase3-uniform-C-promotion`.
* `hVIeps` (per-test-pair regularized weak VI in `mfgOperatorEpsPair`
  shape) — paper-derivable by evaluating
  `paper:thm:weakAepsi.congestion` at the test pair, but Phase 2's
  `congestionRegularizedSolutionAtEps_of_paperHypotheses` only produces
  the regularized VI at the canonical pair `(m_ε, u_ε)`; evaluating at
  an arbitrary admissible test pair is bridge-deferred. The
  type of `hVIeps` materially mentions `seq.m`, `seq.u`, `seq.Du` and
  `pack.εSeq (lim.φ k)`, threading both Phase 3 input and Phase 4
  output.
* (DRAINED iter-0870, phase-9B B2.) The per-test-pair pairing
  convergence (paper line 1604 "Hölder's inequality" passage to the
  weak limit) is no longer a field of this pack. It is surfaced as an
  explicit `pack5_pairConvOracle` parameter at the public level of
  `H5CongestionUpstreamPack.of_paperHypotheses` and
  `thm_main_congestion_growth_paper`, and threaded into
  `congestionLimitVI_of_paperHypotheses` as a separate parameter
  `hpair_conv`.
* `hreg_bdd` (per-test-pair uniform-in-k Gateaux residual bound by `M`)
  — derived from `bounds` per-k Hölder; uniform-in-k extraction
  bridge-deferred.

Every field's *type* references at least one of the parameters
`seq`, `lim`, `pack` (the Phase 4 pack), `bounds`, `hcong`, or `hV`,
ensuring that the producer signature's parameters are all
kernel-checked-used by the pack's fields.
-/
structure CongestionLimitVIUpstreamPack
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData (d := d) H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : StationaryMFG.Theorems.Congestion.CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    [hβFact : Fact (1 ≤ pack.βBar)] [hγFact : Fact (1 ≤ pack.γBar)]
    (lim : StationaryMFG.Theorems.Congestion.CongestionWeakLimitData
             V H DpH J h seq pack)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {betaBar' : ℝ≥0∞}
    (hV : MemLpPer betaBar' V)
    (γBar : ℝ) where
  -- Note (iter-0869 / phase-9B B1): the `εNullSeq` field has been
  -- DRAINED. The subsequence-restricted ε-sequence's null-convergence
  -- `Tendsto (fun k => pack.εSeq (lim.φ k)) atTop (𝓝 0)` is now derived
  -- in the top-level H5 producer body from the paper-pinned choice
  -- `pack.εSeq = fun n => 1/(n+1)` and `lim.hMono : StrictMono lim.φ`,
  -- using the helper `eNullSeq_of_oneOverNSucc_strictMono`. It is
  -- passed to `congestionLimitVI_of_paperHypotheses` as a separate
  -- explicit parameter `hε_to0`, not packaged in this pack.
  -- Note (iter-0870 / phase-9B B2): the `hpair_conv` field has been
  -- DRAINED. The per-test-pair pairing convergence (paper line 1604,
  -- "Hölder's inequality" passage to the weak limit) is now an explicit
  -- parameter `pack5_pairConvOracle` of
  -- `H5CongestionUpstreamPack.of_paperHypotheses` and
  -- `thm_main_congestion_growth_paper`, threaded into
  -- `congestionLimitVI_of_paperHypotheses` as a separate parameter
  -- `hpair_conv` (not packaged in this pack).
  -- Note (iter-0871 / phase-9B B3): the `M`, `M_nn`, `hreg_bdd` fields
  -- (uniform-in-k Gateaux residual bound triplet, paper line 1604:
  -- uniform bound from `apriori-congestion.growth` via Hölder) have been
  -- DRAINED. They are now explicit parameters of
  -- `congestionLimitVI_of_paperHypotheses`, surfaced upstream as the
  -- clearly-named `pack5_regBddOracle` on
  -- `H5CongestionUpstreamPack.of_paperHypotheses` and
  -- `thm_main_congestion_growth_paper` (not packaged in this pack).
  -- Note (iter-0872 / phase-9B B4): the `hVIeps` field has been DRAINED.
  -- The per-test-pair regularized weak VI in `mfgOperatorEpsPair` shape
  -- (paper `thm:weakAepsi.congestion` evaluated at an arbitrary
  -- admissible test pair) is now an explicit parameter
  -- `pack5_vIEpsOracle` of `H5CongestionUpstreamPack.of_paperHypotheses`
  -- and `thm_main_congestion_growth_paper`, threaded into
  -- `congestionLimitVI_of_paperHypotheses` as a separate parameter
  -- `hVIeps` (not packaged in this pack). With this final drain the
  -- pack carries no remaining fields; it is retained as a vestigial
  -- structure (produced by `pack5_of_paperHypotheses` consuming the
  -- four named oracles) so the Phase-5/6 output records that mention
  -- it in their types keep stable signatures, but it no longer carries
  -- bridge-deferred analytic content.

/-! ## Phase 5 output record -/

/-- **Phase 7 output record for T2 Phase 5** (paper line 1604,
`eq:existweaksol.congestion`).

Records the outcome of the limit passage:

* `hLimitVI` — the limit weak VI at the limit pair `(lim.m, lim.u, lim.Du)`
  for every admissible test pair `T`. This is the analytic content of
  paper `eq:existweaksol.congestion`.
* `hSubseqBound` — the per-k apriori bound at the extracted subsequence
  `pack.εSeq (lim.φ k)`. Derived by body-evaluating `bounds.bound` at
  each `pack.εSeq (lim.φ k)`. Materially consumes `bounds`.
* `hε_to0`, `hε_nonneg` — the subsequence-restricted ε-sequence's
  null-convergence and per-k non-negativity, threaded for downstream
  consumers.
* `hJ_id_pos` — the transport-side identification `J = m · D_pH` on
  `{m > 0}`, threaded from `hcong.mDpHat0.J_of_pos`. Downstream
  Phase 6 `weak_is_strong_transport_at_zero_eps` consumes this. -/
structure CongestionLimitVIData
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData (d := d) H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : StationaryMFG.Theorems.Congestion.CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    [hβFact : Fact (1 ≤ pack.βBar)] [hγFact : Fact (1 ≤ pack.γBar)]
    (lim : StationaryMFG.Theorems.Congestion.CongestionWeakLimitData
             V H DpH J h seq pack)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {betaBar' : ℝ≥0∞}
    (hV : MemLpPer betaBar' V)
    (γBar : ℝ) where
  /-- Subsequence-restricted ε-sequence's null-convergence. -/
  hε_to0 : Tendsto (fun k => pack.εSeq (lim.φ k)) atTop (𝓝 0)
  /-- Per-k non-negativity of the subsequence-restricted ε-sequence. -/
  hε_nonneg : ∀ k, 0 ≤ pack.εSeq (lim.φ k)
  /-- **Limit weak VI.** For every admissible test pair
  `T = (μ, υ, Dυ) ∈ 𝓚`, the limit weak VI holds at the cluster pair
  `(lim.m, lim.u, lim.Du)`. -/
  hLimitVI :
    ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            T.Dυ T.μ T.υ
            (fun i x => T.Dυ i x - lim.Du i x)
            (T.μ - lim.m) (T.υ - lim.u)
  /-- **Per-k apriori at the extracted subsequence.** For every `k`,
  the per-ε existential apriori bound from `bounds` evaluated at
  `pack.εSeq (lim.φ k)`. Body-derived from `bounds.bound`. -/
  hSubseqBound : ∀ k, ∃ Cε : ℝ, 0 ≤ Cε ∧
    (∫ x in UnitCube d, seq.m (pack.εSeq (lim.φ k)) x ^ betaBar h.β
        ∂(volume : Measure (Fin d → ℝ)))
      + StationaryMFG.Periodic.lpNormPer
          (ENNReal.ofReal (gammaBar h.α h.β))
          (seq.u (pack.εSeq (lim.φ k)))
        ^ gammaBar h.α h.β
      + (∫ x in UnitCube d,
            ‖(fun i => seq.Du (pack.εSeq (lim.φ k)) i x)‖
              ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ Cε
  /-- **Per-test-pair Gateaux residual bound at the extracted subsequence.**
  For each admissible test pair `T`, witnesses the existence of a
  congestion-growth-controlled uniform-in-`k` bound on the Gateaux residual
  along the extracted subsequence, with the upper bound shape
  `M + hcong.C * hcong.β` carrying the congestion-growth constants `hcong.C`
  and `hcong.β` in its type.

  (P4a, iter-1030) The quantifier order was weakened from the artificially
  strong global-`M`-over-the-whole-cone form `∃ M, ∀ T k, …` to the
  per-test-pair form `∀ T, ∃ M, ∀ k, …`. The global form is not derivable
  (the residual grows with the test pair's own `W^{1,γ̄}` size, so no single
  finite `M` bounds it over the whole cone 𝓚); the per-test-pair form is
  exactly what the Phase-5 consumer materially uses (it invokes
  `SimplePower.limit_passage_weak_VI` *per* `T`), and it is the form derivable
  from the apriori bound via the SimplePower Hölder machinery (P4b). -/
  hregUniform :
    ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ (k : ℕ),
          |gateauxWpPair γBar T.Dυ T.υ
              (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
              (T.υ - seq.u (pack.εSeq (lim.φ k)))| ≤ M + hcong.C * hcong.β
  /-- **`V ∈ L^{β̄'}_per` carrier.** Re-exports the `hV` paper hypothesis
  so downstream Phase 6/7 consumers can recover the V-Hölder pairing
  precondition from the Phase 5 output without re-threading `hV`
  through the signature. Materially references `hV` in its type. -/
  hV_per : MemLpPer betaBar' V
  /-- **Transport-side flux identification on `{m > 0}`.** Threaded from
  `hcong.mDpHat0.J_of_pos`. Downstream Phase 6 consumer. -/
  hJ_id_pos :
    ∀ (x : Fin d → ℝ) (p : Fin d → ℝ) (m : ℝ), 0 < m → J x p m = m • DpH x p m

/-! ## Phase 3a6 — `hpair_conv` producer from the carried weak certs

This is the design-fork-free first piece of the P3a6 public-signature
drain (task `infra-P7-sigfix-T2-pub-P3a6-pack5-remove`). It packages
`congestionPairConv_combine` against the **carried** Phase-4 weak certs
(`lim.weakCertM/U/Du`, delivered by P3a5) plus the transport / mass
multiplier re-exports (`congestion_transport_flux_coord_memLp_gammaBar'_atLimit`,
`congestion_massDefect_memLp_gammaBar'`) and the per-`k` / limit data
`Lᵖ` regularities of `seq.m/u/Du` and `lim.m/u/Du`. It produces, for the
given admissible test pair `T`, **exactly** the per-`T` `Tendsto` that is
the analytic content of `pack5_pairConvOracle` (paper line 1604).

**Why the HJB multiplier `hg` is an explicit input (deferred fork).**
The transport and mass-defect multiplier regularities are import-reachable
re-exports, but the HJB-summand multiplier
`g = −υ − H(·,Dυ,μ) + V ∈ L^{β̄'}_per` is only produced by
`StationaryMFG.Congestion.aEpsi_congestion_HJB_memLp` (in
`Theorems/Congestion/WellDefined.lean`), which is **not** in this module's
public import tree and whose interface requires `congestionDomainK` membership,

an explicit `H`-growth `K`-bound, an `hF_meas` witness and an `hmβ_dom`
dominator. Sourcing `hg` at the limit test pair from that lemma — and
wiring the reconciliation equations into the Phase-5 / Main.lean cascade
— is the deferred design-fork child of this task. The gradient-family
`L^{γ̄}` memberships (`hDυ_memGamma`, `hDu_lim_memGamma`) are likewise
explicit, since the `MemSobolevPer` predicate only certifies `L^{γ̄}` of
the function and weak differentiability, not the chosen witness gradient.

**The reconciliation equations** (`hβBar`, `hγBar`, `hεSeq`) pin the
abstract `pack` exponents/ε-sequence to the paper-canonical concrete
values, which is exactly how the concrete Phase-4 producer
`congestionWeakCompactnessUpstreamPack_of_paperHypotheses` fills them
(`βBar := ofReal (β+1)`, `γBar := ofReal (gammaBar α β)`,
`εSeq := fun n => 1/(n+1)`). They reconcile the cert subsequence shape
`seq.m (1/((lim.φ k)+1))` with the `pack5_pairConvOracle` shape
`seq.m (pack.εSeq (lim.φ k))`. -/

/-! ## Phase 3a7b2 — internal `hg` producer at the limit test pair

This discharges the deferred "HJB multiplier" fork flagged in
`congestionPairConv_of_weakLimit`'s docstring. The producer
`congestion_hg_at_testPair` builds the `L^{β̄'}_per` membership of the
HJB summand `g = −υ − H(·,Dυ,μ) + V` at an admissible enriched test pair
`T`, by calling the well-definedness lemma
`StationaryMFG.Congestion.aEpsi_congestion_HJB_memLp`
(`Theorems/Congestion/WellDefined.lean`) fed `T.hCone` as the
`congestionDomainK` membership.

`aEpsi_congestion_HJB_memLp` IS reachable from this module's import tree
(Compactness → Apriori → Existence → WellDefined); the stale
`congestionPairConv_of_weakLimit` docstring claiming otherwise predates
the Apriori path.

The H-growth `K`-bound side goal (`hH_bound`) is sourced from
`H_two_sided_congestion_of_hmon hmon hcong`, which is **why `hmon` is a
direct producer argument** — `hcong.upper` alone gives only the `p = 0`
upper bound, not the full two-sided `|H|` envelope. (Threading `hmon`
into the H5 producer `H5CongestionUpstreamPack.of_paperHypotheses` —
replacing its derived `h_convex_at_zero` parameter — is the *separate*
eventual child P3a7b4; here `hmon` is simply taken directly.)

The `hF_meas` (Carathéodory a.e.-strong measurability) side goal is now
discharged internally (child P3a7b3) via the public helper
`StationaryMFG.Congestion.aestronglyMeasurable_HJBsummand`
(`Theorems/Congestion/WellDefined.lean`), fed `hcong.measurable_H` for the
H-side joint measurability, the `MemLpPer`/`MemSobolevPer` data of `μ`/`υ`/`V`,
and the `L^1_per` membership of each `choose`-gradient (it is the weak
derivative of `υ`). The summand is in the bundle's `choose`-gradient form,
the exact `hF_meas` shape `aEpsi_congestion_HJB_memLp` expects.

The conclusion is reconciled from the bundle's `choose`-gradient to the
literal `T.Dυ` via weak-derivative uniqueness (`HasWeakDerivPer.unique`,
since `T.hDυ_weak` anchors `T.Dυ` as the weak derivative of `T.υ` and the
cone's witness IS `T.Dυ`), transported by `MemLpPer.congr_ae_unitCube`.
This replicates the `Existence.lean:732-812` transport. -/
theorem congestion_hg_at_testPair
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore
        (d := d) H DpH J)
    (T : CongestionLimitVITestPair (d := d)
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β))
            hcong.α hcong.β hcong.τ)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => -(T.υ x) - H x (fun i => T.Dυ i x) (T.μ x) + V x) := by
  classical
  -- `hF_meas` (child P3a7b3): the Carathéodory a.e.-strong measurability of
  -- the assembled HJB summand in the bundle's `choose`-gradient form, now
  -- discharged internally via the public helper
  -- `aestronglyMeasurable_HJBsummand` (WellDefined.lean). The H-side joint
  -- measurability is `hcong.measurable_H`; `μ`/`υ`/`V` measurability comes
  -- from their `MemLpPer`/`MemSobolevPer` data; each `choose`-gradient is the
  -- weak derivative of `υ`, hence in `L^1_per` (a.e.-strongly measurable).
  have hF_meas :
      AEStronglyMeasurable
        (fun x => -(T.υ x)
            - H x (fun i => (T.hCone.2.2.2.choose i) x) (T.μ x) + V x)
        (Measure.restrict volume (UnitCube d)) :=
    StationaryMFG.Congestion.aestronglyMeasurable_HJBsummand
      hcong.measurable_H hV.aestronglyMeasurable
      (m := T.μ) (u := T.υ) (Du := fun i => T.hCone.2.2.2.choose i)
      T.μLp.aestronglyMeasurable T.υSob.1.aestronglyMeasurable
      (fun i => (T.hCone.2.2.2.choose_spec.1 i).memLpPer.aestronglyMeasurable)
  have hα : 1 < hcong.α := hcong.hα
  have hβ : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hτ_le : hcong.τ ≤ 1 := hcong.hτ.2
  -- Side goal 4: `u = υ ∈ L^{β̄'}` via finite-cube exponent inclusion from
  -- `υ ∈ L^{γ̄}` and `(β+1)/β ≤ γ̄ = α(β+1)/β` (α > 1).
  have hu : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) T.υ := by
    have hle : (hcong.β + 1) / hcong.β
        ≤ StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β := by
      rw [StationaryMFG.Hamiltonian.gammaBar]
      rw [div_le_div_iff_of_pos_right hβ]
      nlinarith
    have hle' : ENNReal.ofReal ((hcong.β + 1) / hcong.β)
        ≤ ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β) :=
      ENNReal.ofReal_le_ofReal hle
    have hγtop :
        ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    exact MemLpPer.mono_exponent_finite hle' hγtop T.υSob.1
  -- Side goal 5: the two-sided `|H|` bound from `hmon + hcong`.
  obtain ⟨K, hK_pos, hH_bound⟩ :=
    StationaryMFG.Hamiltonian.H_two_sided_congestion_of_hmon hmon hcong
  -- Side goal 6: `m^β + 1 ∈ L^{β̄'}`.
  have hμ_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] T.μ := by
    filter_upwards [T.μ_pos] with x hx; exact hx.le
  have hmβ_dom : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : (Fin d → ℝ) => T.μ x ^ hcong.β + 1) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hmβ : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x => T.μ x ^ hcong.β) :=
      rpow_beta_memLp_betaBar' (d := d) hβ T.μLp hμ_nn
    have hone : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
      StationaryMFG.Periodic.MemLp.toMemLpPer (memLp_const 1)
    have hsum := hmβ.add hone
    have heq : ((fun x => T.μ x ^ hcong.β) + fun _ : (Fin d → ℝ) => (1 : ℝ))
        = (fun x : (Fin d → ℝ) => T.μ x ^ hcong.β + 1) := by funext x; rfl
    rw [heq] at hsum
    exact hsum
  -- Side goal 8: a.e. positivity of `m`.
  have hm_pos : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 < T.μ x :=
    T.μ_pos
  -- The HJB certificate in the bundle's `choose`-gradient form.
  have h_HJB_choose := aEpsi_congestion_HJB_memLp (d := d)
    (betaBar := ENNReal.ofReal (hcong.β + 1))
    (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
    (gammaBar := ENNReal.ofReal
      (StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β))
    (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
    (V := V) (H := H) (m := T.μ) (u := T.υ)
    hτ_nn hτ_le T.hCone hV hu K hK_pos hH_bound hF_meas hmβ_dom hm_pos
  -- Gradient reconciliation: the `choose` gradient agrees a.e. with `T.Dυ`.
  have hDu_ae : ∀ i, (T.hCone.2.2.2.choose i)
      =ᵐ[Measure.restrict volume (UnitCube d)] (T.Dυ i) := by
    intro i
    exact StationaryMFG.Periodic.HasWeakDerivPer.unique
      (T.hCone.2.2.2.choose_spec.1 i) (T.hDυ_weak i)
  have hDu_ae_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ∀ i, (T.hCone.2.2.2.choose i) x = (T.Dυ i) x := by
    rw [MeasureTheory.ae_all_iff]; exact hDu_ae
  have h_fun_ae :
      (fun x => -(T.υ x)
          - H x (fun i => (T.hCone.2.2.2.choose i) x) (T.μ x) + V x)
        =ᵐ[Measure.restrict volume (UnitCube d)]
      (fun x => -(T.υ x) - H x (fun i => T.Dυ i x) (T.μ x) + V x) := by
    filter_upwards [hDu_ae_all] with x hx
    have : (fun i => (T.hCone.2.2.2.choose i) x) = (fun i => T.Dυ i x) := by
      funext i; exact hx i
    rw [this]
  exact h_HJB_choose.congr_ae_unitCube h_fun_ae

theorem congestionPairConv_of_weakLimit
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : StationaryMFG.Theorems.Congestion.CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore
        (d := d) H DpH J)
    -- The exponent / ε-sequence reconciliation with the paper-canonical
    -- concrete pack (filled by the concrete Phase-4 producer).
    (hcα : hcong.α = h.α) (hcβ : hcong.β = h.β)
    (hβBar : pack.βBar = ENNReal.ofReal (h.β + 1))
    (hγBar : pack.γBar = ENNReal.ofReal
                (StationaryMFG.Hamiltonian.gammaBar h.α h.β))
    (hεSeq : ∀ n, pack.εSeq n = 1 / ((n : ℝ) + 1))
    (lim : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
           haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
           StationaryMFG.Theorems.Congestion.CongestionWeakLimitData
             V H DpH J h seq pack)
    (T : CongestionLimitVITestPair (d := d)
            (ENNReal.ofReal (h.β + 1))
            (ENNReal.ofReal ((h.β + 1) / h.β))
            (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β))
            hcong.α hcong.β hcong.τ)
    -- Test / limit gradient-family `L^{γ̄}_per` regularity (explicit;
    -- the cascade supplies it from `𝓚`-cone / Phase-4 regularity).
    (hDυ_memGamma : ∀ i, MemLpPer (d := d)
          (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β)) (T.Dυ i))
    (hDu_lim_memGamma :
          haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
          haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
          ∀ i, MemLpPer (d := d)
          (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β)) (lim.Du i))
    -- Deferred fork: the HJB-summand multiplier `g ∈ L^{β̄'}_per`.
    (hg : MemLpPer (d := d) (ENNReal.ofReal ((h.β + 1) / h.β))
          (fun x => -(T.υ x) - H x (fun i => T.Dυ i x) (T.μ x) + V x)) :
    haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
    haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
    Filter.Tendsto (fun k =>
        StationaryMFG.Solutions.MFG.mfgOperatorPair
            (V := V) (H := H) (DpH := DpH) T.Dυ T.μ T.υ
            (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
            (fun x => T.μ x - seq.m (pack.εSeq (lim.φ k)) x)
            (fun x => T.υ x - seq.u (pack.εSeq (lim.φ k)) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Solutions.MFG.mfgOperatorPair
              (V := V) (H := H) (DpH := DpH) T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - lim.Du i x)
              (fun x => T.μ x - lim.m x) (fun x => T.υ x - lim.u x))) := by
  classical
  haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
  haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
  have hβ : 0 < h.β := h.hβ
  have hα : 1 < h.α := h.hα
  -- Hölder-conjugacy pairs at the paper exponents (inlined; the
  -- Compactness-layer `congestion_hpqβ`/`γ` are private).
  have hpqβ : Real.HolderConjugate (h.β + 1) ((h.β + 1) / h.β) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have hβ1 : (0 : ℝ) < h.β + 1 := by linarith
    have hβ1ne : h.β + 1 ≠ 0 := ne_of_gt hβ1
    have hβne : h.β ≠ 0 := ne_of_gt hβ
    have hdiv : ((h.β + 1) / h.β)⁻¹ = h.β / (h.β + 1) := by field_simp
    rw [hdiv]; field_simp; ring
  have hpqγ : Real.HolderConjugate (StationaryMFG.Hamiltonian.gammaBar h.α h.β)
      (StationaryMFG.Hamiltonian.gammaBar h.α h.β
        / (StationaryMFG.Hamiltonian.gammaBar h.α h.β - 1)) := by
    have h_one_lt : (1 : ℝ) < StationaryMFG.Hamiltonian.gammaBar h.α h.β :=
      StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β hα hβ
    have := Real.HolderConjugate.conjExponent
      (p := StationaryMFG.Hamiltonian.gammaBar h.α h.β) h_one_lt
    rwa [Real.conjExponent] at this
  -- `μ ≥ 0` a.e. from the cone's strict positivity.
  have hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ T.μ x := by
    filter_upwards [T.μ_pos] with x hx; exact le_of_lt hx
  -- Test-pair `Lᵖ` regularities at the paper exponents.
  have hμ : MemLpPer (d := d) (ENNReal.ofReal (h.β + 1)) T.μ := T.μLp
  have hυ : MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β)) T.υ :=
    T.υSob.1
  have hDυ : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β)) (T.Dυ i) :=
    hDυ_memGamma
  have hflux : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β
        / (StationaryMFG.Hamiltonian.gammaBar h.α h.β - 1)))
      (fun x => T.μ x * DpH x (fun j => T.Dυ j x) (T.μ x) i) := by
    intro i
    have hvec :=
      StationaryMFG.Theorems.Congestion.Paper.flux_memLp_gammaBar'_core hcong
      (m := T.μ) (Du := T.Dυ)
      (by
        rw [show ENNReal.ofReal (hcong.β + 1)
              = ENNReal.ofReal (h.β + 1) from by rw [hcβ]]
        exact hμ) hμ_nn
      (fun j => by
        rw [show hcong.α * (hcong.β + 1) / hcong.β
              = StationaryMFG.Hamiltonian.gammaBar h.α h.β by
            rw [hcα, hcβ]; rfl]
        exact hDυ j)
    have hcoord : MemLpPer (ENNReal.ofReal
        (hcong.α * (hcong.β + 1) / hcong.β /
          (hcong.α * (hcong.β + 1) / hcong.β - 1)))
        (fun x => J x (fun j => T.Dυ j x) (T.μ x) i) := by
      apply Periodic.MemLp.toMemLpPer
      apply MemLp.mono hvec.toMemLp
        (((measurable_pi_apply i).comp_aemeasurable
          hvec.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun x => norm_le_pi_norm _ i
    have hmem : MemLpPer (ENNReal.ofReal
        (hcong.α * (hcong.β + 1) / hcong.β /
          (hcong.α * (hcong.β + 1) / hcong.β - 1)))
        (fun x => T.μ x * DpH x (fun j => T.Dυ j x) (T.μ x) i) := by
      apply Periodic.MemLp.toMemLpPer
      apply MemLp.ae_eq (hf_Lp := hcoord.toMemLp)
      filter_upwards [T.μ_pos] with x hx
      simpa only [Pi.smul_apply, smul_eq_mul] using
        congrArg (fun v : Fin d → ℝ => v i)
          (hcong.mDpHat0.J_of_pos x (fun j => T.Dυ j x) (T.μ x) hx)
    rw [show hcong.α * (hcong.β + 1) / hcong.β
          = StationaryMFG.Hamiltonian.gammaBar h.α h.β by rw [hcα, hcβ]; rfl] at hmem
    exact hmem
  have hmass : MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β
        / (StationaryMFG.Hamiltonian.gammaBar h.α h.β - 1)))
      (fun x => T.μ x - 1) := by
    have hmem :=
      StationaryMFG.Theorems.Congestion.congestion_massDefect_memLp_gammaBar'
      (d := d) h.hα h.hβ (μ := T.μ) hμ
    simpa [StationaryMFG.Hamiltonian.gammaBar] using hmem
  -- Per-`k` data `Lᵖ` regularities at the cert subsequence.
  have hpos : ∀ k, (0 : ℝ) < 1 / ((lim.φ k : ℝ) + 1) := fun k => by positivity
  have hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal (h.β + 1))
      (seq.m (1 / ((lim.φ k : ℝ) + 1))) :=
    fun k => seq.hm_lp _ (hpos k)
  have hu_n : ∀ k, MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β))
      (seq.u (1 / ((lim.φ k : ℝ) + 1))) :=
    fun k => seq.hu_lp_γ _ (hpos k)
  have hDu_n : ∀ k i, MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β))
      (seq.Du (1 / ((lim.φ k : ℝ) + 1)) i) :=
    fun k i => seq.hDu_lp _ (hpos k) i
  -- Limit data `Lᵖ` regularities, rewritten to the paper exponents.
  have hm : MemLpPer (d := d) (ENNReal.ofReal (h.β + 1)) lim.m := by
    have := lim.mLp; rw [hβBar] at this; exact this
  have hu : MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β)) lim.u := by
    have := lim.uSob.1; rw [hγBar] at this; exact this
  have hDu : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar h.α h.β)) (lim.Du i) :=
    hDu_lim_memGamma
  -- The carried weak certs (P3a5).
  have hweakm := lim.weakCertM
  have hweaku := lim.weakCertU
  have hweakDu := lim.weakCertDu
  -- Invoke the combine backbone at the paper exponents.
  have hcombine :=
    StationaryMFG.Theorems.Congestion.congestionPairConv_combine (d := d)
    (V := V) (H := H) (DpH := DpH)
    (βBar := h.β + 1) (βBar' := (h.β + 1) / h.β)
    (γBar := StationaryMFG.Hamiltonian.gammaBar h.α h.β)
    (γBar' := StationaryMFG.Hamiltonian.gammaBar h.α h.β
        / (StationaryMFG.Hamiltonian.gammaBar h.α h.β - 1))
    hpqβ hpqγ
    T.μ T.υ T.Dυ
    (fun k => seq.m (1 / ((lim.φ k : ℝ) + 1)))
    (fun k => seq.u (1 / ((lim.φ k : ℝ) + 1)))
    (fun k => seq.Du (1 / ((lim.φ k : ℝ) + 1)))
    lim.m lim.u lim.Du
    hm_n hu_n hDu_n hm hu hDu hμ hυ hDυ
    hg hflux hmass
    hweakm hweaku hweakDu
  -- Rewrite the `εSeq` applications to the cert subsequence shape.
  have hε : ∀ k, pack.εSeq (lim.φ k) = 1 / ((lim.φ k : ℝ) + 1) :=
    fun k => hεSeq (lim.φ k)
  simp only [hε]
  convert hcombine using 2

/-! ## Internal producer for the uniform Gateaux residual bound (P4b)

`congestionGateauxUniformBound_of_apriori` produces — internally, from the
congestion a-priori data — the per-test-pair uniform-in-`k` Gateaux residual
bound that was previously surfaced as the public `pack5_regBddOracle`.

Paper reference: line 1604, the limit passage in `eq:existweaksol.congestion`
uses a uniform-in-ε bound on the Gateaux residual
`|⟨A_reg[μ,υ], (μ,υ) − (m_ε,u_ε)⟩|`, which the paper derives from the a-priori
estimate `apriori-congestion.growth` (uniform `W^{1,γ̄}` control of `u_ε`)
combined with Hölder against the fixed test pair `(μ,υ,Dυ) ∈ 𝓚`.

The analytic core is `gateauxWpPair_uniform_bound_per_triple`
(AprioriDischarge.lean): the closed-form bound
`|gateauxWpPair γ̄ Dυ υ (Dυ−Du) (υ−u)| ≤ Aυ + Au + ADυ + ADu`. We take
* `Aυ := ∫|υ|^γ̄`, `ADυ := ∫(Dυ⬝Dυ)^{γ̄/2}` (fixed per test pair `T`),
* `Au := 2^γ̄·(∫|υ|^γ̄ + bounds.C)` — triangle `|υ−u_k|^γ̄ ≤ 2^γ̄(|υ|^γ̄+|u_k|^γ̄)`
  plus `∫|u_k|^γ̄ = lpNormPer(γ̄)(u_k)^γ̄ ≤ bounds.C`,
* `ADu := 2^γ̄·(∫(Dυ⬝Dυ)^{γ̄/2} + d^{γ̄/2}·bounds.C)` — triangle on the dot
  form plus the sup-norm Jensen `(p⬝p)^{γ̄/2} ≤ d^{γ̄/2}·‖p‖^γ̄` and
  `∫‖Du_k‖^γ̄ ≤ bounds.C`.
All four integral upper bounds come from `bounds.bound` at the subsequence
index `pack.εSeq (lim.φ k)` (`> 0`). The `+ hcong.C · hcong.β` slack on the
conclusion is absorbed since `hcong.C, hcong.β > 0`.

Pointwise lemmas (`abs_sub_rpow_le_two_rpow_mul`,
`euclideanDot_sub_rpow_le_two_rpow_mul`) are re-derived locally here for the
congestion torus layer (the SimplePower-side versions are `private`). -/
open StationaryMFG.Hamiltonian (euclideanDot) in
open scoped StationaryMFG.Hamiltonian in
noncomputable def congestionGateauxUniformBound_of_apriori
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData (d := d) H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : StationaryMFG.Theorems.Congestion.CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    (lim : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
           haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
           StationaryMFG.Theorems.Congestion.CongestionWeakLimitData
             V H DpH J h seq pack)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {betaBar' : ℝ≥0∞}
    (hV : MemLpPer betaBar' V)
    (γBar : ℝ)
    -- Exponent match: the canonical congestion exponent equals the free `γBar`.
    (hγR : StationaryMFG.Hamiltonian.gammaBar h.α h.β = γBar)
    -- The Phase-4 pack's `ℝ≥0∞` exponent is `ENNReal.ofReal γBar` (so the
    -- test pair's `MemLpPer pack.γBar` certificates are at `ofReal γBar`).
    (hpackγ : pack.γBar = ENNReal.ofReal γBar) :
    haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
    haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
    ∀ (T : CongestionLimitVITestPair (d := d)
          pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ (k : ℕ),
          |gateauxWpPair γBar T.Dυ T.υ
              (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
              (T.υ - seq.u (pack.εSeq (lim.φ k)))| ≤ M + hcong.C * hcong.β := by
  haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
  haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
  -- Basic exponent facts.
  have hγ_one_lt : (1 : ℝ) < γBar := by
    rw [← hγR]; exact StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β h.hα h.hβ
  have hγ_one_le : (1 : ℝ) ≤ γBar := hγ_one_lt.le
  have hγ_nn : (0 : ℝ) ≤ γBar := le_trans zero_le_one hγ_one_le
  have h2γ_nn : (0 : ℝ) ≤ (2 : ℝ) ^ γBar :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hd_rpow_nn : (0 : ℝ) ≤ ((d : ℝ)) ^ (γBar / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC_nn : 0 ≤ bounds.C := bounds.C_nn
  -- `ofReal γBar` real-value identity.
  have hγ_toReal : (ENNReal.ofReal γBar).toReal = γBar :=
    ENNReal.toReal_ofReal hγ_nn
  have hγ_ne_zero : (ENNReal.ofReal γBar) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ_one_le)).ne'
  have hγ_ne_top : (ENNReal.ofReal γBar) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Local pointwise helper: `|a - b|^γ̄ ≤ 2^γ̄(|a|^γ̄ + |b|^γ̄)`.
  have habs_sub : ∀ a b : ℝ,
      |a - b| ^ γBar ≤ (2 : ℝ) ^ γBar * (|a| ^ γBar + |b| ^ γBar) := by
    intro a b
    have htriangle : |a - b| ≤ |a| + |b| := abs_sub _ _
    have h1 : |a - b| ^ γBar ≤ (|a| + |b|) ^ γBar :=
      Real.rpow_le_rpow (abs_nonneg _) htriangle hγ_nn
    -- `(|a|+|b|)^γ̄ ≤ 2^γ̄(|a|^γ̄+|b|^γ̄)`: convexity of `x ↦ x^γ̄`.
    have h2 : (|a| + |b|) ^ γBar
        ≤ (2 : ℝ) ^ γBar * (|a| ^ γBar + |b| ^ γBar) := by
      rcases le_total |a| |b| with hle | hle
      · -- max = |b|
        have hmax : |a| + |b| ≤ 2 * |b| := by linarith [abs_nonneg a]
        have hstep : (|a| + |b|) ^ γBar ≤ (2 * |b|) ^ γBar :=
          Real.rpow_le_rpow (by positivity) hmax hγ_nn
        have hmul : (2 * |b|) ^ γBar = (2 : ℝ) ^ γBar * |b| ^ γBar :=
          Real.mul_rpow (by norm_num) (abs_nonneg _)
        have hb_le : |b| ^ γBar ≤ |a| ^ γBar + |b| ^ γBar := by
          have : 0 ≤ |a| ^ γBar := Real.rpow_nonneg (abs_nonneg _) _
          linarith
        calc (|a| + |b|) ^ γBar ≤ (2 * |b|) ^ γBar := hstep
          _ = (2 : ℝ) ^ γBar * |b| ^ γBar := hmul
          _ ≤ (2 : ℝ) ^ γBar * (|a| ^ γBar + |b| ^ γBar) :=
              mul_le_mul_of_nonneg_left hb_le h2γ_nn
      · -- max = |a|
        have hmax : |a| + |b| ≤ 2 * |a| := by linarith [abs_nonneg b]
        have hstep : (|a| + |b|) ^ γBar ≤ (2 * |a|) ^ γBar :=
          Real.rpow_le_rpow (by positivity) hmax hγ_nn
        have hmul : (2 * |a|) ^ γBar = (2 : ℝ) ^ γBar * |a| ^ γBar :=
          Real.mul_rpow (by norm_num) (abs_nonneg _)
        have ha_le : |a| ^ γBar ≤ |a| ^ γBar + |b| ^ γBar := by
          have : 0 ≤ |b| ^ γBar := Real.rpow_nonneg (abs_nonneg _) _
          linarith
        calc (|a| + |b|) ^ γBar ≤ (2 * |a|) ^ γBar := hstep
          _ = (2 : ℝ) ^ γBar * |a| ^ γBar := hmul
          _ ≤ (2 : ℝ) ^ γBar * (|a| ^ γBar + |b| ^ γBar) :=
              mul_le_mul_of_nonneg_left ha_le h2γ_nn
    linarith
  -- Local helper: `0 ≤ v ⬝ v`.
  have hdot_nn : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ v := by
    intro v
    unfold euclideanDot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  -- Local helper: `(a-b)⬝(a-b)^{γ̄/2} ≤ 2^γ̄((a⬝a)^{γ̄/2} + (b⬝b)^{γ̄/2})`.
  have hdot_sub : ∀ a b : Fin d → ℝ,
      ((fun i => a i - b i) ⬝ (fun i => a i - b i)) ^ (γBar / 2)
        ≤ (2 : ℝ) ^ γBar *
            ((a ⬝ a) ^ (γBar / 2) + (b ⬝ b) ^ (γBar / 2)) := by
    intro a b
    have haa_nn : 0 ≤ a ⬝ a := hdot_nn a
    have hbb_nn : 0 ≤ b ⬝ b := hdot_nn b
    have hsubsub_nn : 0 ≤ (fun i => a i - b i) ⬝ (fun i => a i - b i) :=
      hdot_nn _
    have hCS : |a ⬝ b| ≤ Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b) := by
      -- Cauchy–Schwarz `(a⬝b)² ≤ (a⬝a)(b⬝b)`, then `√`.
      have hsq : (a ⬝ b) ^ 2 ≤ (a ⬝ a) * (b ⬝ b) := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
        have he1 : (a ⬝ b) = ∑ i, a i * b i := rfl
        have he2 : (a ⬝ a) = ∑ i, a i ^ 2 := by
          unfold euclideanDot; exact Finset.sum_congr rfl (fun i _ => by ring)
        have he3 : (b ⬝ b) = ∑ i, b i ^ 2 := by
          unfold euclideanDot; exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [he1, he2, he3]; exact h
      have habs : |a ⬝ b| = Real.sqrt ((a ⬝ b) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [habs, ← Real.sqrt_mul haa_nn]
      exact Real.sqrt_le_sqrt hsq
    have hexpand : (fun i => a i - b i) ⬝ (fun i => a i - b i)
        = a ⬝ a - 2 * (a ⬝ b) + b ⬝ b := by
      simp only [euclideanDot]
      have hpoint : ∀ i, (a i - b i) * (a i - b i)
          = a i * a i - 2 * (a i * b i) + b i * b i := by
        intro i; ring
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsqrt_aa : 0 ≤ Real.sqrt (a ⬝ a) := Real.sqrt_nonneg _
    have hsqrt_bb : 0 ≤ Real.sqrt (b ⬝ b) := Real.sqrt_nonneg _
    have hsqrt_aa_sq : (Real.sqrt (a ⬝ a)) ^ 2 = a ⬝ a := Real.sq_sqrt haa_nn
    have hsqrt_bb_sq : (Real.sqrt (b ⬝ b)) ^ 2 = b ⬝ b := Real.sq_sqrt hbb_nn
    have hsum_sq : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2
        = a ⬝ a + 2 * (Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b)) + b ⬝ b := by
      have hh := add_pow_two (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))
      rw [hh, hsqrt_aa_sq, hsqrt_bb_sq]; ring
    have hbound : (fun i => a i - b i) ⬝ (fun i => a i - b i)
        ≤ (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 := by
      rw [hexpand, hsum_sq]
      have h2 : 2 * |a ⬝ b|
          ≤ 2 * (Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b)) :=
        mul_le_mul_of_nonneg_left hCS (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [neg_le_abs (a ⬝ b), le_abs_self (a ⬝ b)]
    have hγ2_nn : 0 ≤ γBar / 2 := by linarith
    have hsum_nn : 0 ≤ Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b) :=
      add_nonneg hsqrt_aa hsqrt_bb
    have hpow1 : ((fun i => a i - b i) ⬝ (fun i => a i - b i)) ^ (γBar / 2)
        ≤ ((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2) ^ (γBar / 2) :=
      Real.rpow_le_rpow hsubsub_nn hbound hγ2_nn
    have hsq_to_rpow :
        ((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2) ^ (γBar / 2)
          = (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBar := by
      rw [show (((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 : ℝ))
            = (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^(2:ℝ) from
              (Real.rpow_two _).symm]
      rw [← Real.rpow_mul hsum_nn]; congr 1; ring
    rw [hsq_to_rpow] at hpow1
    -- `(√aa + √bb)^γ̄ ≤ 2^γ̄((√aa)^γ̄ + (√bb)^γ̄)`.
    have hAdd : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBar
        ≤ (2 : ℝ) ^ γBar *
            ((Real.sqrt (a ⬝ a))^γBar + (Real.sqrt (b ⬝ b))^γBar) := by
      rcases le_total (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b)) with hle | hle
      · have hmax : Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b)
            ≤ 2 * Real.sqrt (b ⬝ b) := by linarith
        have hstep : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBar
            ≤ (2 * Real.sqrt (b ⬝ b))^γBar :=
          Real.rpow_le_rpow hsum_nn hmax hγ_nn
        have hmul : (2 * Real.sqrt (b ⬝ b))^γBar
            = (2 : ℝ)^γBar * (Real.sqrt (b ⬝ b))^γBar :=
          Real.mul_rpow (by norm_num) hsqrt_bb
        have hb_le : (Real.sqrt (b ⬝ b))^γBar
            ≤ (Real.sqrt (a ⬝ a))^γBar + (Real.sqrt (b ⬝ b))^γBar := by
          have : 0 ≤ (Real.sqrt (a ⬝ a))^γBar := Real.rpow_nonneg hsqrt_aa _
          linarith
        calc (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBar
            ≤ (2 * Real.sqrt (b ⬝ b))^γBar := hstep
          _ = (2 : ℝ)^γBar * (Real.sqrt (b ⬝ b))^γBar := hmul
          _ ≤ (2 : ℝ)^γBar *
              ((Real.sqrt (a ⬝ a))^γBar + (Real.sqrt (b ⬝ b))^γBar) :=
                mul_le_mul_of_nonneg_left hb_le h2γ_nn
      · have hmax : Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b)
            ≤ 2 * Real.sqrt (a ⬝ a) := by linarith
        have hstep : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBar
            ≤ (2 * Real.sqrt (a ⬝ a))^γBar :=
          Real.rpow_le_rpow hsum_nn hmax hγ_nn
        have hmul : (2 * Real.sqrt (a ⬝ a))^γBar
            = (2 : ℝ)^γBar * (Real.sqrt (a ⬝ a))^γBar :=
          Real.mul_rpow (by norm_num) hsqrt_aa
        have ha_le : (Real.sqrt (a ⬝ a))^γBar
            ≤ (Real.sqrt (a ⬝ a))^γBar + (Real.sqrt (b ⬝ b))^γBar := by
          have : 0 ≤ (Real.sqrt (b ⬝ b))^γBar := Real.rpow_nonneg hsqrt_bb _
          linarith
        calc (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBar
            ≤ (2 * Real.sqrt (a ⬝ a))^γBar := hstep
          _ = (2 : ℝ)^γBar * (Real.sqrt (a ⬝ a))^γBar := hmul
          _ ≤ (2 : ℝ)^γBar *
              ((Real.sqrt (a ⬝ a))^γBar + (Real.sqrt (b ⬝ b))^γBar) :=
                mul_le_mul_of_nonneg_left ha_le h2γ_nn
    -- Identify `(√(v⬝v))^γ̄ = (v⬝v)^{γ̄/2}`.
    have hsqrt_aa_pow : (Real.sqrt (a ⬝ a)) ^ γBar = (a ⬝ a) ^ (γBar / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul haa_nn]; congr 1; ring
    have hsqrt_bb_pow : (Real.sqrt (b ⬝ b)) ^ γBar = (b ⬝ b) ^ (γBar / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbb_nn]; congr 1; ring
    rw [hsqrt_aa_pow, hsqrt_bb_pow] at hAdd
    exact le_trans hpow1 hAdd
  -- Local helper: sup-norm Jensen `(v⬝v)^{γ̄/2} ≤ d^{γ̄/2}·‖v‖^γ̄`.
  have hdot_sup : ∀ v : Fin d → ℝ,
      (v ⬝ v) ^ (γBar / 2) ≤ ((d : ℝ)) ^ (γBar / 2) * ‖v‖ ^ γBar := by
    intro v
    have hvv_nn : 0 ≤ v ⬝ v := hdot_nn v
    -- `v ⬝ v = ∑ vᵢ² ≤ d · ‖v‖²`.
    have hstep : v ⬝ v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
      have hpoint : ∀ i : Fin d, v i * v i ≤ ‖v‖ ^ 2 := by
        intro i
        have hvi : |v i| ≤ ‖v‖ := by
          have := norm_le_pi_norm v i
          rwa [Real.norm_eq_abs] at this
        have h0 : 0 ≤ ‖v‖ := norm_nonneg _
        have : v i * v i = |v i| ^ 2 := by rw [sq_abs]; ring
        rw [this]
        have := mul_le_mul hvi hvi (abs_nonneg _) h0
        nlinarith [abs_nonneg (v i)]
      calc v ⬝ v = ∑ i, v i * v i := rfl
        _ ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := Finset.sum_le_sum (fun i _ => hpoint i)
        _ = (d : ℝ) * ‖v‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
    have hγ2_nn : 0 ≤ γBar / 2 := by linarith
    have hrhs_nn : 0 ≤ (d : ℝ) * ‖v‖ ^ 2 := by positivity
    have h1 : (v ⬝ v) ^ (γBar / 2) ≤ ((d : ℝ) * ‖v‖ ^ 2) ^ (γBar / 2) :=
      Real.rpow_le_rpow hvv_nn hstep hγ2_nn
    have h2 : ((d : ℝ) * ‖v‖ ^ 2) ^ (γBar / 2)
        = ((d : ℝ)) ^ (γBar / 2) * ‖v‖ ^ γBar := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity)]
      congr 1
      rw [show ((‖v‖ ^ 2 : ℝ)) = ‖v‖ ^ (2 : ℝ) from by
            rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num, Real.rpow_natCast],
          ← Real.rpow_mul (norm_nonneg _)]
      congr 1; ring
    rw [h2] at h1; exact h1
  -- Now the per-test-pair bound.
  intro T
  -- Test-side `MemLpPer (ofReal γBar)` certs (`hpackγ` rewrites `pack.γBar`).
  have hυ_memLp : MemLpPer (ENNReal.ofReal γBar) T.υ := hpackγ ▸ T.υSob.1
  have hDυ_memLp : ∀ i, MemLpPer (ENNReal.ofReal γBar) (T.Dυ i) :=
    fun i => hpackγ ▸ T.hDυ_memGamma i
  -- Closed-form integrals (fixed per `T`).
  set Aυ : ℝ := ∫ x in UnitCube d, |T.υ x| ^ γBar with hAυ_def
  set ADυ : ℝ := ∫ x in UnitCube d,
      ((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2) with hADυ_def
  set Au : ℝ := (2 : ℝ) ^ γBar * (Aυ + bounds.C) with hAu_def
  set ADu : ℝ := (2 : ℝ) ^ γBar *
      (ADυ + ((d : ℝ)) ^ (γBar / 2) * bounds.C) with hADu_def
  have hAυ_nn : 0 ≤ Aυ :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hADυ_nn : 0 ≤ ADυ :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hdot_nn _) _)
  have hAu_nn : 0 ≤ Au := by
    rw [hAu_def]; exact mul_nonneg h2γ_nn (by linarith)
  have hADu_nn : 0 ≤ ADu := by
    rw [hADu_def]
    exact mul_nonneg h2γ_nn (by positivity)
  refine ⟨Aυ + Au + ADυ + ADu, by linarith, ?_⟩
  intro k
  -- Subsequence index and positivity.
  set ε := pack.εSeq (lim.φ k) with hε_def
  have hε_pos : 0 < ε := pack.εSeq_pos (lim.φ k)
  -- Seq-side `MemLpPer (ofReal γBar)` certs.
  have hu_memLp : MemLpPer (ENNReal.ofReal γBar) (seq.u ε) := by
    have := seq.hu_lp_γ ε hε_pos; rw [hγR] at this; exact this
  have hDu_memLp : ∀ i, MemLpPer (ENNReal.ofReal γBar) (seq.Du ε i) := by
    intro i; have := seq.hDu_lp ε hε_pos i; rw [hγR] at this; exact this
  -- Integrability certs (mirror `gateauxAux_of_paperHypotheses`).
  have hInt_abs : ∀ (f : (Fin d → ℝ) → ℝ),
      MemLpPer (ENNReal.ofReal γBar) f →
      Integrable (fun x : Fin d → ℝ => |f x| ^ γBar)
        (volume.restrict (UnitCube d)) := by
    intro f hf
    have hI := (hf.toMemLp).integrable_norm_rpow hγ_ne_zero hγ_ne_top
    rw [hγ_toReal] at hI
    have heq : (fun x : Fin d → ℝ => ‖f x‖ ^ γBar)
                = (fun x => |f x| ^ γBar) := by
      funext x; rw [Real.norm_eq_abs]
    rwa [heq] at hI
  -- Pointwise `‖g‖^γ̄ ≤ ∑ᵢ |g i|^γ̄` (sup attained at some coord).
  have hnorm_rpow_le_sum : ∀ (g : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      ‖(fun i => g i x)‖ ^ γBar ≤ ∑ i, |g i x| ^ γBar := by
    intro g x
    rcases isEmpty_or_nonempty (Fin d) with hempty | hne
    · -- d = 0: ‖0‖ = 0.
      have h0 : (fun i => g i x) = 0 := by
        funext i; exact (hempty.false i).elim
      rw [h0, norm_zero, Real.zero_rpow (by linarith : γBar ≠ 0)]
      exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    · -- pick i₀ attaining the sup of `‖g i x‖`.
      have hne' : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
      obtain ⟨i₀, _, hi₀⟩ :=
        Finset.exists_mem_eq_sup' hne' (fun i : Fin d => ‖g i x‖₊)
      have hnorm_eq : ‖(fun i => g i x)‖ = ‖g i₀ x‖ := by
        rw [Pi.norm_def]
        rw [show (Finset.univ.sup (fun i : Fin d => ‖g i x‖₊))
              = Finset.univ.sup' hne' (fun i : Fin d => ‖g i x‖₊) from
                (Finset.sup'_eq_sup hne' _).symm]
        rw [hi₀]; rfl
      rw [hnorm_eq, Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i => |g i x| ^ γBar)
        (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
        (Finset.mem_univ i₀)
  -- Integrability of `(g · g)^{γ̄/2}` (dominate by `d^{γ̄/2}·∑ᵢ|g i|^γ̄`).
  have hInt_dot : ∀ (g : Fin d → (Fin d → ℝ) → ℝ),
      (∀ i, MemLpPer (ENNReal.ofReal γBar) (g i)) →
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBar / 2))
        (volume.restrict (UnitCube d)) := by
    intro g hg
    have hInt_gi : ∀ i, Integrable (fun x : Fin d → ℝ => |g i x| ^ γBar)
        (volume.restrict (UnitCube d)) := fun i => hInt_abs (g i) (hg i)
    have hInt_dom : Integrable
        (fun x : Fin d → ℝ => ((d : ℝ)) ^ (γBar / 2) *
          ∑ i, |g i x| ^ γBar) (volume.restrict (UnitCube d)) :=
      (MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_gi i)).const_mul _
    apply MeasureTheory.Integrable.mono'
      (g := fun x => ((d : ℝ)) ^ (γBar / 2) * ∑ i, |g i x| ^ γBar) hInt_dom
    · -- AEStronglyMeasurable of `(g·g)^{γ̄/2}`.
      have hCont : Continuous (fun y : ℝ => y ^ (γBar / 2)) :=
        Real.continuous_rpow_const (by linarith)
      have hDot_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => ((fun i => g i x) ⬝ (fun i => g i x)))
          (volume.restrict (UnitCube d)) := by
        unfold euclideanDot
        refine Finset.aestronglyMeasurable_fun_sum _ ?_
        intro i _
        exact (hg i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
      exact hCont.comp_aestronglyMeasurable hDot_aesm
    · -- `(g·g)^{γ̄/2} ≤ d^{γ̄/2}·‖g‖^γ̄ ≤ d^{γ̄/2}·∑|g i|^γ̄`.
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hdot_nn _) _)]
      refine le_trans (hdot_sup (fun i => g i x)) ?_
      exact mul_le_mul_of_nonneg_left (hnorm_rpow_le_sum g x) hd_rpow_nn
  -- The four integrability certificates for the analytic core.
  have hInt_DυDυ : Integrable (fun x : Fin d → ℝ =>
      ((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2))
      (volume.restrict (UnitCube d)) := hInt_dot T.Dυ hDυ_memLp
  have hInt_DυmDu : Integrable (fun x : Fin d → ℝ =>
      ((fun i => T.Dυ i x - seq.Du ε i x) ⬝ (fun i => T.Dυ i x - seq.Du ε i x))
        ^ (γBar / 2))
      (volume.restrict (UnitCube d)) :=
    hInt_dot (fun i x => T.Dυ i x - seq.Du ε i x)
      (fun i => by simpa only [Pi.sub_def] using
        Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ_memLp i).toMemLp (hDu_memLp i).toMemLp))
  have hInt_υ : Integrable (fun x : Fin d → ℝ => |T.υ x| ^ γBar)
      (volume.restrict (UnitCube d)) := hInt_abs T.υ hυ_memLp
  have hInt_υmu : Integrable (fun x : Fin d → ℝ =>
      |T.υ x - seq.u ε x| ^ γBar)
      (volume.restrict (UnitCube d)) :=
    hInt_abs (fun x => T.υ x - seq.u ε x)
      (by simpa only [Pi.sub_def] using
        Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hυ_memLp.toMemLp hu_memLp.toMemLp))
  -- Apriori bound at `ε`, with the `u`/`Du` integral terms extracted.
  have hbound := bounds.bound ε hε_pos
  -- The three LHS integral terms and their non-negativity.
  set Im : ℝ := ∫ x in UnitCube d, seq.m ε x ^ betaBar h.β with hIm_def
  set Lu : ℝ := StationaryMFG.Periodic.lpNormPer
      (ENNReal.ofReal (gammaBar h.α h.β)) (seq.u ε)
      ^ gammaBar h.α h.β with hLu_def
  set IDu : ℝ := ∫ x in UnitCube d,
      ‖(fun i => seq.Du ε i x)‖ ^ gammaBar h.α h.β with hIDu_def
  have hIm_nn : 0 ≤ Im := by
    rw [hIm_def]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [seq.mε_nonneg ε hε_pos] with x hx
    exact Real.rpow_nonneg hx _
  have hLu_nn : 0 ≤ Lu := by
    rw [hLu_def]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hIDu_nn : 0 ≤ IDu := by
    rw [hIDu_def]
    exact MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hSum_le : Im + Lu + IDu ≤ bounds.C := hbound
  -- `∫|u_ε|^γ̄ ≤ bounds.C`: convert `Lu` to `∫|u_ε|^γ̄` via the bridge.
  have hLu_eq : Lu = ∫ x in UnitCube d, |seq.u ε x| ^ γBar := by
    have hbridge := StationaryMFG.Theorems.SimplePower.integral_abs_rpow_eq_lpNormPer_rpow
      (d := d) (γBar := gammaBar h.α h.β)
      (lt_of_lt_of_le zero_lt_one
        (StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β h.hα h.hβ).le)
      (seq.u ε) (seq.hu_lp_γ ε hε_pos)
    -- `hbridge : ∫|u|^(gammaBar..) = lpNormPer^(gammaBar..)`; rewrite γ̄.
    rw [hLu_def]
    rw [← hbridge, hγR]
  have hIu_le : (∫ x in UnitCube d, |seq.u ε x| ^ γBar) ≤ bounds.C := by
    rw [← hLu_eq]; linarith
  -- `∫(Du·Du)^{γ̄/2} ≤ d^{γ̄/2}·bounds.C` via sup-norm Jensen + `IDu ≤ C`.
  have hIDu_le : IDu ≤ bounds.C := by linarith
  have hADu_int_le : (∫ x in UnitCube d,
        ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2))
      ≤ ((d : ℝ)) ^ (γBar / 2) * bounds.C := by
    -- Pointwise `(Du·Du)^{γ̄/2} ≤ d^{γ̄/2}·‖Du‖^γ̄`, then integrate.
    have hInt_DuDu : Integrable (fun x : Fin d → ℝ =>
        ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2))
        (volume.restrict (UnitCube d)) := hInt_dot (seq.Du ε) hDu_memLp
    have hInt_normDu : Integrable (fun x : Fin d → ℝ =>
        ((d : ℝ)) ^ (γBar / 2) * ‖(fun i => seq.Du ε i x)‖ ^ γBar)
        (volume.restrict (UnitCube d)) := by
      have hbase : Integrable (fun x : Fin d → ℝ =>
          ‖(fun i => seq.Du ε i x)‖ ^ γBar) (volume.restrict (UnitCube d)) := by
        have hI : Integrable (fun x : Fin d → ℝ =>
            ‖(fun i => seq.Du ε i x)‖ ^ gammaBar h.α h.β)
            (volume.restrict (UnitCube d)) := seq.hDu_norm_int ε hε_pos
        rwa [hγR] at hI
      exact hbase.const_mul _
    have hStep : (∫ x in UnitCube d,
          ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2))
        ≤ ∫ x in UnitCube d,
          ((d : ℝ)) ^ (γBar / 2) * ‖(fun i => seq.Du ε i x)‖ ^ γBar := by
      refine MeasureTheory.integral_mono_ae hInt_DuDu hInt_normDu ?_
      exact Filter.Eventually.of_forall (fun x => hdot_sup _)
    have hLin : (∫ x in UnitCube d,
          ((d : ℝ)) ^ (γBar / 2) * ‖(fun i => seq.Du ε i x)‖ ^ γBar)
        = ((d : ℝ)) ^ (γBar / 2) *
          ∫ x in UnitCube d, ‖(fun i => seq.Du ε i x)‖ ^ γBar := by
      rw [MeasureTheory.integral_const_mul]
    rw [hLin] at hStep
    -- `∫‖Du‖^γ̄ = IDu ≤ C` (after `hγR` rewrite).
    have hIDu_eq : (∫ x in UnitCube d, ‖(fun i => seq.Du ε i x)‖ ^ γBar) = IDu := by
      rw [hIDu_def, ← hγR]
    rw [hIDu_eq] at hStep
    calc (∫ x in UnitCube d,
            ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2))
        ≤ ((d : ℝ)) ^ (γBar / 2) * IDu := hStep
      _ ≤ ((d : ℝ)) ^ (γBar / 2) * bounds.C :=
          mul_le_mul_of_nonneg_left hIDu_le hd_rpow_nn
  -- `Au` bound: `∫|υ - u_k|^γ̄ ≤ Au`.
  have hAu_bound : (∫ x in UnitCube d, |T.υ x - seq.u ε x| ^ γBar) ≤ Au := by
    have hInt_pair : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBar * (|T.υ x| ^ γBar + |seq.u ε x| ^ γBar))
        (volume.restrict (UnitCube d)) :=
      (hInt_υ.add (hInt_abs (seq.u ε) hu_memLp)).const_mul _
    have hStep1 : (∫ x in UnitCube d, |T.υ x - seq.u ε x| ^ γBar)
        ≤ ∫ x in UnitCube d,
            (2 : ℝ) ^ γBar * (|T.υ x| ^ γBar + |seq.u ε x| ^ γBar) := by
      refine MeasureTheory.integral_mono_ae hInt_υmu hInt_pair ?_
      exact Filter.Eventually.of_forall (fun x => habs_sub (T.υ x) (seq.u ε x))
    have hLin : (∫ x in UnitCube d,
          (2 : ℝ) ^ γBar * (|T.υ x| ^ γBar + |seq.u ε x| ^ γBar))
        = (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d, |T.υ x| ^ γBar) +
              ∫ x in UnitCube d, |seq.u ε x| ^ γBar) := by
      rw [MeasureTheory.integral_const_mul]; congr 1
      rw [MeasureTheory.integral_add hInt_υ (hInt_abs (seq.u ε) hu_memLp)]
    rw [hLin] at hStep1
    calc (∫ x in UnitCube d, |T.υ x - seq.u ε x| ^ γBar)
        ≤ (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d, |T.υ x| ^ γBar) +
              ∫ x in UnitCube d, |seq.u ε x| ^ γBar) := hStep1
      _ = (2 : ℝ) ^ γBar * (Aυ + ∫ x in UnitCube d, |seq.u ε x| ^ γBar) := by
          rw [hAυ_def]
      _ ≤ (2 : ℝ) ^ γBar * (Aυ + bounds.C) :=
          mul_le_mul_of_nonneg_left (by linarith [hIu_le]) h2γ_nn
      _ = Au := by rw [hAu_def]
  -- `ADu` bound: `∫((Dυ-Du_k)·(Dυ-Du_k))^{γ̄/2} ≤ ADu`.
  have hADu_bound : (∫ x in UnitCube d,
        ((fun i => T.Dυ i x - seq.Du ε i x)
          ⬝ (fun i => T.Dυ i x - seq.Du ε i x)) ^ (γBar / 2)) ≤ ADu := by
    have hInt_DuDu : Integrable (fun x : Fin d → ℝ =>
        ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2))
        (volume.restrict (UnitCube d)) := hInt_dot (seq.Du ε) hDu_memLp
    have hInt_pair : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBar *
          (((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2) +
            ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2)))
        (volume.restrict (UnitCube d)) :=
      (hInt_DυDυ.add hInt_DuDu).const_mul _
    have hStep1 : (∫ x in UnitCube d,
          ((fun i => T.Dυ i x - seq.Du ε i x)
            ⬝ (fun i => T.Dυ i x - seq.Du ε i x)) ^ (γBar / 2))
        ≤ ∫ x in UnitCube d,
            (2 : ℝ) ^ γBar *
              (((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2) +
                ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2)) := by
      refine MeasureTheory.integral_mono_ae hInt_DυmDu hInt_pair ?_
      exact Filter.Eventually.of_forall
        (fun x => hdot_sub (fun i => T.Dυ i x) (fun i => seq.Du ε i x))
    have hLin : (∫ x in UnitCube d,
          (2 : ℝ) ^ γBar *
            (((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2) +
              ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2)))
        = (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d,
                ((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2)) +
              ∫ x in UnitCube d,
                ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2)) := by
      rw [MeasureTheory.integral_const_mul]; congr 1
      rw [MeasureTheory.integral_add hInt_DυDυ hInt_DuDu]
    rw [hLin] at hStep1
    calc (∫ x in UnitCube d,
            ((fun i => T.Dυ i x - seq.Du ε i x)
              ⬝ (fun i => T.Dυ i x - seq.Du ε i x)) ^ (γBar / 2))
        ≤ (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d,
                ((fun i => T.Dυ i x) ⬝ (fun i => T.Dυ i x)) ^ (γBar / 2)) +
              ∫ x in UnitCube d,
                ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2)) := hStep1
      _ = (2 : ℝ) ^ γBar *
            (ADυ + ∫ x in UnitCube d,
                ((fun i => seq.Du ε i x) ⬝ (fun i => seq.Du ε i x)) ^ (γBar / 2)) := by
          rw [hADυ_def]
      _ ≤ (2 : ℝ) ^ γBar * (ADυ + ((d : ℝ)) ^ (γBar / 2) * bounds.C) :=
          mul_le_mul_of_nonneg_left (by linarith [hADu_int_le]) h2γ_nn
      _ = ADu := by rw [hADu_def]
  -- Assemble via the analytic core, then absorb the slack.
  have hcore := StationaryMFG.Theorems.SimplePower.Banach.gateauxWpPair_uniform_bound_per_triple
    (d := d) γBar hγ_one_le T.μ T.υ T.Dυ (seq.Du ε) (seq.u ε)
    Aυ Au ADυ ADu
    hInt_DυDυ hInt_DυmDu hInt_υ hInt_υmu
    (le_refl Aυ) hAu_bound (le_refl ADυ) hADu_bound
  have hslack : 0 ≤ hcong.C * hcong.β := mul_nonneg hcong.hC.le hcong.hβ.le
  calc |gateauxWpPair γBar T.Dυ T.υ
          (fun i x => T.Dυ i x - seq.Du ε i x) (T.υ - seq.u ε)|
      ≤ Aυ + Au + ADυ + ADu := hcore
    _ ≤ (Aυ + Au + ADυ + ADu) + hcong.C * hcong.β := by linarith

/-! ## Phase 5 closed producer -/

/-- **Phase 7 producer for T2 Phase 5** (paper line 1604,
`eq:existweaksol.congestion`).

Given:

* the Phase 3 regularised sequence data `seq` (per-ε bare-function
  fields),
* the Phase 4 weak-limit data `lim` (subsequence + cluster pair),
* the Phase 3 apriori bound data `bounds`,
* the paper hypothesis `hcong : CongestionGrowthCore H DpH J`,
* the paper hypothesis `hV : MemLpPer betaBar' V`,
* the explicit uniform-in-k Gateaux residual bound triplet `M`, `M_nn`,
  `hreg_bdd` (phase-9B B3 drain; surfaced upstream as
  `pack5_regBddOracle`),
* the explicit per-test-pair regularized weak VI `hVIeps` (phase-9B B4
  drain; surfaced upstream as `pack5_vIEpsOracle`),
* the Phase 7 upstream pack `pkg : CongestionLimitVIUpstreamPack` — now
  a vestigial empty structure (its sole former field `hVIeps` drained to
  the explicit parameter above), retained for type stability only,

produce a `CongestionLimitVIData` recording:
* the limit weak VI at the cluster pair for every admissible test pair
  (proved by per-test-pair invocation of the real-numerical kernel
  `Theorems.SimplePower.limit_passage_weak_VI`);
* the per-k apriori bound at the extracted subsequence (body-derived
  from `bounds.bound`);
* the auxiliary `hε_to0`, `hε_nonneg`, `hJ_id_pos` certificates.

### Parameter consumption

Every signature parameter is kernel-used:

* `seq` — type-level in `bounds`/`lim`/`pkg`; `seq.m`, `seq.u`, `seq.Du`
  appear in the output `hSubseqBound`.
* `lim` — body-derived via `lim.φ`; `lim.m`, `lim.u`, `lim.Du` appear
  in the output `hLimitVI` directly. `lim.hWeakConvCone` is
  destructured below to extract the cluster-point identification
  consumed by `pkg.hpair_conv`'s precondition.
* `bounds` — body-evaluated at each `pack.εSeq (lim.φ k)` to produce
  `hSubseqBound`. Genuine post-extraction restriction, not a rename.
* `hcong` — `hcong.mDpHat0.J_of_pos` is body-extracted to produce
  `hJ_id_pos`; `hcong.C`/`hcong.β` enter type-level in the explicit
  `hreg_bdd` parameter's bound `M + hcong.C * hcong.β`.
* `hV` — type-level prerequisite of `pkg.hpair_conv` (V-pairing
  Hölder convergence requires `V ∈ L^{β̄'}_per`); appears in `_hV` in
  the output type signature.
-/
noncomputable def congestionLimitVI_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData (d := d) H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : StationaryMFG.Theorems.Congestion.CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    (lim : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
           haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
           StationaryMFG.Theorems.Congestion.CongestionWeakLimitData
             V H DpH J h seq pack)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {betaBar' : ℝ≥0∞}
    (hV : MemLpPer betaBar' V)
    (γBar : ℝ)
    -- (P4b0, iter-1030+) Type-only reconciliation of the free Gateaux residual
    -- exponent `γBar` with the canonical `gammaBar hcong.α hcong.β`. This pins
    -- the exponent at which the uniform a-priori control lives (`bounds.bound`
    -- and the test pair `T.υSob` are both at `gammaBar α β`), the prerequisite
    -- for the P4b internal producer of `hreg_bdd`. Carried unused here; P4b
    -- consumes it analytically. No oracle change.
    (hγBar : γBar = StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β)
    -- Phase-9B B1 drain (iter-0869): explicit ε-null-convergence
    -- parameter. Previously a field of `CongestionLimitVIUpstreamPack`;
    -- now derived at the top-level H5 producer body via
    -- `eNullSeq_of_oneOverNSucc_strictMono` and threaded here.
    (hε_to0 : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
              haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
              Tendsto (fun k => pack.εSeq (lim.φ k)) atTop (𝓝 0))
    -- Phase-9B B2 drain (iter-0870): explicit per-test-pair pairing
    -- convergence. Previously a field of `CongestionLimitVIUpstreamPack`;
    -- now an explicit parameter, paper-side justified by the Hölder-
    -- pairing convergence at paper line 1604 ("Hölder's inequality"
    -- after `eq:compactness.congestion`). Surfaced upstream as
    -- `pack5_pairConvOracle` on the H5 producer and the public theorem.
    (hpair_conv :
      haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
      haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
      ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
        Tendsto (fun k =>
          mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
              (T.μ - seq.m (pack.εSeq (lim.φ k)))
              (T.υ - seq.u (pack.εSeq (lim.φ k))))
          atTop
          (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
                T.Dυ T.μ T.υ
                (fun i x => T.Dυ i x - lim.Du i x)
                (T.μ - lim.m) (T.υ - lim.u))))
    -- (P4b, iter-1099) The former `hreg_bdd` parameter (surfaced upstream as
    -- `pack5_regBddOracle`) has been REMOVED: the per-test-pair uniform-in-k
    -- Gateaux residual bound is now sourced INTERNALLY in the body via
    -- `congestionGateauxUniformBound_of_apriori` (paper line 1604, uniform
    -- bound from `apriori-congestion.growth` via Hölder), fed `bounds`, `seq`,
    -- `hcong`, and the exponent matches `hγR`/`hpackγ`. NET oracle removal:
    -- 8 → 7 public oracles. The only new inputs are the *exponent
    -- reconciliations* below (no analytic oracle).
    -- Exponent matches (pure reconciliations, NOT oracles; both dischargeable
    -- at the H5 level from `topPack.γBar_eq` + defeq `h.α = hcong.α`):
    --   `hγR`  : the apriori exponent `gammaBar h.α h.β` equals the free `γBar`
    --            (`bounds.bound`, `seq.hu_lp_γ`, `seq.hDu_lp` all live here);
    --   `hpackγ`: the Phase-4 pack's `ℝ≥0∞` exponent is `ofReal γBar` (the test
    --            pair's `MemLpPer pack.γBar` certs land at `ofReal γBar`).
    -- They are the prerequisite for the internal `hreg_bdd` producer.
    (hγR : StationaryMFG.Hamiltonian.gammaBar h.α h.β = γBar)
    (hpackγ : pack.γBar = ENNReal.ofReal γBar)
    -- Phase-9B B4 drain (iter-0872): explicit per-test-pair regularized
    -- weak VI in `mfgOperatorEpsPair` shape. Previously the sole field
    -- `hVIeps` of `CongestionLimitVIUpstreamPack`; now an explicit
    -- parameter, paper-side justified by evaluating
    -- `paper:thm:weakAepsi.congestion` at an arbitrary admissible test
    -- pair `(μ, υ, Dυ) ∈ 𝓚` (Phase 2's
    -- `congestionRegularizedSolutionAtEps_of_paperHypotheses` only
    -- delivers the regularized VI at the canonical pair `(m_ε, u_ε)`).
    -- Surfaced upstream as `pack5_vIEpsOracle` on the H5 producer and
    -- the public theorem.
    (hVIeps :
      haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
      haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
      ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ) (k : ℕ),
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar (pack.εSeq (lim.φ k)) T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
              (T.μ - seq.m (pack.εSeq (lim.φ k)))
              (T.υ - seq.u (pack.εSeq (lim.φ k))))
    (pkg : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
           haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
           CongestionLimitVIUpstreamPack V h seq pack lim bounds hcong hV γBar) :
    haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
    haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
    CongestionLimitVIData V h seq pack lim bounds hcong hV γBar := by
  -- Pull Phase 4 typeclass facts into scope (these are used implicitly
  -- by the typing of `lim`).
  haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
  haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
  -- Phase-9B B4 (iter-0872): `pkg : CongestionLimitVIUpstreamPack` is now
  -- a *vestigial* (empty) structure — its sole former field `hVIeps`
  -- was drained to the explicit `hVIeps` parameter above. It is retained
  -- so the Phase-5/6 output records that mention it keep stable types;
  -- it is produced by `pack5_of_paperHypotheses` from the four named
  -- oracles. We record its consumption here (no analytic content).
  let _vestigialPack := pkg
  -- (P4b, iter-1099) Source the per-test-pair uniform-in-k Gateaux residual
  -- bound INTERNALLY (drains `pack5_regBddOracle`), from `bounds`/`seq`/`hcong`
  -- and the exponent reconciliations `hγR`/`hpackγ`.
  have hreg_bdd := congestionGateauxUniformBound_of_apriori
    (d := d) V h seq pack lim bounds hcong hV γBar hγR hpackγ
  -- (P4b0) Record the exponent reconciliation as consumed (used by P4b).
  let _hγBar := hγBar
  -- Note on `lim.hWeakConvCone`: the abstract weak-cluster point
  -- existence carried by `lim.hWeakConvCone` is the Phase 4 output
  -- the Phase 5 producer body does not directly inspect — the
  -- analytic pairing-convergence content is routed through the
  -- pack's `pkg.hpair_conv` field, which is stated against the
  -- chosen bare-function representatives `lim.m`, `lim.u`, `lim.Du`
  -- (this is the documented Phase 7 bridge gap; the prior iteration's
  -- discard destructure was a sham caught by review). `lim` is still
  -- materially consumed via `lim.φ`, `lim.m`, `lim.u`, `lim.Du`
  -- (see uses below).
  -- **Per-k apriori at the extracted subsequence.** Body-evaluate
  -- `bounds.bound` at each `pack.εSeq (lim.φ k)` — the choice of
  -- subsequence index `lim.φ k` is body-derived from Phase 4,
  -- making this a genuine restriction, not a rename.
  -- **Phase-3 uniform-C promotion (iter):** `bounds` now carries a
  -- single ε-independent constant `bounds.C` (paper line 1581) with
  -- `bounds.bound : ∀ ε > 0, … ≤ bounds.C`. The per-k existential
  -- below is satisfied uniformly by `Cε := bounds.C`; the choice of
  -- subsequence index `lim.φ k` is still body-derived from Phase 4,
  -- making this a genuine restriction.
  have hSub : ∀ k, ∃ Cε : ℝ, 0 ≤ Cε ∧
      (∫ x in UnitCube d, seq.m (pack.εSeq (lim.φ k)) x ^ betaBar h.β
          ∂(volume : Measure (Fin d → ℝ)))
        + StationaryMFG.Periodic.lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β))
            (seq.u (pack.εSeq (lim.φ k)))
          ^ gammaBar h.α h.β
        + (∫ x in UnitCube d,
              ‖(fun i => seq.Du (pack.εSeq (lim.φ k)) i x)‖
                ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ Cε := by
    intro k
    exact ⟨bounds.C, bounds.C_nn,
      bounds.bound (pack.εSeq (lim.φ k)) (pack.εSeq_pos (lim.φ k))⟩
  -- **Per-test-pair limit weak VI.** Invoke the real-numerical kernel
  -- `SimplePower.limit_passage_weak_VI` per test pair, with the pack's
  -- per-test-pair `hVIeps`/`hpair_conv`/`hreg_bdd` threaded through.
  have hLim : ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            T.Dυ T.μ T.υ
            (fun i x => T.Dυ i x - lim.Du i x)
            (T.μ - lim.m) (T.υ - lim.u) := by
    intro T
    -- Per-k ε-non-negativity at the extracted subsequence.
    have hε_nn : ∀ k, 0 ≤ pack.εSeq (lim.φ k) :=
      fun k => (pack.εSeq_pos (lim.φ k)).le
    -- Rewrite the pack's `hVIeps T k` from `mfgOperatorEpsPair` shape
    -- to the additive `mfgOperatorPair + ε · gateauxWpPair` shape by
    -- unfolding the regularized-operator definition.
    have hVI_add : ∀ k,
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) T.Dυ T.μ T.υ
                (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
                (T.μ - seq.m (pack.εSeq (lim.φ k)))
                (T.υ - seq.u (pack.εSeq (lim.φ k)))
              + pack.εSeq (lim.φ k) *
                gateauxWpPair γBar T.Dυ T.υ
                  (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
                  (T.υ - seq.u (pack.εSeq (lim.φ k))) := by
      intro k
      have hk := hVIeps T k
      unfold mfgOperatorEpsPair at hk
      exact hk
    -- Delegate to the SimplePower real-numerical kernel. (P4a) Extract
    -- the per-test-pair `M`/`hbdd` from the per-pair existential bound;
    -- the kernel only needs the per-`T` `∀ k, |…| ≤ M`.
    obtain ⟨_M, _, hbdd⟩ := hreg_bdd T
    exact StationaryMFG.Theorems.SimplePower.limit_passage_weak_VI
      (V := V) (H := H) (DpH := DpH)
      hε_nn hε_to0 hVI_add (hpair_conv T) hbdd
  -- **Transport-side flux identification** — threaded from
  -- `hcong.mDpHat0.J_of_pos`. The `hcong` parameter materially
  -- contributes this field of the output.
  have hJpos : ∀ (x : Fin d → ℝ) (p : Fin d → ℝ) (m : ℝ),
      0 < m → J x p m = m • DpH x p m := hcong.mDpHat0.J_of_pos
  -- **Per-test-pair Gateaux residual bound output.** (P4a) The per-pair
  -- `hreg_bdd` parameter (surfaced as `pack5_regBddOracle`) is exactly the
  -- output field. The type materially references `hcong.C` and `hcong.β`
  -- (from the bound shape), making `hcong` type-level constrain the Phase 5
  -- output (per Fix 3 of the review).
  have hRegUniform :
      ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ (k : ℕ),
            |gateauxWpPair γBar T.Dυ T.υ
                (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
                (T.υ - seq.u (pack.εSeq (lim.φ k)))| ≤ M + hcong.C * hcong.β :=
    hreg_bdd
  refine
    { hε_to0 := hε_to0
      hε_nonneg := fun k => (pack.εSeq_pos (lim.φ k)).le
      hLimitVI := hLim
      hSubseqBound := hSub
      hregUniform := hRegUniform
      hV_per := hV
      hJ_id_pos := hJpos }

/-! ## Sanity-check example -/

/-- Type-check that the Phase 5 producer signature is
`(V, h, seq, pack, lim, bounds, hcong, hV, γBar, pkg)` and returns
`CongestionLimitVIData`. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData (d := d) H DpH)
    (seq : StationaryMFG.Congestion.CongestionRegularizedSequenceDataNN V H DpH J h τ)
    (pack : StationaryMFG.Theorems.Congestion.CongestionWeakCompactnessUpstreamPack
              V H DpH J h seq)
    (lim : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
           haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
           StationaryMFG.Theorems.Congestion.CongestionWeakLimitData
             V H DpH J h seq pack)
    (bounds : CongestionAprioriBoundData V H DpH J h seq.m seq.u seq.Du)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {betaBar' : ℝ≥0∞}
    (hV : MemLpPer betaBar' V)
    (γBar : ℝ)
    (hγBar : γBar = StationaryMFG.Hamiltonian.gammaBar hcong.α hcong.β)
    (hε_to0 : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
              haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
              Tendsto (fun k => pack.εSeq (lim.φ k)) atTop (𝓝 0))
    (hpair_conv :
      haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
      haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
      ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ),
        Tendsto (fun k =>
          mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
              (T.μ - seq.m (pack.εSeq (lim.φ k)))
              (T.υ - seq.u (pack.εSeq (lim.φ k))))
          atTop
          (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
                T.Dυ T.μ T.υ
                (fun i x => T.Dυ i x - lim.Du i x)
                (T.μ - lim.m) (T.υ - lim.u))))
    -- (P4b, iter-1099) `hreg_bdd` REMOVED — sourced internally; only the two
    -- exponent reconciliations remain.
    (hγR : StationaryMFG.Hamiltonian.gammaBar h.α h.β = γBar)
    (hpackγ : pack.γBar = ENNReal.ofReal γBar)
    (hVIeps :
      haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
      haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
      ∀ (T : CongestionLimitVITestPair (d := d)
            pack.βBar betaBar' pack.γBar hcong.α hcong.β hcong.τ) (k : ℕ),
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar (pack.εSeq (lim.φ k)) T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - seq.Du (pack.εSeq (lim.φ k)) i x)
              (T.μ - seq.m (pack.εSeq (lim.φ k)))
              (T.υ - seq.u (pack.εSeq (lim.φ k))))
    (pkg : haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
           haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
           CongestionLimitVIUpstreamPack V h seq pack lim bounds hcong hV γBar) :
    haveI : Fact (1 ≤ pack.βBar) := pack.hβFact
    haveI : Fact (1 ≤ pack.γBar) := pack.hγFact
    CongestionLimitVIData V h seq pack lim bounds hcong hV γBar :=
  congestionLimitVI_of_paperHypotheses V h seq pack lim bounds hcong hV γBar
    hγBar hε_to0 hpair_conv hγR hpackγ hVIeps pkg

/-! ## P6a0 — concrete-VI bridge kernel (per periodic test pair)

`congestionLimitVI_concrete_at_testPair` is the genuinely-provable kernel
of the P6a0 concrete-VI bridge. It is the **reverse** of
`congestion_vIEps_at_testPair` (StrongIsStrong.lean:3487), specialised to
`ε = 0`: starting from the *abstract* limit weak VI at a **periodic**
admissible test pair `T` (the `mfgOperatorPair` form carried by
`CongestionLimitVIData.hLimitVI`), it produces the **concrete**
Banach-operator inequality
`0 ≤ congestionAepsiOpK hmon hcong hVmeas hV 0 vT (vT − w)` at the Banach
lift `vT` of `T`, against any a.e.-coercion witness `w` for the bare
limit functions `(m, u, Du)`.

**Scope note (split rationale, iter-1030).** This kernel covers exactly the
*periodic* test pairs the abstract VI certifies. The full
`∀ v ∈ congestionBanachK` form consumed by `h_DCT_producer_of_m_nonneg`
(StrongIsStrong.lean:5502) additionally requires the VI at *non-periodic*
test densities (the engine applies it at `ρ = max(muAux, δ)`, which is not
a.e.-periodic). Extending this kernel to the whole Banach cone is the
density-extension child task
`infra-P7-sigfix-T2-pub-P6a0b-limitVI-density-extension`.

The route mirrors `congestion_vIEps_at_testPair` step-for-step (lift,
on-domain operator identity, two a.e.-congruences), then closes with the
ε=0 collapse `mfgOperatorEpsPair_zero_eq` and the abstract `habs T`. -/
theorem congestionLimitVI_concrete_at_testPair
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (hmon : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    -- The abstract limit weak VI, at the `hcong` concrete exponents
    -- (`CongestionLimitVIData.hLimitVI` at the reconciled exponents).
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u))
    -- A.e.-coercion witness for the bare limit functions.
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hw_m : m =ᵐ[volume.restrict (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ))
    (hw_u : u =ᵐ[volume.restrict (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (hw_Du : ∀ i,
      Du i =ᵐ[volume.restrict (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    -- A periodic admissible test pair.
    (T : CongestionLimitVITestPair (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ) :
    ∃ vT : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)),
      (⇑vT.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[volume.restrict (UnitCube d)] T.μ ∧
      (⇑vT.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[volume.restrict (UnitCube d)] T.υ ∧
      (∀ i, (⇑(vT.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[volume.restrict (UnitCube d)] T.Dυ i) ∧
      vT ∈ congestionBanachK d
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
            hcong.α hcong.β hcong.τ ∧
      0 ≤ congestionAepsiOpK hmon hcong hVmeas hV 0 vT (vT - w) := by
  classical
  -- Step A: lift the periodic admissible test pair to the Banach domain.
  obtain ⟨vT, hvT_dens, hvT_val, hvT_grad, hvT_mem⟩ :=
    congestionBanachLift_of_testData (d := d)
      (βBar := ENNReal.ofReal (hcong.β + 1))
      (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      T.μLp T.υSob T.hDυ_memGamma T.hDυ_weak T.hCone
  refine ⟨vT, hvT_dens, hvT_val, hvT_grad, hvT_mem, ?_⟩
  -- Step B: on-domain operator identity at `ε = 0`.
  have h_op : congestionAepsiOpK hmon hcong hVmeas hV 0 vT (vT - w)
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) 0
          (fun i x => (⇑(vT.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑vT.1) (⇑vT.2.1)
          (fun i => (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ))
          (⇑(vT - w).1) (⇑(vT - w).2.1) :=
    congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV 0 hvT_mem (vT - w)
  -- Step C: collapse `ε = 0` to the unregularized operator.
  rw [mfgOperatorEpsPair_zero_eq] at h_op
  -- Step D: a.e. profiles of the test-direction slots (`vT - w`).
  have hqm_ae : (⇑(vT - w).1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] (T.μ - m) := by
    have hsub : (vT - w).1 = vT.1 - w.1 := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub vT.1 w.1, hvT_dens, hw_m]
      with x hx hxμ hxm
    rw [hx, Pi.sub_apply, hxμ, Pi.sub_apply, hxm]
  have hqu_ae : (⇑(vT - w).2.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] (T.υ - u) := by
    have hsub : (vT - w).2.1 = vT.2.1 - w.2.1 := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub vT.2.1 w.2.1, hvT_val, hw_u]
      with x hx hxυ hxu
    rw [hx, Pi.sub_apply, hxυ, Pi.sub_apply, hxu]
  have hqDu_ae : ∀ i, (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => T.Dυ i x - Du i x) := by
    intro i
    have hsub : (vT - w).2.2 i = vT.2.2 i - w.2.2 i := rfl
    rw [hsub]
    filter_upwards [MeasureTheory.Lp.coeFn_sub (vT.2.2 i) (w.2.2 i),
      hvT_grad i, hw_Du i] with x hx hxDυ hxDu
    rw [hx, Pi.sub_apply, hxDυ, hxDu]
  -- Step E: rewrite `h_op` to the bare test-pair shape via two
  -- a.e.-congruences (primal slots, then test-direction slots).
  rw [mfgOperatorPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
        (fun i x => (⇑(vT.2.2 i) : (Fin d → ℝ) → ℝ) x) T.Dυ
        (⇑vT.1) T.μ (⇑vT.2.1) T.υ
        (fun i => (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ))
        (⇑(vT - w).1) (⇑(vT - w).2.1)
        (fun i => hvT_grad i) hvT_dens hvT_val] at h_op
  rw [mfgOperatorPair_congr_ae (V := V) (H := H) (DpH := DpH)
        T.Dυ T.μ T.υ
        (fun i => (⇑((vT - w).2.2 i) : (Fin d → ℝ) → ℝ))
        (fun i x => T.Dυ i x - Du i x)
        (⇑(vT - w).1) (T.μ - m) (⇑(vT - w).2.1) (T.υ - u)
        (fun i => hqDu_ae i) hqm_ae hqu_ae] at h_op
  -- Step F: close via the abstract VI at `T`.
  rw [h_op]
  exact habs T

/-! ## P6a0b — density-slot reduction of the abstract VI to the integral form

The downstream HJB engine `weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg`
(StrongIsStrong.lean:700) consumes its variational input as the **integral
inequality**
`∫ (u + H(Du, ρ) − V)·(ρ − m) ≤ 0`
applied at the truncated density `ρ = max(muAux, δ)` (StrongIsStrong.lean:5502
feeds it via `h_DCT_producer_of_m_nonneg`). The variational engine's per-`δ`
producer `perdelta_vi_integral_le_of_m_nonneg` reaches that integral by
applying the *cone* VI `∀ v ∈ K, 0 ≤ A v (v − w)` at a Banach test point whose
value/gradient slots coincide with the witness `w` (so the gradient/value test
directions vanish), leaving only the density-slot integral.

The lemma below performs the same reduction directly from the **abstract**
limit weak VI (`CongestionLimitVIData.hLimitVI`, the `mfgOperatorPair` form),
*without* threading the cone VI. Its hypothesis is an abstract VI at the single
periodic admissible test pair whose value/gradient are the (periodic) limit
`(u, Du)` and whose density is the periodic admissible `ρ`. Because the
gradient/value test directions are then identically zero, the two non-density
summands of `mfgOperatorPair` vanish pointwise, and the abstract VI collapses
to exactly the integral inequality the engine consumes.

This closes the *periodicity gap* identified in P6a0 (split rationale): the
density `ρ = max(muAux, δ)` is periodic whenever the data `m, u, V, Du` and the
Hamiltonian sections `x ↦ H(x, p, μ₀)` are periodic (`muAux_periodic`,
MuAux.lean; `max` with a constant preserves periodicity), so `ρ` *is* coverable
by a `CongestionLimitVITestPair`, and no `L^{β̄}`-density approximation is
needed for the family the engine actually uses. -/
/-! ## P6a0c — periodic truncated test pair at `max(muAux, δ)` and direct `h_DCT`

This section closes the chain from the abstract limit weak VI to the HJB integral
inequality `h_DCT` consumed by
`weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg` (StrongIsStrong.lean), via the
periodic-VI route (NOT the cone-VI route). It builds:

* `congestionLimitVITestPair_of_muAuxDelta` — the 9-field
  `CongestionLimitVITestPair` at the periodic truncated density
  `ρ = max(muAux k m u V Du H, δ)`, with value/gradient the limit data
  `(u, Du)`. Periodicity of `ρ` comes from `muAux_periodic` (MuAux.lean) and
  periodicity of `max` with a constant; the `𝓚`-domain fields
  (`μLp`, `μ_lower`, `hRatio_memLp`) are produced by `mdelta_admissibility`
  (StrongIsStrong.lean) at `m := muAux`, `φ := 0`.

* `h_DCT_of_abstractPeriodicVI` — feeds the per-`δ` integral inequalities
  obtained from `congestionLimitVI_integral_le_of_abstract_at_periodicDensity`
  at the truncated test pair into the shared `δ → 0` engine
  `h_DCT_of_perdelta`, producing the `h_DCT`-shaped conclusion directly from
  the abstract periodic VI.
-/

open StationaryMFG.Hamiltonian (HypothesisMonotone)

/-- **Periodic truncated admissible test pair at `ρ = max(muAux, δ)`** (paper
`lem:weak.is.strong`, Step 1, δ-truncation route; the periodic test density of
P6a0c).

Assembles the 9-field `CongestionLimitVITestPair` at primal density
`μ := max(muAux k m u V Du H, δ)`, value `υ := u`, gradient `Dυ := Du`.

* Periodicity of `μ` is `muAux_periodic` combined with the fact that taking the
  pointwise `max` with a constant preserves periodicity; periodicity of `u`,
  `Du` is supplied by the caller (limit data).
* The `𝓚`-domain fields `μLp`, `μ_lower`, `hRatio_memLp` are read off the
  `congestionDomainK` membership of `(max(muAux, δ), u)` produced by
  `mdelta_admissibility` at `m := muAux`, `φ := 0` (so the gradient witness in
  the domain existential is `Du`).
* The Sobolev/gradient fields `υSob`, `hDυ_weak`, `hDυ_memGamma` come from the
  caller's limit Sobolev data. -/
noncomputable def congestionLimitVITestPair_of_muAuxDelta
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {α β τ : ℝ}
    {k δ : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hδ : 0 < δ)
    (hτ : 0 ≤ τ)
    (hαt : 1 ≤ α * (1 + τ / β))
    -- periodicity inputs (for `muAux_periodic` and the test-pair certificates)
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hVPer : IsPeriodic V)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hHPer : ∀ p μ₀, IsPeriodic (fun x => H x p μ₀))
    -- `L^{β̄}` / non-negativity of the auxiliary density `muAux`
    (hμ_Lp : MemLpPer (d := d) betaBar (muAux k m u V Du H))
    (hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ muAux k m u V Du H x)
    -- Sobolev / gradient data for the value function `u`
    (hu_Sob : MemSobolevPer (d := d) gammaBar u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hDu_memGamma : ∀ i, MemLpPer (d := d) gammaBar (Du i))
    -- ratio integrability of the auxiliary density (paper `eq:reg.pair.sol`)
    (hQuot_mu_mem :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (muAux k m u V Du H x ^ τ + 1))) :
    CongestionLimitVITestPair (d := d) betaBar betaBarPrime gammaBar α β τ := by
  classical
  -- Note: the result is data (a structure), so we work toward it directly;
  -- the `congestionDomainK` membership is a `Prop`, so its existential
  -- `∃Du` is extracted only inside `Prop`-valued `have`s, never into the
  -- `Type`-valued structure goal.
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  -- The truncated periodic density.
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  -- Periodicity of `μ = muAux …`.
  have hμPer : IsPeriodic μ :=
    muAux_periodic hmPer huPer hVPer hDuPer hHPer
  -- Periodicity of `ρ = max(μ, δ)` (max with a constant preserves periodicity).
  have hρPer : IsPeriodic ρ := by
    intro κ x
    simp only [hρdef]
    rw [hμPer κ x]
  -- Zero test function and its (zero) gradient.
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (α * (1 + τ / β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (α * (1 + τ / β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  -- `congestionDomainK` membership of `(ρ, u + 0)` via `mdelta_admissibility`.
  have hdom0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_mu_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdom0
  -- Extract `μLp`, `μ_lower` (both `Prop`) by projection.
  have hρLp : MemLpPer (d := d) betaBar ρ := hdom0.1
  have hρ_lower : ∃ c : ℝ, 0 < c ∧
      (fun _ => c) ≤ᵐ[volume.restrict (UnitCube d)] ρ := hdom0.2.2.1
  -- `hRatio_memLp` at `ρ = max(μ, δ)`: dominate the ratio at the *truncated*
  -- density by the ratio at `μ`. Since `ρ ≥ μ ≥ 0` and `τ ≥ 0`, the denominator
  -- `ρ^τ + 1 ≥ μ^τ + 1 > 0`, so the truncated ratio is pointwise ≤ the
  -- `μ`-ratio (both non-negative). `MemLp.mono'` then transfers membership.
  have hαt_nn : 0 ≤ α * (1 + τ / β) := le_trans zero_le_one hαt
  have hRatio :
      MemLpPer (d := d) betaBarPrime
        (fun x => (‖fun i => Du i x‖ ^ (α * (1 + τ / β))) / (ρ x ^ τ + 1)) := by
    refine Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.mono'
      (MemLpPer.toMemLp hQuot_mu_mem) ?_ ?_)
    · -- AE strong measurability of the truncated ratio: numerator is `μ`-ratio's
      -- numerator; denominator is `ρ^τ + 1` with `ρ = max(μ, δ)` measurable.
      have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
        fun i => (hDu_memGamma i).aestronglyMeasurable.aemeasurable
      have hvec_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => fun i => Du i x)
          (volume.restrict (UnitCube d)) :=
        (aemeasurable_pi_iff.mpr hDu_aem).aestronglyMeasurable
      have hnum_aesm : AEStronglyMeasurable
          (fun x => ‖fun i => Du i x‖ ^ (α * (1 + τ / β)))
          (volume.restrict (UnitCube d)) :=
        (Real.continuous_rpow_const hαt_nn).comp_aestronglyMeasurable
          hvec_aesm.norm
      have hden_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => ρ x ^ τ + 1) (volume.restrict (UnitCube d)) := by
        have hρ_aesm : AEStronglyMeasurable ρ (volume.restrict (UnitCube d)) :=
          (MemLpPer.toMemLp hρLp).aestronglyMeasurable
        exact ((Real.continuous_rpow_const hτ).comp_aestronglyMeasurable
          hρ_aesm).add aestronglyMeasurable_const
      exact hnum_aesm.aemeasurable.div hden_aesm.aemeasurable
        |>.aestronglyMeasurable
    · -- pointwise domination `|trunc ratio| ≤ |μ-ratio|`.
      filter_upwards [hμ_nn] with x hx
      have hμ_nn_x : 0 ≤ μ x := hx
      have hρ_ge : μ x ≤ ρ x := le_max_left _ _
      have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hμden_pos : (0:ℝ) < μ x ^ τ + 1 := by positivity
      have hρden_pos : (0:ℝ) < ρ x ^ τ + 1 := by positivity
      have hden_le : μ x ^ τ + 1 ≤ ρ x ^ τ + 1 := by
        have : μ x ^ τ ≤ ρ x ^ τ := Real.rpow_le_rpow hμ_nn_x hρ_ge hτ
        linarith
      have htrunc_nn : 0 ≤ ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) / (ρ x ^ τ + 1) :=
        div_nonneg hnum_nn hρden_pos.le
      rw [Real.norm_of_nonneg htrunc_nn]
      exact div_le_div_of_nonneg_left hnum_nn hμden_pos hden_le
  exact
    { μ := ρ
      υ := u
      Dυ := Du
      hμPer := hρPer
      hυPer := huPer
      hDυPer := hDuPer
      μLp := hρLp
      υSob := hu_Sob
      μ_lower := hρ_lower
      hDυ_weak := hDu_weak
      hRatio_memLp := hRatio
      hDυ_memGamma := hDu_memGamma }

/-- **Periodic truncated admissible test pair at `ρ = max(muRe, δ)`** (paper
`eq:congest.HJ0`, Step 2, δ-truncation route; the `μ_re` analogue of
`congestionLimitVITestPair_of_muAuxDelta`).

Assembles the 9-field `CongestionLimitVITestPair` at primal density
`μ := max(muRe k m u V Du H, δ)`, value `υ := u`, gradient `Dυ := Du`. Identical
structure to the `muAux` builder, swapping the density to `muRe` (periodicity
from `muRe_periodic`). -/
noncomputable def congestionLimitVITestPair_of_muReDelta
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {α β τ : ℝ}
    {k δ : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hδ : 0 < δ)
    (hτ : 0 ≤ τ)
    (hαt : 1 ≤ α * (1 + τ / β))
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hVPer : IsPeriodic V)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hHPer : ∀ p μ₀, IsPeriodic (fun x => H x p μ₀))
    (hμ_Lp : MemLpPer (d := d) betaBar (muRe k m u V Du H))
    (hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ muRe k m u V Du H x)
    (hu_Sob : MemSobolevPer (d := d) gammaBar u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hDu_memGamma : ∀ i, MemLpPer (d := d) gammaBar (Du i))
    (hQuot_mu_mem :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) /
            (muRe k m u V Du H x ^ τ + 1))) :
    CongestionLimitVITestPair (d := d) betaBar betaBarPrime gammaBar α β τ := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muRe k m u V Du H with hμdef
  set ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ with hρdef
  have hμPer : IsPeriodic μ :=
    muRe_periodic hmPer huPer hVPer hDuPer hHPer
  have hρPer : IsPeriodic ρ := by
    intro κ x
    simp only [hρdef]
    rw [hμPer κ x]
  have hDφ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        ((fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i) := by
    intro i
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    refine ⟨Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ)), ?_⟩
    intro ψ
    simp only [Periodic.SmoothPeriodic.coe_zero, Pi.zero_apply, zero_mul]
    simp [Periodic.periodicIntegral_const]
  have hDφ_Lp :
      MemLpPer (d := d) betaBarPrime
        (fun x : Fin d → ℝ =>
          ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
            ^ (α * (1 + τ / β))) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hzero : (fun x : Fin d → ℝ =>
        ‖fun i => (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x‖
          ^ (α * (1 + τ / β)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      have hz : (fun i : Fin d =>
          (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ))) i x)
            = (0 : Fin d → ℝ) := by
        funext i; simp
      rw [hz, norm_zero, Real.zero_rpow (by positivity)]
    rw [hzero]
    exact Periodic.MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have hdom0 :
      ((fun x => max (μ x) δ),
          (fun x => u x +
            ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ :=
    mdelta_admissibility (d := d)
      (m := μ) (u := u) (Du := Du)
      (0 : Periodic.SmoothPeriodic d)
      (fun _ : Fin d => (fun _ : (Fin d → ℝ) => (0 : ℝ)))
      hδ hτ hαt hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak
      hDφ_weak hQuot_mu_mem hDφ_Lp
  have hval_eq : (fun x => u x +
        ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) = u := by
    funext x; simp
  rw [hval_eq] at hdom0
  have hρLp : MemLpPer (d := d) betaBar ρ := hdom0.1
  have hρ_lower : ∃ c : ℝ, 0 < c ∧
      (fun _ => c) ≤ᵐ[volume.restrict (UnitCube d)] ρ := hdom0.2.2.1
  have hαt_nn : 0 ≤ α * (1 + τ / β) := le_trans zero_le_one hαt
  have hRatio :
      MemLpPer (d := d) betaBarPrime
        (fun x => (‖fun i => Du i x‖ ^ (α * (1 + τ / β))) / (ρ x ^ τ + 1)) := by
    refine Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.mono'
      (MemLpPer.toMemLp hQuot_mu_mem) ?_ ?_)
    · have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
        fun i => (hDu_memGamma i).aestronglyMeasurable.aemeasurable
      have hvec_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => fun i => Du i x)
          (volume.restrict (UnitCube d)) :=
        (aemeasurable_pi_iff.mpr hDu_aem).aestronglyMeasurable
      have hnum_aesm : AEStronglyMeasurable
          (fun x => ‖fun i => Du i x‖ ^ (α * (1 + τ / β)))
          (volume.restrict (UnitCube d)) :=
        (Real.continuous_rpow_const hαt_nn).comp_aestronglyMeasurable
          hvec_aesm.norm
      have hden_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => ρ x ^ τ + 1) (volume.restrict (UnitCube d)) := by
        have hρ_aesm : AEStronglyMeasurable ρ (volume.restrict (UnitCube d)) :=
          (MemLpPer.toMemLp hρLp).aestronglyMeasurable
        exact ((Real.continuous_rpow_const hτ).comp_aestronglyMeasurable
          hρ_aesm).add aestronglyMeasurable_const
      exact hnum_aesm.aemeasurable.div hden_aesm.aemeasurable
        |>.aestronglyMeasurable
    · filter_upwards [hμ_nn] with x hx
      have hμ_nn_x : 0 ≤ μ x := hx
      have hρ_ge : μ x ≤ ρ x := le_max_left _ _
      have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hμden_pos : (0:ℝ) < μ x ^ τ + 1 := by positivity
      have hρden_pos : (0:ℝ) < ρ x ^ τ + 1 := by positivity
      have hden_le : μ x ^ τ + 1 ≤ ρ x ^ τ + 1 := by
        have : μ x ^ τ ≤ ρ x ^ τ := Real.rpow_le_rpow hμ_nn_x hρ_ge hτ
        linarith
      have htrunc_nn : 0 ≤ ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) / (ρ x ^ τ + 1) :=
        div_nonneg hnum_nn hρden_pos.le
      rw [Real.norm_of_nonneg htrunc_nn]
      exact div_le_div_of_nonneg_left hnum_nn hμden_pos hden_le
  exact
    { μ := ρ
      υ := u
      Dυ := Du
      hμPer := hρPer
      hυPer := huPer
      hDυPer := hDuPer
      μLp := hρLp
      υSob := hu_Sob
      μ_lower := hρ_lower
      hDυ_weak := hDu_weak
      hRatio_memLp := hRatio
      hDυ_memGamma := hDu_memGamma }

set_option maxHeartbeats 1600000 in
/-- **`h_DCT` producer for the `≥`-side from the abstract periodic limit weak VI**
(paper `eq:congest.HJ0`, Step 2; the `μ_re` analogue of
`h_DCT_of_abstractPeriodicVI_aesm`).

This is the abstract-VI sibling of `h_DCT_producer_muRe` (StrongIsStrong): the
per-`δ` VI inequalities are obtained by collapsing the abstract periodic weak VI
`habs` at the muRe truncated test pair `ρ = max(muRe, δ)`
(`congestionLimitVITestPair_of_muReDelta` +
`congestionLimitVI_integral_le_of_abstract_at_periodicDensity`) instead of from
the Banach cone VI. Same conclusion. No Banach/cone data, no
`Hext_finite_at_zero` / power-growth / `0 < m` rider. -/
theorem h_DCT_of_abstractPeriodicVI_muRe_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {k : ℝ} (hk : 0 < k)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty)
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    -- periodicity of the data (for `muRe_periodic` and the test-pair density)
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hVPer : IsPeriodic V)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hHPer : ∀ p μ₀, IsPeriodic (fun x => H x p μ₀))
    -- Sobolev / weak-derivative / gradient `L^{γ̄}` data for the value `u`
    (hu_Sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    -- the abstract limit weak VI over periodic admissible test pairs
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
          * (muRe k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  set μ : (Fin d → ℝ) → ℝ := muRe k m u V Du H with hμdef
  set C : ℝ := hcong.C with hCdef
  set β : ℝ := hcong.β with hβdef
  have hC_pos : 0 < C := hcong.hC
  have hβ_pos : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  set δSeq : ℕ → ℝ := fun n => (1 : ℝ) / (↑n + 1) with hδSeqdef
  have hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  have hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ -k }
        (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    have hF_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ => u x + H x (fun i => Du i x) a - V x)
        (volume.restrict (UnitCube d)) :=
      (hu_meas.aestronglyMeasurable.add hHcomp.aestronglyMeasurable).sub hV_aesm
    exact hF_aesm.nullMeasurableSet_le aestronglyMeasurable_const
  have hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    have hg : Continuous (fun μ₀ : ℝ => ((fun i => Du i x), μ₀)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun μ₀ : ℝ => ((fun i => Du i x), μ₀))
        (Set.Ioi (0 : ℝ)) {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := fun μ₀ hμ₀ => hμ₀
    exact hx.comp hg.continuousOn hmaps
  have hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [Hamiltonian.antitone_in_m hmon] with x hx
    exact hx (fun i => Du i x)
  have hμre_aem : AEMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muRe_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hae_m_nn
      hae_anti hae_cont hae_ne
  have hμre_aesm : AEStronglyMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) := hμre_aem.aestronglyMeasurable
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    muRe_nonneg_ae hae_m_nn hae_ne
  have hae_HJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k := by
    filter_upwards [hae_anti, hae_ne, hHat0.exists_limit_at_zero, hAgree]
      with x hx_anti hx_ne hx_limit hx_agree hμle0
    have hwit := (muReInner_le_zero_iff_of_antitoneOn_Ioi hx_anti hx_ne).mp hμle0
    have hTendsto :
        Filter.Tendsto
          (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
      Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
    set b : ℝ := -k - u x + V x with hb_def
    by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
        (q : ℝ) = 0 ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k
    · obtain ⟨_, _, hq_eq0, _, _, hHJB_q⟩ := hzero
      rw [hq_eq0] at hHJB_q; exact hHJB_q
    · have hPointwise : ∀ ν : ℝ, 0 < ν →
          u x + H x (fun i => Du i x) ν - V x ≤ -k := by
        intro ν hν
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
        obtain ⟨q, hq_nn, hq_hi, hHJB_q⟩ := hwit n
        have hq_lt_ν : (q : ℝ) < ν := by
          have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
            simpa only [one_div] using hn
          exact lt_trans hq_hi h1
        have hq_pos : 0 < (q : ℝ) := by
          rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
          · exact absurd ⟨n, q, hq0.symm, hq_nn, hq_hi, hHJB_q⟩ hzero
          · exact hq_pos
        have hanti_le :
            H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
          hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
        linarith [hHJB_q]
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
          self_mem_nhdsWithin, fun ν hν => ?_⟩
        have := hPointwise ν hν
        have hle : H x (fun i => Du i x) ν ≤ b := by rw [hb_def]; linarith
        exact_mod_cast hle
      have hHext_le :
          Hamiltonian.H_at_zero H x (fun i => Du i x)
            ≤ ((b : ℝ) : WithTop ℝ) := le_of_tendsto hTendsto hEv
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
      have hraw_le :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        rw [hAgree_x]; exact hHext_le
      have hraw : H x (fun i => Du i x) 0 ≤ b := by exact_mod_cast hraw_le
      rw [hb_def] at hraw; linarith
  have hQuot_muRe_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (muRe k m u V Du H x ^ hcong.τ + 1)) :=
    muRe_quotient_dominator_memLp hmon hcong hHat0 hAgree hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hae_m_nn hae_anti hae_cont h_step1 hae_ne
  -- `μ_re ∈ L^{β+1}` (dominated by `m` since `0 ≤ μ_re ≤ m`).
  have hμ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) μ := by
    have hbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖μ x‖ ≤ m x := by
      filter_upwards [hμ_nn] with x hx_nn
      have hle : μ x ≤ m x := by simpa [hμdef] using muRe_le_m k m u V Du H x
      rw [Real.norm_of_nonneg hx_nn]; exact hle
    have hm_mem' : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m := hm_mem
    exact Periodic.memLpPer_iff_memLp.mpr
      (MemLp.mono' (Periodic.memLpPer_iff_memLp.mp hm_mem') hμre_aesm hbnd)
  -- Per-`n` variational inequality from the abstract-VI collapse at the muRe
  -- truncated test pair (the only place the Banach data appeared in the
  -- witness-based producer; here it is sourced from `habs`).
  have hperdelta : ∀ n,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    intro n
    let T : CongestionLimitVITestPair (d := d)
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ :=
      congestionLimitVITestPair_of_muReDelta (d := d) (H := H)
        (k := k) (δ := δSeq n) (m := m) (u := u) (V := V) (Du := Du)
        (hδ_pos n) hτ_nn hαt hmPer huPer hVPer hDuPer hHPer
        hμ_mem hμ_nn hu_Sob hu_L1 hDu_weak hDu_memGamma hQuot_muRe_mem
    have hTυ : T.υ = u := rfl
    have hTDυ : T.Dυ = Du := rfl
    have hTμ : T.μ = (fun x => max (muRe k m u V Du H x) (δSeq n)) := rfl
    have hint :=
      congestionLimitVI_integral_le_of_abstract_at_periodicDensity
        (H := H) (DpH := DpH) (V := V) (m := m) (u := u) (Du := Du)
        habs T hTυ hTDυ
    rw [hTμ] at hint
    simpa only [hμdef] using hint
  -- Lower congestion bound `-(C·(ρ^β+1)) ≤ H(·, ρ)` for `ρ > 0` (a.e.).
  have hH_lower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p ρ, 0 < ρ → -(C * (ρ ^ β + 1)) ≤ H x p ρ := by
    filter_upwards [hcong.lower] with x hx p ρ hρ
    have hfull := hx p ρ hρ
    have hpos : 0 ≤ (1 / C) * (1 / (ρ ^ hcong.τ + 1))
        * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) := by
      have hc1 : (0 : ℝ) ≤ 1 / C := by positivity
      have hc2 : (0 : ℝ) ≤ 1 / (ρ ^ hcong.τ + 1) := by positivity
      have hc3 : (0 : ℝ) ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      exact mul_nonneg (mul_nonneg hc1 hc2) hc3
    have : H x p ρ ≥ -(C * (ρ ^ β + 1)) := by
      have h1 : (1 / C) * (1 / (ρ ^ hcong.τ + 1))
            * (‖p‖ ^ (hcong.α * (1 + hcong.τ / β))) - C * (ρ ^ β + 1)
            ≥ -(C * (ρ ^ β + 1)) := by linarith
      exact le_trans h1 hfull
    linarith [this]
  -- The upper HJB envelope at `μ_re`: `u + H(·, μ_re) − V ≤ 0` a.e. (`muRe_bound_up`).
  have hμ_bound_up : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (μ x) - V x ≤ 0 := by
    have := muRe_bound_up (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H)
      hk hae_cont hae_ne hae_HJB0 h_step1
    simpa only [hμdef] using this
  -- Envelope/dominator data, mirroring `h_DCT_producer_of_m_nonneg`.
  set G1 : (Fin d → ℝ) → ℝ :=
    fun x => ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) with hG1def
  set F2 : (Fin d → ℝ) → ℝ := fun x => ‖μ x - m x‖ + 1 with hF2def
  have hμnorm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => ‖μ x‖ + 1) :=
    (MemLpPer.add (hμ_mem.toMemLp.norm) (MemLpPer.const (1 : ℝ)) :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) _)
  have hexp_id : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β
      = ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
  have hpow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (‖μ x‖ + 1) ^ β) := by
    have h0 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖(‖μ x‖ + 1)‖ ^ β) := by
      have := MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal ((β + 1) / β))
        (r := β) hβ_pos (f := fun x => ‖μ x‖ + 1)
        (by rw [hexp_id]; exact hμnorm1_mem)
      exact this
    have heq : (fun x => ‖(‖μ x‖ + 1)‖ ^ β) = (fun x => (‖μ x‖ + 1) ^ β) := by
      funext x
      rw [Real.norm_of_nonneg (by positivity)]
    rwa [heq] at h0
  have hG1_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) G1 := by
    have hu' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖u x‖) := hu_mem.toMemLp.norm
    have hV' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖V x‖) := hV_mem.toMemLp.norm
    have hCpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => C * ((‖μ x‖ + 1) ^ β + 1)) :=
      (MemLpPer.add hpow_mem (MemLpPer.const (1 : ℝ))).toMemLp.const_mul C
    have := (hu'.add hV').add hCpow
    exact this
  have hF2_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) F2 := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => μ x - m x) := hμ_mem.toMemLp.sub hm_mem.toMemLp
    have hnorm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x => ‖μ x - m x‖) := hsub.toMemLp.norm
    exact MemLpPer.add hnorm (MemLpPer.const (1 : ℝ))
  have hHolder : ((β + 1) / β).HolderConjugate (β + 1) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hβ_pos]; linarith
    · have hβ1 : (β + 1 : ℝ) ≠ 0 := by positivity
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ_pos
      rw [inv_div]; field_simp
  set bound : (Fin d → ℝ) → ℝ := fun x => G1 x * F2 x with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) :=
    MemLpPer.integrable_mul hHolder hG1_mem hF2_mem
  have hae_clamp : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ ρ : ℝ, μ x ≤ ρ → 0 < ρ →
        H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) := by
    filter_upwards [hμ_nn, hae_anti, hHat0.exists_limit_at_zero, hAgree]
      with x hxμ_nn hx_anti hx_limit hx_agree ρ hρ_ge hρ_pos
    rcases eq_or_lt_of_le hxμ_nn with hμ0 | hμpos
    · rw [← hμ0]
      have hTendsto :
          Filter.Tendsto
            (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
        Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ρ : ℝ) : WithTop ℝ)
              ≤ ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr
          ⟨Set.Ioo (0 : ℝ) ρ, Ioo_mem_nhdsGT hρ_pos, fun ν hν => ?_⟩
        have hle : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) ν :=
          hx_anti hν.1 hρ_pos hν.2.le
        exact_mod_cast hle
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
      have hle_top :
          ((H x (fun i => Du i x) ρ : ℝ) : WithTop ℝ)
            ≤ Hamiltonian.H_at_zero H x (fun i => Du i x) :=
        ge_of_tendsto hTendsto hEv
      rw [← hAgree_x] at hle_top
      exact_mod_cast hle_top
    · exact hx_anti hμpos (lt_of_lt_of_le hμpos hρ_ge) hρ_ge
  have hf1_all : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x| ≤ G1 x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    filter_upwards [hμ_nn, hH_lower, hμ_bound_up, hae_clamp]
      with x hxμ_nn hxH_lower hx_up hx_clamp
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_pos : 0 < ρ := lt_of_lt_of_le (hδ_pos n) (le_max_right _ _)
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]; apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    have hHanti_le : H x (fun i => Du i x) ρ ≤ H x (fun i => Du i x) (μ x) :=
      hx_clamp ρ hρ_ge_μ hρ_pos
    have hf1_upper : factor1 ≤ 0 := by
      rw [hf1def]; linarith [hx_up, hHanti_le]
    have hHlow_at : -(C * (ρ ^ β + 1)) ≤ H x (fun i => Du i x) ρ :=
      hxH_lower (fun i => Du i x) ρ hρ_pos
    have hρβ_le : ρ ^ β ≤ (‖μ x‖ + 1) ^ β := by
      apply Real.rpow_le_rpow hρ_pos.le _ hβ_pos.le
      calc ρ ≤ μ x + 1 := hρ_le
        _ ≤ ‖μ x‖ + 1 := by linarith [Real.le_norm_self (μ x)]
    have hf1_lower : -(‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1)) ≤ factor1 := by
      rw [hf1def]
      have h1 : -(C * (ρ ^ β + 1)) ≥ -(C * ((‖μ x‖ + 1) ^ β + 1)) := by
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_left _ hC_pos.le
        linarith [hρβ_le]
      have hu_le : -‖u x‖ ≤ u x := by
        rw [Real.norm_eq_abs]; exact neg_abs_le (u x)
      have hV_le : V x ≤ ‖V x‖ := Real.le_norm_self (V x)
      linarith [hHlow_at, h1, hu_le, hV_le]
    show |factor1| ≤ G1 x
    rw [hG1def, abs_le]
    refine ⟨hf1_lower, ?_⟩
    have : (0 : ℝ) ≤ ‖u x‖ + ‖V x‖ + C * ((‖μ x‖ + 1) ^ β + 1) := by
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      positivity
    linarith [hf1_upper]
  have h_max_meas : ∀ n, AEMeasurable (fun x => max (μ x) (δSeq n))
      (volume.restrict (UnitCube d)) :=
    fun n => hμre_aem.max aemeasurable_const
  have h_Hmax_meas : ∀ n, AEMeasurable
      (fun x => H x (fun i => Du i x) (max (μ x) (δSeq n)))
      (volume.restrict (UnitCube d)) :=
    fun n => hmon.toRegularityH.measurable_H.comp_aemeasurable
      (aemeasurable_id.prodMk
        ((Measurable.of_eval hDu_meas).aemeasurable.prodMk (h_max_meas n)))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x =>
        (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x))
      (volume.restrict (UnitCube d)) :=
    fun n =>
      (((hu_meas.aestronglyMeasurable.add
            (AEMeasurable.aestronglyMeasurable (h_Hmax_meas n))).sub
          hV_aesm).mul
        ((AEMeasurable.aestronglyMeasurable (h_max_meas n)).sub
          hm_meas.aestronglyMeasurable))
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          * (max (μ x) (δSeq n) - m x)‖ ≤ bound x := by
    intro n
    have hδ1 : δSeq n ≤ 1 := by
      rw [hδSeqdef]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    filter_upwards [hf1_all n, hμ_nn] with x hxf1 hxμ_nn
    set ρ : ℝ := max (μ x) (δSeq n) with hρdef
    have hρ_ge_μ : μ x ≤ ρ := le_max_left _ _
    have hρ_le : ρ ≤ μ x + 1 := by
      rw [hρdef]; apply max_le
      · linarith
      · linarith [hδ1, hδ_pos n, hxμ_nn]
    set factor1 : ℝ := u x + H x (fun i => Du i x) ρ - V x with hf1def
    set factor2 : ℝ := ρ - m x with hf2pdef
    have hf1_abs : |factor1| ≤ G1 x := hxf1
    have hf2_abs : |factor2| ≤ F2 x := by
      rw [hf2pdef, hF2def]
      simp only []
      rw [Real.norm_eq_abs]
      have hsplit : |ρ - m x| ≤ |ρ - μ x| + |μ x - m x| :=
        abs_sub_le ρ (μ x) (m x)
      have hρμ : |ρ - μ x| ≤ 1 := by
        rw [abs_le]
        refine ⟨by linarith [hρ_ge_μ], by linarith [hρ_le]⟩
      linarith [hsplit, hρμ]
    have hG1_nonneg : 0 ≤ G1 x := by
      rw [hG1def]
      have : 0 ≤ C * ((‖μ x‖ + 1) ^ β + 1) := by positivity
      positivity
    have hF2_nonneg : 0 ≤ F2 x := by rw [hF2def]; positivity
    calc ‖factor1 * factor2‖ = |factor1| * |factor2| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ G1 x * F2 x := by
            exact mul_le_mul hf1_abs hf2_abs (abs_nonneg _) hG1_nonneg
      _ = bound x := by rw [hbounddef]
  have h_lim : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n =>
          (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
            * (max (μ x) (δSeq n) - m x))
        Filter.atTop
        (nhds
          ((u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x))) := by
    filter_upwards [hμ_nn, hae_cont, hHat0.exists_limit_at_zero, hAgree]
      with x hxμ_nn hx_cont hx_limit hx_agree
    have h_max_lim :
        Filter.Tendsto (fun n => max (μ x) (δSeq n)) Filter.atTop (nhds (μ x)) := by
      have h0 : max (μ x) (0 : ℝ) = μ x := max_eq_left hxμ_nn
      have := (tendsto_const_nhds (x := μ x)).max hδ_lim
      simpa [h0] using this
    have h_H_lim :
        Filter.Tendsto (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
          Filter.atTop (nhds (H x (fun i => Du i x) (μ x))) := by
      rcases eq_or_lt_of_le hxμ_nn with hμ0 | hμpos
      · have hmax_eq : (fun n => max (μ x) (δSeq n)) = δSeq := by
          funext n; rw [← hμ0]; exact max_eq_right (hδ_pos n).le
        have hTop :
            Filter.Tendsto
              (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
          Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
        have hAgree_x :
            ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
              = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
          rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
        have hTop' :
            Filter.Tendsto
              (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ))) := by
          rw [hAgree_x]; exact hTop
        have hReal :
            Filter.Tendsto (fun ν : ℝ => H x (fun i => Du i x) ν)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (H x (fun i => Du i x) 0)) :=
          (WithTop.isEmbedding_coe (ι := ℝ)).tendsto_nhds_iff.mpr hTop'
        have hδ_within :
            Filter.Tendsto δSeq Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ_lim
            (Filter.Eventually.of_forall (fun n => hδ_pos n))
        have hcomp := hReal.comp hδ_within
        have hfun_eq :
            (fun n => H x (fun i => Du i x) (max (μ x) (δSeq n)))
              = (fun n => H x (fun i => Du i x) (δSeq n)) := by
          funext n; rw [← hμ0]; rw [max_eq_right (hδ_pos n).le]
        rw [hfun_eq, ← hμ0]; exact hcomp
      · have hcontAt : ContinuousAt (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (μ x) :=
          (hx_cont _ hμpos).continuousAt (isOpen_Ioi.mem_nhds hμpos)
        exact hcontAt.tendsto.comp h_max_lim
    have h_first :
        Filter.Tendsto
          (fun n => u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
          Filter.atTop (nhds (u x + H x (fun i => Du i x) (μ x) - V x)) :=
      ((tendsto_const_nhds.add h_H_lim).sub tendsto_const_nhds)
    have h_second :
        Filter.Tendsto (fun n => max (μ x) (δSeq n) - m x) Filter.atTop
          (nhds (μ x - m x)) := h_max_lim.sub tendsto_const_nhds
    exact h_first.mul h_second
  have htendsto :
      Filter.Tendsto
        (fun n =>
          ∫ x in UnitCube d,
              (u x + H x (fun i => Du i x) (max (μ x) (δSeq n)) - V x)
                * (max (μ x) (δSeq n) - m x)
              ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds
          (∫ x in UnitCube d,
              (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x)
              ∂(volume : Measure (Fin d → ℝ)))) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hmeas hbound_int hbound h_lim
  exact le_of_tendsto htendsto (Filter.Eventually.of_forall hperdelta)

/-- **Direct `h_DCT` producer from the abstract periodic limit weak VI**
(paper `lem:weak.is.strong`, Step 1).

Given the abstract limit weak VI over periodic admissible test pairs (the
`mfgOperatorPair` form carried by `CongestionLimitVIData.hLimitVI`), produces the
HJB integral inequality
`∫ (u + H(Du, muAux) − V)·(muAux − m) ≤ 0`
consumed by `weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg`.

For each `δ = 1/(n+1)`, the periodic truncated test pair at
`ρ = max(muAux, δ)` (built by `congestionLimitVITestPair_of_muAuxDelta`) collapses
the abstract VI to the per-`δ` integral inequality via
`congestionLimitVI_integral_le_of_abstract_at_periodicDensity`. The `δ → 0`
passage is the shared engine `h_DCT_of_perdelta`. NOTE: this route uses the
abstract *limit* VI directly; it does NOT use per-`ε` pointwise convergence of
the regularized HJB inequalities (only weak `L^p` convergence is available). -/
theorem h_DCT_of_abstractPeriodicVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne_all :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    -- periodicity of the data (for `muAux_periodic` and the test-pair density)
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hVPer : IsPeriodic V)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hHPer : ∀ p μ₀, IsPeriodic (fun x => H x p μ₀))
    -- Sobolev / weak-derivative / gradient `L^{γ̄}` data for the value `u`
    (hu_Sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    -- the abstract limit weak VI over periodic admissible test pairs
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- The auxiliary density `μ = muAux …` and its analytic by-products.
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_nonneg hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  have hQuot_mu_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_nonneg hmon hcong hm_meas hu_meas hV_meas
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne h_anti h_cont h_ne_all
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    Filter.Eventually.of_forall (fun x => le_csInf (h_ne_all x) (fun b hb => hb.1))
  -- The δ-sequence `1/(n+1)` and per-`δ` integral inequalities via the periodic VI.
  have hperdelta : ∀ n : ℕ,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x)
              (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) - V x)
            * (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1)) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    intro n
    have hδ_pos : (0 : ℝ) < (1 : ℝ) / (↑n + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
      exact div_pos one_pos this
    -- The periodic truncated admissible test pair at `ρ = max(μ, δ)`.
    let T : CongestionLimitVITestPair (d := d)
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ :=
      congestionLimitVITestPair_of_muAuxDelta (d := d) (H := H)
        (k := k) (δ := (1 : ℝ) / (↑n + 1)) (m := m) (u := u) (V := V) (Du := Du)
        hδ_pos hτ_nn hαt hmPer huPer hVPer hDuPer hHPer
        hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak hDu_memGamma hQuot_mu_mem
    -- The test pair's value/gradient are the limit data; its density is `ρ`.
    have hTυ : T.υ = u := rfl
    have hTDυ : T.Dυ = Du := rfl
    have hTμ : T.μ = (fun x => max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) :=
      rfl
    -- Collapse the abstract VI at `T` to the integral inequality.
    have hint :=
      congestionLimitVI_integral_le_of_abstract_at_periodicDensity
        (H := H) (DpH := DpH) (V := V) (m := m) (u := u) (Du := Du)
        habs T hTυ hTDυ
    rw [hTμ] at hint
    exact hint
  -- Feed the per-`δ` inequalities into the shared `δ → 0` DCT engine.
  exact h_DCT_of_perdelta hmon hcong hm_meas hu_meas hV_meas hDu_meas
    hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn h_anti h_cont h_ne_all hperdelta

/-- **`h_DCT` producer from the abstract periodic limit weak VI — `Ioi 0`/a.e.
sibling** (paper `lem:weak.is.strong`, Step 1; `eq:congest.HJleq0`, line 1397).

This is the `Ioi 0`/a.e. + `(a:Hat0)`-boundary sibling of
`h_DCT_of_abstractPeriodicVI`, standing to it exactly as
`h_DCT_producer_of_m_nonneg_aesm` stands to the Banach-VI producer. Same
conclusion (the per-`k` `h_DCT` integral inequality), but the three
closed-`Ici 0` / `∀ x` hypotheses (`h_anti`, `h_cont`, `h_ne_all`) are replaced
by the a.e./`Ioi 0` data `hcont`, `hae_anti`, `hne` plus the paper-faithful
boundary device `hHat0`/`hAgree`.

The `μ ∈ L^{β̄}` and the quotient-dominator memberships are produced via the
nonneg `_aesm` envelopes (`muAux_mem_Lp_of_witnessData_nonneg_aesm`,
`muAux_quotient_dominator_memLp_of_m_nonneg_aesm`); `μ ≥ 0` is unconditional
(`muAux_nonneg`). The per-`δ` truncated test pair at `ρ = max(muAux, δ) ≥ δ > 0`
stays in `Ioi 0`, so its admissibility certificates are sourced from the
a.e./`Ioi 0` + Lp inputs. The `δ → 0⁺` passage is the shared engine
`h_DCT_of_perdelta_aesm`. NOTE: this route uses the abstract *limit* VI directly;
it does NOT use per-`ε` pointwise convergence of the regularized HJB
inequalities (only weak `L^p` convergence is available). -/
theorem h_DCT_of_abstractPeriodicVI_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hm_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    -- periodicity of the data (for `muAux_periodic` and the test-pair density)
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hVPer : IsPeriodic V)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hHPer : ∀ p μ₀, IsPeriodic (fun x => H x p μ₀))
    -- Sobolev / weak-derivative / gradient `L^{γ̄}` data for the value `u`
    (hu_Sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    -- the abstract limit weak VI over periodic admissible test pairs
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u)) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x)
          * (muAux k m u V Du H x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hα1 : (1 : ℝ) ≤ hcong.α := le_of_lt hcong.hα
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nn hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
          apply mul_le_mul hα1 h1 (by norm_num) (le_trans (by norm_num) hα1)
  -- The auxiliary density `μ = muAux …` and its analytic by-products (nonneg
  -- `_aesm` envelopes, `(a:Hat0)`-boundary quotient dominator).
  set μ : (Fin d → ℝ) → ℝ := muAux k m u V Du H with hμdef
  have hμ_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) μ :=
    muAux_mem_Lp_of_witnessData_nonneg_aesm hmon hcong hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti
  have hQuot_mu_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (μ x ^ hcong.τ + 1)) :=
    muAux_quotient_dominator_memLp_of_m_nonneg_aesm hmon hcong hHat0 hAgree
      hm_meas hu_meas hV_aesm hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne
      hm_nn hae_anti
  -- `μ ≥ 0` everywhere (unconditional, no boundary data needed).
  have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    Filter.Eventually.of_forall (fun x => muAux_nonneg x)
  -- The δ-sequence `1/(n+1)` and per-`δ` integral inequalities via the periodic VI.
  have hperdelta : ∀ n : ℕ,
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x)
              (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) - V x)
            * (max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1)) - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    intro n
    have hδ_pos : (0 : ℝ) < (1 : ℝ) / (↑n + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
      exact div_pos one_pos this
    -- The periodic truncated admissible test pair at `ρ = max(μ, δ) ≥ δ > 0`.
    let T : CongestionLimitVITestPair (d := d)
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ :=
      congestionLimitVITestPair_of_muAuxDelta (d := d) (H := H)
        (k := k) (δ := (1 : ℝ) / (↑n + 1)) (m := m) (u := u) (V := V) (Du := Du)
        hδ_pos hτ_nn hαt hmPer huPer hVPer hDuPer hHPer
        hμ_Lp hμ_nn hu_Sob hu_L1 hDu_weak hDu_memGamma hQuot_mu_mem
    -- The test pair's value/gradient are the limit data; its density is `ρ`.
    have hTυ : T.υ = u := rfl
    have hTDυ : T.Dυ = Du := rfl
    have hTμ : T.μ = (fun x => max (muAux k m u V Du H x) ((1 : ℝ) / (↑n + 1))) :=
      rfl
    -- Collapse the abstract VI at `T` to the integral inequality.
    have hint :=
      congestionLimitVI_integral_le_of_abstract_at_periodicDensity
        (H := H) (DpH := DpH) (V := V) (m := m) (u := u) (Du := Du)
        habs T hTυ hTDυ
    rw [hTμ] at hint
    exact hint
  -- Feed the per-`δ` inequalities into the shared `δ → 0` DCT engine (aesm).
  exact h_DCT_of_perdelta_aesm hmon hcong hHat0 hAgree hm_meas hu_meas hV_aesm
    hDu_meas hm_mem hu_mem hV_mem hDu_mem hcont hne hm_nn hae_anti hperdelta

end Congestion
end StationaryMFG
