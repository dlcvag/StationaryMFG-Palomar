module

public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext
public import StationaryMFG.Theorems.SimplePower.Banach.UniformSequence
public import StationaryMFG.Theorems.SimplePower.Banach.Closure
public import StationaryMFG.Periodic.Separability
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-!
# T7 — `RegularizedSequenceData` producer

This module discharges Phase-4 task
`infra-P4-rebuild-T7-regularizedSequence`.

Given the paper hypotheses `(hmon, hpow, hV, hExp)`, build a per-`k`
sequence of `RegularizedBareSolution` records (from T4) at parameter
`ε_k := 1 / (k + 1)`, together with a uniform Banach-pair-norm bound on
the bridged Banach pair `(toLp m_k, toLpSobolev u_k Du_k)`.

## Structure

* `banachPairOfBare` — bridge bare `(m, u, Du)` plus their `MemLpPer` /
  `MemSobolevPer` certificates and the `MemLpPer` certificate on each
  gradient component into the `XBanach d βBarReal γBarReal` Banach
  pair, via Mathlib's `MemLp.toLp` and our `MemSobolevPer.toLpSobolev`.
* `aprioriInputs_of_regularizedBareSolution` — package a
  `RegularizedBareSolution` together with an `AprioriInputAuxHyps`
  paper-hypothesis bundle into an `AprioriDischargeInputs` consumable
  by `apriori_at_eps`. This is the bare-function analogue of F.3's
  `aprioriInputsAtEps`, taking the bare-function record from T4 in
  place of the `BanachOutputData` bundle.
* `RegularizedSequenceData` — the headline record: an ε-sequence with
  `ε_k → 0`, a per-`k` `RegularizedBareSolution`, and a uniform
  Banach-pair-norm bound `‖banachPairOfBare (sol k).m (sol k).u …‖ ≤ C`.
* `regularizedSequenceData_of_paperHypotheses` — the producer
  threading T4's `exists_regularizedBareSolution_K` (K_Aepsi-form,
  consuming `AepsiUniformContextK`) per `k`, taking the per-`k`
  Banach-norm certificate as an additional hypothesis (per the AC
  amendment in this task's spec; the closed-form derivation of the
  norm bound from the apriori sum of integrated quantities is out
  of scope).

## AC amendments (per CONVENTIONS.md §8)

The original ACs cannot be discharged closed-form because:

1. `RegularizedBareSolution` does **not** carry HJB/Lagrangian/V-bound
   certificates needed by `AprioriDischargeInputs`. Those originate
   from the paper hypotheses `(hpow, hV)`, the `lem:strong.is.strong`
   chain, and the C.3 V-bound infrastructure. We therefore
   parameterise `aprioriInputs_of_regularizedBareSolution` over an
   `AprioriInputAuxHyps` bundle, mirroring F.3's `aprioriInputsAtEps`.
2. The Banach-pair-norm bound `‖toLp m‖ + ‖toLpSobolev u Du‖ ≤ C` does
   **not** follow directly from `apriori_at_eps`'s sum of integrated
   quantities; the translation requires norm-vs-`Lᵖ`-power identities
   we have not yet developed. The producer therefore takes the
   per-`k` Banach-norm certificate as input (a thin C.4-bridge
   workstream).

These amendments preserve the producer chain shape: T7 still hands out
a sequence of bare-function records with `ε_k → 0` and a uniform
Banach-pair-norm bound — only the form of the inputs is parameterised.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open scoped ENNReal Topology

variable {d : ℕ}

/-! ## Test-direction certificate (raw-exponent form)

(iter `infra-P7-sigfix-T1-testDirCerts`, Phase 1A, 2026-05-24).

Named-structure replacement for the prior anonymous 4-And conjunction
`MemLpPer β̄ η ∧ (∀ i, MemLpPer γ̄ Dν i) ∧ MemLpPer β̄ ν ∧ MemLpPer γ̄ ν`
threaded through the K0 closure consumers
`mintyClosure_familyNative_{set,signed,transport}_of_paperHypotheses_narrowK0`.

Lives here (under `Banach` namespace) rather than in `BanachBridge.lean`
because `BanachBridge.lean` imports this module. The paper-form sibling
`StationaryMFG.Theorems.SimplePower.TestDirectionCerts hpow η ν Dν`
(defined in `BanachBridge.lean`, parameterised by
`hpow : HypothesisPowerGrowth H DpH`) bridges to this raw form via
`TestDirectionCerts.toRaw` at paper-form exponents
`(β̄, γ̄) = (β + 1, gammaBar α β)`. -/

/-- **Test-direction regularity certificate (raw-exponent form).**

Consumer-side surface used by the K0 closure consumers in this module,
which parameterise over abstract real exponents
`{γBarReal βBarReal : ℝ}` rather than `hpow`. The public-API surface is
the `hpow`-parameterised
`StationaryMFG.Theorems.SimplePower.TestDirectionCerts` (defined in
`BanachBridge.lean`); `TestDirectionCerts.toRaw` bridges. -/
structure TestDirectionCertsRaw
    (βBarReal γBarReal : ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) : Prop where
  /-- `η ∈ L^{β̄}_per`. -/
  hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η
  /-- `Dν i ∈ L^{γ̄}_per` for each `i`. -/
  hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)
  /-- `ν ∈ L^{β̄}_per`. -/
  hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν
  /-- `ν ∈ L^{γ̄}_per`. -/
  hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν

/-! ## Bridge: bare functions to a `XBanach` pair -/

/-- **Bridge bare `(m, u, Du)` into a Banach pair.**

Takes:
* a bare `m` with `MemLpPer (ENNReal.ofReal βBarReal) m`,
* a bare `u` with `MemSobolevPer (ENNReal.ofReal γBarReal) u` and an
  explicit weak-derivative family `Du` whose components lie in
  `MemLpPer (ENNReal.ofReal γBarReal)`,
and produces an element of
`XBanach d βBarReal γBarReal = LpPer (ENNReal.ofReal βBarReal) d ×
                              SobolevPerLp 1 (ENNReal.ofReal γBarReal) d`
by routing through `MemLpPer.toLp` and `MemSobolevPer.toLpSobolev`.

This is the Banach-pair counterpart of T4's `RegularizedBareSolution`'s
projections `mOf q`, `uOf q`, `DuOf q i`. -/
noncomputable def banachPairOfBare {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) m)
    (huSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) u)
    (hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du i)) :
    XBanach d βBarReal γBarReal :=
  (hmLp.toLp,
    MemSobolevPer.toLpSobolev (p := ENNReal.ofReal γBarReal) huSob hDuLp)

/-- The Banach pair built from a `RegularizedBareSolution`'s
bare-function projections. The weak-derivative certificates and
`MemLpPer`/`MemSobolevPer` predicates are read off the record. -/
noncomputable def RegularizedBareSolution.toBanachPair
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal') :
    XBanach d βBarReal γBarReal :=
  banachPairOfBare sol.hmLp (sol.memSobolevPer_u) sol.hDuLp

/-! ## Child C — Minty/δ-limit lemma for the set test family

Per the v3 expert plan post-T6 audit (two-domain redesign), the
K_Aepsi-form weak VI delivered by `exists_banachVI_at_eps_KAepsi`
(child A) provides the abstract VI inequality only at strict-positive
test points `q' ∈ K_Aepsi`. The paper's set-indicator regularised VI
`hVIeps_set` is stated for **nonneg** test densities `S.indicator ρ`,
i.e. on the *closed* nonneg cone.

The bridge is a strict-positive perturbation
`μ_n := S.indicator ρ + 1/(n+1)` of the paper test family followed by
limit passage. The perturbation lies in `K_Aepsi` for every `n` (the
constant `1/(n+1)` contributes a strictly positive lower bound), so
the K_Aepsi-form weak VI applies; passing `n → ∞` recovers the
inequality at the limit `μ := S.indicator ρ`.

The continuity-along-perturbation step is genuine analytic content
(it requires continuity of `H` and `D_pH` in the third argument plus
dominated convergence on the unit cube, with the constant `1` as
dominator). That machinery has not yet been factored out of
`Hamiltonian/Estimates.lean`; following the precedent of
`existsStrongVI_at_eps` (`Banach/Closure.lean`), which takes
`hMono`/`hHC`/`hCoerc`/`hClosure` as inputs whenever the upstream
piece is still pending, the present lemma takes the
operator-continuity certificate as an authorised input hypothesis
(per CONVENTIONS §8). -/

/-- **Child C — Minty/δ-limit theorem for the set test family.**

Take the K_Aepsi-form weak VI delivered by child A
(`exists_banachVI_at_eps_KAepsi`) at primal-witness Banach point `q`,
and a paper-test triple `(S.indicator ρ, υ, Dυ)` with `0 ≤ ρ` a.e.
together with its `MemLpPer`/`MemSobolevPer` Banach-embedding
certificates. The strict-positive perturbation
`μ_n := S.indicator ρ + 1/(n+1)` produces a K_Aepsi test point at
each `n`; under the operator-continuity hypothesis `hCont` (the
analytic content), passing `n → ∞` yields the paper's `hVIeps_set`
inequality at the limit. -/
theorem hVIeps_set_of_KAepsi_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    -- K_Aepsi-indexed `MFGOpEpsAuxHyps` supplier, the canonical shape
    -- consumed by `Aepsi_CLM_opK` (per `infra-P4-domain-indexed-Aepsi-CLM`).
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- The K_Aepsi-form weak VI from child A.
    (hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Test triple data.
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x)
    -- Banach embeddability of the test triple.
    (hSρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation `μ_n := S.indicator ρ + 1/(n+1)`.
    -- This is the analytic content: it follows from continuity of `H`
    -- and `D_pH` in the third argument plus dominated convergence on
    -- the unit cube (with the constant `1` as dominator), under the
    -- AC2 integrand bounds. The supplier is paper material and the
    -- corresponding closure task is filed separately.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => Dυ i x - DuOf q i x)
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - mOf q x)
            (υ - uOf q))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ (S.indicator ρ) υ
              (fun i x => Dυ i x - DuOf q i x)
              (S.indicator ρ - mOf q) (υ - uOf q)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (S.indicator ρ) υ
          (fun i x => Dυ i x - DuOf q i x)
          (S.indicator ρ - mOf q) (υ - uOf q) := by
  classical
  -- Finite-measure instance on the unit cube (used for `memLp_const`).
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- For each `n`, build the perturbation Banach test point and apply
  -- the K_Aepsi-form weak VI; package the resulting bare-function
  -- inequality.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - mOf q x)
              (υ - uOf q) := by
    intro n
    -- Strict positivity of the perturbation constant.
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    -- `MemLpPer βBar` for the constant function `1/(n+1)` on the cube.
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    -- `MemLpPer βBar` for the perturbed density.
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hSρ_memLp hcst_memLp
      have heq : ((S.indicator ρ : (Fin d → ℝ) → ℝ)
                    + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
                  = fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    -- Build the Banach test point `q'_n := (μ_n_Lp, toLpSobolev υ Dυ)`.
    set qn : XBanach d βBarReal γBarReal :=
      banachPairOfBare (m := fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
        (u := υ) (Du := Dυ) hμn_memLp hυ_memSob hDυ_memLp with hqn
    -- Strict positivity of `qn.1` a.e.: `0 ≤ S.indicator ρ` (from
    -- `0 ≤ ρ` a.e.) plus `0 < 1/(n+1)`.
    have hSρ_nn :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 ≤ S.indicator ρ x := by
      filter_upwards [hρ_nn] with x hxρ
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS, hxρ]
      · simp [Set.indicator_of_notMem hxS]
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < S.indicator ρ x + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hSρ_nn] with x hxnn
      linarith
    -- `qn ∈ K_Aepsi` via a.e.-equality between `⇑qn.1` and the bare
    -- perturbation.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) := by
      change (⇑(hμn_memLp.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] _
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
      filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
      rw [hx_eq]; exact hx_pos
    -- Apply the K_Aepsi-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_K
    -- Unfold via the on-domain identity for `Aepsi_CLM_opK` (using
    -- `qn ∈ K_Aepsi`).
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Identify the primal triple `(qn.2.2, qn.1, qn.2.1)` with bare data.
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
      intro i
      change (⇑((hDυ_memLp i).toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i
      exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      change (⇑(hυ_memSob.1.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    -- Identify the test triple `((qn-q).2.2, (qn-q).1, (qn-q).2.1)`
    -- with the bare differences via `Lp.coeFn_sub`.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (S.indicator ρ x + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          υ - uOf q := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => Dυ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = Dυ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    -- Replace the test triple in `hVIn` with the bare differences.
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => Dυ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (S.indicator ρ x + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1)) (υ - uOf q)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Replace the primal triple `(qn.2.2, qn.1, qn.2.1)` with the bare
    -- perturbation `(Dυ, S.indicator ρ + 1/(n+1), υ)`.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := Dυ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (S.indicator ρ x + 1 / ((n : ℝ) + 1)) - mOf q x)
          (υ - uOf q)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  -- Pass `n → ∞` using the operator-continuity hypothesis.
  exact ge_of_tendsto' hCont hStep

/-! ## Child D — Minty/δ-limit lemma for the signed test family

Companion to Child C. The K_Aepsi-form weak VI (child A) supplies the
abstract VI inequality only at strict-positive primal points
`q' ∈ K_Aepsi`. The paper's signed regularised VI `hVIeps_signed`
takes a pair `(σ_+, σ_-)` of nonneg densities and pairs the
operator's primal at the **signed** combination
`S.indicator (σ_+ - σ_-)`.

The strict-positive perturbation `μ_n := S.indicator (σ_+ - σ_-) + 1/(n+1)`
is a.e. positive **only when** `S.indicator (σ_+ - σ_-)` is itself
a.e. nonneg (i.e. `σ_+ ≥ σ_-` on `S` a.e., the "restrict-to-`σ ≥ -1`
form" of the task notes). The lemma therefore takes that extra
nonnegativity hypothesis as an additional authorised input
(per CONVENTIONS §8); its closure to the universe shape of the
field is part of the broader Step-2 sign-decomposition argument
filed separately.

Modulo that hypothesis, the proof structure is identical to Child C:
build `μ_n`, embed, K_Aepsi VI invocation, congr-ae conversions,
`ge_of_tendsto'` limit. -/

/-- **Child D — Minty/δ-limit theorem for the signed test family
(narrowed to the paper-exact `StrongVI_setForm_signed` shape per
`infra-P4-narrow-hVIeps-signed-shape`).**

Take the K_Aepsi-form weak VI (child A) at primal-witness Banach
point `q ∈ K0_Aepsi`, a sign `σ ∈ {+1, -1}`, and a measurable
finite-measure subset `S ⊆ UnitCube d`. The paper test triple
`(η, ν, Dν) = (σ · m · 1_S, 0, 0)` (`m := mOf q`) has total density
`m + σ · m · 1_S = m · (1 + σ · 1_S)`, which is `≥ 0` a.e. since
`m ≥ 0` (from `q ∈ K0_Aepsi`) and `σ ∈ {±1}` (so `1 + σ · 1_S ∈ [0, 2]`).
The strict-positive perturbation
`μ_n := m + σ · m · 1_S + 1/(n+1)` is then `> 0` a.e., yielding a
K_Aepsi test point. Passing `n → ∞` via the operator-continuity
hypothesis `hCont` yields the paper's narrowed `hVIeps_signed`
inequality at the limit.

Note: only the *primal* density of the operator pair perturbs with
`n`; the value-function and gradient primal/direction components
stay constant at `(uOf q, DuOf q)` and `(0, 0)` respectively (since
the test point's `υ = uOf q` and `Dυ = DuOf q` agree with `q`'s
projections, making the directions `qn - q` zero in those slots
modulo a.e.). Hence `hCont` is morally continuity of the operator
pair in the primal-density slot only. -/
theorem hVIeps_signed_of_KAepsi_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    -- K_Aepsi-indexed `MFGOpEpsAuxHyps` supplier (canonical shape).
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- K0_Aepsi membership of `q`: `0 ≤ ⇑q.1` a.e. on the cube.
    -- Source of the admissibility `m + σ · m · 1_S ≥ 0` after the
    -- narrowing.
    (hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal)
    -- The K_Aepsi-form weak VI from child A.
    (hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Paper-exact test family parameters.
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (_hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation
    -- `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)`, perturbing only the
    -- primal density and the test-direction density (both shifted by
    -- the constant `1/(n+1)`); the `υ` and `Dυ` slots are unchanged
    -- (zero in the direction). Filed under
    -- `infra-P4-mfg-operator-eps-tendsto-along-additive-perturbation`.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (DuOf q)
            (fun x => mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
            (uOf q)
            (fun _ _ => (0 : ℝ))
            (fun x => σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
            (fun _ => (0 : ℝ)))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              (DuOf q)
              (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (uOf q)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (DuOf q)
          (fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (uOf q)
          (fun _ _ => (0 : ℝ))
          (fun x => σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ`. Used in the admissibility
  -- bound `0 ≤ mOf q · (1 + σ · 1_S)`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  -- `mOf q` Lp embeddability from `q.1`.
  have hm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  -- `mOf q` is a.e. nonneg from K0_Aepsi membership.
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  0 ≤ mOf q x := hq_K0
  -- The signed multiplicative perturbation `σ • mOf q` is `MemLpPer`.
  have hσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => σ * mOf q x) := by
    have hsmul := hm_memLp.const_smul (𝕜 := ℝ) σ
    -- `(σ • mOf q) x = σ * mOf q x` by definition of pointwise smul.
    have heq : (σ • (mOf q : (Fin d → ℝ) → ℝ))
                  = fun x => σ * mOf q x := rfl
    rw [heq] at hsmul; exact hsmul
  -- The indicator-restricted version.
  have hSσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (S.indicator (fun x => σ * mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσm_memLp.toMemLp)
  -- Pointwise: `S.indicator (fun x => σ * mOf q x) x =
  -- σ * mOf q x * S.indicator (fun _ => 1) x`.
  have hSσm_eq : ∀ x : Fin d → ℝ,
      S.indicator (fun x => σ * mOf q x) x
        = σ * mOf q x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Function-level identity for use with `MemLpPer.add` rewrites.
  have hSσm_funEq :
      (S.indicator (fun x => σ * mOf q x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x; exact hSσm_eq x
  -- Lp embeddability of `(fun x => σ * mOf q x * S.indicator 1 x)`.
  have hSσm_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * mOf q x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσm_funEq]; exact hSσm_memLp
  -- Per-`n` strict-positive perturbation.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              (DuOf q)
              (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              (uOf q)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              (fun _ => (0 : ℝ)) := by
    intro n
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    -- Build the Banach test point as `qn := q + (mPert_n.toLp, 0, 0)`,
    -- perturbing only the `m`-component additively. This avoids the
    -- need for a `MemSobolevPer` certificate on `uOf q` (the
    -- structurally non-existent weak-derivative tie inside the bare
    -- abbreviation `XBanach = LpPer × SobolevPerLp = LpPer × LpPer ×
    -- (Fin d → LpPer)`).
    -- The `m`-perturbation: `mPert_n := σ · mOf q · 1_S + 1/(n+1)`.
    have hSσm_const_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hSσm_memLp' hcst_memLp
      have heq :
          ((fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
            = fun x => σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    -- The Banach perturbation: nonzero in `m` only.
    set qn : XBanach d βBarReal γBarReal :=
      (q.1 + hSσm_const_memLp.toLp, q.2) with hqn
    -- Difference identities. `qn - q = (mPert_n.toLp, 0)`.
    have hqn_sub_1 : (qn - q).1 = hSσm_const_memLp.toLp := by
      change (q.1 + hSσm_const_memLp.toLp) - q.1 = hSσm_const_memLp.toLp
      abel
    have hqn_sub_21 : (qn - q).2.1
                        = (0 : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
                              (MeasureTheory.Measure.restrict
                                MeasureTheory.volume (UnitCube d))) := by
      change q.2.1 - q.2.1 = _
      simp
    have hqn_sub_22 : ∀ i, (qn - q).2.2 i
                            = (0 : MeasureTheory.Lp ℝ
                                  (ENNReal.ofReal γBarReal)
                                  (MeasureTheory.Measure.restrict
                                    MeasureTheory.volume (UnitCube d))) := by
      intro i
      change q.2.2 i - q.2.2 i = _
      simp
    -- The m-component direction `(qn - q).1` is a.e. equal to
    -- `mPert_n`.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      rw [hqn_sub_1]
      exact MeasureTheory.MemLp.coeFn_toLp hSσm_const_memLp.toMemLp
    -- The u-component direction `(qn - q).2.1` is `0`.
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun _ => (0 : ℝ) := by
      rw [hqn_sub_21]
      exact MeasureTheory.Lp.coeFn_zero ℝ _ _
    -- The Du-component direction `(qn - q).2.2 i` is `0`.
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (fun _ => (0 : ℝ)) := by
      intro i
      rw [hqn_sub_22 i]
      exact MeasureTheory.Lp.coeFn_zero ℝ _ _
    -- The m-component primal `qn.1` is a.e. equal to
    -- `mOf q + mPert_n = mOf q + σ · mOf q · 1_S + 1/(n+1)`.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => mOf q x + σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      have h1 : qn.1 = q.1 + hSσm_const_memLp.toLp := rfl
      rw [h1]
      have hsum := MeasureTheory.Lp.coeFn_add q.1 hSσm_const_memLp.toLp
      have hcoe := MeasureTheory.MemLp.coeFn_toLp hSσm_const_memLp.toMemLp
      filter_upwards [hsum, hcoe] with x hxsum hxcoe
      have hxsum' : ⇑(q.1 + hSσm_const_memLp.toLp) x
                      = ⇑q.1 x + ⇑hSσm_const_memLp.toLp x := hxsum
      change ⇑(q.1 + hSσm_const_memLp.toLp) x
              = mOf q x + σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)
      rw [hxsum']
      change ⇑q.1 x + ⇑hSσm_const_memLp.toLp x
              = mOf q x + σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)
      have hxcoe' : ⇑hSσm_const_memLp.toLp x
                      = σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1) := hxcoe
      rw [hxcoe']
      change mOf q x + (σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
              = mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)
      ring
    -- The u-component primal `qn.2.1` equals `q.2.1` definitionally,
    -- hence `=ᵐ uOf q`.
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] uOf q :=
      Filter.EventuallyEq.refl _ _
    -- The Du-component primal `qn.2.2 i` equals `q.2.2 i`
    -- definitionally, hence `=ᵐ DuOf q i`.
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] DuOf q i := by
      intro i
      exact Filter.EventuallyEq.refl _ _
    -- Strict positivity of `qn.1` a.e.: `mOf q ≥ 0` and `σ ∈ {±1}`
    -- give `0 ≤ mOf q + σ · mOf q · 1_S`, then add `1/(n+1) > 0`.
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < mOf q x + σ * mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hm_nn] with x hxnn
      have hadd_nn : 0 ≤ mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        by_cases hxS : x ∈ S
        · rw [Set.indicator_of_mem hxS]
          have : mOf q x + σ * mOf q x * 1 = mOf q x * (1 + σ) := by ring
          rw [this]
          have h1σ_nn : (0 : ℝ) ≤ 1 + σ := by linarith
          exact mul_nonneg hxnn h1σ_nn
        · rw [Set.indicator_of_notMem hxS]
          simpa using hxnn
      linarith
    -- `qn ∈ K_Aepsi`.
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
      filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
      rw [hx_eq]; exact hx_pos
    -- Apply the K_Aepsi-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_K
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Substitute the bare-direction representatives into the abstract
    -- VI inequality (replace `(qn - q).{1, 2.1, 2.2}` by their bare
    -- a.e. equivalents).
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun _ _ => (0 : ℝ))
          (⇑((qn - q).1))
          (fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
          (⇑((qn - q).2.1)) (fun _ => (0 : ℝ))
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Substitute the bare-primal representatives.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := DuOf q)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := uOf q)
          (fun _ _ => (0 : ℝ))
          (fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
          (fun _ => (0 : ℝ))
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  exact ge_of_tendsto' hCont hStep

/-! ### Child D′ — Minty/δ-limit for the signed family at a user probe

Companion to `hVIeps_signed_of_KAepsi_VI`. Same primal-density
perturbation `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)`, but the
Banach test point is built from a user-supplied probe `(υ, Dυ)`
instead of `(uOf q, DuOf q)`. The strict-positive admissibility
argument (`m ≥ 0` plus `1 + σ · 1_S ∈ [0, 2]`) is identical to
Child D; the proof template mirrors `hVIeps_set_of_KAepsi_VI`
(Child C) with `S.indicator ρ` replaced by the signed perturbation
`m + σ · m · 1_S`.

The continuity certificate `hCont` is again the authorised
analytic input (CONVENTIONS §8). -/

/-- **Child D′ — Minty/δ-limit theorem for the signed family with
user-supplied probe `(υ, Dυ)`.**

Take the K_Aepsi-form weak VI (child A) at primal-witness Banach
point `q ∈ K0_Aepsi`, a sign `σ ∈ {±1}`, a measurable
finite-measure subset `S`, and a user probe `(υ, Dυ)` carrying
its `MemSobolevPer` / `MemLpPer` Banach-embedding certificates.
The strict-positive perturbation
`μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)` produces a K_Aepsi test
point at each `n`; under the operator-continuity hypothesis
`hCont`, passing `n → ∞` yields the user-probe form of the paper's
signed VI at the limit. -/
theorem hVIeps_signed_user_probe_of_KAepsi_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    -- K_Aepsi-indexed `MFGOpEpsAuxHyps` supplier (canonical shape).
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- K0_Aepsi membership of `q`: `0 ≤ ⇑q.1` a.e. on the cube.
    (hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal)
    -- The K_Aepsi-form weak VI from child A.
    (hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Paper-exact test-family parameters.
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (_hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    -- User-supplied probe `(υ, Dυ)` with Banach-embedding certificates.
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation
    -- `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)` at the user probe.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => Dυ i x - DuOf q i x)
            (fun x => (mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) - mOf q x)
            (fun x => υ x - uOf q x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun x => υ x - uOf q x)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ x - uOf q x) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  -- `mOf q` Lp embeddability and a.e. nonnegativity.
  have hm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  0 ≤ mOf q x := hq_K0
  -- The signed multiplicative perturbation `σ • mOf q` is `MemLpPer`.
  have hσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => σ * mOf q x) := by
    have hsmul := hm_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (mOf q : (Fin d → ℝ) → ℝ))
                  = fun x => σ * mOf q x := rfl
    rw [heq] at hsmul; exact hsmul
  -- The indicator-restricted version.
  have hSσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (S.indicator (fun x => σ * mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσm_memLp.toMemLp)
  -- Pointwise rewrite: indicator of σ•m equals (σ•m)·1_S.
  have hSσm_funEq :
      (S.indicator (fun x => σ * mOf q x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Lp embeddability of `(fun x => σ * mOf q x * S.indicator 1 x)`.
  have hSσm_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * mOf q x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσm_funEq]; exact hSσm_memLp
  -- The "base" perturbation `mF := mOf q + σ · mOf q · 1_S` is `MemLpPer`.
  have hmF_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => mOf q x + σ * mOf q x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    have h := MemLpPer.add hm_memLp hSσm_memLp'
    have heq :
        ((mOf q : (Fin d → ℝ) → ℝ)
            + (fun x => σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := rfl
    rw [← heq]; exact h
  -- `mF` is a.e. ≥ 0.
  have hmF_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ mOf q x + σ * mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    filter_upwards [hm_nn] with x hxnn
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      have hr : mOf q x + σ * mOf q x * 1 = mOf q x * (1 + σ) := by ring
      rw [hr]
      have h1σ_nn : (0 : ℝ) ≤ 1 + σ := by linarith
      exact mul_nonneg hxnn h1σ_nn
    · rw [Set.indicator_of_notMem hxS]
      simpa using hxnn
  -- Per-`n` strict-positive perturbation.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => (mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) - mOf q x)
              (fun x => υ x - uOf q x) := by
    intro n
    -- Strict positivity of the perturbation constant.
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    -- `MemLpPer βBar` for the constant function `1/(n+1)`.
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    -- `MemLpPer βBar` for the perturbed density `mF + 1/(n+1)`.
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hmF_memLp hcst_memLp
      have heq :
          ((fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
            = fun x => mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    -- Build the Banach test point `qn := (μ_n.toLp, toLpSobolev υ Dυ)`.
    set qn : XBanach d βBarReal γBarReal :=
      banachPairOfBare
        (m := fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
        (u := υ) (Du := Dυ) hμn_memLp hυ_memSob hDυ_memLp with hqn
    -- Strict positivity of `qn.1` a.e.
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < mOf q x + σ * mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hmF_nn] with x hxnn
      linarith
    -- `qn ∈ K_Aepsi` via a.e.-equality between `⇑qn.1` and the bare
    -- perturbation.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => mOf q x + σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      change (⇑(hμn_memLp.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] _
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
      filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
      rw [hx_eq]; exact hx_pos
    -- Apply the K_Aepsi-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_K
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Identify `(qn.2.2, qn.1, qn.2.1)` with bare data.
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
      intro i
      change (⇑((hDυ_memLp i).toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i
      exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      change (⇑(hυ_memSob.1.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    -- Identify `((qn-q).2.2, (qn-q).1, (qn-q).2.1)` with bare diffs.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => υ x - uOf q x := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => Dυ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = Dυ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    -- Replace the test triple.
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => Dυ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1))
          (fun x => υ x - uOf q x)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Replace the primal triple.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := Dυ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (fun x => υ x - uOf q x)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  -- Pass `n → ∞` using the operator-continuity hypothesis.
  exact ge_of_tendsto' hCont hStep

/-! ### Child D″ — Minty/δ-limit for the signed family at a user **triple**

Companion to `hVIeps_signed_user_probe_of_KAepsi_VI`. Same shape, but
the primal density in the perturbation `μ_n := μ + σ · μ · 1_S + 1/(n+1)`
is a **user-supplied** density `μ` (carrying its `MemLpPer βBar`
certificate plus a.e.-nonnegativity), in lieu of the iter-358 hardcoded
`mOf q`. The strict-positive admissibility argument is unchanged
(`μ ≥ 0` plus `1 + σ · 1_S ∈ [0, 2]`); the proof template is a
line-for-line mirror of Child D′ with `mOf q ↦ μ` everywhere in the
perturbation construction (`mOf q` continues to appear in the bare
difference `μ_n - mOf q`).

The continuity certificate `hCont` is again the authorised analytic
input (CONVENTIONS §8). -/

/-- **Child D″ — Minty/δ-limit theorem for the signed family with a
user-supplied primal-density triple `(μ, υ, Dυ)`.**

Take the K_Aepsi-form weak VI (child A) at primal-witness Banach point
`q ∈ K0_Aepsi`, a sign `σ ∈ {±1}`, a measurable finite-measure subset
`S`, a user primal density `μ` (with `0 ≤ μ` a.e. and `MemLpPer βBar`
embeddability), and a user probe `(υ, Dυ)` carrying its
`MemSobolevPer` / `MemLpPer` Banach-embedding certificates. The
strict-positive perturbation `μ_n := μ + σ · μ · 1_S + 1/(n+1)`
produces a K_Aepsi test point at each `n`; under the
operator-continuity hypothesis `hCont`, passing `n → ∞` yields the
user-triple form of the paper's signed VI at the limit. -/
theorem hVIeps_signed_user_triple_of_KAepsi_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    -- K_Aepsi-indexed `MFGOpEpsAuxHyps` supplier (canonical shape).
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- K0_Aepsi membership of `q`: `0 ≤ ⇑q.1` a.e. on the cube.
    (_hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal)
    -- The K_Aepsi-form weak VI from child A.
    (hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Paper-exact test-family parameters.
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (_hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    -- User-supplied primal density `μ` plus probe `(υ, Dυ)` with
    -- Banach-embedding certificates.
    (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation
    -- `μ_n := μ + σ · μ · 1_S + 1/(n+1)` at the user triple.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => Dυ i x - DuOf q i x)
            (fun x => (μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) - mOf q x)
            (fun x => υ x - uOf q x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => (μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - mOf q x)
              (fun x => υ x - uOf q x)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                      - mOf q x)
          (fun x => υ x - uOf q x) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  -- The signed multiplicative perturbation `σ • μ` is `MemLpPer`.
  have hσμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => σ * μ x) := by
    have hsmul := hμ_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (μ : (Fin d → ℝ) → ℝ))
                  = fun x => σ * μ x := rfl
    rw [heq] at hsmul; exact hsmul
  -- The indicator-restricted version.
  have hSσμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (S.indicator (fun x => σ * μ x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσμ_memLp.toMemLp)
  -- Pointwise rewrite: indicator of σ•μ equals (σ•μ)·1_S.
  have hSσμ_funEq :
      (S.indicator (fun x => σ * μ x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Lp embeddability of `(fun x => σ * μ x * S.indicator 1 x)`.
  have hSσμ_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * μ x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσμ_funEq]; exact hSσμ_memLp
  -- The "base" perturbation `μF := μ + σ · μ · 1_S` is `MemLpPer`.
  have hμF_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => μ x + σ * μ x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    have h := MemLpPer.add hμ_memLp hSσμ_memLp'
    have heq :
        ((μ : (Fin d → ℝ) → ℝ)
            + (fun x => σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := rfl
    rw [← heq]; exact h
  -- `μF` is a.e. ≥ 0.
  have hμF_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    filter_upwards [hμ_nn] with x hxnn
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      have hr : μ x + σ * μ x * 1 = μ x * (1 + σ) := by ring
      rw [hr]
      have h1σ_nn : (0 : ℝ) ≤ 1 + σ := by linarith
      exact mul_nonneg hxnn h1σ_nn
    · rw [Set.indicator_of_notMem hxS]
      simpa using hxnn
  -- Per-`n` strict-positive perturbation.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => (μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) - mOf q x)
              (fun x => υ x - uOf q x) := by
    intro n
    -- Strict positivity of the perturbation constant.
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    -- `MemLpPer βBar` for the constant function `1/(n+1)`.
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    -- `MemLpPer βBar` for the perturbed density `μF + 1/(n+1)`.
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hμF_memLp hcst_memLp
      have heq :
          ((fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
            = fun x => μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    -- Build the Banach test point `qn := (μ_n.toLp, toLpSobolev υ Dυ)`.
    set qn : XBanach d βBarReal γBarReal :=
      banachPairOfBare
        (m := fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
        (u := υ) (Du := Dυ) hμn_memLp hυ_memSob hDυ_memLp with hqn
    -- Strict positivity of `qn.1` a.e.
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hμF_nn] with x hxnn
      linarith
    -- `qn ∈ K_Aepsi` via a.e.-equality between `⇑qn.1` and the bare
    -- perturbation.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => μ x + σ * μ x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      change (⇑(hμn_memLp.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] _
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
      filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
      rw [hx_eq]; exact hx_pos
    -- Apply the K_Aepsi-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_K
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Identify `(qn.2.2, qn.1, qn.2.1)` with bare data.
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
      intro i
      change (⇑((hDυ_memLp i).toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i
      exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      change (⇑(hυ_memSob.1.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    -- Identify `((qn-q).2.2, (qn-q).1, (qn-q).2.1)` with bare diffs.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => υ x - uOf q x := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => Dυ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = Dυ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    -- Replace the test triple.
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => Dυ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1))
          (fun x => υ x - uOf q x)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Replace the primal triple.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := Dυ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (fun x => υ x - uOf q x)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  -- Pass `n → ∞` using the operator-continuity hypothesis.
  exact ge_of_tendsto' hCont hStep

/-! ## Child D — Minty/δ-limit lemma for the transport test family

Companion to the signed family. The transport-family regularised VI
`hVIeps_transport` has primal density `σ` (nonneg, no indicator) and
test gradient family `φ`. Structurally this is exactly Child C with
the `S.indicator` wrapper removed: the strict-positive perturbation
`μ_n := σ + 1/(n+1)` is a.e. positive (since `0 ≤ σ` a.e. plus
`0 < 1/(n+1)`), and Child C's proof template applies verbatim.

The operator-continuity certificate `hCont` is again the authorised
analytic input filed under
`infra-P4-mfg-operator-eps-tendsto-along-additive-perturbation`. -/

/-- **Child D — Minty/δ-limit theorem for the transport test family.**

Take the K_Aepsi-form weak VI (child A) at primal-witness Banach
point `q`, and a paper-test transport triple `(σ, υ, φ)` with
`0 ≤ σ` a.e. The strict-positive perturbation
`μ_n := σ + 1/(n+1)` produces a K_Aepsi test point at each `n`;
under the operator-continuity hypothesis `hCont`, passing `n → ∞`
yields the paper's `hVIeps_transport` inequality at the limit. -/
theorem hVIeps_transport_of_KAepsi_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    -- K_Aepsi-indexed `MFGOpEpsAuxHyps` supplier (canonical shape).
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- The K_Aepsi-form weak VI from child A.
    (hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Test triple data: nonneg primal density `σ`, value function `υ`,
    -- and test gradient family `φ`.
    (σ υ : (Fin d → ℝ) → ℝ) (φ : Fin d → (Fin d → ℝ) → ℝ)
    (hσ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x)
    -- Banach embeddability.
    (hσ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hφ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation `μ_n := σ + 1/(n+1)`. Filed
    -- under `infra-P4-mfg-operator-eps-tendsto-along-additive-perturbation`.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ
            (fun x => σ x + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => φ i x - DuOf q i x)
            (fun x => σ x + 1 / ((n : ℝ) + 1) - mOf q x)
            (υ - uOf q))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ σ υ
              (fun i x => φ i x - DuOf q i x)
              (σ - mOf q) (υ - uOf q)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ σ υ
          (fun i x => φ i x - DuOf q i x)
          (σ - mOf q) (υ - uOf q) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ
              (fun x => σ x + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => φ i x - DuOf q i x)
              (fun x => σ x + 1 / ((n : ℝ) + 1) - mOf q x)
              (υ - uOf q) := by
    intro n
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => σ x + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hσ_memLp hcst_memLp
      have heq : ((σ : (Fin d → ℝ) → ℝ)
                    + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
                  = fun x => σ x + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    set qn : XBanach d βBarReal γBarReal :=
      banachPairOfBare (m := fun x => σ x + 1 / ((n : ℝ) + 1))
        (u := υ) (Du := φ) hμn_memLp hυ_memSob hφ_memLp with hqn
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < σ x + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hσ_nn] with x hxnn
      linarith
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => σ x + 1 / ((n : ℝ) + 1) := by
      change (⇑(hμn_memLp.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] _
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
      filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
      rw [hx_eq]; exact hx_pos
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_K
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] φ i := by
      intro i
      change (⇑((hφ_memLp i).toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] φ i
      exact MeasureTheory.MemLp.coeFn_toLp (hφ_memLp i)
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      change (⇑(hυ_memSob.1.toLp) : (Fin d → ℝ) → ℝ)
                =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (σ x + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          υ - uOf q := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => φ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = φ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => φ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (σ x + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1)) (υ - uOf q)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := φ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => σ x + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => φ i x - DuOf q i x)
          (fun x => (σ x + 1 / ((n : ℝ) + 1)) - mOf q x)
          (υ - uOf q)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  exact ge_of_tendsto' hCont hStep

/-! ### Sanity-check `example` — opK shape

Per `infra-P4-retarget-minty-helpers-to-opK` AC6: pin the
K_Aepsi-totalized-operator (`Aepsi_CLM_opK`) input shape consumed by
the three Minty/δ-limit helpers. The supplier `auxHypsK` is the
canonical K_Aepsi-indexed shape produced by
`infra-P4-domain-indexed-Aepsi-CLM`; the on-domain reduction inside
each helper goes through `Aepsi_CLM_opK_apply_of_mem` (re-using the
same proof body as the universal-form unfolding, since both produce
the bare pairing `mfgOperatorEpsPair`). -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    (hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => Dυ i x - DuOf q i x)
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - mOf q x)
            (υ - uOf q))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ (S.indicator ρ) υ
              (fun i x => Dυ i x - DuOf q i x)
              (S.indicator ρ - mOf q) (υ - uOf q)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (S.indicator ρ) υ
          (fun i x => Dυ i x - DuOf q i x)
          (S.indicator ρ - mOf q) (υ - uOf q) :=
  hVIeps_set_of_KAepsi_VI auxHypsK q hVI S hS ρ υ Dυ
    hρ_nn hSρ_memLp hυ_memSob hDυ_memLp hCont

/-! ## Apriori-bound discharge from a `RegularizedBareSolution` -/

/-- **AC2 (closed form) — Build `AprioriInputAuxHyps` from
paper hypotheses plus authorised paper-residue inputs.**

Given the paper-power-growth bundle `h : HypothesisPowerGrowth H DpH`,
the `MemLpPer βBar' V` certificate `hV`, and a
`RegularizedBareSolution` at the standard exponents
`(γBar, βBar) := (gammaBar h.α h.β, betaBar h.β)`, dispatch each of
the ~30 fields of `AprioriInputAuxHyps`:

* exponent facts (`hβBar_one_lt`, `hHolder`, `hγBar'_one_le`) are
  derived from the paper-data fields `(h.α, h.β, h.hα, h.hβ)` via
  `one_lt_betaBar`, `paper_holderConjugate_betaBar`, and the
  `Real.HolderConjugate.symm`/`.lt` API;
* `hV_Lp` is the input parameter `hV`;
* `hu_lp_γ`, `hDu_lp`, `hDu_weak`, `hm_Lp` are read off `sol`;
* the genuinely paper-residue fields are taken as authorised input
  parameters per CONVENTIONS §1b: `epsTerms`, `Vbound`, `Vβp_bound`,
  the three `MemLpPer` certificates `hRes_Lp`/`hFlux_Lp` (whose
  exponents `βBar' = (β+1)/β` and `γBar' = γBar/(γBar-1)` are
  generally not part of `sol`'s carriage at the standard β̄/γ̄
  exponents), the Lagrangian bound `h_lagr`, the a.e. positivity
  bounds `hMpos`/`hVbnd`/`hEpsNN`, the transport identity
  `h_identity`, the eight `Integrable` certificates, the `hVβp`
  bound, the structural `(meas, per, loc)` regularity certificates
  on `(u, Du)`, and the three `hStrongVI_*` (set/signed/transport).

The constructor body is a single anonymous-constructor record build:
each field of `AprioriInputAuxHyps` is assigned from either the
derived paper-data lemma or the corresponding input. -/
noncomputable def aprioriInputAuxHyps_of_paperHypotheses
    [AxisMixMeasureHypothesis]
    {ε : ℝ} (_hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β)) V)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar h.α h.β) (betaBar h.β) βBarReal' γBarReal')
    -- Authorised paper-residue inputs (CONVENTIONS §1b):
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vβp_bound : ℝ)
    (hRes_Lp :
      MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u))
    (hFlux_Lp :
      MemLpPer (d := d) (ENNReal.ofReal (gammaBar' h.α h.β))
        (fun x => StationaryMFG.Hamiltonian.mDpH DpH x
                    (fun i => sol.Du i x) (sol.m x)))
    (h_lagr :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < sol.m x)
    (hVbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_int : MeasureTheory.Integrable sol.u
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSabove_int : MeasureTheory.Integrable
              (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hLB_int : MeasureTheory.Integrable
                (fun x => sol.m x ^ (h.β + 1))
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbeta_int : MeasureTheory.Integrable
                (fun x => sol.m x ^ h.β)
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelow_int : MeasureTheory.Integrable
                (fun x =>
                  sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                            + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
                    + V x * sol.m x
                    + epsTerms x)
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_meas : MeasureTheory.AEStronglyMeasurable sol.u
                  (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : StationaryMFG.Periodic.IsPeriodic sol.u)
    (hu_loc : MeasureTheory.LocallyIntegrable sol.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, StationaryMFG.Periodic.IsPeriodic (sol.Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (sol.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_int : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hUbetap_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hVbetap_int : MeasureTheory.Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hStrongVI_set :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u)
    (hStrongVI_signed :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u)
    (hStrongVI_transport :
      StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u) :
    AprioriInputAuxHyps (d := d) h V sol.Du sol.m sol.u ε where
  -- Data fields read from authorised inputs.
  epsTerms := epsTerms
  Vbound := Vbound
  Vβp_bound := Vβp_bound
  -- C.1-flavoured `MemLpPer` certificates.
  hRes_Lp := hRes_Lp
  hm_Lp := sol.hmLp
  hFlux_Lp := hFlux_Lp
  -- Exponent facts derived from `(h.α, h.β, h.hα, h.hβ)`.
  hβBar_one_lt := one_lt_betaBar h.β h.hβ
  hHolder :=
    (StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
      h.hβ).symm
  hγBar'_one_le := by
    -- `1 < γBar'` from the Hölder conjugate `(γBar, γBar')`, then
    -- lift to `ENNReal.ofReal`.
    have hγConj : Real.HolderConjugate (gammaBar h.α h.β)
                    (gammaBar' h.α h.β) := by
      unfold gammaBar'
      exact StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
        h.hα h.hβ
    have hγ'_one_lt : 1 < gammaBar' h.α h.β := hγConj.symm.lt
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (gammaBar' h.α h.β) :=
      ENNReal.ofReal_le_ofReal hγ'_one_lt.le
    simpa using h1
  -- Paper-residue analytic content (authorised inputs).
  h_lagr := h_lagr
  hMpos := hMpos
  hVbnd := hVbnd
  hEpsNN := hEpsNN
  h_identity := h_identity
  hu_int := hu_int
  hRHSabove_int := hRHSabove_int
  hLB_int := hLB_int
  hMbeta_int := hMbeta_int
  hRHSbelow_int := hRHSbelow_int
  hu_meas := hu_meas
  hu_per := hu_per
  hu_loc := hu_loc
  -- Bare-solution-derived weak-derivative tie.
  hDu_weak := sol.hWeakDeriv
  hDu_meas := hDu_meas
  hDu_per := hDu_per
  hDu_loc := hDu_loc
  -- Bare-solution-derived `MemLpPer` of each gradient component at γ̄.
  hDu_lp := sol.hDuLp
  hDu_norm_int := hDu_norm_int
  hUbetap_int := hUbetap_int
  hVbetap_int := hVbetap_int
  hVβp := hVβp
  -- Bare-solution-derived `MemLpPer γ̄ u`.
  hu_lp_γ := sol.huLp
  -- Paper-data `MemLpPer β̄' V` (the user's `hV`).
  hV_Lp := hV
  -- F.2-derived strong-VI specialisations (authorised inputs).
  hStrongVI_set := hStrongVI_set
  hStrongVI_signed := hStrongVI_signed
  hStrongVI_transport := hStrongVI_transport

/-- **AC2 (parameterised) — Build `AprioriDischargeInputs` from a
`RegularizedBareSolution` plus an `AprioriInputAuxHyps` bundle.**

The `RegularizedBareSolution` (T4) supplies the bare-function triple
`(m, u, Du)` together with `MemLpPer`/`MemSobolevPer` certificates,
weak-derivative ties, the integrability bundle (`MFGOpEpsAuxHyps`),
and almost-everywhere non-negativity of `m`. The
`AprioriInputAuxHyps` bundle (introduced in `Banach/Closure.lean` for
F.3) supplies the paper-hypothesis-derived ingredients
(`hHJB`, `h_lagr`, `hMpos`, `hVbnd`, `h_identity`, `Vbound`,
`Vβp_bound`, the L¹-integrabilities, the C.3 V-norm bound, etc.) that
the abstract Banach VI witness does not carry.

Per the AC amendment (CONVENTIONS §8), the auxiliary bundle is taken
explicitly; closing the loop on `(hpow, hV) → AprioriInputAuxHyps` is
tracked separately. The body is essentially `aprioriInputsAtEps`
(`Banach/Closure.lean`) with `BanachOutputData` replaced by the
direct bare-function projections of `RegularizedBareSolution`. -/
noncomputable def aprioriInputs_of_regularizedBareSolution
    [AxisMixMeasureHypothesis]
    {ε : ℝ} (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar h.α h.β) (betaBar h.β) βBarReal' γBarReal')
    (aux : AprioriInputAuxHyps (d := d) h V sol.Du sol.m sol.u ε) :
    AprioriDischargeInputs (d := d) h V ε hε where
  u := sol.u
  m := sol.m
  Du := sol.Du
  epsTerms := aux.epsTerms
  Vbound := aux.Vbound
  Vint_bound :=
    StationaryMFG.Theorems.SimplePower.Banach.Vint_bound
      (d := d) (ENNReal.ofReal (betaBar' h.β)) V
  Vβp_bound := aux.Vβp_bound
  hHJB := by
    -- Same plan as `aprioriInputsAtEps`: residual integrability +
    -- `lem_strong_is_strong_HJB_ineq` applied to the strong-VI set form.
    have hβBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' h.β) := by
      have hβ'_one_le : (1 : ℝ) ≤ betaBar' h.β :=
        (one_lt_betaBar' h.β h.hβ).le
      have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (betaBar' h.β) :=
        ENNReal.ofReal_le_ofReal hβ'_one_le
      simpa using h1
    have hRes_int :
        MeasureTheory.Integrable
          (StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u)
          (MeasureTheory.volume.restrict (UnitCube d)) :=
      aprioriDischarge_residual_integrable
        (βBar' := ENNReal.ofReal (betaBar' h.β))
        hβBar'_one_le aux.hRes_Lp
    exact StationaryMFG.Theorems.SimplePower.lem_strong_is_strong_HJB_ineq
      V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u
      hRes_int aux.hStrongVI_set
  h_lagr := aux.h_lagr
  hMpos := aux.hMpos
  hVbnd := aux.hVbnd
  hEpsNN := aux.hEpsNN
  h_identity := aux.h_identity
  hu_int := aux.hu_int
  hRHSabove_int := aux.hRHSabove_int
  hLB_int := aux.hLB_int
  hMbeta_int := aux.hMbeta_int
  hRHSbelow_int := aux.hRHSbelow_int
  hVint := by
    -- `∫ |V| ≤ Vint_bound βBar' V`, from the C.3 V-norm bound, using
    -- `aux.hV_Lp` as the `MemLpPer βBar' V` certificate.
    have hβBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' h.β) := by
      have hβ'_one_le : (1 : ℝ) ≤ betaBar' h.β :=
        (one_lt_betaBar' h.β h.hβ).le
      have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (betaBar' h.β) :=
        ENNReal.ofReal_le_ofReal hβ'_one_le
      simpa using h1
    exact V_norm_le_Vint_bound (d := d) hβBar'_one_le aux.hV_Lp
  hγ_one_le := by
    -- `1 ≤ γBar` from `h.hα, h.hβ`.
    have hγ_one_lt : 1 < gammaBar h.α h.β :=
      one_lt_gammaBar h.α h.β h.hα h.hβ
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (gammaBar h.α h.β) :=
      ENNReal.ofReal_le_ofReal hγ_one_lt.le
    simpa using h1
  hγ_top := ENNReal.ofReal_ne_top
  hu_meas := aux.hu_meas
  hu_per := aux.hu_per
  hu_loc := aux.hu_loc
  hu_sob := sol.memSobolevPer_u
  hDu_weak := sol.hWeakDeriv
  hDu_meas := aux.hDu_meas
  hDu_per := aux.hDu_per
  hDu_loc := aux.hDu_loc
  hDu_lp := aux.hDu_lp
  hDu_norm_int := aux.hDu_norm_int
  hUbetap_int := aux.hUbetap_int
  hVbetap_int := aux.hVbetap_int
  hVβp := aux.hVβp
  hu_lp_γ := aux.hu_lp_γ

/-- AC2 sanity-check `example` — feed the closed-form
`aprioriInputAuxHyps_of_paperHypotheses` constructor's output through
the existing `aprioriInputs_of_regularizedBareSolution` consumer to
produce an `AprioriDischargeInputs` consumable by `apriori_at_eps`.

Pin the type-shape: a single F.2 strong-VI triple
`(hStrongVI_set, hStrongVI_signed, hStrongVI_transport)` plus the
structural authorised inputs (paper-residue analytic content) lifts
to an `AprioriDischargeInputs`. -/
example
    [AxisMixMeasureHypothesis]
    {ε : ℝ} (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β)) V)
    {βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar h.α h.β) (betaBar h.β) βBarReal' γBarReal')
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vβp_bound : ℝ)
    (hRes_Lp :
      MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u))
    (hFlux_Lp :
      MemLpPer (d := d) (ENNReal.ofReal (gammaBar' h.α h.β))
        (fun x => StationaryMFG.Hamiltonian.mDpH DpH x
                    (fun i => sol.Du i x) (sol.m x)))
    (h_lagr :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < sol.m x)
    (hVbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, sol.u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_int : MeasureTheory.Integrable sol.u
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSabove_int : MeasureTheory.Integrable
              (fun x => |V x| + h.C * (sol.m x ^ h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hLB_int : MeasureTheory.Integrable
                (fun x => sol.m x ^ (h.β + 1))
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hMbeta_int : MeasureTheory.Integrable
                (fun x => sol.m x ^ h.β)
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hRHSbelow_int : MeasureTheory.Integrable
                (fun x =>
                  sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                            + (DpH x (fun i => sol.Du i x) (sol.m x)) ⬝ (fun i => sol.Du i x))
                    + V x * sol.m x
                    + epsTerms x)
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hu_meas : MeasureTheory.AEStronglyMeasurable sol.u
                  (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : StationaryMFG.Periodic.IsPeriodic sol.u)
    (hu_loc : MeasureTheory.LocallyIntegrable sol.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (sol.Du i)
                        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, StationaryMFG.Periodic.IsPeriodic (sol.Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (sol.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_norm_int : MeasureTheory.Integrable
        (fun x => ‖(fun i => sol.Du i x)‖ ^ gammaBar h.α h.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hUbetap_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hVbetap_int : MeasureTheory.Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hStrongVI_set :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u)
    (hStrongVI_signed :
      StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u)
    (hStrongVI_transport :
      StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
        V H DpH (gammaBar h.α h.β) ε sol.Du sol.m sol.u) :
    AprioriDischargeInputs (d := d) h V ε hε :=
  aprioriInputs_of_regularizedBareSolution hε h sol
    (aprioriInputAuxHyps_of_paperHypotheses hε h hV sol
      epsTerms Vbound Vβp_bound hRes_Lp hFlux_Lp h_lagr hMpos hVbnd
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hMbeta_int
      hRHSbelow_int hu_meas hu_per hu_loc hDu_meas hDu_per hDu_loc
      hDu_norm_int hUbetap_int hVbetap_int hVβp
      hStrongVI_set hStrongVI_signed hStrongVI_transport)

/-! ## Consumer-level operator-tendsto compositional lemma

Per `infra-P4-rebuild-T7-discharge-AC1-hMinty` (iter 252+ deferral):
the integrand-level analytic core for the strict-positive
perturbation passage `μ_n := μ + 1/(n+1) → μ` was landed at iter 228
in `Hamiltonian/Estimates.lean` as three named DCT wrappers
(`tendsto_setIntegral_HJB_mul_of_dom`,
`tendsto_setIntegral_flux_mul_of_dom`,
`tendsto_setIntegral_mass_mul_of_dom`). The composition into the
`mfgOperatorEpsPair`-level tendsto consumer was deferred at that
iteration because `mfgOperatorEpsPair` (defined in
`Solutions/Regularized.lean`) is downstream of `Hamiltonian/Estimates.lean`
in the import graph.

This module *does* import `Solutions/Regularized.lean` (transitively
through `Banach/Operator.lean`/`Banach/AbstractLifts.lean`), so it is
the natural place for the consumer-level composition.

**Lemma shape.** Given:

* a sequence of *primal densities* `μ_n` and *test directions* `η_n`,
  both `n`-dependent, with the primal value-function `υ` and
  gradient family `Dυ`, plus the test value-function `ν` and gradient
  family `Dν` all constant in `n`;
* three integrand-level tendstos for the three summands of
  `mfgOperatorPair` (HJB, flux, mass);
* per-`n` and per-limit integrability witnesses for each of the three
  summands (consumed by `mfgOperatorPair_split` to algebraically
  decompose the operator value);

the lemma concludes the operator-level tendsto

```
mfgOperatorEpsPair γBar ε Dυ μ_n υ Dν η_n ν
  → mfgOperatorEpsPair γBar ε Dυ μ_∞ υ Dν η_∞ ν.
```

**Why the gateaux term is trivial.** `gateauxWpPair γBar Dυ υ Dν ν`
depends only on `(Dυ, υ, Dν, ν)`, *not* on `(μ, η)`. Therefore when
those four pieces are held fixed across `n`, the Gateaux summand of
`mfgOperatorEpsPair` is constant in `n`, and the operator-level
tendsto follows by `Tendsto.add_const` from the `mfgOperatorPair`
tendsto.

**How callers invoke this.** The downstream Minty/δ-limit lifts
(`hVIeps_*_of_KAepsi_VI` in this file) consume an `hCont` operator-
tendsto certificate. Each caller supplies the three integrand-level
tendstos via the corresponding `tendsto_setIntegral_*_mul_of_dom`
wrapper from `Hamiltonian/Estimates.lean` (specialised to the
perturbation `μ_n := μ + 1/(n+1)`) and hands the integrability
witnesses (paper-level material from the AC2 dominator-closure
infrastructure plus continuity of `H`/`D_pH` in the third argument).
Those caller-side dischargers are filed as separate follow-up tasks
(`infra-P4-rebuild-T7-AC1-discharge-hCont-{set,signed,transport}`),
each producing a specialisation of the lemma below.
-/

open MeasureTheory Filter

variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- **Consumer-level compositional lemma** lifting three integrand-
level tendstos plus per-`n`/per-limit integrability into an
`mfgOperatorEpsPair`-level tendsto along an additive perturbation
of the *primal density* and *test direction* slots, with the primal
value-function `υ` / gradient family `Dυ` and the test value-function
`ν` / gradient family `Dν` held *constant* in `n`.

The Gateaux pairing `gateauxWpPair γBar Dυ υ Dν ν` does not depend on
`(μ, η)`, so it is constant in `n` and adds trivially to both sides
of the `mfgOperatorPair` tendsto.

The three integrand-level tendsto inputs match the three summands of
`mfgOperatorPair` per `mfgOperatorPair_split`. -/
theorem mfgOperatorEpsPair_tendsto_of_summands
    {γBar ε : ℝ}
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    (μN : ℕ → (Fin d → ℝ) → ℝ) (μInf : (Fin d → ℝ) → ℝ)
    (ηN : ℕ → (Fin d → ℝ) → ℝ) (ηInf : (Fin d → ℝ) → ℝ)
    -- Per-`n` integrability of the three `mfgOperatorPair` summands.
    (h_int1_n : ∀ n,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μN n x) + V x) * ηN n x)
        (volume.restrict (UnitCube d)))
    (h_int2_n : ∀ n,
      Integrable (fun x =>
        μN n x * (DpH x (fun i => Dυ i x) (μN n x) ⬝ (fun i => Dν i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_n : ∀ n,
      Integrable (fun x => (μN n x - 1) * ν x)
        (volume.restrict (UnitCube d)))
    -- Limit integrability of the three summands.
    (h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μInf x) + V x) * ηInf x)
        (volume.restrict (UnitCube d)))
    (h_int2_lim :
      Integrable (fun x =>
        μInf x * (DpH x (fun i => Dυ i x) (μInf x) ⬝ (fun i => Dν i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_lim :
      Integrable (fun x => (μInf x - 1) * ν x)
        (volume.restrict (UnitCube d)))
    -- Three integrand-level tendstos (one per `mfgOperatorPair` summand).
    -- These are typically discharged by the per-summand wrappers
    -- `tendsto_setIntegral_{HJB,flux,mass}_mul_of_dom` from
    -- `Hamiltonian/Estimates.lean`.
    (h_tendsto1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μN n x) + V x) * ηN n x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μInf x) + V x) * ηInf x)))
    (h_tendsto2 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
          μN n x * (DpH x (fun i => Dυ i x) (μN n x) ⬝ (fun i => Dν i x)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          μInf x * (DpH x (fun i => Dυ i x) (μInf x) ⬝ (fun i => Dν i x)))))
    (h_tendsto3 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d, (μN n x - 1) * ν x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (μInf x - 1) * ν x))) :
    Filter.Tendsto
      (fun n => mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBar ε Dυ (μN n) υ Dν (ηN n) ν)
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μInf υ Dν ηInf ν)) := by
  -- Step 1: rewrite both sides via the algebraic split of
  -- `mfgOperatorPair` plus the (constant) Gateaux pairing.
  have hsplit_n : ∀ n,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ (μN n) υ Dν (ηN n) ν
        = ((∫ x in UnitCube d,
              (-(υ x) - H x (fun i => Dυ i x) (μN n x) + V x) * ηN n x)
           + (∫ x in UnitCube d,
                μN n x * (DpH x (fun i => Dυ i x) (μN n x) ⬝ (fun i => Dν i x)))
           + (∫ x in UnitCube d, (μN n x - 1) * ν x))
        + ε * gateauxWpPair γBar Dυ υ Dν ν := by
    intro n
    unfold mfgOperatorEpsPair
    rw [Solutions.MFG.mfgOperatorPair_split (V := V) (H := H) (DpH := DpH)
        Dυ (μN n) υ Dν (ηN n) ν (h_int1_n n) (h_int2_n n) (h_int3_n n)]
  have hsplit_lim :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μInf υ Dν ηInf ν
        = ((∫ x in UnitCube d,
              (-(υ x) - H x (fun i => Dυ i x) (μInf x) + V x) * ηInf x)
           + (∫ x in UnitCube d,
                μInf x * (DpH x (fun i => Dυ i x) (μInf x) ⬝ (fun i => Dν i x)))
           + (∫ x in UnitCube d, (μInf x - 1) * ν x))
        + ε * gateauxWpPair γBar Dυ υ Dν ν := by
    unfold mfgOperatorEpsPair
    rw [Solutions.MFG.mfgOperatorPair_split (V := V) (H := H) (DpH := DpH)
        Dυ μInf υ Dν ηInf ν h_int1_lim h_int2_lim h_int3_lim]
  -- Step 2: rewrite the goal using the splits.
  simp only [hsplit_n, hsplit_lim]
  -- Step 3: the constant Gateaux summand factors out; reduce to the
  -- tendsto of the three-summand sum, plus a constant added on each
  -- side.
  refine Filter.Tendsto.add_const _ ?_
  -- Step 4: assemble the three-summand tendsto by pairwise `Tendsto.add`.
  exact (h_tendsto1.add h_tendsto2).add h_tendsto3

/-! ### Sanity-check `example` for the consumer-level lift

Trivial-case sanity check: for constant primal/test data and
`μ_n ≡ μ_∞ ≡ 1`, `η_n ≡ η_∞ ≡ 0`, all three integrand-level tendstos
collapse to `tendsto_const_nhds` and the lemma instantiates to a
tendsto of a constant sequence. -/
example {γBar ε : ℝ}
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    (h_int1 : Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (1 : ℝ) + V x) * (0 : ℝ))
        (volume.restrict (UnitCube d)))
    (h_int2 : Integrable (fun x =>
        (1 : ℝ) * (DpH x (fun i => Dυ i x) (1 : ℝ) ⬝ (fun i => Dν i x)))
        (volume.restrict (UnitCube d)))
    (h_int3 : Integrable (fun x => ((1 : ℝ) - 1) * ν x)
        (volume.restrict (UnitCube d))) :
    Filter.Tendsto
      (fun _ : ℕ => mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                      γBar ε Dυ (fun _ => (1 : ℝ)) υ Dν (fun _ => (0 : ℝ)) ν)
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ (fun _ => (1 : ℝ)) υ Dν (fun _ => (0 : ℝ)) ν)) := by
  exact mfgOperatorEpsPair_tendsto_of_summands
    Dυ υ Dν ν
    (μN := fun _ _ => (1 : ℝ)) (μInf := fun _ => (1 : ℝ))
    (ηN := fun _ _ => (0 : ℝ)) (ηInf := fun _ => (0 : ℝ))
    (fun _ => h_int1) (fun _ => h_int2) (fun _ => h_int3)
    h_int1 h_int2 h_int3
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds

/-! ## Set-perturbation specialisation: `μ_n := S.indicator ρ + 1/(n+1)`

This section discharges the `hCont` operator-tendsto certificate
consumed by `hVIeps_set_of_KAepsi_VI` (Child C of the two-domain
redesign). The headline lemma
`mfgOperatorEpsPair_tendsto_set_perturbation` specialises the consumer-
level compositional lemma `mfgOperatorEpsPair_tendsto_of_summands`
above at the strict-positive perturbation
`μ_n := S.indicator ρ + 1/(n+1)`, with limit `μ_∞ := S.indicator ρ`.

The three integrand-level tendsto inputs are discharged by invoking
`tendsto_setIntegral_HJB_mul_of_dom`,
`tendsto_setIntegral_flux_mul_of_dom`,
`tendsto_setIntegral_mass_mul_of_dom` (in `Hamiltonian/Estimates.lean`),
each at its proper Hölder pair derived from `(α, β)` exponents in
`HypothesisPowerGrowth`.

Per CONVENTIONS §8 the following are authorised inputs:

* the three per-`x` pointwise tendsto inputs `(g_n, η_n) → (g_∞, η_∞)`
  for the HJB and flux summands (continuity of `H` and `DpH` in the
  third argument; `RegularityH.continuous_*_pm` is `ContinuousOn {m > 0}`
  only, and the limit `μ_∞ = S.indicator ρ` may equal `0` on the
  complement of `S`, so these tendstos are paper-level material);
* the per-`n` and per-limit integrability witnesses for the three
  `mfgOperatorPair` summands (built upstream from the AC2 dominator
  closures `g_dominator_memLp_betaBar'`, `flux_dominator_memLp_gammaBar'`
  paired with Hölder integration of the test side);
* the per-`x` dominator bounds for the three integrand sequences (also
  paper-level, threading through `RegularityH.measurable_*` plus the
  AC2 dominator structure).

This shape exactly matches the abstract pattern set by
`hVIeps_set_of_KAepsi_VI`, which already takes the `hCont` certificate
as an authorised input. The present lemma packages the discharge into
a closed-form `Tendsto`, with the analytic content reduced to the
caller-side authorised inputs listed above. -/

/-- **Headline: `mfgOperatorEpsPair`-tendsto for the set-family Minty
perturbation `μ_n := S.indicator ρ + 1/(n+1)`.**

This is the Child C-specific specialisation of
`mfgOperatorEpsPair_tendsto_of_summands` (above) at the perturbation
arising in `hVIeps_set_of_KAepsi_VI`'s strict-positive bridge.

The proof simply routes:
* the three per-`n`/per-limit integrability witnesses through the
  per-summand integrability slots of `mfgOperatorEpsPair_tendsto_of_summands`,
* the three integrand-level tendstos through
  `tendsto_setIntegral_HJB_mul_of_dom`,
  `tendsto_setIntegral_flux_mul_of_dom`,
  `tendsto_setIntegral_mass_mul_of_dom` from `Hamiltonian/Estimates.lean`,
  with the Hölder pair fixed by `(hpow.α, hpow.β)`.

Per CONVENTIONS §8: the dominators `Gh, Eh, Gf, Ef, Gm, Em` and the
pointwise tendsto inputs are accepted as authorised hypotheses; their
upstream derivation from `RegularityH`/`HypothesisPowerGrowth` plus the
AC2 dominator closures (`g_dominator_memLp_betaBar'`,
`flux_dominator_memLp_gammaBar'`) is not factored out yet. -/

theorem mfgOperatorEpsPair_tendsto_set_perturbation
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {β : ℝ} (hβ : 0 < β)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (_hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (_hρ_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    -- Per-`n` integrability of the three `mfgOperatorPair` summands
    -- at the perturbation `μ_n := S.indicator ρ + 1/(n+1)`.
    (h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
          * (S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x))
        (volume.restrict (UnitCube d)))
    (h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x))
        (volume.restrict (UnitCube d)))
    -- Limit integrability of the three summands at `μ_∞ := S.indicator ρ`.
    (h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x)
          * (S.indicator ρ x - m x))
        (volume.restrict (UnitCube d)))
    (h_int2_lim :
      Integrable (fun x =>
        S.indicator ρ x
          * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_lim :
      Integrable (fun x =>
        (S.indicator ρ x - 1) * (υ x - u x))
        (volume.restrict (UnitCube d)))
    -- Dominator inputs for the three summands, at the (Hölder)-paired
    -- exponents `((β+1)/β, β+1)` for HJB,
    -- `(γ̄/(γ̄-1), γ̄)` for flux, `(β+1, (β+1)/β)` for mass.
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    -- iter 0617 flux-pair retype: `(γ̄', γ̄) → (β̄, β̄')` per
    -- `paperSolFor-supplier-flux-pairing-beta`. Both `Gf` and `Ef`
    -- envelopes now live in standard `β̄`-family slots, eliminating
    -- the `γ̄`/`γ̄'` mismatch.
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x)
    -- Strong measurability of the per-`n` integrand sequences.
    (hgN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)))
    (hηN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
        (volume.restrict (UnitCube d)))
    (hgN2_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)))
    (hηN2_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x))
        (volume.restrict (UnitCube d)))
    (hgN3_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1)
        (volume.restrict (UnitCube d)))
    (hηN3_meas : ∀ _n : ℕ,
      AEStronglyMeasurable (fun x => υ x - u x)
        (volume.restrict (UnitCube d)))
    -- Per-`x` pointwise tendsto inputs (authorised, CONVENTIONS §8).
    -- These come from continuity of `H`, `DpH` in the third argument.
    -- Since `μ_∞ = S.indicator ρ` may equal `0` on `Sᶜ` and
    -- `RegularityH.continuous_*_pm` is `ContinuousOn {m > 0}` only,
    -- these are paper-level inputs.
    (hPointwise_H :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
                    (S.indicator ρ x) + V x)))
    (hPointwise_DpH_prod :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n : ℕ =>
            (S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => Dυ i x)
                  (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x)))
          Filter.atTop
          (𝓝 (S.indicator ρ x *
              (DpH x (fun i => Dυ i x) (S.indicator ρ x)
                ⬝ (fun i => Dυ i x - Du i x))))) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) := by
  -- Shorthand for the perturbation and its limit.
  set μN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμN
  set μInf : (Fin d → ℝ) → ℝ := S.indicator ρ with hμInf
  set ηN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x with hηN
  set ηInf : (Fin d → ℝ) → ℝ := fun x => S.indicator ρ x - m x with hηInf
  -- Pointwise tendsto: `1/(n+1) → 0`.
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Pointwise tendsto: `μ_n x → μ_∞ x` for every `x`.
  have h_μN_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) := by
    intro x
    have := h_one_div_tendsto.const_add (S.indicator ρ x)
    simpa [hμN, hμInf, add_zero] using this
  -- Pointwise tendsto: `η_n x → η_∞ x` for every `x`.
  have h_ηN_pointwise :
      ∀ x, Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) := by
    intro x
    have := (h_one_div_tendsto.const_add (S.indicator ρ x)).sub_const (m x)
    simpa [hηN, hηInf, add_zero] using this
  -- Pointwise tendsto for the mass-summand factor `μ_n - 1`.
  have h_μN1_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x - 1) Filter.atTop
              (𝓝 (μInf x - 1)) :=
    fun x => (h_μN_pointwise x).sub_const 1
  -- A.e. versions.
  have h_μN_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) :=
    Filter.Eventually.of_forall h_μN_pointwise
  have h_ηN_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) :=
    Filter.Eventually.of_forall h_ηN_pointwise
  have h_μN1_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => μN n x - 1) Filter.atTop
              (𝓝 (μInf x - 1)) :=
    Filter.Eventually.of_forall h_μN1_pointwise
  -- Constant-in-`n` tendsto of `(υ - u)`.
  have h_νconst_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun _ : ℕ => υ x - u x) Filter.atTop
          (𝓝 (υ x - u x)) :=
    Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  -- Standing positivity fact on the paper exponent `β`.
  have hβ_pos : 0 < β := hβ
  -- Step 1: HJB integrand-level tendsto via `tendsto_setIntegral_HJB_mul_of_dom`.
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μN n x) + V x) * ηN n x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μInf x) + V x) * ηInf x)) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := β) hβ_pos
      (gN := fun n x =>
        -(υ x) - H x (fun i => Dυ i x) (μN n x) + V x)
      (gInf := fun x =>
        -(υ x) - H x (fun i => Dυ i x) (μInf x) + V x)
      (ηN := ηN) (ηInf := ηInf)
      hGh_memLp hEh_memLp hgN1_meas hηN1_meas hGh_bd hEh_bd ?_ h_ηN_ae
    exact hPointwise_H
  -- Step 2: flux integrand-level tendsto via direct DCT on the
  -- **product** integrand `μ_n · (DpH·v)`. We do NOT factor through
  -- `tendsto_setIntegral_flux_mul_of_dom` here, because that wrapper
  -- requires bare `DpH·v` pointwise tendsto, which is paper-illegal
  -- at points where `μ_∞ = 0` (no `(a:DpHat0)` exists in the paper —
  -- only `(a:mDpHat0)` for `J = m·DpH`). Instead, the consumer
  -- delivers `hPointwise_DpH_prod` (product-form pointwise tendsto)
  -- via `set_perturbation_pointwise_tendsto_DpH`, whose squeeze
  -- argument at `μ_∞ = 0` only uses `hpow.DpH_upper` (paper-correct).
  have h_tendsto2 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          μN n x * (DpH x (fun i => Dυ i x) (μN n x)
                      ⬝ (fun i => Dυ i x - Du i x)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          μInf x * (DpH x (fun i => Dυ i x) (μInf x)
                      ⬝ (fun i => Dυ i x - Du i x)))) := by
    -- iter 0617 flux-pair retype: Apply DCT on the product `μ_n · (DpH·v)`
    -- with dominator `Gf · Ef ∈ L¹` (Hölder pair `(β̄, β̄') = (β+1, (β+1)/β)`).
    set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d)
    set bound : (Fin d → ℝ) → ℝ := fun x => Gf x * Ef x with hbound
    -- L¹ bound from Hölder.
    have hbb_pos : 0 < β + 1 := by linarith
    have hβp_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ_pos
    have hpq :
        Real.HolderConjugate (β + 1) ((β + 1) / β) := by
      refine ⟨?_, hbb_pos, hβp_pos⟩
      field_simp
      ring
    have hbound_int : Integrable bound μm := by
      have := Periodic.MemLpPer.integrable_mul
        (p := β + 1)
        (q := (β + 1) / β)
        hpq hGf_memLp hEf_memLp
      exact this
    -- AE-strong-measurability of the products.
    have hprod_meas : ∀ n,
        AEStronglyMeasurable
          (fun x => μN n x * (DpH x (fun i => Dυ i x) (μN n x)
                        ⬝ (fun i => Dυ i x - Du i x))) μm :=
      fun n => (hgN2_meas n).mul (hηN2_meas n)
    -- Dominator nonnegativity.
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    -- Pointwise dominator bound for the products.
    have hprod_bd : ∀ n, ∀ᵐ x ∂μm,
        ‖μN n x * (DpH x (fun i => Dυ i x) (μN n x)
                    ⬝ (fun i => Dυ i x - Du i x))‖ ≤ bound x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    -- Pointwise convergence of the products: this is exactly
    -- `hPointwise_DpH_prod`.
    have hprod_lim : ∀ᵐ x ∂μm,
        Filter.Tendsto
          (fun n => μN n x * (DpH x (fun i => Dυ i x) (μN n x)
                      ⬝ (fun i => Dυ i x - Du i x)))
          Filter.atTop
          (𝓝 (μInf x * (DpH x (fun i => Dυ i x) (μInf x)
                      ⬝ (fun i => Dυ i x - Du i x)))) := by
      filter_upwards [hPointwise_DpH_prod] with x hx
      simpa [μN, μInf] using hx
    -- DCT.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hprod_meas hbound_int hprod_bd hprod_lim
  -- Step 3: mass integrand-level tendsto via `tendsto_setIntegral_mass_mul_of_dom`.
  have h_tendsto3 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d, (μN n x - 1) * (υ x - u x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (μInf x - 1) * (υ x - u x))) := by
    refine Hamiltonian.tendsto_setIntegral_mass_mul_of_dom (β := β) hβ_pos
      (gN := fun n x => μN n x - 1) (gInf := fun x => μInf x - 1)
      (ηN := fun _ x => υ x - u x) (ηInf := fun x => υ x - u x)
      hGm_memLp hEm_memLp hgN3_meas hηN3_meas hGm_bd ?_ h_μN1_ae h_νconst_ae
    intro _
    exact hEm_bd
  -- Bridge integrals to the `(υ - u)` formulation used by the consumer.
  -- Since `υ - u` and `fun x => υ x - u x` are equal as functions, this
  -- requires a `simp [Pi.sub_apply]` rewrite at the integrals.
  have h_νsub_eq : (υ - u) = fun x => υ x - u x := rfl
  -- Apply the consumer-level compositional lemma.
  have h_main :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (μN n) υ
            (fun i x => Dυ i x - Du i x)
            (ηN n) (fun x => υ x - u x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ μInf υ
              (fun i x => Dυ i x - Du i x)
              ηInf (fun x => υ x - u x))) := by
    refine mfgOperatorEpsPair_tendsto_of_summands
      (V := V) (H := H) (DpH := DpH)
      Dυ υ (fun i x => Dυ i x - Du i x) (fun x => υ x - u x)
      μN μInf ηN ηInf
      h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
      h_tendsto1 h_tendsto2 h_tendsto3
  -- Convert `fun x => υ x - u x` to `υ - u` (definitionally equal as
  -- bare Lean functions) — this is `rfl` modulo `Pi.sub_apply`.
  have h_test_eq :
      (fun x => υ x - u x) = υ - u := by
    funext x; rfl
  rw [h_test_eq] at h_main
  -- Identify `ηInf = S.indicator ρ - m` and `μInf = S.indicator ρ` and
  -- `ηN n = fun x => S.indicator ρ x + 1/(n+1) - m x` and `μN n` similarly.
  -- These are all `rfl` modulo bare-function `Pi.sub_apply` unfolding.
  have h_ηInf_eq : ηInf = S.indicator ρ - m := by
    funext x; simp [hηInf, Pi.sub_apply]
  rw [h_ηInf_eq] at h_main
  -- The body of `μN`, `μInf`, `ηN` is already in the headline form by
  -- definition (`hμN`, `hμInf`, `hηN`).
  exact h_main

/-! ### Phase G — set-perturbation AE-strong measurability witnesses
(task `infra-P5-phase-G-set-dominator-bounds-and-measurability`).

The `mfgOperatorEpsPair_tendsto_set_perturbation` lemma above consumes
six AE-strong-measurability witnesses for the per-`n` integrand
sequences at the perturbation `μ_n := S.indicator ρ + 1/(n+1)`.

This subsection lands six closed-form derivations of those witnesses
from the underlying joint-measurability fields
`hpow.measurable_H`, `hpow.measurable_DpH`, plus per-coordinate
measurability of the test-triple data `(Sρ, Dυ, Du, υ, u, m, V)`.

The six pointwise a.e. dominator bounds (`hGh_bd`, `hEh_bd`, `hGf_bd`,
`hEf_bd`, `hGm_bd`, `hEm_bd`) — which require `H_upper_pointwise`,
`DpH_upper`, the lower bound, and Cauchy–Schwarz — are deferred to the
sister task `infra-P5-phase-G-set-dominator-ae-bounds`.
-/

/-- AE-strong measurability of `x ↦ S.indicator ρ x + 1/(n+1)`. The
core building block: the perturbation `μ_n` itself is measurable
whenever `S` is measurable and `ρ` is measurable. -/
theorem set_perturbation_μN_meas
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ)
    (n : ℕ) :
    AEStronglyMeasurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1))
      (volume.restrict (UnitCube d)) := by
  have h1 : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
    hρ.indicator hS
  have h2 : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    h1.add_const _
  exact h2.aestronglyMeasurable

/-- **`gN2_meas`** — AE-strong measurability of the flux μ-factor
`x ↦ S.indicator ρ x + 1/(n+1)`. -/
theorem set_perturbation_gN2_meas
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)) :=
  fun n => set_perturbation_μN_meas hS hρ n

/-- **`ηN1_meas`** — AE-strong measurability of the HJB η-factor
`x ↦ S.indicator ρ x + 1/(n+1) - m x`. -/
theorem set_perturbation_ηN1_meas
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ m : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ) (hm : Measurable m) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
        (volume.restrict (UnitCube d)) := by
  intro n
  have h1 : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
    hρ.indicator hS
  have h2 : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    h1.add_const _
  have h3 : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) :=
    h2.sub hm
  exact h3.aestronglyMeasurable

/-- **`gN3_meas`** — AE-strong measurability of the mass μ-factor
`x ↦ S.indicator ρ x + 1/(n+1) - 1`. -/
theorem set_perturbation_gN3_meas
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1)
        (volume.restrict (UnitCube d)) := by
  intro n
  have h1 : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
    hρ.indicator hS
  have h2 : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    h1.add_const _
  have h3 : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) :=
    h2.sub_const _
  exact h3.aestronglyMeasurable

/-- **`ηN3_meas`** — AE-strong measurability of the mass test-factor
`x ↦ υ x - u x` (constant in `n`). -/
theorem set_perturbation_ηN3_meas
    {υ u : (Fin d → ℝ) → ℝ} (hυ : Measurable υ) (hu : Measurable u) :
    ∀ _n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => υ x - u x)
        (volume.restrict (UnitCube d)) := by
  intro _
  exact (hυ.sub hu).aestronglyMeasurable

/-- **`gN1_meas_of_aeMeasH`** (D2b-1c-ii-b, route (b)) — AE-strong
measurability of the HJB g-factor
`x ↦ -υ x - H x (fun i ↦ Dυ i x) (S.indicator ρ x + 1/(n+1)) + V x`,
consuming the H-composition `x ↦ H x (Dυ · x) (μ_n x)` as a per-`n`
AE composite `hHcomp_ae` INSTEAD of the strict global `hpow.measurable_H`.
This is the AE entry point the `HdeltaK0`/T3 path needs (there is no global
strict `measurable_H` on `HdeltaK0`; only the AE composite from
`aemeasurable_HdeltaK0_comp_of_rc0`). -/
theorem set_perturbation_gN1_meas_of_aeMeasH
    {S : Set (Fin d → ℝ)}
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hHcomp_ae : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d))) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)) := by
  intro n
  exact (((hυ.aemeasurable.neg).sub (hHcomp_ae n)).add
    hV.aemeasurable).aestronglyMeasurable

/-- **`gN1_meas`** — AE-strong measurability of the HJB g-factor
`x ↦ -υ x - H x (fun i ↦ Dυ i x) (S.indicator ρ x + 1/(n+1)) + V x`.
The H-composition uses joint measurability `hpow.measurable_H`, but the
density is strictly positive (`+1/(n+1)`); the strict global field is
consumed only as an AE composite (`comp_aemeasurable`), and the proof
DELEGATES to `set_perturbation_gN1_meas_of_aeMeasH`. -/
theorem set_perturbation_gN1_meas
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hρ : Measurable ρ) (hV : Measurable V) (hυ : Measurable υ)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hDυ : ∀ i, Measurable (Dυ i)) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)) := by
  -- Derive the per-`n` AE composite from the strict global field via
  -- `comp_aemeasurable`, then delegate to the `_of_aeMeasH` variant.
  refine set_perturbation_gN1_meas_of_aeMeasH (H := H)
    hV.aestronglyMeasurable hυ.aestronglyMeasurable (fun n => ?_)
  have hSρ : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
    hρ.indicator hS
  have hμ : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    hSρ.add_const _
  have hDυ_pi : Measurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
    measurable_pi_iff.mpr hDυ
  have hxpm : Measurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => Dυ i x),
            S.indicator ρ x + 1 / ((n : ℝ) + 1))) :=
    measurable_id.prodMk (hDυ_pi.prodMk hμ)
  exact hpow.measurable_H.comp_aemeasurable hxpm.aemeasurable

/-- **`ηN2_meas_of_meas`** (D2b-1c-ii-c2, step 1, DpH-side decoupling) —
AE-strong measurability of the flux η-factor
`x ↦ DpH x (fun i ↦ Dυ i x) (S.indicator ρ x + 1/(n+1)) ⬝
     (fun i ↦ Dυ i x - Du i x)`, taking the joint measurability of `DpH`
(`hDpH_meas : Measurable (uncurry DpH)`) DIRECTLY instead of the whole
`HypothesisPowerGrowth` bundle.

This is the decoupled DpH-side entry point. `DpHepsilonFam` is globally
measurable (D2b-1a), so the DpH composite always composes *strictly* via
`hDpH_meas.comp`; no AE composite is needed on the DpH side. The strict
`set_perturbation_ηN2_meas` delegates by supplying `hpow.measurable_DpH`. -/
theorem set_perturbation_ηN2_meas_of_meas
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ)
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i)) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x))
        (volume.restrict (UnitCube d)) := by
  intro n
  -- `μ_n` is measurable.
  have hSρ : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
    hρ.indicator hS
  have hμ : Measurable
      (fun x : (Fin d → ℝ) => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    hSρ.add_const _
  -- `fun x => fun i => Dυ i x` is measurable into `Fin d → ℝ`.
  have hDυ_pi : Measurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
    measurable_pi_iff.mpr hDυ
  -- The composite `x ↦ (x, (fun i ↦ Dυ i x), μ_n x)` is measurable.
  have hxpm : Measurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => Dυ i x),
            S.indicator ρ x + 1 / ((n : ℝ) + 1))) :=
    measurable_id.prodMk (hDυ_pi.prodMk hμ)
  -- Compose with the decoupled `hDpH_meas` (DpH globally measurable).
  have hDpHcomp : Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))) :=
    hDpH_meas.comp hxpm
  -- Per-coordinate measurability of the DpH-composition.
  have hDpHcomp_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)) i) :=
    fun i => (measurable_pi_apply i).comp hDpHcomp
  -- Per-coordinate measurability of `Dυ i x - Du i x`.
  have hDdiff_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) => Dυ i x - Du i x) :=
    fun i => (hDυ i).sub (hDu i)
  -- Each summand `(DpH _ i) * (Dυ i - Du i)` is measurable.
  have hsum_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)) i
          * (Dυ i x - Du i x)) :=
    fun i => (hDpHcomp_i i).mul (hDdiff_i i)
  -- The dot product `⬝` is the finite sum.
  have hdot : Measurable
      (fun x : (Fin d → ℝ) =>
        ∑ i : Fin d,
          DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)) i
            * (Dυ i x - Du i x)) :=
    Finset.measurable_sum _ (fun i _ => hsum_i i)
  have hdot_eq :
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          ⬝ (fun i => Dυ i x - Du i x))
        = (fun x : (Fin d → ℝ) =>
            ∑ i : Fin d,
              DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) i
                * (Dυ i x - Du i x)) := by
    funext x
    rfl
  rw [hdot_eq]
  exact hdot.aestronglyMeasurable

/-- **`ηN2_meas`** — AE-strong measurability of the flux η-factor
`x ↦ DpH x (fun i ↦ Dυ i x) (S.indicator ρ x + 1/(n+1)) ⬝
     (fun i ↦ Dυ i x - Du i x)`. The DpH-composition uses joint
measurability `hpow.measurable_DpH`. DELEGATES to
`set_perturbation_ηN2_meas_of_meas`. -/
theorem set_perturbation_ηN2_meas
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : Measurable ρ)
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i)) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x))
        (volume.restrict (UnitCube d)) :=
  set_perturbation_ηN2_meas_of_meas hpow.measurable_DpH hS hρ hDυ hDu

/-! ### Set-perturbation pointwise dominator a.e. bounds

These six lemmas discharge the per-`n` a.e. dominator bounds consumed
by `mfgOperatorEpsPair_tendsto_set_perturbation`. Four are routine
triangle inequalities (`hEh_bd`, `hGf_bd`, `hGm_bd`, `hEm_bd`); two
require the analytic content of `HypothesisPowerGrowth`
(`hGh_bd` via `H_upper_pointwise` plus `lower`; `hEf_bd` via
`DpH_upper` plus Cauchy–Schwarz). All bounds are pointwise (the `∀ᵐ`
quantifier is only used for the bounds that route through `H`/`DpH`
upper bounds, which are themselves a.e. statements).

Sister to `set_perturbation_*_meas` (lines 1963–2163 above), discharging
the AE-strong-measurability witnesses.

Per task `infra-P5-phase-G-set-dominator-ae-bounds`. -/

/-- Helper: `0 < 1/((n:ℝ)+1)` for any `n : ℕ`. -/
private lemma set_perturbation_one_div_pos (n : ℕ) :
    (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
  have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact one_div_pos.mpr h

/-- Helper: `1/((n:ℝ)+1) ≤ 1` for any `n : ℕ`. -/
private lemma set_perturbation_one_div_le_one (n : ℕ) :
    (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ h1, one_mul]
  have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  linarith

/-- **`hEh_bd`** — pointwise bound on the HJB η-factor:
`‖S.indicator ρ x + 1/(n+1) - m x‖ ≤ |S.indicator ρ x| + 1 + |m x|`. -/
theorem set_perturbation_hEh_bd
    {S : Set (Fin d → ℝ)} {ρ m : (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖
          ≤ |S.indicator ρ x| + 1 + |m x| := by
  intro n
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x|
      ≤ |S.indicator ρ x + 1 / ((n : ℝ) + 1)| + |m x| := abs_sub _ _
  have h2 : |S.indicator ρ x + 1 / ((n : ℝ) + 1)|
      ≤ |S.indicator ρ x| + |1 / ((n : ℝ) + 1)| := abs_add_le _ _
  have h3 : |1 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_pos (set_perturbation_one_div_pos n)]
    exact set_perturbation_one_div_le_one n
  linarith

/-- **`hGf_bd`** — pointwise bound on the flux μ-factor:
`‖S.indicator ρ x + 1/(n+1)‖ ≤ |S.indicator ρ x| + 1`. -/
theorem set_perturbation_hGf_bd
    {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖
          ≤ |S.indicator ρ x| + 1 := by
  intro n
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |S.indicator ρ x + 1 / ((n : ℝ) + 1)|
      ≤ |S.indicator ρ x| + |1 / ((n : ℝ) + 1)| := abs_add_le _ _
  have h2 : |1 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_pos (set_perturbation_one_div_pos n)]
    exact set_perturbation_one_div_le_one n
  linarith

/-- **`hGm_bd`** — pointwise bound on the mass μ-factor:
`‖S.indicator ρ x + 1/(n+1) - 1‖ ≤ |S.indicator ρ x| + 2`. -/
theorem set_perturbation_hGm_bd
    {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖
          ≤ |S.indicator ρ x| + 2 := by
  intro n
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1|
      ≤ |S.indicator ρ x + 1 / ((n : ℝ) + 1)| + |(1 : ℝ)| := abs_sub _ _
  have h2 : |S.indicator ρ x + 1 / ((n : ℝ) + 1)|
      ≤ |S.indicator ρ x| + |1 / ((n : ℝ) + 1)| := abs_add_le _ _
  have h3 : |1 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_pos (set_perturbation_one_div_pos n)]
    exact set_perturbation_one_div_le_one n
  have h4 : |(1 : ℝ)| = 1 := abs_one
  linarith

/-- **`hEm_bd`** — pointwise bound on the mass test factor (constant in
`n`): `‖υ x - u x‖ ≤ |υ x - u x|`. Trivial via `Real.norm_eq_abs`. -/
theorem set_perturbation_hEm_bd
    {υ u : (Fin d → ℝ) → ℝ} :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖υ x - u x‖ ≤ |υ x - u x| := by
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]

/-! #### Analytic bounds (`hGh_bd`, `hEf_bd`)

These two bounds use the analytic fields of `HypothesisPowerGrowth`:
* `hGh_bd` combines `H_upper_pointwise` (yields `H ≤ C(‖p‖^α + 1) -
  m^β/C`, hence `H ≤ C(‖p‖^α + 1)` since `m^β/C ≥ 0`) with `lower`
  (yields `H ≥ ‖p‖^α/C - C(m^β + 1)`, hence `-H ≤ C(m^β + 1)`). The
  envelope absorbs `μ_n^β` into `(|Sρ x|+1)^β` via monotonicity of
  `t ↦ t^β` on `[0, ∞)`.
* `hEf_bd` uses `DpH_upper` and Cauchy–Schwarz `|v⬝w| ≤ √(v·v)·√(w·w)
  ≤ ‖v‖·‖w‖`.

Both require `μ_n > 0`, which follows from `0 ≤ S.indicator ρ`
(itself from `0 ≤ ρ` a.e.) plus `1/(n+1) > 0`. They also use that
`μ_n ≤ |Sρ x| + 1` since `Sρ ≥ 0 ⇒ Sρ = |Sρ|` and `1/(n+1) ≤ 1`. -/

/-- **`hGh_bd`** — pointwise bound on the HJB g-factor:
`‖-υ x - H x (Dυ, μ_n) + V x‖ ≤ Gh x` with envelope
`Gh x := (h.C+1) · (‖Dυ‖^α + 1) + h.C · ((|Sρ x|+1)^β + 1) + |υ x| + |V x|`. -/
theorem set_perturbation_hGh_bd
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)}
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖
          ≤ (hpow.C + 1) * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
              + hpow.C * ((|S.indicator ρ x| + 1) ^ hpow.β + 1)
              + |υ x| + |V x| := by
  intro n
  -- Standing positivity facts.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hC_pos : 0 < hpow.C := hpow.hC
  have hone_div_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    set_perturbation_one_div_pos n
  have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    set_perturbation_one_div_le_one n
  -- Combine `H_upper_pointwise`, `lower`, and `hρ_nn` via `filter_upwards`.
  filter_upwards [hpow.H_upper_pointwise, hpow.lower, hρ_nn]
    with x hx_upper hx_lower hx_ρ_nn
  -- Set up `μ_n x` and its key properties.
  set μn : ℝ := S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμn_def
  -- `S.indicator ρ x ≥ 0` since `ρ x ≥ 0`.
  have hSρ_nn : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun _ _ => hx_ρ_nn) x
  -- `μn > 0` since `S.indicator ρ x ≥ 0` and `1/(n+1) > 0`.
  have hμn_pos : 0 < μn := by
    rw [hμn_def]
    linarith
  have hμn_nn : 0 ≤ μn := le_of_lt hμn_pos
  -- `μn ≤ |Sρ x| + 1` since `|Sρ x| = Sρ x` (when `Sρ ≥ 0`) and `1/(n+1) ≤ 1`.
  have hSρ_abs : |S.indicator ρ x| = S.indicator ρ x := abs_of_nonneg hSρ_nn
  have hμn_le_env : μn ≤ |S.indicator ρ x| + 1 := by
    rw [hμn_def, hSρ_abs]
    linarith
  -- Apply `H_upper_pointwise` at `(p, μn)`: `H ≤ C·(‖p‖^α + 1) - μn^β/C`.
  have hH_upper := hx_upper (fun i => Dυ i x) μn hμn_pos
  -- Apply `lower` at `(p, μn)`: `H ≥ ‖p‖^α/C - C·(μn^β + 1)`.
  have hH_lower := hx_lower (fun i => Dυ i x) μn hμn_pos
  -- From `H_upper_pointwise`, since `μn^β / C ≥ 0`:
  -- `H ≤ C·(‖p‖^α + 1)`.
  have hμn_β_nn : 0 ≤ μn ^ hpow.β := Real.rpow_nonneg hμn_nn _
  have hμn_β_div_C_nn : 0 ≤ (μn ^ hpow.β) / hpow.C :=
    div_nonneg hμn_β_nn (le_of_lt hC_pos)
  have hH_upper' : H x (fun i => Dυ i x) μn
      ≤ hpow.C * (‖fun i => Dυ i x‖ ^ hpow.α + 1) := by
    linarith
  -- From `lower`, since `‖p‖^α/C ≥ 0`: `-H ≤ C·(μn^β + 1)`.
  have hp_α_nn : 0 ≤ ‖fun i => Dυ i x‖ ^ hpow.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hp_α_div_C_nn : 0 ≤ ‖fun i => Dυ i x‖ ^ hpow.α / hpow.C :=
    div_nonneg hp_α_nn (le_of_lt hC_pos)
  have hH_lower' : -H x (fun i => Dυ i x) μn
      ≤ hpow.C * (μn ^ hpow.β + 1) := by
    linarith
  -- Bound `μn^β ≤ (|Sρ x|+1)^β` using monotonicity of `t ↦ t^β` on `[0, ∞)`
  -- (β > 0).
  have hSρ_env_nn : 0 ≤ |S.indicator ρ x| + 1 := by
    have := abs_nonneg (S.indicator ρ x); linarith
  have hμn_β_le : μn ^ hpow.β ≤ (|S.indicator ρ x| + 1) ^ hpow.β :=
    Real.rpow_le_rpow hμn_nn hμn_le_env (le_of_lt hβ_pos)
  -- Triangle: `‖-υ - H + V‖ ≤ |υ| + |H| + |V|`.
  have habs1 : |-(υ x) - H x (fun i => Dυ i x) μn + V x|
      ≤ |-(υ x) - H x (fun i => Dυ i x) μn| + |V x| := abs_add_le _ _
  have habs2 : |-(υ x) - H x (fun i => Dυ i x) μn|
      ≤ |υ x| + |H x (fun i => Dυ i x) μn| := by
    have := abs_sub (-(υ x)) (H x (fun i => Dυ i x) μn)
    rw [abs_neg] at this
    linarith
  -- Bound `|H|` via `H_upper'` and `H_lower'`.
  -- We have `H ≤ A` and `-H ≤ B`, with `A, B ≥ 0`, so `|H| ≤ A + B`.
  have hA_nn : 0 ≤ hpow.C * (‖fun i => Dυ i x‖ ^ hpow.α + 1) := by
    have h1 : 0 ≤ ‖fun i => Dυ i x‖ ^ hpow.α + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hB_nn : 0 ≤ hpow.C * (μn ^ hpow.β + 1) := by
    have h1 : 0 ≤ μn ^ hpow.β + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hH_abs : |H x (fun i => Dυ i x) μn|
      ≤ hpow.C * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
          + hpow.C * (μn ^ hpow.β + 1) := by
    -- `|H| ≤ A+B` iff `-(A+B) ≤ H ≤ A+B`. We have `H ≤ A` and `-H ≤ B`,
    -- with `A, B ≥ 0`.
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  -- Finally bound `μn^β` by `(|Sρ x|+1)^β`.
  have hH_abs' : |H x (fun i => Dυ i x) μn|
      ≤ hpow.C * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
          + hpow.C * ((|S.indicator ρ x| + 1) ^ hpow.β + 1) := by
    have h1 : hpow.C * (μn ^ hpow.β + 1)
        ≤ hpow.C * ((|S.indicator ρ x| + 1) ^ hpow.β + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
      linarith
    linarith
  -- Combine.
  rw [Real.norm_eq_abs]
  -- Goal: `|-υ - H + V| ≤ (C+1)·(‖p‖^α+1) + C·((|Sρ|+1)^β + 1) + |υ| + |V|`.
  -- We have:
  --   `|-υ - H + V| ≤ |υ| + |H| + |V|`
  --   `|H| ≤ C·(‖p‖^α+1) + C·((|Sρ|+1)^β+1)`
  -- So `|·| ≤ |υ| + |V| + C·(‖p‖^α+1) + C·((|Sρ|+1)^β+1)`.
  -- The envelope has `(C+1)·(‖p‖^α+1)` instead of `C·(‖p‖^α+1)`. The
  -- extra `1·(‖p‖^α+1) = ‖p‖^α+1 ≥ 0` is slack.
  have hslack : 0 ≤ ‖fun i => Dυ i x‖ ^ hpow.α + 1 := by linarith
  nlinarith [hH_abs', habs1, habs2, hslack]

/-- **`set_perturbation_hGh_bd_ae`** — bare/AE sibling of `set_perturbation_hGh_bd`
(EXPERT RULING #4 retype, D2c-2e-1 child B).

Identical HJB g-factor pointwise envelope bound, but keyed on plain exponents
`(β α C : ℝ)` with positivity facts `(hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)` and
taking the two **AE** analytic bounds (`H_upper_pointwise`-shaped + `lower`-shaped)
as plain `∀ᵐ` arguments `hH_upper_pt` / `hlower`, INSTEAD of consuming
`hpow : HypothesisPowerGrowth`. The strict proof consumes `hpow` ONLY through
`hpow.H_upper_pointwise`, `hpow.lower`, the values `hpow.{C,α,β}` and positivity
`hpow.{hC,hβ}`; none of `RegularityH`/`DpH_upper`/`lagr`/`upper`. So the result is
value/positivity + a.e.-bound-level — exactly the inputs the T3 `setTendstoResidue`
envelope can supply off the AE carrier.

Body is the verbatim adaptation of `set_perturbation_hGh_bd` with
`hpow.H_upper_pointwise ↦ hH_upper_pt`, `hpow.lower ↦ hlower`, `hpow.C ↦ C`,
`hpow.α ↦ α`, `hpow.β ↦ β`, `hpow.hC ↦ hC`, `hpow.hβ ↦ hβ`. -/
theorem set_perturbation_hGh_bd_ae
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {S : Set (Fin d → ℝ)}
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hH_upper_pt : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C)
    (hlower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)) :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖
          ≤ (C + 1) * (‖fun i => Dυ i x‖ ^ α + 1)
              + C * ((|S.indicator ρ x| + 1) ^ β + 1)
              + |υ x| + |V x| := by
  intro n
  -- Standing positivity facts.
  have hβ_pos : 0 < β := hβ
  have hC_pos : 0 < C := hC
  have hone_div_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    set_perturbation_one_div_pos n
  have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    set_perturbation_one_div_le_one n
  -- Combine the AE `H_upper_pointwise`/`lower` bounds with `hρ_nn`.
  filter_upwards [hH_upper_pt, hlower, hρ_nn]
    with x hx_upper hx_lower hx_ρ_nn
  set μn : ℝ := S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμn_def
  have hSρ_nn : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun _ _ => hx_ρ_nn) x
  have hμn_pos : 0 < μn := by
    rw [hμn_def]
    linarith
  have hμn_nn : 0 ≤ μn := le_of_lt hμn_pos
  have hSρ_abs : |S.indicator ρ x| = S.indicator ρ x := abs_of_nonneg hSρ_nn
  have hμn_le_env : μn ≤ |S.indicator ρ x| + 1 := by
    rw [hμn_def, hSρ_abs]
    linarith
  have hH_upper := hx_upper (fun i => Dυ i x) μn hμn_pos
  have hH_lower := hx_lower (fun i => Dυ i x) μn hμn_pos
  have hμn_β_nn : 0 ≤ μn ^ β := Real.rpow_nonneg hμn_nn _
  have hμn_β_div_C_nn : 0 ≤ (μn ^ β) / C :=
    div_nonneg hμn_β_nn (le_of_lt hC_pos)
  have hH_upper' : H x (fun i => Dυ i x) μn
      ≤ C * (‖fun i => Dυ i x‖ ^ α + 1) := by
    linarith
  have hp_α_nn : 0 ≤ ‖fun i => Dυ i x‖ ^ α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hp_α_div_C_nn : 0 ≤ ‖fun i => Dυ i x‖ ^ α / C :=
    div_nonneg hp_α_nn (le_of_lt hC_pos)
  have hH_lower' : -H x (fun i => Dυ i x) μn
      ≤ C * (μn ^ β + 1) := by
    linarith
  have hSρ_env_nn : 0 ≤ |S.indicator ρ x| + 1 := by
    have := abs_nonneg (S.indicator ρ x); linarith
  have hμn_β_le : μn ^ β ≤ (|S.indicator ρ x| + 1) ^ β :=
    Real.rpow_le_rpow hμn_nn hμn_le_env (le_of_lt hβ_pos)
  have habs1 : |-(υ x) - H x (fun i => Dυ i x) μn + V x|
      ≤ |-(υ x) - H x (fun i => Dυ i x) μn| + |V x| := abs_add_le _ _
  have habs2 : |-(υ x) - H x (fun i => Dυ i x) μn|
      ≤ |υ x| + |H x (fun i => Dυ i x) μn| := by
    have := abs_sub (-(υ x)) (H x (fun i => Dυ i x) μn)
    rw [abs_neg] at this
    linarith
  have hA_nn : 0 ≤ C * (‖fun i => Dυ i x‖ ^ α + 1) := by
    have h1 : 0 ≤ ‖fun i => Dυ i x‖ ^ α + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hB_nn : 0 ≤ C * (μn ^ β + 1) := by
    have h1 : 0 ≤ μn ^ β + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hH_abs : |H x (fun i => Dυ i x) μn|
      ≤ C * (‖fun i => Dυ i x‖ ^ α + 1)
          + C * (μn ^ β + 1) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have hH_abs' : |H x (fun i => Dυ i x) μn|
      ≤ C * (‖fun i => Dυ i x‖ ^ α + 1)
          + C * ((|S.indicator ρ x| + 1) ^ β + 1) := by
    have h1 : C * (μn ^ β + 1)
        ≤ C * ((|S.indicator ρ x| + 1) ^ β + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
      linarith
    linarith
  rw [Real.norm_eq_abs]
  have hslack : 0 ≤ ‖fun i => Dυ i x‖ ^ α + 1 := by linarith
  nlinarith [hH_abs', habs1, habs2, hslack]

/-- **`signed_perturbation_hGh_bd`** — pointwise bound on the HJB g-factor
for the **signed family** `μ_n := m + σ · m · 1_S + 1/(n+1)` with
`σ ∈ {±1}` and `m ≥ 0` a.e.:
`‖-u - H(Du, μ_n) + V‖ ≤ Gh x` with envelope
`Gh x := (h.C+1) · (‖Du‖^α + 1) + h.C · ((2·|m x| + 1)^β + 1) + |u x| + |V x|`.

Mirrors `set_perturbation_hGh_bd` with `Sρ ↦ 2·|m|`. Uses `μ_n > 0`
(from `m ≥ 0`, `|σ·1_S| ≤ 1`, `1/(n+1) > 0`) and `μ_n ≤ 2·|m| + 1`
(from `m ≥ 0 ⇒ |m| = m`, `|σ·1_S| ≤ 1`, `1/(n+1) ≤ 1`). -/
theorem signed_perturbation_hGh_bd
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)}
    {m V u : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖
          ≤ (hpow.C + 1) * (‖fun i => Du i x‖ ^ hpow.α + 1)
              + hpow.C * ((2 * |m x| + 1) ^ hpow.β + 1)
              + |u x| + |V x| := by
  intro n
  -- Standing positivity facts.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hC_pos : 0 < hpow.C := hpow.hC
  have hone_div_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    set_perturbation_one_div_pos n
  have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    set_perturbation_one_div_le_one n
  -- Sign bound: `|σ| ≤ 1`.
  have hσ_abs : |σ| ≤ 1 := by
    rcases hσ with h | h <;> simp [h]
  -- Combine via `filter_upwards`.
  filter_upwards [hpow.H_upper_pointwise, hpow.lower, hm_nn]
    with x hx_upper hx_lower hx_m_nn
  -- Indicator bound: `0 ≤ 1_S x ≤ 1`.
  have hInd_bd :
      0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
    by_cases hxS : x ∈ S
    · refine ⟨?_, ?_⟩
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_mem hxS]
    · refine ⟨?_, ?_⟩
      · simp [Set.indicator_of_notMem hxS]
      · simp [Set.indicator_of_notMem hxS]
  -- Set up `μ_n x` and its key properties.
  set μn : ℝ := m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) with hμn_def
  -- `1 + σ · 1_S x ≥ 0` (since `σ ≥ -1` and `1_S ∈ [0,1]`).
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with h | h <;> linarith
  have hone_plus_sigma_ind_nn :
      0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    -- `σ * 1_S x ≥ -1 * 1 = -1` (since `σ ≥ -1` and `1_S x ∈ [0, 1]`).
    have hσ_ind_lb :
        -1 ≤ σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      have : -1 * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              ≤ σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
        mul_le_mul_of_nonneg_right hσ_lb hInd_bd.1
      have : -S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              ≤ σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        have heq : (-1 : ℝ) * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    = -S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          ring
        rw [heq] at this; exact this
      linarith [hInd_bd.2]
    linarith
  -- `m x + σ · m x · 1_S x = m x · (1 + σ · 1_S x) ≥ 0` (m ≥ 0, factor ≥ 0).
  have hm_term_nn :
      0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    have hprod_nn : 0 ≤ m x * (1 + σ * S.indicator
                                (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      mul_nonneg hx_m_nn hone_plus_sigma_ind_nn
    have heq : m x * (1 + σ * S.indicator
                                (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                = m x + σ * m x * S.indicator
                                  (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      ring
    linarith [hprod_nn, heq.ge, heq.le]
  -- `μn > 0`.
  have hμn_pos : 0 < μn := by
    rw [hμn_def]
    linarith
  have hμn_nn : 0 ≤ μn := le_of_lt hμn_pos
  -- `μn ≤ 2·|m| + 1`. From `m x ≤ |m x|`, `|σ · m · 1_S| ≤ |m|`, `1/(n+1) ≤ 1`.
  have hm_le_abs : m x ≤ |m x| := le_abs_self _
  have hσm_ind_abs_le :
      |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ |m x| := by
    have h1 : |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              = |σ| * |m x| * |S.indicator
                                (fun _ : Fin d → ℝ => (1 : ℝ)) x| := by
      rw [abs_mul, abs_mul]
    have hInd_abs :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg hInd_bd.1]; exact hInd_bd.2
    have habs_m_nn : 0 ≤ |m x| := abs_nonneg _
    have h2 : |σ| * |m x| ≤ 1 * |m x| :=
      mul_le_mul_of_nonneg_right hσ_abs habs_m_nn
    have h3 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ |σ| * |m x| * 1 := by
      apply mul_le_mul_of_nonneg_left hInd_abs
      exact mul_nonneg (abs_nonneg _) habs_m_nn
    have h4 : |σ| * |m x| * 1 ≤ 1 * |m x| * 1 := by
      have := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    have h5 : 1 * |m x| * 1 = |m x| := by ring
    linarith [h1.le, h1.ge, h3, h4, h5.le, h5.ge]
  have hσm_ind_le :
      σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ |m x| := by
    have := le_abs_self (σ * m x * S.indicator
                          (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    linarith [hσm_ind_abs_le]
  have hμn_le_env : μn ≤ 2 * |m x| + 1 := by
    rw [hμn_def]
    linarith [hm_le_abs, hσm_ind_le, hone_div_le_one]
  -- Apply `H_upper_pointwise` at `(p, μn)`.
  have hH_upper := hx_upper (fun i => Du i x) μn hμn_pos
  have hH_lower := hx_lower (fun i => Du i x) μn hμn_pos
  -- From `H_upper_pointwise`, since `μn^β / C ≥ 0`:
  -- `H ≤ C·(‖p‖^α + 1)`.
  have hμn_β_nn : 0 ≤ μn ^ hpow.β := Real.rpow_nonneg hμn_nn _
  have hμn_β_div_C_nn : 0 ≤ (μn ^ hpow.β) / hpow.C :=
    div_nonneg hμn_β_nn (le_of_lt hC_pos)
  have hH_upper' : H x (fun i => Du i x) μn
      ≤ hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1) := by
    linarith
  -- From `lower`, since `‖p‖^α/C ≥ 0`: `-H ≤ C·(μn^β + 1)`.
  have hp_α_nn : 0 ≤ ‖fun i => Du i x‖ ^ hpow.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hp_α_div_C_nn : 0 ≤ ‖fun i => Du i x‖ ^ hpow.α / hpow.C :=
    div_nonneg hp_α_nn (le_of_lt hC_pos)
  have hH_lower' : -H x (fun i => Du i x) μn
      ≤ hpow.C * (μn ^ hpow.β + 1) := by
    linarith
  -- Bound `μn^β ≤ (2·|m x| + 1)^β` by monotonicity.
  have h_env_nn : 0 ≤ 2 * |m x| + 1 := by
    have habs := abs_nonneg (m x); linarith
  have hμn_β_le : μn ^ hpow.β ≤ (2 * |m x| + 1) ^ hpow.β :=
    Real.rpow_le_rpow hμn_nn hμn_le_env (le_of_lt hβ_pos)
  -- Triangle.
  have habs1 : |-(u x) - H x (fun i => Du i x) μn + V x|
      ≤ |-(u x) - H x (fun i => Du i x) μn| + |V x| := abs_add_le _ _
  have habs2 : |-(u x) - H x (fun i => Du i x) μn|
      ≤ |u x| + |H x (fun i => Du i x) μn| := by
    have := abs_sub (-(u x)) (H x (fun i => Du i x) μn)
    rw [abs_neg] at this
    linarith
  -- Bound `|H|` via `H_upper'` and `H_lower'`.
  have hA_nn : 0 ≤ hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1) := by
    have h1 : 0 ≤ ‖fun i => Du i x‖ ^ hpow.α + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hB_nn : 0 ≤ hpow.C * (μn ^ hpow.β + 1) := by
    have h1 : 0 ≤ μn ^ hpow.β + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hH_abs : |H x (fun i => Du i x) μn|
      ≤ hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1)
          + hpow.C * (μn ^ hpow.β + 1) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have hH_abs' : |H x (fun i => Du i x) μn|
      ≤ hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1)
          + hpow.C * ((2 * |m x| + 1) ^ hpow.β + 1) := by
    have h1 : hpow.C * (μn ^ hpow.β + 1)
        ≤ hpow.C * ((2 * |m x| + 1) ^ hpow.β + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
      linarith
    linarith
  -- Combine.
  rw [Real.norm_eq_abs]
  have hslack : 0 ≤ ‖fun i => Du i x‖ ^ hpow.α + 1 := by linarith
  nlinarith [hH_abs', habs1, habs2, hslack]

/-- Helper: `|v ⬝ w| ≤ ‖v‖ * ∑ |w i|`. Inline copy of
`abs_euclideanDot_le_norm_mul_sum_abs` from `Hemicontinuity.lean`
(which is `private` to that file). -/
private lemma set_perturbation_abs_dot_le_norm_mul_sum_abs
    (v w : Fin d → ℝ) :
    |v ⬝ w| ≤ ‖v‖ * ∑ i, |w i| := by
  unfold euclideanDot
  have hsum : |∑ i, v i * w i| ≤ ∑ i, |v i * w i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      |v i * w i| ≤ ‖v‖ * |w i| := by
    intro i _
    rw [abs_mul]
    have h1 : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at this
      exact this
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hbnd : ∑ i, |v i * w i| ≤ ∑ i, ‖v‖ * |w i| :=
    Finset.sum_le_sum hcoord
  have hfact : (∑ i, ‖v‖ * |w i|) = ‖v‖ * ∑ i, |w i| := by
    rw [← Finset.mul_sum]
  linarith [hsum, hbnd, hfact.le, hfact.ge]

/-- **`hEf_bd`** — pointwise bound on the flux test factor.
`‖DpH(x, Dυ, μ_n) ⬝ (Dυ - Du)‖ ≤ Ef x`, with envelope
`Ef x := h.C · (‖Dυ‖^(α-1) + (|Sρ x|+1)^(β-β/α) + 1) · ∑ i, |Dυ i x - Du i x|`.

Uses `hpow.DpH_upper` (which gives `‖DpH(x,p,m)‖ ≤ C(‖p‖^(α-1) +
m^(β-β/α) + 1)` for the Pi-sup norm `‖·‖`) plus the elementary
inequality `|v⬝w| ≤ ‖v‖ · ∑|w_i|`. The `μ_n` factor is bounded by
`|Sρ x| + 1` using `μ_n ≤ |Sρ x| + 1` and monotonicity of `t ↦ t^q`
on `[0, ∞)` for `q ≥ 0`. We require `0 ≤ β - β/α` (true since `α ≥ 1`,
i.e. `β ≥ β/α`) for the `t ↦ t^(β-β/α)` rpow-monotonicity step. -/
theorem set_perturbation_hEf_bd
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)}
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖
          ≤ hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
                  + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                  + 1)
              * ∑ i, |Dυ i x - Du i x| := by
  intro n
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hC_pos : 0 < hpow.C := hpow.hC
  have hα_ge_one : 1 ≤ hpow.α := le_of_lt hpow.hα
  -- `β - β/α ≥ 0` since `α ≥ 1` implies `β/α ≤ β`.
  have hβ_div_α_le : hpow.β / hpow.α ≤ hpow.β := by
    rw [div_le_iff₀ hα_pos]
    nlinarith
  have hβ_minus_pos : 0 ≤ hpow.β - hpow.β / hpow.α := by linarith
  filter_upwards [hpow.DpH_upper, hρ_nn] with x hx_DpH hx_ρ_nn
  set μn : ℝ := S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμn_def
  have hone_div_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    set_perturbation_one_div_pos n
  have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    set_perturbation_one_div_le_one n
  have hSρ_nn : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun _ _ => hx_ρ_nn) x
  have hμn_pos : 0 < μn := by rw [hμn_def]; linarith
  have hμn_nn : 0 ≤ μn := le_of_lt hμn_pos
  have hSρ_abs : |S.indicator ρ x| = S.indicator ρ x := abs_of_nonneg hSρ_nn
  have hμn_le_env : μn ≤ |S.indicator ρ x| + 1 := by
    rw [hμn_def, hSρ_abs]; linarith
  -- DpH_upper gives `‖DpH‖ ≤ C·(‖p‖^(α-1) + μn^(β-β/α) + 1)`.
  have hDpH_bd := hx_DpH (fun i => Dυ i x) μn hμn_pos
  -- Cauchy-Schwarz-style: `|DpH ⬝ (Dυ-Du)| ≤ ‖DpH‖ · ∑ |(Dυ-Du)_i|`.
  have hCS := set_perturbation_abs_dot_le_norm_mul_sum_abs
    (DpH x (fun i => Dυ i x) μn) (fun i => Dυ i x - Du i x)
  -- Norm = abs for ℝ-valued.
  rw [Real.norm_eq_abs]
  -- Bound `μn^(β-β/α) ≤ (|Sρ|+1)^(β-β/α)`.
  have hμn_pow_le : μn ^ (hpow.β - hpow.β / hpow.α)
      ≤ (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α) :=
    Real.rpow_le_rpow hμn_nn hμn_le_env hβ_minus_pos
  -- Now combine: `‖DpH‖ ≤ C·(‖p‖^(α-1) + (|Sρ|+1)^(β-β/α) + 1)`.
  have hDpH_bd' :
      ‖DpH x (fun i => Dυ i x) μn‖
        ≤ hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
                + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                + 1) := by
    have h1 :
        hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
              + μn ^ (hpow.β - hpow.β / hpow.α) + 1)
          ≤ hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
              + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
      linarith
    linarith
  -- Multiply by `∑ |(Dυ-Du)_i| ≥ 0`.
  have hsum_nn : 0 ≤ ∑ i, |Dυ i x - Du i x| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hCS_bd :
      |DpH x (fun i => Dυ i x) μn ⬝ (fun i => Dυ i x - Du i x)|
        ≤ hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
                + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                + 1)
            * ∑ i, |Dυ i x - Du i x| := by
    -- `|DpH ⬝ Y| ≤ ‖DpH‖ · ∑ |Y_i| ≤ RHS`.
    have h2 :
        ‖DpH x (fun i => Dυ i x) μn‖ * ∑ i, |Dυ i x - Du i x|
          ≤ hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
                  + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                  + 1)
              * ∑ i, |Dυ i x - Du i x| :=
      mul_le_mul_of_nonneg_right hDpH_bd' hsum_nn
    -- Identify `(fun i => Dυ i x - Du i x) i = Dυ i x - Du i x`.
    have hCS' :
        |DpH x (fun i => Dυ i x) μn ⬝ (fun i => Dυ i x - Du i x)|
          ≤ ‖DpH x (fun i => Dυ i x) μn‖ * ∑ i, |Dυ i x - Du i x| := by
      simpa using hCS
    linarith
  exact hCS_bd

/-- **`set_perturbation_hEf_bd_ae`** — bare/AE sibling of `set_perturbation_hEf_bd`
(EXPERT RULING #4 retype, D2c-2e-1 child B).

Identical flux test-factor pointwise envelope bound, but keyed on plain exponents
`(β α C : ℝ)` with positivity facts `(hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)` and
taking the **AE** `DpH_upper`-shaped bound as a plain `∀ᵐ` argument `hDpH_upper`,
INSTEAD of consuming `hpow : HypothesisPowerGrowth`. The strict proof consumes
`hpow` ONLY through `hpow.DpH_upper`, the values `hpow.{C,α,β}` and positivity
`hpow.{hC,hα,hβ}`; none of `RegularityH`/`H_upper_pointwise`/`lower`/`lagr`/`upper`.

Body is the verbatim adaptation of `set_perturbation_hEf_bd` with
`hpow.DpH_upper ↦ hDpH_upper`, `hpow.C ↦ C`, `hpow.α ↦ α`, `hpow.β ↦ β`,
`hpow.hC ↦ hC`, `hpow.hα ↦ hα`, `hpow.hβ ↦ hβ`. -/
theorem set_perturbation_hEf_bd_ae
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {S : Set (Fin d → ℝ)}
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hDpH_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)) :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖
          ≤ C * (‖fun i => Dυ i x‖ ^ (α - 1)
                  + (|S.indicator ρ x| + 1) ^ (β - β / α)
                  + 1)
              * ∑ i, |Dυ i x - Du i x| := by
  intro n
  have hβ_pos : 0 < β := hβ
  have hα_pos : 0 < α := lt_trans Real.zero_lt_one hα
  have hC_pos : 0 < C := hC
  have hα_ge_one : 1 ≤ α := le_of_lt hα
  have hβ_div_α_le : β / α ≤ β := by
    rw [div_le_iff₀ hα_pos]
    nlinarith
  have hβ_minus_pos : 0 ≤ β - β / α := by linarith
  filter_upwards [hDpH_upper, hρ_nn] with x hx_DpH hx_ρ_nn
  set μn : ℝ := S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμn_def
  have hone_div_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    set_perturbation_one_div_pos n
  have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    set_perturbation_one_div_le_one n
  have hSρ_nn : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun _ _ => hx_ρ_nn) x
  have hμn_pos : 0 < μn := by rw [hμn_def]; linarith
  have hμn_nn : 0 ≤ μn := le_of_lt hμn_pos
  have hSρ_abs : |S.indicator ρ x| = S.indicator ρ x := abs_of_nonneg hSρ_nn
  have hμn_le_env : μn ≤ |S.indicator ρ x| + 1 := by
    rw [hμn_def, hSρ_abs]; linarith
  have hDpH_bd := hx_DpH (fun i => Dυ i x) μn hμn_pos
  have hCS := set_perturbation_abs_dot_le_norm_mul_sum_abs
    (DpH x (fun i => Dυ i x) μn) (fun i => Dυ i x - Du i x)
  rw [Real.norm_eq_abs]
  have hμn_pow_le : μn ^ (β - β / α)
      ≤ (|S.indicator ρ x| + 1) ^ (β - β / α) :=
    Real.rpow_le_rpow hμn_nn hμn_le_env hβ_minus_pos
  have hDpH_bd' :
      ‖DpH x (fun i => Dυ i x) μn‖
        ≤ C * (‖fun i => Dυ i x‖ ^ (α - 1)
                + (|S.indicator ρ x| + 1) ^ (β - β / α)
                + 1) := by
    have h1 :
        C * (‖fun i => Dυ i x‖ ^ (α - 1)
              + μn ^ (β - β / α) + 1)
          ≤ C * (‖fun i => Dυ i x‖ ^ (α - 1)
              + (|S.indicator ρ x| + 1) ^ (β - β / α) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
      linarith
    linarith
  have hsum_nn : 0 ≤ ∑ i, |Dυ i x - Du i x| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hCS_bd :
      |DpH x (fun i => Dυ i x) μn ⬝ (fun i => Dυ i x - Du i x)|
        ≤ C * (‖fun i => Dυ i x‖ ^ (α - 1)
                + (|S.indicator ρ x| + 1) ^ (β - β / α)
                + 1)
            * ∑ i, |Dυ i x - Du i x| := by
    have h2 :
        ‖DpH x (fun i => Dυ i x) μn‖ * ∑ i, |Dυ i x - Du i x|
          ≤ C * (‖fun i => Dυ i x‖ ^ (α - 1)
                  + (|S.indicator ρ x| + 1) ^ (β - β / α)
                  + 1)
              * ∑ i, |Dυ i x - Du i x| :=
      mul_le_mul_of_nonneg_right hDpH_bd' hsum_nn
    have hCS' :
        |DpH x (fun i => Dυ i x) μn ⬝ (fun i => Dυ i x - Du i x)|
          ≤ ‖DpH x (fun i => Dυ i x) μn‖ * ∑ i, |Dυ i x - Du i x| := by
      simpa using hCS
    linarith
  exact hCS_bd

/-- **`signed_perturbation_hGh_bd_ae`** — bare/AE sibling of
`signed_perturbation_hGh_bd` (D2c-2e-2b child C, signed).

Identical HJB g-factor pointwise envelope bound for the signed family,
but keyed on plain exponents `(β α C : ℝ)` with positivity facts
`(hβ : 0 < β) (hC : 0 < C)` and taking the two **AE** analytic bounds
(`H_upper_pointwise`-shaped + `lower`-shaped) as plain `∀ᵐ` arguments
`hH_upper_pt` / `hlower`, INSTEAD of consuming
`hpow : HypothesisPowerGrowth`. The strict proof consumes `hpow` ONLY
through `hpow.H_upper_pointwise`, `hpow.lower`, the values
`hpow.{C,α,β}` and positivity `hpow.{hC,hβ}`. Body is the verbatim
adaptation of `signed_perturbation_hGh_bd` with
`hpow.H_upper_pointwise ↦ hH_upper_pt`, `hpow.lower ↦ hlower`,
`hpow.C ↦ C`, `hpow.α ↦ α`, `hpow.β ↦ β`, `hpow.hC ↦ hC`,
`hpow.hβ ↦ hβ`. -/
theorem signed_perturbation_hGh_bd_ae
    {β α C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    {S : Set (Fin d → ℝ)}
    {m V u : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hH_upper_pt : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C)
    (hlower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)) :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖
          ≤ (C + 1) * (‖fun i => Du i x‖ ^ α + 1)
              + C * ((2 * |m x| + 1) ^ β + 1)
              + |u x| + |V x| := by
  intro n
  have hβ_pos : 0 < β := hβ
  have hC_pos : 0 < C := hC
  have hone_div_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
    set_perturbation_one_div_pos n
  have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    set_perturbation_one_div_le_one n
  have hσ_abs : |σ| ≤ 1 := by
    rcases hσ with h | h <;> simp [h]
  filter_upwards [hH_upper_pt, hlower, hm_nn]
    with x hx_upper hx_lower hx_m_nn
  have hInd_bd :
      0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
    by_cases hxS : x ∈ S
    · refine ⟨?_, ?_⟩
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_mem hxS]
    · refine ⟨?_, ?_⟩
      · simp [Set.indicator_of_notMem hxS]
      · simp [Set.indicator_of_notMem hxS]
  set μn : ℝ := m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) with hμn_def
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with h | h <;> linarith
  have hone_plus_sigma_ind_nn :
      0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    have hσ_ind_lb :
        -1 ≤ σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      have : -1 * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              ≤ σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
        mul_le_mul_of_nonneg_right hσ_lb hInd_bd.1
      have : -S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              ≤ σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        have heq : (-1 : ℝ) * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    = -S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          ring
        rw [heq] at this; exact this
      linarith [hInd_bd.2]
    linarith
  have hm_term_nn :
      0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    have hprod_nn : 0 ≤ m x * (1 + σ * S.indicator
                                (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      mul_nonneg hx_m_nn hone_plus_sigma_ind_nn
    have heq : m x * (1 + σ * S.indicator
                                (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                = m x + σ * m x * S.indicator
                                  (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      ring
    linarith [hprod_nn, heq.ge, heq.le]
  have hμn_pos : 0 < μn := by
    rw [hμn_def]
    linarith
  have hμn_nn : 0 ≤ μn := le_of_lt hμn_pos
  have hm_le_abs : m x ≤ |m x| := le_abs_self _
  have hσm_ind_abs_le :
      |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ |m x| := by
    have h1 : |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              = |σ| * |m x| * |S.indicator
                                (fun _ : Fin d → ℝ => (1 : ℝ)) x| := by
      rw [abs_mul, abs_mul]
    have hInd_abs :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg hInd_bd.1]; exact hInd_bd.2
    have habs_m_nn : 0 ≤ |m x| := abs_nonneg _
    have h2 : |σ| * |m x| ≤ 1 * |m x| :=
      mul_le_mul_of_nonneg_right hσ_abs habs_m_nn
    have h3 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ |σ| * |m x| * 1 := by
      apply mul_le_mul_of_nonneg_left hInd_abs
      exact mul_nonneg (abs_nonneg _) habs_m_nn
    have h4 : |σ| * |m x| * 1 ≤ 1 * |m x| * 1 := by
      have := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    have h5 : 1 * |m x| * 1 = |m x| := by ring
    linarith [h1.le, h1.ge, h3, h4, h5.le, h5.ge]
  have hσm_ind_le :
      σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ |m x| := by
    have := le_abs_self (σ * m x * S.indicator
                          (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    linarith [hσm_ind_abs_le]
  have hμn_le_env : μn ≤ 2 * |m x| + 1 := by
    rw [hμn_def]
    linarith [hm_le_abs, hσm_ind_le, hone_div_le_one]
  have hH_upper := hx_upper (fun i => Du i x) μn hμn_pos
  have hH_lower := hx_lower (fun i => Du i x) μn hμn_pos
  have hμn_β_nn : 0 ≤ μn ^ β := Real.rpow_nonneg hμn_nn _
  have hμn_β_div_C_nn : 0 ≤ (μn ^ β) / C :=
    div_nonneg hμn_β_nn (le_of_lt hC_pos)
  have hH_upper' : H x (fun i => Du i x) μn
      ≤ C * (‖fun i => Du i x‖ ^ α + 1) := by
    linarith
  have hp_α_nn : 0 ≤ ‖fun i => Du i x‖ ^ α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hp_α_div_C_nn : 0 ≤ ‖fun i => Du i x‖ ^ α / C :=
    div_nonneg hp_α_nn (le_of_lt hC_pos)
  have hH_lower' : -H x (fun i => Du i x) μn
      ≤ C * (μn ^ β + 1) := by
    linarith
  have h_env_nn : 0 ≤ 2 * |m x| + 1 := by
    have habs := abs_nonneg (m x); linarith
  have hμn_β_le : μn ^ β ≤ (2 * |m x| + 1) ^ β :=
    Real.rpow_le_rpow hμn_nn hμn_le_env (le_of_lt hβ_pos)
  have habs1 : |-(u x) - H x (fun i => Du i x) μn + V x|
      ≤ |-(u x) - H x (fun i => Du i x) μn| + |V x| := abs_add_le _ _
  have habs2 : |-(u x) - H x (fun i => Du i x) μn|
      ≤ |u x| + |H x (fun i => Du i x) μn| := by
    have := abs_sub (-(u x)) (H x (fun i => Du i x) μn)
    rw [abs_neg] at this
    linarith
  have hA_nn : 0 ≤ C * (‖fun i => Du i x‖ ^ α + 1) := by
    have h1 : 0 ≤ ‖fun i => Du i x‖ ^ α + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hB_nn : 0 ≤ C * (μn ^ β + 1) := by
    have h1 : 0 ≤ μn ^ β + 1 := by linarith
    exact mul_nonneg (le_of_lt hC_pos) h1
  have hH_abs : |H x (fun i => Du i x) μn|
      ≤ C * (‖fun i => Du i x‖ ^ α + 1)
          + C * (μn ^ β + 1) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have hH_abs' : |H x (fun i => Du i x) μn|
      ≤ C * (‖fun i => Du i x‖ ^ α + 1)
          + C * ((2 * |m x| + 1) ^ β + 1) := by
    have h1 : C * (μn ^ β + 1)
        ≤ C * ((2 * |m x| + 1) ^ β + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
      linarith
    linarith
  rw [Real.norm_eq_abs]
  have hslack : 0 ≤ ‖fun i => Du i x‖ ^ α + 1 := by linarith
  nlinarith [hH_abs', habs1, habs2, hslack]

/-- **`transport_perturbation_hGh_bd_ae`** — bare/AE sibling of
`transport_perturbation_hGh_bd` (D2c-2e-2b child C, transport).

Reduces to `set_perturbation_hGh_bd_ae` at `S := Set.univ`, `ρ := σ`,
using `Set.univ.indicator σ = σ` pointwise. -/
theorem transport_perturbation_hGh_bd_ae
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {σ V υ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hH_upper_pt : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C)
    (hlower : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)) :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖
          ≤ (C + 1) * (‖fun i => φ i x‖ ^ α + 1)
              + C * ((|σ x| + 1) ^ β + 1)
              + |υ x| + |V x| := by
  intro n
  have h_set := set_perturbation_hGh_bd_ae (H := H)
    hα hβ hC (S := Set.univ) (ρ := σ) (V := V) (υ := υ) hσ_nn (Dυ := φ)
    hH_upper_pt hlower n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-- **`transport_perturbation_hEf_bd_ae`** — bare/AE sibling of
`transport_perturbation_hEf_bd` (D2c-2e-2b child C, transport).

Reduces to `set_perturbation_hEf_bd_ae` at `S := Set.univ`, `ρ := σ`,
using `Set.univ.indicator σ = σ` pointwise. -/
theorem transport_perturbation_hEf_bd_ae
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {σ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    {φ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hDpH_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)) :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖
          ≤ C * (‖fun i => φ i x‖ ^ (α - 1)
                  + (|σ x| + 1) ^ (β - β / α)
                  + 1)
              * ∑ i, |φ i x - Du i x| := by
  intro n
  have h_set := set_perturbation_hEf_bd_ae (DpH := DpH)
    hα hβ hC (S := Set.univ) (ρ := σ) hσ_nn (Dυ := φ) (Du := Du)
    hDpH_upper n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-! ### Set-perturbation pointwise tendsto inputs (`hPointwise_H`,
`hPointwise_DpH_prod`)

Discharge the two pointwise-tendsto inputs of
`mfgOperatorEpsPair_tendsto_set_perturbation` from the paper-level
regularity assumptions:

* `RegularityH H DpH` / `HypothesisPowerGrowth`: `(p, m) ↦ H(x, p, m)`
  and `(p, m) ↦ DpH(x, p, m)` are continuous on `ℝ^d × ℝ^+` (open
  positive-mass set);
* For `H`: paper hypothesis `(a:Hat0)` (Source line 383) gives the
  right-continuity of `H` at `m = 0`, packaged as the input
  `hH_rc0` to `set_perturbation_pointwise_tendsto_H`.
* For `DpH`: **no analogous bare-DpH right-continuity hypothesis is
  needed.** The paper's `(a:mDpHat0)` is right-continuity of
  `J = m · DpH`, NOT of bare `DpH`, and `DpH` itself can blow up as
  `m → 0` (e.g. congestion models with `DpH ~ m^{-τ}`). In the actual
  flux integrand of `mfgOperatorPair`, `DpH` appears multiplied by
  `m`. Working with the **product** `μ_n · (DpH · v)` rather than
  the bare `DpH · v`, the boundary case `μ_∞ = 0` is closed by a
  squeeze argument using the power-growth bound from
  `hpow.DpH_upper`; no paper input beyond `hpow` is required.

Structural challenge resolved by this section: at points where
`S.indicator ρ x = 0`, the limit `μ_∞ x = 0` lies on the **boundary**
of the open positive-mass set `{m > 0}`, so the standard
`ContinuousOn.continuousAt` argument does not apply directly. We
case-split on whether `S.indicator ρ x` is zero or positive (using
`hρ_nn`):

* On `{S.indicator ρ > 0}`: eventually `μ_n x ≥ S.indicator ρ x / 2 > 0`,
  so `μ_n x` lies in the open set `{m > 0}` for large `n`. The
  ContinuousOn hypothesis and `Tendsto.comp` close the case.
* On `{S.indicator ρ = 0}`: `μ_n x = 1/(n+1) → 0⁺` from above. For
  the H-side this uses `hH_rc0` (paper `(a:Hat0)`); for the flux side
  the squeeze argument on the **product** form
  `μ_n · (DpH · v) → 0` is used (no `(a:DpHat0)` needed). -/

/-- **Pointwise tendsto for the HJB factor at the set perturbation —
continuity-only form** (D2b-1c-ii-c, route (b)).

Discharges the `hPointwise_H` input of
`mfgOperatorEpsPair_tendsto_set_perturbation` (above). For a.e. `x`,
the perturbation `μ_n x = S.indicator ρ x + 1/(n+1)` converges to
`μ_∞ x = S.indicator ρ x` from above (since `1/(n+1) > 0`), so
`H(x, Dυ x, μ_n x) → H(x, Dυ x, μ_∞ x)` follows from the
open-set continuity on `{m > 0}` together with right-continuity at `m = 0`.

This `_of_cont` form takes the genuine `RegularityH.continuous_H_pm` field
`hcont_H_pm` DIRECTLY (continuity of `(p, m) ↦ H(x, p, m)` on `{0 < pm.2}`),
instead of the whole `RegularityH H DpH` bundle. The whole bundle is NOT
constructible for `H := HdeltaK0` (no global `measurable_H` at `{m = 0}`), but
this single continuity field IS (on `{0 < m}`, `HdeltaK0 = HdeltaPos`). This is
the H-side entry point the `HdeltaK0`/T3 `_of_aeMeasH` chain needs.

The right-continuity of `H` at `m = 0` is taken as the input
`hH_rc0`. This is exactly the paper's hypothesis `(a:Hat0)`
(Source line 383): the paper's extended `H` is defined so that
`H(x, p, 0) = lim_{m → 0⁺} H(x, p, m)`, i.e., right-continuous at
`m = 0` by construction. -/
theorem set_perturbation_pointwise_tendsto_H_of_cont
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    {S : Set (Fin d → ℝ)}
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x)) := by
  -- Continuity certificate is consumed from `hcont_H_pm` (the genuine
  -- `RegularityH.continuous_H_pm` field), NOT the whole bundle.
  filter_upwards [hcont_H_pm, hρ_nn, hH_rc0]
    with x hx_cont hx_ρ_nn hx_rc0
  set p : Fin d → ℝ := fun i => Dυ i x with hp_def
  set μN : ℕ → ℝ := fun n => S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμN_def
  set μInf : ℝ := S.indicator ρ x with hμInf_def
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h_μN_tendsto : Filter.Tendsto μN Filter.atTop (𝓝 μInf) := by
    have := h_one_div_tendsto.const_add μInf
    simpa [hμN_def, hμInf_def, add_zero] using this
  have h_one_div_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_pos.mpr hn1
  have hSρ_nn : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun _ _ => hx_ρ_nn) x
  have h_H_tendsto :
      Filter.Tendsto (fun n : ℕ => H x p (μN n)) Filter.atTop
        (𝓝 (H x p μInf)) := by
    rcases eq_or_lt_of_le hSρ_nn with hSρ0 | hSρpos
    · have hμInf0 : μInf = 0 := by
        rw [hμInf_def]; linarith [hSρ0]
      have hμN_pos : ∀ n, (0 : ℝ) < μN n := by
        intro n
        show 0 < μInf + 1 / ((n : ℝ) + 1)
        rw [hμInf0, zero_add]
        exact h_one_div_pos n
      have h_rc := hx_rc0 p
      have h_μN_tendsto_zero : Filter.Tendsto μN Filter.atTop (𝓝 0) := by
        have := h_μN_tendsto
        rw [hμInf0] at this; exact this
      have h_eventually_pos :
          ∀ᶠ n in Filter.atTop, μN n ∈ Set.Ioi (0 : ℝ) :=
        Filter.Eventually.of_forall (fun n => hμN_pos n)
      have h_μN_tendsto_within :
          Filter.Tendsto μN Filter.atTop (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨h_μN_tendsto_zero,
          h_eventually_pos⟩
      have h_comp : Filter.Tendsto (fun n => H x p (μN n)) Filter.atTop
          (𝓝 (H x p 0)) := h_rc.comp h_μN_tendsto_within
      have h_eq : H x p μInf = H x p 0 := by rw [hμInf0]
      rw [h_eq]
      exact h_comp
    · have hμInf_pos : 0 < μInf := hSρpos
      have h_eventually_pos : ∀ᶠ n in Filter.atTop, 0 < μN n := by
        have h_half_pos : 0 < μInf / 2 := half_pos hμInf_pos
        have h_lt : μInf / 2 < μInf := half_lt_self hμInf_pos
        have h_ev := (h_μN_tendsto.eventually
          (eventually_gt_nhds h_lt))
        filter_upwards [h_ev] with n hn
        linarith
      have h_pt_in : (p, μInf) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
        change 0 < μInf
        exact hμInf_pos
      have h_cwa : ContinuousWithinAt
          (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2)
          {pm | 0 < pm.2} (p, μInf) := hx_cont _ h_pt_in
      have h_open : IsOpen {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
        have : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
        exact this.preimage continuous_snd
      have h_ca : ContinuousAt
          (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) (p, μInf) :=
        (continuousWithinAt_iff_continuousAt
          (h_open.mem_nhds h_pt_in)).mp h_cwa
      have h_pair_tendsto :
          Filter.Tendsto (fun n : ℕ => (p, μN n)) Filter.atTop
            (𝓝 (p, μInf)) :=
        Filter.Tendsto.prodMk_nhds tendsto_const_nhds h_μN_tendsto
      exact h_ca.tendsto.comp h_pair_tendsto
  have h_neg_υ_const :
      Filter.Tendsto (fun _ : ℕ => -(υ x)) Filter.atTop (𝓝 (-(υ x))) :=
    tendsto_const_nhds
  have h_V_const :
      Filter.Tendsto (fun _ : ℕ => V x) Filter.atTop (𝓝 (V x)) :=
    tendsto_const_nhds
  have h_neg_H : Filter.Tendsto (fun n : ℕ => -(υ x) - H x p (μN n))
      Filter.atTop (𝓝 (-(υ x) - H x p μInf)) :=
    h_neg_υ_const.sub h_H_tendsto
  exact h_neg_H.add h_V_const

/-- **Pointwise tendsto for the HJB factor at the set perturbation** (strict
bundle form). Delegates to `set_perturbation_pointwise_tendsto_H_of_cont` via the
`RegularityH.continuous_H_pm` projection, keeping the strict path intact for the
T1/T2 producers. -/
theorem set_perturbation_pointwise_tendsto_H
    (hRegH : RegularityH H DpH)
    {S : Set (Fin d → ℝ)}
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x)) :=
  set_perturbation_pointwise_tendsto_H_of_cont (V := V)
    hRegH.continuous_H_pm (S := S) (ρ := ρ) (υ := υ) hρ_nn hH_rc0 Dυ

/-- **Phase G bridge: derive `set_perturbation_pointwise_tendsto_H`'s
`hH_rc0` rider from the paper-level `(a:Hat0)` plus two paper-faithful
finiteness/agreement riders.**

The `set_perturbation_pointwise_tendsto_H` lemma above takes a
real-valued right-continuity hypothesis `hH_rc0` against the raw
`H x p 0`. The paper's `(a:Hat0)` (`HypothesisHat0`) provides
convergence in `WithTop ℝ` against the extended `Hext H x p 0`. The
shape mismatch is closed by `Hamiltonian.H_rc0_of_hHat0`, which adds
the two paper-faithful riders:

* `Hext_finite_at_zero H` — the limit is finite (not `+∞`);
* `H_zero_eq_Hext H` — the raw `H x p 0` records the limit value (the
  paper's writing convention `H(x, p, 0) = lim_{m → 0⁺} H(x, p, m)`).

This corollary is the single entry point used by the set-perturbation
G-aggregator: it threads the bridge into
`set_perturbation_pointwise_tendsto_H` so the aggregator can
discharge `hPointwise_H` from `(hHat0, hFin, hAgree)` without any
non-paper assumption. -/
theorem set_perturbation_pointwise_tendsto_H_of_hHat0
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    {S : Set (Fin d → ℝ)}
    {ρ V υ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x)) := by
  have hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)) :=
    StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hHat0 hFin hAgree
  exact set_perturbation_pointwise_tendsto_H (V := V)
    hRegH (S := S) (ρ := ρ) (υ := υ) hρ_nn hH_rc0 Dυ

/-! **Pointwise tendsto for the (mass-weighted) flux factor at the set
perturbation.**

Discharges the `hPointwise_DpH_prod` (product-form) input of
`mfgOperatorEpsPair_tendsto_set_perturbation` (above). For a.e. `x`,
the product `μ_n x · (DpH(x, Dυ x, μ_n x) ⬝ (Dυ x - Du x))` converges
to `μ_∞ x · (DpH(x, Dυ x, μ_∞ x) ⬝ (Dυ x - Du x))`.

This is the **paper-correct shape**: the actual flux integrand of
`mfgOperatorPair` is `μ · DpH · v`, not bare `DpH · v`. The product
form admits a clean treatment of the `μ_∞ x = 0` boundary case, where
the paper's `(a:mDpHat0)` continuity of `J = m·DpH` (rather than of
`DpH` itself) gives the limit:

* On `{S.indicator ρ x > 0}`: open-set continuity of `(p, m) ↦ DpH`
  on `{m > 0}` (from `(a:regularityH)`/`hRegH`) gives the limit by
  `Tendsto.comp` with `(μ_n x → μ_∞ x)`, multiplied by the trivial
  `μ_n x → μ_∞ x` tendsto.
* On `{S.indicator ρ x = 0}`: `μ_n x = 1/(n+1) → 0⁺`. The bare factor
  `DpH(x, p, μ_n x) ⬝ v` may not converge (e.g., congestion models
  with `DpH ~ m^{-τ}`), but the **product** `μ_n x · (DpH · v) → 0`
  by the squeeze argument: the power-growth bound
  `‖DpH x p m‖ ≤ C(‖p‖^{α-1} + m^{β-β/α} + 1)` (from
  `hpow.DpH_upper`, valid for `m > 0`) gives
  `|μ_n · (DpH · v)| ≤ μ_n · C(‖p‖^{α-1} + μ_n^{β-β/α} + 1) · ‖v‖`,
  whose right side → 0 as `μ_n → 0` (since `β - β/α > 0`).

No paper-level `(a:DpHat0)` hypothesis (right-continuity of bare
`DpH·v` at `m=0`) is required — only `hpow` and the open-set
continuity from `hRegH`. The genuine analytic content is carried by the
`_of_fields` variant below; this strict bundle form delegates. -/

/-- **`set_perturbation_pointwise_tendsto_DpH_of_fields`**
(D2b-1c-ii-c2, step 1, DpH-side decoupling) — the `_of_fields` variant of
`set_perturbation_pointwise_tendsto_DpH`, taking the genuine individual
regularity fields
(`continuous_DpH_pm`, `DpH_upper`, exponents `α β`, with `hα : 1 < α`,
`hβ : 0 < β`, and constant `C`) DIRECTLY instead of the whole
`HypothesisPowerGrowth` bundle.

This is the H-measurability-free DpH-pointwise entry point the
`HdeltaK0`/T3 chain needs: the `HypothesisPowerGrowth` bundle is NOT
constructible for `H := HdeltaK0` (no global `measurable_H` at `{m = 0}`),
but each of `continuous_DpH_pm` and `DpH_upper` on `{0 < m}` IS available.
The strict `set_perturbation_pointwise_tendsto_DpH` delegates via the
`hpow` projections. -/
theorem set_perturbation_pointwise_tendsto_DpH_of_fields
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hcont_DpH_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hDpH_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    {S : Set (Fin d → ℝ)}
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (Dυ Du : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          (S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)))
        Filter.atTop
        (𝓝 (S.indicator ρ x *
            (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x)))) := by
  -- Continuity / growth fields consumed DIRECTLY (no `hpow` bundle).
  filter_upwards [hcont_DpH_pm, hρ_nn, hDpH_upper]
    with x hx_cont hx_ρ_nn hx_DpH_bd
  set p : Fin d → ℝ := fun i => Dυ i x with hp_def
  set v : Fin d → ℝ := fun i => Dυ i x - Du i x with hv_def
  set μN : ℕ → ℝ := fun n => S.indicator ρ x + 1 / ((n : ℝ) + 1) with hμN_def
  set μInf : ℝ := S.indicator ρ x with hμInf_def
  -- Pointwise tendsto: `1/(n+1) → 0`.
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- `μ_n → μ_∞`.
  have h_μN_tendsto : Filter.Tendsto μN Filter.atTop (𝓝 μInf) := by
    have := h_one_div_tendsto.const_add μInf
    simpa [hμN_def, hμInf_def, add_zero] using this
  have h_one_div_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_pos.mpr hn1
  have hSρ_nn : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun _ _ => hx_ρ_nn) x
  -- `μN n > 0` for all `n`.
  have hμN_pos : ∀ n, (0 : ℝ) < μN n := by
    intro n
    have : 0 < S.indicator ρ x + 1 / ((n : ℝ) + 1) :=
      add_pos_of_nonneg_of_pos hSρ_nn (h_one_div_pos n)
    exact this
  -- Convergence of the product along `μ_n`.
  rcases eq_or_lt_of_le hSρ_nn with hSρ0 | hSρpos
  · -- Case `μInf = 0`: squeeze argument using `hDpH_upper`.
    have hμInf0 : μInf = 0 := by rw [hμInf_def]; linarith [hSρ0]
    -- Target reduces to `0`.
    have h_target_zero :
        μInf * (DpH x p μInf ⬝ v) = 0 := by
      rw [hμInf0]; ring
    rw [h_target_zero]
    -- Show `μN n · (DpH x p (μN n) ⬝ v) → 0` via squeeze.
    -- Step 1: power-growth bound on `‖DpH x p (μN n)‖`.
    have hβ_pos : 0 < β := hβ
    have hα_pos : 0 < α - 1 := by linarith [hα]
    have hβα_pos : 0 < β - β / α := by
      have h1 : β / α < β := by
        rw [div_lt_iff₀ (lt_trans Real.zero_lt_one hα)]
        nlinarith [hβ, hα]
      linarith
    -- The dominator function `n ↦ μN n · C · (‖p‖^(α-1) + μN n^(β-β/α) + 1) · ‖v‖`
    -- tends to 0 since `μN n → 0` and the bracketed factor tends to a
    -- finite constant.
    have h_μN_tendsto_zero : Filter.Tendsto μN Filter.atTop (𝓝 0) := by
      have := h_μN_tendsto; rw [hμInf0] at this; exact this
    -- Pointwise: `μN n^(β-β/α) → 0`.
    have h_pow_tendsto :
        Filter.Tendsto (fun n => μN n ^ (β - β / α))
          Filter.atTop (𝓝 0) := by
      -- `(fun t => t ^ c)` is continuous on ℝ for `c ≥ 0` (Real.rpow).
      have h_cont : ContinuousAt
          (fun t : ℝ => t ^ (β - β / α)) 0 :=
        (Real.continuous_rpow_const hβα_pos.le).continuousAt
      have h_zero : (0 : ℝ) ^ (β - β / α) = 0 :=
        Real.zero_rpow hβα_pos.ne'
      have := h_cont.tendsto.comp h_μN_tendsto_zero
      rw [h_zero] at this
      exact this
    -- Constant tendsto for `‖p‖^(α-1) + 1`.
    have h_const :
        Filter.Tendsto
          (fun _ : ℕ => ‖p‖ ^ (α - 1) + 1)
          Filter.atTop (𝓝 (‖p‖ ^ (α - 1) + 1)) :=
      tendsto_const_nhds
    -- Sum tendsto: `‖p‖^(α-1) + μN n^(β-β/α) + 1`
    -- → `‖p‖^(α-1) + 0 + 1 = ‖p‖^(α-1) + 1`.
    have h_bracket_tendsto :
        Filter.Tendsto
          (fun n : ℕ => ‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
          Filter.atTop
          (𝓝 (‖p‖ ^ (α - 1) + 0 + 1)) := by
      exact ((tendsto_const_nhds.add h_pow_tendsto).add tendsto_const_nhds)
    -- Set up the sum-of-abs `Vsum := ∑ i, |v i|` used by the
    -- coordinate Cauchy-Schwarz bound below. Tracking `Vsum` instead
    -- of `‖v‖` keeps the proof free of `EuclideanSpace` overhead.
    set Vsum : ℝ := ∑ i, |v i| with hVsum_def
    have hVsum_nn : 0 ≤ Vsum := by
      apply Finset.sum_nonneg
      intro i _
      exact abs_nonneg _
    -- Multiply by `μN n` to get the dominator → 0.
    have h_dom_tendsto :
        Filter.Tendsto
          (fun n : ℕ => μN n * (C *
            (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
            * Vsum))
          Filter.atTop (𝓝 0) := by
      have h1 :
          Filter.Tendsto
            (fun n : ℕ => C *
              (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
              * Vsum)
            Filter.atTop
            (𝓝 (C * (‖p‖ ^ (α - 1) + 0 + 1) * Vsum)) := by
        exact (tendsto_const_nhds.mul h_bracket_tendsto).mul tendsto_const_nhds
      have := h_μN_tendsto_zero.mul h1
      simpa using this
    -- Squeeze. Cauchy-Schwarz coordinate form: `|w ⬝ v| ≤ ‖w‖ * Vsum`.
    have h_bd : ∀ n,
        |μN n * (DpH x p (μN n) ⬝ v)|
          ≤ μN n * (C *
              (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
              * Vsum) := by
      intro n
      have hμN_pos_n : 0 < μN n := hμN_pos n
      have hμN_nn : 0 ≤ μN n := hμN_pos_n.le
      have h_DpH_bd_n :
          ‖DpH x p (μN n)‖
            ≤ C *
              (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1) :=
        hx_DpH_bd p (μN n) hμN_pos_n
      -- Coordinate Cauchy-Schwarz: `|w ⬝ v| ≤ ‖w‖ * ∑ i, |v i|`.
      have h_CS : |DpH x p (μN n) ⬝ v| ≤ ‖DpH x p (μN n)‖ * Vsum := by
        unfold euclideanDot
        have hsum : |∑ i, DpH x p (μN n) i * v i|
            ≤ ∑ i, |DpH x p (μN n) i * v i| :=
          Finset.abs_sum_le_sum_abs _ _
        have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin d)),
            |DpH x p (μN n) i * v i| ≤ ‖DpH x p (μN n)‖ * |v i| := by
          intro i _
          rw [abs_mul]
          have h1 : |DpH x p (μN n) i| ≤ ‖DpH x p (μN n)‖ := by
            have := norm_le_pi_norm (DpH x p (μN n)) i
            rw [Real.norm_eq_abs] at this
            exact this
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        have hbnd : ∑ i, |DpH x p (μN n) i * v i|
            ≤ ∑ i, ‖DpH x p (μN n)‖ * |v i| :=
          Finset.sum_le_sum hcoord
        have hfact : (∑ i, ‖DpH x p (μN n)‖ * |v i|)
            = ‖DpH x p (μN n)‖ * Vsum := by
          rw [← Finset.mul_sum]
        linarith [hsum, hbnd, hfact.le, hfact.ge]
      -- `|μN · (DpH·v)| = μN · |DpH·v|`.
      have h_abs_eq : |μN n * (DpH x p (μN n) ⬝ v)|
          = μN n * |DpH x p (μN n) ⬝ v| := by
        rw [abs_mul, abs_of_nonneg hμN_nn]
      rw [h_abs_eq]
      have h_step1 : μN n * |DpH x p (μN n) ⬝ v|
          ≤ μN n * (‖DpH x p (μN n)‖ * Vsum) :=
        mul_le_mul_of_nonneg_left h_CS hμN_nn
      have h_step2 :
          μN n * (‖DpH x p (μN n)‖ * Vsum)
            ≤ μN n * (C *
                (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
                * Vsum) := by
        have h_DpH_norm_v :
            ‖DpH x p (μN n)‖ * Vsum
              ≤ C *
                (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
                * Vsum :=
          mul_le_mul_of_nonneg_right h_DpH_bd_n hVsum_nn
        exact mul_le_mul_of_nonneg_left h_DpH_norm_v hμN_nn
      linarith
    -- Apply squeeze theorem (`Filter.Tendsto.squeeze` via abs bound).
    have h_zero_const :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds
    have h_neg_dom : Filter.Tendsto
        (fun n : ℕ => -(μN n * (C *
            (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
            * Vsum)))
        Filter.atTop (𝓝 (-0)) := h_dom_tendsto.neg
    -- From `|fN| ≤ DN` and `DN → 0`, get `fN → 0` by `tendsto_of_tendsto_of_tendsto_of_le_of_le`.
    rw [show (-(0 : ℝ)) = 0 by ring] at h_neg_dom
    have h_lower : ∀ n,
        -(μN n * (C *
            (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
            * Vsum))
          ≤ μN n * (DpH x p (μN n) ⬝ v) := by
      intro n
      have := h_bd n
      have h_abs := abs_le.mp this
      exact h_abs.1
    have h_upper : ∀ n,
        μN n * (DpH x p (μN n) ⬝ v)
          ≤ μN n * (C *
            (‖p‖ ^ (α - 1) + μN n ^ (β - β / α) + 1)
            * Vsum) := by
      intro n
      have := h_bd n
      have h_abs := abs_le.mp this
      exact h_abs.2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_neg_dom h_dom_tendsto
      h_lower h_upper
  · -- Case `μInf > 0`: use ContinuousOn on the open set, then multiply.
    have hμInf_pos : 0 < μInf := hSρpos
    have h_pt_in : (p, μInf) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
      change 0 < μInf
      exact hμInf_pos
    have h_cwa : ContinuousWithinAt
        (fun pm : (Fin d → ℝ) × ℝ => DpH x pm.1 pm.2)
        {pm | 0 < pm.2} (p, μInf) := hx_cont _ h_pt_in
    have h_open : IsOpen {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
      have : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
      exact this.preimage continuous_snd
    have h_ca : ContinuousAt
        (fun pm : (Fin d → ℝ) × ℝ => DpH x pm.1 pm.2) (p, μInf) :=
      (continuousWithinAt_iff_continuousAt
        (h_open.mem_nhds h_pt_in)).mp h_cwa
    have h_pair_tendsto :
        Filter.Tendsto (fun n : ℕ => (p, μN n)) Filter.atTop
          (𝓝 (p, μInf)) :=
      Filter.Tendsto.prodMk_nhds tendsto_const_nhds h_μN_tendsto
    -- `n ↦ DpH x p (μN n) → DpH x p μInf`.
    have h_DpH_tendsto :
        Filter.Tendsto (fun n : ℕ => DpH x p (μN n)) Filter.atTop
          (𝓝 (DpH x p μInf)) := h_ca.tendsto.comp h_pair_tendsto
    -- Compose with continuity of `(· ⬝ v)` at `DpH x p μInf`.
    have h_dot_cont :
        Continuous (fun w : Fin d → ℝ => w ⬝ v) := by
      unfold euclideanDot
      exact continuous_finset_sum _ (fun i _ =>
        (continuous_apply i).mul continuous_const)
    have h_dot_tendsto :
        Filter.Tendsto (fun n : ℕ => DpH x p (μN n) ⬝ v) Filter.atTop
          (𝓝 (DpH x p μInf ⬝ v)) :=
      (h_dot_cont.tendsto _).comp h_DpH_tendsto
    -- Multiply by `μN n → μInf`.
    exact h_μN_tendsto.mul h_dot_tendsto

/-- **Pointwise tendsto for the (mass-weighted) flux factor at the set
perturbation** (strict bundle form). Delegates to
`set_perturbation_pointwise_tendsto_DpH_of_fields` via the
`HypothesisPowerGrowth` projections, keeping the strict path intact for
the T1/T2 producers. -/
theorem set_perturbation_pointwise_tendsto_DpH
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)}
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (Dυ Du : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          (S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)))
        Filter.atTop
        (𝓝 (S.indicator ρ x *
            (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x)))) :=
  set_perturbation_pointwise_tendsto_DpH_of_fields
    (DpH := DpH) (C := hpow.C) (α := hpow.α) (β := hpow.β)
    hpow.hα hpow.hβ hpow.continuous_DpH_pm hpow.DpH_upper
    (S := S) (ρ := ρ) hρ_nn Dυ Du

/-! ### Signed-perturbation measurability + pointwise-tendsto helpers

The signed perturbation
`μ_n x := m x + σ · m x · 𝟙_S x + 1/(n+1) = m x · (1 + σ · 𝟙_S x) + 1/(n+1)`
arises in `hVIeps_signed_of_KAepsi_VI`. Its limit is
`μ_∞ x = m x + σ · m x · 𝟙_S x = m x · (1 + σ · 𝟙_S x)`.

For `σ ∈ {±1}` and `m ≥ 0` a.e., `μ_∞ ≥ 0` a.e.: `1 + σ · 𝟙_S ∈ [0, 2]`
(since `𝟙_S ∈ {0, 1}`). For `σ = -1`, `μ_∞ x = 0` on `S`, so the
boundary case `μ_∞ = 0` arises here.

The four lemmas below mirror the set-perturbation building blocks:

* `signed_perturbation_μN_meas` — measurability of `μ_n`.
* `signed_perturbation_gN1_meas` — HJB g-factor measurability.
* `signed_perturbation_ηN1_meas` — measurability of the direction
  density `σ · m · 𝟙_S + 1/(n+1)`.
* `signed_perturbation_pointwise_tendsto_H_of_hHat0` — bridge:
  pointwise tendsto of the HJB integrand. Reduces to
  `set_perturbation_pointwise_tendsto_H_of_hHat0` applied at
  `S' := Set.univ` and `ρ' x := m x + σ · m x · 𝟙_S x`, since
  `Set.univ.indicator ρ' = ρ' = μ_∞`. -/

/-- AE-strong measurability of the signed perturbation
`x ↦ m x + σ · m x · S.indicator (fun _ => 1) x + 1/(n+1)`. -/
theorem signed_perturbation_μN_meas
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {m : (Fin d → ℝ) → ℝ} (hm : Measurable m)
    (σ : ℝ) (n : ℕ) :
    AEStronglyMeasurable
      (fun x : (Fin d → ℝ) =>
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          + 1 / ((n : ℝ) + 1))
      (volume.restrict (UnitCube d)) := by
  have hOne : Measurable (fun _ : (Fin d → ℝ) => (1 : ℝ)) := measurable_const
  have hInd : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hOne.indicator hS
  have hσm : Measurable (fun x : (Fin d → ℝ) => σ * m x) :=
    measurable_const.mul hm
  have hσmInd : Measurable
      (fun x : (Fin d → ℝ) =>
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hσm.mul hInd
  have hsum : Measurable
      (fun x : (Fin d → ℝ) =>
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hm.add hσmInd
  have hμ : Measurable
      (fun x : (Fin d → ℝ) =>
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          + 1 / ((n : ℝ) + 1)) :=
    hsum.add_const _
  exact hμ.aestronglyMeasurable

/-- AE-strong measurability of the signed direction density
`x ↦ σ · m x · S.indicator (fun _ => 1) x + 1/(n+1)`. -/
theorem signed_perturbation_ηN1_meas
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {m : (Fin d → ℝ) → ℝ} (hm : Measurable m)
    (σ : ℝ) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)) := by
  intro n
  have hOne : Measurable (fun _ : (Fin d → ℝ) => (1 : ℝ)) := measurable_const
  have hInd : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hOne.indicator hS
  have hσm : Measurable (fun x : (Fin d → ℝ) => σ * m x) :=
    measurable_const.mul hm
  have hσmInd : Measurable
      (fun x : (Fin d → ℝ) =>
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hσm.mul hInd
  have hη : Measurable
      (fun x : (Fin d → ℝ) =>
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          + 1 / ((n : ℝ) + 1)) :=
    hσmInd.add_const _
  exact hη.aestronglyMeasurable

/-- **`signed_perturbation_gN1_meas_of_aeMeasH`** (D2b-1c-ii-b, route (b)) —
AE-strong measurability of the signed HJB g-factor, consuming the
H-composition as a per-`n` AE composite `hHcomp_ae` INSTEAD of the strict
global `hpow.measurable_H`. The AE entry point for the `HdeltaK0`/T3 path. -/
theorem signed_perturbation_gN1_meas_of_aeMeasH
    {S : Set (Fin d → ℝ)}
    {m V υ : (Fin d → ℝ) → ℝ}
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (σ : ℝ)
    (hHcomp_ae : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d))) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)) := by
  intro n
  exact (((hυ.aemeasurable.neg).sub (hHcomp_ae n)).add
    hV.aemeasurable).aestronglyMeasurable

theorem signed_perturbation_gN1_meas
    (hpow : HypothesisPowerGrowth H DpH)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {m V υ : (Fin d → ℝ) → ℝ}
    (hm : Measurable m) (hV : Measurable V) (hυ : Measurable υ)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hDυ : ∀ i, Measurable (Dυ i))
    (σ : ℝ) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)) := by
  -- Derive the per-`n` AE composite from the strict global field via
  -- `comp_aemeasurable`, then delegate to the `_of_aeMeasH` variant.
  refine signed_perturbation_gN1_meas_of_aeMeasH (H := H)
    hV.aestronglyMeasurable hυ.aestronglyMeasurable σ (fun n => ?_)
  -- `μ_n` is measurable.
  have hOne : Measurable (fun _ : (Fin d → ℝ) => (1 : ℝ)) := measurable_const
  have hInd : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hOne.indicator hS
  have hσm : Measurable (fun x : (Fin d → ℝ) => σ * m x) :=
    measurable_const.mul hm
  have hσmInd : Measurable
      (fun x : (Fin d → ℝ) =>
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hσm.mul hInd
  have hsum : Measurable
      (fun x : (Fin d → ℝ) =>
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    hm.add hσmInd
  have hμ : Measurable
      (fun x : (Fin d → ℝ) =>
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          + 1 / ((n : ℝ) + 1)) :=
    hsum.add_const _
  have hDυ_pi : Measurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
    measurable_pi_iff.mpr hDυ
  have hxpm : Measurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => Dυ i x),
            m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))) :=
    measurable_id.prodMk (hDυ_pi.prodMk hμ)
  exact hpow.measurable_H.comp_aemeasurable hxpm.aemeasurable

/-- **Phase G bridge — pointwise-tendsto for the signed-perturbation
HJB integrand at `μ_∞ = m + σ · m · 𝟙_S`.**

For `σ ∈ {±1}` and `m ≥ 0` a.e., the limit `μ_∞ x = m x · (1 + σ · 𝟙_S x)`
is a.e. nonneg (`1 + σ · 𝟙_S ∈ [0, 2]`). The boundary case `μ_∞ x = 0`
arises for `σ = -1` on `S` (where `1 + σ · 𝟙_S = 0`); the per-`n`
positivity `μ_n x > 0` still holds because the `1/(n+1)` shift is
strictly positive even when `m · (1 + σ · 𝟙_S) = 0`.

Proof: reduce to the set version `set_perturbation_pointwise_tendsto_H_of_hHat0`
applied at `S' := Set.univ` and the limit density
`ρ' x := m x + σ · m x · 𝟙_S x`. Then
`Set.univ.indicator ρ' x = ρ' x = μ_∞ x`, and the set lemma's
conclusion specialises directly. Non-negativity of `ρ'` follows
from `hm_nn` and `hσ_lb : -1 ≤ σ`. -/
theorem signed_perturbation_pointwise_tendsto_H_of_hHat0
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    {S : Set (Fin d → ℝ)}
    {m V υ : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x)
            (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x)) := by
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ ≤ 1`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  -- Define `ρ' x := m x + σ * m x * 𝟙_S x = m x * (1 + σ * 𝟙_S x)`.
  set ρ' : (Fin d → ℝ) → ℝ :=
    fun x => m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ'_def
  -- A.e. non-negativity of `ρ'`.
  have hρ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ' x := by
    filter_upwards [hm_nn] with x hxnn
    -- `𝟙_S x ∈ {0, 1}`.
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    -- `1 + σ * 𝟙_S x ≥ 0`: since `𝟙_S ≤ 1` and `σ ≥ -1`,
    -- `σ * 𝟙_S ≥ -1` (whether `𝟙_S = 0` or `𝟙_S = 1`), so `1 + σ * 𝟙_S ≥ 0`.
    have hfactor_nn : 0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · -- `𝟙_S x = 1`, so `σ * 𝟙_S = σ ≥ -1`, so `1 + σ ≥ 0`.
        rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · -- `𝟙_S x = 0`, so `σ * 𝟙_S = 0`, so `1 + 0 = 1 ≥ 0`.
        rw [Set.indicator_of_notMem hxS]
        simp
    -- `ρ' x = m x * (1 + σ * 𝟙_S x) ≥ 0`.
    show 0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = m x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]
    exact mul_nonneg hxnn hfactor_nn
  -- Apply the set version at `S' := Set.univ`, `ρ := ρ'`.
  have h_set := set_perturbation_pointwise_tendsto_H_of_hHat0
    (V := V) (υ := υ) hRegH hHat0 hFin hAgree
    (S := Set.univ) (ρ := ρ') hρ'_nn Dυ
  -- `Set.univ.indicator ρ' x = ρ' x` for every `x`.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ' x = ρ' x := by
    intro x
    simp [Set.indicator_of_mem (Set.mem_univ x)]
  -- Rewrite `h_set`'s conclusion using `h_ind_univ`.
  have h_rewrite : ∀ x : (Fin d → ℝ),
      (Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  ((Set.univ : Set (Fin d → ℝ)).indicator ρ' x
                    + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator ρ' x) + V x)))
      ↔
      (Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
              (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x))) := by
    intro x
    rw [h_ind_univ x]
  filter_upwards [h_set] with x hx
  exact (h_rewrite x).mp hx

/-- **`rc0`-input variant** of `signed_perturbation_pointwise_tendsto_H_of_hHat0`.

Identical conclusion, but takes the right-continuity-at-`0` certificate
`hH_rc0` for `H(x, p, ·)` directly (paper `(a:Hat0)`, Source line 383)
instead of the `HypothesisHat0`/`Hext_finite_at_zero`/`H_zero_eq_Hext`
bundle. This is the `Hext_finite_at_zero`-free leaf used by the T3
substituted-pair supply (the regularised Hamiltonian provides its own
`hH_rc0`). Reduces to the `rc0` set leaf
`set_perturbation_pointwise_tendsto_H` at `S' := Set.univ`,
`ρ' x := m x + σ · m x · 𝟙_S x`, exactly as the `_of_hHat0` variant
reduces to `set_perturbation_pointwise_tendsto_H_of_hHat0`. -/
theorem signed_perturbation_pointwise_tendsto_H_of_rc0
    (hRegH : RegularityH H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    {S : Set (Fin d → ℝ)}
    {m V υ : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x)
            (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x)) := by
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ ≤ 1`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  -- Define `ρ' x := m x + σ * m x * 𝟙_S x = m x * (1 + σ * 𝟙_S x)`.
  set ρ' : (Fin d → ℝ) → ℝ :=
    fun x => m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ'_def
  -- A.e. non-negativity of `ρ'`.
  have hρ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ' x := by
    filter_upwards [hm_nn] with x hxnn
    have hfactor_nn : 0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        simp
    show 0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = m x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]
    exact mul_nonneg hxnn hfactor_nn
  -- Apply the `rc0` set version at `S' := Set.univ`, `ρ := ρ'`.
  have h_set := set_perturbation_pointwise_tendsto_H
    (V := V) (υ := υ) hRegH (S := Set.univ) (ρ := ρ') hρ'_nn hH_rc0 Dυ
  -- `Set.univ.indicator ρ' x = ρ' x` for every `x`.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ' x = ρ' x := by
    intro x
    simp [Set.indicator_of_mem (Set.mem_univ x)]
  have h_rewrite : ∀ x : (Fin d → ℝ),
      (Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  ((Set.univ : Set (Fin d → ℝ)).indicator ρ' x
                    + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator ρ' x) + V x)))
      ↔
      (Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
              (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x))) := by
    intro x
    rw [h_ind_univ x]
  filter_upwards [h_set] with x hx
  exact (h_rewrite x).mp hx

/-- **`of_cont`-input variant** of `signed_perturbation_pointwise_tendsto_H_of_rc0`
(D2b-1c-ii-c3, the c1 continuity-only sibling for the signed family).

Identical conclusion, but consumes the genuine individual continuity field
`hcont_H_pm` (`ContinuousOn {m > 0}`, available on `HdeltaK0`) plus the
right-continuity-at-`0` certificate `hH_rc0`, INSTEAD of the `RegularityH`
bundle. This is the `measurable_H`-free continuity leaf used by the signed
`_of_rc0_of_aeMeasH` producer. Reduces to the set `_of_cont` leaf
`set_perturbation_pointwise_tendsto_H_of_cont` at `S' := Set.univ`,
`ρ' x := m x + σ · m x · 𝟙_S x`, exactly as the `_of_rc0` variant reduces to
`set_perturbation_pointwise_tendsto_H`. -/
theorem signed_perturbation_pointwise_tendsto_H_of_cont
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    {S : Set (Fin d → ℝ)}
    {m V υ : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x)
            (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x)) := by
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ ≤ 1`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  -- Define `ρ' x := m x + σ * m x * 𝟙_S x = m x * (1 + σ * 𝟙_S x)`.
  set ρ' : (Fin d → ℝ) → ℝ :=
    fun x => m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ'_def
  -- A.e. non-negativity of `ρ'`.
  have hρ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ' x := by
    filter_upwards [hm_nn] with x hxnn
    have hfactor_nn : 0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        simp
    show 0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = m x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]
    exact mul_nonneg hxnn hfactor_nn
  -- Apply the set `_of_cont` version at `S' := Set.univ`, `ρ := ρ'`.
  have h_set := set_perturbation_pointwise_tendsto_H_of_cont
    (V := V) (υ := υ) hcont_H_pm (S := Set.univ) (ρ := ρ') hρ'_nn hH_rc0 Dυ
  -- `Set.univ.indicator ρ' x = ρ' x` for every `x`.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ' x = ρ' x := by
    intro x
    simp [Set.indicator_of_mem (Set.mem_univ x)]
  have h_rewrite : ∀ x : (Fin d → ℝ),
      (Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  ((Set.univ : Set (Fin d → ℝ)).indicator ρ' x
                    + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator ρ' x) + V x)))
      ↔
      (Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x)
              (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x))) := by
    intro x
    rw [h_ind_univ x]
  filter_upwards [h_set] with x hx
  exact (h_rewrite x).mp hx

/-! ### Transport-perturbation measurability + pointwise-tendsto helpers

The transport perturbation `μ_n x := σ x + 1/(n+1)` (with limit
`μ_∞ x := σ x`) arises in `hVIeps_transport_of_KAepsi_VI`. The test
triple is `(σ, υ, φ - Du)`.

These lemmas mirror the set-perturbation building blocks
(`set_perturbation_*_meas`, `set_perturbation_pointwise_tendsto_*`)
without the `S.indicator ρ` wrapper. The pointwise-tendsto lemmas
reduce to the set form at `S' := Set.univ`, `ρ' := σ`, since
`Set.univ.indicator σ x = σ x`.

Per task `infra-P5-phase-G-tendsto-transport-meas-pointwise`. -/

/-- AE-strong measurability of the transport perturbation
`x ↦ σ x + 1/(n+1)`. -/
theorem transport_perturbation_μN_meas
    {σ : (Fin d → ℝ) → ℝ} (hσ : Measurable σ)
    (n : ℕ) :
    AEStronglyMeasurable
      (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1))
      (volume.restrict (UnitCube d)) :=
  (hσ.add_const _).aestronglyMeasurable

/-- **`gN2_meas`** (transport) — AE-strong measurability of the flux
μ-factor `x ↦ σ x + 1/(n+1)`. -/
theorem transport_perturbation_gN2_meas
    {σ : (Fin d → ℝ) → ℝ} (hσ : Measurable σ) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)) :=
  fun n => transport_perturbation_μN_meas hσ n

/-- **`ηN1_meas`** (transport) — AE-strong measurability of the HJB
η-factor `x ↦ σ x + 1/(n+1) - m x`. -/
theorem transport_perturbation_ηN1_meas
    {σ m : (Fin d → ℝ) → ℝ} (hσ : Measurable σ) (hm : Measurable m) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1) - m x)
        (volume.restrict (UnitCube d)) := by
  intro n
  have h : Measurable
      (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1) - m x) :=
    (hσ.add_const _).sub hm
  exact h.aestronglyMeasurable

/-- **`gN3_meas`** (transport) — AE-strong measurability of the mass
μ-factor `x ↦ σ x + 1/(n+1) - 1`. -/
theorem transport_perturbation_gN3_meas
    {σ : (Fin d → ℝ) → ℝ} (hσ : Measurable σ) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1) - 1)
        (volume.restrict (UnitCube d)) := by
  intro n
  have h : Measurable
      (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1) - 1) :=
    (hσ.add_const _).sub_const _
  exact h.aestronglyMeasurable

/-- **`ηN3_meas`** (transport) — AE-strong measurability of the mass
test-factor `x ↦ υ x - u x` (constant in `n`). -/
theorem transport_perturbation_ηN3_meas
    {υ u : (Fin d → ℝ) → ℝ} (hυ : Measurable υ) (hu : Measurable u) :
    ∀ _n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => υ x - u x)
        (volume.restrict (UnitCube d)) := by
  intro _
  exact (hυ.sub hu).aestronglyMeasurable

/-- **`transport_perturbation_gN1_meas_of_aeMeasH`** (D2b-1c-ii-b, route (b)) —
AE-strong measurability of the transport HJB g-factor, consuming the
H-composition as a per-`n` AE composite `hHcomp_ae` INSTEAD of the strict
global `hpow.measurable_H`. The AE entry point for the `HdeltaK0`/T3 path. -/
theorem transport_perturbation_gN1_meas_of_aeMeasH
    {σ V υ : (Fin d → ℝ) → ℝ}
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hHcomp_ae : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d))) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)) := by
  intro n
  exact (((hυ.aemeasurable.neg).sub (hHcomp_ae n)).add
    hV.aemeasurable).aestronglyMeasurable

theorem transport_perturbation_gN1_meas
    (hpow : HypothesisPowerGrowth H DpH)
    {σ V υ : (Fin d → ℝ) → ℝ}
    (hσ : Measurable σ) (hV : Measurable V) (hυ : Measurable υ)
    {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hφ : ∀ i, Measurable (φ i)) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)) := by
  -- Derive the per-`n` AE composite from the strict global field via
  -- `comp_aemeasurable`, then delegate to the `_of_aeMeasH` variant.
  refine transport_perturbation_gN1_meas_of_aeMeasH (H := H)
    hV.aestronglyMeasurable hυ.aestronglyMeasurable (fun n => ?_)
  have hμ : Measurable
      (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1)) :=
    hσ.add_const _
  have hφ_pi : Measurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => φ i x)) :=
    measurable_pi_iff.mpr hφ
  have hxpm : Measurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => φ i x), σ x + 1 / ((n : ℝ) + 1))) :=
    measurable_id.prodMk (hφ_pi.prodMk hμ)
  exact hpow.measurable_H.comp_aemeasurable hxpm.aemeasurable

/-- **`ηN2_meas`** (transport) — AE-strong measurability of the flux
η-factor `x ↦ DpH x (fun i ↦ φ i x) (σ x + 1/(n+1)) ⬝
     (fun i ↦ φ i x - Du i x)`. The DpH-composition uses joint
measurability `hpow.measurable_DpH`. -/
theorem transport_perturbation_ηN2_meas
    (hpow : HypothesisPowerGrowth H DpH)
    {σ : (Fin d → ℝ) → ℝ} (hσ : Measurable σ)
    {φ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hφ : ∀ i, Measurable (φ i)) (hDu : ∀ i, Measurable (Du i)) :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x))
        (volume.restrict (UnitCube d)) := by
  intro n
  -- `μ_n` is measurable.
  have hμ : Measurable
      (fun x : (Fin d → ℝ) => σ x + 1 / ((n : ℝ) + 1)) :=
    hσ.add_const _
  -- `fun x => fun i => φ i x` is measurable into `Fin d → ℝ`.
  have hφ_pi : Measurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => φ i x)) :=
    measurable_pi_iff.mpr hφ
  -- The composite `x ↦ (x, (fun i ↦ φ i x), μ_n x)` is measurable.
  have hxpm : Measurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => φ i x), σ x + 1 / ((n : ℝ) + 1))) :=
    measurable_id.prodMk (hφ_pi.prodMk hμ)
  -- Compose with `hpow.measurable_DpH`.
  have hDpHcomp : Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))) :=
    hpow.measurable_DpH.comp hxpm
  -- Per-coordinate measurability of the DpH-composition.
  have hDpHcomp_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)) i) :=
    fun i => (measurable_pi_apply i).comp hDpHcomp
  -- Per-coordinate measurability of `φ i x - Du i x`.
  have hφdiff_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) => φ i x - Du i x) :=
    fun i => (hφ i).sub (hDu i)
  -- Each summand is measurable.
  have hsum_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)) i
          * (φ i x - Du i x)) :=
    fun i => (hDpHcomp_i i).mul (hφdiff_i i)
  -- The dot product is the finite sum.
  have hdot : Measurable
      (fun x : (Fin d → ℝ) =>
        ∑ i : Fin d,
          DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)) i
            * (φ i x - Du i x)) :=
    Finset.measurable_sum _ (fun i _ => hsum_i i)
  have hdot_eq :
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
          ⬝ (fun i => φ i x - Du i x))
        = (fun x : (Fin d → ℝ) =>
            ∑ i : Fin d,
              DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)) i
                * (φ i x - Du i x)) := by
    funext x; rfl
  rw [hdot_eq]
  exact hdot.aestronglyMeasurable

/-- **Phase G bridge — pointwise-tendsto for the transport-perturbation
HJB integrand at `μ_∞ = σ`.**

For `σ ≥ 0` a.e., the limit `μ_∞ x = σ x` may equal `0` on `{σ = 0}`.
The boundary case is closed by the paper's `(a:Hat0)` (right-continuity
of `H` at `m = 0`), threaded via `H_rc0_of_hHat0` and `(hFin, hAgree)`.

Proof: reduce to the set version
`set_perturbation_pointwise_tendsto_H_of_hHat0` applied at
`S' := Set.univ` and `ρ' := σ`. Then `Set.univ.indicator σ x = σ x`,
and the conclusion specialises directly. -/
theorem transport_perturbation_pointwise_tendsto_H_of_hHat0
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    {σ V υ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (φ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => φ i x) (σ x) + V x)) := by
  -- Apply the set version at `S' := Set.univ`, `ρ := σ`.
  have h_set := set_perturbation_pointwise_tendsto_H_of_hHat0
    (V := V) (υ := υ) hRegH hHat0 hFin hAgree
    (S := Set.univ) (ρ := σ) hσ_nn φ
  -- `Set.univ.indicator σ x = σ x` for every `x`.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x
    simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  -- Rewrite hypothesis using `h_ind_univ x`.
  have hx' := hx
  rw [h_ind_univ x] at hx'
  exact hx'

/-- **`rc0`-input variant** of `transport_perturbation_pointwise_tendsto_H_of_hHat0`.

Identical conclusion, but takes the right-continuity-at-`0` certificate
`hH_rc0` for `H(x, p, ·)` directly (paper `(a:Hat0)`) instead of the
`HypothesisHat0`/`Hext_finite_at_zero`/`H_zero_eq_Hext` bundle. This is
the `Hext_finite_at_zero`-free transport leaf for the T3 substituted-pair
supply. Reduces to the `rc0` set leaf
`set_perturbation_pointwise_tendsto_H` at `S' := Set.univ`, `ρ' := σ`. -/
theorem transport_perturbation_pointwise_tendsto_H_of_rc0
    (hRegH : RegularityH H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    {σ V υ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (φ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => φ i x) (σ x) + V x)) := by
  -- Apply the `rc0` set version at `S' := Set.univ`, `ρ := σ`.
  have h_set := set_perturbation_pointwise_tendsto_H
    (V := V) (υ := υ) hRegH (S := Set.univ) (ρ := σ) hσ_nn hH_rc0 φ
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x
    simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  have hx' := hx
  rw [h_ind_univ x] at hx'
  exact hx'

/-- **Phase G bridge — pointwise-tendsto for the (mass-weighted) flux
integrand at `μ_∞ = σ`.**

For `σ ≥ 0` a.e., the product
`μ_n x · (DpH(x, φ x, μ_n x) ⬝ (φ x - Du x))` converges to
`σ x · (DpH(x, φ x, σ x) ⬝ (φ x - Du x))` by `set_perturbation_pointwise_tendsto_DpH`
at `S' := Set.univ`, `ρ' := σ`. -/
theorem transport_perturbation_pointwise_tendsto_DpH
    (hpow : HypothesisPowerGrowth H DpH)
    {σ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (φ Du : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          (σ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)))
        Filter.atTop
        (𝓝 (σ x *
            (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x)))) := by
  have h_set := set_perturbation_pointwise_tendsto_DpH (DpH := DpH) hpow
    (S := Set.univ) (ρ := σ) hσ_nn φ Du
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x
    simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  have hx' := hx
  rw [h_ind_univ x] at hx'
  exact hx'

/-! ### Transport-perturbation pointwise bound lemmas

The six pointwise bound lemmas `transport_perturbation_h{Gh,Eh,Gf,Ef,Gm,Em}_bd`
mirror the set-perturbation analogues with the indicator wrapper
removed (`S.indicator ρ ↦ σ` directly). Each is derived from the set
version at `S := Set.univ`, `ρ := σ`, then specialised by
`Set.indicator_univ`.

These discharge the six `h*_bd` slots of
`TransportTendstoResidueOf` once paired with the corresponding
envelopes built in `BanachBridge.lean`. -/

/-- **`transport_perturbation_hEh_bd`** — pointwise bound on the
HJB η-factor (transport): `‖σ x + 1/(n+1) - m x‖ ≤ |σ x| + 1 + |m x|`. -/
theorem transport_perturbation_hEh_bd
    {σ m : (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖
          ≤ |σ x| + 1 + |m x| := by
  intro n
  have h_set := set_perturbation_hEh_bd (S := Set.univ) (ρ := σ) (m := m) n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-- **`transport_perturbation_hGf_bd`** — pointwise bound on the
flux μ-factor (transport): `‖σ x + 1/(n+1)‖ ≤ |σ x| + 1`. -/
theorem transport_perturbation_hGf_bd
    {σ : (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖
          ≤ |σ x| + 1 := by
  intro n
  have h_set := set_perturbation_hGf_bd (S := Set.univ) (ρ := σ) n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-- **`transport_perturbation_hGm_bd`** — pointwise bound on the
mass μ-factor (transport): `‖σ x + 1/(n+1) - 1‖ ≤ |σ x| + 2`. -/
theorem transport_perturbation_hGm_bd
    {σ : (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖
          ≤ |σ x| + 2 := by
  intro n
  have h_set := set_perturbation_hGm_bd (S := Set.univ) (ρ := σ) n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-- **`transport_perturbation_hEm_bd`** — pointwise bound on the
mass test factor (constant in `n`): `‖υ x - u x‖ ≤ |υ x - u x|`.
Identical to the set version (no σ dependency). -/
theorem transport_perturbation_hEm_bd
    {υ u : (Fin d → ℝ) → ℝ} :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖υ x - u x‖ ≤ |υ x - u x| :=
  set_perturbation_hEm_bd (υ := υ) (u := u)

/-- **`transport_perturbation_hGh_bd`** — pointwise bound on the
HJB g-factor (transport):
`‖-υ x - H x (φ, σ x + 1/(n+1)) + V x‖ ≤ (h.C+1)·(‖φ‖^α + 1)
   + h.C·((|σ x| + 1)^β + 1) + |υ x| + |V x|`. -/
theorem transport_perturbation_hGh_bd
    (hpow : HypothesisPowerGrowth H DpH)
    {σ V υ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    {φ : Fin d → (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖
          ≤ (hpow.C + 1) * (‖fun i => φ i x‖ ^ hpow.α + 1)
              + hpow.C * ((|σ x| + 1) ^ hpow.β + 1)
              + |υ x| + |V x| := by
  intro n
  have h_set := set_perturbation_hGh_bd (H := H) (DpH := DpH)
    hpow (S := Set.univ) (ρ := σ) (V := V) (υ := υ) hσ_nn (Dυ := φ) n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-- **`transport_perturbation_hEf_bd`** — pointwise bound on the
flux test factor (transport):
`‖DpH(x, φ x, σ x + 1/(n+1)) ⬝ (φ x - Du x)‖
  ≤ h.C · (‖φ‖^(α-1) + (|σ x| + 1)^(β-β/α) + 1) · ∑ i, |φ i x - Du i x|`. -/
theorem transport_perturbation_hEf_bd
    (hpow : HypothesisPowerGrowth H DpH)
    {σ : (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    {φ Du : Fin d → (Fin d → ℝ) → ℝ} :
    ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖
          ≤ hpow.C * (‖fun i => φ i x‖ ^ (hpow.α - 1)
                  + (|σ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                  + 1)
              * ∑ i, |φ i x - Du i x| := by
  intro n
  have h_set := set_perturbation_hEf_bd (H := H) (DpH := DpH)
    hpow (S := Set.univ) (ρ := σ) hσ_nn (Dυ := φ) (Du := Du) n
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  filter_upwards [h_set] with x hx
  rw [h_ind_univ x] at hx
  exact hx

/-! ### Phase G — closed-form aggregator
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`.

This is the routing aggregator that consumes only paper hypotheses,
test-triple structural data, and the **six abstract dominator
certificates** (`(Gh, Eh, Gf, Ef, Gm, Em)` together with their
`MemLpPer` integrabilities at the Hölder-paired exponents and the
six a.e. pointwise bounds) — and produces the
`mfgOperatorEpsPair_tendsto_set_perturbation` conclusion. The
aggregator's win is that it discharges:

* the six AE-strong-measurability witnesses
  (`set_perturbation_{gN1,gN2,gN3,ηN1,ηN2,ηN3}_meas`),
* per-`n` and limit integrability of the three product summands
  (via `MemLp.of_le_mul` on each factor + `MemLpPer.integrable_mul`,
  and a full-product squeeze for the flux limit case where bare
  `(DpH·v)` may blow up at `μ_∞ = 0`),
* the two pointwise tendsto inputs
  (`set_perturbation_pointwise_tendsto_H_of_hHat0`,
  `set_perturbation_pointwise_tendsto_DpH`).

The dominators themselves are consumed as authorised inputs; their
shapes are paper-prescribed and have been landed in
`Hamiltonian/Estimates.lean` and in this module. -/

/-- **`rc0`-input variant** of
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`.

Identical to the named producer below, but takes the **right-continuity
at `m = 0`** certificate `hH_rc0` for `H(x, p, ·)` *directly* as an
authorised input, instead of deriving it from the
`HypothesisHat0`/`Hext_finite_at_zero`/`H_zero_eq_Hext` bundle.

This is the **`Hext_finite_at_zero`-free** entry point used by the
T3 (weak-growth / inf-convolution) substituted-pair Browder–Minty
supply: the regularised Hamiltonian `Hdelta hweak ε` provides its
`hH_rc0` from a paper-faithful right-continuity clause, so the T3 chain
never pulls `Hext_finite_at_zero` (T3 must stay Hext-free). The named
producer below is recovered as a thin wrapper deriving `hH_rc0` from
the Hext bundle via `Hamiltonian.H_rc0_of_hHat0`. -/
theorem mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    -- Test-triple data.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    -- Measurabilities of the test-triple structural data.
    (hS : MeasurableSet S) (hρ : Measurable ρ)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `ρ`.
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    -- `MemLpPer` of `S.indicator ρ` at `βBarReal` (paper-canonical
    -- when `βBarReal = β + 1`; the headline only requires the abstract
    -- exponent, not the paper exponent, since the slot is underscored
    -- in the consumer body).
    (hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    -- The six dominator pairs with `MemLpPer` certificates and the six
    -- a.e. pointwise bounds (authorised inputs).
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    -- iter 0617 flux-pair retype: `(γ̄', γ̄) → (β̄, β̄')`.
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) := by
  -- Standing positivity facts on the paper exponents.
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  have hβp_pos : 0 < (hpow.β + 1) / hpow.β :=
    div_pos hbb_pos hβ_pos
  have hγb_pos : 0 < hpow.α * (hpow.β + 1) / hpow.β :=
    div_pos (mul_pos hα_pos hbb_pos) hβ_pos
  have hγb_gt_one : 1 < hpow.α * (hpow.β + 1) / hpow.β := by
    rw [lt_div_iff₀ hβ_pos]; nlinarith [hpow.hα]
  have hγbm1_pos : 0 < hpow.α * (hpow.β + 1) / hpow.β - 1 := by linarith
  have hγb'_pos : 0 < hpow.α * (hpow.β + 1) / hpow.β /
      (hpow.α * (hpow.β + 1) / hpow.β - 1) := div_pos hγb_pos hγbm1_pos
  -- Six measurability witnesses.
  have hgN1_meas := set_perturbation_gN1_meas hpow hS hρ hV hυ hDυ
    (S := S) (ρ := ρ) (V := V) (υ := υ) (Dυ := Dυ)
  have hηN1_meas := set_perturbation_ηN1_meas hS hρ hm
    (S := S) (ρ := ρ) (m := m)
  have hgN2_meas := set_perturbation_gN2_meas hS hρ
    (S := S) (ρ := ρ)
  have hηN2_meas := set_perturbation_ηN2_meas hpow hS hρ hDυ hDu
    (S := S) (ρ := ρ) (Dυ := Dυ) (Du := Du)
  have hgN3_meas := set_perturbation_gN3_meas hS hρ
    (S := S) (ρ := ρ)
  have hηN3_meas := set_perturbation_ηN3_meas hυ hu
    (υ := υ) (u := u)
  -- Pointwise tendsto inputs.
  have hPointwise_H :=
    set_perturbation_pointwise_tendsto_H
      (V := V) hRegH (S := S) (ρ := ρ) (υ := υ) hρ_nn hH_rc0 Dυ
  have hPointwise_DpH_prod :=
    set_perturbation_pointwise_tendsto_DpH (DpH := DpH) hpow
      (S := S) (ρ := ρ) hρ_nn Dυ Du
  -- Real Hölder pairs.
  have hβp_ne : (hpow.β + 1 : ℝ) ≠ 0 := hbb_pos.ne'
  have hβ_ne : (hpow.β : ℝ) ≠ 0 := hβ_pos.ne'
  have hHJB_pq : Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1) := by
    refine ⟨?_, hβp_pos, hbb_pos⟩
    field_simp
  -- iter 0617 flux-pair retype: was `(γ̄', γ̄)`, now `(β̄, β̄')`.
  have hflux_pq :
      Real.HolderConjugate (hpow.β + 1) ((hpow.β + 1) / hpow.β) := by
    refine ⟨?_, hbb_pos, hβp_pos⟩
    field_simp
    ring
  have hmass_pq : Real.HolderConjugate (hpow.β + 1) ((hpow.β + 1) / hpow.β) := by
    refine ⟨?_, hbb_pos, hβp_pos⟩
    field_simp
    ring
  -- Restricted measure (used everywhere below).
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm_def
  haveI : IsFiniteMeasure μm := by
    rw [hμm_def]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Per-`n` HJB summand integrability.
  have h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
          * (S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)) μm := by
    intro n
    have hgN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖
            ≤ (1 : ℝ) * ‖Gh x‖ := by
        filter_upwards [hGh_bd n] with x hx
        have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGh_memLp.toMemLp (hgN1_meas n) hbd)
    have hηN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖
            ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd n] with x hx
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp (hηN1_meas n) hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq hgN1_memLp hηN1_memLp
  -- Per-`n` flux summand integrability.
  -- iter 0617: `Gf, Ef` now at `(β̄, β̄')`.
  have h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x))) μm := by
    intro n
    have hgN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ (1 : ℝ) * ‖Gf x‖ := by
        filter_upwards [hGf_bd n] with x hx
        have hGf_nn : 0 ≤ Gf x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGf_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGf_memLp.toMemLp (hgN2_meas n) hbd)
    have hηN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => DpH x (fun i => Dυ i x)
                  (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x)‖ ≤ (1 : ℝ) * ‖Ef x‖ := by
        filter_upwards [hEf_bd n] with x hx
        have hEf_nn : 0 ≤ Ef x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEf_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEf_memLp.toMemLp (hηN2_meas n) hbd)
    exact Periodic.MemLpPer.integrable_mul hflux_pq hgN2_memLp hηN2_memLp
  -- Per-`n` mass summand integrability.
  have h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x)) μm := by
    intro n
    have hgN3_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖
            ≤ (1 : ℝ) * ‖Gm x‖ := by
        filter_upwards [hGm_bd n] with x hx
        have hGm_nn : 0 ≤ Gm x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGm_memLp.toMemLp (hgN3_meas n) hbd)
    have hηN3_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => υ x - u x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖υ x - u x‖ ≤ (1 : ℝ) * ‖Em x‖ := by
        filter_upwards [hEm_bd] with x hx
        have hEm_nn : 0 ≤ Em x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEm_memLp.toMemLp (hηN3_meas 0) hbd)
    exact Periodic.MemLpPer.integrable_mul hmass_pq hgN3_memLp hηN3_memLp
  -- HJB limit-integrability via squeeze on individual factors.
  have hgN1_lim_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x) μm := by
    have hSρ : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
      hρ.indicator hS
    have hDυ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
      measurable_pi_iff.mpr hDυ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => Dυ i x), S.indicator ρ x)) :=
      measurable_id.prodMk (hDυ_pi.prodMk hSρ)
    -- Limit-density (`{m = 0}`-reaching) H composite consumed only as an AE
    -- composite (`comp_aemeasurable`), so strict global `measurable_H` is used
    -- only in AE form here; the goal is `AEStronglyMeasurable`.
    have hHcomp : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => Dυ i x) (S.indicator ρ x))
        μm :=
      hpow.measurable_H.comp_aemeasurable hxpm.aemeasurable
    exact (((hυ.aemeasurable.neg).sub hHcomp).add
      hV.aemeasurable).aestronglyMeasurable
  have hηN1_lim_meas :
      AEStronglyMeasurable (fun x => S.indicator ρ x - m x) μm :=
    ((hρ.indicator hS).sub hm).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(υ x) - H x (fun i => Dυ i x)
            (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖)
      Filter.atTop
      (𝓝 ‖-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have hEh_bd_lim :
      ∀ᵐ x ∂μm, ‖S.indicator ρ x - m x‖ ≤ Eh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x :=
      MeasureTheory.ae_all_iff.mpr hEh_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) Filter.atTop
          (𝓝 (S.indicator ρ x - m x)) := by
      have := (h_one_div_tendsto.const_add (S.indicator ρ x)).sub_const (m x)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖)
      Filter.atTop (𝓝 ‖S.indicator ρ x - m x‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x)
          * (S.indicator ρ x - m x)) μm := by
    have hgN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => -(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x‖
            ≤ (1 : ℝ) * ‖Gh x‖ := by
        filter_upwards [hGh_bd_lim, hGh_bd 0] with x hx h0
        have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGh_memLp.toMemLp hgN1_lim_meas hbd)
    have hηN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => S.indicator ρ x - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x - m x‖ ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd_lim, hEh_bd 0] with x hx h0
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp hηN1_lim_meas hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq
      hgN1_lim_memLp hηN1_lim_memLp
  -- Flux limit-integrability: full-product squeeze on `Gf · Ef ∈ L¹`.
  have h_int2_lim :
      Integrable (fun x =>
        S.indicator ρ x
          * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))) μm := by
    have hSρ_meas : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
      hρ.indicator hS
    have hDυ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
      measurable_pi_iff.mpr hDυ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => Dυ i x), S.indicator ρ x)) :=
      measurable_id.prodMk (hDυ_pi.prodMk hSρ_meas)
    have hDpHcomp : Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x)) :=
      hpow.measurable_DpH.comp hxpm
    have hDpHcomp_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x) i) :=
      fun i => (measurable_pi_apply i).comp hDpHcomp
    have hDdiff_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) => Dυ i x - Du i x) :=
      fun i => (hDυ i).sub (hDu i)
    have hsum_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x) i
            * (Dυ i x - Du i x)) :=
      fun i => (hDpHcomp_i i).mul (hDdiff_i i)
    have hdot : Measurable
        (fun x : (Fin d → ℝ) =>
          ∑ i : Fin d,
            DpH x (fun i => Dυ i x) (S.indicator ρ x) i
              * (Dυ i x - Du i x)) :=
      Finset.measurable_sum _ (fun i _ => hsum_i i)
    have hdot_eq :
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x)
            ⬝ (fun i => Dυ i x - Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                DpH x (fun i => Dυ i x) (S.indicator ρ x) i
                  * (Dυ i x - Du i x)) := by
      funext x; rfl
    have hflux_lim_meas :
        AEStronglyMeasurable
          (fun x => DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x)) μm := by
      rw [hdot_eq]; exact hdot.aestronglyMeasurable
    have hprod_lim_meas :
        AEStronglyMeasurable
          (fun x => S.indicator ρ x
              * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
                  ⬝ (fun i => Dυ i x - Du i x))) μm :=
      hSρ_meas.aestronglyMeasurable.mul hflux_lim_meas
    have hbound_int : Integrable (fun x => Gf x * Ef x) μm :=
      Periodic.MemLpPer.integrable_mul hflux_pq hGf_memLp hEf_memLp
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hprod_bd_n : ∀ n : ℕ, ∀ᵐ x ∂μm,
        ‖(S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x))‖ ≤ Gf x * Ef x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    have hprod_bd_lim : ∀ᵐ x ∂μm,
        ‖S.indicator ρ x * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))‖ ≤ Gf x * Ef x := by
      have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
          ‖(S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x))‖ ≤ Gf x * Ef x :=
        MeasureTheory.ae_all_iff.mpr hprod_bd_n
      filter_upwards [hPointwise_DpH_prod, h_all_n] with x hx_pt h_seq
      have h_norm_lim : Filter.Tendsto
        (fun n : ℕ => ‖(S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x))‖)
        Filter.atTop
        (𝓝 ‖S.indicator ρ x * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))‖) :=
        (continuous_norm.tendsto _).comp hx_pt
      exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
        (Filter.Eventually.of_forall h_seq)
    have hbd' : ∀ᵐ x ∂μm,
        ‖S.indicator ρ x * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))‖ ≤ ‖Gf x * Ef x‖ := by
      filter_upwards [hprod_bd_lim, hGf_nn, hEf_nn] with x hx h1 h2
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg h1 h2)]
      simp only [Real.norm_eq_abs] at hx
      exact hx
    exact hbound_int.mono hprod_lim_meas hbd'
  -- Mass limit-integrability.
  have hgN3_lim_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => S.indicator ρ x - 1) μm :=
    ((hρ.indicator hS).sub_const _).aestronglyMeasurable
  have hηN3_lim_meas :
      AEStronglyMeasurable (fun x : (Fin d → ℝ) => υ x - u x) μm :=
    (hυ.sub hu).aestronglyMeasurable
  have hGm_bd_lim :
      ∀ᵐ x ∂μm, ‖S.indicator ρ x - 1‖ ≤ Gm x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x :=
      MeasureTheory.ae_all_iff.mpr hGm_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) Filter.atTop
          (𝓝 (S.indicator ρ x - 1)) := by
      have := (h_one_div_tendsto.const_add (S.indicator ρ x)).sub_const (1 : ℝ)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖)
      Filter.atTop (𝓝 ‖S.indicator ρ x - 1‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int3_lim :
      Integrable (fun x => (S.indicator ρ x - 1) * (υ x - u x)) μm := by
    have hgN3_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => S.indicator ρ x - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x - 1‖ ≤ (1 : ℝ) * ‖Gm x‖ := by
        filter_upwards [hGm_bd_lim, hGm_bd 0] with x hx h0
        have hGm_nn : 0 ≤ Gm x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGm_memLp.toMemLp hgN3_lim_meas hbd)
    have hηN3_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => υ x - u x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖υ x - u x‖ ≤ (1 : ℝ) * ‖Em x‖ := by
        filter_upwards [hEm_bd] with x hx
        have hEm_nn : 0 ≤ Em x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEm_memLp.toMemLp hηN3_lim_meas hbd)
    exact Periodic.MemLpPer.integrable_mul hmass_pq
      hgN3_lim_memLp hηN3_lim_memLp
  -- Apply the headline.
  exact mfgOperatorEpsPair_tendsto_set_perturbation
    (V := V) (H := H) (DpH := DpH)
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    (β := hpow.β) hpow.hβ hExp Dυ υ u Du m S ρ hSρ_memLp hρ_nn
    h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    Gf Ef hGf_memLp hEf_memLp hGf_bd hEf_bd
    Gm Em hGm_memLp hEm_memLp hGm_bd hEm_bd
    hgN1_meas hηN1_meas hgN2_meas hηN2_meas hgN3_meas hηN3_meas
    hPointwise_H hPointwise_DpH_prod

/-- **`aeMeasH`-input variant** of
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0`
(D2b-1c-ii-c2b keystone).

This is the **`measurable_H`-free** entry point used by the T3
(weak-growth / inf-convolution) substituted-pair Browder–Minty supply,
instantiable at `H := HdeltaK0`. Instead of consuming the strict global
joint measurability `hpow.measurable_H` (which is unavailable on
`HdeltaK0` at `{m = 0}`), it consumes:

* per-`n` H AE composite `hHcomp_ae_n`
  (`x ↦ H x (Dυ·x) (S.indicator ρ x + 1/(n+1))` is `AEMeasurable`),
  built for `HdeltaK0` via `aemeasurable_HdeltaK0_comp_of_rc0`;
* boundary H AE composite `hHcomp_ae_lim`
  (`x ↦ H x (Dυ·x) (S.indicator ρ x)` is `AEMeasurable`).

All other H/DpH data is supplied as the **genuine individual fields**:
`hDpH_meas` (DpH globally measurable, D2b-1a), `hcont_H_pm`,
`hcont_DpH_pm`, `hDpH_upper`, and the bare growth exponents `α β` with
`hα : 1 < α`, `hβ : 0 < β` and constant `C`. No `RegularityH`/
`HypothesisPowerGrowth` binder appears.

This is an **additive** producer: the strict `…_of_rc0` is left intact
for the T1 (`thm_main_simplePowerGrowth_paper`) and T2
(`thm_main_congestion_growth_paper`) headline theorems, whose `#print
axioms` are unchanged. The strict `…_of_rc0` could itself be recovered
as a thin wrapper deriving the two H AE composites from
`hpow.measurable_H.comp_aemeasurable` and supplying the bundle fields,
but we keep it as a standalone proof to avoid disturbing T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    -- DpH joint measurability (D2b-1a; `DpHepsilonFam` is globally measurable).
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    -- The two `RegularityH` continuity fields on `{0 < m}` (individual,
    -- NOT the bundle; available for `HdeltaK0`).
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hcont_DpH_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    -- The power-growth DpH bound on `{0 < m}` at the bare exponents `α β`.
    (hDpH_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    -- Test-triple data.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    -- Measurabilities of the test-triple structural data.
    (hS : MeasurableSet S) (hρ : Measurable ρ)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `ρ`.
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    -- `MemLpPer` of `S.indicator ρ` at `βBarReal`.
    (hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    -- The two H AE composites (replacing `hpow.measurable_H`).
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x))
      (volume.restrict (UnitCube d)))
    -- The six dominator pairs at the bare-`β` Hölder-paired exponents.
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) := by
  -- Standing positivity facts on the bare exponents.
  have hα_pos : 0 < α := lt_trans Real.zero_lt_one hα
  have hβ_pos : 0 < β := hβ
  have hbb_pos : 0 < β + 1 := by linarith
  have hβp_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ_pos
  -- Six measurability witnesses (gN1 / ηN2 routed through the AE variants).
  have hgN1_meas := set_perturbation_gN1_meas_of_aeMeasH (H := H)
    (S := S) (ρ := ρ) (V := V) (υ := υ) (Dυ := Dυ)
    hV.aestronglyMeasurable hυ.aestronglyMeasurable hHcomp_ae_n
  have hηN1_meas := set_perturbation_ηN1_meas hS hρ hm
    (S := S) (ρ := ρ) (m := m)
  have hgN2_meas := set_perturbation_gN2_meas hS hρ
    (S := S) (ρ := ρ)
  have hηN2_meas := set_perturbation_ηN2_meas_of_meas hDpH_meas hS hρ hDυ hDu
    (S := S) (ρ := ρ) (Dυ := Dυ) (Du := Du)
  have hgN3_meas := set_perturbation_gN3_meas hS hρ
    (S := S) (ρ := ρ)
  have hηN3_meas := set_perturbation_ηN3_meas hυ hu
    (υ := υ) (u := u)
  -- Pointwise tendsto inputs (continuity-only H / DpH-of-fields).
  have hPointwise_H :=
    set_perturbation_pointwise_tendsto_H_of_cont (V := V) hcont_H_pm
      (S := S) (ρ := ρ) (υ := υ) hρ_nn hH_rc0 Dυ
  have hPointwise_DpH_prod :=
    set_perturbation_pointwise_tendsto_DpH_of_fields (DpH := DpH)
      hα hβ hcont_DpH_pm hDpH_upper
      (S := S) (ρ := ρ) hρ_nn Dυ Du
  -- Real Hölder pairs.
  have hHJB_pq : Real.HolderConjugate ((β + 1) / β) (β + 1) := by
    refine ⟨?_, hβp_pos, hbb_pos⟩
    field_simp
  have hflux_pq :
      Real.HolderConjugate (β + 1) ((β + 1) / β) := by
    refine ⟨?_, hbb_pos, hβp_pos⟩
    field_simp
    ring
  have hmass_pq : Real.HolderConjugate (β + 1) ((β + 1) / β) := by
    refine ⟨?_, hbb_pos, hβp_pos⟩
    field_simp
    ring
  -- Restricted measure.
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm_def
  haveI : IsFiniteMeasure μm := by
    rw [hμm_def]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Per-`n` HJB summand integrability.
  have h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x)
          * (S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)) μm := by
    intro n
    have hgN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => -(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖
            ≤ (1 : ℝ) * ‖Gh x‖ := by
        filter_upwards [hGh_bd n] with x hx
        have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGh_memLp.toMemLp (hgN1_meas n) hbd)
    have hηN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖
            ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd n] with x hx
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp (hηN1_meas n) hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq hgN1_memLp hηN1_memLp
  -- Per-`n` flux summand integrability.
  have h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x))) μm := by
    intro n
    have hgN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ (1 : ℝ) * ‖Gf x‖ := by
        filter_upwards [hGf_bd n] with x hx
        have hGf_nn : 0 ≤ Gf x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGf_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGf_memLp.toMemLp (hgN2_meas n) hbd)
    have hηN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => DpH x (fun i => Dυ i x)
                  (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖DpH x (fun i => Dυ i x)
                (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x)‖ ≤ (1 : ℝ) * ‖Ef x‖ := by
        filter_upwards [hEf_bd n] with x hx
        have hEf_nn : 0 ≤ Ef x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEf_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEf_memLp.toMemLp (hηN2_meas n) hbd)
    exact Periodic.MemLpPer.integrable_mul hflux_pq hgN2_memLp hηN2_memLp
  -- Per-`n` mass summand integrability.
  have h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x)) μm := by
    intro n
    have hgN3_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖
            ≤ (1 : ℝ) * ‖Gm x‖ := by
        filter_upwards [hGm_bd n] with x hx
        have hGm_nn : 0 ≤ Gm x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGm_memLp.toMemLp (hgN3_meas n) hbd)
    have hηN3_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => υ x - u x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖υ x - u x‖ ≤ (1 : ℝ) * ‖Em x‖ := by
        filter_upwards [hEm_bd] with x hx
        have hEm_nn : 0 ≤ Em x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEm_memLp.toMemLp (hηN3_meas 0) hbd)
    exact Periodic.MemLpPer.integrable_mul hmass_pq hgN3_memLp hηN3_memLp
  -- HJB limit-integrability via squeeze on individual factors.
  -- Here the limit H composite is consumed as `hHcomp_ae_lim` (NO
  -- `hpow.measurable_H`).
  have hgN1_lim_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x) μm := by
    exact (((hυ.aemeasurable.neg).sub hHcomp_ae_lim).add
      hV.aemeasurable).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(υ x) - H x (fun i => Dυ i x)
            (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖)
      Filter.atTop
      (𝓝 ‖-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have hEh_bd_lim :
      ∀ᵐ x ∂μm, ‖S.indicator ρ x - m x‖ ≤ Eh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x :=
      MeasureTheory.ae_all_iff.mpr hEh_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) Filter.atTop
          (𝓝 (S.indicator ρ x - m x)) := by
      have := (h_one_div_tendsto.const_add (S.indicator ρ x)).sub_const (m x)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖)
      Filter.atTop (𝓝 ‖S.indicator ρ x - m x‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x)
          * (S.indicator ρ x - m x)) μm := by
    have hgN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => -(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => Dυ i x) (S.indicator ρ x) + V x‖
            ≤ (1 : ℝ) * ‖Gh x‖ := by
        filter_upwards [hGh_bd_lim, hGh_bd 0] with x hx h0
        have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGh_memLp.toMemLp hgN1_lim_meas hbd)
    have hηN1_lim_meas :
        AEStronglyMeasurable (fun x => S.indicator ρ x - m x) μm :=
      ((hρ.indicator hS).sub hm).aestronglyMeasurable
    have hηN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => S.indicator ρ x - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x - m x‖ ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd_lim, hEh_bd 0] with x hx h0
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp hηN1_lim_meas hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq
      hgN1_lim_memLp hηN1_lim_memLp
  -- Flux limit-integrability: full-product squeeze on `Gf · Ef ∈ L¹`.
  -- The limit DpH composite uses `hDpH_meas.comp` (STRICT; `DpHepsilonFam`
  -- globally measurable, D2b-1a).
  have h_int2_lim :
      Integrable (fun x =>
        S.indicator ρ x
          * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))) μm := by
    have hSρ_meas : Measurable (fun x : (Fin d → ℝ) => S.indicator ρ x) :=
      hρ.indicator hS
    have hDυ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
      measurable_pi_iff.mpr hDυ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => Dυ i x), S.indicator ρ x)) :=
      measurable_id.prodMk (hDυ_pi.prodMk hSρ_meas)
    have hDpHcomp : Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x)) :=
      hDpH_meas.comp hxpm
    have hDpHcomp_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x) i) :=
      fun i => (measurable_pi_apply i).comp hDpHcomp
    have hDdiff_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) => Dυ i x - Du i x) :=
      fun i => (hDυ i).sub (hDu i)
    have hsum_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x) i
            * (Dυ i x - Du i x)) :=
      fun i => (hDpHcomp_i i).mul (hDdiff_i i)
    have hdot : Measurable
        (fun x : (Fin d → ℝ) =>
          ∑ i : Fin d,
            DpH x (fun i => Dυ i x) (S.indicator ρ x) i
              * (Dυ i x - Du i x)) :=
      Finset.measurable_sum _ (fun i _ => hsum_i i)
    have hdot_eq :
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => Dυ i x) (S.indicator ρ x)
            ⬝ (fun i => Dυ i x - Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                DpH x (fun i => Dυ i x) (S.indicator ρ x) i
                  * (Dυ i x - Du i x)) := by
      funext x; rfl
    have hflux_lim_meas :
        AEStronglyMeasurable
          (fun x => DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x)) μm := by
      rw [hdot_eq]; exact hdot.aestronglyMeasurable
    have hprod_lim_meas :
        AEStronglyMeasurable
          (fun x => S.indicator ρ x
              * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
                  ⬝ (fun i => Dυ i x - Du i x))) μm :=
      hSρ_meas.aestronglyMeasurable.mul hflux_lim_meas
    have hbound_int : Integrable (fun x => Gf x * Ef x) μm :=
      Periodic.MemLpPer.integrable_mul hflux_pq hGf_memLp hEf_memLp
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hprod_bd_n : ∀ n : ℕ, ∀ᵐ x ∂μm,
        ‖(S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x))‖ ≤ Gf x * Ef x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    have hprod_bd_lim : ∀ᵐ x ∂μm,
        ‖S.indicator ρ x * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))‖ ≤ Gf x * Ef x := by
      have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
          ‖(S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x))‖ ≤ Gf x * Ef x :=
        MeasureTheory.ae_all_iff.mpr hprod_bd_n
      filter_upwards [hPointwise_DpH_prod, h_all_n] with x hx_pt h_seq
      have h_norm_lim : Filter.Tendsto
        (fun n : ℕ => ‖(S.indicator ρ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => Dυ i x - Du i x))‖)
        Filter.atTop
        (𝓝 ‖S.indicator ρ x * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))‖) :=
        (continuous_norm.tendsto _).comp hx_pt
      exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
        (Filter.Eventually.of_forall h_seq)
    have hbd' : ∀ᵐ x ∂μm,
        ‖S.indicator ρ x * (DpH x (fun i => Dυ i x) (S.indicator ρ x)
              ⬝ (fun i => Dυ i x - Du i x))‖ ≤ ‖Gf x * Ef x‖ := by
      filter_upwards [hprod_bd_lim, hGf_nn, hEf_nn] with x hx h1 h2
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg h1 h2)]
      simp only [Real.norm_eq_abs] at hx
      exact hx
    exact hbound_int.mono hprod_lim_meas hbd'
  -- Mass limit-integrability.
  have hgN3_lim_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => S.indicator ρ x - 1) μm :=
    ((hρ.indicator hS).sub_const _).aestronglyMeasurable
  have hηN3_lim_meas :
      AEStronglyMeasurable (fun x : (Fin d → ℝ) => υ x - u x) μm :=
    (hυ.sub hu).aestronglyMeasurable
  have hGm_bd_lim :
      ∀ᵐ x ∂μm, ‖S.indicator ρ x - 1‖ ≤ Gm x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x :=
      MeasureTheory.ae_all_iff.mpr hGm_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1) Filter.atTop
          (𝓝 (S.indicator ρ x - 1)) := by
      have := (h_one_div_tendsto.const_add (S.indicator ρ x)).sub_const (1 : ℝ)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖)
      Filter.atTop (𝓝 ‖S.indicator ρ x - 1‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int3_lim :
      Integrable (fun x => (S.indicator ρ x - 1) * (υ x - u x)) μm := by
    have hgN3_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => S.indicator ρ x - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖S.indicator ρ x - 1‖ ≤ (1 : ℝ) * ‖Gm x‖ := by
        filter_upwards [hGm_bd_lim, hGm_bd 0] with x hx h0
        have hGm_nn : 0 ≤ Gm x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGm_memLp.toMemLp hgN3_lim_meas hbd)
    have hηN3_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => υ x - u x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖υ x - u x‖ ≤ (1 : ℝ) * ‖Em x‖ := by
        filter_upwards [hEm_bd] with x hx
        have hEm_nn : 0 ≤ Em x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEm_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEm_memLp.toMemLp hηN3_lim_meas hbd)
    exact Periodic.MemLpPer.integrable_mul hmass_pq
      hgN3_lim_memLp hηN3_lim_memLp
  -- Apply the headline (`β`-decoupled, bare `β`/`hβ`).
  exact mfgOperatorEpsPair_tendsto_set_perturbation
    (V := V) (H := H) (DpH := DpH)
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    (β := β) hβ hExp Dυ υ u Du m S ρ hSρ_memLp hρ_nn
    h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    Gf Ef hGf_memLp hEf_memLp hGf_bd hEf_bd
    Gm Em hGm_memLp hEm_memLp hGm_bd hEm_bd
    hgN1_meas hηN1_meas hgN2_meas hηN2_meas hgN3_meas hηN3_meas
    hPointwise_H hPointwise_DpH_prod

/-- **Hext-bundle wrapper** recovering the original
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
signature from the `rc0`-input core
`…_of_rc0`. Derives the right-continuity certificate `hH_rc0` from the
`HypothesisHat0`/`Hext_finite_at_zero`/`H_zero_eq_Hext` bundle via
`Hamiltonian.H_rc0_of_hHat0`, then delegates. (T1 / simple-power chain
entry point; the T3 chain calls `…_of_rc0` directly to stay Hext-free.) -/
theorem mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (hS : MeasurableSet S) (hρ : Measurable ρ)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) :=
  mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0
    (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hpow hRegH hExp
    (StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hHat0 hFin hAgree)
    Dυ υ u Du m V S ρ hS hρ hm hV hυ hu hDυ hDu hρ_nn hSρ_memLp
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    Gf Ef hGf_memLp hEf_memLp hGf_bd hEf_bd
    Gm Em hGm_memLp hEm_memLp hGm_bd hEm_bd

/-- **AE-strongly-measurable test-data + `V` wrapper for the
set-perturbation consumer.**

Same conclusion as
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses` but
takes AE-strongly-measurable witnesses for `V` (iter 0674) and
additionally for the test data `(ρ, υ, Dυ)` (iter post-0689,
`paperSolFor-final-phase5-aggregator-closed-testdata-meas-bridge-set`)
in place of strict `Measurable` witnesses. Used by the closed supplier
chain where the test data enters via `MemLpPer`/`MemSobolevPer` rather
than via bare measurability witnesses.

The body introduces measurable representatives
`V' := hV.mk V`, `ρ' := hρ.mk ρ`, `υ' := hυ.mk υ`,
`Dυ' i := (hDυ i).mk (Dυ i)`, transports the six per-`n` bounds and
the `MemLpPer`/non-negativity inputs from `(ρ, υ, Dυ, V)` to
`(ρ', υ', Dυ', V')` via the a.e. equalities, calls the strict consumer
at the primed data, and bridges the resulting `Tendsto` back via
`mfgOperatorEpsPair_congr_V_ae` (for `V`),
`mfgOperatorEpsPair_congr_ae_primal` (for the primal triple
`(Dυ, S.indicator ρ, υ)`), and `mfgOperatorEpsPair_congr_ae`
(for the test triple `(Dυ - Du, S.indicator ρ + 1/n - m, υ - u)`). -/
theorem mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (hS : MeasurableSet S)
    -- Iter-0713 refactor (option b of
    -- `paperSolFor-final-phase5-aggregator-closed-set-rho-meas-supplier`):
    -- the consumer's body uses `hρ` exclusively through `S.indicator ρ`,
    -- so we take AE-strong-measurability of the indicator directly. The
    -- partial aggregator's `residueOf_set` already supplies
    -- `MemLpPer (S.indicator ρ)`, from which the closed producer can
    -- build this field via `.aestronglyMeasurable`.
    (hρ : AEStronglyMeasurable (S.indicator ρ) (volume.restrict (UnitCube d)))
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hDυ : ∀ i, AEStronglyMeasurable (Dυ i) (volume.restrict (UnitCube d)))
    (hDu : ∀ i, Measurable (Du i))
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) := by
  -- Iter-0713 option-(b) refactor. We now have AE-strong-measurability
  -- of the indicator `S.indicator ρ` (rather than raw `ρ`), so we build
  -- a measurable representative `Sρ'` of `S.indicator ρ` and pass it as
  -- the `ρ`-slot of the strict consumer at the test set `S' := Set.univ`.
  -- Then `Set.univ.indicator Sρ' = Sρ'` pointwise, so the strict consumer's
  -- internal `S'.indicator ρ` matches our `Sρ'`. Finally we transport the
  -- resulting Tendsto back to the original `(S.indicator ρ, υ, Dυ, V)`
  -- shape via the congr_ae chain.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  -- Measurable representative of `S.indicator ρ`.
  set Sρ' : (Fin d → ℝ) → ℝ := hρ.mk (S.indicator ρ) with hSρ'_def
  have hSρ'_meas : Measurable Sρ' := hρ.measurable_mk
  have hSρ_ae0 : S.indicator ρ =ᵐ[volume.restrict (UnitCube d)] Sρ' :=
    hρ.ae_eq_mk
  have hSρ_ae : (fun x => S.indicator ρ x)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => Sρ' x) := hSρ_ae0
  have hSρ_ae_symm : (fun x => Sρ' x)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => S.indicator ρ x) :=
    hSρ_ae.symm
  set υ' : (Fin d → ℝ) → ℝ := hυ.mk υ with hυ'_def
  have hυ'_meas : Measurable υ' := hυ.measurable_mk
  have hυ_ae : υ =ᵐ[volume.restrict (UnitCube d)] υ' := hυ.ae_eq_mk
  have hυ_ae_symm : υ' =ᵐ[volume.restrict (UnitCube d)] υ := hυ_ae.symm
  set Dυ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hDυ i).mk (Dυ i) with hDυ'_def
  have hDυ'_meas : ∀ i, Measurable (Dυ' i) := fun i => (hDυ i).measurable_mk
  have hDυ_ae : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i :=
    fun i => (hDυ i).ae_eq_mk
  have hDυ_ae_symm : ∀ i, Dυ' i =ᵐ[volume.restrict (UnitCube d)] Dυ i :=
    fun i => (hDυ_ae i).symm
  -- Pointwise equality `Set.univ.indicator Sρ' x = Sρ' x`.
  have hUnivInd : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator Sρ' x = Sρ' x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  -- The function-extensionality form, needed for rewriting bare references.
  have hUnivInd_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator Sρ' = Sρ' := by
    funext x; exact hUnivInd x
  -- Non-negativity of `Sρ'`. From `0 ≤ ρ` a.e. we get `0 ≤ S.indicator ρ`
  -- a.e. (since the indicator is either `ρ` or `0`), and then transport
  -- to `Sρ'` via `hSρ_ae`.
  have hSρ_nn_orig : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ S.indicator ρ x := by
    filter_upwards [hρ_nn] with x hx
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS]; exact hx
    · simp [Set.indicator_of_notMem hxS]
  have hSρ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ Sρ' x := by
    filter_upwards [hSρ_nn_orig, hSρ_ae0] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Transport `hSρ_memLp` from `S.indicator ρ` to `Sρ'`.
  have hSρ'_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) Sρ' :=
    Periodic.MemLpPer.congr_ae_unitCube hSρ_memLp hSρ_ae
  -- Re-express `hSρ'_memLp` as `MemLpPer (Set.univ.indicator Sρ')` so the
  -- strict consumer accepts it at `S' := Set.univ`.
  have hSρ'_memLp_univ :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator Sρ') := by
    rw [hUnivInd_eq]; exact hSρ'_memLp
  -- Transport the six per-`n` bounds from `(S.indicator ρ, υ, Dυ, V)` to
  -- `(Sρ', υ', Dυ', V')`, then re-express using
  -- `Set.univ.indicator Sρ' = Sρ'`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ' x) - H x (fun i => Dυ' i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
                + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hGh_bd n, hV_ae, hυ_ae, hDυ_all_ae,
                    hSρ_ae] with x hx hVxeq hυxeq hDυxeq hSρxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    rw [hUnivInd, ← hVxeq, ← hυxeq, ← hSρxeq, ← hpt]
    exact hx
  have hEh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x := by
    intro n
    filter_upwards [hEh_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hGf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x := by
    intro n
    filter_upwards [hGf_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hEf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ' i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ' i x - Du i x)‖ ≤ Ef x := by
    intro n
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hEf_bd n, hSρ_ae, hDυ_all_ae] with x hx hSρxeq hDυxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    have hptsub : (fun i => Dυ i x - Du i x) = (fun i => Dυ' i x - Du i x) := by
      funext i; rw [hDυxeq i]
    rw [hUnivInd, ← hSρxeq, ← hpt, ← hptsub]
    exact hx
  have hGm_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x := by
    intro n
    filter_upwards [hGm_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hEm_bd' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ' x - u x‖ ≤ Em x := by
    filter_upwards [hEm_bd, hυ_ae] with x hx hυxeq
    rw [← hυxeq]; exact hx
  -- Apply the strict consumer at the primed data
  -- `(S := Set.univ, ρ := Sρ', υ', Dυ', V')`.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal')
      hpow hRegH hExp hHat0 hFin hAgree
      Dυ' υ' u Du m V' (Set.univ : Set (Fin d → ℝ)) Sρ'
      MeasurableSet.univ hSρ'_meas hm hV'_meas hυ'_meas hu hDυ'_meas hDu
      hSρ'_nn hSρ'_memLp_univ
      Gh Eh hGh_memLp hEh_memLp hGh_bd' hEh_bd'
      Gf Ef hGf_memLp hEf_memLp hGf_bd' hEf_bd'
      Gm Em hGm_memLp hEm_memLp hGm_bd' hEm_bd'
  -- Eliminate `Set.univ.indicator Sρ'` → `Sρ'` in the Tendsto statement.
  -- `simp_rw` handles λ-body occurrences; `rw [hUnivInd_eq]` handles bare
  -- function references (`Set.univ.indicator Sρ'` as a function-level term,
  -- e.g. in `Set.univ.indicator Sρ' - m`).
  simp_rw [hUnivInd] at h_tendsto
  rw [hUnivInd_eq] at h_tendsto
  -- Bridge the primed `Tendsto` back to the unprimed data in three steps:
  -- (i) `V' → V` via `mfgOperatorEpsPair_congr_V_ae`,
  -- (ii) primal triple `(Dυ', Sρ', υ') → (Dυ, S.indicator ρ, υ)`
  --      via `mfgOperatorEpsPair_congr_ae_primal`,
  -- (iii) test triple `(Dυ' - Du, Sρ' + 1/n - m, υ' - u) →
  --       (Dυ - Du, S.indicator ρ + 1/n - m, υ - u)` via
  --       `mfgOperatorEpsPair_congr_ae`.
  -- Per-`n` rewrites for the sequence side.
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => Dυ' i x - Du i x)
          (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u) := by
    intro n
    -- Step (i): swap V' → V.
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
        (fun i x => Dυ' i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hV_ae_symm
    -- Step (ii): swap primal `(Dυ', Sρ', υ') → (Dυ, S.indicator ρ, υ)`.
    have hμ_ae : (fun x => Sρ' x + 1 / ((n : ℝ) + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) := by
      filter_upwards [hSρ_ae_symm] with x hxeq; rw [hxeq]
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ' Dυ
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1))
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
        υ' υ
        (fun i x => Dυ' i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hDυ_ae_symm hμ_ae hυ_ae_symm
    -- Step (iii): swap test `(Dυ' - Du, Sρ' + 1/n - m, υ' - u) →
    --             (Dυ - Du, S.indicator ρ + 1/n - m, υ - u)`.
    have hDν_ae : ∀ i, (fun x => Dυ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
      intro i
      filter_upwards [hDυ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) := by
      filter_upwards [hSρ_ae_symm] with x hxeq; rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ i x - Du i x)
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
            (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
        (fun i x => Dυ' i x - Du i x) (fun i x => Dυ i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  -- Limit-side rewrite (mirror of `hSeq_eq` without the `1/(n+1)` term).
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' Sρ' υ'
          (fun i x => Dυ' i x - Du i x)
          (Sρ' - m) (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (S.indicator ρ) υ
          (fun i x => Dυ i x - Du i x)
          (S.indicator ρ - m) (υ - u) := by
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        Dυ' Sρ' υ'
        (fun i x => Dυ' i x - Du i x)
        (Sρ' - m) (υ' - u) hV_ae_symm
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ' Dυ
        Sρ' (S.indicator ρ)
        υ' υ
        (fun i x => Dυ' i x - Du i x)
        (Sρ' - m) (υ' - u)
        hDυ_ae_symm hSρ_ae_symm hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => Dυ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
      intro i
      filter_upwards [hDυ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (Sρ' - m)
        =ᵐ[volume.restrict (UnitCube d)] (S.indicator ρ - m) := by
      filter_upwards [hSρ_ae_symm] with x hxeq
      change Sρ' x - m x = S.indicator ρ x - m x
      rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ (S.indicator ρ) υ
        (fun i x => Dυ' i x - Du i x) (fun i x => Dυ i x - Du i x)
        (Sρ' - m) (S.indicator ρ - m)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  -- Stitch the per-`n` and limit rewrites into a `Tendsto` congruence.
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => Dυ' i x - Du i x)
          (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  exact h_tendsto

/-- **Hext-free (`rc0`) AE-strongly-measurable set-perturbation bridge.**

Identical conclusion and AE-strong-measurability interface to
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
above, but instead of the `Hext_finite_at_zero`-pulling triple
`(hHat0, hFin, hAgree)` it takes the **paper line-1821 right-continuity**
rider `hH_rc0` directly and routes the inner strict call through the
Hext-free core
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0`.

This is the reusable bridge that the substituted-pair `hMinty_set`
δ-limit wrapper (T3 A1d-final, step 6+) consumes: the substituted
operator `A_ε^δ` must stay Hext-free, so its operator-continuity
certificate cannot route through the T1 `_of_paperHypotheses` producer.

The body is the same measurable-representative transport as the
`_of_paperHypotheses` aesm variant; only the inner call differs. -/
theorem mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (hS : MeasurableSet S)
    (hρ : AEStronglyMeasurable (S.indicator ρ) (volume.restrict (UnitCube d)))
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hDυ : ∀ i, AEStronglyMeasurable (Dυ i) (volume.restrict (UnitCube d)))
    (hDu : ∀ i, Measurable (Du i))
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) := by
  -- Same measurable-representative transport as the `_of_paperHypotheses`
  -- aesm variant; the inner strict call is the Hext-free `_of_rc0` core.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  set Sρ' : (Fin d → ℝ) → ℝ := hρ.mk (S.indicator ρ) with hSρ'_def
  have hSρ'_meas : Measurable Sρ' := hρ.measurable_mk
  have hSρ_ae0 : S.indicator ρ =ᵐ[volume.restrict (UnitCube d)] Sρ' :=
    hρ.ae_eq_mk
  have hSρ_ae : (fun x => S.indicator ρ x)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => Sρ' x) := hSρ_ae0
  have hSρ_ae_symm : (fun x => Sρ' x)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => S.indicator ρ x) :=
    hSρ_ae.symm
  set υ' : (Fin d → ℝ) → ℝ := hυ.mk υ with hυ'_def
  have hυ'_meas : Measurable υ' := hυ.measurable_mk
  have hυ_ae : υ =ᵐ[volume.restrict (UnitCube d)] υ' := hυ.ae_eq_mk
  have hυ_ae_symm : υ' =ᵐ[volume.restrict (UnitCube d)] υ := hυ_ae.symm
  set Dυ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hDυ i).mk (Dυ i) with hDυ'_def
  have hDυ'_meas : ∀ i, Measurable (Dυ' i) := fun i => (hDυ i).measurable_mk
  have hDυ_ae : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i :=
    fun i => (hDυ i).ae_eq_mk
  have hDυ_ae_symm : ∀ i, Dυ' i =ᵐ[volume.restrict (UnitCube d)] Dυ i :=
    fun i => (hDυ_ae i).symm
  have hUnivInd : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator Sρ' x = Sρ' x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hUnivInd_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator Sρ' = Sρ' := by
    funext x; exact hUnivInd x
  have hSρ_nn_orig : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ S.indicator ρ x := by
    filter_upwards [hρ_nn] with x hx
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS]; exact hx
    · simp [Set.indicator_of_notMem hxS]
  have hSρ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ Sρ' x := by
    filter_upwards [hSρ_nn_orig, hSρ_ae0] with x hx hxeq
    rw [← hxeq]; exact hx
  have hSρ'_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) Sρ' :=
    Periodic.MemLpPer.congr_ae_unitCube hSρ_memLp hSρ_ae
  have hSρ'_memLp_univ :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator Sρ') := by
    rw [hUnivInd_eq]; exact hSρ'_memLp
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ' x) - H x (fun i => Dυ' i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
                + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hGh_bd n, hV_ae, hυ_ae, hDυ_all_ae,
                    hSρ_ae] with x hx hVxeq hυxeq hDυxeq hSρxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    rw [hUnivInd, ← hVxeq, ← hυxeq, ← hSρxeq, ← hpt]
    exact hx
  have hEh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x := by
    intro n
    filter_upwards [hEh_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hGf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x := by
    intro n
    filter_upwards [hGf_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hEf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ' i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ' i x - Du i x)‖ ≤ Ef x := by
    intro n
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hEf_bd n, hSρ_ae, hDυ_all_ae] with x hx hSρxeq hDυxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    have hptsub : (fun i => Dυ i x - Du i x) = (fun i => Dυ' i x - Du i x) := by
      funext i; rw [hDυxeq i]
    rw [hUnivInd, ← hSρxeq, ← hpt, ← hptsub]
    exact hx
  have hGm_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x := by
    intro n
    filter_upwards [hGm_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hEm_bd' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ' x - u x‖ ≤ Em x := by
    filter_upwards [hEm_bd, hυ_ae] with x hx hυxeq
    rw [← hυxeq]; exact hx
  -- Inner strict call: the Hext-free `_of_rc0` core at the primed data.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal')
      hpow hRegH hExp hH_rc0
      Dυ' υ' u Du m V' (Set.univ : Set (Fin d → ℝ)) Sρ'
      MeasurableSet.univ hSρ'_meas hm hV'_meas hυ'_meas hu hDυ'_meas hDu
      hSρ'_nn hSρ'_memLp_univ
      Gh Eh hGh_memLp hEh_memLp hGh_bd' hEh_bd'
      Gf Ef hGf_memLp hEf_memLp hGf_bd' hEf_bd'
      Gm Em hGm_memLp hEm_memLp hGm_bd' hEm_bd'
  simp_rw [hUnivInd] at h_tendsto
  rw [hUnivInd_eq] at h_tendsto
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => Dυ' i x - Du i x)
          (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u) := by
    intro n
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
        (fun i x => Dυ' i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hV_ae_symm
    have hμ_ae : (fun x => Sρ' x + 1 / ((n : ℝ) + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) := by
      filter_upwards [hSρ_ae_symm] with x hxeq; rw [hxeq]
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ' Dυ
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1))
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
        υ' υ
        (fun i x => Dυ' i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hDυ_ae_symm hμ_ae hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => Dυ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
      intro i
      filter_upwards [hDυ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) := by
      filter_upwards [hSρ_ae_symm] with x hxeq; rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ i x - Du i x)
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
            (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
        (fun i x => Dυ' i x - Du i x) (fun i x => Dυ i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' Sρ' υ'
          (fun i x => Dυ' i x - Du i x)
          (Sρ' - m) (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (S.indicator ρ) υ
          (fun i x => Dυ i x - Du i x)
          (S.indicator ρ - m) (υ - u) := by
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        Dυ' Sρ' υ'
        (fun i x => Dυ' i x - Du i x)
        (Sρ' - m) (υ' - u) hV_ae_symm
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ' Dυ
        Sρ' (S.indicator ρ)
        υ' υ
        (fun i x => Dυ' i x - Du i x)
        (Sρ' - m) (υ' - u)
        hDυ_ae_symm hSρ_ae_symm hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => Dυ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
      intro i
      filter_upwards [hDυ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (Sρ' - m)
        =ᵐ[volume.restrict (UnitCube d)] (S.indicator ρ - m) := by
      filter_upwards [hSρ_ae_symm] with x hxeq
      change Sρ' x - m x = S.indicator ρ x - m x
      rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ (S.indicator ρ) υ
        (fun i x => Dυ' i x - Du i x) (fun i x => Dυ i x - Du i x)
        (Sρ' - m) (S.indicator ρ - m)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => Dυ' i x - Du i x)
          (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  exact h_tendsto

/-- **`aeMeasH`-input, AE-strongly-measurable-input keystone** for the
set family (D2b-1c-ii-c4).

Same statement as
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`
(it takes AE-strongly-measurable structural test data and produces the
sequence `Tendsto` of `mfgOperatorEpsPair`), but — like the
`_of_rc0_of_aeMeasH` core it delegates to — it is **`measurable_H`-free**:
it drops the strict `RegularityH`/`HypothesisPowerGrowth` binders and
instead consumes the genuine individual H/DpH fields
(`hDpH_meas, hcont_H_pm, hcont_DpH_pm, hDpH_upper`, bare exponents `α β`)
plus the two H AE composites at the *original* (unprimed) test data
`(Dυ, S.indicator ρ)`.

This is the bridge the `HdeltaK0`/T3 `paperSection8_hMinty_*_of_aeMeasH`
producers route through: it does the same measurable-representative
transport as the strict aesm bridge, then transports the AE composites
across the a.e.-equalities `Dυ' =ᵐ Dυ`, `Sρ' =ᵐ S.indicator ρ` and
delegates to `…_of_rc0_of_aeMeasH` at the primed data and `S := univ`.

Additive: the strict `_of_aestronglyMeasurable_of_rc0` is left intact
for T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hcont_DpH_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hDpH_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (hS : MeasurableSet S)
    (hρ : AEStronglyMeasurable (S.indicator ρ) (volume.restrict (UnitCube d)))
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hDυ : ∀ i, AEStronglyMeasurable (Dυ i) (volume.restrict (UnitCube d)))
    (hDu : ∀ i, Measurable (Du i))
    (hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) (S.indicator ρ))
    -- The two H AE composites at the ORIGINAL (unprimed) test data.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x))
      (volume.restrict (UnitCube d)))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u))) := by
  -- Same measurable-representative transport as the strict aesm bridge.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  set Sρ' : (Fin d → ℝ) → ℝ := hρ.mk (S.indicator ρ) with hSρ'_def
  have hSρ'_meas : Measurable Sρ' := hρ.measurable_mk
  have hSρ_ae0 : S.indicator ρ =ᵐ[volume.restrict (UnitCube d)] Sρ' :=
    hρ.ae_eq_mk
  have hSρ_ae : (fun x => S.indicator ρ x)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => Sρ' x) := hSρ_ae0
  have hSρ_ae_symm : (fun x => Sρ' x)
      =ᵐ[volume.restrict (UnitCube d)] (fun x => S.indicator ρ x) :=
    hSρ_ae.symm
  set υ' : (Fin d → ℝ) → ℝ := hυ.mk υ with hυ'_def
  have hυ'_meas : Measurable υ' := hυ.measurable_mk
  have hυ_ae : υ =ᵐ[volume.restrict (UnitCube d)] υ' := hυ.ae_eq_mk
  have hυ_ae_symm : υ' =ᵐ[volume.restrict (UnitCube d)] υ := hυ_ae.symm
  set Dυ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hDυ i).mk (Dυ i) with hDυ'_def
  have hDυ'_meas : ∀ i, Measurable (Dυ' i) := fun i => (hDυ i).measurable_mk
  have hDυ_ae : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i :=
    fun i => (hDυ i).ae_eq_mk
  have hDυ_ae_symm : ∀ i, Dυ' i =ᵐ[volume.restrict (UnitCube d)] Dυ i :=
    fun i => (hDυ_ae i).symm
  have hUnivInd : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator Sρ' x = Sρ' x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hUnivInd_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator Sρ' = Sρ' := by
    funext x; exact hUnivInd x
  have hSρ_nn_orig : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ S.indicator ρ x := by
    filter_upwards [hρ_nn] with x hx
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS]; exact hx
    · simp [Set.indicator_of_notMem hxS]
  have hSρ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ Sρ' x := by
    filter_upwards [hSρ_nn_orig, hSρ_ae0] with x hx hxeq
    rw [← hxeq]; exact hx
  have hSρ'_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) Sρ' :=
    Periodic.MemLpPer.congr_ae_unitCube hSρ_memLp hSρ_ae
  have hSρ'_memLp_univ :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator Sρ') := by
    rw [hUnivInd_eq]; exact hSρ'_memLp
  -- Transport the bounds to the primed data and `S := univ`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ' x) - H x (fun i => Dυ' i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
                + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hGh_bd n, hV_ae, hυ_ae, hDυ_all_ae,
                    hSρ_ae] with x hx hVxeq hυxeq hDυxeq hSρxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    rw [hUnivInd, ← hVxeq, ← hυxeq, ← hSρxeq, ← hpt]
    exact hx
  have hEh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x := by
    intro n
    filter_upwards [hEh_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hGf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x := by
    intro n
    filter_upwards [hGf_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hEf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ' i x)
              ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ' i x - Du i x)‖ ≤ Ef x := by
    intro n
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hEf_bd n, hSρ_ae, hDυ_all_ae] with x hx hSρxeq hDυxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    have hptsub : (fun i => Dυ i x - Du i x) = (fun i => Dυ' i x - Du i x) := by
      funext i; rw [hDυxeq i]
    rw [hUnivInd, ← hSρxeq, ← hpt, ← hptsub]
    exact hx
  have hGm_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x := by
    intro n
    filter_upwards [hGm_bd n, hSρ_ae] with x hx hSρxeq
    rw [hUnivInd, ← hSρxeq]; exact hx
  have hEm_bd' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ' x - u x‖ ≤ Em x := by
    filter_upwards [hEm_bd, hυ_ae] with x hx hυxeq
    rw [← hυxeq]; exact hx
  -- Transport the two H AE composites to the primed data and `S := univ`.
  have hHcomp_ae_n' : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ' i x)
          ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x
            + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)) := by
    intro n
    refine (hHcomp_ae_n n).congr ?_
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hSρ_ae, hDυ_all_ae] with x hSρxeq hDυxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    rw [hUnivInd, ← hSρxeq, ← hpt]
  have hHcomp_ae_lim' : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ' i x)
          ((Set.univ : Set (Fin d → ℝ)).indicator Sρ' x))
      (volume.restrict (UnitCube d)) := by
    refine hHcomp_ae_lim.congr ?_
    have hDυ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, Dυ i x = Dυ' i x := by
      rw [Filter.eventually_all]; exact hDυ_ae
    filter_upwards [hSρ_ae, hDυ_all_ae] with x hSρxeq hDυxeq
    have hpt : (fun i => Dυ i x) = (fun i => Dυ' i x) := by
      funext i; exact hDυxeq i
    rw [hUnivInd, ← hSρxeq, ← hpt]
  -- Inner call: the `measurable_H`-free `_of_rc0_of_aeMeasH` core.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (C := C) (α := α) (β := β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ' υ' u Du m V' (Set.univ : Set (Fin d → ℝ)) Sρ'
      MeasurableSet.univ hSρ'_meas hm hV'_meas hυ'_meas hu hDυ'_meas hDu
      hSρ'_nn hSρ'_memLp_univ
      hHcomp_ae_n' hHcomp_ae_lim'
      Gh Eh hGh_memLp hEh_memLp hGh_bd' hEh_bd'
      Gf Ef hGf_memLp hEf_memLp hGf_bd' hEf_bd'
      Gm Em hGm_memLp hEm_memLp hGm_bd' hEm_bd'
  simp_rw [hUnivInd] at h_tendsto
  rw [hUnivInd_eq] at h_tendsto
  -- Transport the sequence + limit operators back to the original data.
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => Dυ' i x - Du i x)
          (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u) := by
    intro n
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
        (fun i x => Dυ' i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hV_ae_symm
    have hμ_ae : (fun x => Sρ' x + 1 / ((n : ℝ) + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) := by
      filter_upwards [hSρ_ae_symm] with x hxeq; rw [hxeq]
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ' Dυ
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1))
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
        υ' υ
        (fun i x => Dυ' i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hDυ_ae_symm hμ_ae hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => Dυ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
      intro i
      filter_upwards [hDυ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x) := by
      filter_upwards [hSρ_ae_symm] with x hxeq; rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ' i x - Du i x)
            (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => Dυ i x - Du i x)
            (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
            (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
        (fun i x => Dυ' i x - Du i x) (fun i x => Dυ i x - Du i x)
        (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' Sρ' υ'
          (fun i x => Dυ' i x - Du i x)
          (Sρ' - m) (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (S.indicator ρ) υ
          (fun i x => Dυ i x - Du i x)
          (S.indicator ρ - m) (υ - u) := by
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        Dυ' Sρ' υ'
        (fun i x => Dυ' i x - Du i x)
        (Sρ' - m) (υ' - u) hV_ae_symm
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ' Sρ' υ'
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ' Dυ
        Sρ' (S.indicator ρ)
        υ' υ
        (fun i x => Dυ' i x - Du i x)
        (Sρ' - m) (υ' - u)
        hDυ_ae_symm hSρ_ae_symm hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => Dυ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => Dυ i x - Du i x) := by
      intro i
      filter_upwards [hDυ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (Sρ' - m)
        =ᵐ[volume.restrict (UnitCube d)] (S.indicator ρ - m) := by
      filter_upwards [hSρ_ae_symm] with x hxeq
      change Sρ' x - m x = S.indicator ρ x - m x
      rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ' i x - Du i x)
            (Sρ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ (S.indicator ρ) υ
            (fun i x => Dυ i x - Du i x)
            (S.indicator ρ - m) (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        Dυ (S.indicator ρ) υ
        (fun i x => Dυ' i x - Du i x) (fun i x => Dυ i x - Du i x)
        (Sρ' - m) (S.indicator ρ - m)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Dυ' (fun x => Sρ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => Dυ' i x - Du i x)
          (fun x => Sρ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => Dυ i x - Du i x)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  exact h_tendsto

/-! ## Signed-perturbation specialisation:
`μ_n := m + σ · m · 1_S + 1/(n+1)`

This section discharges the `hCont` operator-tendsto certificate
consumed by `hVIeps_signed_of_KAepsi_VI` (Child D of the two-domain
consumed by `hVIeps_signed_of_KAepsi_VI` (Child D of the two-domain
redesign, narrowed shape per `infra-P4-narrow-hVIeps-signed-shape`).

The headline lemma `mfgOperatorEpsPair_tendsto_signed_perturbation`
specialises the consumer-level compositional lemma
`mfgOperatorEpsPair_tendsto_of_summands` at the paper-exact perturbation
`μ_n := m + σ · m · 1_S + 1/(n+1)` with limit
`μ_∞ := m + σ · m · 1_S`, against test direction `(0, η_n, 0)` with
`η_n := σ · m · 1_S + 1/(n+1)` and `η_∞ := σ · m · 1_S`.

Because the gradient test direction is zero (`Dν := fun _ _ => 0`)
and the value-function test slot is zero (`ν := fun _ => 0`), two of
the three integrand-level summands collapse pointwise to zero:

* **Flux summand:** `μ_n · (D_pH(·, Du, μ_n) ⬝ 0) = 0` pointwise (using
  `v ⬝ (fun _ => 0) = 0`).
* **Mass summand:** `(μ_n - 1) · 0 = 0` pointwise.

Both tendstos thus reduce to `tendsto_const_nhds`. Only the HJB summand
remains non-trivial, and is discharged by
`tendsto_setIntegral_HJB_mul_of_dom` exactly as in the set case.

Per CONVENTIONS §8 the following are authorised inputs (paper-level):

* the per-`x` pointwise tendsto input for `H` along `μ_n x → μ_∞ x`
  (continuity of `H` in the third argument);
* the per-`n` and per-limit integrability witnesses for the three
  `mfgOperatorPair` summands;
* the per-`x` HJB-summand dominator bounds (paper-level dominators
  composed from `RegularityH.measurable_*` and the AC2 dominator
  closures).

This shape exactly matches the abstract pattern set by
`hVIeps_signed_of_KAepsi_VI`. -/

/-- **Headline: `mfgOperatorEpsPair`-tendsto for the signed-family
Minty perturbation `μ_n := m + σ · m · 1_S + 1/(n+1)`.**

This is the Child D-specific specialisation of
`mfgOperatorEpsPair_tendsto_of_summands` (above) at the paper-exact
narrowed perturbation arising in `hVIeps_signed_of_KAepsi_VI`'s
strict-positive bridge.

Because the test direction is `(Dν, ν) = (0, 0)`, two of three
integrand-level summands collapse pointwise to zero, so only the HJB
summand requires the dominator/pointwise tendsto inputs. The flux and
mass tendstos are `tendsto_const_nhds` after a rewrite to `∫ 0 = 0`.

Per CONVENTIONS §8: the HJB-summand dominators `Gh, Eh` and the
HJB pointwise tendsto input `hPointwise_H` are accepted as authorised
hypotheses; their upstream derivation from
`RegularityH`/`HypothesisPowerGrowth` plus the AC2 dominator closures
is not factored out yet. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (_hRegH : RegularityH H DpH)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (_hSmeas : MeasurableSet S)
    -- Per-`n` integrability of the HJB summand at the perturbation
    -- `μ_n := m + σ · m · 1_S + 1/(n+1)` against `η_n := σ · m · 1_S + 1/(n+1)`.
    (h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x)
          * (σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)))
        (volume.restrict (UnitCube d)))
    -- Per-`n` integrability of the flux summand. Pointwise zero, but
    -- recorded for the `mfgOperatorPair_split` invocation below.
    (h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              ⬝ (fun _ : Fin d => (0 : ℝ))))
        (volume.restrict (UnitCube d)))
    -- Per-`n` integrability of the mass summand. Pointwise zero.
    (h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) - 1)
          * (0 : ℝ))
        (volume.restrict (UnitCube d)))
    -- Limit integrability at `μ_∞ := m + σ · m · 1_S`.
    (h_int1_lim :
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x)
          * (σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        (volume.restrict (UnitCube d)))
    (h_int2_lim :
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun _ : Fin d => (0 : ℝ))))
        (volume.restrict (UnitCube d)))
    (h_int3_lim :
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x - 1)
          * (0 : ℝ))
        (volume.restrict (UnitCube d)))
    -- HJB-summand dominator inputs.
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Eh x)
    -- AE-strong measurability of the HJB-summand factors.
    (hgN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          -(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)))
    (hηN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)))
    -- Per-`x` pointwise tendsto input for the HJB summand
    -- (authorised, CONVENTIONS §8 — continuity of `H` in the third
    -- argument; `RegularityH.continuous_H_pm` is `ContinuousOn {m > 0}`
    -- only and the limit `μ_∞ = m + σ · m · 1_S` may equal `0` on the
    -- complement of `S`, so this is paper-level material).
    (hPointwise_H :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n : ℕ =>
            -(u x) - H x (fun i => Du i x)
                  (m x + σ * m x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                            + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(u x) - H x (fun i => Du i x)
                    (m x + σ * m x *
                                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    + V x))) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Du
            (fun x => m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            u
            (fun _ _ => (0 : ℝ))
            (fun x => σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)))) := by
  -- Shorthand for the perturbation and its limit.
  set μN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) with hμN
  set μInf : (Fin d → ℝ) → ℝ :=
    fun x => m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x with hμInf
  set ηN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) with hηN
  set ηInf : (Fin d → ℝ) → ℝ :=
    fun x => σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x with hηInf
  -- Pointwise tendsto: `1/(n+1) → 0`.
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Pointwise tendsto: `μ_n x → μ_∞ x` (used for flux summand).
  have h_μN_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) := by
    intro x
    have :=
      h_one_div_tendsto.const_add (m x + σ * m x *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    simpa [hμN, hμInf, add_zero] using this
  -- AE version.
  have h_μN_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) :=
    Filter.Eventually.of_forall h_μN_pointwise
  -- Pointwise tendsto: `η_n x → η_∞ x`.
  have h_ηN_pointwise :
      ∀ x, Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) := by
    intro x
    have :=
      h_one_div_tendsto.const_add (σ * m x *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    simpa [hηN, hηInf, add_zero] using this
  -- AE version.
  have h_ηN_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) :=
    Filter.Eventually.of_forall h_ηN_pointwise
  -- Standing positivity facts on the paper exponents.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  -- Step 1: HJB integrand-level tendsto.
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (μN n x) + V x) * ηN n x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (μInf x) + V x) * ηInf x)) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := hpow.β) hβ_pos
      (gN := fun n x =>
        -(u x) - H x (fun i => Du i x) (μN n x) + V x)
      (gInf := fun x =>
        -(u x) - H x (fun i => Du i x) (μInf x) + V x)
      (ηN := ηN) (ηInf := ηInf)
      hGh_memLp hEh_memLp hgN1_meas hηN1_meas hGh_bd hEh_bd ?_ h_ηN_ae
    exact hPointwise_H
  -- Step 2: flux integrand-level tendsto. The flux integrand is
  -- pointwise zero because `D_pH ⬝ (fun _ => 0) = 0`. So both
  -- integrals collapse to `0` and the tendsto is constant.
  have h_dot_zero : ∀ (v : Fin d → ℝ),
      v ⬝ (fun _ : Fin d => (0 : ℝ)) = 0 := by
    intro v
    change ∑ i, v i * (0 : ℝ) = 0
    simp
  have h_flux_zero_n : ∀ n : ℕ, ∀ x : Fin d → ℝ,
      μN n x * (DpH x (fun i => Du i x) (μN n x)
                  ⬝ (fun _ : Fin d => (0 : ℝ))) = 0 := by
    intro n x
    rw [h_dot_zero]; ring
  have h_flux_zero_lim : ∀ x : Fin d → ℝ,
      μInf x * (DpH x (fun i => Du i x) (μInf x)
                  ⬝ (fun _ : Fin d => (0 : ℝ))) = 0 := by
    intro x
    rw [h_dot_zero]; ring
  have h_tendsto2 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          μN n x * (DpH x (fun i => Du i x) (μN n x)
                      ⬝ (fun _ : Fin d => (0 : ℝ))))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          μInf x * (DpH x (fun i => Du i x) (μInf x)
                      ⬝ (fun _ : Fin d => (0 : ℝ))))) := by
    have h_lim_zero :
        ∫ x in UnitCube d,
          μInf x * (DpH x (fun i => Du i x) (μInf x)
                      ⬝ (fun _ : Fin d => (0 : ℝ))) = 0 := by
      simp_rw [h_flux_zero_lim]
      exact MeasureTheory.integral_zero _ _
    have h_n_zero : ∀ n,
        ∫ x in UnitCube d,
          μN n x * (DpH x (fun i => Du i x) (μN n x)
                      ⬝ (fun _ : Fin d => (0 : ℝ))) = 0 := by
      intro n
      simp_rw [h_flux_zero_n n]
      exact MeasureTheory.integral_zero _ _
    rw [h_lim_zero]
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    exact Filter.Eventually.of_forall (fun n => (h_n_zero n).symm)
  -- Step 3: mass integrand-level tendsto. Pointwise zero (`(_ - 1) * 0 = 0`).
  have h_tendsto3 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d, (μN n x - 1) * (0 : ℝ))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (μInf x - 1) * (0 : ℝ))) := by
    have h_n_zero : ∀ n,
        ∫ x in UnitCube d, (μN n x - 1) * (0 : ℝ) = 0 := by
      intro n
      simp_rw [mul_zero]
      exact MeasureTheory.integral_zero _ _
    have h_lim_zero :
        ∫ x in UnitCube d, (μInf x - 1) * (0 : ℝ) = 0 := by
      simp_rw [mul_zero]
      exact MeasureTheory.integral_zero _ _
    rw [h_lim_zero]
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    exact Filter.Eventually.of_forall (fun n => (h_n_zero n).symm)
  -- Apply the consumer-level compositional lemma.
  -- We need the integrability witnesses cast into the `μN/ηN` shape.
  have h_int1_n' : ∀ n,
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x) (μN n x) + V x) * ηN n x)
        (volume.restrict (UnitCube d)) := h_int1_n
  have h_int2_n' : ∀ n,
      Integrable (fun x =>
        μN n x * (DpH x (fun i => Du i x) (μN n x)
                    ⬝ (fun _ : Fin d => (0 : ℝ))))
        (volume.restrict (UnitCube d)) := h_int2_n
  have h_int3_n' : ∀ n,
      Integrable (fun x => (μN n x - 1) * (0 : ℝ))
        (volume.restrict (UnitCube d)) := h_int3_n
  have h_int1_lim' :
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x) (μInf x) + V x) * ηInf x)
        (volume.restrict (UnitCube d)) := h_int1_lim
  have h_int2_lim' :
      Integrable (fun x =>
        μInf x * (DpH x (fun i => Du i x) (μInf x)
                    ⬝ (fun _ : Fin d => (0 : ℝ))))
        (volume.restrict (UnitCube d)) := h_int2_lim
  have h_int3_lim' :
      Integrable (fun x => (μInf x - 1) * (0 : ℝ))
        (volume.restrict (UnitCube d)) := h_int3_lim
  exact mfgOperatorEpsPair_tendsto_of_summands
    (V := V) (H := H) (DpH := DpH)
    Du u (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    μN μInf ηN ηInf
    h_int1_n' h_int2_n' h_int3_n'
    h_int1_lim' h_int2_lim' h_int3_lim'
    h_tendsto1 h_tendsto2 h_tendsto3

end Banach
end SimplePower
end Theorems
end StationaryMFG
end
