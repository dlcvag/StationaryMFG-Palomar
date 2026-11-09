module

public import StationaryMFG.Theorems.SimplePower.Banach.AbstractLifts
public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge
public import StationaryMFG.Theorems.SimplePower.Banach.Operator
public import StationaryMFG.Theorems.SimplePower.Banach.ExponentFacts
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Monotone.AbstractWeak
public import StationaryMFG.Periodic.Reflexive
public import StationaryMFG.Periodic.LpReflexive

/-!
# Uniform aux context for the regularised MFG operator

This module discharges Phase-4 task `infra-P4-rebuild-T3-uniform-aux`:
the **uniform aux context** `MFGOpEpsUniformAux` for the family
`mfgOperatorEps_CLM`, scoped to an entire domain `K`.

## Motivation

The expert-identified anti-pattern of the previous architecture was that
each `F.*` helper (e.g. the B.1/B.2/B.3 lifts) consumed *per-q*
`MFGOpEpsAuxHyps` certificates, forcing every consumer to re-supply them.
The fix is a single record bundling the per-q and per-pair aux hyps
once, scoped to the entire abstract-VI domain `K`.

## API

* `DuOf q`, `mOf q`, `uOf q` — bare-function projections of a Banach
  pair `q : XBanach d βBarReal γBarReal` into its primal triple
  `(Du, m, u)` of bare functions on the unit cube.
* `MFGOpEpsTestAuxHyps … V H DpH Du m u Du' m' u'` — bundle of the
  **two** primal `MFGOpEpsAuxHyps` certificates (one for each of the
  two triples). Sufficient for the cross-pairing of the operator at
  one primal triple against the test triple from the other.
* `MFGOpEpsUniformAux d ε V H DpH … K` — uniform record:
    * `of_mem : ∀ q ∈ K, MFGOpEpsAuxHyps … (DuOf q) (mOf q) (uOf q)`,
    * `of_test : ∀ q q' ∈ K, MFGOpEpsTestAuxHyps … (q's triple) (q's triple)`.
* `mfgOpEps_uniformAux_of_perPairAuxHyps` — producer that, given a
  per-q `MFGOpEpsAuxHyps` supplier on `K`, assembles the uniform record.

## Status

Per the rebuild plan T3, this module sits below T6
(`infra-P4-rebuild-T6-aepsiUniformContext`), which threads the
paper-hypothesis grinding `(hpow, hV) → MFGOpEpsAuxHyps` (currently
open work, tracked by `infra-P4-thin-chain-discharge`) into the
uniform record. T3 itself is purely structural: it defines the record
shape and the trivial assembler.
-/


@[expose] public section

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal

variable {d : ℕ}
variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- Local abbreviation for the Banach domain of `mfgOperatorEps_CLM`,
mirroring the private one in `Banach/AbstractLifts.lean`. We re-expose
it here (non-`private`) so that the uniform-aux record's domain can be
named in downstream modules. -/
abbrev XBanach (d : ℕ) (βBarReal γBarReal : ℝ) : Type :=
  Periodic.LpPer (ENNReal.ofReal βBarReal) d
    × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d

/-! ## Bare-function projections

`DuOf q`, `mOf q`, `uOf q` extract the primal triple of bare functions
`(Du, m, u) : (Fin d → (Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)`
from a Banach pair `q : XBanach d βBarReal γBarReal`. The `m` and `u`
projections use `Lp.coeFn` on the first factor and the value-component
of the Sobolev pair; `Du` uses the gradient component.
-/

/-- The bare-function `m`-component of a Banach pair. -/
def mOf {d : ℕ} {βBarReal γBarReal : ℝ}
    (q : XBanach d βBarReal γBarReal) :
    (Fin d → ℝ) → ℝ :=
  ⇑q.1

/-- The bare-function `u`-component (value) of a Banach pair. -/
def uOf {d : ℕ} {βBarReal γBarReal : ℝ}
    (q : XBanach d βBarReal γBarReal) :
    (Fin d → ℝ) → ℝ :=
  ⇑q.2.1

/-- The bare-function `Du`-component (gradient family) of a Banach
pair. -/
def DuOf {d : ℕ} {βBarReal γBarReal : ℝ}
    (q : XBanach d βBarReal γBarReal) :
    Fin d → (Fin d → ℝ) → ℝ :=
  fun i => ⇑(q.2.2 i)

@[simp] lemma mOf_def {d : ℕ} {βBarReal γBarReal : ℝ}
    (q : XBanach d βBarReal γBarReal) :
    mOf q = ⇑q.1 := rfl

@[simp] lemma uOf_def {d : ℕ} {βBarReal γBarReal : ℝ}
    (q : XBanach d βBarReal γBarReal) :
    uOf q = ⇑q.2.1 := rfl

@[simp] lemma DuOf_def {d : ℕ} {βBarReal γBarReal : ℝ}
    (q : XBanach d βBarReal γBarReal) (i : Fin d) :
    DuOf q i = ⇑(q.2.2 i) := rfl

/-! ## Per-pair test-aux bundle

`MFGOpEpsTestAuxHyps` carries the primal `MFGOpEpsAuxHyps` of *both*
triples of a pair. This is the level of input that any cross-pairing
of the operator (one triple as primal data, the other's bare-function
representatives as test triple) consumes — concretely, the
`integrable_mfgPair_integrand` and `integrable_gateaux_integrand`
helpers in `Banach/Operator.lean` need the primal aux hyps of one
triple, and the test side's `MemLpPer` certificates are automatic for
elements of `Lp` (via `MeasureTheory.Lp.memLp`).
-/

/-- **Per-pair test-aux bundle** for the regularised MFG operator.

Given two primal triples `(Du, m, u)` and `(Du', m', u')`, this records
a `MFGOpEpsAuxHyps` certificate for **each**. With both certificates
in hand, every cross-pairing of `mfgOperatorEpsPair` is integrable
(by the `integrable_mfgPair_integrand` / `integrable_gateaux_integrand`
helpers in `Banach/Operator.lean`, applied with the appropriate
`memLpPer_coe_lp_*` certificates for the test-side bare functions). -/
structure MFGOpEpsTestAuxHyps
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ)
    (Du' : Fin d → (Fin d → ℝ) → ℝ) (m' u' : (Fin d → ℝ) → ℝ) : Prop where
  /-- The primal `MFGOpEpsAuxHyps` certificate at the first triple. -/
  primal : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH Du m u
  /-- The primal `MFGOpEpsAuxHyps` certificate at the second triple. -/
  primal' : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH Du' m' u'

namespace MFGOpEpsTestAuxHyps

variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The reflected pair: swap the two triples. -/
def swap
    {Du : Fin d → (Fin d → ℝ) → ℝ} {m u : (Fin d → ℝ) → ℝ}
    {Du' : Fin d → (Fin d → ℝ) → ℝ} {m' u' : (Fin d → ℝ) → ℝ}
    (h : MFGOpEpsTestAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u Du' m' u') :
    MFGOpEpsTestAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH Du' m' u' Du m u where
  primal := h.primal'
  primal' := h.primal

end MFGOpEpsTestAuxHyps

/-- Build a `MFGOpEpsTestAuxHyps` from two primal `MFGOpEpsAuxHyps`. -/
def mfgOpEpsTestAuxHyps_of_pair
    {Du : Fin d → (Fin d → ℝ) → ℝ} {m u : (Fin d → ℝ) → ℝ}
    {Du' : Fin d → (Fin d → ℝ) → ℝ} {m' u' : (Fin d → ℝ) → ℝ}
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    (h' : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du' m' u') :
    MFGOpEpsTestAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH Du m u Du' m' u' where
  primal := h
  primal' := h'

/-! ## Uniform aux record

`MFGOpEpsUniformAux d ε V H DpH … K` packages the two universally-
quantified aux hyps over a domain `K ⊆ XBanach d βBarReal γBarReal`:

* `of_mem` — for every `q ∈ K`, the primal `MFGOpEpsAuxHyps` at the
  bare-function triple `(DuOf q, mOf q, uOf q)`.
* `of_test` — for every pair `q, q' ∈ K`, the per-pair test-aux at
  the two bare-function triples.

Per the rebuild plan, downstream B.1/B.2/B.3 lifts will consume this
record (instead of per-q `auxHyps` suppliers), unblocking the
"wrapper-on-wrapper" assembly pattern called out in
`docs/THEOREM1_BLOCKER.md`.
-/

/-- **Uniform aux context** for the regularised MFG operator on the
domain `K`. -/
structure MFGOpEpsUniformAux
    (d : ℕ) (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    (K : Set (XBanach d βBarReal γBarReal)) : Prop where
  /-- Per-`q ∈ K`, the primal `MFGOpEpsAuxHyps` certificate at the
  bare-function primal triple of `q`. -/
  of_mem :
    ∀ q ∈ K,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH (DuOf q) (mOf q) (uOf q)
  /-- Per-pair `q, q' ∈ K`, the test-aux certificate at the two bare-
  function primal triples. -/
  of_test :
    ∀ q ∈ K, ∀ q' ∈ K,
      MFGOpEpsTestAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH
        (DuOf q) (mOf q) (uOf q)
        (DuOf q') (mOf q') (uOf q')

namespace MFGOpEpsUniformAux

variable {ε : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {K : Set (XBanach d βBarReal γBarReal)}

/-- The `of_mem` projection at a fixed `q ∈ K`. -/
lemma auxHyps_of_mem
    (h : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K)
    {q : XBanach d βBarReal γBarReal} (hq : q ∈ K) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH (DuOf q) (mOf q) (uOf q) :=
  h.of_mem q hq

/-- The `of_test` projection at a fixed pair `q, q' ∈ K`. -/
lemma testAuxHyps_of_pair
    (h : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K)
    {q q' : XBanach d βBarReal γBarReal} (hq : q ∈ K) (hq' : q' ∈ K) :
    MFGOpEpsTestAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH
      (DuOf q) (mOf q) (uOf q)
      (DuOf q') (mOf q') (uOf q') :=
  h.of_test q hq q' hq'

/-- Restrict the uniform record to a smaller subdomain. -/
lemma mono
    (h : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K)
    {K' : Set (XBanach d βBarReal γBarReal)} (hK' : K' ⊆ K) :
    MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K' where
  of_mem := fun q hq => h.of_mem q (hK' hq)
  of_test := fun q hq q' hq' => h.of_test q (hK' hq) q' (hK' hq')

end MFGOpEpsUniformAux

/-! ## Producer

`mfgOpEps_uniformAux_of_perPairAuxHyps` assembles the uniform record
from a per-q `MFGOpEpsAuxHyps` supplier on `K`. The per-pair test-aux
is then trivially `mfgOpEpsTestAuxHyps_of_pair (auxHyps q hq) (auxHyps q' hq')`.

Per the rebuild plan, the *paper-hypothesis-direct* producer
`mfgOpEps_uniformAux_of_paperHypotheses` will be the headline outer
wrapper in T6, where the actual `(hpow, hV) → MFGOpEpsAuxHyps`
grinding (currently open work tracked by
`infra-P4-thin-chain-discharge`) lives. T3 itself is structural: it
exposes the producer parametric in the per-q aux hyps.
-/

/-- **Producer** of `MFGOpEpsUniformAux` from a per-q
`MFGOpEpsAuxHyps` supplier on `K`. -/
theorem mfgOpEps_uniformAux_of_perPairAuxHyps
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε : ℝ)
    (K : Set (XBanach d βBarReal γBarReal))
    (auxHyps : ∀ q ∈ K,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH (DuOf q) (mOf q) (uOf q)) :
    MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K where
  of_mem := auxHyps
  of_test := fun q hq q' hq' =>
    mfgOpEpsTestAuxHyps_of_pair (auxHyps q hq) (auxHyps q' hq')

/-! ## Sanity-check `example`s

These exercises confirm that the projection lemmas type-check on
trivial data and that the producer assembles cleanly from a constant
supplier. -/

/-- Sanity check: the `of_mem` projection delivers the per-q aux hyps. -/
example
    (ε : ℝ) (K : Set (XBanach d βBarReal γBarReal))
    (h : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K)
    (q : XBanach d βBarReal γBarReal) (hq : q ∈ K) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH (DuOf q) (mOf q) (uOf q) :=
  h.auxHyps_of_mem hq

/-- Sanity check: the `of_test` projection delivers the per-pair
test-aux hyps. -/
example
    (ε : ℝ) (K : Set (XBanach d βBarReal γBarReal))
    (h : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K)
    (q q' : XBanach d βBarReal γBarReal) (hq : q ∈ K) (hq' : q' ∈ K) :
    MFGOpEpsTestAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH
      (DuOf q) (mOf q) (uOf q)
      (DuOf q') (mOf q') (uOf q') :=
  h.testAuxHyps_of_pair hq hq'

/-- Sanity check: the producer assembles the uniform record from a
per-q supplier. -/
example
    (ε : ℝ) (K : Set (XBanach d βBarReal γBarReal))
    (auxHyps : ∀ q ∈ K,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH (DuOf q) (mOf q) (uOf q)) :
    MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal' K :=
  mfgOpEps_uniformAux_of_perPairAuxHyps ε K auxHyps

/-! ## T4 — Banach VI → bare regularised solution producer

Per `infra-P4-rebuild-T4-banachVI-to-bare`, this section assembles:

* `RegularizedBareSolution` — a bare-function record bundling
  `(m, u, Du)` with the integrability/non-negativity certificates
  needed downstream (T7's apriori-bound ingestion). Per the
  two-domain redesign child B, the universal `hVIeps` field has
  been replaced by three per-family fields `hVIeps_set`,
  `hVIeps_signed`, `hVIeps_transport`.
* `AepsiUniformContextK` — the K_Aepsi-form context record, the
  canonical replacement (post-`infra-P4-delete-AepsiUniformContext-K0-form`)
  of the legacy K0-form `AepsiUniformContext`.
* `exists_banachVI_at_eps_KAepsi` — Browder–Minty on the
  strict-positivity cone `K_Aepsi`, with the witness descended into
  `K0_Aepsi` via `K_Aepsi_closure_subset_K0_Aepsi`.
* `exists_regularizedBareSolution_K` — the bare-bridging producer
  consuming `AepsiUniformContextK` and the three Minty/δ-limit
  inputs.

See the AC amendments in
`docs/TASKS/in_flight/infra-P4-rebuild-T4-banachVI-to-bare.md` for
the historical context of the (now-deleted) K0-form chain. -/

open StationaryMFG.Monotone (IsMonotone IsHemicontinuous IsCoerciveAt)
open StationaryMFG.Periodic (IsReflexiveNormedSpace HasWeakDerivPer
  MemLpPer MemSobolevPer)
open StationaryMFG.Solutions.MFG (mfgOperatorEpsPair absPowMinusTwo
  vecAbsPowMinusTwo)

/-- **Bare-function regularised MFG solution.**

A point `(m, u, Du) : (Fin d → ℝ) → ℝ × … × Fin d → … → ℝ` together with
the integrability/non-negativity certificates needed by downstream
consumers (T7's apriori-bound ingestion):

* `hmLp`, `huLp`, `hDuLp` — `MemLpPer` of each component at the
  appropriate Banach exponent.
* `hWeakDeriv` — the per-coordinate weak-derivative tie between `u`
  and `Du`. Together with `huLp`/`hDuLp` this delivers
  `MemSobolevPer γBar u` via `memSobolevPer_of_sobolevPerLp` / direct
  `MemSobolevPer.mk`.
* `hmNonneg` — `0 ≤ m` a.e. on the unit cube (i.e. `m ∈ K0_Aepsi`).
* `hInt` — the standard `MFGOpEpsAuxHyps` integrability bundle for
  `(Du, m, u)` against `(γBar, βBar)`-Hölder data.

Per the v3 expert plan post-T6 audit (two-domain redesign),
the universal-form `hVIeps` field has been **replaced** by three
per-family fields `hVIeps_set`, `hVIeps_signed`, `hVIeps_transport`,
matching the three regularised paper-family VIs that downstream
limit-passage consumers (the AC3-bare-test-triple translation path)
actually require:

* `hVIeps_set` — for every measurable subset `S ⊆ UnitCube d` and
  every nonneg test density `ρ` (a.e.), the inequality on the
  indicator-driven `mfgOperatorEpsPair`. The test family is
  `(μ_S, υ, Dυ)` where `μ_S := ρ · 𝟙_S` is the indicator-modulated
  density.
* `hVIeps_signed` — for every signed pair `(σ_+, σ_-)` of nonneg
  densities and every measurable subset `S`. The test family is
  `(σ_+ - σ_-, υ, Dυ)` paired against `S`.
* `hVIeps_transport` — for every nonneg density `σ` and every test
  gradient field `φ : Fin d → ((Fin d → ℝ) → ℝ)`. The test family
  is `(σ, υ, φ)` (the gradient slot is the user-chosen `φ`).

Together these three families exhaust the test-triple universe
required by the AC3-bare-test-triple translation, replacing the
contradictory universal-Banach shape that the K0-form weak VI
could not deliver. -/
structure RegularizedBareSolution
    (d : ℕ) (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ) where
  /-- The mass-distribution component. -/
  m : (Fin d → ℝ) → ℝ
  /-- The value-function component. -/
  u : (Fin d → ℝ) → ℝ
  /-- The gradient-component family. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `m ∈ Lᵝ_per` on the unit cube. -/
  hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) m
  /-- `u ∈ Lᵞ_per` on the unit cube. -/
  huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) u
  /-- Each gradient component is in `Lᵞ_per`. -/
  hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du i)
  /-- `Du i` is the `i`-th periodic weak derivative of `u`. -/
  hWeakDeriv : ∀ i, HasWeakDerivPer (d := d) i u (Du i)
  /-- `u` admits an a.e.-periodic representative.

  **Phase 2a (`infra-P5-T10-v7-phase2a-RegularizedBareSolution-periodicity-fields`,
  iter 2 — `AEPeriodic`-typed):** the bare-function representative
  `u : (Fin d → ℝ) → ℝ` is the `Lp.coeFn` of `q.2.1 : LpPer γ d`, which
  agrees a.e. on the unit cube with the periodic function constructed
  by `Periodic.bareCoeFnOfLpPer` (precomposition with `Int.fract`).
  This field carries that a.e.-periodic representative — strictly
  weaker than pointwise `IsPeriodic` (which would require the chosen
  measurable representative to be invariant on the nose), but
  sufficient for all consumers that already work modulo a.e. equality.
  The producer `exists_regularizedBareSolution_K` constructs this
  field in-body via `Periodic.bareCoeFnOfLpPer` — no auth parameter
  needed. -/
  hu_per : StationaryMFG.Periodic.AEPeriodic u
  /-- Each gradient component `Du i` admits an a.e.-periodic
  representative.

  **Phase 2a (iter 2):** parallel to `hu_per`. Each gradient component
  `Du i = ⇑(q.2.2 i) : (Fin d → ℝ) → ℝ` is the `Lp.coeFn` of the
  corresponding `Lp` factor, hence has an a.e.-periodic representative
  via `Periodic.bareCoeFnOfLpPer`. The `AEPeriodic`-shape (versus
  pointwise `IsPeriodic`) is what makes this constructible without an
  authorisation parameter on `exists_regularizedBareSolution_K`. -/
  hDu_per : ∀ i, StationaryMFG.Periodic.AEPeriodic (Du i)
  /-- `m ≥ 0` a.e. on the unit cube. -/
  hmNonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                0 ≤ m x
  /-- The integrability bundle for the `mfgOperatorEpsPair` pairing
  at `(Du, m, u)`. -/
  hInt : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u
  /-- **Set-family regularised VI.** For every measurable subset
  `S ⊆ UnitCube d` and every nonneg test density `ρ` together with
  test value-function `υ` and gradient family `Dυ` (with their
  `MemLpPer` / `MemSobolevPer` Banach-embedding certificates), the
  `mfgOperatorEpsPair` pairing of `(Du, m, u)` against the
  indicator-modulated test triple is non-negative.

  The MemLp/MemSobolev parameters match the K_Aepsi-form helper
  `hVIeps_set_of_KAepsi_VI`'s test-triple Banach-embedding inputs
  byte-for-byte, so the field can be populated by a single invocation
  of the helper. -/
  hVIeps_set :
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
    ∀ (ρ υ : (Fin d → ℝ) → ℝ)
      (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ (S.indicator ρ) υ
              (fun i x => Dυ i x - Du i x)
              (S.indicator ρ - m) (υ - u)
  /-- **Signed-family regularised VI** — paper-exact shape per
  `StrongVI_setForm_signed` (`StrongIsStrong.lean:309`). For every
  sign `σ ∈ {+1, -1}` and every measurable subset `S ⊆ UnitCube d`
  of finite restricted-cube measure, the `mfgOperatorEpsPair`
  pairing on the test triple
  `(η, ν, Dν) = (σ · m · 1_S, 0, 0)` (so probe = test point
  `(Du, m + σ · m · 1_S, u)`, direction = test triple) is
  non-negative.

  Admissibility of the perturbed density `m + σ · m · 1_S ≥ 0`
  follows from `m ≥ 0` a.e. and `σ ∈ {±1}` (forces `σ ≥ -1`); no
  separate hypothesis is needed in the field. -/
  hVIeps_signed :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Du
              (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))
  /-- **Signed-family regularised VI — user-probe variant.** Same
  family parameters as `hVIeps_signed` (sign `σ ∈ {±1}` and
  measurable finite-measure subset `S`), but with a user-supplied
  probe `(Dυ, υ)` in the dual-primal/value-function slot. The
  primal density still perturbs to `m + σ · m · 1_S`; the test
  triple in `mfgOperatorEpsPair` is `(Dυ - Du, σ · m · 1_S, υ - u)`,
  i.e. the difference between the user probe and the actual
  `(sol k)` projections, with the density direction fixed at the
  signed perturbation `σ · m · 1_S`.

  This is the user-probe analogue of `hVIeps_signed`:
  whereas `hVIeps_signed` hardcodes the probe to
  `(Du, m + σ · m · 1_S, u)` (so the dual/value direction is `0`),
  the user-probe form lets the consumer specialise the probe to
  any `(Dυ, υ)` carrying the appropriate Banach-embedding
  certificates. Discharged from the K_Aepsi-form weak VI by the
  perturbation `μ_n := m + σ · m · 1_S + 1/(n+1)` and the same
  Minty/δ-limit argument as `hVIeps_signed_of_KAepsi_VI`. -/
  hVIeps_signed_user_probe :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
    ∀ (υ : (Fin d → ℝ) → ℝ)
      (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ
              (fun i x => Dυ i x - Du i x)
              (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun x => υ x - u x)
  /-- **Signed-family regularised VI — user-triple variant.** Same
  family parameters as `hVIeps_signed_user_probe` (sign `σ ∈ {±1}` and
  measurable finite-measure subset `S`), but with **user-supplied
  primal density `μ`** (carrying a nonnegativity certificate) in
  addition to the user-supplied probe `(Dυ, υ)`. The primal density
  is `μ + σ · μ · 1_S` (replacing the iter-358 hardcoded
  `(sol k).m + σ · (sol k).m · 1_S`); the test triple in
  `mfgOperatorEpsPair` is
  `(Dυ - Du, (μ + σ · μ · 1_S) - m, υ - u)`, i.e. the difference
  between the user probe/density and the actual `(sol k)`
  projections, with the density direction at the signed-perturbed
  user density minus the bare `m`.

  This is the most general user-probe form: whereas
  `hVIeps_signed_user_probe` hardcodes the primal slot to
  `m + σ · m · 1_S` (so the density direction is `σ · m · 1_S`),
  this user-triple form lets the consumer pin the primal density to
  any nonneg `μ` carrying its own admissibility cert. The
  strict-positive perturbation `μ + σ · μ · 1_S + 1/(n+1) > 0`
  follows pointwise from `μ ≥ 0` (user cert) and `σ · 1_S ≥ -1`
  (true since `σ ∈ {±1}` and `0 ≤ 1_S ≤ 1`); the same δ-limit /
  Minty argument as `hVIeps_signed_of_KAepsi_VI` then applies, with
  `μ` in place of `mOf q` throughout the perturbation.

  *Pattern:* mirrors the iter-358 `hVIeps_signed_user_probe`
  constructor pattern but threads a user-supplied density `μ` (with
  `h_mu_nonneg`) instead of hardcoding `(sol k).m`. -/
  hVIeps_signed_user_triple :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
    ∀ (μ υ : (Fin d → ℝ) → ℝ)
      (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ
              (fun i x => Dυ i x - Du i x)
              (fun x => (μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                        - m x)
              (fun x => υ x - u x)
  /-- **Transport-family regularised VI.** For every nonneg test
  density `σ` and every test gradient field `φ` (with associated
  test value-function `υ`, all carrying their `MemLpPer` /
  `MemSobolevPer` Banach-embedding certificates), the
  `mfgOperatorEpsPair` pairing of `(Du, m, u)` against the test
  triple `(φ, σ, υ)` is non-negative.

  The MemLp/MemSobolev parameters match the K_Aepsi-form helper
  `hVIeps_transport_of_KAepsi_VI`'s test-triple Banach-embedding
  inputs byte-for-byte, so the field can be populated by a single
  invocation of the helper. -/
  hVIeps_transport :
    ∀ (σ υ : (Fin d → ℝ) → ℝ)
      (φ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (φ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ σ υ
              (fun i x => φ i x - Du i x)
              (σ - m) (υ - u)

namespace RegularizedBareSolution

variable {d : ℕ} {ε : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}

/-- The bundled `MemSobolevPer γBar u` derived from `huLp` and
`hWeakDeriv` (the weak-derivative certificate is what
`MemSobolevPer` requires in addition to `MemLpPer`). -/
lemma memSobolevPer_u
    (sol : RegularizedBareSolution d ε V H DpH γBarReal βBarReal
            βBarReal' γBarReal') :
    MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) sol.u :=
  ⟨sol.huLp, ⟨sol.Du, sol.hWeakDeriv⟩⟩

end RegularizedBareSolution

/-! ## Phase 1 v3 — `RegularizedPaperSolutionData`

Type-level scaffolding for the Theorem-1 closed chain (Phase 2 endgame).

`RegularizedPaperSolutionData` enriches a `RegularizedBareSolution`
with three paper-side identities/inequalities (HJ0 equality, paper-line-
1212 transport identity, Lagrangian/Legendre lower bound) that the
existing bare-record API cannot deliver from `(hpow, hVIeps_*)` alone
(per the iter-430 audit). The constructor
`RegularizedPaperSolutionData.of_paperHypotheses` realises paper §3,
§4, and `thm:strongAepsi`; it is multi-week mathematical work and is
**not** defined in this task.

This task lands the type-level surface only: the structure plus
trivial projection lemmas in `AprioriUniform.lean` that downstream
consumers (specifically `AprioriUniformPerSolHypotheses.fromCAnd
Authorised`) use to source `hLagrRaw` and `hIdentityRaw`. -/

/-- **Phase 1 v3 — paper-enriched regularised solution data.**

Bundles a `RegularizedBareSolution` with the three paper-side
identities/inequalities that the bare-record API cannot deliver from
`(hpow, hVIeps_*)` alone (per the iter-430 audit):

* `hHJ0` — paper HJ0 equality: `∫ m · (u + H − V) = 0` (the
  orthogonality between the regularised HJB residual and `m`).
* `hTransport_identity` — paper line 1212: integral of `u` equals
  integral of `m · (−H + DpH · Du) + V · m + ε · |Du|^γ̄ +
  ε · |u|^γ̄`.
* `h_lagr` — paper §3 Legendre/convex-at-zero lower bound:
  `m^β / C − C ≤ DpH · p − H` whenever `m > 0`.

The fields use the same `⬝` (dot product) and integration-on-the-cube
shapes that `AprioriUniformPerSolHypotheses` consumes downstream, so
the Phase 1 projection lemmas in `AprioriUniform.lean` are direct.

The constructor `of_paperHypotheses` (Phase 2) is intentionally
unimplemented in this task. -/
structure RegularizedPaperSolutionData
    (ε : ℝ) (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) where
  /-- The base `RegularizedBareSolution`. -/
  sol : RegularizedBareSolution d ε V H DpH
          γBarReal βBarReal βBarReal' γBarReal'
  /-- Paper HJ0 equality: `∫ m · (u + H − V) = 0`. -/
  hHJ0 :
    ∫ x in UnitCube d,
        sol.m x * (sol.u x +
            H x (fun i => sol.Du i x) (sol.m x) - V x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = 0
  /-- Paper line-1212 transport identity (the conclusion the iter-430
  audit identified as out of reach from `hVIeps_transport` alone). -/
  hTransport_identity :
    ∫ x in UnitCube d, sol.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      =
      ∫ x in UnitCube d,
          (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                    + (DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + V x * sol.m x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Lagrangian/Legendre lower bound (paper §3 convex-at-zero). -/
  h_lagr :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ hpow.β) / hpow.C - hpow.C ≤
          (DpH x p mx) ⬝ p - H x p mx

/-! ## Legacy K0-form `AepsiUniformContext` chain — DELETED

The K0-form record `AepsiUniformContext`, its Browder–Minty
producer `exists_banachVI_at_eps`, and the bare-bridging producer
`exists_regularizedBareSolution` were deleted by
`infra-P4-delete-AepsiUniformContext-K0-form`. They threaded through
the contradictory K0-form abstract-operator lifts in
`Banach/AbstractLifts.lean`, which asked for an unprovable
`hPos`-on-`K0_Aepsi` strict-positivity residue. The canonical
replacement is the K_Aepsi-form chain (`AepsiUniformContextK`,
`exists_banachVI_at_eps_KAepsi`, `exists_regularizedBareSolution_K`)
defined below; it isolates the strict-positivity requirement to the
abstract-VI machinery on `K_Aepsi` and descends the witness to
`K0_Aepsi` via `K_Aepsi_closure_subset_K0_Aepsi`. -/

/-! ## Two-domain redesign — K_Aepsi-form abstract-VI context

Per the v3 expert plan post-T6 audit (`infra-P4-two-domain-redesign`,
child A): the abstract-VI machinery genuinely requires strict
positivity from the elements it inspects (the
`aepsi_isMonotone_integrated` family is consumed pointwise on
`K_Aepsi`, where `0 < ⇑v.1` is needed for the paper's `eq:hpos`
hypotheses). The "K0-form lifts" `*_K0` in
`Banach/AbstractLifts.lean` consume a per-K0 strict-positivity
certificate `hPos : ∀ v ∈ K0_Aepsi, 0 < ⇑v.1 a.e.` that *cannot* be
discharged from K0-membership alone — strict positivity is strictly
stronger than `0 ≤ᵐ ⇑v.1`. That residue is the architectural bug
identified at `Banach/AbstractLifts.lean:1138`.

The two-domain redesign isolates the strict-positivity requirement
to the **internal** abstract-VI machinery: the new
`AepsiUniformContextK` carries `IsMonotone`, `IsHemicontinuous`, and
`IsCoerciveAt` certificates **on `K_Aepsi`** (where strict
positivity is part of the domain itself). The Browder–Minty witness
is then descended to `K0_Aepsi` via the closure inclusion
`K_Aepsi_closure_subset_K0_Aepsi`. The public-target K0-membership
of the witness is preserved; the contradictory K0-form `hPos`
residue is eliminated entirely.

This subsection provides:

* `AepsiUniformContextK` — the K_Aepsi-form context record.
* `exists_banachVI_at_eps_KAepsi` — the K_Aepsi-form Browder–Minty
  producer that lands its witness in `K0_Aepsi`.
* a sanity-check `example` exercising the new shape.

The replacement of `RegularizedBareSolution.hVIeps` with the three
per-family fields `hVIeps_set`, `hVIeps_signed`, `hVIeps_transport`,
together with the three Minty/δ-limit theorems
(`hVIeps_*_of_KAepsi_VI`) whose statements consume the K_Aepsi-form
abstract VI delivered here, are children B/C/D of the redesign,
filed as separate backlog tasks. The deletion of the contradictory
K0-form lifts and `aepsiUniformContext_of_paperHypotheses_closed`
chain is child E. -/

/-- **K_Aepsi-form uniform aux context.**

Parallel to `AepsiUniformContext`, but with the abstract-operator
predicates `hMono`, `hHC`, `hCoerc` stated on the strict-positivity
cone `K_Aepsi` (rather than the contradictory `K0_Aepsi`-form they
took before the two-domain redesign).

Fields:

* `hReflexive` — Phase 1 reflexivity of the Banach pair (unchanged).
* `auxHyps` — universal per-triple `MFGOpEpsAuxHyps` supplier
  (unchanged; the operator family `Aepsi_CLM_op` evaluates the CLM
  at every Banach point).
* `qRef`, `hqRef` — Browder–Minty base point in `K_Aepsi`.
* `aux` — uniform integrability bundle on `K0_Aepsi` (kept in
  K0-form because the bare-function producer downstream needs it
  at the K0-witness, not at the strict-positive interior).
* `hMono`, `hHC`, `hCoerc` — abstract-operator predicates on
  `K_Aepsi`. Discharged from `isMonotone_Aepsi_CLM`,
  `isHemicontinuous_Aepsi_CLM`, `isCoerciveAt_Aepsi_CLM`
  (the K_Aepsi-form lifts in `Banach/AbstractLifts.lean`, which
  consume strict positivity *as part of the domain* and so do not
  carry the contradictory `hPos`-on-K0 residue).
* `hWeakDeriv` — weak-derivative tie on K0 elements (unchanged;
  see AC amendment 3 in the original task). -/
structure AepsiUniformContextK
    (d : ℕ) (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] : Type where
  /-- Reflexivity of the Banach pair (Phase 1). -/
  hReflexive : IsReflexiveNormedSpace (XBanach d βBarReal γBarReal)
  /-- **K_Aepsi-indexed aux supplier** for the totalized CLM family
  `Aepsi_CLM_opK`. Per `infra-P4-domain-indexed-Aepsi-CLM` (the
  domain-indexed redesign): the universal supplier
  `∀ Du m u, MFGOpEpsAuxHyps …` is structurally false (strict positivity
  cannot be asserted for arbitrary `m`). The K_Aepsi-indexed shape
  matches `auxHyps_of_paperHypotheses_on_KAepsi` (iter 230). -/
  auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
              MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1)
  /-- The Browder–Minty base point. -/
  qRef : XBanach d βBarReal γBarReal
  /-- The base point lies in `K_Aepsi` (the strict-positivity cone). -/
  hqRef : qRef ∈ K_Aepsi d βBarReal γBarReal
  /-- The K0-restricted uniform aux record (T3). The bare-function
  producer downstream consumes the integrability bundle at the K0
  witness (`q ∈ K0_Aepsi` after the closure descent), not at the
  K_Aepsi witness. -/
  aux : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal
            βBarReal' γBarReal' (K0_Aepsi d βBarReal γBarReal)
  /-- Monotonicity of `Aepsi_CLM_opK auxHypsK ε` on `K_Aepsi`. -/
  hMono : IsMonotone (X := XBanach d βBarReal γBarReal)
            (K_Aepsi d βBarReal γBarReal)
            (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHypsK ε)
  /-- Hemicontinuity of `Aepsi_CLM_opK auxHypsK ε` on `K_Aepsi`. -/
  hHC : IsHemicontinuous (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V H DpH auxHypsK ε)
  /-- Coercivity of `Aepsi_CLM_opK auxHypsK ε` at `qRef` on `K_Aepsi`. -/
  hCoerc : IsCoerciveAt (X := XBanach d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHypsK ε)
              qRef
  /-- Per AC amendment 3: every K0 element's gradient component is
  the periodic weak derivative of its value component. -/
  hWeakDeriv :
    ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)

/-- **K_Aepsi-form Browder–Minty producer.**

Apply `monotone_abstract_weak` to `Aepsi_CLM_op auxHyps ε` on
**`K_Aepsi`** (convex by `K_Aepsi_convex` in
`Banach/AbstractLifts.lean`), and descend the witness from
`closure K_Aepsi` into `K0_Aepsi` via
`K_Aepsi_closure_subset_K0_Aepsi`.

The conclusion exposes:

* `q ∈ K0_Aepsi` — the public-target nonneg-cone membership.
* For every test point `q' ∈ K_Aepsi`, the weak-VI inequality
  `0 ≤ Aepsi_CLM_op auxHyps ε q' (q' - q)`.

The K_Aepsi-quantification of the test side is *intentional*: the
strong-VI form (`A` evaluated at the witness) is delivered by the
abstract Minty trick in `Banach/Closure.lean`
(`existsStrongVI_at_eps`); meanwhile, the three regularised
paper-family VIs (`hVIeps_set`, `hVIeps_signed`,
`hVIeps_transport`) are obtained from the K_Aepsi-form weak VI by
strict-positive perturbation `μ_n := μ + 1/n` of the paper's test
families (the Minty/δ-limit lemmas `hVIeps_*_of_KAepsi_VI` filed
as children C/D of the redesign).

Compare this to the legacy K0-form `exists_banachVI_at_eps`, which
runs Browder–Minty on `K0_Aepsi`; that path is structurally broken
because the paper's `aepsi_isMonotone_integrated` family genuinely
requires strict positivity, so the K0-form `hMono` cannot be
discharged without an unprovable `hPos`-on-K0 residue. -/
theorem exists_banachVI_at_eps_KAepsi
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (_hε : 0 < ε)
    (ctx : AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal') :
    ∃ q ∈ K0_Aepsi d βBarReal γBarReal,
      ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH ctx.auxHypsK ε q' (q' - q) := by
  -- Apply Browder–Minty on `K_Aepsi` (convex by AbstractLifts).
  have h_cvx : Convex ℝ (K_Aepsi d βBarReal γBarReal) :=
    K_Aepsi_convex d βBarReal γBarReal
  obtain ⟨q, hq_closure, hVI⟩ :=
    Monotone.monotone_abstract_weak (X := XBanach d βBarReal γBarReal)
      ctx.hReflexive h_cvx ctx.hMono ctx.hCoerc
  -- Descend `closure K_Aepsi ⊆ K0_Aepsi` via the two-domain bridge.
  have hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal :=
    K_Aepsi_closure_subset_K0_Aepsi d βBarReal γBarReal hq_closure
  exact ⟨q, hq_K0, hVI⟩

/-- **Sanity-check `example`.** The K_Aepsi-form producer
`exists_banachVI_at_eps_KAepsi` accepts an `AepsiUniformContextK`
and delivers a K0-membership witness together with the K_Aepsi-form
weak-VI inequality. This exercises the two-domain shape end-to-end:
abstract-VI machinery internal to `K_Aepsi`, public conclusion in
`K0_Aepsi`. -/
example
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hε : 0 < ε)
    (ctx : AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal') :
    ∃ q ∈ K0_Aepsi d βBarReal γBarReal,
      ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH ctx.auxHypsK ε q' (q' - q) :=
  exists_banachVI_at_eps_KAepsi hε ctx

/-! ## Producer: `exists_regularizedBareSolution_K`

Take the conclusion of `exists_banachVI_at_eps_KAepsi`, project the
witness `q ∈ K0_Aepsi` (descended from `closure K_Aepsi` via
`K_Aepsi_closure_subset_K0_Aepsi`) to its bare-function triple
`(DuOf q, mOf q, uOf q)`, and assemble a `RegularizedBareSolution`
record. The translation from the abstract-VI form
`0 ≤ Aepsi_CLM_opK auxHypsK ε q' (q' - q)` (for `q' ∈ K_Aepsi`) to
the bare-function form is delegated to the three per-family
Minty/δ-limit conclusions, taken as authorised inputs per
CONVENTIONS §8 (filed: children C/D of the two-domain redesign). -/

/-! ### Authorised inputs (per CONVENTIONS §8): the three Minty/δ-limit
schema

The K_Aepsi-form weak VI delivered by
`exists_banachVI_at_eps_KAepsi` is the input of three per-family
Minty/δ-limit theorems (`hVIeps_*_of_KAepsi_VI`). Those theorems
each take the abstract-VI inequality on the strict-positive cone
`K_Aepsi` and, by strict-positive perturbation `μ_n := μ + 1/n`,
produce the regularised paper-family VI shape required by
downstream limit-passage consumers. They are taken as authorised
input hypotheses of the producer below per CONVENTIONS §8. -/

/-- **T4 bare-bridging producer (K_Aepsi-form input, two-domain redesign).**

Consumes `AepsiUniformContextK` (the strict-positive-form context
from child A of the two-domain redesign) and applies
`exists_banachVI_at_eps_KAepsi` to extract a witness with
K0-membership; the three regularised paper-family VIs are fed by
the authorised Minty/δ-limit inputs of children C/D.

This is the canonical bare-bridging producer; the legacy K0-form
counterpart `exists_regularizedBareSolution` was deleted by
`infra-P4-delete-AepsiUniformContext-K0-form`. -/
theorem exists_regularizedBareSolution_K
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hε : 0 < ε)
    (ctx : AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    -- Authorised input: per-family Minty/δ-limit conclusions, indexed
    -- at the *specific witness* `q` extracted internally by
    -- Browder–Minty (per
    -- `infra-P4-rebuild-T7-AC1-refactor-bareSolution-K-witness-specific`).
    -- The previous shape universally-quantified over `(m, u, Du)`,
    -- which created a structural mismatch with the closed-form
    -- producers `hVIeps_*_of_KAepsi_VI` (whose conclusion is at the
    -- specific `(mOf q, uOf q, DuOf q)`). The refactored shape takes
    -- each Minty input as a function of `(q, hq_K0, hVI)`.
    (hMinty_set :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  Dυ (S.indicator ρ) υ
                  (fun i x => Dυ i x - DuOf q i x)
                  (S.indicator ρ - mOf q) (υ - uOf q))
    (hMinty_signed :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  (DuOf q)
                  (fun x => mOf q x + σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (uOf q)
                  (fun _ _ => (0 : ℝ))
                  (fun x => σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun _ => (0 : ℝ)))
    (hMinty_transport :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (φ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  φ σ υ
                  (fun i x => φ i x - DuOf q i x)
                  (σ - mOf q) (υ - uOf q))
    -- Authorised input: signed-family **user-probe** Minty/δ-limit
    -- conclusion at the specific witness `q`. Mirror of
    -- `hMinty_signed`, but with user-supplied `(Dυ, υ)` probe.
    (hMinty_signed_user_probe :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  Dυ
                  (fun x => mOf q x + σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  υ
                  (fun i x => Dυ i x - DuOf q i x)
                  (fun x => σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun x => υ x - uOf q x))
    -- Authorised input: signed-family **user-triple** Minty/δ-limit
    -- conclusion at the specific witness `q`. Mirror of
    -- `hMinty_signed_user_probe`, but with **user-supplied** primal
    -- density `μ` (with nonnegativity cert and Lp embedding), in
    -- addition to the user-supplied `(Dυ, υ)` probe.
    (hMinty_signed_user_triple :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
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
                  (fun x => υ x - uOf q x))
    :
    -- **Phase 2a (iter 2 — `AEPeriodic`-typed; no auth parameter).**
    -- The new `RegularizedBareSolution.{hu_per, hDu_per}` fields are
    -- typed as `Periodic.AEPeriodic`, which is constructible from
    -- `Periodic.bareCoeFnOfLpPer` for any `Lp`-coercion bare function.
    -- No authorised periodicity parameter is needed.
    Nonempty (RegularizedBareSolution d ε V H DpH γBarReal βBarReal
                βBarReal' γBarReal') := by
  -- Extract the K_Aepsi-form abstract-VI witness; the witness lands
  -- in `K0_Aepsi` via the closure inclusion
  -- `K_Aepsi_closure_subset_K0_Aepsi` already discharged inside
  -- `exists_banachVI_at_eps_KAepsi`.
  obtain ⟨q, hq_K0, hVI⟩ := exists_banachVI_at_eps_KAepsi hε ctx
  -- Bare-function projections.
  set m : (Fin d → ℝ) → ℝ := mOf q with hm_def
  set u : (Fin d → ℝ) → ℝ := uOf q with hu_def
  set Du : Fin d → (Fin d → ℝ) → ℝ := DuOf q with hDu_def
  -- `MemLpPer` certificates from the Lp components of `q`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) m :=
    memLpPer_of_lpPer (d := d) q.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) u :=
    memLpPer_of_lpPer (d := d) q.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du i) := by
    intro i
    exact memLpPer_of_lpPer (d := d) (q.2.2 i)
  -- Weak-derivative certificate from `ctx.hWeakDeriv` (per-K0 tie).
  have hWeakDeriv : ∀ i, HasWeakDerivPer (d := d) i u (Du i) :=
    ctx.hWeakDeriv q hq_K0
  -- **Phase 2a (iter 2) AE-periodicity certificates**, derived in-body
  -- via `Periodic.bareCoeFnOfLpPer` from the underlying `Lp` factors of
  -- `q : XBanach d β γ`. No auth parameter needed: the construction is
  -- purely structural (precomposition with `Int.fract`).
  have hu_per : StationaryMFG.Periodic.AEPeriodic u :=
    -- `u = uOf q = ⇑q.2.1` where `q.2.1 : Lp ℝ γ (volume.restrict (UnitCube d))`.
    ⟨StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) q.2.1⟩
  have hDu_per : ∀ i, StationaryMFG.Periodic.AEPeriodic (Du i) := fun i =>
    -- Same construction for each gradient factor.
    ⟨StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (q.2.2 i)⟩
  -- Non-negativity from K0 membership.
  have hmNonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                    0 ≤ m x := hq_K0
  -- Integrability bundle from `ctx.aux.of_mem` (still K0-restricted).
  have hInt : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                V H DpH Du m u :=
    ctx.aux.of_mem q hq_K0
  -- Assemble using the three authorised Minty/δ-limit inputs at the
  -- specific witness `(q, hq_K0, hVI)`.
  exact ⟨{
    m := m
    u := u
    Du := Du
    hmLp := hmLp
    huLp := huLp
    hDuLp := hDuLp
    hWeakDeriv := hWeakDeriv
    hu_per := hu_per
    hDu_per := hDu_per
    hmNonneg := hmNonneg
    hInt := hInt
    hVIeps_set := hMinty_set q hq_K0 hVI
    hVIeps_signed := hMinty_signed q hq_K0 hVI
    hVIeps_signed_user_probe := hMinty_signed_user_probe q hq_K0 hVI
    hVIeps_signed_user_triple := hMinty_signed_user_triple q hq_K0 hVI
    hVIeps_transport := hMinty_transport q hq_K0 hVI
  }⟩

/-! ## T5 — Canonical base point `qRef_simplePower`

Per the rebuild plan T5, downstream Browder–Minty applications need a
canonical base point in `K0_Aepsi`, both as the `IsCoerciveAt` reference
point (T6) and as the existence-of-some-point witness needed by
`monotone_abstract_weak`. The simplest such choice is the bare-function
triple `(m, u, Du) = (1, 0, 0)` lifted to the Banach pair via
`MemLp.toLp` on the constant `1` for the `m`-factor and the zero element
of `Lp` for the `u` and gradient factors.

The membership lemma `qRef_simplePower_mem_K0` reduces to `0 ≤ 1` a.e.
via `MemLp.coeFn_toLp` (the `Lp` coercion of the bridged constant agrees
a.e. with the constant). -/

/-- **Canonical base point** of the Banach domain
`XBanach d βBarReal γBarReal`. Built as the bridged pair
`(m, u, Du) = (1, 0, 0)`:

* `m`-factor: `MemLp.toLp (fun _ => 1)` (using `IsFiniteMeasure` of
  the unit-cube measure to invoke `memLp_const`).
* `u`-factor: the zero element of `Lp`.
* gradient factor: the zero element of `Lp` in each coordinate.

Used as the `qRef` field of `AepsiUniformContext` (T6) and as the
reference point for `IsCoerciveAt` therein. -/
noncomputable def qRef_simplePower
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    XBanach d βBarReal γBarReal :=
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict
        (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  ((MeasureTheory.memLp_const (μ := MeasureTheory.Measure.restrict
        (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d))
      (p := ENNReal.ofReal βBarReal) (1 : ℝ)).toLp
      (fun _ => (1 : ℝ)),
    (0 : Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))

/-- The `m`-factor of `qRef_simplePower` is a.e. equal to the constant
`1` on the unit cube. -/
lemma qRef_simplePower_mOf_ae
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    mOf (qRef_simplePower d βBarReal γBarReal)
      =ᵐ[MeasureTheory.Measure.restrict
            (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)]
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict
        (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  -- `mOf qRef = ⇑((memLp_const 1).toLp _)`, which is `=ᵐ` to `fun _ => 1`.
  have hmem : MeasureTheory.MemLp (fun _ : (Fin d → ℝ) => (1 : ℝ))
                (ENNReal.ofReal βBarReal)
                (MeasureTheory.Measure.restrict
                  (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)) :=
    MeasureTheory.memLp_const (1 : ℝ)
  exact MeasureTheory.MemLp.coeFn_toLp hmem

/-- The `u`-factor of `qRef_simplePower` is a.e. equal to `0`. -/
lemma qRef_simplePower_uOf_ae
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    uOf (qRef_simplePower d βBarReal γBarReal)
      =ᵐ[MeasureTheory.Measure.restrict
            (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)]
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  -- `uOf qRef = ⇑(0 : Lp …)`, which agrees a.e. with the zero function.
  exact MeasureTheory.Lp.coeFn_zero _ _ _

/-- Each gradient component of `qRef_simplePower` is a.e. equal to `0`. -/
lemma qRef_simplePower_DuOf_ae
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (i : Fin d) :
    DuOf (qRef_simplePower d βBarReal γBarReal) i
      =ᵐ[MeasureTheory.Measure.restrict
            (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)]
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  -- `DuOf qRef i = ⇑(0 : Lp …)`, which agrees a.e. with the zero function.
  exact MeasureTheory.Lp.coeFn_zero _ _ _

/-- **`qRef_simplePower` lies in the closed nonneg cone `K0_Aepsi`.**

The `m`-factor of `qRef_simplePower` agrees a.e. with the constant `1`
on the unit cube, and `0 ≤ 1`. -/
theorem qRef_simplePower_mem_K0
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    qRef_simplePower d βBarReal γBarReal
      ∈ K0_Aepsi d βBarReal γBarReal := by
  -- Membership unfolds to `0 ≤ ⇑q.1 x` a.e.; since `⇑q.1 =ᵐ (fun _ => 1)`,
  -- this reduces to `0 ≤ 1`.
  have h_ae : mOf (qRef_simplePower d βBarReal γBarReal)
                =ᵐ[MeasureTheory.Measure.restrict
                      (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)]
                (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    qRef_simplePower_mOf_ae d βBarReal γBarReal
  -- `mOf q x = ⇑q.1 x` definitionally.
  change ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)),
    0 ≤ mOf (qRef_simplePower d βBarReal γBarReal) x
  refine h_ae.mono ?_
  intro x hx
  -- `hx : mOf qRef x = 1`; conclude `0 ≤ mOf qRef x`.
  rw [hx]
  exact zero_le_one

/-! ## Sanity-check `example`s -/

/-- Sanity check: the `RegularizedBareSolution` projections type-check
on a trivial existential extraction. -/
example
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH γBarReal βBarReal
            βBarReal' γBarReal') :
    MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) sol.u :=
  sol.memSobolevPer_u

/-- Sanity check: `exists_regularizedBareSolution_K` type-checks (the
K_Aepsi-form producer of the two-domain redesign). The three Minty
inputs are taken at the *specific witness* `q` extracted internally
(per `infra-P4-rebuild-T7-AC1-refactor-bareSolution-K-witness-specific`). -/
example
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hε : 0 < ε)
    (ctx : AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    (hMinty_set :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  Dυ (S.indicator ρ) υ
                  (fun i x => Dυ i x - DuOf q i x)
                  (S.indicator ρ - mOf q) (υ - uOf q))
    (hMinty_signed :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  (DuOf q)
                  (fun x => mOf q x + σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (uOf q)
                  (fun _ _ => (0 : ℝ))
                  (fun x => σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun _ => (0 : ℝ)))
    (hMinty_transport :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (φ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  φ σ υ
                  (fun i x => φ i x - DuOf q i x)
                  (σ - mOf q) (υ - uOf q))
    (hMinty_signed_user_probe :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  Dυ
                  (fun x => mOf q x + σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  υ
                  (fun i x => Dυ i x - DuOf q i x)
                  (fun x => σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun x => υ x - uOf q x))
    (hMinty_signed_user_triple :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
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
                  (fun x => υ x - uOf q x))
    :
    Nonempty (RegularizedBareSolution d ε V H DpH γBarReal βBarReal
                βBarReal' γBarReal') :=
  exists_regularizedBareSolution_K hε ctx hMinty_set hMinty_signed hMinty_transport
    hMinty_signed_user_probe hMinty_signed_user_triple

/-- Sanity check: the new field `hVIeps_signed_user_probe` on
`RegularizedBareSolution` accepts a user-supplied probe `(Dυ, υ)` and
delivers the signed-family VI shape. This example pins the field's
type signature, paralleling the existing `hVIeps_signed` and
`hVIeps_set` sanity checks. -/
example
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    (υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => sol.m x + σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ i x - sol.Du i x)
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ x - sol.u x) :=
  sol.hVIeps_signed_user_probe σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp hWeak_υ

/-- Sanity check: the new field `hVIeps_signed_user_triple` on
`RegularizedBareSolution` accepts a **user-supplied primal density `μ`**
(with nonnegativity / Lp certs) AND a user-supplied probe `(Dυ, υ)`,
delivering the signed-family VI shape with `μ` (rather than `sol.m`)
in the perturbation. This example pins the field's type signature,
mirroring the iter-358 `hVIeps_signed_user_probe` sanity check. -/
example
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => μ x + σ * μ x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ i x - sol.Du i x)
          (fun x => (μ x + σ * μ x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    - sol.m x)
          (fun x => υ x - sol.u x) :=
  sol.hVIeps_signed_user_triple σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp
    hυ_memSob hDυ_memLp hWeak_υ

/-- Sanity check (T5): `qRef_simplePower` lies in `K0_Aepsi`. -/
example
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    qRef_simplePower d βBarReal γBarReal
      ∈ K0_Aepsi d βBarReal γBarReal :=
  qRef_simplePower_mem_K0 d βBarReal γBarReal

/-! ## T6 — Paper-hypothesis-driven producers

Per the rebuild plan T6, this section assembles the headline producers
that thread the three paper hypotheses `(hmon, hpow, hV)` plus the
exponent facts `hExp` into the `MFGOpEpsUniformAux` (AC3) record.

The legacy K0-form AC1 producer `aepsiUniformContext_of_paperHypotheses`
(building the now-deleted `AepsiUniformContext`) was removed by
`infra-P4-delete-AepsiUniformContext-K0-form`; the canonical
replacement is `AepsiUniformContextK` (assembled by direct record
syntax from the `infra-P4-mfg-A-*` outputs in
`Banach/AbstractLifts.lean` for the K_Aepsi-form lifts).

### Status — AC amendment 2026-04-30 (CONVENTIONS §8 staging)

The remaining producer is parameterised over the **outputs** of the
upstream "missing-piece" workstreams of
`docs/TASKS/backlog/infra-P4-thin-chain-discharge.md`:

* AC3's `auxHyps : ∀ q ∈ K0_Aepsi, MFGOpEpsAuxHyps …` parameter
  abstracts over **missing piece 1** (the `(hpow, hV) → MFGOpEpsAuxHyps`
  integrability lift, target of `infra-P4-mfg-operator-clm`).

The paper hypotheses `(hmon, hpow, hV, hExp)` are kept in the
signature (as underscore-named bindings) for downstream schema
compatibility: once the missing pieces land, a closed-form producer
will derive the abstracted output from the paper hypotheses and apply
this producer internally. -/

/-- **AC3 producer.** Build the K0-restricted uniform aux record from
the paper hypotheses, given the upstream `auxHyps` supplier on K0.

The body is a one-line application of
`mfgOpEps_uniformAux_of_perPairAuxHyps`. The paper hypotheses
`(hmon, hpow, hV, hExp)` are accepted in the signature for downstream
schema compatibility — they are *not* used in the body, but will be
used by the closed-form variant once the `auxHyps` parameter becomes
derivable from `(hpow, hV)` (workstream `infra-P4-mfg-operator-clm`). -/
theorem mfgOpEps_uniformAux_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε : ℝ)
    (_hε : 0 < ε)
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (auxHyps : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (DuOf q) (mOf q) (uOf q)) :
    MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal'
      (K0_Aepsi d βBarReal γBarReal) :=
  mfgOpEps_uniformAux_of_perPairAuxHyps ε
    (K0_Aepsi d βBarReal γBarReal) auxHyps

/-! ### Sanity-check `example`s for T6 -/

/-- Sanity check (AC3): the AC3 producer assembles the K0-uniform aux
record from a per-q `auxHyps` supplier on K0. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε : ℝ)
    (hε : 0 < ε)
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (auxHyps : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (DuOf q) (mOf q) (uOf q)) :
    MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal'
      (K0_Aepsi d βBarReal γBarReal) :=
  mfgOpEps_uniformAux_of_paperHypotheses ε hε hmon hpow hV hExp auxHyps

/-! Note: the legacy K0-form `AepsiUniformContext` AC1 producer
`aepsiUniformContext_of_paperHypotheses` was deleted by
`infra-P4-delete-AepsiUniformContext-K0-form` together with the
K0-form context record itself. The canonical replacement is the
K_Aepsi-form `AepsiUniformContextK` (constructed by direct
record-syntax assembly from `infra-P4-mfg-A-*` outputs) consumed by
`exists_regularizedBareSolution_K`. -/

/-! ## T6 — Feeder 1 (universal per-triple `MFGOpEpsAuxHyps` supplier)

Per the v3 expert plan Step 12, T6 was originally a composition of
**four** feeder lemmas plus a weak-derivative tie. The two-domain
redesign child E (`infra-P4-two-domain-redesign-E-delete-K0-form-lifts`)
**deleted** the legacy K0-form feeders 2/3/4
(`Aepsi_mono_of_paperHypotheses`,
`Aepsi_hemicont_of_paperHypotheses`,
`Aepsi_coercive_of_paperHypotheses`) and the closed-form composition
theorem `aepsiUniformContext_of_paperHypotheses_closed` because they
chained through the contradictory K0-form lifts in
`Banach/AbstractLifts.lean` (which asked for an unprovable
`hPos`-on-`K0_Aepsi` strict-positivity residue).

The canonical replacement is the K_Aepsi-form chain:
* `AepsiUniformContextK` (this file, above) for the abstract-VI
  context on the strict-positive cone `K_Aepsi`,
* `exists_banachVI_at_eps_KAepsi` for Browder–Minty on `K_Aepsi`,
  with the witness descended into `K0_Aepsi` via
  `K_Aepsi_closure_subset_K0_Aepsi`,
* `exists_regularizedBareSolution_K` for the bare-bridging producer.

Feeder 1 (`auxHyps_of_paperHypotheses_at_triple` and the universal
pass-through `auxHyps_of_paperHypotheses`) and Feeder 5
(`aepsi_weakDerivTie_of_paperHypotheses`) are retained: they are the
shared infrastructure consumed by both the deleted K0-form chain and
the surviving K_Aepsi-form chain.

Filed follow-up backlog tasks for Feeder 1's residues:
- `infra-P4-mfg-operator-clm` — discharge `auxHyps`'s five MemLpPer
  dominator closures + per-triple integrability bundle.
- `infra-P4-weak-limit-pointwise-rep` — discharge the K0
  weak-derivative tie via `SobolevPerLp 1`-style coercion.

The K_Aepsi-form replacements for Feeders 2/3/4 are the canonical
lifts in `Banach/AbstractLifts.lean`
(`isMonotone_Aepsi_CLM`, `isHemicontinuous_Aepsi_CLM`,
`isCoerciveAt_Aepsi_CLM`) consumed directly by
`AepsiUniformContextK`. Their per-paper-hypothesis residues are
filed as `infra-P4-mfg-A-{monotone,hemicontinuous,coercive}` (the
same backlog tasks the deleted K0-form feeders were filed under;
those tasks now target the K_Aepsi-form lifts as their final
consumers). -/

/-- **Feeder 1 (per-triple, AC2-consuming form).** Build a single
`MFGOpEpsAuxHyps` certificate at a fixed primal triple `(Du, m, u)` by
*invoking* the three AC2 lemmas
`Hamiltonian.g_memLp_betaBar'_at_test`,
`Hamiltonian.flux_memLp_gammaBar'_at_test`,
`Hamiltonian.μMinusOne_memLp_of_betaBar` to discharge the
`hF_HJB`, `hF_flux`, `hF_mass` fields. The remaining fields (`hβ`,
`hγ`, `hβγ`, `hβTop`, `hG_grad`, `hG_val`) are threaded as parameters
because they are not derivable from `(hpow, hV)` alone:

* The Hölder-conjugacy facts (`hβ`, `hγ`, `hβγ`, `hβTop`) require a
  bridge from `hExp.βConj` (which lives on `(ENNReal.ofReal βBarReal).toReal`)
  to the raw real `βBarReal`. With `Fact (1 ≤ ENNReal.ofReal βBarReal)`,
  this is a small `ENNReal.toReal_ofReal` rewrite — but the exponent
  cleanup is filed as `infra-P4-eliminate-hExp-parameter`.
* The `G_grad`, `G_val` `MemLpPer` certificates are the true Hölder
  rpow-product dominator closures (filed:
  `infra-P4-ADFGU-test-triple-dominator-closure`); these are *not*
  derivable from `(hpow, hV)` either.

Per CONVENTIONS §8, the residual parameters are explicitly named with
their backlog-task source. The body's invocation of the three AC2
lemmas is the genuine partial discharge requested by the reviewer of
iteration 1.

The hypotheses consumed in the body:
* `hpow` (via `Hamiltonian.upper_bound_powergrowth` projecting through
  the `h_slice` parameter to obtain the upper bound used by AC2);
* the strict-positivity residue `hμ_pos` (paper's `essinf μ > 0`);
* the dominator-`MemLpPer` residues for the three F-side certificates;
* AC2's three lemmas in the body. -/
theorem auxHyps_of_paperHypotheses_at_triple
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ)
    -- Hölder pair residues (filed: `infra-P4-eliminate-hExp-parameter`).
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    -- Phase 0 routing fix (`infra-P5-theorem1-phase-0`):
    -- `γ̄' ≤ β̄` exponent inclusion for the `F_mass` discharge.
    -- This *does* follow from `α > 1, β > 0` via
    -- `Hamiltonian.gammaBar'_le_betaBar`; threaded as a residue so
    -- this feeder remains agnostic to the paper exponent shape.
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Strict positivity of `m` (paper `essinf μ > 0`, line 303 / 1330).
    (hμ_pos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < m x)
    -- `(C', h_upper)` from `Hamiltonian.upper_bound_powergrowth(hpow, …)`.
    -- Threaded as residues here because `upper_bound_powergrowth`'s
    -- own slice hypothesis is filed as
    -- `infra-P4-ADFGU-test-triple-dominator-closure`. Once that lands,
    -- the caller obtains `(C', hC'_pos, h_upper)` directly from
    -- `upper_bound_powergrowth(hpow, h_slice)` and passes them in.
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    -- Measurability witnesses for the three F-side functions.
    (hF_HJB_meas :
      AEStronglyMeasurable
        (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ i,
        AEStronglyMeasurable
          (fun x => m x * DpH x (fun j => Du j x) (m x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Dominator `MemLpPer` certificates for the three F-side functions
    -- (filed: `infra-P4-ADFGU-test-triple-dominator-closure`).
    (hG_HJB_dom :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun i => Du i x‖ ^ hpow.α + 1)
            + hpow.C * (m x ^ hpow.β + 1)
            + |u x| + |V x|))
    (hG_flux_dom :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (m x * ‖fun j => Du j x‖ ^ (hpow.α - 1)
                      + m x ^ (1 + hpow.β - hpow.β / hpow.α) + m x)))
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) m)
    -- G-side certificates (filed: `infra-P4-ADFGU-test-triple-dominator-closure`).
    (hG_grad_mem :
      ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (G_grad γBarReal Du i))
    (hG_val_mem :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal u)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH Du m u := by
  -- AC2 invocation 1: discharge `hF_HJB` via
  -- `Hamiltonian.g_memLp_betaBar'_at_test` with the threaded
  -- `(C', hC'_pos, h_upper)` (which the caller obtains from
  -- `Hamiltonian.upper_bound_powergrowth(hpow, h_slice)`).
  have hF_HJB :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x) :=
    Hamiltonian.g_memLp_betaBar'_at_test (d := d) hpow
      (q := ENNReal.ofReal βBarReal') V u m Du
      hμ_pos hC'_pos h_upper hF_HJB_meas hG_HJB_dom
  -- AC2 invocation 2: discharge `hF_flux i` via
  -- `Hamiltonian.flux_memLp_gammaBar'_at_test` for each `i`.
  have hF_flux : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => m x * DpH x (fun j => Du j x) (m x) i) := fun i =>
    Hamiltonian.flux_memLp_gammaBar'_at_test (d := d) hpow
      (q := ENNReal.ofReal γBarReal') m Du i
      hμ_pos (hF_flux_meas i) hG_flux_dom
  -- AC2 invocation 3: discharge `hF_mass` via
  -- `Hamiltonian.μMinusOne_memLp_of_betaBar` at `(p := βBar, q := γBar')`.
  -- Phase 0 routing fix (`infra-P5-theorem1-phase-0`): the mass term
  -- now lives in `L^γ̄'` (paired with `ν ∈ L^γ̄`). The exponent
  -- inclusion `γ̄' ≤ β̄` follows from `α > 1, β > 0` via
  -- `Hamiltonian.gammaBar'_le_betaBar`; here we thread it as `hγ'_le_β`.
  have hF_mass :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => m x - 1) :=
    Hamiltonian.μMinusOne_memLp_of_betaBar (d := d)
      (p := ENNReal.ofReal βBarReal) (q := ENNReal.ofReal γBarReal')
      m hm_memLp hγ'_le_β ENNReal.ofReal_ne_top
  -- Assemble the record. `F_HJB`, `F_flux`, `F_mass` are
  -- definitionally equal to the AC2 conclusions' literal `fun`-shapes.
  exact
    { hβ := hβ
      hγ := hγ
      hF_HJB := hF_HJB
      hF_flux := hF_flux
      hF_mass := hF_mass
      hG_grad := hG_grad_mem
      hG_val := hG_val_mem
      hβTop := hβTop }

/-- **Feeder 1 (universal pass-through wrapper).**

This wrapper threads a *universal* per-triple residue
`(∀ Du m u, MFGOpEpsAuxHyps …)` through unchanged. It exists for
historical/schema-compatibility reasons with the legacy K0-form
`AepsiUniformContext` chain (now deleted by
`infra-P4-delete-AepsiUniformContext-K0-form`), which expected the
universal shape. The genuine analytic content lives in
`auxHyps_of_paperHypotheses_at_triple`, where AC2 is actually invoked
in the body. The universal `(∀ Du m u, …)` shape is *not* in general
derivable from `(hpow, hV)` alone — strict positivity of `m` cannot be
asserted for arbitrary `m` — so this pass-through wrapper is honest:
the residue must come from a domain-specific source (per-K0 supplier
or the regularised `m_ε` sequence).

**AC amendment (CONVENTIONS §8).** The reviewer of iteration 1 noted
that the universal supplier shape `∀ Du m u, MFGOpEpsAuxHyps …` is
structurally too strong (it asserts strict positivity for arbitrary
`m`, which fails). The amendment recorded in the task file replaces
the universal residue with a per-triple feeder
`auxHyps_of_paperHypotheses_at_triple` whose body genuinely consumes
AC2; the universal pass-through below remains for the closed-form
producer's signature compatibility. -/
theorem auxHyps_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Residue (filed: `infra-P4-mfg-operator-clm`): per-triple
    -- five-MemLpPer integrability bundle, packaged as a universal
    -- supplier. See `auxHyps_of_paperHypotheses_at_triple` above
    -- for the AC2-consuming per-triple feeder this would dispatch to.
    (auxRes :
      ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
        MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
          V H DpH Du m u) :
    ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH Du m u :=
  auxRes

/-- Sanity check: `auxHyps_of_paperHypotheses_at_triple` type-checks
and produces the per-triple `MFGOpEpsAuxHyps` record from the AC2
inputs. Pins the type-shape of the AC2-consuming feeder. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ)
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hμ_pos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < m x)
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    (hF_HJB_meas :
      AEStronglyMeasurable
        (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ i,
        AEStronglyMeasurable
          (fun x => m x * DpH x (fun j => Du j x) (m x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hG_HJB_dom :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun i => Du i x‖ ^ hpow.α + 1)
            + hpow.C * (m x ^ hpow.β + 1)
            + |u x| + |V x|))
    (hG_flux_dom :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (m x * ‖fun j => Du j x‖ ^ (hpow.α - 1)
                      + m x ^ (1 + hpow.β - hpow.β / hpow.α) + m x)))
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) m)
    (hG_grad_mem :
      ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (G_grad γBarReal Du i))
    (hG_val_mem :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal u)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH Du m u :=
  auxHyps_of_paperHypotheses_at_triple
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hmon hpow hV hExp Du m u
    hβ hγ hβTop hγ'_le_β hμ_pos
    C' hC'_pos h_upper hF_HJB_meas hF_flux_meas
    hG_HJB_dom hG_flux_dom hm_memLp hG_grad_mem hG_val_mem

/-! ## γ̄-Laplacian Gateaux integrand `MemLpPer γ̄'` closures

The `MFGOpEpsAuxHyps` record carries `MemLpPer γ̄'` certificates for
the two γ̄-Laplacian Gateaux integrand factors

```
G_grad γBar Du i x = vecAbsPowMinusTwo γBar (Du x) * Du i x
                   = ‖Du x‖^{γBar - 2} · Du i x
G_val γBar u x      = absPowMinusTwo γBar (u x) * u x
                   = |u x|^{γBar - 2} · u x.
```

Their pointwise norms are dominated by `‖Du x‖^{γBar - 1}` and
`|u x|^{γBar - 1}` respectively. Combined with `MemLp.norm_rpow_div`
applied to the test-triple's `MemLpPer γBar` regularity (gradient
and value components), this lands the dominators in
`MemLpPer (γBar / (γBar - 1)) = MemLpPer γBar'`. The `MemLp.of_le`
absorption then yields the closure for `G_grad i` and `G_val`.

These closures are the genuine analytic content of the `hG_grad`
and `hG_val` fields of `MFGOpEpsAuxHyps` (filed:
`infra-P4-mfg-operator-clm`). -/

/-- **Pointwise bound for the γ̄-Laplacian gradient factor.**

For any `γBar > 1` and `v : Fin d → ℝ`,
`|vecAbsPowMinusTwo γBar v · v_i| ≤ (∑ j, |v_j|) ^ (γBar - 1)`.

Proof: case-split on whether `v⬝v = 0` (i.e. `v = 0`) or not.
* If `v = 0`, then `v_i = 0` so the LHS is `0`; the RHS is
  `0 ^ (γBar - 1) = 0` since `γBar - 1 > 0`.
* Otherwise, work in the `(v⬝v) > 0` regime where `Real.rpow_add`
  applies, and bound `vecAbsPowMinusTwo γBar v · |v_i|
  ≤ (v⬝v)^((γBar-1)/2) ≤ (∑|v_j|)^(γBar-1)` (using `(v_i)² ≤ v⬝v`
  and `v⬝v ≤ (∑|v_j|)²`). -/
private lemma abs_G_grad_pointwise_le
    {d : ℕ} (γBar : ℝ) (hγBar : 1 < γBar)
    (v : Fin d → ℝ) (i : Fin d) :
    |vecAbsPowMinusTwo γBar v * v i|
      ≤ (∑ j : Fin d, |v j|) ^ (γBar - 1) := by
  have hVV_nn : 0 ≤ v ⬝ v := euclideanDot_self_nonneg v
  have hSum_nn : 0 ≤ ∑ j : Fin d, |v j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hγm1_pos : 0 < γBar - 1 := by linarith
  -- Case split on `v⬝v = 0` vs `v⬝v > 0`.
  rcases eq_or_lt_of_le hVV_nn with hVV_zero | hVV_pos
  · -- Case `v⬝v = 0`: then `v = 0`, so `v_i = 0`.
    have hVV_zero' : v ⬝ v = 0 := hVV_zero.symm
    have hVi_zero : v i = 0 := by
      have hsum_eq_zero : (∑ j : Fin d, v j * v j) = 0 := by
        unfold dotProduct at hVV_zero'
        exact hVV_zero'
      have h_each_zero : ∀ j ∈ (Finset.univ : Finset (Fin d)), v j * v j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => mul_self_nonneg _)).mp hsum_eq_zero
      exact mul_self_eq_zero.mp (h_each_zero i (Finset.mem_univ i))
    rw [hVi_zero, mul_zero, abs_zero]
    exact Real.rpow_nonneg hSum_nn _
  · -- Case `v⬝v > 0`. Combine all factors via `Real.rpow_add` (positive base).
    have hVV_ne : v ⬝ v ≠ 0 := ne_of_gt hVV_pos
    -- `|vecAbsPowMinusTwo γBar v| = (v⬝v)^((γBar-2)/2)`.
    have hpow_nn : 0 ≤ (v ⬝ v) ^ ((γBar - 2)/2) := Real.rpow_nonneg hVV_nn _
    rw [abs_mul, show |vecAbsPowMinusTwo γBar v| = (v ⬝ v) ^ ((γBar - 2)/2) from
        by unfold vecAbsPowMinusTwo; exact abs_of_nonneg hpow_nn]
    -- `|v_i| ≤ √(v⬝v) = (v⬝v)^(1/2)`.
    have habs_v_i_le_sqrt : |v i| ≤ (v ⬝ v) ^ ((1:ℝ)/2) := by
      rw [show ((1:ℝ)/2) = ((1:ℝ)/2 : ℝ) from rfl, ← Real.sqrt_eq_rpow]
      have hvi_sq_le : (v i)^2 ≤ v ⬝ v := by
        have hsum_split :
            v ⬝ v = (v i)^2 + ∑ j ∈ Finset.univ.erase i, (v j)^2 := by
          unfold dotProduct
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          simp [sq, add_comm]
        have hrest_nn : 0 ≤ ∑ j ∈ Finset.univ.erase i, (v j)^2 :=
          Finset.sum_nonneg (fun j _ => sq_nonneg _)
        linarith
      have habs_sq_le : (|v i|)^2 ≤ (Real.sqrt (v ⬝ v))^2 := by
        rw [sq_abs, Real.sq_sqrt hVV_nn]
        exact hvi_sq_le
      have habs_nn : 0 ≤ |v i| := abs_nonneg _
      have hsqrt_nn : 0 ≤ Real.sqrt (v ⬝ v) := Real.sqrt_nonneg _
      exact (abs_le_of_sq_le_sq' habs_sq_le hsqrt_nn).2
    -- Combine: `(v⬝v)^((γBar-2)/2) · |v_i| ≤ (v⬝v)^((γBar-2)/2) · (v⬝v)^(1/2)
    --                                    = (v⬝v)^((γBar-1)/2)`.
    have hcombine :
        (v ⬝ v) ^ ((γBar - 2)/2) * |v i| ≤ (v ⬝ v) ^ ((γBar - 1)/2) := by
      calc (v ⬝ v) ^ ((γBar - 2)/2) * |v i|
          ≤ (v ⬝ v) ^ ((γBar - 2)/2) * (v ⬝ v) ^ ((1:ℝ)/2) :=
            mul_le_mul_of_nonneg_left habs_v_i_le_sqrt hpow_nn
        _ = (v ⬝ v) ^ ((γBar - 2)/2 + (1:ℝ)/2) :=
            (Real.rpow_add hVV_pos _ _).symm
        _ = (v ⬝ v) ^ ((γBar - 1)/2) := by congr 1; ring
    refine le_trans hcombine ?_
    -- Bound `(v⬝v)^((γBar-1)/2) ≤ (∑ |v_j|)^(γBar-1)`.
    -- Via `(v⬝v) ≤ (∑ |v_j|)²` and the monotonicity of `x ↦ x^((γBar-1)/2)`.
    have hVV_le_sumSq : v ⬝ v ≤ (∑ j : Fin d, |v j|) ^ 2 := by
      have hsum_sq :
          (∑ j : Fin d, |v j|) ^ 2 =
            ∑ j : Fin d, ∑ k : Fin d, |v j| * |v k| := by
        rw [sq, Finset.sum_mul_sum]
      rw [hsum_sq]
      have hVV_eq : v ⬝ v = ∑ j : Fin d, |v j| * |v j| := by
        unfold dotProduct
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [← abs_mul, abs_mul_self]
      rw [hVV_eq]
      refine Finset.sum_le_sum ?_
      intro j _
      exact Finset.single_le_sum
        (f := fun k => |v j| * |v k|)
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ j)
    have hexp_nn : 0 ≤ (γBar - 1)/2 := by linarith
    have h1 : (v ⬝ v) ^ ((γBar - 1)/2)
              ≤ ((∑ j : Fin d, |v j|) ^ 2) ^ ((γBar - 1)/2) :=
      Real.rpow_le_rpow hVV_nn hVV_le_sumSq hexp_nn
    -- `((∑|v_j|)²)^((γBar-1)/2) = (∑|v_j|)^(γBar-1)`.
    have h2 : ((∑ j : Fin d, |v j|) ^ 2) ^ ((γBar - 1)/2)
              = (∑ j : Fin d, |v j|) ^ (γBar - 1) := by
      rw [← Real.rpow_natCast (∑ j : Fin d, |v j|) 2, ← Real.rpow_mul hSum_nn]
      congr 1
      push_cast
      ring
    linarith

/-- **Pointwise bound for the γ̄-Laplacian value factor.**

For any `γBar > 1` and `s : ℝ`,
`|absPowMinusTwo γBar s · s| ≤ |s| ^ (γBar - 1)`. -/
private lemma abs_G_val_pointwise_le
    (γBar : ℝ) (hγBar : 1 < γBar) (s : ℝ) :
    |absPowMinusTwo γBar s * s| ≤ |s| ^ (γBar - 1) := by
  unfold absPowMinusTwo
  rw [abs_mul]
  have habs_nn : 0 ≤ |s| := abs_nonneg _
  have hpow_nn : 0 ≤ |s| ^ (γBar - 2) := Real.rpow_nonneg habs_nn _
  rw [abs_of_nonneg hpow_nn]
  -- Goal: `|s|^(γBar-2) * |s| ≤ |s|^(γBar-1)`. The `|(|s|)|` was already
  -- simplified to `|s|` by the elaborator's `abs_abs`-aware unfolding.
  rcases eq_or_lt_of_le habs_nn with hzero | hpos
  · -- `|s| = 0`: both sides are zero (using `γBar - 1 ≠ 0`).
    rw [← hzero, mul_zero,
        Real.zero_rpow (sub_ne_zero.mpr (by linarith : (γBar : ℝ) ≠ 1))]
  · -- `|s| > 0`: combine via `Real.rpow_add`.
    have hRHS : |s| ^ (γBar - 2) * |s| = |s| ^ (γBar - 1) := by
      have h1 : |s| ^ (γBar - 2) * |s| ^ (1 : ℝ) = |s| ^ (γBar - 2 + 1) :=
        (Real.rpow_add hpos _ _).symm
      rw [Real.rpow_one] at h1
      rw [h1]
      congr 1; ring
    exact le_of_eq hRHS

/-- **`MemLpPer γ̄'` closure for the γ̄-Laplacian gradient factor
`G_grad γBar Du i`** at a test triple whose gradient family
`Du i ∈ MemLpPer γBar`.

Reduces to `MemLp.norm_rpow_div` of the scalar function
`Sum x := ∑ j, |Du j x|` (in `MemLpPer γBar` by finite-sum closure)
at exponent `γBar - 1` (yielding `MemLpPer γBar'`), then
`MemLp.of_le` against the pointwise bound
`abs_G_grad_pointwise_le`.

The exponent identity `γBar / (γBar - 1) = γBar'` is supplied as
the residue parameter `hγγ'`. -/
theorem G_grad_memLpPer_gammaBar'
    {d : ℕ} {γBarReal γBarReal' : ℝ}
    (hγ : 1 < γBarReal)
    (hγγ' : γBarReal' = γBarReal / (γBarReal - 1))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du i))
    (i : Fin d) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_grad γBarReal Du i) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- `Sum x := ∑ j, |Du j x|` lies in `MemLpPer γBar`.
  set Sum : (Fin d → ℝ) → ℝ := fun x => ∑ j : Fin d, |Du j x| with hSum_def
  have habs_memLp : ∀ j, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                          (fun x => |Du j x|) := by
    intro j
    have h := (hDuLp j).toMemLp
    have h2 := h.norm
    have heq : (fun x => ‖Du j x‖) = fun x => |Du j x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h2
    exact MemLp.toMemLpPer h2
  have hSum_memLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) Sum := by
    have hsum :
        MemLp (fun x => ∑ j : Fin d, (fun x => |Du j x|) x)
                (ENNReal.ofReal γBarReal)
                (Measure.restrict volume (UnitCube d)) := by
      refine memLp_finset_sum (Finset.univ : Finset (Fin d)) ?_
      intro j _
      exact (habs_memLp j).toMemLp
    exact MemLp.toMemLpPer hsum
  -- `Sum^(γBar-1) ∈ Lp(γBar/(γBar-1)) = Lp γBar'` via `MemLp.norm_rpow_div`.
  have hγm1_pos : 0 < γBarReal - 1 := by linarith
  set qE : ℝ≥0∞ := ENNReal.ofReal (γBarReal - 1) with hqE_def
  have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
  have hqE_toReal : qE.toReal = γBarReal - 1 := by
    rw [hqE_def]; exact ENNReal.toReal_ofReal hγm1_pos.le
  have hRpow_memLp : MemLp
      (fun x : (Fin d → ℝ) => ‖Sum x‖ ^ qE.toReal)
      (ENNReal.ofReal γBarReal / qE)
      (Measure.restrict volume (UnitCube d)) :=
    MemLp.norm_rpow_div hSum_memLp.toMemLp qE
  -- `‖Sum x‖ = Sum x` since `Sum x ≥ 0`.
  have hSum_nn : ∀ x, 0 ≤ Sum x := fun x =>
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hRpow_eq :
      (fun x : (Fin d → ℝ) => ‖Sum x‖ ^ qE.toReal)
      = (fun x : (Fin d → ℝ) => Sum x ^ (γBarReal - 1)) := by
    funext x
    rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hSum_nn x)]
  have hdiv :
      ENNReal.ofReal γBarReal / qE = ENNReal.ofReal γBarReal' := by
    rw [hqE_def, ← ENNReal.ofReal_div_of_pos hγm1_pos, hγγ']
  have hRpow_memLpPer :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) => Sum x ^ (γBarReal - 1)) := by
    rw [← hRpow_eq]
    have := MemLp.toMemLpPer hRpow_memLp
    rw [hdiv] at this
    exact this
  -- Measurability of `G_grad γBar Du i`.
  have hG_meas : AEStronglyMeasurable (G_grad γBarReal Du i)
                  (Measure.restrict volume (UnitCube d)) := by
    unfold G_grad
    refine AEStronglyMeasurable.mul ?_ (hDuLp i).aestronglyMeasurable
    have h_each : ∀ j, AEStronglyMeasurable (fun x => Du j x)
                  (Measure.restrict volume (UnitCube d)) :=
      fun j => (hDuLp j).aestronglyMeasurable
    have h_each_aem : ∀ j, AEMeasurable (fun x => Du j x)
                  (Measure.restrict volume (UnitCube d)) :=
      fun j => (h_each j).aemeasurable
    -- `(fun j => Du j x) ⬝ (fun j => Du j x) = ∑ j, Du j x * Du j x`.
    have h_dot_aem : AEMeasurable
                  (fun x : (Fin d → ℝ) => (fun j => Du j x) ⬝ (fun j => Du j x))
                  (Measure.restrict volume (UnitCube d)) := by
      have heq : (fun x : (Fin d → ℝ) => (fun j => Du j x) ⬝ (fun j => Du j x))
              = (fun x : (Fin d → ℝ) => ∑ j : Fin d, Du j x * Du j x) := by
        funext x; rfl
      rw [heq]
      exact Finset.aemeasurable_fun_sum (s := (Finset.univ : Finset (Fin d)))
              (f := fun j x => Du j x * Du j x)
              (fun j _ => (h_each_aem j).mul (h_each_aem j))
    change AEStronglyMeasurable
          (fun x => vecAbsPowMinusTwo γBarReal (fun j => Du j x))
          (Measure.restrict volume (UnitCube d))
    unfold vecAbsPowMinusTwo
    exact (h_dot_aem.pow_const ((γBarReal - 2) / 2)).aestronglyMeasurable
  -- Apply `MemLp.of_le` with the pointwise bound.
  refine MemLp.toMemLpPer (MemLp.of_le hRpow_memLpPer.toMemLp hG_meas ?_)
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  have habs_le := abs_G_grad_pointwise_le γBarReal hγ (fun j => Du j x) i
  have hRHS_nn : 0 ≤ Sum x ^ (γBarReal - 1) :=
    Real.rpow_nonneg (hSum_nn x) _
  rw [show ‖Sum x ^ (γBarReal - 1)‖ = Sum x ^ (γBarReal - 1) from
      by rw [Real.norm_eq_abs, abs_of_nonneg hRHS_nn]]
  -- |G_grad γBar Du i x| = |vecAbsPowMinusTwo γBar (Du x) * Du i x| (defeq).
  change |G_grad γBarReal Du i x| ≤ Sum x ^ (γBarReal - 1)
  exact habs_le

/-- **`MemLpPer γ̄'` closure for the γ̄-Laplacian value factor
`G_val γBar u`** at a test triple whose value `u ∈ MemLpPer γBar`.

Mirrors `G_grad_memLpPer_gammaBar'` on the scalar side. -/
theorem G_val_memLpPer_gammaBar'
    {d : ℕ} {γBarReal γBarReal' : ℝ}
    (hγ : 1 < γBarReal)
    (hγγ' : γBarReal' = γBarReal / (γBarReal - 1))
    (u : (Fin d → ℝ) → ℝ)
    (huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) u) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal u) := by
  have hγm1_pos : 0 < γBarReal - 1 := by linarith
  set qE : ℝ≥0∞ := ENNReal.ofReal (γBarReal - 1) with hqE_def
  have hqE_top : qE ≠ ⊤ := by rw [hqE_def]; exact ENNReal.ofReal_ne_top
  have hqE_toReal : qE.toReal = γBarReal - 1 := by
    rw [hqE_def]; exact ENNReal.toReal_ofReal hγm1_pos.le
  have hRpow_memLp : MemLp
      (fun x : (Fin d → ℝ) => ‖u x‖ ^ qE.toReal)
      (ENNReal.ofReal γBarReal / qE)
      (Measure.restrict volume (UnitCube d)) :=
    MemLp.norm_rpow_div huLp.toMemLp qE
  have hdiv :
      ENNReal.ofReal γBarReal / qE = ENNReal.ofReal γBarReal' := by
    rw [hqE_def, ← ENNReal.ofReal_div_of_pos hγm1_pos, hγγ']
  have hRpow_memLpPer :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) => |u x| ^ (γBarReal - 1)) := by
    have heq :
        (fun x : (Fin d → ℝ) => |u x| ^ (γBarReal - 1))
        = (fun x : (Fin d → ℝ) => ‖u x‖ ^ qE.toReal) := by
      funext x; rw [hqE_toReal, Real.norm_eq_abs]
    rw [heq]
    have := MemLp.toMemLpPer hRpow_memLp
    rw [hdiv] at this
    exact this
  -- Measurability of `G_val γBar u`.
  have hu_meas : AEStronglyMeasurable u
                  (Measure.restrict volume (UnitCube d)) :=
    huLp.aestronglyMeasurable
  have habs_aem : AEMeasurable (fun x => |u x|)
                    (Measure.restrict volume (UnitCube d)) := by
    have h1 : AEMeasurable (fun x => ‖u x‖)
              (Measure.restrict volume (UnitCube d)) :=
      hu_meas.norm.aemeasurable
    refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
    exact (Real.norm_eq_abs (u x)).symm
  have hG_meas : AEStronglyMeasurable (G_val γBarReal u)
                  (Measure.restrict volume (UnitCube d)) := by
    unfold G_val absPowMinusTwo
    refine AEStronglyMeasurable.mul ?_ hu_meas
    exact (habs_aem.pow_const _).aestronglyMeasurable
  refine MemLp.toMemLpPer (MemLp.of_le hRpow_memLpPer.toMemLp hG_meas ?_)
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  have habs_le := abs_G_val_pointwise_le γBarReal hγ (u x)
  have hRHS_nn : 0 ≤ |u x| ^ (γBarReal - 1) :=
    Real.rpow_nonneg (abs_nonneg _) _
  rw [show ‖|u x| ^ (γBarReal - 1)‖ = |u x| ^ (γBarReal - 1) from
      by rw [Real.norm_eq_abs, abs_of_nonneg hRHS_nn]]
  change |G_val γBarReal u x| ≤ |u x| ^ (γBarReal - 1)
  exact habs_le

/-! ## K_Aepsi-form `MFGOpEpsAuxHyps` supplier

Per the v3 expert plan post-T6 audit, the universal
`∀ Du m u, MFGOpEpsAuxHyps …` shape is structurally false: strict
positivity of `m` cannot be asserted for arbitrary `m`. The fix is
the `K_Aepsi`-restricted (strict-positive) supplier below: a
function indexed over `q ∈ K_Aepsi` (the strict-positivity cone),
each value built from `auxHyps_of_paperHypotheses_at_triple` with:

* `hμ_pos` discharged from `q ∈ K_Aepsi` membership,
* `hm_memLp` discharged from the `LpPer βBar`-component of `q` via
  `memLpPer_of_lpPer`,
* `hG_HJB_dom` discharged from
  `Hamiltonian.g_dominator_memLp_betaBar'` (AC2 closure, just
  landed in iter 224),
* `hG_flux_dom` discharged from
  `Hamiltonian.flux_dominator_memLp_gammaBar'` (AC2 closure, just
  landed in iter 224),
* `hG_grad_mem` discharged from `G_grad_memLpPer_gammaBar'`,
* `hG_val_mem` discharged from `G_val_memLpPer_gammaBar'`,
* `(C', hC'_pos, h_upper)` and `(hβ, hγ, hβγ, hβTop, hβ'_le_β)`
  threaded as residues (filed under the per-triple feeder's
  follow-ups: `infra-P4-eliminate-hExp-parameter` for the Hölder
  pair residues, and the slice hypothesis for
  `upper_bound_powergrowth`),
* `hF_HJB_meas`, `hF_flux_meas` threaded as universal-q
  measurability residues (each is a Caratheodory composition of
  `H, DpH` with the Lp coercions of `q` — the discharge of these
  from `RegularityH.measurable_H` requires a separate measurability
  helper, filed as a follow-up inside this task body),
* the paper-exponent identifications
  `(βBarReal = β + 1, γBarReal = α(β+1)/β, βBarReal' = (β+1)/β)`
  threaded as residues so the dominator-closure hypotheses align
  with the paper-side exponents.

The output is the per-`q ∈ K_Aepsi` `MFGOpEpsAuxHyps` certificate at
the bare-function triple `(DuOf q, mOf q, uOf q)`. -/

/-- **K_Aepsi-form `MFGOpEpsAuxHyps` supplier.** -/
theorem auxHyps_of_paperHypotheses_on_KAepsi
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Paper-exponent identification (residue: align user-supplied
    -- real exponents with the paper's `(α, β)` formulae).
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    -- Hölder pair residues.
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- `(C', h_upper)` from `upper_bound_powergrowth` (residue).
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    -- Measurability witnesses (universal-q residue).
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    ∀ q ∈ K_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH (DuOf q) (mOf q) (uOf q) := by
  -- Standing positivity / bound facts.
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]
    exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have : (hpow.β + 1) < hpow.α * (hpow.β + 1) := by
      have : (1 : ℝ) * (hpow.β + 1) < hpow.α * (hpow.β + 1) :=
        mul_lt_mul_of_pos_right hpow.hα hβ1_pos
      simpa using this
    linarith
  intro q hq_K
  -- `q ∈ K_Aepsi` ⇒ `0 < mOf q a.e.`.
  have hμ_pos :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < mOf q x := hq_K
  -- `MemLpPer` certificates from the Lp components of `q`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf q) :=
    memLpPer_of_lpPer (d := d) q.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf q i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (q.2.2 i)
  -- Reframe the test-triple regularity at the paper exponents.
  have hμ_paperBetaBar : MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) (mOf q) := by
    rw [← hβBar_eq]; exact hmLp
  have hυ_paperGammaBar :
      MemLpPer (d := d) (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        (uOf q) := by
    rw [← hγBar_eq]; exact huLp
  have hDυ_paperGammaBar : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        (DuOf q i) := by
    intro i; rw [← hγBar_eq]; exact hDuLp i
  have hV_paperBetaBar' : MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V := by
    rw [← hβBar'_eq]; exact hV
  -- Discharge `hG_HJB_dom` via `g_dominator_memLp_betaBar'`.
  have hG_HJB_dom_paper :
      MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun i => DuOf q i x‖ ^ hpow.α + 1)
            + hpow.C * (mOf q x ^ hpow.β + 1)
            + |uOf q x| + |V x|) :=
    Hamiltonian.g_dominator_memLp_betaBar' hpow V (uOf q) (mOf q) (DuOf q)
      hμ_paperBetaBar hυ_paperGammaBar hDυ_paperGammaBar hV_paperBetaBar'
      hC'_pos
  have hG_HJB_dom :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          C' * (‖fun i => DuOf q i x‖ ^ hpow.α + 1)
            + hpow.C * (mOf q x ^ hpow.β + 1)
            + |uOf q x| + |V x|) := by
    rw [hβBar'_eq]; exact hG_HJB_dom_paper
  -- Discharge `hG_flux_dom` via `flux_dominator_memLp_gammaBar'`.
  have hG_flux_dom_paper :
      MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
          (hpow.α * (hpow.β + 1) / hpow.β - 1)))
        (fun x : (Fin d → ℝ) =>
          hpow.C * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hpow.α - 1)
                      + mOf q x ^ (1 + hpow.β - hpow.β / hpow.α) + mOf q x)) :=
    Hamiltonian.flux_dominator_memLp_gammaBar' hpow (mOf q) (DuOf q)
      hμ_paperBetaBar hDυ_paperGammaBar
  have hG_flux_dom :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hpow.α - 1)
                      + mOf q x ^ (1 + hpow.β - hpow.β / hpow.α) + mOf q x)) := by
    have hγ'_paper_eq :
        γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                    (hpow.α * (hpow.β + 1) / hpow.β - 1) := by
      rw [hγBar'_eq, hγBar_eq]
    rw [hγ'_paper_eq]; exact hG_flux_dom_paper
  -- Discharge `hG_grad_mem` and `hG_val_mem` via the new closures.
  have hG_grad_mem : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (G_grad γBarReal (DuOf q) i) := by
    intro i
    exact G_grad_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq
            (DuOf q) hDuLp i
  have hG_val_mem :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal (uOf q)) :=
    G_val_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq (uOf q) huLp
  -- Assemble via the per-triple feeder.
  exact auxHyps_of_paperHypotheses_at_triple
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hmon hpow hV hExp (DuOf q) (mOf q) (uOf q)
    hβ hγ hβTop hγ'_le_β hμ_pos
    C' hC'_pos h_upper (hF_HJB_meas q) (hF_flux_meas q)
    hG_HJB_dom hG_flux_dom hmLp hG_grad_mem hG_val_mem

/-- Sanity check: `auxHyps_of_paperHypotheses_on_KAepsi` type-checks
on a strict-positive triple. Pins the `K_Aepsi`-indexed shape
consumed by the K_Aepsi-form abstract VI lifts. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (q : XBanach d βBarReal γBarReal) (hq : q ∈ K_Aepsi d βBarReal γBarReal) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH (DuOf q) (mOf q) (uOf q) :=
  auxHyps_of_paperHypotheses_on_KAepsi
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hmon hpow hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hβTop hγ'_le_β
    C' hC'_pos h_upper hF_HJB_meas hF_flux_meas q hq

/-! ## Per-pair monotonicity-identity integrability discharge

Per `infra-P4-mfg-A-monotone`: the K_Aepsi-form CLM monotonicity wrap
`isMonotone_Aepsi_CLM_K_Aepsi` (in `Banach/AbstractLifts.lean`)
takes a per-pair `hInteg` argument quantifying integrability of the
four monotonicity-identity integrands at every pair
`(v₁, v₂) ∈ K_Aepsi × K_Aepsi`. The lemma below discharges that
argument from a K_Aepsi-indexed `auxHypsK` supplier (matching the
shape of `auxHyps_of_paperHypotheses_on_KAepsi`), reducing the
integrability obligations to:

* `MemLpPer βBarReal` of `m₁ - m₂` (built from `Lp` coercions via
  `MemLp.sub` and the `MemLpPer = MemLp …` defeq);
* `MemLpPer γBarReal` of `Du₁ i - Du₂ i` and `u₁ - u₂` (likewise);
* `MFGOpEpsAuxHyps`'s `hF_HJB`, `hF_flux`, `hF_mass`, `hG_grad`,
  `hG_val` fields at the primal triple of `v₁` (resp. `v₂`);
* `MemLpPer.integrable_mul` for each summand under the appropriate
  Hölder pair `(βBarReal, βBarReal')` or `(γBarReal, γBarReal')`.
-/

/-- **Per-pair integrability of the four monotonicity-identity
integrands.** Given a K_Aepsi-indexed `auxHypsK` supplier and a pair
`(v₁, v₂) ∈ K_Aepsi × K_Aepsi`, produce the four `IntegrableOn`
certificates required by `isMonotone_Aepsi_CLM_K_Aepsi`'s `hInteg`
argument.

The proof unfolds each integrand into a sum of Hölder products
(`F · ξ` for the MFG side, `G · ξ` for the gateaux side) and
discharges each via `MemLpPer.integrable_mul`. The Lp-coercion test
side is built using `MemLp.sub` on `MemLpPer` of the components of
`v₁, v₂`. -/
theorem aepsi_mono_integrability_KAepsi
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (v₁ v₂ : XBanach d βBarReal γBarReal)
    (hv₁ : v₁ ∈ K_Aepsi d βBarReal γBarReal)
    (hv₂ : v₂ ∈ K_Aepsi d βBarReal γBarReal) :
    (IntegrableOn
      (fun x =>
        (-(⇑v₁.2.1 x) - H x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
            + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
          + (⇑v₁.1) x * (DpH x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
                      ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
          + ((⇑v₁.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
      (UnitCube d)
    ∧ IntegrableOn
        (fun x =>
          (-(⇑v₂.2.1 x) - H x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
              + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
            + (⇑v₂.1) x * (DpH x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
                        ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
            + ((⇑v₂.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
        (UnitCube d)
    ∧ IntegrableOn
        (fun x =>
          vecAbsPowMinusTwo γBarReal (fun i => ⇑(v₁.2.2 i) x)
                * ((fun i => ⇑(v₁.2.2 i) x)
                    ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
            + absPowMinusTwo γBarReal (⇑v₁.2.1 x)
                * ((⇑v₁.2.1) x * (((⇑v₁.2.1) - (⇑v₂.2.1)) x)))
        (UnitCube d)
    ∧ IntegrableOn
        (fun x =>
          vecAbsPowMinusTwo γBarReal (fun i => ⇑(v₂.2.2 i) x)
                * ((fun i => ⇑(v₂.2.2 i) x)
                    ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
            + absPowMinusTwo γBarReal (⇑v₂.2.1 x)
                * ((⇑v₂.2.1) x * (((⇑v₁.2.1) - (⇑v₂.2.1)) x)))
        (UnitCube d)) := by
  -- Primal aux records at v₁, v₂.
  have h₁ := auxHypsK v₁ hv₁
  have h₂ := auxHypsK v₂ hv₂
  -- Set up bare-function abbreviations.
  set m₁ : (Fin d → ℝ) → ℝ := ⇑v₁.1
  set m₂ : (Fin d → ℝ) → ℝ := ⇑v₂.1
  set u₁ : (Fin d → ℝ) → ℝ := ⇑v₁.2.1
  set u₂ : (Fin d → ℝ) → ℝ := ⇑v₂.2.1
  set Du₁ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₁.2.2 i)
  set Du₂ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₂.2.2 i)
  -- MemLpPer certificates from Lp coercions.
  have hm₁β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) m₁ :=
    memLpPer_of_lpPer (d := d) v₁.1
  have hm₂β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) m₂ :=
    memLpPer_of_lpPer (d := d) v₂.1
  have hu₁γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) u₁ :=
    memLpPer_of_lpPer (d := d) v₁.2.1
  have hu₂γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) u₂ :=
    memLpPer_of_lpPer (d := d) v₂.2.1
  have hDu₁γ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du₁ i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v₁.2.2 i)
  have hDu₂γ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du₂ i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v₂.2.2 i)
  -- Difference test side: MemLpPer βBarReal of m₁ - m₂.
  have hdm_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (m₁ - m₂) :=
    MemLp.toMemLpPer (hm₁β.toMemLp.sub hm₂β.toMemLp)
  -- u₁ - u₂ in MemLpPer γBarReal.
  have hdu_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (u₁ - u₂) :=
    MemLp.toMemLpPer (hu₁γ.toMemLp.sub hu₂γ.toMemLp)
  -- Du₁ i - Du₂ i in MemLpPer γBarReal.
  have hdDu_γ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                  (fun x => Du₁ i x - Du₂ i x) := by
    intro i
    have : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du₁ i - Du₂ i) :=
      MemLp.toMemLpPer ((hDu₁γ i).toMemLp.sub (hDu₂γ i).toMemLp)
    -- `Du₁ i - Du₂ i = fun x => Du₁ i x - Du₂ i x` by `Pi.sub_apply`.
    convert this using 1
  -- Phase 0 routing fix (`infra-P5-theorem1-phase-0`): the mass term is
  -- now paired against `ν ∈ L^γ̄`, so we no longer need a `βBar`-side
  -- carriage of `u₁ - u₂` (the previous `hdu_β` and `toBetaMem`).
  -- A single-summand integrability template (F * ξ).
  -- We will build the four conjuncts by decomposing each into the
  -- F-form summands and then applying `MemLpPer.integrable_mul`
  -- and `Integrable.add` / `integrable_finset_sum`.
  -- Convenience: reformulate the difference as a Pi.sub_apply.
  have h_sub_m : ∀ x, ((⇑v₁.1) - (⇑v₂.1)) x = m₁ x - m₂ x := by
    intro x; rfl
  have h_sub_u : ∀ x, ((⇑v₁.2.1) - (⇑v₂.2.1)) x = u₁ x - u₂ x := by
    intro x; rfl
  -- Step 1: integrand at primal v₁ (the MFG block).
  -- Decompose: (F_HJB · η) + Σᵢ (F_flux_i · Dν_i) + (F_mass · ν).
  have hI₁_HJB : IntegrableOn
      (fun x => F_HJB V H Du₁ m₁ u₁ x * (m₁ - m₂) x) (UnitCube d) :=
    Periodic.MemLpPer.integrable_mul h₁.hβ.symm h₁.hF_HJB hdm_β
  have hI₁_flux_i : ∀ i, IntegrableOn
      (fun x => F_flux DpH Du₁ m₁ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    intro i
    exact Periodic.MemLpPer.integrable_mul h₁.hγ.symm (h₁.hF_flux i) (hdDu_γ i)
  have hI₁_flux_sum : IntegrableOn
      (fun x => ∑ i : Fin d, F_flux DpH Du₁ m₁ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    have : Integrable
        (fun x => ∑ i : Fin d, F_flux DpH Du₁ m₁ i x * (Du₁ i x - Du₂ i x))
        (Measure.restrict volume (UnitCube d)) :=
      integrable_finset_sum _ (fun i _ => hI₁_flux_i i)
    exact this
  have hI₁_mass : IntegrableOn
      (fun x => F_mass m₁ x * (u₁ - u₂) x) (UnitCube d) :=
    Periodic.MemLpPer.integrable_mul h₁.hγ.symm h₁.hF_mass hdu_γ
  -- Now repackage Σ + Σ + Σ into the literal integrand shape.
  have hI₁ : IntegrableOn
      (fun x =>
        (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
          + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                    ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₁ x - 1) * ((u₁ - u₂) x))
      (UnitCube d) := by
    have hpt : (fun x =>
          (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
            + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
            + (m₁ x - 1) * ((u₁ - u₂) x))
        = (fun x => F_HJB V H Du₁ m₁ u₁ x * (m₁ - m₂) x
              + (∑ i : Fin d, F_flux DpH Du₁ m₁ i x * (Du₁ i x - Du₂ i x))
              + F_mass m₁ x * (u₁ - u₂) x) := by
      funext x
      unfold F_HJB F_flux F_mass dotProduct
      simp only [Finset.mul_sum]
      ring_nf
    rw [hpt]
    exact (hI₁_HJB.add hI₁_flux_sum).add hI₁_mass
  -- Step 2: integrand at primal v₂ (the MFG block, swap primal).
  have hI₂_HJB : IntegrableOn
      (fun x => F_HJB V H Du₂ m₂ u₂ x * (m₁ - m₂) x) (UnitCube d) :=
    Periodic.MemLpPer.integrable_mul h₂.hβ.symm h₂.hF_HJB hdm_β
  have hI₂_flux_i : ∀ i, IntegrableOn
      (fun x => F_flux DpH Du₂ m₂ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    intro i
    exact Periodic.MemLpPer.integrable_mul h₂.hγ.symm (h₂.hF_flux i) (hdDu_γ i)
  have hI₂_flux_sum : IntegrableOn
      (fun x => ∑ i : Fin d, F_flux DpH Du₂ m₂ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    have : Integrable
        (fun x => ∑ i : Fin d, F_flux DpH Du₂ m₂ i x * (Du₁ i x - Du₂ i x))
        (Measure.restrict volume (UnitCube d)) :=
      integrable_finset_sum _ (fun i _ => hI₂_flux_i i)
    exact this
  have hI₂_mass : IntegrableOn
      (fun x => F_mass m₂ x * (u₁ - u₂) x) (UnitCube d) :=
    Periodic.MemLpPer.integrable_mul h₂.hγ.symm h₂.hF_mass hdu_γ
  have hI₂ : IntegrableOn
      (fun x =>
        (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
          + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                    ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₂ x - 1) * ((u₁ - u₂) x))
      (UnitCube d) := by
    have hpt : (fun x =>
          (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
            + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
            + (m₂ x - 1) * ((u₁ - u₂) x))
        = (fun x => F_HJB V H Du₂ m₂ u₂ x * (m₁ - m₂) x
              + (∑ i : Fin d, F_flux DpH Du₂ m₂ i x * (Du₁ i x - Du₂ i x))
              + F_mass m₂ x * (u₁ - u₂) x) := by
      funext x
      unfold F_HJB F_flux F_mass dotProduct
      simp only [Finset.mul_sum]
      ring_nf
    rw [hpt]
    exact (hI₂_HJB.add hI₂_flux_sum).add hI₂_mass
  -- Step 3: integrand at primal v₁ (the gateaux block).
  have hI₃_grad_i : ∀ i, IntegrableOn
      (fun x => G_grad γBarReal Du₁ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    intro i
    exact Periodic.MemLpPer.integrable_mul h₁.hγ.symm (h₁.hG_grad i) (hdDu_γ i)
  have hI₃_grad_sum : IntegrableOn
      (fun x => ∑ i : Fin d, G_grad γBarReal Du₁ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    have : Integrable
        (fun x => ∑ i : Fin d, G_grad γBarReal Du₁ i x * (Du₁ i x - Du₂ i x))
        (Measure.restrict volume (UnitCube d)) :=
      integrable_finset_sum _ (fun i _ => hI₃_grad_i i)
    exact this
  have hI₃_val : IntegrableOn
      (fun x => G_val γBarReal u₁ x * (u₁ - u₂) x) (UnitCube d) :=
    Periodic.MemLpPer.integrable_mul h₁.hγ.symm h₁.hG_val hdu_γ
  have hI₃ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBarReal (fun i => Du₁ i x)
              * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBarReal (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
      (UnitCube d) := by
    have hpt : (fun x =>
          vecAbsPowMinusTwo γBarReal (fun i => Du₁ i x)
                * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
            + absPowMinusTwo γBarReal (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
        = (fun x => (∑ i : Fin d, G_grad γBarReal Du₁ i x * (Du₁ i x - Du₂ i x))
              + G_val γBarReal u₁ x * (u₁ - u₂) x) := by
      funext x
      unfold G_grad G_val dotProduct
      simp only [Finset.mul_sum]
      ring_nf
    rw [hpt]
    exact hI₃_grad_sum.add hI₃_val
  -- Step 4: integrand at primal v₂ (the gateaux block, swap primal).
  have hI₄_grad_i : ∀ i, IntegrableOn
      (fun x => G_grad γBarReal Du₂ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    intro i
    exact Periodic.MemLpPer.integrable_mul h₂.hγ.symm (h₂.hG_grad i) (hdDu_γ i)
  have hI₄_grad_sum : IntegrableOn
      (fun x => ∑ i : Fin d, G_grad γBarReal Du₂ i x * (Du₁ i x - Du₂ i x))
      (UnitCube d) := by
    have : Integrable
        (fun x => ∑ i : Fin d, G_grad γBarReal Du₂ i x * (Du₁ i x - Du₂ i x))
        (Measure.restrict volume (UnitCube d)) :=
      integrable_finset_sum _ (fun i _ => hI₄_grad_i i)
    exact this
  have hI₄_val : IntegrableOn
      (fun x => G_val γBarReal u₂ x * (u₁ - u₂) x) (UnitCube d) :=
    Periodic.MemLpPer.integrable_mul h₂.hγ.symm h₂.hG_val hdu_γ
  have hI₄ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBarReal (fun i => Du₂ i x)
              * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBarReal (u₂ x) * (u₂ x * ((u₁ - u₂) x)))
      (UnitCube d) := by
    have hpt : (fun x =>
          vecAbsPowMinusTwo γBarReal (fun i => Du₂ i x)
                * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
            + absPowMinusTwo γBarReal (u₂ x) * (u₂ x * ((u₁ - u₂) x)))
        = (fun x => (∑ i : Fin d, G_grad γBarReal Du₂ i x * (Du₁ i x - Du₂ i x))
              + G_val γBarReal u₂ x * (u₁ - u₂) x) := by
      funext x
      unfold G_grad G_val dotProduct
      simp only [Finset.mul_sum]
      ring_nf
    rw [hpt]
    exact hI₄_grad_sum.add hI₄_val
  -- Bridge each conjunct from the bare-difference shape (m₁ - m₂) x to
  -- the Lp-coercion difference shape ((⇑v₁.1) - (⇑v₂.1)) x. Since
  -- `Pi.sub_apply` gives `(f - g) x = f x - g x`, the two shapes agree
  -- pointwise.
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hI₁ using 1
  · convert hI₂ using 1
  · convert hI₃ using 1
  · convert hI₄ using 1

/-! ## Composition: `Aepsi_mono_of_paperHypotheses`

The K_Aepsi-form CLM monotonicity wrap `isMonotone_Aepsi_CLM_K_Aepsi`
in `Banach/AbstractLifts.lean` takes a per-pair `hInteg` argument; we
discharge that argument via `aepsi_mono_integrability_KAepsi` above.
The result is the composition theorem `Aepsi_mono_of_paperHypotheses`,
parameterised only by:

* `auxHypsK` — the K_Aepsi-indexed `MFGOpEpsAuxHyps` supplier produced
  by `auxHyps_of_paperHypotheses_on_KAepsi` (or any equivalent
  K_Aepsi-shaped supplier from `infra-P4-mfg-operator-clm`),
* the paper monotonicity bundle `hMon : HypothesisMonotone H DpH`,
* the abstract scalar / vector `|·|^{γ-2}·` monotonicity facts
  `hScalarMono`, `hVecMono` (paper line 944, structurally
  orthogonal to `HypothesisMonotone` but elementary at `γBarReal ≥ 2`),
* `hε : 0 ≤ ε`.

No further residues are threaded — the per-pair integrability bundle is
internally produced by `aepsi_mono_integrability_KAepsi`. -/

/-- **Composition theorem (LL-only carrier).** Monotonicity of the
K_Aepsi-totalized operator `Aepsi_CLM_opK auxHypsK ε` on the
strict-positivity cone `K_Aepsi`, threaded from the K_Aepsi-indexed
`auxHypsK` supplier and the **bare Lasry–Lions inequality**
`LLInequality H DpH` (the type of `HypothesisMonotone.monotone`),
without a parametric integrability residue and without requiring the
full `HypothesisMonotone` bundle.

This is the carrier the T3 `HdeltaK0` assembly needs: the carrier-keyed
LL inequality `llMono_HdeltaK0_of_AEData` is available from selector AE
data, but the full `RegularityH`/`HypothesisMonotone` bundle on
`HdeltaK0` is NOT (its global `measurable_H` field is underivable
without a banned formula bridge). The full-bundle version
`Aepsi_mono_of_paperHypotheses` below delegates here via `hMon.toLL`. -/
theorem Aepsi_mono_of_paperHypotheses_of_ll
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hMon : LLInequality H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w)) :
    Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) := by
  -- Discharge `hInteg` via the per-pair integrability lemma above.
  have hInteg := fun (v₁ v₂ : XBanach d βBarReal γBarReal)
                    (hv₁ : v₁ ∈ K_Aepsi d βBarReal γBarReal)
                    (hv₂ : v₂ ∈ K_Aepsi d βBarReal γBarReal) =>
    aepsi_mono_integrability_KAepsi (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      auxHypsK v₁ v₂ hv₁ hv₂
  exact isMonotone_Aepsi_CLM_K_Aepsi_of_ll (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hMon hε hScalarMono hVecMono hInteg

/-- **Composition theorem.** Monotonicity of the K_Aepsi-totalized
operator `Aepsi_CLM_opK auxHypsK ε` on the strict-positivity cone
`K_Aepsi`, threaded from the K_Aepsi-indexed `auxHypsK` supplier and
the paper monotonicity hypotheses without a parametric integrability
residue.

Thin wrapper over `Aepsi_mono_of_paperHypotheses_of_ll` accepting the
full `HypothesisMonotone H DpH` bundle, forwarding only its `monotone`
field via `hMon.toLL`. -/
theorem Aepsi_mono_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hMon : Hamiltonian.HypothesisMonotone H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w)) :
    Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) :=
  Aepsi_mono_of_paperHypotheses_of_ll (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hMon.toLL hε hScalarMono hVecMono

/-- **Sanity-check `example`.** `Aepsi_mono_of_paperHypotheses` accepts
the K_Aepsi-indexed `auxHypsK` supplier (e.g. produced by
`auxHyps_of_paperHypotheses_on_KAepsi`) plus the paper monotonicity
hypotheses, and delivers `IsMonotone (K_Aepsi …) (Aepsi_CLM_opK …
auxHypsK ε)` with **no** parametric integrability residue. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hMon : Hamiltonian.HypothesisMonotone H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w)) :
    Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) :=
  Aepsi_mono_of_paperHypotheses (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hMon hε hScalarMono hVecMono

/-! ## Composition: `Aepsi_coercive_of_paperHypotheses`

The K_Aepsi-form CLM coercivity wrap `isCoerciveAt_Aepsi_CLM_K_Aepsi`
in `Banach/AbstractLifts.lean` consumes a coercivity-gauge bundle
`(g, C, hbound, hquot_tendsto)`. We discharge:

* the gauge `g v := ‖v‖ ^ γBarReal / γBarReal` (paper line 982's
  natural choice, dominant power on the gauge side as `‖v‖ → ∞`);
* the membership `qRef_simplePower ∈ K_Aepsi` (the m-factor is
  a.e. equal to the constant `1`, and `0 < 1`);
* the a.e.-equalities for the canonical base point's primal data
  via `qRef_simplePower_{m,u,Du}Of_ae`;
* the quotient-tendsto `g v / ‖v‖ → +∞` along
  `cobounded ⊓ 𝓟 K_Aepsi`, reduced to `‖v‖^(γBarReal - 1) → ∞`
  via `tendsto_norm_cobounded_atTop` and `tendsto_rpow_atTop`
  (paper line 982's algebraic step).

The integrated lower bound `hbound_residue` (paper line 982,
quotient form) is threaded as a parameter: it is the
**Banach-pair-norm-translated** lift of paper line 967's
integrated `coercivity_integral_lower_bound` (in `Coercivity.lean`)
through `MemLpPer.norm_pair_rpow_le` and
`MemSobolevPer.norm_toLpSobolev_rpow_le` (the
`infra-P4-refactor-banach-norm-translation` infrastructure). This
matches the `hScalarMono`/`hVecMono` pattern in
`Aepsi_mono_of_paperHypotheses` (paper-line-944 residues threaded
as parameters because they are structurally orthogonal to the
paper hypothesis bundle but elementary).
-/

/-- **Coercivity gauge exponent** `κ := min β̄ γ̄`.

Expert audit (2026-05-17, post iter 0644): the paper-line-982
coercivity LHS cannot use bare `γBarReal` as the gauge exponent
without imposing the non-paper polarity `γBarReal ≤ βBarReal`
(equivalently `α ≤ β`). The fix is to weaken the exponent to
`min βBarReal γBarReal`, matching the primitive
`Periodic.MemLpPer.norm_pair_rpow_min_le` which handles both
polarities uniformly. Coercivity is preserved because the exponent
is `> 1` whenever both `βBarReal, γBarReal > 1` (cf.
`one_lt_coercivityGaugeExponent`). -/
noncomputable def coercivityGaugeExponent (βBarReal γBarReal : ℝ) : ℝ :=
  min βBarReal γBarReal

lemma one_lt_coercivityGaugeExponent
    {βBarReal γBarReal : ℝ}
    (hβ : 1 < βBarReal) (hγ : 1 < γBarReal) :
    1 < coercivityGaugeExponent βBarReal γBarReal := by
  unfold coercivityGaugeExponent
  exact lt_min hβ hγ

@[simp] lemma coercivityGaugeExponent_le_left
    (βBarReal γBarReal : ℝ) :
    coercivityGaugeExponent βBarReal γBarReal ≤ βBarReal :=
  min_le_left _ _

@[simp] lemma coercivityGaugeExponent_le_right
    (βBarReal γBarReal : ℝ) :
    coercivityGaugeExponent βBarReal γBarReal ≤ γBarReal :=
  min_le_right _ _

/-- **Coercivity gauge** `g(v) := ‖v‖^γBarReal / γBarReal`.

The natural choice of gauge for paper line 982: with `γBarReal ≥ 2`,
`g v / ‖v‖ = ‖v‖^(γBarReal - 1) / γBarReal → +∞` as `‖v‖ → +∞`. -/
noncomputable def aepsiCoerciveGauge
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (γ : ℝ) (v : XBanach d βBarReal γBarReal) : ℝ :=
  ‖v‖ ^ γ / γ

/-- **`qRef_simplePower` lies in the strict-positive cone `K_Aepsi`.**

The `m`-factor of `qRef_simplePower` agrees a.e. with the constant
`1` on the unit cube, and `0 < 1`. -/
theorem qRef_simplePower_mem_K_Aepsi
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    qRef_simplePower d βBarReal γBarReal
      ∈ K_Aepsi d βBarReal γBarReal := by
  -- Membership unfolds to `0 < ⇑v.1 x` a.e.; the m-factor is a.e. `1`.
  have h_ae : mOf (qRef_simplePower d βBarReal γBarReal)
                =ᵐ[MeasureTheory.Measure.restrict
                      (volume : MeasureTheory.Measure (Fin d → ℝ)) (UnitCube d)]
                (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    qRef_simplePower_mOf_ae d βBarReal γBarReal
  -- `mOf q x = ⇑q.1 x` definitionally; rewrite the membership target to use `mOf`.
  refine h_ae.mono ?_
  intro x hx
  -- `hx : mOf qRef x = 1`; `mOf qRef x` is definitionally `⇑qRef.1 x`.
  show 0 < (mOf (qRef_simplePower d βBarReal γBarReal)) x
  rw [hx]
  exact zero_lt_one

/-! ## Scaled-gauge sibling: `Aepsi_coercive_of_paperHypotheses_scaled`

Per the iter-0668 user decision (Path B), the paper-line-982 coercivity
bound that the downstream chain genuinely produces is the **scaled**
form `λ · gauge κ v − C ≤ op-diff(v)` on the cobounded ⊓ K_Aepsi filter,
with `λ > 0` and `κ > 1`. The unscaled wrapper
`Aepsi_coercive_of_paperHypotheses` (above) is retained for legacy
callers; this scaled sibling threads the `λ`-factor and the exponent
`κ` as parameters (`κ := coercivityGaugeExponent βBarReal γBarReal
= min β̄ γ̄` at the paper-faithful call site).

This is the inlined copy of the wrapper of the same name that lives in
`StationaryMFG/Theorems/SimplePower/Coercivity/Integrability.lean`:
the two are interchangeable (both route the quotient-tendsto through
`tendsto_rpow_atTop`), but we land a local copy here to avoid the
public import cycle `Banach/AssemblyContext ← Coercivity/Integrability ←

Banach/AssemblyContext` that the aggregator rewire would otherwise
introduce. -/

/-- **Scaled-gauge sibling of `Aepsi_coercive_of_paperHypotheses`.**
Coercivity of the K_Aepsi-totalized operator `Aepsi_CLM_opK auxHypsK ε`
on `K_Aepsi` at the canonical base point `qRef_simplePower`, with the
**scaled** gauge `g v := lam * (‖v‖^κ / κ)`.

The integrated lower bound `hbound_residue` is the scaled paper-line-982
quotient bridge — exactly the shape produced by
`coercivity_scaled_min_gauge_le_operator_diff_eventually` in
`Coercivity/Integrability.lean`.

The quotient-tendsto `g v / ‖v‖ = lam · ‖v‖^(κ-1) / κ → +∞` is
discharged honestly via `tendsto_rpow_atTop` and
`Filter.Tendsto.atTop_div_const` (paper line 982's algebraic step). -/
theorem Aepsi_coercive_of_paperHypotheses_scaled
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ)
    -- Scaled-gauge parameters: exponent `κ > 1` and positive scaling
    -- `lam > 0`.
    (κ : ℝ) (hκ : 1 < κ)
    (lam : ℝ) (hlam : 0 < lam)
    -- Additive coercivity constant.
    (C : ℝ)
    -- Scaled paper-line-982 residue on the cobounded filter.
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              κ v - C ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)) :
    Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε)
      (qRef_simplePower d βBarReal γBarReal) := by
  -- The scaled gauge `g(v) := lam * (‖v‖^κ / κ)`.
  set g : XBanach d βBarReal γBarReal → ℝ :=
    fun v => lam * aepsiCoerciveGauge
                    (βBarReal := βBarReal) (γBarReal := γBarReal) κ v
    with hg_def
  -- Membership: `qRef ∈ K_Aepsi`.
  have hqRef_mem : qRef_simplePower d βBarReal γBarReal
                    ∈ K_Aepsi d βBarReal γBarReal :=
    qRef_simplePower_mem_K_Aepsi d βBarReal γBarReal
  -- a.e.-equalities for the canonical base point.
  have h_m0_ae := qRef_simplePower_mOf_ae d βBarReal γBarReal
  have h_u0_ae := qRef_simplePower_uOf_ae d βBarReal γBarReal
  have h_Du0_ae := qRef_simplePower_DuOf_ae d βBarReal γBarReal
  -- Quotient-tendsto: `g v / ‖v‖ = lam · ‖v‖^(κ - 1) / κ → +∞`.
  have hκ_pos : 0 < κ := lt_trans zero_lt_one hκ
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ_pos
  have hκ_m1_pos : 0 < κ - 1 := sub_pos.mpr hκ
  -- Norm tendsto along `cobounded ⊓ 𝓟 K_Aepsi`.
  have h_nrm_tendsto :
      Filter.Tendsto (fun v : XBanach d βBarReal γBarReal => ‖v‖)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  -- `‖v‖^(κ - 1) → +∞`.
  have h_pow_tendsto :
      Filter.Tendsto (fun v : XBanach d βBarReal γBarReal => ‖v‖ ^ (κ - 1))
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    (tendsto_rpow_atTop hκ_m1_pos).comp h_nrm_tendsto
  -- Divide by `κ > 0`: `‖v‖^(κ - 1) / κ → +∞`.
  have h_pow_div_tendsto :
      Filter.Tendsto
        (fun v : XBanach d βBarReal γBarReal => ‖v‖ ^ (κ - 1) / κ)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    h_pow_tendsto.atTop_div_const hκ_pos
  -- Multiply by `lam > 0`: `lam · (‖v‖^(κ - 1) / κ) → +∞`.
  have h_quot_pre :
      Filter.Tendsto
        (fun v : XBanach d βBarReal γBarReal => lam * (‖v‖ ^ (κ - 1) / κ))
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hlam h_pow_div_tendsto
  -- Identify `g v / ‖v‖` with `lam * (‖v‖^(κ - 1) / κ)` eventually
  -- (whenever `‖v‖ > 0`).
  have h_nrm_pos :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        (0 : ℝ) < ‖v‖ :=
    h_nrm_tendsto.eventually_gt_atTop 0
  have hquot_tendsto :
      Filter.Tendsto (fun v => g v / ‖v‖)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop := by
    refine h_quot_pre.congr' ?_
    filter_upwards [h_nrm_pos] with v hv
    have hv_ne : ‖v‖ ≠ 0 := ne_of_gt hv
    have hv_nn : (0 : ℝ) ≤ ‖v‖ := le_of_lt hv
    -- `‖v‖^κ = ‖v‖^(κ - 1) * ‖v‖^1 = ‖v‖^(κ - 1) * ‖v‖`.
    have hsplit : ‖v‖ ^ κ = ‖v‖ ^ (κ - 1) * ‖v‖ := by
      have hh := Real.rpow_add hv (κ - 1) 1
      rw [Real.rpow_one] at hh
      have hsum : (κ - 1) + 1 = κ := by ring
      rw [hsum] at hh
      exact hh
    -- Goal: `lam * (‖v‖^(κ-1) / κ) = g v / ‖v‖`.
    change lam * (‖v‖ ^ (κ - 1) / κ)
            = lam * aepsiCoerciveGauge (βBarReal := βBarReal)
                    (γBarReal := γBarReal) κ v / ‖v‖
    unfold aepsiCoerciveGauge
    rw [hsplit]
    field_simp
  -- Compose via the K_Aepsi-form coercivity lift.
  exact isCoerciveAt_Aepsi_CLM_K_Aepsi (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK ε
    (qRef_simplePower d βBarReal γBarReal)
    hqRef_mem h_m0_ae h_u0_ae h_Du0_ae
    g C hbound_residue hquot_tendsto

/-! ## Norm-closedness of `S_W` (weak-derivative tie set)

Sub-child 1a of `infra-P4-K0_Aepsi_W-norm-closed` (iter-0684 split).
We record the set `S_W d β γ ⊆ XBanach d β γ` of Banach pairs whose
per-coordinate value/gradient components satisfy the weak-derivative
IBP identity against every smooth periodic test function, and prove
it is norm-closed.

The proof passes both sides of the IBP identity through the limit
via the Hölder pairing `f ↦ ∫ ⇑f · g` (continuous on `Lp ℝ p μ` since
the test function `g` is bounded and `μ` is finite). Both projections
`v ↦ v.2.1` and `v ↦ v.2.2 i` from `XBanach` are continuous (product
projections), so the composition is continuous; the set defining the
IBP identity is then a preimage of `{0}` (the diagonal of two
continuous maps), hence closed.

The `MemLpPer 1 (DuOf v i)` half of `HasWeakDerivPer` is automatic
for `v : XBanach`, because `DuOf v i = ⇑(v.2.2 i)` with `v.2.2 i ∈
Lp ℝ (ENNReal.ofReal γBarReal) μ` and the finite measure of the unit
cube gives the L¹ inclusion via `MemLp.mono_exponent`. -/

section S_W_Closedness

open MeasureTheory Set
open StationaryMFG.Periodic

/-- A `SmoothPeriodic` function is bounded almost everywhere on the
unit cube (a.e. with respect to the restricted Lebesgue measure). We
return a nonnegative constant `M` together with the pointwise bound
on the unit cube. -/
private lemma smoothPeriodic_bdd_aux {d : ℕ}
    (φ : StationaryMFG.Periodic.SmoothPeriodic d) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : Fin d → ℝ,
        ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ M := by
  -- φ is continuous, periodic; we bound on the closed cube [0,1]^d
  -- (compact), then extend by periodicity to all of ℝ^d.
  classical
  have hcont : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
  have hcompact :
      IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hcont.norm.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x
  -- Periodicity: there exists an integer translate `x - k ∈ UnitCube`.
  obtain ⟨k, hk⟩ :=
    StationaryMFG.Periodic.exists_int_translate_mem_unitCube (d := d) x
  -- Use `IsPeriodic` directly: `φ (y + k) = φ y` for any integer `k`.
  have hper : (φ : (Fin d → ℝ) → ℝ) x =
              (φ : (Fin d → ℝ) → ℝ) (x - fun i => (k i : ℝ)) := by
    have h := φ.periodic k (x - fun i => (k i : ℝ))
    have hcancel : ((x - fun i => (k i : ℝ)) + fun i => (k i : ℝ)) = x := by
      funext i; simp
    rw [hcancel] at h
    exact h
  show ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ max C 0
  rw [hper]
  -- Bound `‖φ (x - k)‖ ≤ C ≤ max C 0`.
  have hmem : (x - fun i => (k i : ℝ)) ∈
      Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
    intro j _
    have hkj : (x - fun i => (k i : ℝ)) j ∈ Set.Ico (0 : ℝ) 1 := by
      have hkj' := hk
      rw [StationaryMFG.Periodic.mem_unitCube_iff] at hkj'
      exact ⟨(hkj' j).1, (hkj' j).2⟩
    exact Set.Ico_subset_Icc_self hkj
  have hbd : ‖(φ : (Fin d → ℝ) → ℝ) (x - fun i => (k i : ℝ))‖ ≤ C :=
    hC ⟨(x - fun i => (k i : ℝ)), hmem, rfl⟩
  exact hbd.trans (le_max_left C 0)

/-- **Hölder pairing CLM.** For a bounded measurable test function `g`
on a finite-measure space, the integral pairing `f ↦ ∫ ⇑f · g` is a
continuous function from `Lp ℝ p μ` to `ℝ`. We factor through L¹: the
finite-measure inclusion `Lp ℝ p μ → Lp ℝ 1 μ` is continuous (it is
linear with operator norm bounded by `μ(univ)^{1-1/p}` via the Hölder
inequality applied at exponents `1, p, p/(p-1)`), and the L¹ pairing
`L¹ → ℝ, h ↦ ∫ ⇑h * g` is continuous (it has Lipschitz constant `M`
on `L¹` since `g` is bounded by `M`). -/
private lemma continuous_integral_smul_bounded_aux
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g μ)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) :
    Continuous (fun f : MeasureTheory.Lp ℝ p μ => ∫ x, ⇑f x * g x ∂μ) := by
  -- Step 1: Set up the L¹ inclusion as a function `incl : Lp ℝ p μ → Lp ℝ 1 μ`
  -- via `MemLp.mono_exponent`. We do not need this to be a CLM in
  -- Mathlib's sense; we only need to show that the composed function
  -- is continuous, which we do by an explicit ε-δ proof.
  --
  -- Step 2: Show that the function under study is locally Lipschitz
  -- at every point. We use `Metric.continuous_iff`.
  refine Metric.continuous_iff.mpr ?_
  intro f₀ ε hε
  -- The Lipschitz constant is `M * (μ univ).toReal ^ (1 - 1/p.toReal)`,
  -- finite because μ is finite.
  -- For our argument we don't compute the exact constant; instead we
  -- pick the constant from the Hölder bound on `eLpNorm h 1 μ`.
  --
  -- Concretely: for any `f, h : Lp ℝ p μ`:
  --  |∫ ⇑f * g - ∫ ⇑h * g|
  --    = |∫ (⇑f - ⇑h) * g|
  --    ≤ ∫ |⇑f - ⇑h| * |g|
  --    ≤ M * ∫ |⇑f - ⇑h|
  --    = M * ‖f - h‖_{L¹}
  --    ≤ M * (μ univ).toReal^(1-1/p.toReal) * ‖f - h‖.
  -- The constant is `C := M * (μ univ).toReal^(1-1/p.toReal)`.
  -- Pick `δ = ε / (C + 1)` so that `C * δ < ε`.
  classical
  set pR : ℝ := p.toReal with hpR_def
  set Cmu : ℝ := (μ Set.univ).toReal ^ (1 - 1 / pR) with hCmu_def
  have hμfin : μ Set.univ < ∞ := measure_lt_top μ Set.univ
  have hμtoReal_nn : 0 ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
  have hCmu_nn : 0 ≤ Cmu := Real.rpow_nonneg hμtoReal_nn _
  set C : ℝ := M * Cmu + 1 with hC_def
  have hC_pos : 0 < C := by
    have : 0 ≤ M * Cmu := mul_nonneg hM hCmu_nn
    linarith
  refine ⟨ε / C, div_pos hε hC_pos, ?_⟩
  intro f hf
  -- `dist f f₀ < ε / C` means `‖f - f₀‖ < ε / C`.
  rw [dist_eq_norm] at hf
  -- We want: `|∫ ⇑f * g - ∫ ⇑f₀ * g| < ε`.
  show dist (∫ x, ⇑f x * g x ∂μ) (∫ x, ⇑f₀ x * g x ∂μ) < ε
  rw [Real.dist_eq]
  -- Key bound: |∫ (⇑f - ⇑f₀) * g| ≤ M * ∫ |⇑f - ⇑f₀|.
  -- and ∫ |⇑f - ⇑f₀| ≤ μ(univ)^(1-1/p) * ‖f - f₀‖_p.
  -- First, integrability of f * g and f₀ * g.
  have hg_ae_bd : ∀ᵐ x ∂μ, ‖g x‖ ≤ M := hg_bound
  have hf_int : Integrable (fun x => ⇑f x * g x) μ := by
    have h1 : Integrable (⇑f : α → ℝ) μ :=
      (MeasureTheory.Lp.memLp f).mono_exponent (Fact.out)
        |>.integrable le_rfl
    exact h1.mul_bdd hg_meas hg_ae_bd
  have hf₀_int : Integrable (fun x => ⇑f₀ x * g x) μ := by
    have h1 : Integrable (⇑f₀ : α → ℝ) μ :=
      (MeasureTheory.Lp.memLp f₀).mono_exponent (Fact.out)
        |>.integrable le_rfl
    exact h1.mul_bdd hg_meas hg_ae_bd
  have hdiff_int : Integrable (fun x => (⇑f x - ⇑f₀ x) * g x) μ := by
    have h1 : Integrable (fun x => ⇑f x - ⇑f₀ x) μ := by
      have h1' : Integrable (⇑(f - f₀) : α → ℝ) μ :=
        (MeasureTheory.Lp.memLp (f - f₀)).mono_exponent (Fact.out)
          |>.integrable le_rfl
      -- (f - f₀ : Lp) coincides ae with ⇑f - ⇑f₀
      have hcoe := MeasureTheory.Lp.coeFn_sub f f₀
      exact h1'.congr hcoe
    exact h1.mul_bdd hg_meas hg_ae_bd
  have habs_int : Integrable (fun x => |⇑f x - ⇑f₀ x|) μ := by
    have h1 : Integrable (fun x => ⇑f x - ⇑f₀ x) μ := by
      have h1' : Integrable (⇑(f - f₀) : α → ℝ) μ :=
        (MeasureTheory.Lp.memLp (f - f₀)).mono_exponent (Fact.out)
          |>.integrable le_rfl
      have hcoe := MeasureTheory.Lp.coeFn_sub f f₀
      exact h1'.congr hcoe
    exact h1.abs
  -- Step A: combine the two integrals into one.
  have hsub :
      (∫ x, ⇑f x * g x ∂μ) - (∫ x, ⇑f₀ x * g x ∂μ) =
        ∫ x, (⇑f x - ⇑f₀ x) * g x ∂μ := by
    rw [← integral_sub hf_int hf₀_int]
    congr 1; funext x; ring
  rw [hsub]
  -- Step B: |∫ (⇑f - ⇑f₀) * g| ≤ ∫ |⇑f - ⇑f₀| * M ≤ M * ∫ |⇑f - ⇑f₀|.
  have hbound1 :
      |∫ x, (⇑f x - ⇑f₀ x) * g x ∂μ| ≤ ∫ x, |⇑f x - ⇑f₀ x| * M ∂μ := by
    calc
      |∫ x, (⇑f x - ⇑f₀ x) * g x ∂μ|
          ≤ ∫ x, ‖(⇑f x - ⇑f₀ x) * g x‖ ∂μ := by
            have h := norm_integral_le_integral_norm
              (fun x => (⇑f x - ⇑f₀ x) * g x) (μ := μ)
            simpa [Real.norm_eq_abs] using h
        _ ≤ ∫ x, |⇑f x - ⇑f₀ x| * M ∂μ := by
            apply integral_mono_ae
            · -- integrable LHS
              exact hdiff_int.norm
            · -- integrable RHS
              exact habs_int.mul_const M
            · filter_upwards [hg_ae_bd] with x hx
              calc ‖(⇑f x - ⇑f₀ x) * g x‖
                  = |⇑f x - ⇑f₀ x| * |g x| := by
                    rw [Real.norm_eq_abs, abs_mul]
                _ ≤ |⇑f x - ⇑f₀ x| * M := by
                    have habs : 0 ≤ |⇑f x - ⇑f₀ x| := abs_nonneg _
                    have hgxabs : |g x| ≤ M := by simpa [Real.norm_eq_abs] using hx
                    exact mul_le_mul_of_nonneg_left hgxabs habs
  -- Simplify the RHS: `∫ |⇑f - ⇑f₀| * M = M * ∫ |⇑f - ⇑f₀|`.
  have hRHS_eq :
      (∫ x, |⇑f x - ⇑f₀ x| * M ∂μ) = M * ∫ x, |⇑f x - ⇑f₀ x| ∂μ := by
    rw [integral_mul_const, mul_comm]
  rw [hRHS_eq] at hbound1
  -- Step C: `∫ |⇑f - ⇑f₀| dμ ≤ Cmu * ‖f - f₀‖`.
  have hbound2 :
      (∫ x, |⇑f x - ⇑f₀ x| ∂μ) ≤ Cmu * ‖f - f₀‖ := by
    -- The integral of `|⇑(f - f₀)|` equals `‖f - f₀‖_{L^1(μ)}` =
    -- `(eLpNorm (f - f₀) 1 μ).toReal`.
    -- This is bounded by `μ(univ)^{1-1/p} * ‖f - f₀‖_{Lp}` by Hölder.
    have h_coe : (fun x => |⇑f x - ⇑f₀ x|) =ᵐ[μ]
                 (fun x => ‖⇑(f - f₀) x‖) := by
      filter_upwards [MeasureTheory.Lp.coeFn_sub f f₀] with x hx
      rw [hx, Pi.sub_apply, Real.norm_eq_abs]
    have h_eq : (∫ x, |⇑f x - ⇑f₀ x| ∂μ) = ∫ x, ‖⇑(f - f₀) x‖ ∂μ :=
      integral_congr_ae h_coe
    rw [h_eq]
    -- `∫ ‖⇑(f - f₀) x‖ dμ = (eLpNorm (f - f₀) 1 μ).toReal`
    have h_eLp1 : (eLpNorm (⇑(f - f₀)) 1 μ).toReal =
                  ∫ x, ‖⇑(f - f₀) x‖ ∂μ := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm
        (MeasureTheory.Lp.aestronglyMeasurable (f - f₀))]
      rw [MeasureTheory.integral_norm_eq_lintegral_enorm
            (MeasureTheory.Lp.aestronglyMeasurable (f - f₀))]
    rw [← h_eLp1]
    -- Hölder: eLpNorm 1 ≤ eLpNorm p * μ(univ)^(1-1/p).
    have hpfact : (1 : ℝ≥0∞) ≤ p := Fact.out
    have hbd : eLpNorm (⇑(f - f₀)) 1 μ ≤
        eLpNorm (⇑(f - f₀)) p μ * μ Set.univ ^ ((1 : ℝ) - 1 / pR) := by
      have := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ) (p := 1) (q := p) hpfact
        (MeasureTheory.Lp.aestronglyMeasurable (f - f₀))
      -- The formula matches with `1 / (1 : ℝ≥0∞).toReal = 1`.
      have h1 : ((1 : ℝ≥0∞).toReal) = 1 := ENNReal.toReal_one
      rw [h1] at this
      have : eLpNorm (⇑(f - f₀)) 1 μ ≤
             eLpNorm (⇑(f - f₀)) p μ * μ Set.univ ^ (1 / (1 : ℝ) - 1 / pR) :=
        this
      simpa [one_div] using this
    -- Convert from `eLpNorm` to `‖·‖` via `Lp.norm_def`.
    have heq_p : eLpNorm (⇑(f - f₀)) p μ = ENNReal.ofReal ‖f - f₀‖ := by
      rw [MeasureTheory.Lp.norm_def]
      exact (ENNReal.ofReal_toReal (MeasureTheory.Lp.eLpNorm_ne_top _)).symm
    -- The RHS of `hbd` (before rewriting) is finite.
    have hμpow_ne_top : (μ Set.univ ^ ((1 : ℝ) - 1 / pR)) ≠ ∞ := by
      refine ENNReal.rpow_ne_top_of_nonneg ?_ hμfin.ne
      -- Need 1 - 1/pR ≥ 0, i.e. 1/pR ≤ 1, i.e. pR ≥ 1.
      by_cases hp_top : p = ∞
      · subst hp_top; simp [pR]
      have hpR_ge1 : 1 ≤ pR := by
        have := ENNReal.toReal_mono hp_top hpfact
        simpa [pR] using this
      have hpR_pos : 0 < pR := by linarith
      have : 1 / pR ≤ 1 := by rw [div_le_one hpR_pos]; exact hpR_ge1
      linarith
    have hRHS_ne_top : eLpNorm (⇑(f - f₀)) p μ * μ Set.univ ^ ((1 : ℝ) - 1 / pR) ≠ ∞ := by
      apply ENNReal.mul_ne_top
      · rw [heq_p]; exact ENNReal.ofReal_ne_top
      · exact hμpow_ne_top
    have htoR := ENNReal.toReal_mono hRHS_ne_top hbd
    -- Make sense of `toReal` of the product
    rw [ENNReal.toReal_mul] at htoR
    rw [heq_p, ENNReal.toReal_ofReal (norm_nonneg _)] at htoR
    -- Reorder: Cmu * ‖f-f₀‖
    have htoR' : (eLpNorm (⇑(f - f₀)) 1 μ).toReal ≤
                 ‖f - f₀‖ * (μ Set.univ ^ ((1 : ℝ) - 1 / pR)).toReal := htoR
    rw [show (μ Set.univ ^ ((1 : ℝ) - 1 / pR)).toReal = Cmu from ?_] at htoR'
    · linarith
    · -- (μ univ ^ r).toReal = (μ univ).toReal ^ r
      rw [hCmu_def]
      exact (ENNReal.toReal_rpow _ _).symm
  -- Combine: |LHS| ≤ M * (Cmu * ‖f - f₀‖) = M * Cmu * ‖f - f₀‖.
  calc |∫ x, (⇑f x - ⇑f₀ x) * g x ∂μ|
      ≤ M * ∫ x, |⇑f x - ⇑f₀ x| ∂μ := hbound1
    _ ≤ M * (Cmu * ‖f - f₀‖) :=
        mul_le_mul_of_nonneg_left hbound2 hM
    _ = M * Cmu * ‖f - f₀‖ := by ring
    _ ≤ C * ‖f - f₀‖ := by
        have h_nn : 0 ≤ ‖f - f₀‖ := norm_nonneg _
        have hC' : M * Cmu ≤ C := by rw [hC_def]; linarith
        exact mul_le_mul_of_nonneg_right hC' h_nn
    _ < C * (ε / C) := by
        have hfn : ‖f - f₀‖ < ε / C := hf
        have := mul_lt_mul_of_pos_left hfn hC_pos
        exact this
    _ = ε := by
        field_simp

/-- **Continuity of the gradient projection from `XBanach`.** The map
`v ↦ v.2.2 i` is continuous from the `XBanach` product space into the
corresponding gradient `Lp ℝ γBar μ`. -/
private lemma continuous_DuOf_proj
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (i : Fin d) :
    Continuous (fun v : XBanach d βBarReal γBarReal =>
      v.2.2 i) := by
  exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)

/-- **Continuity of the value projection from `XBanach`.** The map
`v ↦ v.2.1` is continuous from the `XBanach` product space into the
corresponding value `Lp ℝ γBar μ`. -/
private lemma continuous_uOf_proj
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    Continuous (fun v : XBanach d βBarReal γBarReal => v.2.1) :=
  continuous_fst.comp continuous_snd

/-- **The weak-derivative-tie set.** Following the iter-0684 split,
this is the slice of `XBanach` recording the IBP identity for every
smooth periodic test function and every coordinate. The
`MemLpPer 1 (DuOf v i)` half of `HasWeakDerivPer` is automatic for
`v : XBanach` (since `DuOf v i = ⇑(v.2.2 i)` lies in `Lp ℝ γBar μ`,
which embeds in `L¹` on the finite-measure unit cube via
`MemLp.mono_exponent`). So we package only the IBP identity here. -/
def S_W (d : ℕ) (βBarReal γBarReal : ℝ) :
    Set (XBanach d βBarReal γBarReal) :=
  { v | ∀ (i : Fin d) (φ : StationaryMFG.Periodic.SmoothPeriodic d),
      periodicIntegral (fun x => DuOf v i x *
        (φ : (Fin d → ℝ) → ℝ) x) =
      - periodicIntegral (fun x => uOf v x *
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ :
            StationaryMFG.Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) }

/-- Membership unfolding for `S_W`. -/
lemma mem_S_W_iff {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal} :
    v ∈ S_W d βBarReal γBarReal ↔
      ∀ (i : Fin d) (φ : StationaryMFG.Periodic.SmoothPeriodic d),
        periodicIntegral (fun x => DuOf v i x *
          (φ : (Fin d → ℝ) → ℝ) x) =
        - periodicIntegral (fun x => uOf v x *
          ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ :
              StationaryMFG.Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) :=
  Iff.rfl

/-- **Norm-closedness of `S_W`.** The set of Banach pairs satisfying
the per-coordinate weak-derivative IBP identity against every smooth
periodic test function is norm-closed. The proof: for each fixed
`(i, φ)`, the set of `v` satisfying the IBP identity is the equalizer
of two continuous functions `XBanach → ℝ`, hence closed. Then `S_W`
is the intersection of all such equalizers, hence closed. -/
theorem S_W_closed (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    IsClosed (S_W d βBarReal γBarReal) := by
  -- Express `S_W` as a (universal) intersection of equalizer sets.
  rw [show S_W d βBarReal γBarReal =
        ⋂ (i : Fin d), ⋂ (φ : StationaryMFG.Periodic.SmoothPeriodic d),
          { v : XBanach d βBarReal γBarReal |
            periodicIntegral (fun x => DuOf v i x *
              (φ : (Fin d → ℝ) → ℝ) x) =
            - periodicIntegral (fun x => uOf v x *
              ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ :
                  StationaryMFG.Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) } from ?_]
  · -- The intersection of closed sets is closed.
    refine isClosed_iInter (fun i => isClosed_iInter (fun φ => ?_))
    -- The equalizer of two continuous functions to a T2 space is closed.
    refine isClosed_eq ?_ ?_
    · -- LHS: `v ↦ ∫ DuOf v i · φ` is continuous, as the composition
      -- of `v ↦ v.2.2 i` (continuous projection) with the integral
      -- pairing `Lp → ℝ, h ↦ ∫ ⇑h · φ` (continuous since φ is bounded
      -- and the measure is finite).
      have hbdM := smoothPeriodic_bdd_aux (φ := φ)
      obtain ⟨M, hM, hM_bnd⟩ := hbdM
      have h_pair :
          Continuous (fun h : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
                          (Measure.restrict volume (UnitCube d)) =>
            ∫ x, ⇑h x * (φ : (Fin d → ℝ) → ℝ) x
              ∂(Measure.restrict volume (UnitCube d))) :=
        continuous_integral_smul_bounded_aux
          (g := ((φ : (Fin d → ℝ) → ℝ))) M hM
          (φ.smooth.continuous.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun x => hM_bnd x))
      have h_proj := continuous_DuOf_proj
        (βBarReal := βBarReal) (γBarReal := γBarReal) (d := d) i
      -- Compose: `v ↦ ∫ ⇑(v.2.2 i) · φ`.
      have hcomp := h_pair.comp h_proj
      -- Identify the result with `v ↦ ∫ DuOf v i · φ`.
      unfold periodicIntegral
      simp only [DuOf_def]
      exact hcomp
    · -- RHS: `v ↦ - ∫ uOf v · ∂_i φ` is continuous by the same
      -- argument with `∂_i φ` in place of `φ`.
      set ψ : StationaryMFG.Periodic.SmoothPeriodic d :=
        StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ with hψ_def
      have hbdM := smoothPeriodic_bdd_aux (φ := ψ)
      obtain ⟨M, hM, hM_bnd⟩ := hbdM
      have h_pair :
          Continuous (fun h : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
                          (Measure.restrict volume (UnitCube d)) =>
            ∫ x, ⇑h x * (ψ : (Fin d → ℝ) → ℝ) x
              ∂(Measure.restrict volume (UnitCube d))) :=
        continuous_integral_smul_bounded_aux
          (g := ((ψ : (Fin d → ℝ) → ℝ)))
          M hM
          (ψ.smooth.continuous.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun x => hM_bnd x))
      have h_proj := continuous_uOf_proj
        (βBarReal := βBarReal) (γBarReal := γBarReal) (d := d)
      have hcomp := h_pair.comp h_proj
      unfold periodicIntegral
      simp only [uOf_def]
      exact hcomp.neg
  · -- The reformulation of `S_W` as a doubly-indexed intersection.
    ext v
    simp [S_W, Set.mem_iInter]

end S_W_Closedness

/-! ## Norm-closedness of `S_AE` (AEPeriodic-flag set)

Sub-child 1b of `infra-P4-K0_Aepsi_W-norm-closed` (iter-0684 split).

We record the set `S_AE d β γ ⊆ XBanach d β γ` of Banach pairs whose
gradient coordinates `DuOf v i` admit a periodic a.e.-representative
(i.e. `Periodic.AEPeriodic (DuOf v i)` for every `i`), and prove it
is norm-closed.

The closedness here is in fact *trivial*: every gradient coordinate
`DuOf v i = ⇑(v.2.2 i)` is the bare coercion of an `Lp` element on
the unit-cube-restricted Lebesgue measure, and
`Periodic.bareCoeFnOfLpPer` constructs an `AEPeriodicRep` for any
such bare coercion via the `Int.fract`-precomposition trick. So
`Periodic.AEPeriodic (DuOf v i)` holds for *every* `v : XBanach` and
*every* `i`, making `S_AE = Set.univ` and the closedness immediate
from `isClosed_univ`.

This sidesteps the standard
`tendstoInMeasure_of_tendsto_Lp`-plus-subsequence-extraction route
documented in the task spec: the latter route would be necessary if
the gradient components were bare functions without a chosen periodic
representative, but in our `XBanach` setting they are already `Lp`
elements and the periodization primitive is already available. -/

section S_AE_Closedness

open MeasureTheory Set
open StationaryMFG.Periodic

/-- **Auxiliary: every `XBanach` gradient is `AEPeriodic`.** For any
`v : XBanach d β γ` and any `i : Fin d`, the bare function
`DuOf v i = ⇑(v.2.2 i)` admits a periodic a.e.-representative on
the unit cube, constructed by `bareCoeFnOfLpPer` (precomposition
with the coordinate-wise fractional part). -/
lemma aePeriodic_DuOf {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (v : XBanach d βBarReal γBarReal) (i : Fin d) :
    Periodic.AEPeriodic (DuOf v i) := by
  -- `DuOf v i = ⇑(v.2.2 i)` and `v.2.2 i : Lp ℝ γBar μ`. Apply the
  -- `bareCoeFnOfLpPer` primitive to obtain an `AEPeriodicRep`.
  rw [DuOf_def]
  exact ⟨Periodic.bareCoeFnOfLpPer (d := d) (v.2.2 i)⟩

/-- **The `AEPeriodic`-flag set.** Following the iter-0684 split, this
is the slice of `XBanach` recording the existence of a periodic
a.e.-representative for every gradient coordinate. Since the gradient
coordinates are bare coercions of `Lp` elements, the slice is in fact
the whole space (see `S_AE_eq_univ`). -/
def S_AE (d : ℕ) (βBarReal γBarReal : ℝ) :
    Set (XBanach d βBarReal γBarReal) :=
  { v | ∀ i, Periodic.AEPeriodic (DuOf v i) }

/-- Membership unfolding for `S_AE`. -/
lemma mem_S_AE_iff {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal} :
    v ∈ S_AE d βBarReal γBarReal ↔
      ∀ i, Periodic.AEPeriodic (DuOf v i) :=
  Iff.rfl

/-- **`S_AE` is the whole space.** Every `XBanach` pair has periodic
a.e.-representatives in each gradient coordinate, because the gradient
coordinates are bare coercions of `Lp` elements (see
`aePeriodic_DuOf`). -/
lemma S_AE_eq_univ (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    S_AE d βBarReal γBarReal = (Set.univ : Set (XBanach d βBarReal γBarReal)) := by
  ext v
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  intro i
  exact aePeriodic_DuOf v i

/-- **Norm-closedness of `S_AE`.** The set of Banach pairs whose
gradient coordinates admit a periodic a.e.-representative is
norm-closed. Indeed, it is the whole space (see `S_AE_eq_univ`),
because every gradient coordinate is a bare coercion of an `Lp`
element, and `bareCoeFnOfLpPer` provides a periodic
a.e.-representative for every such bare coercion. -/
theorem S_AE_closed (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    IsClosed (S_AE d βBarReal γBarReal) := by
  rw [S_AE_eq_univ]
  exact isClosed_univ

end S_AE_Closedness

/-! ## Weak-derivative-tied refined cones `K_Aepsi_W` / `K0_Aepsi_W`

Per `infra-P4-weak-limit-pointwise-rep`, we localise the per-coordinate
weak-derivative tie between the value component `uOf q` and the
gradient component `DuOf q i` of a Banach pair into the **domain
predicate** itself. The original cones `K_Aepsi`, `K0_Aepsi`
characterise only the (strict / non-strict) positivity of the
`m`-component; the refined variants `K_Aepsi_W`, `K0_Aepsi_W` add the
weak-derivative tie, packaged with an `AEPeriodic` flag on each
gradient component (the Prop-flavour of the `AEPeriodicRep` interface
in `Periodic/Lp.lean`). Downstream consumers that previously took the
tie as a parameter can project it out of refined-cone membership.

The refinement is *additive*: the existing `K_Aepsi`, `K0_Aepsi`,
their convexity / closedness lemmas, and the abstract-operator lifts
they support remain unchanged. The refined cones plug in as a
**strengthening** at the producer interface only. -/

/-- **Refined strict-positivity cone.** Membership in `K_Aepsi_W`
asserts both the strict-positivity condition of `K_Aepsi` and the
per-coordinate weak-derivative tie. We use a Prop-shaped
conjunction (the `AEPeriodic` Prop alias plus `HasWeakDerivPer`) so
that membership is definitionally a `Prop`; the data-form
`WeakDerivTieData` is recovered by `Classical.choice` only when a
chosen `AEPeriodicRep` is needed downstream. -/
def K_Aepsi_W (d : ℕ) (βBarReal γBarReal : ℝ) :
    Set (XBanach d βBarReal γBarReal) :=
  { v |
      v ∈ K_Aepsi d βBarReal γBarReal
        ∧ (∀ i, Periodic.AEPeriodic (DuOf v i))
        ∧ (∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i)) }

/-- **Refined non-negativity cone.** Membership in `K0_Aepsi_W`
asserts both the non-negativity condition of `K0_Aepsi` and the
per-coordinate weak-derivative tie. -/
def K0_Aepsi_W (d : ℕ) (βBarReal γBarReal : ℝ) :
    Set (XBanach d βBarReal γBarReal) :=
  { v |
      v ∈ K0_Aepsi d βBarReal γBarReal
        ∧ (∀ i, Periodic.AEPeriodic (DuOf v i))
        ∧ (∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i)) }

/-- **Membership unfolding for `K_Aepsi_W`.** -/
lemma mem_K_Aepsi_W_iff {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal} :
    v ∈ K_Aepsi_W d βBarReal γBarReal ↔
      v ∈ K_Aepsi d βBarReal γBarReal
        ∧ (∀ i, Periodic.AEPeriodic (DuOf v i))
        ∧ (∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i)) :=
  Iff.rfl

/-- **Membership unfolding for `K0_Aepsi_W`.** -/
lemma mem_K0_Aepsi_W_iff {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal} :
    v ∈ K0_Aepsi_W d βBarReal γBarReal ↔
      v ∈ K0_Aepsi d βBarReal γBarReal
        ∧ (∀ i, Periodic.AEPeriodic (DuOf v i))
        ∧ (∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i)) :=
  Iff.rfl

/-- **Refined cone is contained in the unrefined one** (positivity
projection). -/
lemma K_Aepsi_W_subset_K_Aepsi (d : ℕ) (βBarReal γBarReal : ℝ) :
    K_Aepsi_W d βBarReal γBarReal ⊆ K_Aepsi d βBarReal γBarReal :=
  fun _ hv => hv.1

/-- **Refined non-neg cone is contained in the unrefined one**
(non-negativity projection). -/
lemma K0_Aepsi_W_subset_K0_Aepsi (d : ℕ) (βBarReal γBarReal : ℝ) :
    K0_Aepsi_W d βBarReal γBarReal ⊆ K0_Aepsi d βBarReal γBarReal :=
  fun _ hv => hv.1

/-- **Refined strict-positivity cone is contained in the refined
non-negativity cone.** -/
lemma K_Aepsi_W_subset_K0_Aepsi_W (d : ℕ) (βBarReal γBarReal : ℝ) :
    K_Aepsi_W d βBarReal γBarReal ⊆ K0_Aepsi_W d βBarReal γBarReal := by
  intro v hv
  refine ⟨?_, hv.2.1, hv.2.2⟩
  exact K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal hv.1

/-! ### Convexity of the refined cone `K_Aepsi_W`

Step 0 of the iter-0694 five-child split of
`paperSolFor-final-phase5-hWeakDeriv-refined-domain-final`. The
refined-domain Browder–Minty path needs to run
`Monotone.monotone_abstract_weak` on `K_Aepsi_W` rather than the
plain `K_Aepsi`; that call requires convexity of the domain. We
derive it via the same decomposition used for
`K0_Aepsi_W_closed`:

  `K_Aepsi_W = K_Aepsi ∩ S_AE ∩ S_W`

* `K_Aepsi_convex` is the existing strict-positivity-cone
  convexity (`Banach/AbstractLifts.lean:288`).
* `S_AE` is the whole space (`S_AE_eq_univ`), hence trivially
  convex.
* `S_W` is convex because the IBP test-integral identity is
  linear in both `(uOf v, DuOf v)` (the Lp coercions of the
  convex combination a.e.-equal the convex combination of
  coercions; the integrand is multiplied by a fixed test
  function, so linearity of the integral closes the loop). -/

section K_Aepsi_W_Convexity

open MeasureTheory

/-- **Convexity of `S_AE`.** Trivial since `S_AE = Set.univ`. -/
lemma S_AE_convex (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    Convex ℝ (S_AE d βBarReal γBarReal) := by
  rw [S_AE_eq_univ]
  exact convex_univ

/-- **Auxiliary: linearity of the bounded `Lp`-pairing.** For a finite
measure `μ`, exponent `p ≥ 1`, and a bounded measurable `g : α → ℝ`,
the map `f ↦ ∫ ⇑f · g` is linear in `f : Lp ℝ p μ`. Concretely:

`∫ ⇑(a • f₁ + b • f₂) · g = a * ∫ ⇑f₁ · g + b * ∫ ⇑f₂ · g`. -/
private lemma integral_pairing_linear_aux
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : α → ℝ) (M : ℝ)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g μ)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ M)
    (a b : ℝ) (f₁ f₂ : MeasureTheory.Lp ℝ p μ) :
    ∫ x, ⇑(a • f₁ + b • f₂) x * g x ∂μ =
      a * (∫ x, ⇑f₁ x * g x ∂μ) + b * (∫ x, ⇑f₂ x * g x ∂μ) := by
  classical
  -- a.e. rewrite of the integrand via `Lp.coeFn_add` and `Lp.coeFn_smul`.
  have h_add := MeasureTheory.Lp.coeFn_add (a • f₁) (b • f₂)
  have h_s1 := MeasureTheory.Lp.coeFn_smul a f₁
  have h_s2 := MeasureTheory.Lp.coeFn_smul b f₂
  have hpt : (fun x => ⇑(a • f₁ + b • f₂) x * g x)
      =ᵐ[μ]
        (fun x => a * (⇑f₁ x * g x) + b * (⇑f₂ x * g x)) := by
    filter_upwards [h_add, h_s1, h_s2] with x hx_add hx_s1 hx_s2
    rw [hx_add, Pi.add_apply, hx_s1, hx_s2, Pi.smul_apply, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul]
    ring
  -- Integrability of `⇑fⱼ * g` from `fⱼ ∈ L¹` (Lp on finite measure)
  -- and boundedness of `g`.
  have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hf₁_L1 : Integrable (⇑f₁) μ :=
    (memLp_one_iff_integrable).1 ((MeasureTheory.Lp.memLp f₁).mono_exponent hp_one)
  have hf₂_L1 : Integrable (⇑f₂) μ :=
    (memLp_one_iff_integrable).1 ((MeasureTheory.Lp.memLp f₂).mono_exponent hp_one)
  have h_int_f₁ : Integrable (fun x => ⇑f₁ x * g x) μ :=
    hf₁_L1.mul_bdd hg_meas hg_bound
  have h_int_f₂ : Integrable (fun x => ⇑f₂ x * g x) μ :=
    hf₂_L1.mul_bdd hg_meas hg_bound
  -- Compute via `integral_congr_ae`, then linearity.
  calc ∫ x, ⇑(a • f₁ + b • f₂) x * g x ∂μ
      = ∫ x, a * (⇑f₁ x * g x) + b * (⇑f₂ x * g x) ∂μ :=
        integral_congr_ae hpt
    _ = (∫ x, a * (⇑f₁ x * g x) ∂μ) + (∫ x, b * (⇑f₂ x * g x) ∂μ) :=
        integral_add (h_int_f₁.const_mul a) (h_int_f₂.const_mul b)
    _ = a * (∫ x, ⇑f₁ x * g x ∂μ) + b * (∫ x, ⇑f₂ x * g x ∂μ) := by
        rw [integral_const_mul, integral_const_mul]

/-- **Convexity of `S_W`.** For `v₁, v₂ ∈ S_W` and `a, b ≥ 0` with
`a + b = 1`, the convex combination `a • v₁ + b • v₂` again satisfies
the per-coordinate IBP identity. The proof uses linearity of the
integral pairing `Lp → ℝ, f ↦ ∫ ⇑f · g` for bounded test `g`, applied
at `g = φ` (for the LHS) and `g = ∂_i φ` (for the RHS). -/
lemma S_W_convex (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    Convex ℝ (S_W d βBarReal γBarReal) := by
  rw [convex_iff_add_mem]
  intro v₁ hv₁ v₂ hv₂ a b _ha _hb _hab
  intro i φ
  -- Bound `‖φ‖ ≤ M` and `‖∂ᵢ φ‖ ≤ N` on the cube via boundedness aux.
  obtain ⟨M, _hM, hM_bnd⟩ := smoothPeriodic_bdd_aux (φ := φ)
  set ψ : StationaryMFG.Periodic.SmoothPeriodic d :=
    StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ with hψ_def
  obtain ⟨N, _hN, hN_bnd⟩ := smoothPeriodic_bdd_aux (φ := ψ)
  -- Identify `(a • v₁ + b • v₂).2.2 i` and `.2.1` with the convex combos.
  have h_DuSum :
      ((a • v₁ + b • v₂).2.2 i
        : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
            (Measure.restrict volume (UnitCube d)))
        = a • v₁.2.2 i + b • v₂.2.2 i := rfl
  have h_uSum :
      ((a • v₁ + b • v₂).2.1
        : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
            (Measure.restrict volume (UnitCube d)))
        = a • v₁.2.1 + b • v₂.2.1 := rfl
  -- LHS linearity: `∫ DuOf v i · φ = a * ∫ DuOf v₁ i · φ + b * ∫ DuOf v₂ i · φ`.
  have h_lin_LHS :
      ∫ x, DuOf (a • v₁ + b • v₂) i x * (φ : (Fin d → ℝ) → ℝ) x
          ∂(Measure.restrict volume (UnitCube d))
        = a * (∫ x, DuOf v₁ i x * (φ : (Fin d → ℝ) → ℝ) x
            ∂(Measure.restrict volume (UnitCube d)))
          + b * (∫ x, DuOf v₂ i x * (φ : (Fin d → ℝ) → ℝ) x
            ∂(Measure.restrict volume (UnitCube d))) := by
    simp only [DuOf_def]
    rw [h_DuSum]
    exact integral_pairing_linear_aux
      (g := ((φ : (Fin d → ℝ) → ℝ))) M
      (φ.smooth.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => hM_bnd x))
      a b (v₁.2.2 i) (v₂.2.2 i)
  -- RHS linearity (without the minus sign).
  have h_lin_RHS_inner :
      ∫ x, uOf (a • v₁ + b • v₂) x * (ψ : (Fin d → ℝ) → ℝ) x
          ∂(Measure.restrict volume (UnitCube d))
        = a * (∫ x, uOf v₁ x * (ψ : (Fin d → ℝ) → ℝ) x
            ∂(Measure.restrict volume (UnitCube d)))
          + b * (∫ x, uOf v₂ x * (ψ : (Fin d → ℝ) → ℝ) x
            ∂(Measure.restrict volume (UnitCube d))) := by
    simp only [uOf_def]
    rw [h_uSum]
    exact integral_pairing_linear_aux
      (g := ((ψ : (Fin d → ℝ) → ℝ))) N
      (ψ.smooth.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => hN_bnd x))
      a b (v₁.2.1) (v₂.2.1)
  -- Unfold `periodicIntegral`, then assemble.
  unfold periodicIntegral
  rw [h_lin_LHS]
  -- The IBP identity for `v₁`, `v₂`.
  have hv₁_ibp := hv₁ i φ
  have hv₂_ibp := hv₂ i φ
  unfold periodicIntegral at hv₁_ibp hv₂_ibp
  rw [hv₁_ibp, hv₂_ibp]
  -- Now: `a * (-X₁) + b * (-X₂) = -(a*X₁ + b*X₂) = -[a*X₁ + b*X₂]`.
  -- RHS goal becomes `-∫ uOf (a•v₁+b•v₂) · ∂ᵢφ`, and `h_lin_RHS_inner`
  -- expresses that integral as `a * Y₁ + b * Y₂`.
  rw [← hψ_def, h_lin_RHS_inner]
  ring

/-- **Convexity of the refined cone `K_Aepsi_W`.** Decompose
`K_Aepsi_W = K_Aepsi ∩ S_AE ∩ S_W` (analogous to the closedness
decomposition in `K0_Aepsi_W_closed`), then combine
`K_Aepsi_convex`, `S_AE_convex`, `S_W_convex` via `Convex.inter`.

This is Step 0 of the iter-0694 five-child split required for the
refined-domain Browder–Minty path
(`Monotone.monotone_abstract_weak` on `K_Aepsi_W`). -/
theorem K_Aepsi_W_convex (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    Convex ℝ (K_Aepsi_W d βBarReal γBarReal) := by
  have h_eq :
      K_Aepsi_W d βBarReal γBarReal
        = (K_Aepsi d βBarReal γBarReal ∩ S_AE d βBarReal γBarReal)
            ∩ S_W d βBarReal γBarReal := by
    ext v
    simp only [Set.mem_inter_iff, mem_K_Aepsi_W_iff, mem_S_AE_iff,
               mem_S_W_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun i φ => (h3 i).2 φ⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun i => ⟨?_, fun φ => h3 i φ⟩⟩
      -- `MemLpPer 1 (DuOf v i)` is automatic on the finite-measure
      -- cube with `γBar ≥ 1`.
      have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
      exact StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d) (v.2.2 i))
  rw [h_eq]
  exact (K_Aepsi_convex d βBarReal γBarReal |>.inter
          (S_AE_convex d βBarReal γBarReal)).inter
        (S_W_convex d βBarReal γBarReal)

end K_Aepsi_W_Convexity

/-! ### Norm-closedness of the refined cone `K0_Aepsi_W`

Iter-0688 in-line re-assembly of `infra-P4-K0_Aepsi_W-norm-closed`
(the parent of `S_W_closed` / `S_AE_closed`). The refined cone
decomposes as `K0_Aepsi_W = K0_Aepsi ∩ S_AE ∩ S_W`: positivity from
`K0_Aepsi`, AEPeriodic flags on each gradient coordinate from `S_AE`,
and the IBP half of `HasWeakDerivPer` from `S_W`. The remaining
`MemLpPer 1 (DuOf v i)` half of `HasWeakDerivPer` is automatic for
every `v : XBanach` because `DuOf v i = ⇑(v.2.2 i)` with
`v.2.2 i ∈ Lp ℝ (ENNReal.ofReal γBarReal) μ` and the finite-measure
embedding `L^γBar ↪ L^1` (via `memLpPer_one_of_mono`,
`memLpPer_of_lpPer`). -/

/-- **Norm-closedness of `K0_Aepsi_W`.** Direct intersection of the
three closed slices `K0_Aepsi`, `S_AE`, `S_W`, with the automatic
`MemLpPer 1`-half absorbed via `memLpPer_one_of_mono`. -/
theorem K0_Aepsi_W_closed (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    IsClosed (K0_Aepsi_W d βBarReal γBarReal) := by
  have h0 := K0_Aepsi_closed d βBarReal γBarReal
  have hAE := S_AE_closed d βBarReal γBarReal
  have hW := S_W_closed d βBarReal γBarReal
  have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
  have h_eq :
      K0_Aepsi_W d βBarReal γBarReal
        = (K0_Aepsi d βBarReal γBarReal ∩ S_AE d βBarReal γBarReal)
            ∩ S_W d βBarReal γBarReal := by
    ext v
    simp only [Set.mem_inter_iff, mem_K0_Aepsi_W_iff, mem_S_AE_iff,
               mem_S_W_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun i φ => (h3 i).2 φ⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun i => ⟨?_, fun φ => h3 i φ⟩⟩
      -- `MemLpPer 1 (DuOf v i)` is automatic: `DuOf v i = ⇑(v.2.2 i)`
      -- with `v.2.2 i ∈ Lp ℝ γBar μ` and `γBar ≥ 1`, finite measure.
      exact StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d) (v.2.2 i))
  rw [h_eq]
  exact (h0.inter hAE).inter hW

/-- **Closure of `K0_Aepsi_W` lies inside `K0_Aepsi_W`** — immediate
from norm-closedness via `IsClosed.closure_subset`. -/
theorem K0_Aepsi_W_closure_subset (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    closure (K0_Aepsi_W d βBarReal γBarReal)
      ⊆ K0_Aepsi_W d βBarReal γBarReal :=
  (K0_Aepsi_W_closed d βBarReal γBarReal).closure_subset

/-- **Two-domain bridge for the refined cones:
`closure (K_Aepsi_W) ⊆ K0_Aepsi_W`.**

Refined analogue of `K_Aepsi_closure_subset_K0_Aepsi` (line 345 of
`Banach/AbstractLifts.lean`). Compose monotonicity of `closure` with
`K_Aepsi_W ⊆ K0_Aepsi_W` and norm-closedness of `K0_Aepsi_W`.

This is the descent route used by the refined-witness producer to
send a Browder–Minty witness `q ∈ closure (K_Aepsi_W)` to a
`K0_Aepsi_W` membership. -/
theorem K_Aepsi_W_closure_subset_K0_Aepsi_W (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    closure (K_Aepsi_W d βBarReal γBarReal)
      ⊆ K0_Aepsi_W d βBarReal γBarReal := by
  intro q hq
  have h_mono :
      closure (K_Aepsi_W d βBarReal γBarReal)
        ⊆ closure (K0_Aepsi_W d βBarReal γBarReal) :=
    closure_mono (K_Aepsi_W_subset_K0_Aepsi_W d βBarReal γBarReal)
  exact K0_Aepsi_W_closure_subset d βBarReal γBarReal (h_mono hq)

/-! ## Refined-domain abstract-VI context `AepsiUniformContextK_W`

Step 2 of the iter-0694 five-child split of
`paperSolFor-final-phase5-hWeakDeriv-refined-domain-final`. This
section provides the **refined-domain companion** to
`AepsiUniformContextK` / `exists_banachVI_at_eps_KAepsi`: the
abstract-VI context and Browder–Minty producer are now typed at the
refined strict-positivity cone `K_Aepsi_W`, which encodes the
per-coordinate `AEPeriodic` flags and weak-derivative ties in
addition to strict positivity.

The two-domain pattern is preserved: the internal Browder–Minty call
runs on `K_Aepsi_W` (convex by `K_Aepsi_W_convex`, iter 0695), and the
witness is descended from `closure (K_Aepsi_W)` into `K0_Aepsi_W` via
the bridge `K_Aepsi_W_closure_subset_K0_Aepsi_W` (just above). The
public conclusion therefore lands at `K0_Aepsi_W` membership, which —
unlike `K0_Aepsi` — carries the weak-derivative tie by projection
(`hasWeakDerivPer_of_mem_K0_Aepsi_W`), so the refined context drops
the `hWeakDeriv` field entirely.

Coercivity on `K_Aepsi_W` transfers trivially from `K_Aepsi` via the
inclusion `K_Aepsi_W ⊆ K_Aepsi` (`K_Aepsi_W_subset_K_Aepsi`) when
needed by an assembler, but the producer itself accepts `hCoerc`
directly on `K_Aepsi_W`. -/

/-- **Refined-domain abstract-VI context record.**

Companion of `AepsiUniformContextK` typed at the refined cone
`K_Aepsi_W` (instead of `K_Aepsi`). The aux supplier `auxHypsK` is
indexed at `K_Aepsi_W`, which is a strict strengthening of the domain
(every `K_Aepsi`-indexed supplier specialises to a `K_Aepsi_W`-indexed
one via `K_Aepsi_W_subset_K_Aepsi`). The base point `qRef` and the
three Browder–Minty hypotheses `hMono` / `hHC` / `hCoerc` are all
asserted on `K_Aepsi_W`. The `aux` field is the uniform aux record at
the refined non-negativity cone `K0_Aepsi_W`.

There is **no** `hWeakDeriv` field: the weak-derivative tie is
recovered from refined-cone membership by direct projection (see
`hasWeakDerivPer_of_mem_K0_Aepsi_W`). This is the principal
simplification justifying the refinement. -/
structure AepsiUniformContextK_W
    (d : ℕ) (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] : Type where
  /-- Reflexivity of the Banach pair (Phase 1). -/
  hReflexive : IsReflexiveNormedSpace (XBanach d βBarReal γBarReal)
  /-- **K_Aepsi-indexed aux supplier** for the totalized CLM family
  `Aepsi_CLM_opK`. The supplier is typed at the (larger) strict-positivity
  cone `K_Aepsi` because that is what `Aepsi_CLM_opK` consumes (see
  `Banach/AbstractLifts.lean:1267`); every `K_Aepsi`-indexed supplier
  trivially restricts to a `K_Aepsi_W`-indexed one via the inclusion
  `K_Aepsi_W ⊆ K_Aepsi` (`K_Aepsi_W_subset_K_Aepsi`). The refinement
  to `K_Aepsi_W` happens on the Browder–Minty side (`hMono`, `hHC`,
  `hCoerc`), not on the aux supplier. -/
  auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
              MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1)
  /-- The Browder–Minty base point. -/
  qRef : XBanach d βBarReal γBarReal
  /-- The base point lies in the refined strict-positivity cone
  `K_Aepsi_W`. -/
  hqRef : qRef ∈ K_Aepsi_W d βBarReal γBarReal
  /-- The K0_Aepsi_W-restricted uniform aux record. -/
  aux : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal
            βBarReal' γBarReal' (K0_Aepsi_W d βBarReal γBarReal)
  /-- Monotonicity of `Aepsi_CLM_opK auxHypsK ε` on `K_Aepsi_W`. -/
  hMono : IsMonotone (X := XBanach d βBarReal γBarReal)
            (K_Aepsi_W d βBarReal γBarReal)
            (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHypsK ε)
  /-- Hemicontinuity of `Aepsi_CLM_opK auxHypsK ε` on `K_Aepsi_W`. -/
  hHC : IsHemicontinuous (X := XBanach d βBarReal γBarReal)
          (K_Aepsi_W d βBarReal γBarReal)
          (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V H DpH auxHypsK ε)
  /-- Coercivity of `Aepsi_CLM_opK auxHypsK ε` at `qRef` on
  `K_Aepsi_W`. -/
  hCoerc : IsCoerciveAt (X := XBanach d βBarReal γBarReal)
              (K_Aepsi_W d βBarReal γBarReal)
              (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHypsK ε)
              qRef

/-- **Refined-domain Browder–Minty producer.**

Apply `Monotone.monotone_abstract_weak` to `Aepsi_CLM_opK auxHypsK ε`
on the refined strict-positivity cone `K_Aepsi_W` (convex by
`K_Aepsi_W_convex`, iter 0695), and descend the witness from
`closure (K_Aepsi_W)` into `K0_Aepsi_W` via
`K_Aepsi_W_closure_subset_K0_Aepsi_W` (iter 0688).

The conclusion exposes:

* `q ∈ K0_Aepsi_W` — the refined non-negativity-cone membership,
  which entails the weak-derivative tie by direct projection.
* For every test point `q' ∈ K_Aepsi_W`, the weak-VI inequality
  `0 ≤ Aepsi_CLM_opK auxHypsK ε q' (q' - q)`.

This is the refined-domain analogue of
`exists_banachVI_at_eps_KAepsi`. The `hWeakDeriv` field is no longer
threaded as a residue — refined-cone membership carries it
structurally. -/
theorem exists_banachVI_at_eps_KAepsi_W
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (_hε : 0 < ε)
    (ctx : AepsiUniformContextK_W (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal') :
    ∃ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH ctx.auxHypsK ε q' (q' - q) := by
  -- Apply Browder–Minty on the refined cone `K_Aepsi_W` (convex by
  -- iter 0695).
  have h_cvx : Convex ℝ (K_Aepsi_W d βBarReal γBarReal) :=
    K_Aepsi_W_convex d βBarReal γBarReal
  obtain ⟨q, hq_closure, hVI⟩ :=
    Monotone.monotone_abstract_weak (X := XBanach d βBarReal γBarReal)
      ctx.hReflexive h_cvx ctx.hMono ctx.hCoerc
  -- Descend `closure (K_Aepsi_W) ⊆ K0_Aepsi_W` via the refined
  -- two-domain bridge (iter 0688).
  have hq_K0W : q ∈ K0_Aepsi_W d βBarReal γBarReal :=
    K_Aepsi_W_closure_subset_K0_Aepsi_W d βBarReal γBarReal hq_closure
  exact ⟨q, hq_K0W, hVI⟩

/-- **Sanity-check `example`.** The refined-domain producer
`exists_banachVI_at_eps_KAepsi_W` accepts an
`AepsiUniformContextK_W` and delivers a `K0_Aepsi_W`-membership
witness together with the `K_Aepsi_W`-form weak-VI inequality. -/
example
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hε : 0 < ε)
    (ctx : AepsiUniformContextK_W (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal') :
    ∃ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH ctx.auxHypsK ε q' (q' - q) :=
  exists_banachVI_at_eps_KAepsi_W hε ctx

/-- **Weak-derivative-tie projection from `K0_Aepsi_W`.** -/
lemma hasWeakDerivPer_of_mem_K0_Aepsi_W
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal}
    (hv : v ∈ K0_Aepsi_W d βBarReal γBarReal) :
    ∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i) :=
  hv.2.2

/-- **AEPeriodic projection from `K0_Aepsi_W`.** -/
lemma aePeriodic_DuOf_of_mem_K0_Aepsi_W
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal}
    (hv : v ∈ K0_Aepsi_W d βBarReal γBarReal) :
    ∀ i, Periodic.AEPeriodic (DuOf v i) :=
  hv.2.1

/-- **Refined-cone constructor.** Build a `K0_Aepsi_W` membership
from a `K0_Aepsi` membership plus the per-coordinate weak-derivative
tie and `AEPeriodic` flags. -/
lemma mem_K0_Aepsi_W_of_K0_Aepsi
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal}
    (hv : v ∈ K0_Aepsi d βBarReal γBarReal)
    (hAE : ∀ i, Periodic.AEPeriodic (DuOf v i))
    (hWeak : ∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i)) :
    v ∈ K0_Aepsi_W d βBarReal γBarReal :=
  ⟨hv, hAE, hWeak⟩

/-- **Refined strict-positivity-cone constructor.** -/
lemma mem_K_Aepsi_W_of_K_Aepsi
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : XBanach d βBarReal γBarReal}
    (hv : v ∈ K_Aepsi d βBarReal γBarReal)
    (hAE : ∀ i, Periodic.AEPeriodic (DuOf v i))
    (hWeak : ∀ i, HasWeakDerivPer (d := d) i (uOf v) (DuOf v i)) :
    v ∈ K_Aepsi_W d βBarReal γBarReal :=
  ⟨hv, hAE, hWeak⟩

/-- Sanity check: the projection `K0_Aepsi_W → HasWeakDerivPer`
type-checks (this is the principal use of the refinement
downstream). -/
example (d : ℕ) (βBarReal γBarReal : ℝ)
    (q : XBanach d βBarReal γBarReal)
    (hq : q ∈ K0_Aepsi_W d βBarReal γBarReal) :
    ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i) :=
  hasWeakDerivPer_of_mem_K0_Aepsi_W hq

/-- Sanity check: the projection `K0_Aepsi_W → K0_Aepsi` type-checks. -/
example (d : ℕ) (βBarReal γBarReal : ℝ)
    (q : XBanach d βBarReal γBarReal)
    (hq : q ∈ K0_Aepsi_W d βBarReal γBarReal) :
    q ∈ K0_Aepsi d βBarReal γBarReal :=
  K0_Aepsi_W_subset_K0_Aepsi d βBarReal γBarReal hq

/-- **Refined-record constructor for `RegularizedBareSolution`.**

Given a Banach pair `q ∈ K0_Aepsi_W` (i.e., a non-negativity-cone
element with the per-coordinate weak-derivative tie), the bare-
function projections `(mOf q, uOf q, DuOf q)` carry the `hWeakDeriv`
field of `RegularizedBareSolution` directly from refined-cone
membership — no residue parameter. The `MemLpPer` certificates come
from the `Lp` components via `memLpPer_of_lpPer`; the non-negativity
comes from `K0_Aepsi` membership.

This is the projection used by the bare-bridging producer chain when
the witness is delivered as a refined-cone element. The remaining
fields (`hInt`, three `hVIeps_*` families) are the analytic content
of the producer and are not affected by the refinement. -/
lemma hasWeakDerivPer_of_K0_Aepsi_W_witness
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {q : XBanach d βBarReal γBarReal}
    (hq : q ∈ K0_Aepsi_W d βBarReal γBarReal) :
    ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i) :=
  hasWeakDerivPer_of_mem_K0_Aepsi_W hq

/-- **Feeder 5 / weak-derivative tie (discharged form, refined cone).**

Per `infra-P4-weak-limit-pointwise-rep` (this task), the
weak-derivative tie between the value and gradient components of a
Banach pair is now packaged into the **refined non-negativity cone**
`K0_Aepsi_W` (defined in `Banach/AbstractLifts.lean`), which
strengthens `K0_Aepsi` with the per-coordinate `HasWeakDerivPer` tie
plus an `AEPeriodicRep` flag on each gradient component. Membership
in the refined cone yields the tie by direct projection
(`hasWeakDerivPer_of_mem_K0_Aepsi_W`), so this feeder no longer needs
to take the tie as a residue parameter.

The conclusion is now stated on the *refined* cone `K0_Aepsi_W`, so
downstream consumers thread refined-cone membership through the chain
instead of the residue. The legacy form
`aepsi_weakDerivTie_of_paperHypotheses_legacy` (preserved below) takes
the residue parameter and delivers the same conclusion on the
unrefined `K0_Aepsi`; it remains available for migration purposes
during the cascade rollout but is no longer the headline form.

Note: the K0-form composition theorem
`aepsiUniformContext_of_paperHypotheses_closed` that previously
chained this feeder with the K0-form `Aepsi_*_of_paperHypotheses`
feeders was deleted in the two-domain redesign child E
(`infra-P4-two-domain-redesign-E-delete-K0-form-lifts`). -/
theorem aepsi_weakDerivTie_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal')) :
    ∀ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i) :=
  fun _q hq => hasWeakDerivPer_of_mem_K0_Aepsi_W hq

/-- **Legacy feeder-5 form.** Identity bridge from a per-K0 residue
to the `hWeakDeriv` conclusion on the *unrefined* `K0_Aepsi`. Kept
during the cascade migration; new producer chains use the discharged
form `aepsi_weakDerivTie_of_paperHypotheses` above (which consumes
`K0_Aepsi_W` instead of the residue). -/
theorem aepsi_weakDerivTie_of_paperHypotheses_legacy
    {d : ℕ}
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hWeakDeriv :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i) :=
  hWeakDeriv

/-- **Sanity-check `example`.** The discharged form derives the
weak-derivative tie at every `K0_Aepsi_W` element with no residue
parameter. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (q : XBanach d βBarReal γBarReal)
    (hq : q ∈ K0_Aepsi_W d βBarReal γBarReal) :
    ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i) :=
  aepsi_weakDerivTie_of_paperHypotheses (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal')
    hmon hpow hV hExp q hq

/-! ## Producer: `exists_regularizedBareSolution_K_W` (refined-cone consumer)

Step 3 of the iter-0694 five-child split of
`paperSolFor-final-phase5-hWeakDeriv-refined-domain-final`. This is
the refined-cone sibling of `exists_regularizedBareSolution_K`: it
consumes the refined-domain abstract-VI context
`AepsiUniformContextK_W` (Step 2) and recovers the weak-derivative
tie by projection from `K0_Aepsi_W`-membership
(`hasWeakDerivPer_of_mem_K0_Aepsi_W`), with no `hWeakDeriv` auth
parameter on the context record. The witness is delivered by
`exists_banachVI_at_eps_KAepsi_W` (Step 2), whose conclusion lands at
`q ∈ K0_Aepsi_W` (refined non-negativity cone), and the abstract-VI
hypothesis quantifies over test points `q' ∈ K_Aepsi_W` (refined
strict-positivity cone).

The five `hMinty_*` authorised inputs are retyped so that:
* the witness `q` is fed at `K0_Aepsi_W` membership rather than
  `K0_Aepsi`,
* the abstract-VI hypothesis quantifies test points on `K_Aepsi_W`
  rather than `K_Aepsi`.

The `Aepsi_CLM_opK` shape itself is unchanged: per Step-2 design,
`ctx.auxHypsK` still has type at `K_Aepsi` (an API constraint from
`Aepsi_CLM_opK` consuming the unrefined cone, see
`Banach/AbstractLifts.lean:1267`); every `K_Aepsi`-indexed supplier
specialises to a `K_Aepsi_W`-indexed one via the inclusion. -/

/-- **T4 bare-bridging producer (refined-cone input).**

Refined-cone sibling of `exists_regularizedBareSolution_K`. Consumes
`AepsiUniformContextK_W` (the refined-domain context from Step 2)
and applies `exists_banachVI_at_eps_KAepsi_W` to extract a witness
with `K0_Aepsi_W`-membership; the weak-derivative tie is recovered
by projection (`hasWeakDerivPer_of_mem_K0_Aepsi_W`), not as an auth
parameter on the context. The five Minty/δ-limit conclusions are
the authorised inputs, indexed at the specific witness `q` extracted
internally by Browder–Minty and retyped at the refined cones. -/
theorem exists_regularizedBareSolution_K_W
    {d : ℕ} {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hε : 0 < ε)
    (ctx : AepsiUniformContextK_W (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    -- Authorised input: per-family Minty/δ-limit conclusions, indexed
    -- at the *specific witness* `q` extracted internally by
    -- Browder–Minty, retyped at the refined cones (`K0_Aepsi_W` for
    -- the witness, `K_Aepsi_W` for the test side).
    (hMinty_set :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi_W d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  Dυ (S.indicator ρ) υ
                  (fun i x => Dυ i x - DuOf q i x)
                  (S.indicator ρ - mOf q) (υ - uOf q))
    (hMinty_signed :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi_W d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  (DuOf q)
                  (fun x => mOf q x + σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (uOf q)
                  (fun _ _ => (0 : ℝ))
                  (fun x => σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun _ => (0 : ℝ)))
    (hMinty_transport :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi_W d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (φ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  φ σ υ
                  (fun i x => φ i x - DuOf q i x)
                  (σ - mOf q) (υ - uOf q))
    (hMinty_signed_user_probe :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi_W d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
            0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε
                  Dυ
                  (fun x => mOf q x + σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  υ
                  (fun i x => Dυ i x - DuOf q i x)
                  (fun x => σ * mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun x => υ x - uOf q x))
    (hMinty_signed_user_triple :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi_W d βBarReal γBarReal →
        (∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
            0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH ctx.auxHypsK ε q' (q' - q)) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
          (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
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
                  (fun x => υ x - uOf q x))
    :
    Nonempty (RegularizedBareSolution d ε V H DpH γBarReal βBarReal
                βBarReal' γBarReal') := by
  -- Extract the refined-domain abstract-VI witness; the witness lands
  -- in `K0_Aepsi_W` via the closure inclusion
  -- `K_Aepsi_W_closure_subset_K0_Aepsi_W` already discharged inside
  -- `exists_banachVI_at_eps_KAepsi_W`.
  obtain ⟨q, hq_K0W, hVI⟩ := exists_banachVI_at_eps_KAepsi_W hε ctx
  -- Bare-function projections.
  set m : (Fin d → ℝ) → ℝ := mOf q with hm_def
  set u : (Fin d → ℝ) → ℝ := uOf q with hu_def
  set Du : Fin d → (Fin d → ℝ) → ℝ := DuOf q with hDu_def
  -- `MemLpPer` certificates from the Lp components of `q`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) m :=
    memLpPer_of_lpPer (d := d) q.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) u :=
    memLpPer_of_lpPer (d := d) q.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du i) := by
    intro i
    exact memLpPer_of_lpPer (d := d) (q.2.2 i)
  -- **Weak-derivative certificate by projection from `K0_Aepsi_W`-
  -- membership** — this is the principal simplification of Step 3:
  -- no auth parameter, no `ctx.hWeakDeriv` field.
  have hWeakDeriv : ∀ i, HasWeakDerivPer (d := d) i u (Du i) :=
    hasWeakDerivPer_of_mem_K0_Aepsi_W hq_K0W
  -- AE-periodicity certificates (Phase 2a iter 2), derived structurally
  -- from `Periodic.bareCoeFnOfLpPer`.
  have hu_per : StationaryMFG.Periodic.AEPeriodic u :=
    ⟨StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) q.2.1⟩
  have hDu_per : ∀ i, StationaryMFG.Periodic.AEPeriodic (Du i) := fun i =>
    ⟨StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (q.2.2 i)⟩
  -- Non-negativity from refined-cone membership (`K0_Aepsi_W ⊆ K0_Aepsi`).
  have hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal :=
    K0_Aepsi_W_subset_K0_Aepsi d βBarReal γBarReal hq_K0W
  have hmNonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                    0 ≤ m x := hq_K0
  -- Integrability bundle from `ctx.aux.of_mem` (typed at `K0_Aepsi_W`).
  have hInt : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                V H DpH Du m u :=
    ctx.aux.of_mem q hq_K0W
  -- Assemble using the five authorised Minty/δ-limit inputs at the
  -- specific witness `(q, hq_K0W, hVI)`.
  exact ⟨{
    m := m
    u := u
    Du := Du
    hmLp := hmLp
    huLp := huLp
    hDuLp := hDuLp
    hWeakDeriv := hWeakDeriv
    hu_per := hu_per
    hDu_per := hDu_per
    hmNonneg := hmNonneg
    hInt := hInt
    hVIeps_set := hMinty_set q hq_K0W hVI
    hVIeps_signed := hMinty_signed q hq_K0W hVI
    hVIeps_signed_user_probe := hMinty_signed_user_probe q hq_K0W hVI
    hVIeps_signed_user_triple := hMinty_signed_user_triple q hq_K0W hVI
    hVIeps_transport := hMinty_transport q hq_K0W hVI
  }⟩

/-! ## `HemicontSegmentData` producer from K_Aepsi endpoints + test direction

Per `infra-P4-hemicont-segment-data-of-KAepsi`: rather than extending
`MFGOpEpsAuxHyps` with segment-dominator certs (which depend on TWO
endpoints + a test direction, so don't belong in the fixed-primal
operator aux record), this section files a separate producer for
`HemicontSegmentData`.

The headline lemma `hemicontSegmentData_of_KAepsi` consumes:

* paper hypotheses `(hpow, hExp)` plus `V`-regularity `hV`,
* two K_Aepsi endpoints `q₁ q₂ : XBanach d βBarReal γBarReal` (the
  pair `(μ, mBar) := (mOf q₁, mOf q₂)` has both components strictly
  positive a.e. by membership in `K_Aepsi`),
* a test direction `(Dν, η, ν)`,
* the standard residues threaded through
  `auxHyps_of_paperHypotheses_on_KAepsi` (paper-exponent
  identifications, Hölder-pair facts, the slice hypothesis for
  `upper_bound_powergrowth`, and the segment-specific measurability
  + pointwise-bound certificates),
* `g_unreg, g_gat : (Fin d → ℝ) → ℝ` segment dominators with their
  `IntegrableOn (UnitCube d)` certificates.

The producer **discharges** the `hPos` field of `HemicontSegmentData`
from convexity of the strict-positivity cone: for a.e. `x`, both
`mOf q₁ x > 0` and `mOf q₂ x > 0`, so the convex combination
`(1-t) · mOf q₂ x + t · mOf q₁ x` is strictly positive for every
`t ∈ [0,1]`. The remaining fields (dominators, integrability,
measurability, bounds) are consumed verbatim from the residues.

The dominator residues `g_unreg, g_gat` and their `MemLpPer 1`
certificates are produced by the AC2-dominator-closure infrastructure
(`flux_dominator_memLp_gammaBar'`, `g_dominator_memLp_betaBar'`)
combined with the Hölder closures
`hemicont_*_dominator_holder_memLp` from `Hemicontinuity.lean`.

This module **does not** extend `MFGOpEpsAuxHyps`: the fixed-primal
operator aux record carries the per-q (single triple) integrability
bundle, while the segment-dominator content depends on a pair of
endpoints plus the test direction and lives in a separate record.

The producer is a `noncomputable def` (not a `theorem`) because
`HemicontSegmentData` is `Type`-valued (its dominator fields
`g_unreg, g_gat` are functions, not Props). -/

open StationaryMFG.Theorems.SimplePower (HemicontSegmentData
  cxComb cxCombGrad aepsiIntegrandAt_unreg aepsiIntegrandAt_gateaux
  IsHK0AbsDominator IsmDpHK0Dominator
  aepsiIntegrandAt_unreg_pointwise_bound_K0)

/-- **Convexity of strict positivity along the segment.** Given two
K_Aepsi endpoints `q₁, q₂`, almost every `x` is in the full-measure
set on which both `mOf q₁ x > 0` and `mOf q₂ x > 0`; on that set, the
convex combination `cxComb (mOf q₁) (mOf q₂) t x = (1-t)·mOf q₂ x +
t·mOf q₁ x` is strictly positive for every `t ∈ [0,1]`.

This is the core convexity step underpinning
`hemicontSegmentData_of_KAepsi.hPos`. -/
lemma K_Aepsi_segment_pos
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (hq₁ : q₁ ∈ K_Aepsi d βBarReal γBarReal)
    (hq₂ : q₂ ∈ K_Aepsi d βBarReal γBarReal) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb (mOf q₁) (mOf q₂) t x := by
  -- Both endpoints are strictly positive a.e. on the unit cube.
  have hμ : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑q₁.1 : (Fin d → ℝ) → ℝ) x := hq₁
  have hmBar : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 < (⇑q₂.1 : (Fin d → ℝ) → ℝ) x := hq₂
  filter_upwards [hμ, hmBar] with x hμ_pos hmBar_pos t ht
  -- `cxComb μ mBar t x = (1 - t) * mBar x + t * μ x`.
  unfold cxComb
  -- `0 ≤ 1 - t` and `0 ≤ t` from `t ∈ [0, 1]`.
  have h1mt_nn : 0 ≤ 1 - t := by linarith [ht.2]
  have ht_nn : 0 ≤ t := ht.1
  -- Show the sum `(1 - t) * mBar + t * μ` is strictly positive.
  rcases lt_or_eq_of_le ht_nn with ht_pos | ht_zero
  · -- Case `0 < t`: the second summand `t * μ x` is strictly positive
    -- (μ_pos), and the first `(1 - t) * mBar x` is non-negative.
    have h_first_nn : 0 ≤ (1 - t) * ((⇑q₂.1 : (Fin d → ℝ) → ℝ) x) :=
      mul_nonneg h1mt_nn hmBar_pos.le
    have h_second_pos : 0 < t * ((⇑q₁.1 : (Fin d → ℝ) → ℝ) x) :=
      mul_pos ht_pos hμ_pos
    -- These are exactly `mOf q₂` and `mOf q₁` (by `mOf_def`).
    show 0 < (1 - t) * mOf q₂ x + t * mOf q₁ x
    have heq1 : mOf q₁ x = (⇑q₁.1 : (Fin d → ℝ) → ℝ) x := rfl
    have heq2 : mOf q₂ x = (⇑q₂.1 : (Fin d → ℝ) → ℝ) x := rfl
    rw [heq1, heq2]
    linarith
  · -- Case `t = 0`: the convex combination simplifies to `mBar x > 0`.
    show 0 < (1 - t) * mOf q₂ x + t * mOf q₁ x
    have ht_eq : t = 0 := ht_zero.symm
    rw [ht_eq]
    have heq2 : mOf q₂ x = (⇑q₂.1 : (Fin d → ℝ) → ℝ) x := rfl
    rw [heq2]
    have h_calc : (1 - (0 : ℝ)) * (⇑q₂.1 : (Fin d → ℝ) → ℝ) x
                    + 0 * (mOf q₁ x) = (⇑q₂.1 : (Fin d → ℝ) → ℝ) x := by
      ring
    rw [h_calc]
    exact hmBar_pos

/-- **Concrete segment dominator (unregularised piece).**

Built from the per-q `F_HJB`, `F_flux`, `F_mass` `MemLpPer`
certificates (carried by `MFGOpEpsAuxHyps`) at the two endpoints
`q₁, q₂`, paired against the test data `(Dν, η, ν)` via the
Hölder-conjugate exponent pairs `(βBar', βBar)` and `(γBar', γBar)`.

The function is the sum (over both endpoints, both Hölder slots) of
the absolute-value Hölder products:

  `g_unreg_concrete x =`
    `|F_HJB(q₁) x| · |η x|`
      `+ |F_HJB(q₂) x| · |η x|`
      `+ ∑ i, |F_flux i (q₁) x| · |Dν i x|`
      `+ ∑ i, |F_flux i (q₂) x| · |Dν i x|`
      `+ |F_mass(q₁) x| · |ν x|`
      `+ |F_mass(q₂) x| · |ν x|`.

Its integrability is given by `g_unreg_concrete_integrable` below;
the pointwise comparison `‖aepsiIntegrandAt_unreg ...‖ ≤
g_unreg_concrete x` for `t ∈ [0,1]` is supplied as a residue
(`hF_unreg_bound`), since assembling that bound from the scattered
pointwise content `hemicont_H_abs_dominator` /
`hemicont_mDpH_dominator` requires a separate pointwise-comparison
layer that lives outside this module — see follow-up
`infra-P4-hemicont-segment-pointwise-bound`. -/
noncomputable def g_unreg_concrete
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (q₁ q₂ : XBanach d βBarReal γBarReal)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (_aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (_aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂)) :
    (Fin d → ℝ) → ℝ :=
  fun x =>
    |F_HJB V H (DuOf q₁) (mOf q₁) (uOf q₁) x| * |η x|
      + |F_HJB V H (DuOf q₂) (mOf q₂) (uOf q₂) x| * |η x|
      + (∑ i : Fin d, |F_flux DpH (DuOf q₁) (mOf q₁) i x| * |Dν i x|)
      + (∑ i : Fin d, |F_flux DpH (DuOf q₂) (mOf q₂) i x| * |Dν i x|)
      + |F_mass (mOf q₁) x| * |ν x|
      + |F_mass (mOf q₂) x| * |ν x|

/-- **Concrete segment dominator (Gateaux piece).**

Built from the per-q `G_grad`, `G_val` `MemLpPer` certificates
(carried by `MFGOpEpsAuxHyps`) at the two endpoints, paired
against `(Dν, ν)` via the Hölder pair `(γBar', γBar)`. -/
noncomputable def g_gat_concrete
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (q₁ q₂ : XBanach d βBarReal γBarReal)
    (γBar : ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (ν : (Fin d → ℝ) → ℝ)
    (_aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (_aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂)) :
    (Fin d → ℝ) → ℝ :=
  fun x =>
    (∑ i : Fin d, |G_grad γBar (DuOf q₁) i x| * |Dν i x|)
      + (∑ i : Fin d, |G_grad γBar (DuOf q₂) i x| * |Dν i x|)
      + |G_val γBar (uOf q₁) x| * |ν x|
      + |G_val γBar (uOf q₂) x| * |ν x|

/-- The concrete unregularised dominator is integrable on the unit
cube. Each summand is a Hölder product of `MemLpPer p` (from the
per-q aux record) and `MemLpPer q` (from the test data) with
`(p, q)` real Hölder conjugates. -/
lemma g_unreg_concrete_integrableOn
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (q₁ q₂ : XBanach d βBarReal γBarReal)
    {Dν : Fin d → (Fin d → ℝ) → ℝ} {η ν : (Fin d → ℝ) → ℝ}
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    -- Phase 0 routing fix (`infra-P5-theorem1-phase-0`): the mass test
    -- side now lives in `L^γ̄` (paired against `F_mass ∈ L^γ̄'`).
    (hν : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    MeasureTheory.IntegrableOn
      (g_unreg_concrete q₁ q₂ Dν η ν aux₁ aux₂) (UnitCube d) := by
  -- Each summand is `MemLpPer.integrable_mul`-integrable; the sum is
  -- integrable by `MeasureTheory.Integrable.add`.
  -- Helper: |·| versions still satisfy `MemLpPer p`. Use `MemLp.abs`
  -- via the `MemLpPer = MemLp …` bridge.
  have hF_HJB₁_abs : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |F_HJB V H (DuOf q₁) (mOf q₁) (uOf q₁) x|) :=
    MemLp.toMemLpPer (aux₁.hF_HJB.toMemLp.abs)
  have hF_HJB₂_abs : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |F_HJB V H (DuOf q₂) (mOf q₂) (uOf q₂) x|) :=
    MemLp.toMemLpPer (aux₂.hF_HJB.toMemLp.abs)
  have hF_flux₁_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |F_flux DpH (DuOf q₁) (mOf q₁) i x|) :=
    fun i => MemLp.toMemLpPer ((aux₁.hF_flux i).toMemLp.abs)
  have hF_flux₂_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |F_flux DpH (DuOf q₂) (mOf q₂) i x|) :=
    fun i => MemLp.toMemLpPer ((aux₂.hF_flux i).toMemLp.abs)
  have hF_mass₁_abs : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |F_mass (mOf q₁) x|) :=
    MemLp.toMemLpPer (aux₁.hF_mass.toMemLp.abs)
  have hF_mass₂_abs : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |F_mass (mOf q₂) x|) :=
    MemLp.toMemLpPer (aux₂.hF_mass.toMemLp.abs)
  have hη_abs : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (fun x => |η x|) :=
    MemLp.toMemLpPer (hη.toMemLp.abs)
  have hDν_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => |Dν i x|) :=
    fun i => MemLp.toMemLpPer ((hDν i).toMemLp.abs)
  have hν_abs : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (fun x => |ν x|) :=
    MemLp.toMemLpPer (hν.toMemLp.abs)
  -- Integrability of each Hölder summand.
  have hi_HJB₁ : MeasureTheory.IntegrableOn
      (fun x => |F_HJB V H (DuOf q₁) (mOf q₁) (uOf q₁) x| * |η x|)
      (UnitCube d) := MemLpPer.integrable_mul hβconj hF_HJB₁_abs hη_abs
  have hi_HJB₂ : MeasureTheory.IntegrableOn
      (fun x => |F_HJB V H (DuOf q₂) (mOf q₂) (uOf q₂) x| * |η x|)
      (UnitCube d) := MemLpPer.integrable_mul hβconj hF_HJB₂_abs hη_abs
  have hi_flux₁ : ∀ i, MeasureTheory.IntegrableOn
      (fun x => |F_flux DpH (DuOf q₁) (mOf q₁) i x| * |Dν i x|)
      (UnitCube d) :=
    fun i => MemLpPer.integrable_mul hγconj (hF_flux₁_abs i) (hDν_abs i)
  have hi_flux₂ : ∀ i, MeasureTheory.IntegrableOn
      (fun x => |F_flux DpH (DuOf q₂) (mOf q₂) i x| * |Dν i x|)
      (UnitCube d) :=
    fun i => MemLpPer.integrable_mul hγconj (hF_flux₂_abs i) (hDν_abs i)
  have hi_mass₁ : MeasureTheory.IntegrableOn
      (fun x => |F_mass (mOf q₁) x| * |ν x|)
      (UnitCube d) := MemLpPer.integrable_mul hγconj hF_mass₁_abs hν_abs
  have hi_mass₂ : MeasureTheory.IntegrableOn
      (fun x => |F_mass (mOf q₂) x| * |ν x|)
      (UnitCube d) := MemLpPer.integrable_mul hγconj hF_mass₂_abs hν_abs
  -- Integrability of the finite sums of flux summands.
  have hi_flux₁_sum : MeasureTheory.IntegrableOn
      (fun x => ∑ i : Fin d, |F_flux DpH (DuOf q₁) (mOf q₁) i x| * |Dν i x|)
      (UnitCube d) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => hi_flux₁ i)
  have hi_flux₂_sum : MeasureTheory.IntegrableOn
      (fun x => ∑ i : Fin d, |F_flux DpH (DuOf q₂) (mOf q₂) i x| * |Dν i x|)
      (UnitCube d) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => hi_flux₂ i)
  -- Combine the six summands.
  unfold g_unreg_concrete
  exact ((((hi_HJB₁.add hi_HJB₂).add hi_flux₁_sum).add hi_flux₂_sum).add
            hi_mass₁).add hi_mass₂

/-- The concrete Gateaux dominator is integrable on the unit cube. -/
lemma g_gat_concrete_integrableOn
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (q₁ q₂ : XBanach d βBarReal γBarReal)
    (γBar : ℝ)
    {Dν : Fin d → (Fin d → ℝ) → ℝ} {ν : (Fin d → ℝ) → ℝ}
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hG_grad_eq : γBar = γBarReal)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    MeasureTheory.IntegrableOn
      (g_gat_concrete q₁ q₂ γBar Dν ν aux₁ aux₂) (UnitCube d) := by
  -- Helpers: |·|-versions of the per-q `MemLpPer` certs and test data.
  -- The `G_grad`/`G_val` certs are stated at `γBar = γBarReal`; we
  -- rewrite via `hG_grad_eq`.
  have hG_grad₁_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |G_grad γBar (DuOf q₁) i x|) := by
    intro i
    have h := aux₁.hG_grad i
    rw [hG_grad_eq]; exact MemLp.toMemLpPer (h.toMemLp.abs)
  have hG_grad₂_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |G_grad γBar (DuOf q₂) i x|) := by
    intro i
    have h := aux₂.hG_grad i
    rw [hG_grad_eq]; exact MemLp.toMemLpPer (h.toMemLp.abs)
  have hG_val₁_abs : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |G_val γBar (uOf q₁) x|) := by
    have h := aux₁.hG_val
    rw [hG_grad_eq]; exact MemLp.toMemLpPer (h.toMemLp.abs)
  have hG_val₂_abs : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |G_val γBar (uOf q₂) x|) := by
    have h := aux₂.hG_val
    rw [hG_grad_eq]; exact MemLp.toMemLpPer (h.toMemLp.abs)
  have hDν_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => |Dν i x|) :=
    fun i => MemLp.toMemLpPer ((hDν i).toMemLp.abs)
  have hν_abs : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (fun x => |ν x|) :=
    MemLp.toMemLpPer (hν.toMemLp.abs)
  -- Integrability of each Hölder summand.
  have hi_grad₁ : ∀ i, MeasureTheory.IntegrableOn
      (fun x => |G_grad γBar (DuOf q₁) i x| * |Dν i x|)
      (UnitCube d) :=
    fun i => MemLpPer.integrable_mul hγconj (hG_grad₁_abs i) (hDν_abs i)
  have hi_grad₂ : ∀ i, MeasureTheory.IntegrableOn
      (fun x => |G_grad γBar (DuOf q₂) i x| * |Dν i x|)
      (UnitCube d) :=
    fun i => MemLpPer.integrable_mul hγconj (hG_grad₂_abs i) (hDν_abs i)
  have hi_val₁ : MeasureTheory.IntegrableOn
      (fun x => |G_val γBar (uOf q₁) x| * |ν x|)
      (UnitCube d) := MemLpPer.integrable_mul hγconj hG_val₁_abs hν_abs
  have hi_val₂ : MeasureTheory.IntegrableOn
      (fun x => |G_val γBar (uOf q₂) x| * |ν x|)
      (UnitCube d) := MemLpPer.integrable_mul hγconj hG_val₂_abs hν_abs
  have hi_grad₁_sum : MeasureTheory.IntegrableOn
      (fun x => ∑ i : Fin d, |G_grad γBar (DuOf q₁) i x| * |Dν i x|)
      (UnitCube d) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => hi_grad₁ i)
  have hi_grad₂_sum : MeasureTheory.IntegrableOn
      (fun x => ∑ i : Fin d, |G_grad γBar (DuOf q₂) i x| * |Dν i x|)
      (UnitCube d) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => hi_grad₂ i)
  unfold g_gat_concrete
  exact (((hi_grad₁_sum.add hi_grad₂_sum).add hi_val₁).add hi_val₂)

/-! ## Natural-form segment dominators and their integrability

The natural-form dominators `g_unreg_natural`, `g_gat_natural` mirror
the **right-hand side** produced by
`aepsiIntegrandAt_unreg_pointwise_bound` and
`aepsiIntegrandAt_gateaux_pointwise_bound` (in
`StationaryMFG/Theorems/SimplePower/Hemicontinuity.lean`).

Whereas `g_unreg_concrete`/`g_gat_concrete` package the dominator in
**operator form** (sums of `|F_HJB|·|η|`, `∑|F_flux i|·|Dν i|`,
`|F_mass|·|ν|`, `∑|G_grad i|·|Dν i|`, `|G_val|·|ν|`), the natural form
exposes the *power-of-input* shapes
`(|Dῡ|+|Dυ|)^α`, `(|mBar|+|μ|)^β`,
`(|mBar|+|μ|)·‖|Dῡ|+|Dυ|‖^(α-1)`, etc., which is the form needed for
the dominated-convergence step in the proof of `lem_hemicont`.

The integrability of `g_unreg_natural`, `g_gat_natural` is supplied
by composing `MemLpPer p` certificates of the *power-of-input*
building blocks (e.g. `(|Dῡ|+|Dυ|)^α ∈ L^{γ̄/α}_per`) with the test
direction `MemLpPer q` certs at the Hölder-conjugate exponents.
These power-of-input certs are **not** in `MFGOpEpsAuxHyps`; they
must be supplied by the caller (per CONVENTIONS §8, mirroring the
`hScalarMono`/`hVecMono` precedent).
-/

/-- **Natural-form unreg dominator** matching the RHS shape of
`aepsiIntegrandAt_unreg_pointwise_bound`. Parameters:
`α β C` from `HypothesisPowerGrowth` (`h.α, h.β, h.C`), `C'` the
existential constant from `hemicont_H_abs_dominator`, plus the data
`(V, Dυ, Dῡ, μ, mBar, υ, ῡ, Dν, η, ν)`. -/
noncomputable def g_unreg_natural
    {d : ℕ}
    (α β C C' : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x =>
    (|ῡ x| + |υ x|) * |η x|
      + (C' * (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1)
          + C * ((|mBar x| + |μ x|) ^ β + 1)) * |η x|
      + |V x| * |η x|
      + C * ((|mBar x| + |μ x|)
                  * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)
                + (|mBar x| + |μ x|) ^ (1 + β - β / α)
                + (|mBar x| + |μ x|))
          * (∑ i, |Dν i x|)
      + ((|mBar x| + |μ x|) + 1) * |ν x|

/-- **Natural-form Gateaux dominator** matching the RHS shape of
`aepsiIntegrandAt_gateaux_pointwise_bound_product`. Product form is
valid for all `γBar > 1` (no `2 ≤ γBar` required). -/
noncomputable def g_gat_natural
    {d : ℕ}
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x =>
    (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
        * (∑ i, |Dν i x|)
      + (|ῡ x| + |υ x|) ^ (γBar - 1) * |ν x|

/-- **`IntegrableOn` for the natural-form unreg dominator.**

The producer takes:

* Real Hölder-conjugate pairs `(βBar, βBar')`, `(γBar, γBar')`.
* `MemLpPer (ofReal βBar') η`, `MemLpPer (ofReal βBar') ν`,
  `MemLpPer (ofReal γBar) (Dν i)` — test-direction Lp regularity.
* `MemLpPer (ofReal βBar') V`, `MemLpPer (ofReal βBar') (|ῡ|+|υ|)` —
  paper-input Lp regularity at the `βBar'` exponent.
* `MemLpPer (ofReal βBar') (‖|Dῡ|+|Dυ|‖^α + 1)` — α-power cert in
  natural form (this is what the caller assembles from
  `(|Dῡ|+|Dυ|) ∈ L^γBar` plus `α/γBar = 1/βBar'`).
* `MemLpPer (ofReal βBar') ((|mBar|+|μ|)^β + 1)` — β-power cert.
* `MemLpPer (ofReal γBar') ((|mBar|+|μ|) · ‖|Dῡ|+|Dυ|‖^(α-1))` —
  the `m·grad^(α-1)` Hölder-side cert.
* `MemLpPer (ofReal γBar') ((|mBar|+|μ|)^(1+β-β/α))` — endpoint-scale
  m-power cert.
* `MemLpPer (ofReal γBar') (|mBar|+|μ|)` — m-itself cert.
* `MemLpPer (ofReal βBar') ((|mBar|+|μ|) + 1)` — m+1 cert.

Composing summand-by-summand via `MemLpPer.integrable_mul` over the
two real Hölder conjugate pairs, plus `Integrable.const_mul` and
`Integrable.add` to glue. -/
lemma g_unreg_natural_integrableOn
    {d : ℕ}
    {βBar βBar' γBar γBar' α β C C' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (hβconj : βBar'.HolderConjugate βBar)
    (hγconj : γBar'.HolderConjugate γBar)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBar) η)
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBar) ν)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dν i))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => |ῡ x| + |υ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => (|mBar x| + |μ x|) ^ β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|mBar x| + |μ x|)
                  * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|mBar x| + |μ x|) ^ (1 + β - β / α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => |mBar x| + |μ x|))
    (hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => (|mBar x| + |μ x|) + 1)) :
    MeasureTheory.IntegrableOn
      (g_unreg_natural α β C C' V Dυ Dῡ μ mBar υ ῡ Dν η ν)
      (UnitCube d) := by
  -- |·|-versions of the test Lp certs.
  have hη_abs : MemLpPer (d := d) (ENNReal.ofReal βBar) (fun x => |η x|) :=
    MemLp.toMemLpPer (hη.toMemLp.abs)
  have hν_abs : MemLpPer (d := d) (ENNReal.ofReal βBar) (fun x => |ν x|) :=
    MemLp.toMemLpPer (hν_β.toMemLp.abs)
  have hDν_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => |Dν i x|) :=
    fun i => MemLp.toMemLpPer ((hDν i).toMemLp.abs)
  -- Hölder-conjugate βBar ↔ βBar' (we have βBar'.HolderConjugate βBar);
  -- the integrable-mul lemma takes `p.HolderConjugate q` with f∈L^p, g∈L^q.
  have hβconj' : βBar.HolderConjugate βBar' := hβconj.symm
  have hγconj' : γBar.HolderConjugate γBar' := hγconj.symm
  -- |V|-version of the V Lp cert.
  have hV_abs : MemLpPer (d := d) (ENNReal.ofReal βBar')
        (fun x => |V x|) :=
    MemLp.toMemLpPer (hV.toMemLp.abs)
  -- Term 1: (|ῡ|+|υ|) * |η|.
  -- Note: hΔυ already represents the non-negative function `|ῡ|+|υ|`,
  -- but we also need the absolute value of it for the Hölder pair.
  -- Since (|ῡ x| + |υ x|) ≥ 0, |·| is identity, but the bare term in
  -- `g_unreg_natural` writes it without |·|. We pair `hΔυ` with `hη_abs`
  -- via the (βBar', βBar) Hölder pair.
  have hi_term1 : MeasureTheory.IntegrableOn
      (fun x => (|ῡ x| + |υ x|) * |η x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔυ hη_abs
  -- Term 2: (C' * (‖Δp‖^α + 1) + C * (Δm^β + 1)) * |η|.
  -- We split into two Hölder products and a sum.
  have hi_term2a_pre : MeasureTheory.IntegrableOn
      (fun x => (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|)
      (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔp_pow hη_abs
  have hi_term2a : MeasureTheory.IntegrableOn
      (fun x => C' * ((‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|))
      (UnitCube d) := hi_term2a_pre.const_mul C'
  have hi_term2b_pre : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|) ^ β + 1) * |η x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔm_pow hη_abs
  have hi_term2b : MeasureTheory.IntegrableOn
      (fun x => C * (((|mBar x| + |μ x|) ^ β + 1) * |η x|))
      (UnitCube d) := hi_term2b_pre.const_mul C
  -- Combine 2a + 2b and rewrite the goal shape.
  have hi_term2_sum : MeasureTheory.IntegrableOn
      (fun x =>
        C' * ((‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|)
        + C * (((|mBar x| + |μ x|) ^ β + 1) * |η x|))
      (UnitCube d) := hi_term2a.add hi_term2b
  have heq_term2 :
      (fun x =>
        C' * ((‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|)
        + C * (((|mBar x| + |μ x|) ^ β + 1) * |η x|))
        = (fun x =>
          (C' * (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1)
            + C * ((|mBar x| + |μ x|) ^ β + 1)) * |η x|) := by
    funext x; ring
  rw [heq_term2] at hi_term2_sum
  have hi_term2 := hi_term2_sum
  -- Term 3: |V| * |η|.
  have hi_term3 : MeasureTheory.IntegrableOn
      (fun x => |V x| * |η x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hV_abs hη_abs
  -- Term 4: C * (Δm·‖Δp‖^(α-1) + Δm^(1+β-β/α) + Δm) * (∑|Dν|).
  -- Split the inner sum.
  -- We package `∑ i, |Dν i|` as a single `MemLpPer (ofReal γBar)` via
  -- `MemLp.fun_finset_sum'`.
  have hsumDν : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => ∑ i, |Dν i x|) := by
    have h : MemLp (fun x : (Fin d → ℝ) => ∑ i, |Dν i x|)
        (ENNReal.ofReal γBar)
        (MeasureTheory.volume.restrict (UnitCube (d := d))) :=
      MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (f := fun i x => |Dν i x|)
        (fun i _ => (hDν_abs i : MemLp _ _ _))
    exact MemLp.toMemLpPer h
  have hi_term4_a : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|)
          * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1))
          * (∑ i, |Dν i x|))
      (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm_grad hsumDν
  have hi_term4_b : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|) ^ (1 + β - β / α))
          * (∑ i, |Dν i x|))
      (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm_endpoint hsumDν
  have hi_term4_c : MeasureTheory.IntegrableOn
      (fun x => (|mBar x| + |μ x|) * (∑ i, |Dν i x|))
      (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm hsumDν
  have hi_term4_pre := (hi_term4_a.add hi_term4_b).add hi_term4_c
  have hi_term4 : MeasureTheory.IntegrableOn
      (fun x => C * ((|mBar x| + |μ x|)
          * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)
        + (|mBar x| + |μ x|) ^ (1 + β - β / α)
        + (|mBar x| + |μ x|)) * (∑ i, |Dν i x|))
      (UnitCube d) := by
    -- `Integrable.add` uses Pi-add at the function level, so the resulting
    -- `hi_term4_pre` has shape `(f1 + f2) + f3` where `+` is function add.
    -- Rewrite via `MeasureTheory.Integrable.congr` to get the desired
    -- single-lambda form.
    have hcongr : (fun x : (Fin d → ℝ) =>
        C * ((|mBar x| + |μ x|)
            * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)
          + (|mBar x| + |μ x|) ^ (1 + β - β / α)
          + (|mBar x| + |μ x|)) * (∑ i, |Dν i x|))
        = fun x : (Fin d → ℝ) =>
          C *
          (((fun y => ((|mBar y| + |μ y|)
              * ‖fun i => |Dῡ i y| + |Dυ i y|‖ ^ (α - 1))
              * (∑ i, |Dν i y|))
            + (fun y => ((|mBar y| + |μ y|) ^ (1 + β - β / α))
              * (∑ i, |Dν i y|))
            + (fun y => (|mBar y| + |μ y|) * (∑ i, |Dν i y|))) x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [hcongr]
    exact hi_term4_pre.const_mul C
  -- Term 5: ((|mBar|+|μ|)+1) * |ν|.
  have hi_term5 : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|) + 1) * |ν x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔm1 hν_abs
  -- Combine all five.
  unfold g_unreg_natural
  exact ((((hi_term1.add hi_term2).add hi_term3).add hi_term4).add hi_term5)

/-! ### Helper: `L^p ⊂ L^1` on the unit cube for `1 ≤ p` -/

/-- **Finite-measure `Lᵖ`-to-`L¹` inclusion (absolute-value form) on the
unit cube.** Given `MemLpPer p f` with `1 ≤ p`, the absolute value `|f|`
is integrable on the unit cube. This is the helper consumed by the
paper-faithful `_min` variant of `g_unreg_natural_integrableOn`, where
Term 5 `((|m̄|+|μ|)+1) * |ν|` is split as `(|m̄|+|μ|) * |ν| + |ν|` and
the second piece is discharged from `|ν| ∈ L^γ̄` plus `1 ≤ γ̄`. -/
private lemma memLpPer_abs_integrableOn_unitCube_of_one_le
    {d : ℕ} {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hp : 1 ≤ p)
    (hf : MemLpPer (d := d) p f) :
    MeasureTheory.IntegrableOn (fun x => |f x|) (UnitCube d) := by
  -- `|f|` is `MemLpPer p` because `MemLp.abs` lifts `MemLp f p` to
  -- `MemLp |f| p`.
  have hf_abs : MemLpPer (d := d) p (fun x => |f x|) :=
    MemLp.toMemLpPer (hf.toMemLp.abs)
  -- And `MemLpPer p ↪ MemLpPer 1` for `1 ≤ p` on the finite-measure cube
  -- (`StationaryMFG.Solutions.MFG.integrableOn_of_memLpPer`).
  exact StationaryMFG.Solutions.MFG.integrableOn_of_memLpPer hp hf_abs

/-- **Paper-faithful sibling of `g_unreg_natural_integrableOn`.**

Same conclusion as the legacy 13-hypothesis form, but drops the two
over-specified residues `hν_β : MemLpPer βBar ν` and
`hΔm1 : MemLpPer βBar' ((|m̄|+|μ|) + 1)` and adds the paper-faithful
`hγ_one_le : 1 ≤ ofReal γBar` and `hν_γ : MemLpPer γBar ν`.

The difference is concentrated on Term 5: the legacy form pairs
`((|m̄|+|μ|)+1) ∈ L^β̄'` with `|ν| ∈ L^β̄` via the `(β̄', β̄)` Hölder pair;
the paper-faithful form splits the term as
`((|m̄|+|μ|)+1) * |ν| = (|m̄|+|μ|) * |ν| + |ν|`, integrates the first
piece via the `(γ̄', γ̄)` Hölder pair against `hν_γ`, and discharges the
second piece via the `L^γ̄ ⊂ L¹` inclusion on the unit cube (using the
helper `memLpPer_abs_integrableOn_unitCube_of_one_le` and `1 ≤ γ̄`).

The legacy lemma is **not** deleted; it remains available for downstream
consumers that have not yet retargeted to the paper-faithful path. -/
lemma g_unreg_natural_integrableOn_min
    {d : ℕ}
    {βBar βBar' γBar γBar' α β C C' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (hβconj : βBar'.HolderConjugate βBar)
    (hγconj : γBar'.HolderConjugate γBar)
    (hγ_one_le : 1 ≤ ENNReal.ofReal γBar)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBar) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dν i))
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBar) ν)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => |ῡ x| + |υ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => (|mBar x| + |μ x|) ^ β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|mBar x| + |μ x|)
                  * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|mBar x| + |μ x|) ^ (1 + β - β / α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => |mBar x| + |μ x|)) :
    MeasureTheory.IntegrableOn
      (g_unreg_natural α β C C' V Dυ Dῡ μ mBar υ ῡ Dν η ν)
      (UnitCube d) := by
  -- |·|-versions of the test Lp certs.
  have hη_abs : MemLpPer (d := d) (ENNReal.ofReal βBar) (fun x => |η x|) :=
    MemLp.toMemLpPer (hη.toMemLp.abs)
  have hν_abs_γ : MemLpPer (d := d) (ENNReal.ofReal γBar) (fun x => |ν x|) :=
    MemLp.toMemLpPer (hν_γ.toMemLp.abs)
  have hDν_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => |Dν i x|) :=
    fun i => MemLp.toMemLpPer ((hDν i).toMemLp.abs)
  -- |V|-version of the V Lp cert.
  have hV_abs : MemLpPer (d := d) (ENNReal.ofReal βBar')
        (fun x => |V x|) :=
    MemLp.toMemLpPer (hV.toMemLp.abs)
  -- Term 1: (|ῡ|+|υ|) * |η|.
  have hi_term1 : MeasureTheory.IntegrableOn
      (fun x => (|ῡ x| + |υ x|) * |η x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔυ hη_abs
  -- Term 2: split into 2a + 2b, then rewrite to the natural-form shape.
  have hi_term2a_pre : MeasureTheory.IntegrableOn
      (fun x => (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|)
      (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔp_pow hη_abs
  have hi_term2a : MeasureTheory.IntegrableOn
      (fun x => C' * ((‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|))
      (UnitCube d) := hi_term2a_pre.const_mul C'
  have hi_term2b_pre : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|) ^ β + 1) * |η x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hΔm_pow hη_abs
  have hi_term2b : MeasureTheory.IntegrableOn
      (fun x => C * (((|mBar x| + |μ x|) ^ β + 1) * |η x|))
      (UnitCube d) := hi_term2b_pre.const_mul C
  have hi_term2_sum : MeasureTheory.IntegrableOn
      (fun x =>
        C' * ((‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|)
        + C * (((|mBar x| + |μ x|) ^ β + 1) * |η x|))
      (UnitCube d) := hi_term2a.add hi_term2b
  have heq_term2 :
      (fun x =>
        C' * ((‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1) * |η x|)
        + C * (((|mBar x| + |μ x|) ^ β + 1) * |η x|))
        = (fun x =>
          (C' * (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1)
            + C * ((|mBar x| + |μ x|) ^ β + 1)) * |η x|) := by
    funext x; ring
  rw [heq_term2] at hi_term2_sum
  have hi_term2 := hi_term2_sum
  -- Term 3: |V| * |η|.
  have hi_term3 : MeasureTheory.IntegrableOn
      (fun x => |V x| * |η x|) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hV_abs hη_abs
  -- Term 4: same structure as the legacy proof, but using the γ-side
  -- residues and the `(γBar', γBar)` Hölder pair.
  have hsumDν : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => ∑ i, |Dν i x|) := by
    have h : MemLp (fun x : (Fin d → ℝ) => ∑ i, |Dν i x|)
        (ENNReal.ofReal γBar)
        (MeasureTheory.volume.restrict (UnitCube (d := d))) :=
      MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (f := fun i x => |Dν i x|)
        (fun i _ => (hDν_abs i : MemLp _ _ _))
    exact MemLp.toMemLpPer h
  have hi_term4_a : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|)
          * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1))
          * (∑ i, |Dν i x|))
      (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm_grad hsumDν
  have hi_term4_b : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|) ^ (1 + β - β / α))
          * (∑ i, |Dν i x|))
      (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm_endpoint hsumDν
  have hi_term4_c : MeasureTheory.IntegrableOn
      (fun x => (|mBar x| + |μ x|) * (∑ i, |Dν i x|))
      (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm hsumDν
  have hi_term4_pre := (hi_term4_a.add hi_term4_b).add hi_term4_c
  have hi_term4 : MeasureTheory.IntegrableOn
      (fun x => C * ((|mBar x| + |μ x|)
          * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)
        + (|mBar x| + |μ x|) ^ (1 + β - β / α)
        + (|mBar x| + |μ x|)) * (∑ i, |Dν i x|))
      (UnitCube d) := by
    have hcongr : (fun x : (Fin d → ℝ) =>
        C * ((|mBar x| + |μ x|)
            * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)
          + (|mBar x| + |μ x|) ^ (1 + β - β / α)
          + (|mBar x| + |μ x|)) * (∑ i, |Dν i x|))
        = fun x : (Fin d → ℝ) =>
          C *
          (((fun y => ((|mBar y| + |μ y|)
              * ‖fun i => |Dῡ i y| + |Dυ i y|‖ ^ (α - 1))
              * (∑ i, |Dν i y|))
            + (fun y => ((|mBar y| + |μ y|) ^ (1 + β - β / α))
              * (∑ i, |Dν i y|))
            + (fun y => (|mBar y| + |μ y|) * (∑ i, |Dν i y|))) x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [hcongr]
    exact hi_term4_pre.const_mul C
  -- New Term 5: `((|m̄|+|μ|)+1) * |ν|`. Split as the sum and discharge
  -- the two pieces via the paper-faithful routes.
  have hi_term5a : MeasureTheory.IntegrableOn
      (fun x => (|mBar x| + |μ x|) * |ν x|) (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm hν_abs_γ
  have hi_term5b : MeasureTheory.IntegrableOn
      (fun x => |ν x|) (UnitCube d) :=
    memLpPer_abs_integrableOn_unitCube_of_one_le hγ_one_le hν_γ
  have hi_term5 : MeasureTheory.IntegrableOn
      (fun x => ((|mBar x| + |μ x|) + 1) * |ν x|) (UnitCube d) := by
    have hsum := hi_term5a.add hi_term5b
    -- `hsum : IntegrableOn ((fun x => (|mBar x|+|μ x|)*|ν x|) + fun x => |ν x|) …`
    -- with `+` at the function level (`Pi.add_apply`). Rewrite to the
    -- single-lambda product shape via `Integrable.congr`.
    have heq : ((fun x => (|mBar x| + |μ x|) * |ν x|) + fun x => |ν x|)
                = (fun x => ((|mBar x| + |μ x|) + 1) * |ν x|) := by
      funext x; simp [Pi.add_apply]; ring
    rw [heq] at hsum
    exact hsum
  -- Combine all five terms exactly as in the legacy proof.
  unfold g_unreg_natural
  exact ((((hi_term1.add hi_term2).add hi_term3).add hi_term4).add hi_term5)

/-- **`IntegrableOn` for the natural-form Gateaux dominator (product form).**

Two Hölder products against the test factors `∑|Dν|` and `|ν|` at
the `(γBar', γBar)` Hölder pair, valid for all `γBar > 1`. -/
lemma g_gat_natural_integrableOn
    {d : ℕ}
    {γBar γBar' : ℝ}
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    (hγconj : γBar'.HolderConjugate γBar)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dν i))
    (hν : MemLpPer (d := d) (ENNReal.ofReal γBar) ν)
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x =>
                (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|ῡ x| + |υ x|) ^ (γBar - 1))) :
    MeasureTheory.IntegrableOn
      (g_gat_natural γBar Dυ Dῡ υ ῡ Dν ν) (UnitCube d) := by
  -- |·|-versions of the test Lp certs.
  have hν_abs : MemLpPer (d := d) (ENNReal.ofReal γBar) (fun x => |ν x|) :=
    MemLp.toMemLpPer (hν.toMemLp.abs)
  have hDν_abs : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => |Dν i x|) :=
    fun i => MemLp.toMemLpPer ((hDν i).toMemLp.abs)
  have hsumDν : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => ∑ i, |Dν i x|) := by
    have h : MemLp (fun x : (Fin d → ℝ) => ∑ i, |Dν i x|)
        (ENNReal.ofReal γBar)
        (MeasureTheory.volume.restrict (UnitCube (d := d))) :=
      MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (f := fun i x => |Dν i x|)
        (fun i _ => (hDν_abs i : MemLp _ _ _))
    exact MemLp.toMemLpPer h
  -- Term G1: (S2)^((γ-1)/2) * (∑|Dν|).
  -- Pair (G_grad ∈ L^γBar') with (∑|Dν| ∈ L^γBar) via Hölder.
  have hi_term_grad : MeasureTheory.IntegrableOn
      (fun x =>
        ((∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2))
          * (∑ i, |Dν i x|)) (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hG_grad hsumDν
  -- Term G2: (Δυ^(γ-1)) * |ν|.
  have hi_term_val : MeasureTheory.IntegrableOn
      (fun x => ((|ῡ x| + |υ x|) ^ (γBar - 1)) * |ν x|) (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hG_val hν_abs
  unfold g_gat_natural
  exact hi_term_grad.add hi_term_val

/-- **Sanity check (type-level).** The producer `g_unreg_natural_integrableOn`
type-checks at any data + Hölder pair + supplied `MemLpPer p` certs. -/
example
    {d : ℕ}
    {βBar βBar' γBar γBar' α β C C' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (hβconj : βBar'.HolderConjugate βBar)
    (hγconj : γBar'.HolderConjugate γBar)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBar) η)
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBar) ν)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dν i))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => |ῡ x| + |υ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => (|mBar x| + |μ x|) ^ β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|mBar x| + |μ x|)
                  * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|mBar x| + |μ x|) ^ (1 + β - β / α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => |mBar x| + |μ x|))
    (hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBar')
              (fun x => (|mBar x| + |μ x|) + 1)) :
    MeasureTheory.IntegrableOn
      (g_unreg_natural α β C C' V Dυ Dῡ μ mBar υ ῡ Dν η ν)
      (UnitCube d) :=
  g_unreg_natural_integrableOn hβconj hγconj hη hν_β hDν hV hΔυ
    hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm hΔm1

/-- **Sanity check (Gateaux, type-level).** -/
example
    {d : ℕ}
    {γBar γBar' : ℝ}
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    (hγconj : γBar'.HolderConjugate γBar)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dν i))
    (hν : MemLpPer (d := d) (ENNReal.ofReal γBar) ν)
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x =>
                (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBar')
              (fun x => (|ῡ x| + |υ x|) ^ (γBar - 1))) :
    MeasureTheory.IntegrableOn
      (g_gat_natural γBar Dυ Dῡ υ ῡ Dν ν) (UnitCube d) :=
  g_gat_natural_integrableOn hγconj hDν hν hG_grad hG_val

/-- **`HemicontSegmentData` producer from two K_Aepsi endpoints.**

Builds the per-segment hypothesis bundle of `lem_hemicont` (paper
line 990) for the convex segment between two strict-positive endpoints
`(μ, mBar) := (mOf q₁, mOf q₂)` against the test direction `(Dν, η, ν)`.

**Concretely discharged fields (7 of 9):**

* `hPos` — from convexity of the strict-positivity cone (via
  `K_Aepsi_segment_pos`).
* `g_unreg`, `g_gat` — natural-form dominators
  `g_unreg_natural`, `g_gat_natural` matching the right-hand sides of
  `aepsiIntegrandAt_unreg_pointwise_bound` and
  `aepsiIntegrandAt_gateaux_pointwise_bound`. The `H`-existential
  constant `C'` from the unreg pointwise bound is captured via
  `Exists.choose`.
* `hg_unreg_int`, `hg_gat_int` — `IntegrableOn` certificates from
  `g_unreg_natural_integrableOn` / `g_gat_natural_integrableOn`,
  composed `MemLpPer.integrable_mul` Hölder products at the
  natural-form `MemLpPer p`-of-power residues supplied by the caller
  (see the `hΔ*`/`hG_*` parameters below).
* `hF_unreg_bound`, `hF_gat_bound` — pointwise comparisons obtained
  from the natural-form pointwise-bound lemmas
  `aepsiIntegrandAt_unreg_pointwise_bound` (consumed at the
  segment-positivity certificate `K_Aepsi_segment_pos`) and
  `aepsiIntegrandAt_gateaux_pointwise_bound` (uniform in `t ∈ [0,1]`).

**Residue fields (2 of 9, genuinely test-direction-dependent):**

* `hF_unreg_meas`, `hF_gat_meas` — Caratheodory measurability of the
  segment integrands. Genuinely test-direction-dependent (they
  depend on the joint measurability of `t ↦ integrand x t`, which is
  not an a.e.-statement on `x` alone but a standard
  separable-measurability fact for the test triple).

This producer **does NOT extend `MFGOpEpsAuxHyps`** — the fixed-primal
aux record stays focused on per-q integrability (strict-positivity
supplied by K_Aepsi membership), while the segment-specific dominator
data is computed here from a pair of per-q records together with the
natural-form `MemLpPer`-of-power residues that the AC2-dominator-closure
infrastructure produces. -/
noncomputable def hemicontSegmentData_of_KAepsi
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (hq₁ : q₁ ∈ K_Aepsi d βBarReal γBarReal)
    (hq₂ : q₂ ∈ K_Aepsi d βBarReal γBarReal)
    -- Per-q `MFGOpEpsAuxHyps` certificates at the two endpoints (produced
    -- by `auxHyps_of_paperHypotheses_on_KAepsi` from the paper hypotheses
    -- `(hpow, hV, hExp, …)`). Retained as parameters so callers can
    -- continue to thread them; the natural-form bounds do not consume
    -- them directly but they are still required by the K_Aepsi
    -- positivity step's downstream consumers and document the role of
    -- the per-q records in the producer's overall API.
    (_aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (_aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    -- Hölder-pair facts on the real exponents.
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- Paper hypothesis (power growth) and the slice form needed by
    -- `aepsiIntegrandAt_unreg_pointwise_bound`.
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    -- The product-form Gateaux pointwise bound requires only `1 < γBar`.
    (hγ_one_lt : 1 < γBar)
    -- Test direction with its `MemLpPer`-regularity at the test exponents.
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    -- Identification of the Gateaux exponent with the paper's γ̄.
    (hγBar_eq : γBar = γBarReal)
    -- Natural-form `MemLpPer p`-of-power residues consumed by
    -- `g_unreg_natural_integrableOn` and `g_gat_natural_integrableOn`.
    -- The unreg side wants exponents `(βBarReal, βBarReal')` and
    -- `(γBarReal, γBarReal')`, while the Gateaux side uses
    -- `(γBarReal, γBarReal')` only. The Gateaux residues
    -- `hG_grad`/`hG_val` are in **product form** (no
    -- `‖|Dῡ|+|Dυ|‖` factor on `hG_grad`, no extra `(|ῡ|+|υ|)` factor on
    -- `hG_val`); cf. `g_gat_natural` and
    -- `aepsiIntegrandAt_gateaux_pointwise_bound_product`.
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|))
    (hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1))
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)))
    -- Genuinely test-direction-dependent residues: measurability of the
    -- segment integrands.
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                    (uOf q₁) (uOf q₂) Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
      (uOf q₁) (uOf q₂) Dν η ν :=
  -- Pick the existential `H`-constant `C'` from the unreg pointwise bound.
  let hbound :=
    aepsiIntegrandAt_unreg_pointwise_bound V h h_slice
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂) (uOf q₁) (uOf q₂) Dν η ν
  let C' : ℝ := hbound.choose
  let hbound_spec : 0 < C' ∧ _ := hbound.choose_spec
  let hPos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1,
                0 < cxComb (mOf q₁) (mOf q₂) t x :=
    K_Aepsi_segment_pos hq₁ hq₂
  { hPos := hPos
    g_unreg := g_unreg_natural h.α h.β h.C C' V
                  (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                  (uOf q₁) (uOf q₂) Dν η ν
    g_gat := g_gat_natural γBar
                  (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν
    hg_unreg_int :=
      g_unreg_natural_integrableOn (α := h.α) (β := h.β)
        (C := h.C) (C' := C') (V := V)
        (Dυ := DuOf q₁) (Dῡ := DuOf q₂)
        (μ := mOf q₁) (mBar := mOf q₂) (υ := uOf q₁) (ῡ := uOf q₂)
        (Dν := Dν) (η := η) (ν := ν)
        hβconj hγconj hη hν_β hDν hV hΔυ
        hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm hΔm1
    hg_gat_int := by
      -- The natural-form Gateaux integrability lemma is stated at the
      -- abstract `γBar`; the test certificates `hDν, hν_γ, hγconj` are
      -- stated at `γBarReal`. Rewrite via `hγBar_eq : γBar = γBarReal`.
      have :=
        g_gat_natural_integrableOn (γBar := γBarReal)
          (Dυ := DuOf q₁) (Dῡ := DuOf q₂) (υ := uOf q₁) (ῡ := uOf q₂)
          (Dν := Dν) (ν := ν) hγconj hDν hν_γ
          (hγBar_eq ▸ hG_grad) (hγBar_eq ▸ hG_val)
      simpa [hγBar_eq] using this
    hF_unreg_meas := hF_unreg_meas
    hF_unreg_bound := by
      -- Combine the a.e.-uniform pointwise bound with K_Aepsi positivity.
      intro t ht
      have h₁ := hbound_spec.2
      filter_upwards [h₁, hPos] with x hx hposx
      exact hx t ht (hposx t ht)
    hF_gat_meas := hF_gat_meas
    hF_gat_bound := by
      -- Product-form Gateaux pointwise bound, uniform in `x` and
      -- `t ∈ [0,1]`. Valid for all `γBar > 1`.
      intro t ht
      have hgat :=
        aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
          (γBar := γBar) hγ_one_lt
          (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν
      refine MeasureTheory.ae_of_all _ ?_
      intro x
      exact hgat x t ht }

/-- **Sanity-check `example`.** The producer
`hemicontSegmentData_of_KAepsi` type-checks at any pair of K_Aepsi
endpoints with any test direction, given the paper-hypothesis
inputs `(aux₁, aux₂, hβconj, hγconj, h, h_slice, hγ, hη, hDν, hν_β,
hν_γ, hγBar_eq)`, the natural-form `MemLpPer p`-of-power residues
`(hV, hΔυ, hΔp_pow, hΔm_pow, hΔm_grad, hΔm_endpoint, hΔm, hΔm1,
hG_grad, hG_val)`, and the two genuinely-residue measurability certs. -/
example
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (hq₁ : q₁ ∈ K_Aepsi d βBarReal γBarReal)
    (hq₂ : q₂ ∈ K_Aepsi d βBarReal γBarReal)
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|))
    (hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1))
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                    (uOf q₁) (uOf q₂) Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
      (uOf q₁) (uOf q₂) Dν η ν :=
  hemicontSegmentData_of_KAepsi hq₁ hq₂ aux₁ aux₂ hβconj hγconj
    h h_slice hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq
    hV hΔυ hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm hΔm1
    hG_grad hG_val hF_unreg_meas hF_gat_meas

/-! ### Paper-faithful sibling: `hemicontSegmentData_of_KAepsi_min`

Mirrors `hemicontSegmentData_of_KAepsi` but **drops** the two
over-specified residues `hν_β` (test-`u` regularity at `β̄`) and
`hΔm1` (`m + 1 ∈ L^β̄'`), keeping only the paper-faithful `hν_γ` and
`hΔm`. Routes the unreg integrability through
`g_unreg_natural_integrableOn_min`, which handles Term 5 of
`g_unreg_natural` via the `(γ̄', γ̄)` Hölder pair plus the finite-measure
`L^γ̄ ⊂ L¹` inclusion (helper `memLpPer_abs_integrableOn_unitCube_of_one_le`).

The Gateaux integrability proof is identical to the legacy producer
(it already uses only γ-side data).
-/

/-- **Paper-faithful sibling of `hemicontSegmentData_of_KAepsi`.**

Same conclusion as the legacy producer at a pair of K_Aepsi endpoints
with a test direction, but consumes only the 11 paper-faithful
`MemLpPer`-residues (drops `hν_β` and `hΔm1`). Routes Term 5 of
`g_unreg_natural` via `g_unreg_natural_integrableOn_min`. -/
noncomputable def hemicontSegmentData_of_KAepsi_min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (hq₁ : q₁ ∈ K_Aepsi d βBarReal γBarReal)
    (hq₂ : q₂ ∈ K_Aepsi d βBarReal γBarReal)
    (_aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (_aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|))
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                    (uOf q₁) (uOf q₂) Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
      (uOf q₁) (uOf q₂) Dν η ν :=
  -- Pick the existential `H`-constant `C'` from the unreg pointwise bound.
  let hbound :=
    aepsiIntegrandAt_unreg_pointwise_bound V h h_slice
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂) (uOf q₁) (uOf q₂) Dν η ν
  let C' : ℝ := hbound.choose
  let hbound_spec : 0 < C' ∧ _ := hbound.choose_spec
  let hPos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1,
                0 < cxComb (mOf q₁) (mOf q₂) t x :=
    K_Aepsi_segment_pos hq₁ hq₂
  { hPos := hPos
    g_unreg := g_unreg_natural h.α h.β h.C C' V
                  (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                  (uOf q₁) (uOf q₂) Dν η ν
    g_gat := g_gat_natural γBar
                  (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν
    hg_unreg_int := by
      -- Derive `1 ≤ ENNReal.ofReal γBarReal` from `1 < γBar` plus
      -- `γBar = γBarReal`.
      have hγBarReal_one_lt : (1 : ℝ) < γBarReal := hγBar_eq ▸ hγ_one_lt
      have hγBarReal_one_le_real : (1 : ℝ) ≤ γBarReal := hγBarReal_one_lt.le
      have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := by
        have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarReal :=
          ENNReal.ofReal_le_ofReal hγBarReal_one_le_real
        simpa using h1
      exact g_unreg_natural_integrableOn_min (α := h.α) (β := h.β)
        (C := h.C) (C' := C') (V := V)
        (Dυ := DuOf q₁) (Dῡ := DuOf q₂)
        (μ := mOf q₁) (mBar := mOf q₂) (υ := uOf q₁) (ῡ := uOf q₂)
        (Dν := Dν) (η := η) (ν := ν)
        hβconj hγconj hγ_one_le hη hDν hν_γ hV hΔυ
        hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm
    hg_gat_int := by
      have :=
        g_gat_natural_integrableOn (γBar := γBarReal)
          (Dυ := DuOf q₁) (Dῡ := DuOf q₂) (υ := uOf q₁) (ῡ := uOf q₂)
          (Dν := Dν) (ν := ν) hγconj hDν hν_γ
          (hγBar_eq ▸ hG_grad) (hγBar_eq ▸ hG_val)
      simpa [hγBar_eq] using this
    hF_unreg_meas := hF_unreg_meas
    hF_unreg_bound := by
      intro t ht
      have h₁ := hbound_spec.2
      filter_upwards [h₁, hPos] with x hx hposx
      exact hx t ht (hposx t ht)
    hF_gat_meas := hF_gat_meas
    hF_gat_bound := by
      intro t ht
      have hgat :=
        aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
          (γBar := γBar) hγ_one_lt
          (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν
      refine MeasureTheory.ae_of_all _ ?_
      intro x
      exact hgat x t ht }

/-! ## K0-form `HemicontSegmentData` producer (μ ≥ 0 boundary)

The K0-form producer `hemicontSegmentData_of_K0Aepsi` is the
nonneg-cone analogue of `hemicontSegmentData_of_KAepsi` above:
endpoints `q₁, q₂ ∈ K0_Aepsi` rather than `K_Aepsi`, and the
segment-positivity certificate is `0 ≤ cxComb` rather than `0 <`.

The `hPos` field of `HemicontSegmentData` requires strict positivity.
For the **K0 form** we still discharge `hPos : 0 < cxComb μ mBar t x`
a.e.-uniformly in `t`, but it is now upgraded to **non-strict** at
the K0 level: see `K0_Aepsi_segment_pos_nn` below for the nonneg
analogue. The full K0 segment-data producer keeps the strict-positivity
field by **adding a strict-positivity slot at the construction site**
where the caller threads in either `K_Aepsi` membership or an
external strict-positivity certificate.

Given the concrete shape of `HemicontSegmentData.hPos`, the K0-form
producer below takes a **caller-supplied strict-positivity certificate**
`hPosSeg`, in addition to the K0 membership of the endpoints. This
factoring isolates the strict-positivity content from the rest of the
producer (which is uniform over K0 endpoints).

For the wider Minty closure chain (the consumer of this K0 producer),
the strict-positivity certificate at the limit `mLim` is obtained from
a perturbation argument: replace `mLim` with `mLim + 1/n` (which is
strictly positive everywhere) and pass to the limit in the resulting
weak VI inequality. The K0 producer here delivers the per-segment
data assuming that perturbation has already been performed.

Alternatively, when the strict-positivity field of `HemicontSegmentData`
is not actually required by the downstream DCT step (which only needs
`0 ≤ cxComb` for the K0-form pointwise bound), the producer can be
adapted to output an equivalent bundle without the `hPos` field; this
adaptation is captured below by accepting `hPosSeg` from the caller. -/

/-- **Convexity of nonnegativity along the segment.** Given two
K0_Aepsi endpoints `q₁, q₂`, almost every `x` is in the full-measure
set on which both `mOf q₁ x ≥ 0` and `mOf q₂ x ≥ 0`; on that set, the
convex combination `cxComb (mOf q₁) (mOf q₂) t x = (1-t)·mOf q₂ x +
t·mOf q₁ x` is non-negative for every `t ∈ [0,1]`.

This is the K0 analogue of `K_Aepsi_segment_pos`, with the strict
inequality relaxed to non-strict at the boundary `mOf q₁ x = 0` or
`mOf q₂ x = 0`. -/
lemma K0_Aepsi_segment_pos_nn
    {d : ℕ} {βBarReal γBarReal : ℝ}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (hq₁ : q₁ ∈ K0_Aepsi d βBarReal γBarReal)
    (hq₂ : q₂ ∈ K0_Aepsi d βBarReal γBarReal) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ cxComb (mOf q₁) (mOf q₂) t x := by
  -- Both endpoints are nonneg a.e. on the unit cube.
  have hμ : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 ≤ (⇑q₁.1 : (Fin d → ℝ) → ℝ) x := hq₁
  have hmBar : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 ≤ (⇑q₂.1 : (Fin d → ℝ) → ℝ) x := hq₂
  filter_upwards [hμ, hmBar] with x hμ_nn hmBar_nn t ht
  -- `cxComb μ mBar t x = (1 - t) * mBar x + t * μ x`.
  unfold cxComb
  have h1mt_nn : 0 ≤ 1 - t := by linarith [ht.2]
  have ht_nn : 0 ≤ t := ht.1
  have heq1 : mOf q₁ x = (⇑q₁.1 : (Fin d → ℝ) → ℝ) x := rfl
  have heq2 : mOf q₂ x = (⇑q₂.1 : (Fin d → ℝ) → ℝ) x := rfl
  show 0 ≤ (1 - t) * mOf q₂ x + t * mOf q₁ x
  rw [heq1, heq2]
  exact add_nonneg (mul_nonneg h1mt_nn hmBar_nn) (mul_nonneg ht_nn hμ_nn)

/-- **`HemicontSegmentData` producer from two K0_Aepsi endpoints.**

K0-form analogue of `hemicontSegmentData_of_KAepsi`: endpoints in the
closed nonneg cone `K0_Aepsi` rather than the strict-positivity cone
`K_Aepsi`. The segment-positivity certificate `hPos` of
`HemicontSegmentData` (which still asks for strict positivity) is
supplied by the caller as `hPosSeg`. The remaining fields are
discharged using the K0-form pointwise bound
`aepsiIntegrandAt_unreg_pointwise_bound_K0` together with the
caller-supplied K0 dominator certificates `hHabs_K0`, `hmDpH_K0`.

The K0 dominator certificates are paper-faithful for K0_Aepsi
endpoints by limit-passage from the K-strict version (using
`HypothesisHat0` and the upper/lower extension theorems
`HypothesisPowerGrowth.upper_extends_to_zero` /
`lower_extends_to_zero` plus `H_zero_eq_Hext`).

This producer is the entry point used by the wide Minty closure
chain whose limit triple `(mLim, uLim, DuLim)` lives in `K0_Aepsi`
(by `wkBundle.hmRep_nonneg`) but not necessarily in `K_Aepsi`.

### API design choice for `hPosSeg`

The argument `hPosSeg` is a **B-class caller-supplied** strict-positivity
certificate for the convex segment `t ↦ (1-t) mOf q₂ x + t mOf q₁ x`.
It exists solely as a passthrough to the structure field
`HemicontSegmentData.hPos`; the producer body itself only uses the
non-strict variant `K0_Aepsi_segment_pos_nn` for discharging the
K0-form pointwise bound `hF_unreg_bound`.

We deliberately keep the strict form on `HemicontSegmentData.hPos`
(option (b) of `infra-P5-mintyData-K0-form-relax-hPosSeg-to-nn`)
rather than introduce a parallel `HemicontSegmentDataNN`: the
downstream consumer chain `Aepsi_hemicontinuous_segment` /
`lem_hemicont` is structured around the strict form, and the
strict-positivity content can be discharged by the caller from
a perturbation residue `μ_n := μ + 1/n` (which is strictly positive
everywhere by construction). The transport helper
`HemicontSegmentData.ae_eq` (in `Hemicontinuity.lean`) lets the
caller move between a.e.-equal representatives of `(μ, mBar, …)`
once the strict positivity has been arranged on a perturbation. -/
noncomputable def hemicontSegmentData_of_K0Aepsi
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (_hq₁ : q₁ ∈ K0_Aepsi d βBarReal γBarReal)
    (_hq₂ : q₂ ∈ K0_Aepsi d βBarReal γBarReal)
    -- Per-q `MFGOpEpsAuxHyps` certificates at the two endpoints.
    -- Retained as parameters for documentary symmetry with the K_Aepsi
    -- producer; the K0-form natural bounds do not consume them directly.
    (_aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (_aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    -- Hölder-pair facts on the real exponents.
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- Paper hypothesis (power growth).
    (h : HypothesisPowerGrowth (d := d) H DpH)
    -- K0-form natural-form pointwise bound inputs (paper-faithful via
    -- Hat0/Hext; supplied by the caller).
    (C' : ℝ) (hC'_pos : 0 < C')
    (hHabs_K0 : IsHK0AbsDominator (d := d) h
                  (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂) C')
    (hmDpH_K0 : IsmDpHK0Dominator (d := d) h
                  (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂))
    -- Caller-supplied strict-positivity certificate along the segment
    -- (e.g. obtained by perturbation `μ_n := μ + 1/n`).
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb (mOf q₁) (mOf q₂) t x)
    -- The product-form Gateaux pointwise bound requires only `1 < γBar`.
    (hγ_one_lt : 1 < γBar)
    -- Test direction with its `MemLpPer`-regularity.
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    -- Natural-form `MemLpPer p`-of-power residues (same as K_Aepsi form).
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|))
    (hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1))
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)))
    -- Genuinely test-direction-dependent residues: measurability.
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                    (uOf q₁) (uOf q₂) Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
      (uOf q₁) (uOf q₂) Dν η ν := by
  -- Build the K0-form unreg pointwise bound (a.e.-uniform, K0 segment).
  have hbound_K0 :=
    aepsiIntegrandAt_unreg_pointwise_bound_K0 V h hC'_pos
      (mOf q₁) (mOf q₂) (uOf q₁) (uOf q₂) (DuOf q₁) (DuOf q₂)
      Dν η ν hHabs_K0 hmDpH_K0
  -- K0 segment positivity (a.e.-uniform-in-`t`).
  have hPos_nn :=
    K0_Aepsi_segment_pos_nn _hq₁ _hq₂
  exact
    { hPos := hPosSeg
      g_unreg := g_unreg_natural h.α h.β h.C C' V
                    (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                    (uOf q₁) (uOf q₂) Dν η ν
      g_gat := g_gat_natural γBar
                    (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν
      hg_unreg_int :=
        g_unreg_natural_integrableOn (α := h.α) (β := h.β)
          (C := h.C) (C' := C') (V := V)
          (Dυ := DuOf q₁) (Dῡ := DuOf q₂)
          (μ := mOf q₁) (mBar := mOf q₂) (υ := uOf q₁) (ῡ := uOf q₂)
          (Dν := Dν) (η := η) (ν := ν)
          hβconj hγconj hη hν_β hDν hV hΔυ
          hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm hΔm1
      hg_gat_int := by
        have :=
          g_gat_natural_integrableOn (γBar := γBarReal)
            (Dυ := DuOf q₁) (Dῡ := DuOf q₂) (υ := uOf q₁) (ῡ := uOf q₂)
            (Dν := Dν) (ν := ν) hγconj hDν hν_γ
            (hγBar_eq ▸ hG_grad) (hγBar_eq ▸ hG_val)
        simpa [hγBar_eq] using this
      hF_unreg_meas := hF_unreg_meas
      hF_unreg_bound := by
        -- Use the K0 form pointwise bound at the K0 segment positivity.
        intro t ht
        filter_upwards [hbound_K0, hPos_nn] with x hx hposx
        exact hx t ht (hposx t ht)
      hF_gat_meas := hF_gat_meas
      hF_gat_bound := by
        intro t ht
        have hgat :=
          aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
            (γBar := γBar) hγ_one_lt
            (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν
        refine MeasureTheory.ae_of_all _ ?_
        intro x
        exact hgat x t ht }

/-- **Sanity-check `example`.** The K0-form producer
`hemicontSegmentData_of_K0Aepsi` type-checks at any pair of K0_Aepsi
endpoints with any test direction, given the K0-form dominator certs
`(C', hHabs_K0, hmDpH_K0)` plus the caller-supplied segment
strict-positivity certificate `hPosSeg`. -/
example
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {q₁ q₂ : XBanach d βBarReal γBarReal}
    (hq₁ : q₁ ∈ K0_Aepsi d βBarReal γBarReal)
    (hq₂ : q₂ ∈ K0_Aepsi d βBarReal γBarReal)
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₁) (mOf q₁) (uOf q₁))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH (DuOf q₂) (mOf q₂) (uOf q₂))
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (C' : ℝ) (hC'_pos : 0 < C')
    (hHabs_K0 : IsHK0AbsDominator (d := d) h
                  (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂) C')
    (hmDpH_K0 : IsmDpHK0Dominator (d := d) h
                  (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂))
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb (mOf q₁) (mOf q₂) t x)
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|))
    (hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1))
    (hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1))
    (hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)))
    (hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α)))
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|))
    (hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1))
    (hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                    (uOf q₁) (uOf q₂) Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
      (uOf q₁) (uOf q₂) Dν η ν :=
  hemicontSegmentData_of_K0Aepsi hq₁ hq₂ aux₁ aux₂ hβconj hγconj h
    C' hC'_pos hHabs_K0 hmDpH_K0 hPosSeg
    hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq
    hV hΔυ hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm hΔm1
    hG_grad hG_val hF_unreg_meas hF_gat_meas

/-! ## K0 dominator producers from paper hypotheses (Child C)

The K0-form pointwise dominator hypotheses `IsHK0AbsDominator` and
`IsmDpHK0Dominator` (from `Hemicontinuity.lean`) are derived here from
the paper hypotheses

* `hpow : HypothesisPowerGrowth H DpH`,
* `hHat0 : HypothesisHat0 H`,
* `hAgree : H_zero_eq_Hext H`,

without any per-pair residues. The K-strict bounds
`hemicont_H_abs_dominator` / `hemicont_mDpH_dominator` are valid for
`m > 0`; the K0 form extends them to `m ≥ 0` by limit-passage at the
boundary `m = 0`. The `m = 0` case uses

* for the `H` abs bound, the closed-form
  `Hamiltonian.H_abs_bound_nonneg_of_hHat0` (`Estimates.lean`,
  Phase H5d auxiliary), which uses the real-valued right-continuity
  `H_rc0_of_hHat0` (derived from `(hHat0, hAgree)` together with the
  finiteness rider `Hext_finite_at_zero_of_powerGrowth(hpow, hHat0)`);
* for the `m · D_pH` bound, the trivial fact that at `m = 0` both
  sides vanish: LHS `‖0 • _‖ = 0`, RHS uses
  `Real.zero_rpow` for the strictly positive exponent `1+β-β/α`.

The unifying constant for the K0 abs bound is `C' := h.C` (the
`Hamiltonian.H_abs_bound_nonneg_of_hHat0` shape).
-/

/-- **K0 abs-bound producer from paper hypotheses.** From
`(hpow, hHat0, hAgree)` produce `IsHK0AbsDominator h μ mBar Dυ Dῡ h.C`
for any choice of `(μ, mBar, Dυ, Dῡ)`. The pointwise bound holds
a.e.-uniformly in `t ∈ [0,1]` whenever `0 ≤ cxComb μ mBar t x`. -/
theorem isHK0AbsDominator_of_paperHypotheses
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : HypothesisHat0 (d := d) H)
    (hAgree : H_zero_eq_Hext (d := d) H)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    IsHK0AbsDominator (d := d) hpow μ mBar Dυ Dῡ hpow.C := by
  -- Derive the finiteness rider from the upper bound at `p = 0`.
  have hFin : Hext_finite_at_zero (d := d) H :=
    Hext_finite_at_zero_of_powerGrowth (d := d) hpow hHat0
  -- The closed-form abs bound for `m ≥ 0`, with `C = h.C`.
  have habs := H_abs_bound_nonneg_of_hHat0 (d := d) hpow hHat0 hFin hAgree
  -- Specialise at `(p := cxCombGrad …, m := cxComb …)`.
  unfold IsHK0AbsDominator
  filter_upwards [habs] with x hxAbs t _ht hμt_nn
  exact hxAbs (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x) hμt_nn

/-- **K0 `m·D_pH` bound producer from paper hypotheses.** From
`(hpow, hHat0, hAgree)` produce `IsmDpHK0Dominator h μ mBar Dυ Dῡ`
for any choice of `(μ, mBar, Dυ, Dῡ)`.

The K-strict pointwise bound `mDpH_pointwise_bound` holds for `m > 0`.
At the boundary `m = 0` both sides collapse to zero:
* LHS = `‖0 • DpH x p 0‖ = 0`,
* RHS = `h.C · (0 · ‖p‖^{α-1} + 0^{1+β-β/α} + 0) = 0`,

since `1+β-β/α > 0` (strict super-linearity `α > 1, β > 0`) and
`Real.zero_rpow` gives `0^c = 0` for any `c ≠ 0`. -/
theorem isMDpHK0Dominator_of_paperHypotheses
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (_hHat0 : HypothesisHat0 (d := d) H)
    (_hAgree : H_zero_eq_Hext (d := d) H)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    IsmDpHK0Dominator (d := d) hpow μ mBar Dυ Dῡ := by
  -- The K-strict pointwise bound (m > 0 form) at the convex combination.
  -- We unfold `IsmDpHK0Dominator` and extend to `m ≥ 0`.
  unfold IsmDpHK0Dominator
  -- Key positivity facts needed for the `m = 0` branch.
  have hαpos : 0 < hpow.α := lt_trans one_pos hpow.hα
  have hβpos : 0 < hpow.β := hpow.hβ
  -- `1 + β - β/α > 0` since `β/α < β` (because `α > 1`).
  have hexp_pos : 0 < 1 + hpow.β - hpow.β / hpow.α := by
    have hbb : hpow.β / hpow.α < hpow.β := by
      have heq : hpow.β / hpow.α * hpow.α = hpow.β :=
        div_mul_cancel₀ _ (ne_of_gt hαpos)
      nlinarith [hpow.hα, hβpos, hαpos]
    linarith
  have hexp_ne : (1 + hpow.β - hpow.β / hpow.α) ≠ 0 := ne_of_gt hexp_pos
  -- Use `hpow.DpH_upper` a.e.-set directly.
  filter_upwards [hpow.DpH_upper] with x hxDpH t hμt_nn
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hp_t
  set μt : ℝ := cxComb μ mBar t x with hμt_def
  rcases hμt_nn.lt_or_eq with hμt_pos | hμt_zero
  · -- Strict-positivity case `0 < μt`: re-derive the K-strict bound
    -- from `hpow.DpH_upper` at `(p := p_t, m := μt)`.
    -- ‖μt • DpH x p_t μt‖ = μt * ‖DpH x p_t μt‖ (since μt > 0).
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμt_pos]
    have hb := hxDpH p_t μt hμt_pos
    have hmle :
        μt * ‖DpH x p_t μt‖
          ≤ μt * (hpow.C * (‖p_t‖ ^ (hpow.α - 1)
                            + μt ^ (hpow.β - hpow.β / hpow.α) + 1)) :=
      mul_le_mul_of_nonneg_left hb hμt_pos.le
    -- Expand `μt · μt^{β-β/α} = μt^{1+β-β/α}`.
    have hpow_id : μt * μt ^ (hpow.β - hpow.β / hpow.α)
                    = μt ^ (1 + hpow.β - hpow.β / hpow.α) := by
      have hμt_one : μt ^ (1 : ℝ) = μt := Real.rpow_one μt
      calc μt * μt ^ (hpow.β - hpow.β / hpow.α)
          = μt ^ (1 : ℝ) * μt ^ (hpow.β - hpow.β / hpow.α) := by rw [hμt_one]
        _ = μt ^ ((1 : ℝ) + (hpow.β - hpow.β / hpow.α)) :=
              (Real.rpow_add hμt_pos 1 _).symm
        _ = μt ^ (1 + hpow.β - hpow.β / hpow.α) := by ring_nf
    have hrhs_eq :
        μt * (hpow.C * (‖p_t‖ ^ (hpow.α - 1)
                        + μt ^ (hpow.β - hpow.β / hpow.α) + 1))
          = hpow.C * (μt * ‖p_t‖ ^ (hpow.α - 1)
                      + μt ^ (1 + hpow.β - hpow.β / hpow.α) + μt) := by
      have hexpand : μt * (hpow.C * (‖p_t‖ ^ (hpow.α - 1)
                          + μt ^ (hpow.β - hpow.β / hpow.α) + 1))
          = hpow.C * (μt * ‖p_t‖ ^ (hpow.α - 1)
                      + μt * μt ^ (hpow.β - hpow.β / hpow.α) + μt) := by ring
      rw [hexpand, hpow_id]
    linarith
  · -- Boundary case `μt = 0`: both sides vanish.
    have hμt_eq : μt = 0 := hμt_zero.symm
    -- LHS = `‖0 • DpH x p_t 0‖ = ‖0‖ = 0`.
    have hLHS : ‖μt • DpH x p_t μt‖ = 0 := by
      rw [hμt_eq, zero_smul, norm_zero]
    -- RHS = `h.C · (0 · ‖p_t‖^{α-1} + 0^{1+β-β/α} + 0) = 0`.
    have h0pow : (0 : ℝ) ^ (1 + hpow.β - hpow.β / hpow.α) = 0 :=
      Real.zero_rpow hexp_ne
    have hRHS_eq :
        hpow.C * (μt * ‖p_t‖ ^ (hpow.α - 1)
                  + μt ^ (1 + hpow.β - hpow.β / hpow.α) + μt) = 0 := by
      rw [hμt_eq]; rw [h0pow]; ring
    rw [hLHS, hRHS_eq]

/-! ### Per-q `MFGOpEpsAuxHyps` at K0 endpoints (Child C, auxHyps part)

Below we package `auxHyps_K0_at_setPaperTriple`, the K0-form analogue
of `auxHyps_of_paperHypotheses_at_triple`. The signature mirrors the
K-strict version, but `m ≥ 0` a.e. replaces `m > 0` a.e., and the
F-side discharges use the K0-form pointwise abs bound
`Hamiltonian.H_abs_bound_nonneg_of_hHat0`. The unifying constant is
`C' := h.C` (no caller-supplied `C'`). -/

/-- **K0-form per-q `MFGOpEpsAuxHyps` producer.**

Mirrors `auxHyps_of_paperHypotheses_at_triple` with two differences:
* `m ≥ 0` a.e. (rather than `m > 0` a.e.);
* the unifying constant for the HJB-side dominator is `C' := h.C`
  (so no caller-supplied `(C', h_upper)` is required — instead the
  caller supplies the `(hHat0, hAgree)` riders driving
  `H_abs_bound_nonneg_of_hHat0`).

The flux-side discharge uses an inline pointwise bound (the same
`mDpH_pointwise_bound`-trivializes-at-zero argument used in
`mDpH_integrable_of_memLpPer`). -/
theorem auxHyps_K0_at_setPaperTriple
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ)
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- **K0 form**: `m ≥ 0` a.e. (rather than `m > 0` a.e.).
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
    -- Measurability witnesses.
    (hF_HJB_meas :
      AEStronglyMeasurable
        (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ i,
        AEStronglyMeasurable
          (fun x => m x * DpH x (fun j => Du j x) (m x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Dominator `MemLpPer` certificates at the K0 form: HJB-side uses
    -- `C' := h.C` as the unifying constant (no caller-supplied `C'`).
    (hG_HJB_dom :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1)
            + hpow.C * (m x ^ hpow.β + 1)
            + |u x| + |V x|))
    (hG_flux_dom :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (m x * ‖fun j => Du j x‖ ^ (hpow.α - 1)
                      + m x ^ (1 + hpow.β - hpow.β / hpow.α) + m x)))
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) m)
    -- G-side certificates (passed through).
    (hG_grad_mem :
      ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (G_grad γBarReal Du i))
    (hG_val_mem :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal u)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH Du m u := by
  -- Derive the finiteness rider from `(hpow, hHat0)`.
  have hFin : Hamiltonian.Hext_finite_at_zero (d := d) H :=
    Hamiltonian.Hext_finite_at_zero_of_powerGrowth (d := d) hpow hHat0
  -- ---------------------------------------------------------------------
  -- F_HJB discharge: pointwise `‖-u-H+V‖ ≤ G_HJB` via the K0 abs bound.
  -- ---------------------------------------------------------------------
  have habs := Hamiltonian.H_abs_bound_nonneg_of_hHat0
                  (d := d) hpow hHat0 hFin hAgree
  have hF_HJB_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x) (m x) + V x‖
          ≤ (1 : ℝ) *
            ‖hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1)
              + hpow.C * (m x ^ hpow.β + 1)
              + |u x| + |V x|‖ := by
    filter_upwards [habs, hμ_nn] with x hxAbs hxμ
    set p_x : Fin d → ℝ := fun i => Du i x with hp_x
    have hxμ' : 0 ≤ m x := hxμ
    have hα_p_nn : 0 ≤ ‖p_x‖ ^ hpow.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_m_nn : 0 ≤ m x ^ hpow.β := Real.rpow_nonneg hxμ' _
    -- K0 abs bound at `(p_x, m x)`.
    have hH_abs : |H x p_x (m x)|
                  ≤ hpow.C * (‖p_x‖ ^ hpow.α + 1)
                      + hpow.C * (m x ^ hpow.β + 1) :=
      hxAbs p_x (m x) hxμ'
    -- Triangle: `|−u − H + V| ≤ |u| + |H| + |V|`.
    have htri :
        ‖-(u x) - H x p_x (m x) + V x‖
          ≤ |u x| + |H x p_x (m x)| + |V x| := by
      rw [Real.norm_eq_abs]
      have h1 : |(-(u x)) - H x p_x (m x) + V x|
                ≤ |(-(u x)) - H x p_x (m x)| + |V x| := abs_add_le _ _
      have h2 : |(-(u x)) - H x p_x (m x)|
                ≤ |-(u x)| + |-(H x p_x (m x))| := by
        have hh := abs_add_le (-(u x)) (-(H x p_x (m x)))
        have heq : -(u x) + -(H x p_x (m x)) = (-(u x)) - H x p_x (m x) := by
          ring
        rw [heq] at hh
        exact hh
      have h3 : |-(u x)| = |u x| := abs_neg _
      have h4 : |-(H x p_x (m x))| = |H x p_x (m x)| := abs_neg _
      linarith
    have htotal :
        ‖-(u x) - H x p_x (m x) + V x‖
          ≤ hpow.C * (‖p_x‖ ^ hpow.α + 1)
              + hpow.C * (m x ^ hpow.β + 1) + |u x| + |V x| := by linarith
    have hG_nn :
        0 ≤ hpow.C * (‖p_x‖ ^ hpow.α + 1)
            + hpow.C * (m x ^ hpow.β + 1) + |u x| + |V x| := by
      have hC1 : 0 ≤ hpow.C * (‖p_x‖ ^ hpow.α + 1) := by
        have : 0 ≤ ‖p_x‖ ^ hpow.α + 1 := by linarith
        exact mul_nonneg hpow.hC.le this
      have hC2 : 0 ≤ hpow.C * (m x ^ hpow.β + 1) := by
        have : 0 ≤ m x ^ hpow.β + 1 := by linarith
        exact mul_nonneg hpow.hC.le this
      linarith [abs_nonneg (u x), abs_nonneg (V x)]
    -- Goal: `‖LHS‖ ≤ 1 * ‖RHS‖`. Simplify by `one_mul` and norm-of-nonneg.
    have hRHS_norm :
        ‖hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1)
          + hpow.C * (m x ^ hpow.β + 1) + |u x| + |V x|‖
          = hpow.C * (‖fun i => Du i x‖ ^ hpow.α + 1)
            + hpow.C * (m x ^ hpow.β + 1) + |u x| + |V x| := by
      rw [Real.norm_eq_abs, abs_of_nonneg hG_nn]
    rw [one_mul, hRHS_norm]
    exact htotal
  have hF_HJB :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x) :=
    MemLp.toMemLpPer (MemLp.of_le_mul hG_HJB_dom.toMemLp hF_HJB_meas hF_HJB_bound)
  -- ---------------------------------------------------------------------
  -- F_flux i discharge: pointwise `‖m·DpH ⋯ i‖ ≤ G_flux x` via the
  -- K-strict bound for `m > 0` and the trivialization at `m = 0`.
  -- ---------------------------------------------------------------------
  have hαpos : 0 < hpow.α := lt_trans one_pos hpow.hα
  have hβpos : 0 < hpow.β := hpow.hβ
  have hexp_pos : 0 < 1 + hpow.β - hpow.β / hpow.α := by
    have hbb : hpow.β / hpow.α < hpow.β := by
      have heq : hpow.β / hpow.α * hpow.α = hpow.β :=
        div_mul_cancel₀ _ (ne_of_gt hαpos)
      nlinarith [hpow.hα, hβpos, hαpos]
    linarith
  have hF_flux : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => m x * DpH x (fun j => Du j x) (m x) i) := by
    intro i
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ‖m x * DpH x (fun j => Du j x) (m x) i‖
            ≤ (1 : ℝ) *
              ‖hpow.C * (m x * ‖fun j => Du j x‖ ^ (hpow.α - 1)
                          + m x ^ (1 + hpow.β - hpow.β / hpow.α) + m x)‖ := by
      filter_upwards [hpow.DpH_upper, hμ_nn] with x hxDpH hxμ
      set p_x : Fin d → ℝ := fun j => Du j x with hp_x
      have hxμ' : 0 ≤ m x := hxμ
      have hα1_nn : 0 ≤ ‖p_x‖ ^ (hpow.α - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have hμα_nn : 0 ≤ m x ^ (1 + hpow.β - hpow.β / hpow.α) :=
        Real.rpow_nonneg hxμ' _
      have hG_nn :
          0 ≤ hpow.C * (m x * ‖p_x‖ ^ (hpow.α - 1)
                        + m x ^ (1 + hpow.β - hpow.β / hpow.α) + m x) := by
        apply mul_nonneg hpow.hC.le
        have h1 : 0 ≤ m x * ‖p_x‖ ^ (hpow.α - 1) := mul_nonneg hxμ' hα1_nn
        linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
      -- Coordinate bound: `|m x * DpH x p_x (m x) i| ≤ ‖m x • DpH x p_x (m x)‖`.
      rcases hxμ'.lt_or_eq with hxpos | hxz
      · -- Case `0 < m x`: use the K-strict pointwise bound, restricted
        -- to coordinate `i` (`|v i| ≤ ‖v‖`).
        have hb := hxDpH p_x (m x) hxpos
        have hcoord : |m x * DpH x p_x (m x) i| ≤ m x * ‖DpH x p_x (m x)‖ := by
          rw [abs_mul, abs_of_pos hxpos]
          have hi : |DpH x p_x (m x) i| ≤ ‖DpH x p_x (m x)‖ :=
            norm_le_pi_norm (DpH x p_x (m x)) i
          exact mul_le_mul_of_nonneg_left hi hxpos.le
        have hmle :
            m x * ‖DpH x p_x (m x)‖
              ≤ m x * (hpow.C * (‖p_x‖ ^ (hpow.α - 1)
                                  + m x ^ (hpow.β - hpow.β / hpow.α) + 1)) :=
          mul_le_mul_of_nonneg_left hb hxpos.le
        -- Expand `m x · m x^{β-β/α} = m x^{1+β-β/α}`.
        have hpow_id : m x * m x ^ (hpow.β - hpow.β / hpow.α)
                        = m x ^ (1 + hpow.β - hpow.β / hpow.α) := by
          have hxone : m x ^ (1 : ℝ) = m x := Real.rpow_one (m x)
          calc m x * m x ^ (hpow.β - hpow.β / hpow.α)
              = m x ^ (1 : ℝ) * m x ^ (hpow.β - hpow.β / hpow.α) := by
                rw [hxone]
            _ = m x ^ ((1 : ℝ) + (hpow.β - hpow.β / hpow.α)) :=
                  (Real.rpow_add hxpos 1 _).symm
            _ = m x ^ (1 + hpow.β - hpow.β / hpow.α) := by ring_nf
        have hrhs_eq :
            m x * (hpow.C * (‖p_x‖ ^ (hpow.α - 1)
                            + m x ^ (hpow.β - hpow.β / hpow.α) + 1))
              = hpow.C * (m x * ‖p_x‖ ^ (hpow.α - 1)
                          + m x ^ (1 + hpow.β - hpow.β / hpow.α) + m x) := by
          have hexpand : m x * (hpow.C * (‖p_x‖ ^ (hpow.α - 1)
                              + m x ^ (hpow.β - hpow.β / hpow.α) + 1))
              = hpow.C * (m x * ‖p_x‖ ^ (hpow.α - 1)
                          + m x * m x ^ (hpow.β - hpow.β / hpow.α) + m x) := by
            ring
          rw [hexpand, hpow_id]
        linarith
      · -- Case `m x = 0`: LHS = 0, RHS ≥ 0.
        have hmzero : m x = 0 := hxz.symm
        have hLHS : m x * DpH x p_x (m x) i = 0 := by rw [hmzero]; ring
        rw [hLHS, abs_zero]
        exact hG_nn
    exact MemLp.toMemLpPer (MemLp.of_le_mul hG_flux_dom.toMemLp (hF_flux_meas i) hbound)
  -- ---------------------------------------------------------------------
  -- F_mass discharge: same as K-strict version.
  -- ---------------------------------------------------------------------
  have hF_mass :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => m x - 1) :=
    Hamiltonian.μMinusOne_memLp_of_betaBar (d := d)
      (p := ENNReal.ofReal βBarReal) (q := ENNReal.ofReal γBarReal')
      m hm_memLp hγ'_le_β ENNReal.ofReal_ne_top
  -- Assemble the record.
  exact
    { hβ := hβ
      hγ := hγ
      hF_HJB := hF_HJB
      hF_flux := hF_flux
      hF_mass := hF_mass
      hG_grad := hG_grad_mem
      hG_val := hG_val_mem
      hβTop := hβTop }

/-- **Sanity-check `example`** for the K0 dominator producers and the
K0-form per-q `MFGOpEpsAuxHyps` producer. Pins the type-shapes of all
three feeders. -/
example
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : HypothesisHat0 (d := d) H)
    (hAgree : H_zero_eq_Hext (d := d) H)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    IsHK0AbsDominator (d := d) hpow μ mBar Dυ Dῡ hpow.C
      ∧ IsmDpHK0Dominator (d := d) hpow μ mBar Dυ Dῡ :=
  ⟨isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree μ mBar Dυ Dῡ,
   isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree μ mBar Dυ Dῡ⟩

/-! ## Composition: `Aepsi_hemicont_of_paperHypotheses`

The K_Aepsi-form CLM hemicontinuity wrap
`isHemicontinuous_Aepsi_CLM_K_Aepsi` in `Banach/AbstractLifts.lean`
takes a per-segment `hData` argument producing the
`HemicontSegmentData` bundle for every pair of K_Aepsi endpoints
together with a Banach test direction. We discharge that argument via
`hemicontSegmentData_of_KAepsi`, which itself consumes:

* the per-q `MFGOpEpsAuxHyps` certificates supplied by `auxHypsK`,
* the paper power-growth hypothesis `hpow` and its slice form
  `h_slice` (paper Hypothesis-A `(a:H)`),
* the Hölder-pair facts `hβconj`, `hγconj` between the user-supplied
  primal exponents and their conjugates,
* the natural-form `MemLpPer p`-of-power residues for the **segment**
  dominators (parameterised over every pair of K_Aepsi endpoints
  and every Banach test direction; this is the
  `infra-P4-ADFGU-test-triple-dominator-closure` content that
  `auxHypsK` does not bundle), and
* the two genuinely test-direction-dependent measurability residues
  `hF_unreg_meas`, `hF_gat_meas`.

The result is the composition theorem
`Aepsi_hemicont_of_paperHypotheses`, which targets the totalized
operator `Aepsi_CLM_opK`. It mirrors the shape of
`Aepsi_mono_of_paperHypotheses` and `Aepsi_coercive_of_paperHypotheses`
above. -/

/-- **Composition theorem.** Hemicontinuity of the K_Aepsi-totalized
operator `Aepsi_CLM_opK auxHypsK ε` on the strict-positivity cone
`K_Aepsi`, threaded from the K_Aepsi-indexed `auxHypsK` supplier and
the paper power-growth hypotheses, with the per-pair / per-test
natural-form `MemLpPer p`-residues and Caratheodory measurability
threaded as parameters (mirroring `hScalarMono`/`hVecMono` in
`Aepsi_mono_of_paperHypotheses` and `hbound_residue` in
`Aepsi_coercive_of_paperHypotheses`).

The pointwise content of paper Lemma `lem:hemicont` (lines 1038–1043)
is delegated to `hemicontSegmentData_of_KAepsi`; this composition
theorem performs the K_Aepsi-form lift to the totalized operator. -/
theorem Aepsi_hemicont_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    -- Paper power-growth hypothesis and its slice form (paper `(a:H)`).
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    -- Regularity consumed by the K_Aepsi-form lift; `1 < γBarReal`
    -- consumed by the segment DCT (Phase 1c relaxation, see
    -- `infra-P5-theorem1-phase-1c`).
    (hReg : RegularityH (d := d) H DpH)
    (hγ : 1 < γBarReal)
    -- Hölder-pair facts on the real exponents (matching the shape of
    -- `auxHyps_of_paperHypotheses_on_KAepsi`'s callers).
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- `V`-regularity at the conjugate exponent `βBarReal'`.
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    -- Per-pair, per-test natural-form `MemLpPer p`-of-power residues
    -- consumed by the segment dominator's `IntegrableOn` certificates.
    -- These are the `infra-P4-ADFGU-test-triple-dominator-closure`
    -- residues (segment-dominator `MemLpPer` witnesses), threaded as
    -- a parametric supplier indexed by `(u, v, w) ∈ K_Aepsi × K_Aepsi
    -- × XBanach`, plus the test-triple `MemLpPer` certificates.
    (hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      -- Test-triple `MemLpPer` regularity at the test exponents
      -- (`η`, `Dν`, `ν` of `w`) used by the natural-form integrability.
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                    (fun x => ⇑(w.2.2 i) x)) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
      -- Segment-dominator `MemLpPer p`-of-power residues.
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |uOf u x| + |uOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |mOf u x| + |mOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1)))
    -- Caratheodory measurability of the segment integrands (genuinely
    -- test-direction-dependent residues, see the producer's own
    -- analysis in `hemicontSegmentData_of_KAepsi`).
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d))) :
    Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) := by
  -- Build the per-segment `HemicontSegmentData` from the K_Aepsi
  -- producer, then compose with the K_Aepsi-form lift.
  refine isHemicontinuous_Aepsi_CLM_K_Aepsi (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hReg hγ ?_
  intro u v hu hv w
  -- Unpack the per-pair, per-test `MemLpPer`-residues.
  obtain ⟨hη, hDν, hν_β, hν_γ,
          hΔυ, hΔp_pow, hΔm_pow, hΔm_grad, hΔm_endpoint, hΔm,
          hΔm1, hG_grad, hG_val⟩ := hSegRes u v hu hv w
  -- Apply the producer at `q₁ := v`, `q₂ := u`, `γBar := γBarReal`.
  -- The product-form Gateaux pointwise bound only needs `1 < γBarReal`,
  -- which is exactly `hγ` (Phase 1c, `infra-P5-theorem1-phase-1c`).
  exact hemicontSegmentData_of_KAepsi (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (γBar := γBarReal) (V := V) (H := H) (DpH := DpH)
    hv hu (auxHypsK v hv) (auxHypsK u hu)
    hβconj hγconj hpow h_slice hγ
    (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)
    hη hDν hν_β hν_γ rfl
    hV hΔυ hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm hΔm1
    hG_grad hG_val
    (hF_unreg_meas u v hu hv w) (hF_gat_meas u v hu hv w)

/-- **Sanity-check `example`.** `Aepsi_hemicont_of_paperHypotheses`
accepts the K_Aepsi-indexed `auxHypsK` supplier, the paper power-growth
hypotheses, the segment-dominator residue supplier, and the two
test-direction-dependent measurability residues, and delivers
`IsHemicontinuous (K_Aepsi …) (Aepsi_CLM_opK …)`. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hReg : RegularityH (d := d) H DpH)
    (hγ : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                    (fun x => ⇑(w.2.2 i) x)) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |uOf u x| + |uOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |mOf u x| + |mOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1)))
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d))) :
    Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) :=
  Aepsi_hemicont_of_paperHypotheses (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hpow h_slice hReg hγ hβconj hγconj hV
    hSegRes hF_unreg_meas hF_gat_meas

/-! ## Closed-form composition: `aepsiUniformContextK_of_paperHypotheses`

This is the closed-form composition theorem T10's pipeline calls per `k`:
build an `AepsiUniformContextK` directly from the paper hypotheses,
threading the residue parameters of the four K_Aepsi-form feeders plus
the weak-derivative tie residue and the K0 supplier residue for the
`aux` field.

Per the task spec, the assembly uses:
* `auxHypsK := auxHyps_of_paperHypotheses_on_KAepsi …`
* `hMono := Aepsi_mono_of_paperHypotheses …`
* `hHC := Aepsi_hemicont_of_paperHypotheses …`
* `hCoerc := Aepsi_coercive_of_paperHypotheses …`
* `hWeakDeriv := <residue>` (per-K0 weak-derivative tie)
* `hReflexive := lpSobolev_product_isReflexive …`
* base point `qRef := qRef_simplePower …` with membership
  `qRef_simplePower_mem_K_Aepsi`.

The residues are paraphernalia from the four feeders' signatures; this
composition is *pure orchestration* (no new analysis). Once T10 lands,
each of these residues will be discharged from the paper hypotheses
either through dedicated backlog tasks (paper line 944, 982 residues;
segment-dominator closure; weak-derivative tie via `K0_Aepsi_W`) or as
the elementary algebra they are. -/

/-- **Closed-form composition theorem.** Build the K_Aepsi-form
abstract-VI context `AepsiUniformContextK` from the paper hypotheses,
threading the residue parameters of the four K_Aepsi-form feeders. -/
noncomputable def aepsiUniformContextK_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Paper-exponent identification residues (`auxHyps_of_paperHypotheses_on_KAepsi`).
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    -- Hölder pair residues for the K_Aepsi auxHyps feeder.
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Power-growth upper-bound residue (paper Hypothesis-A `(a:H)`).
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    -- Measurability residues (universal-q form, K_Aepsi auxHyps feeder).
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Paper-line-944 residues for monotonicity (`Aepsi_mono_of_paperHypotheses`).
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    -- Coercivity residues (`Aepsi_coercive_of_paperHypotheses_scaled`,
    -- paper line 982). Scaled-gauge form: exponent `κ > 1` and positive
    -- scaling `lamCoerc > 0`; the gauge exponent in `hbound_residue` is
    -- the supplied `κ` (typically `coercivityGaugeExponent βBarReal
    -- γBarReal = min β̄ γ̄` at the paper-faithful call site).
    (hγBar_one_lt : 1 < γBarReal)
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    -- Hemicontinuity residues (`Aepsi_hemicont_of_paperHypotheses`).
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hReg : RegularityH (d := d) H DpH)
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                    (fun x => ⇑(w.2.2 i) x)) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |uOf u x| + |uOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |mOf u x| + |mOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1)))
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    -- K0 supplier residue for the `aux` field (`MFGOpEpsUniformAux …
    -- K0_Aepsi`); the K_Aepsi-indexed feeder's strict-positivity input
    -- is incompatible with K0 elements (paper line 944's strict-pos
    -- regime), so this is threaded as a separate residue.
    (auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (DuOf q) (mOf q) (uOf q))
    -- Weak-derivative tie residue (per K0 element, projected via
    -- `aepsi_weakDerivTie_of_paperHypotheses_legacy`).
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
      βBarReal' γBarReal' := by
  classical
  -- Build the K_Aepsi-indexed `auxHypsK` supplier.
  set auxHypsK :
      ∀ q ∈ K_Aepsi d βBarReal γBarReal,
        MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
          V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
    auxHyps_of_paperHypotheses_on_KAepsi
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β
      C' hC'_pos h_upper hF_HJB_meas hF_flux_meas
    with hauxHypsK_def
  -- Reflexivity of the Banach pair, derived from `hExp` via
  -- `lpSobolev_product_isReflexive`.
  have hReflexive :
      Periodic.IsReflexiveNormedSpace (XBanach d βBarReal γBarReal) := by
    -- Step 1: `1 < βBarReal` and `0 < βBarReal`.
    have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by
      by_contra hle
      push_neg at hle
      have h1 : ENNReal.ofReal βBarReal ≤ (1 : ℝ≥0∞) := by
        calc ENNReal.ofReal βBarReal
            ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
          _ = 1 := ENNReal.ofReal_one
      exact absurd hExp.βBar_one_lt (not_lt_of_ge h1)
    have h_βBarReal_pos : (0 : ℝ) < βBarReal := by linarith
    have h_βBar_toReal_eq : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
      ENNReal.toReal_ofReal h_βBarReal_pos.le
    -- Step 2: `1 < βBarReal'` and `0 < βBarReal'`.
    have h_one_lt_βBar' : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal' :=
      hExp.betaBar'_one_lt
    have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
      by_contra hle
      push_neg at hle
      have h_zero : ENNReal.ofReal βBarReal' = 0 :=
        ENNReal.ofReal_eq_zero.mpr hle
      rw [h_zero] at h_one_lt_βBar'
      exact absurd h_one_lt_βBar' (by simp)
    have h_βBar'_toReal_eq : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
      ENNReal.toReal_ofReal h_βBarReal'_pos.le
    have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
      h_one_lt_βBar'.le
    haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') := ⟨h_one_le_βBar'⟩
    -- Step 3: ENNReal Hölder conjugacy for β.
    have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
      have := hExp.βConj
      rw [h_βBar_toReal_eq, h_βBar'_toReal_eq] at this
      exact this
    have hβConj_enn :
        ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
          (ENNReal.ofReal βBarReal') :=
      Real.HolderConjugate.ennrealOfReal hβConj_real
    haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
              (ENNReal.ofReal βBarReal') := hβConj_enn
    -- Step 4: similar setup for γ. Conjugate is `γBarReal/(γBarReal-1)`.
    have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
    have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
    let γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1)
    have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
    have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
      div_pos h_γBarReal_pos h_γBar_minus_one_pos
    have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
      show (1 : ℝ) < γBarReal / (γBarReal - 1)
      rw [lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
      linarith
    have h_one_le_γBarPrime : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarPrimeReal := by
      have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarPrimeReal :=
        ENNReal.ofReal_le_ofReal h_one_lt_γBarPrimeReal.le
      simpa using h1
    haveI : Fact (1 ≤ ENNReal.ofReal γBarPrimeReal) := ⟨h_one_le_γBarPrime⟩
    have h_γBar_toReal_eq :
        (ENNReal.ofReal γBarReal).toReal = γBarReal :=
      ENNReal.toReal_ofReal h_γBarReal_pos.le
    have hγConj_real : Real.HolderConjugate γBarReal γBarPrimeReal := by
      have := hExp.γConj
      rw [h_γBar_toReal_eq] at this
      show Real.HolderConjugate γBarReal (γBarReal / (γBarReal - 1))
      exact this
    have hγConj_enn :
        ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal γBarPrimeReal) :=
      Real.HolderConjugate.ennrealOfReal hγConj_real
    haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal γBarPrimeReal) := hγConj_enn
    -- Step 5: top-finiteness.
    have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    -- Step 6: invoke the reflexivity lemma.
    exact StationaryMFG.Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Build the four feeder outputs.
  have hMono :
      Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) :=
    Aepsi_mono_of_paperHypotheses (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK hmon hε.le hScalarMono hVecMono
  have hCoerc :
      Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε)
        (qRef_simplePower d βBarReal γBarReal) :=
    Aepsi_coercive_of_paperHypotheses_scaled (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK ε κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
  have hHC :
      Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) :=
    Aepsi_hemicont_of_paperHypotheses (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK hpow h_slice hReg hγ2 hβconj hγconj hV
      hSegRes hF_unreg_meas hF_gat_meas
  -- The K0 uniform aux record from the K0 supplier residue.
  have hAux :
      MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal'
        (K0_Aepsi d βBarReal γBarReal) :=
    mfgOpEps_uniformAux_of_perPairAuxHyps ε
      (K0_Aepsi d βBarReal γBarReal) auxHypsK0
  -- Assemble the context record.
  exact {
    hReflexive := hReflexive
    auxHypsK := auxHypsK
    qRef := qRef_simplePower d βBarReal γBarReal
    hqRef := qRef_simplePower_mem_K_Aepsi d βBarReal γBarReal
    aux := hAux
    hMono := hMono
    hHC := hHC
    hCoerc := hCoerc
    hWeakDeriv := hWeakDerivK0
  }

/-- **Sanity-check `example`.** The closed-form composition theorem
`aepsiUniformContextK_of_paperHypotheses` accepts the paper hypotheses
plus the threaded residues of the four K_Aepsi-form feeders, plus the
K0 supplier and weak-derivative tie residues, and delivers an
`AepsiUniformContextK` consumable by `exists_banachVI_at_eps_KAepsi`
(and hence by `exists_regularizedBareSolution_K`). -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hγBar_one_lt : 1 < γBarReal)
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hReg : RegularityH (d := d) H DpH)
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                    (fun x => ⇑(w.2.2 i) x)) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |uOf u x| + |uOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |mOf u x| + |mOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1)))
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
      βBarReal' γBarReal' :=
  aepsiUniformContextK_of_paperHypotheses (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hε hmon hpow hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hβTop hγ'_le_β
    C' hC'_pos h_upper hF_HJB_meas hF_flux_meas
    hScalarMono hVecMono
    hγBar_one_lt κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
    h_slice hReg hγ2 hβconj hγconj
    hSegRes hF_unreg_meas hF_gat_meas
    auxHypsK0 hWeakDerivK0

/-! ## Closed-form aggregator: `aepsiUniformContextK_of_paperHypotheses_closed`

This is the partially-closed wrapper around
`aepsiUniformContextK_of_paperHypotheses`. It absorbs the
**immediately derivable** residues (group A in the task notes):

* `hReg := hpow.toRegularityH`,
* `C' := hpow.C`, `hC'_pos := hpow.hC`,
* `hγBar_one_lt := hExp.γBar_one_lt_real`,
* `hβTop := hExp.gammaBar_lt_top.ne`.

The remaining residues stay as explicit parameters. They split into:

* **Group B — algebra/exponent identifications** (`hβBar_eq`,
  `hγBar_eq`, `hβBar'_eq`, `hγBar'_eq`, `hβ`, `hγ`, `hβγ`,
  `hβ'_le_β`, `hγ2`, `hβconj`, `hγconj`): only true at the paper
  exponents `paperBetaBar hpow.β`, `paperGammaBar hpow.α hpow.β`,
  etc. They cannot be derived from `(hpow, hExp)` alone at arbitrary
  type-level `(βBarReal, γBarReal, βBarReal', γBarReal')`. Closing
  these requires either specialising the wrapper to paper exponents
  or threading additional bridging equalities. Filed as a follow-up
  task `infra-P4-aepsiUniformContextK-closed-residue-discharge`.
* **Group C — paper-level analytic residues** (`h_upper`,
  `hF_HJB_meas`, `hF_flux_meas`, `hScalarMono`, `hVecMono`, `Ccoerc`,
  `hbound_residue`, `h_slice`, `hSegRes`, `hF_unreg_meas`,
  `hF_gat_meas`, `auxHypsK0`, `hWeakDerivK0`): paper §8 analytic
  facts (paper lines 944, 982, 1038–1043) authorised as paper-residue
  inputs per CONVENTIONS §1b.

The signature still satisfies the task's intent: it presents
`(hε, hmon, hpow, hV, hExp)` as the four primary paper hypotheses,
plus the residues that genuinely cannot be derived from them at this
level of generality. -/

/-- **Closed-form aggregator** (partial closure). Wrap
`aepsiUniformContextK_of_paperHypotheses` with the four
immediately-derivable residues internalised: regularity, the
power-growth constant, the `1 < γBarReal` fact, and `γBarReal ≠ ⊤`. -/
noncomputable def aepsiUniformContextK_of_paperHypotheses_closed
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV   : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Group B (algebra/exponent identifications, see the section
    -- docstring above).
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Phase 1c (`infra-P5-theorem1-phase-1c`): relaxed from `2 ≤ γBarReal`
    -- to `1 < γBarReal` (the only consumer is the segment DCT, which
    -- needs only `1 < γBarReal`).
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- Group C (paper-level analytic residues, paper §8).
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / hpow.C)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                    (fun x => ⇑(w.2.2 i) x)) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |uOf u x| + |uOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |mOf u x| + |mOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1)))
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
      βBarReal' γBarReal' :=
  -- Group A — derived internally:
  --   * `hReg := hpow.toRegularityH`,
  --   * `(C', hC'_pos) := (hpow.C, hpow.hC)`,
  --   * `hγBar_one_lt := hExp.γBar_one_lt_real`,
  --   * `hβTop := hExp.gammaBar_lt_top.ne`.
  aepsiUniformContextK_of_paperHypotheses (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hε hmon hpow hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hExp.gammaBar_lt_top.ne hγ'_le_β
    hpow.C hpow.hC h_upper hF_HJB_meas hF_flux_meas
    hScalarMono hVecMono
    hExp.γBar_one_lt_real κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
    h_slice hpow.toRegularityH hγ2 hβconj hγconj
    hSegRes hF_unreg_meas hF_gat_meas
    auxHypsK0 hWeakDerivK0

/-- **Sanity-check `example`.**
`aepsiUniformContextK_of_paperHypotheses_closed` accepts the four
paper hypotheses `(hε, hmon, hpow, hV, hExp)` plus the
algebra/exponent identifications (group B) and the paper-level
analytic residues (group C, authorised per CONVENTIONS §1b), and
delivers an `AepsiUniformContextK`. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / hpow.C)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                    (fun x => ⇑(w.2.2 i) x)) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |uOf u x| + |uOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|mOf u x| + |mOf v x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |mOf u x| + |mOf v x|) ∧
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) ∧
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1)))
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
      βBarReal' γBarReal' :=
  aepsiUniformContextK_of_paperHypotheses_closed (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hε hmon hpow hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hγ'_le_β hγ2 hβconj hγconj
    h_upper hF_HJB_meas hF_flux_meas
    hScalarMono hVecMono
    κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
    h_slice
    hSegRes hF_unreg_meas hF_gat_meas
    auxHypsK0 hWeakDerivK0

/-! ## Paper-exponent specialisation

The closed-form aggregator `aepsiUniformContextK_of_paperHypotheses_closed`
above absorbs group-A residues but still threads group-B (algebra/exponent
identifications) and group-C (paper §8 analytic) residues. The
specialisation below fixes the type-level exponents
`(βBarReal, γBarReal, βBarReal', γBarReal')` to the **paper exponents**
derived from `hpow.α, hpow.β`:

```
βBarReal  := hpow.β + 1
γBarReal  := hpow.α * (hpow.β + 1) / hpow.β
βBarReal' := (hpow.β + 1) / hpow.β
γBarReal' := γBarReal / (γBarReal - 1)
```

At those values the four group-B equality residues `hβBar_eq`, `hγBar_eq`,
`hβBar'_eq`, `hγBar'_eq` are tautologies (definitional `rfl`); the four
Hölder conjugacies `hβ`, `hβconj`, `hγ`, `hγconj` come from the
`paper_holderConjugate_*` lemmas in `ExponentFacts.lean`.

Phase 0 (`infra-P5-theorem1-phase-0`) eliminated the two routing-artefact
algebra side conditions `1 ≤ β` and `β ≤ α` by re-routing the mass term
`F_mass = m - 1` through the gamma-side Hölder pair. Phase 1c
(`infra-P5-theorem1-phase-1c`) eliminated the residual side condition
`2 ≤ γ̄` from the public surface: the relaxed hemicontinuity producer
chain only needs `1 < γ̄`, supplied internally by
`hExp.γBar_one_lt_real`.

The only inequality residue still consumed by the closed aggregator is
`γ̄' ≤ β̄`, which follows from `α > 1, β > 0` via
`Hamiltonian.gammaBar'_le_betaBar` (available unconditionally).

The group-C analytic residues are bundled into a single record
`PaperSection8AnalyticResidues` (paper §8 facts authorised per
CONVENTIONS §1b).

The result, `aepsiUniformContextK_of_paperHypotheses_closed_paper`, is the
intended call site for downstream consumers (cf. `BanachBridge.lean`
line 513): it accepts only `(hε, hmon, hpow, hV, hAnalytic)` plus the two
`Fact` instances required by `XBanach`. Note that `hExp` is **also**
derived internally via `SimplePowerExponentFacts.ofPowerGrowth`, so it
does not appear in the parameter list. -/

/-! ## Paper §8 closed/measurable partial bundle

The `PaperSection8ClosedMeasFields` bundle below carries the **closed
or mostly-closed** subset of the paper-§8 analytic residues, namely the
five fields that follow mechanically from
`Hamiltonian.HypothesisPowerGrowth` (`h_upper`, `hF_HJB_meas`,
`hF_flux_meas`) and from the `Solutions.MFG` signed-rpow monotonicity
infrastructure (`hScalarMono`, `hVecMono`). It is deliberately partial:
the hard analytic fields `hbound_residue`, `h_slice`, `hSegRes`,
`auxHypsK0`, `hWeakDerivK0` of `PaperSection8AnalyticResidues` are
**not** included here.

Discharger:
`PaperSection8ClosedMeasFields.of_paperHypotheses_paper`, taking only
`(hpow, hV)` at the paper exponents
`(βBar = β+1, γBar = α(β+1)/β, βBar' = (β+1)/β,
   γBar' = γBar/(γBar-1))`.

This is the deliverable of `paperSolFor-analytic-measurability` (phase 5). -/

/-- **Paper §8 closed/measurable partial bundle.**

Carries five of the thirteen `PaperSection8AnalyticResidues` fields —
exactly those derivable directly from `HypothesisPowerGrowth` (via
`H_upper_pointwise`, `measurable_H`, `measurable_DpH`) and from the
scalar / vector signed-rpow monotonicity (`rpow_signed_mono_scalar` /
`rpow_signed_mono_vec`).

This is intentionally partial: it excludes the real analytic fields
`hbound_residue`, `h_slice`, `hSegRes`, `auxHypsK0`, `hWeakDerivK0`. -/
structure PaperSection8ClosedMeasFields
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) where
  /-- Paper-line-944 general upper bound (Hyp-A `(a:H)`). -/
  h_upper :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mm, 0 < mm →
        H x p mm ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / hpow.C
  /-- HJB-flux measurability (universal-`q` form). -/
  hF_HJB_meas :
    ∀ q : XBanach d βBarReal γBarReal,
      MeasureTheory.AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Flux measurability (universal-`q` form). -/
  hF_flux_meas :
    ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      MeasureTheory.AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Scalar monotonicity for `absPowMinusTwo γBarReal`. -/
  hScalarMono :
    ∀ s t : ℝ,
      0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
            * (t - s)
  /-- Vector monotonicity for `vecAbsPowMinusTwo γBarReal`. -/
  hVecMono :
    ∀ v w : Fin d → ℝ,
      0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
            ⬝ (v - w)
  /-- Unregularised segment-integrand measurability (paper-§8 cxComb side). -/
  hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
              ∀ t ∈ Set.Icc (0 : ℝ) 1,
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_unreg V H DpH
                  (DuOf v) (DuOf u) (mOf v) (mOf u)
                  (uOf v) (uOf u)
                  (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- Gateaux segment-integrand measurability (paper-§8 cxComb side). -/
  hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
              ∀ t ∈ Set.Icc (0 : ℝ) 1,
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_gateaux γBarReal
                  (DuOf v) (DuOf u) (uOf v) (uOf u)
                  (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
      (MeasureTheory.volume.restrict (UnitCube d))

/-! ### Closed-field producers (Step 2 of `paperSolFor-analytic-measurability`)

`paperSection8_h_upper_of_powerGrowth` is a one-line projection of
`HypothesisPowerGrowth.H_upper_pointwise`. The two monotonicity
wrappers `paperSection8_hScalarMono_of_gamma` and
`paperSection8_hVecMono_of_gamma` reduce to
`Solutions.MFG.rpow_signed_mono_scalar` /
`Solutions.MFG.rpow_signed_mono_vec` (proved by `simpa [signedRpow]`
and a `vecSignedRpow` `funext` rewrite respectively). -/

/-- **Closed `h_upper` producer.** The `h_upper` field of
`PaperSection8ClosedMeasFields` (and of `PaperSection8AnalyticResidues`)
is a one-line projection of
`Hamiltonian.HypothesisPowerGrowth.H_upper_pointwise`. -/
theorem paperSection8_h_upper_of_powerGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (m ^ hpow.β) / hpow.C :=
  hpow.H_upper_pointwise

/-- **Closed `h_slice` producer.** The `h_slice` field of
`PaperSection8AnalyticResidues` is the paper-line-944 slice form of
the general upper bound:

  `H(x, p, m) ≤ -m^β/C + C + C·‖p‖^α + C·‖p‖·(m^{β-β/α} + 1)`.

This is **strictly weaker** than the bound supplied by
`HypothesisPowerGrowth.H_upper_pointwise`, which gives the same first
three summands and zero in place of the last `C·‖p‖·(…)` summand. Since
the latter summand is non-negative (for `m > 0`, `‖p‖ ≥ 0`, `C > 0`), the
slice bound follows by adding a non-negative slack. The "Young-inequality
derivability" advertised in the paper §8 narrative is therefore here a
trivial slack step — the genuine Young application is the *reverse*
direction in `Hamiltonian.upper_bound_powergrowth`, which absorbs the
slice cross-term `C·‖p‖·(m^{β-β/α}+1)` back into the `‖p‖^α` and `m^β`
summands via parametric Young. -/
theorem paperSection8_hSlice_of_powerGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1) := by
  filter_upwards [hpow.H_upper_pointwise] with x hx p m hm
  have hC : 0 < hpow.C := hpow.hC
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  -- `m ^ (hpow.β - hpow.β / hpow.α) ≥ 0` since `m > 0` and `Real.rpow_nonneg`.
  have hmrpow_nn : 0 ≤ m ^ (hpow.β - hpow.β / hpow.α) :=
    Real.rpow_nonneg hm.le _
  -- The cross-term slack is non-negative: `C·‖p‖·(m^{β-β/α} + 1) ≥ 0`.
  have hSlack_nn :
      0 ≤ hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1) := by
    have h1 : 0 ≤ hpow.C * ‖p‖ := mul_nonneg hC.le hp_nn
    have h2 : 0 ≤ m ^ (hpow.β - hpow.β / hpow.α) + 1 := by linarith
    exact mul_nonneg h1 h2
  -- The base bound `H ≤ C(‖p‖^α + 1) - m^β/C` rewrites algebraically to
  -- `H ≤ -m^β/C + C + C·‖p‖^α`. Add the non-negative slack.
  have hb : H x p m ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (m ^ hpow.β) / hpow.C :=
    hx p m hm
  have hrw :
      hpow.C * (‖p‖ ^ hpow.α + 1) - (m ^ hpow.β) / hpow.C
        = -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α := by
    ring
  rw [hrw] at hb
  linarith

/-- **Closed scalar-monotonicity producer.** The `hScalarMono` field of
`PaperSection8ClosedMeasFields` is a `simpa [signedRpow]` wrapper around
`Solutions.MFG.rpow_signed_mono_scalar`. -/
theorem paperSection8_hScalarMono_of_gamma
    {γBarReal : ℝ} (hγ : 1 < γBarReal) :
    ∀ s t : ℝ,
      0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
            * (t - s) := by
  intro s t
  have h := Solutions.MFG.rpow_signed_mono_scalar (γBar := γBarReal) hγ s t
  simpa [Solutions.MFG.signedRpow] using h

/-- **Closed vector-monotonicity producer.** The `hVecMono` field of
`PaperSection8ClosedMeasFields` is a wrapper around
`Solutions.MFG.rpow_signed_mono_vec` via the pointwise identity
`vecSignedRpow γBar v = vecAbsPowMinusTwo γBar v • v`
(`funext i; rfl`). -/
theorem paperSection8_hVecMono_of_gamma
    {d : ℕ} {γBarReal : ℝ} (hγ : 1 < γBarReal) :
    ∀ v w : Fin d → ℝ,
      0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
            ⬝ (v - w) := by
  intro v w
  have h := Solutions.MFG.rpow_signed_mono_vec (d := d) (γBar := γBarReal) hγ v w
  have hv : Solutions.MFG.vecSignedRpow γBarReal v
              = vecAbsPowMinusTwo γBarReal v • v := by
    funext i; rfl
  have hw : Solutions.MFG.vecSignedRpow γBarReal w
              = vecAbsPowMinusTwo γBarReal w • w := by
    funext i; rfl
  rw [hv, hw] at h
  exact h

/-! ### Universal-`q` measurability helpers (Step 3 of
`paperSolFor-analytic-measurability`)

The three `xbanach_*_aemeasurable` helpers below are private — they
just expose the `Lp.aestronglyMeasurable` / `aemeasurable` chain
behind the `XBanach` projections `mOf`, `uOf`, `DuOf`. They feed the
two `paperSection8_hF_*_meas_of_powerGrowth` field producers, which
compose `hpow.measurable_H` / `hpow.measurable_DpH` with the AE-
measurable `(x, p, m)` triple. -/

private lemma xbanach_m_aemeasurable
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (q : XBanach d βBarReal γBarReal) :
    AEMeasurable (mOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  (MeasureTheory.Lp.aestronglyMeasurable q.1).aemeasurable

private lemma xbanach_u_aemeasurable
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (q : XBanach d βBarReal γBarReal) :
    AEMeasurable (uOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  (MeasureTheory.Lp.aestronglyMeasurable q.2.1).aemeasurable

private lemma xbanach_Du_pi_aemeasurable
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (q : XBanach d βBarReal γBarReal) :
    AEMeasurable
      (fun x : Fin d → ℝ => fun i : Fin d => DuOf q i x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  refine aemeasurable_pi_iff.mpr ?_
  intro i
  exact (MeasureTheory.Lp.aestronglyMeasurable (q.2.2 i)).aemeasurable

/-- **HJB-flux measurability producer.** Universal-`q` AE-strong
measurability of `x ↦ -u(x) - H(x, Du(x), m(x)) + V(x)`, derived from
`HypothesisPowerGrowth.measurable_H` plus the AE-measurable `XBanach`
projections. -/
theorem paperSection8_hF_HJB_meas_of_powerGrowth
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V) :
    ∀ q : XBanach d βBarReal γBarReal,
      MeasureTheory.AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro q
  have hu : AEMeasurable (uOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    xbanach_u_aemeasurable q
  have hm : AEMeasurable (mOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    xbanach_m_aemeasurable q
  have hDu : AEMeasurable
      (fun x : Fin d → ℝ => fun i : Fin d => DuOf q i x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    xbanach_Du_pi_aemeasurable q
  have hVmeas : AEMeasurable V
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hV.aestronglyMeasurable.aemeasurable
  have hxpm : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i : Fin d => DuOf q i x), mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.aemeasurable.prodMk (hDu.prodMk hm)
  have hH : AEMeasurable
      (fun x : Fin d → ℝ => H x (fun i => DuOf q i x) (mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hpow.measurable_H.comp_aemeasurable hxpm
  exact ((hu.neg.sub hH).add hVmeas).aestronglyMeasurable

/-- **Flux-measurability producer.** Universal-`q` AE-strong
measurability of `x ↦ m(x) * D_pH(x, Du(x), m(x)) i`, derived from
`HypothesisPowerGrowth.measurable_DpH` plus the AE-measurable
`XBanach` projections. -/
theorem paperSection8_hF_flux_meas_of_powerGrowth
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      MeasureTheory.AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro q i
  have hm : AEMeasurable (mOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    xbanach_m_aemeasurable q
  have hDu : AEMeasurable
      (fun x : Fin d → ℝ => fun j : Fin d => DuOf q j x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    xbanach_Du_pi_aemeasurable q
  have hxpm : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun j : Fin d => DuOf q j x), mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.aemeasurable.prodMk (hDu.prodMk hm)
  have hDpH : AEMeasurable
      (fun x : Fin d → ℝ => DpH x (fun j => DuOf q j x) (mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hpow.measurable_DpH.comp_aemeasurable hxpm
  exact (hm.mul (hDpH.eval i)).aestronglyMeasurable

/-! ### `cxComb`-side measurability producers
(`paperSolFor-analytic-cxComb-meas`)

The two wrapper producers `paperSection8_hF_unreg_meas_of_powerGrowth`
and `paperSection8_hF_gat_meas_of_powerGrowth` discharge the
`hF_unreg_meas` and `hF_gat_meas` fields of
`PaperSection8ClosedMeasFields` (and matching fields of
`PaperSection8AnalyticResidues`) from `(hpow, hV)` alone, at the
universal-`(u, v, w, t)` level. They wrap four generic lemmas:

* `private_aemeasurable_cxComb_at`
* `private_aemeasurable_cxCombGrad_pi`
* `private_aestronglyMeasurable_aepsiIntegrandAt_unreg`
* `private_aestronglyMeasurable_aepsiIntegrandAt_gateaux`

which are local duplicates (per the split decision in the task spec)
of the generic measurability lemmas living in
`BanachBridge.lean`. Duplicating them here avoids the upward import
cycle that would arise if we relocated them, since `BanachBridge.lean`
already imports `AssemblyContext.lean` transitively. -/

-- Adapted from BanachBridge.aemeasurable_cxComb_at.
private lemma private_aemeasurable_cxComb_at
    {d : ℕ}
    {a ā : (Fin d → ℝ) → ℝ} (t : ℝ)
    (ha : MeasureTheory.AEStronglyMeasurable a
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hā : MeasureTheory.AEStronglyMeasurable ā
            (MeasureTheory.volume.restrict (UnitCube d))) :
    AEMeasurable (fun x => cxComb a ā t x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  unfold cxComb
  exact ((aemeasurable_const (b := (1 - t : ℝ))).mul
            hā.aemeasurable).add
        ((aemeasurable_const (b := t)).mul ha.aemeasurable)

-- Adapted from BanachBridge.aemeasurable_cxCombGrad_pi.
private lemma private_aemeasurable_cxCombGrad_pi
    {d : ℕ}
    {Da Dā : Fin d → (Fin d → ℝ) → ℝ} (t : ℝ)
    (hDa : ∀ i, MeasureTheory.AEStronglyMeasurable (Da i)
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hDā : ∀ i, MeasureTheory.AEStronglyMeasurable (Dā i)
                  (MeasureTheory.volume.restrict (UnitCube d))) :
    AEMeasurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => cxCombGrad Da Dā t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  refine aemeasurable_pi_iff.mpr ?_
  intro i
  unfold cxCombGrad
  exact ((aemeasurable_const (b := (1 - t : ℝ))).mul
            (hDā i).aemeasurable).add
        ((aemeasurable_const (b := t)).mul (hDa i).aemeasurable)

-- Adapted from BanachBridge.aestronglyMeasurable_aepsiIntegrandAt_unreg.
private lemma private_aestronglyMeasurable_aepsiIntegrandAt_unreg
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (hμ : MeasureTheory.AEStronglyMeasurable μ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hmBar : MeasureTheory.AEStronglyMeasurable mBar
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hυ : MeasureTheory.AEStronglyMeasurable υ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hῡ : MeasureTheory.AEStronglyMeasurable ῡ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dυ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dῡ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
            (MeasureTheory.volume.restrict (UnitCube d)))
    (t : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  unfold aepsiIntegrandAt_unreg
  have hμt : AEMeasurable
      (fun x => cxComb μ mBar t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    private_aemeasurable_cxComb_at (d := d) t hμ hmBar
  have hυt : AEMeasurable
      (fun x => cxComb υ ῡ t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    private_aemeasurable_cxComb_at (d := d) t hυ hῡ
  have hpt : AEMeasurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    private_aemeasurable_cxCombGrad_pi (d := d) t hDυ hDῡ
  have htriple : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => cxCombGrad Dυ Dῡ t i x), cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.aemeasurable.prodMk (hpt.prodMk hμt)
  have hH : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hReg.measurable_H.comp_aemeasurable htriple
  have hDpH : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hReg.measurable_DpH.comp_aemeasurable htriple
  have hDpH_dot_Dν : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
          ⬝ (fun i : Fin d => Dν i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    unfold dotProduct
    refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
    exact (hDpH.eval i).mul (hDν i).aemeasurable
  have hpart1 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (-cxComb υ ῡ t x
          - H x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
          + V x) * η x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ((hυt.neg.sub hH).add hV.aemeasurable).mul hη.aemeasurable
  have hpart2 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        cxComb μ mBar t x *
          (DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                 (cxComb μ mBar t x)
            ⬝ (fun i : Fin d => Dν i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hμt.mul hDpH_dot_Dν
  have hpart3 : AEMeasurable
      (fun x : (Fin d → ℝ) => (cxComb μ mBar t x - 1) * ν x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (hμt.sub (aemeasurable_const (b := (1:ℝ)))).mul hν.aemeasurable
  exact ((hpart1.add hpart2).add hpart3).aestronglyMeasurable

-- Adapted from BanachBridge.aestronglyMeasurable_aepsiIntegrandAt_gateaux.
private lemma private_aestronglyMeasurable_aepsiIntegrandAt_gateaux
    {d : ℕ}
    (γBar : ℝ)
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    (hυ : MeasureTheory.AEStronglyMeasurable υ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hῡ : MeasureTheory.AEStronglyMeasurable ῡ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dυ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dῡ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
            (MeasureTheory.volume.restrict (UnitCube d)))
    (t : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  unfold aepsiIntegrandAt_gateaux
  have hυt : AEMeasurable
      (fun x => cxComb υ ῡ t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    private_aemeasurable_cxComb_at (d := d) t hυ hῡ
  have hpt : AEMeasurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    private_aemeasurable_cxCombGrad_pi (d := d) t hDυ hDῡ
  have hpt_dot_pt : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
          ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    unfold dotProduct
    refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
    exact (hpt.eval i).mul (hpt.eval i)
  have hpt_dot_pt_nn : ∀ x,
      0 ≤ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
              ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) := by
    intro x
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hvec : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have h_ennreal_meas : Measurable
        (fun s : ℝ => ((ENNReal.ofReal s) ^ ((γBar - 2) / 2)).toReal) := by
      refine ENNReal.measurable_toReal.comp ?_
      exact (ENNReal.continuous_rpow_const).measurable.comp
              ENNReal.measurable_ofReal
    have h_ae_eq :
        (fun x : (Fin d → ℝ) =>
          vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
        =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (UnitCube d))]
        (fun x : (Fin d → ℝ) =>
          ((ENNReal.ofReal
              ((fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)))
            ^ ((γBar - 2) / 2)).toReal) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      show vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
            = ((ENNReal.ofReal
                ((fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                  ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)))
              ^ ((γBar - 2) / 2)).toReal
      unfold vecAbsPowMinusTwo
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (hpt_dot_pt_nn x)]
    refine AEMeasurable.congr ?_ h_ae_eq.symm
    exact h_ennreal_meas.comp_aemeasurable hpt_dot_pt
  have hpt_dot_Dν : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
          ⬝ (fun i : Fin d => Dν i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    unfold dotProduct
    refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
    exact (hpt.eval i).mul (hDν i).aemeasurable
  have habsυt_nn : ∀ x, (0 : ℝ) ≤ |cxComb υ ῡ t x| := fun x => abs_nonneg _
  have habsυt : AEMeasurable (fun x => |cxComb υ ῡ t x|)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    continuous_abs.measurable.comp_aemeasurable hυt
  have habsυ : AEMeasurable
      (fun x : (Fin d → ℝ) => absPowMinusTwo γBar (cxComb υ ῡ t x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have h_ennreal_meas : Measurable
        (fun s : ℝ => ((ENNReal.ofReal s) ^ (γBar - 2)).toReal) := by
      refine ENNReal.measurable_toReal.comp ?_
      exact (ENNReal.continuous_rpow_const).measurable.comp
              ENNReal.measurable_ofReal
    have h_ae_eq :
        (fun x : (Fin d → ℝ) => absPowMinusTwo γBar (cxComb υ ῡ t x))
        =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (UnitCube d))]
        (fun x : (Fin d → ℝ) =>
          ((ENNReal.ofReal |cxComb υ ῡ t x|) ^ (γBar - 2)).toReal) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      show absPowMinusTwo γBar (cxComb υ ῡ t x)
            = ((ENNReal.ofReal |cxComb υ ῡ t x|) ^ (γBar - 2)).toReal
      unfold absPowMinusTwo
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (habsυt_nn x)]
    refine AEMeasurable.congr ?_ h_ae_eq.symm
    exact h_ennreal_meas.comp_aemeasurable habsυt
  have hpart1 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
          * ((fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                ⬝ (fun i : Fin d => Dν i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hvec.mul hpt_dot_Dν
  have hpart2 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        absPowMinusTwo γBar (cxComb υ ῡ t x)
          * (cxComb υ ῡ t x * ν x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    habsυ.mul (hυt.mul hν.aemeasurable)
  exact (hpart1.add hpart2).aestronglyMeasurable

/-- **Unregularised cxComb-segment-integrand measurability producer.**
Universal-`(u, v, w, t)` AE-strong measurability of the unregularised
integrand at convex-combination endpoints `(DuOf v, DuOf u, mOf v,
mOf u, uOf v, uOf u)` paired with test direction `(w.2.2, w.1, w.2.1)`. -/
theorem paperSection8_hF_unreg_meas_of_powerGrowth
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V) :
    ∀ (u v : XBanach d βBarReal γBarReal),
        u ∈ K_Aepsi d βBarReal γBarReal →
        v ∈ K_Aepsi d βBarReal γBarReal →
        ∀ (w : XBanach d βBarReal γBarReal),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf v) (DuOf u) (mOf v) (mOf u)
                    (uOf v) (uOf u)
                    (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro u v _hu _hv w t _ht
  -- AEStronglyMeasurable witnesses for the bare projections.
  have hμ : MeasureTheory.AEStronglyMeasurable (mOf v)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable v.1
  have hmBar : MeasureTheory.AEStronglyMeasurable (mOf u)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable u.1
  have hυ : MeasureTheory.AEStronglyMeasurable (uOf v)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable v.2.1
  have hῡ : MeasureTheory.AEStronglyMeasurable (uOf u)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable u.2.1
  have hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf v i)
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    MeasureTheory.Lp.aestronglyMeasurable (v.2.2 i)
  have hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf u i)
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    MeasureTheory.Lp.aestronglyMeasurable (u.2.2 i)
  have hDν : ∀ i, MeasureTheory.AEStronglyMeasurable
      (fun x => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x)
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    MeasureTheory.Lp.aestronglyMeasurable (w.2.2 i)
  have hη : MeasureTheory.AEStronglyMeasurable
      ((⇑w.1 : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable w.1
  have hν : MeasureTheory.AEStronglyMeasurable
      ((⇑w.2.1 : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable w.2.1
  have hVmeas : MeasureTheory.AEStronglyMeasurable V
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hV.aestronglyMeasurable
  exact private_aestronglyMeasurable_aepsiIntegrandAt_unreg
    (d := d) hpow.toRegularityH
    hμ hmBar hυ hῡ hDυ hDῡ hDν hη hν hVmeas t

/-- **Gateaux cxComb-segment-integrand measurability producer.**
Universal-`(u, v, w, t)` AE-strong measurability of the Gateaux
integrand at convex-combination endpoints `(DuOf v, DuOf u, uOf v,
uOf u)` paired with test direction `(w.2.2, w.2.1)`. -/
theorem paperSection8_hF_gat_meas_of_powerGrowth
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    ∀ (u v : XBanach d βBarReal γBarReal),
        u ∈ K_Aepsi d βBarReal γBarReal →
        v ∈ K_Aepsi d βBarReal γBarReal →
        ∀ (w : XBanach d βBarReal γBarReal),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBarReal
                    (DuOf v) (DuOf u) (uOf v) (uOf u)
                    (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro u v _hu _hv w t _ht
  have hυ : MeasureTheory.AEStronglyMeasurable (uOf v)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable v.2.1
  have hῡ : MeasureTheory.AEStronglyMeasurable (uOf u)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable u.2.1
  have hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf v i)
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    MeasureTheory.Lp.aestronglyMeasurable (v.2.2 i)
  have hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf u i)
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    MeasureTheory.Lp.aestronglyMeasurable (u.2.2 i)
  have hDν : ∀ i, MeasureTheory.AEStronglyMeasurable
      (fun x => (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x)
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    MeasureTheory.Lp.aestronglyMeasurable (w.2.2 i)
  have hν : MeasureTheory.AEStronglyMeasurable
      ((⇑w.2.1 : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable w.2.1
  exact private_aestronglyMeasurable_aepsiIntegrandAt_gateaux
    (d := d) γBarReal hυ hῡ hDυ hDῡ hDν hν t

/-! ### Partial-bundle producers (Step 4 of
`paperSolFor-analytic-measurability`) -/

/-- **Partial-bundle producer.** Assembles a
`PaperSection8ClosedMeasFields` from `(hpow, hV, hγ : 1 < γBarReal)`,
exactly the inputs already in scope at the paper-exponent call site
(no new authorisation parameters). -/
noncomputable def PaperSection8ClosedMeasFields.of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hγ : 1 < γBarReal) :
    PaperSection8ClosedMeasFields
      (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH hpow where
  h_upper := paperSection8_h_upper_of_powerGrowth hpow
  hF_HJB_meas :=
    paperSection8_hF_HJB_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') hpow hV
  hF_flux_meas :=
    paperSection8_hF_flux_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) hpow
  hScalarMono := paperSection8_hScalarMono_of_gamma hγ
  hVecMono := paperSection8_hVecMono_of_gamma (d := d) hγ
  hF_unreg_meas :=
    paperSection8_hF_unreg_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') hpow hV
  hF_gat_meas :=
    paperSection8_hF_gat_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')

/-- **Paper-exponent specialisation.** Fixes the four type-level
exponents to their paper values and uses
`Hamiltonian.one_lt_gammaBar` to discharge `1 < γBarReal`. -/
noncomputable def PaperSection8ClosedMeasFields.of_paperHypotheses_paper
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1 : ℝ))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β : ℝ))]
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V) :
    PaperSection8ClosedMeasFields
      (d := d)
      (hpow.α * (hpow.β + 1) / hpow.β)
      (hpow.β + 1)
      ((hpow.β + 1) / hpow.β)
      ((hpow.α * (hpow.β + 1) / hpow.β)
        / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      V H DpH hpow :=
  PaperSection8ClosedMeasFields.of_paperHypotheses (V := V) hpow hV
    (Hamiltonian.one_lt_gammaBar hpow.α hpow.β hpow.hα hpow.hβ)

end Banach
end SimplePower
end Theorems
end StationaryMFG
end
