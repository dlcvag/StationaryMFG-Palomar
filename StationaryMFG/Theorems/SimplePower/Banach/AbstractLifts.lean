module

public import StationaryMFG.Theorems.SimplePower.Banach.Operator
public import StationaryMFG.Theorems.SimplePower.Banach.WeakLimit
public import StationaryMFG.Theorems.SimplePower.Regularized
public import StationaryMFG.Theorems.SimplePower.Hemicontinuity
public import StationaryMFG.Theorems.SimplePower.Coercivity
public import StationaryMFG.Monotone.Operator
public import StationaryMFG.Monotone.Hemicontinuous
public import StationaryMFG.Monotone.Coercive
public import StationaryMFG.Monotone.FiniteConvexHullWeakVI

@[expose] public section

/-!
# Banach-level monotonicity wrap of `mfgOperatorEps_CLM`

This module discharges Phase-4 task `infra-P4-banach-B1b-clm-monotone-wrap`:
**lifting** the bare-function integrated monotonicity of `A_ε`
(`StationaryMFG.Theorems.SimplePower.aepsi_isMonotone_integrated`) to the
abstract `IsMonotone` predicate of `Monotone/Operator.lean` against the
CLM `mfgOperatorEps_CLM` of `Banach/Operator.lean`.

The CLM has Banach domain
```
X := LpPer (ENNReal.ofReal βBarReal) d × SobolevPerLp 1 (ENNReal.ofReal γBarReal) d.
```

## Operator family `Aepsi_CLM_op`

`Aepsi_CLM_op` is a function `X → (X →L[ℝ] ℝ)` whose value at a point `v`
is the CLM `mfgOperatorEps_CLM` constructed with primal data
`(Du, m, u) = (fun i => ⇑(v.2.2 i), ⇑v.1, ⇑v.2.1)`. The auxiliary
`MFGOpEpsAuxHyps` certificate is supplied by the caller as a per-primal
function `auxHyps`; this matches the per-CLM packaging in
`Banach/Operator.lean`.

## Domain `K_Aepsi`

Per the task's interpretation of "image of `MFGDomain` under `toLp`",
`K_Aepsi` records the *strict* positivity of the `m`-component of `v`
(consistent with `InMFGOperatorDomain`'s admissibility). The
bare-function integrated monotonicity `aepsi_isMonotone_integrated`
genuinely requires strict positivity (`paper:hpos₁`/`paper:hpos₂`),
which is strictly stronger than `MFGDomain`'s `0 ≤ᵐ m`. We document the
discrepancy here: downstream Phase-4 consumers feed strict positivity
into the wrap, so the lift on the strict-positivity cone is what the
Browder–Minty machinery actually consumes.

## Integrability discharge

`aepsi_isMonotone_integrated` carries four `IntegrableOn` side
conditions on the linear-difference test integrands. These are
genuine integrability obligations on `(Du₁, m₁, u₁), (Du₂, m₂, u₂)`
that the CLM-level statement cannot avoid; we expose them as a
universally-quantified hypothesis `hInteg` of the wrap theorem
`isMonotone_Aepsi_CLM`. Discharging `hInteg` from `MFGOpEpsAuxHyps`
alone is the routine bookkeeping done by the integrability flow in
`Banach/Operator.lean`; we keep the wrap-level statement parametric in
`hInteg` to avoid duplicating that infrastructure here.

## Main contents

* `Aepsi_CLM_op` — the operator family `X → (X →L[ℝ] ℝ)`.
* `K_Aepsi` — the strict-positivity cone.
* `isMonotone_Aepsi_CLM` — `IsMonotone K_Aepsi (Aepsi_CLM_op …)`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Monotone
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open scoped ENNReal

variable {d : ℕ}
variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- Local abbreviation for the Banach domain of `mfgOperatorEps_CLM`. -/
abbrev palomar_AbstractLifts_XBanach (d : ℕ) (βBarReal γBarReal : ℝ) : Type :=
  Periodic.LpPer (ENNReal.ofReal βBarReal) d
    × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d

variable [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-! ## `FiniteConvexHullWeakVI` instance for `palomar_AbstractLifts_XBanach`

The unconditional instance `instFiniteConvexHullWeakVI` from
`StationaryMFG/Monotone/FiniteConvexHullWeakVI.lean` discharges
`FiniteConvexHullWeakVI X` for *every* normed real space. Since
`palomar_AbstractLifts_XBanach d βBarReal γBarReal` is a product of Mathlib `Lp` spaces
(through the `abbrev`s `LpPer`, `SobolevPerLp`), it inherits
`NormedAddCommGroup` and `NormedSpace ℝ` from Mathlib under the
standing `Fact (1 ≤ p)` hypotheses, so `inferInstance` succeeds
immediately. We pin the synthesis result down here as a sanity-check
example so that downstream T4 invocations of `monotone_abstract_weak`
on this domain do not need to wait for typeclass search to traverse
the full `abbrev`/product chain. -/

/-- **Sanity-check `example`.** The unconditional Sion-discharge
instance applies to the concrete Banach pair `palomar_AbstractLifts_XBanach`. -/
example : FiniteConvexHullWeakVI (palomar_AbstractLifts_XBanach d βBarReal γBarReal) :=
  inferInstance

/-! ## Operator family `Aepsi_CLM_op` -/

/-- **CLM-form regularised MFG operator family.**

Given a per-primal `auxHyps` supplier, `Aepsi_CLM_op auxHyps ε` is the
function `X → (X →L[ℝ] ℝ)` whose value at `v` is the CLM
`mfgOperatorEps_CLM` built with primal data extracted from `v` via
`Lp.coeFn`.

The per-primal `auxHyps` packages `MFGOpEpsAuxHyps` certificates for
every triple `(Du, m, u)`; this matches the per-CLM packaging in
`Banach/Operator.lean`. -/
noncomputable def Aepsi_CLM_op
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    (ε : ℝ) (v : palomar_AbstractLifts_XBanach d βBarReal γBarReal) :
    palomar_AbstractLifts_XBanach d βBarReal γBarReal →L[ℝ] ℝ :=
  mfgOperatorEps_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (V := V) (H := H) (DpH := DpH)
    (Du := fun i => ⇑(v.2.2 i)) (m := ⇑v.1) (u := ⇑v.2.1)
    (auxHyps (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)) ε

/-- Unfolding identity for `Aepsi_CLM_op`: applying the CLM at primal `v`
to a test point `q` yields the bare-function pairing on the Lp
coercions. -/
theorem Aepsi_CLM_op_apply
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    (ε : ℝ) (v q : palomar_AbstractLifts_XBanach d βBarReal γBarReal) :
    Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHyps ε v q
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) := by
  unfold Aepsi_CLM_op
  exact mfgOperatorEps_CLM_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (V := V) (H := H) (DpH := DpH)
    (Du := fun i => ⇑(v.2.2 i)) (m := ⇑v.1) (u := ⇑v.2.1)
    (auxHyps (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)) ε q

/-! ## Domain `K_Aepsi` -/

/-- **The strict-positivity cone** in the Banach domain.

Per the task's interpretation of "image of `MFGDomain` under `toLp`",
this records strict positivity of the `m`-component (consistent with
`InMFGOperatorDomain`'s admissibility, and the strict-positivity
hypothesis carried by `aepsi_isMonotone_integrated`). -/
def K_Aepsi (d : ℕ) (βBarReal γBarReal : ℝ) :
    Set (palomar_AbstractLifts_XBanach d βBarReal γBarReal) :=
  { v | ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x }

/-! ## Closed nonneg cone `K0_Aepsi`

Per the expert-rebuild plan T1: the strict-positivity cone `K_Aepsi`
is **not weakly closed** — strict positivity does not pass to weak
limits. The Browder–Minty / Mazur machinery only yields
`closure K ⊆ K` for *closed* cones. The fix is to use the closed
nonneg cone `K0_Aepsi := { v | 0 ≤ ⇑v.1 a.e. }` as the abstract-VI
domain, and encode strict positivity inside the operator (or as a
per-pair side hypothesis) rather than the domain.

The convexity and norm-closedness lemmas reduce to
`nonNegConeLpPer_convex` and `nonNegConeLpPer_isClosed` from
`Banach/WeakLimit.lean`, applied through the first projection of
the product `palomar_AbstractLifts_XBanach = LpPer × SobolevPerLp`.
-/

/-- **The closed nonneg cone** in the Banach domain.

`K0_Aepsi d βBarReal γBarReal := { v | 0 ≤ ⇑v.1 a.e. on the unit cube }`.

This is the canonical Browder–Minty / Mazur domain: it is convex and
norm-closed (and hence weakly sequentially closed in the appropriate
sense). Strict positivity, when needed by the operator, is supplied
as a per-pair side hypothesis — not folded into the domain. -/
def K0_Aepsi (d : ℕ) (βBarReal γBarReal : ℝ) :
    Set (palomar_AbstractLifts_XBanach d βBarReal γBarReal) :=
  { v | ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 ≤ (⇑v.1 : (Fin d → ℝ) → ℝ) x }

/-- Membership unfolding for `K0_Aepsi`. -/
lemma mem_K0_Aepsi_iff {d : ℕ} {βBarReal γBarReal : ℝ}
    {v : palomar_AbstractLifts_XBanach d βBarReal γBarReal} :
    v ∈ K0_Aepsi d βBarReal γBarReal ↔
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ (⇑v.1 : (Fin d → ℝ) → ℝ) x :=
  Iff.rfl

/-- The strict-positivity cone is contained in the nonneg cone:
`K_Aepsi ⊆ K0_Aepsi`. -/
lemma K_Aepsi_subset_K0_Aepsi (d : ℕ) (βBarReal γBarReal : ℝ) :
    K_Aepsi d βBarReal γBarReal ⊆ K0_Aepsi d βBarReal γBarReal := by
  intro v hv
  have hv' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x := hv
  exact hv'.mono (fun _ hx => hx.le)

/-- **Convexity of `K0_Aepsi`.**

Reduces to `nonNegConeLpPer_convex` applied through `Prod.fst`. -/
theorem K0_Aepsi_convex (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    Convex ℝ (K0_Aepsi d βBarReal γBarReal) := by
  intro v₁ hv₁ v₂ hv₂ a b ha hb _hab
  -- Goal: `a • v₁ + b • v₂ ∈ K0_Aepsi`, i.e. `0 ≤ ⇑((a • v₁ + b • v₂).1) x` a.e.
  change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ (⇑(a • v₁ + b • v₂).1 : (Fin d → ℝ) → ℝ) x
  -- `(a • v₁ + b • v₂).1 = a • v₁.1 + b • v₂.1` definitionally.
  have hsum : ((a • v₁ + b • v₂).1 :
                  Periodic.LpPer (ENNReal.ofReal βBarReal) d)
                = a • v₁.1 + b • v₂.1 := rfl
  rw [hsum]
  -- Now apply convexity of `nonNegConeLpPer` on the first factor.
  have h_conv : Convex ℝ (nonNegConeLpPer (ENNReal.ofReal βBarReal) d) :=
    nonNegConeLpPer_convex
  have hv₁' : v₁.1 ∈ nonNegConeLpPer (ENNReal.ofReal βBarReal) d := hv₁
  have hv₂' : v₂.1 ∈ nonNegConeLpPer (ENNReal.ofReal βBarReal) d := hv₂
  exact h_conv hv₁' hv₂' ha hb _hab

/-- **Norm-closedness of `K0_Aepsi`.**

Reduces to `nonNegConeLpPer_isClosed` applied through the continuous
projection `Prod.fst : palomar_AbstractLifts_XBanach → LpPer`. -/
theorem K0_Aepsi_closed (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    IsClosed (K0_Aepsi d βBarReal γBarReal) := by
  -- `K0_Aepsi = (Prod.fst)⁻¹' (nonNegConeLpPer βBar d)` definitionally.
  have h_eq :
      K0_Aepsi d βBarReal γBarReal
        = (Prod.fst : palomar_AbstractLifts_XBanach d βBarReal γBarReal →
              Periodic.LpPer (ENNReal.ofReal βBarReal) d)
            ⁻¹' (nonNegConeLpPer (ENNReal.ofReal βBarReal) d) := rfl
  rw [h_eq]
  exact (nonNegConeLpPer_isClosed (βBar := ENNReal.ofReal βBarReal)
            (d := d)).preimage continuous_fst

/-- **Closure of `K0_Aepsi` is contained in `K0_Aepsi`** — direct from
norm-closedness via `IsClosed.closure_subset_iff`. -/
theorem K0_Aepsi_closure_subset (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    closure (K0_Aepsi d βBarReal γBarReal) ⊆ K0_Aepsi d βBarReal γBarReal :=
  (K0_Aepsi_closed d βBarReal γBarReal).closure_subset

/-- Sanity-check `example`: `K0_Aepsi_closure_subset` type-checks on
trivial data. -/
example (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (q : palomar_AbstractLifts_XBanach d βBarReal γBarReal)
    (hq : q ∈ closure (K0_Aepsi d βBarReal γBarReal)) :
    q ∈ K0_Aepsi d βBarReal γBarReal :=
  K0_Aepsi_closure_subset d βBarReal γBarReal hq

/-! ## Convexity of `K_Aepsi`

The strict-positivity cone is convex: if `0 < ⇑v₁.1` and `0 < ⇑v₂.1`
a.e., and `a, b ≥ 0` with `a + b = 1`, then
`0 < (a • v₁ + b • v₂).1` a.e. (at least one of `a, b` is strictly
positive, both summands are non-negative). This was previously
proved (locally) inside `Banach/Closure.lean`; we promote it here so
that the K_Aepsi-form Browder–Minty producer in
`Banach/AssemblyContext.lean` can use it without an upward import. -/

/-- **Convexity of `K_Aepsi`.** -/
lemma K_Aepsi_convex (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    Convex ℝ (K_Aepsi d βBarReal γBarReal) := by
  rw [convex_iff_add_mem]
  intro v₁ hv₁ v₂ hv₂ a b ha hb hab
  have hsum : ((a • v₁ + b • v₂).1 : Periodic.LpPer (ENNReal.ofReal βBarReal) d)
                = a • v₁.1 + b • v₂.1 := rfl
  have h_add := MeasureTheory.Lp.coeFn_add (a • v₁.1) (b • v₂.1)
  have h_smul1 := MeasureTheory.Lp.coeFn_smul a v₁.1
  have h_smul2 := MeasureTheory.Lp.coeFn_smul b v₂.1
  have hv₁_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  0 < (⇑v₁.1 : (Fin d → ℝ) → ℝ) x := hv₁
  have hv₂_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  0 < (⇑v₂.1 : (Fin d → ℝ) → ℝ) x := hv₂
  change ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 < (⇑((a • v₁ + b • v₂).1 : Periodic.LpPer _ d) : (Fin d → ℝ) → ℝ) x
  rw [hsum]
  filter_upwards [h_add, h_smul1, h_smul2, hv₁_ae, hv₂_ae]
    with x hx_add hx_s1 hx_s2 hpos1 hpos2
  rw [hx_add]
  rw [Pi.add_apply, hx_s1, hx_s2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases (lt_or_eq_of_le ha) with ha_pos | ha_zero
  · have h1 : 0 < a * (⇑v₁.1 : (Fin d → ℝ) → ℝ) x := mul_pos ha_pos hpos1
    have h2 : 0 ≤ b * (⇑v₂.1 : (Fin d → ℝ) → ℝ) x :=
      mul_nonneg hb hpos2.le
    linarith
  · have hb_pos : 0 < b := by
      rw [← ha_zero] at hab
      linarith
    have h2 : 0 < b * (⇑v₂.1 : (Fin d → ℝ) → ℝ) x := mul_pos hb_pos hpos2
    have h1 : 0 ≤ a * (⇑v₁.1 : (Fin d → ℝ) → ℝ) x :=
      mul_nonneg ha hpos1.le
    linarith

/-! ## Two-domain bridge: `closure K_Aepsi ⊆ K0_Aepsi`

The two-domain redesign (per the v3 expert plan post-T6 audit) keeps
the strict-positivity cone `K_Aepsi` *internal* to the abstract VI
machinery (Browder–Minty's monotonicity / coercivity / hemicontinuity
arguments genuinely require strict positivity for the
`aepsi_isMonotone_integrated` family), while the closed nonneg cone
`K0_Aepsi` is the **public** target of the closure-of-the-witness
step.

The structural bridge is the closure inclusion below: since
`K_Aepsi ⊆ K0_Aepsi` (`K_Aepsi_subset_K0_Aepsi`) and `K0_Aepsi` is
norm-closed (`K0_Aepsi_closed`), the closure of `K_Aepsi` lies inside
`K0_Aepsi`. This is the single foundational lemma that lets the
Browder–Minty witness `q ∈ closure K_Aepsi` produced by the abstract
machinery descend to `q ∈ K0_Aepsi` for the public-API conclusion.
-/

/-- **Closure inclusion `closure K_Aepsi ⊆ K0_Aepsi`.**

Foundational two-domain bridge: combine `K_Aepsi ⊆ K0_Aepsi` with
norm-closedness of `K0_Aepsi`. -/
theorem K_Aepsi_closure_subset_K0_Aepsi (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    closure (K_Aepsi d βBarReal γBarReal) ⊆ K0_Aepsi d βBarReal γBarReal := by
  -- `closure K_Aepsi ⊆ closure K0_Aepsi` from `K_Aepsi ⊆ K0_Aepsi`
  -- (closure is monotone), then `closure K0_Aepsi ⊆ K0_Aepsi` from
  -- `K0_Aepsi_closure_subset` (closedness).
  intro q hq
  have h_mono : closure (K_Aepsi d βBarReal γBarReal)
                  ⊆ closure (K0_Aepsi d βBarReal γBarReal) :=
    closure_mono (K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal)
  exact K0_Aepsi_closure_subset d βBarReal γBarReal (h_mono hq)

/-- Sanity-check `example`: `K_Aepsi_closure_subset_K0_Aepsi` type-checks
and delivers a `K0_Aepsi`-membership conclusion from a
`closure K_Aepsi`-membership hypothesis. This is the public-target
shape used by the K_Aepsi-form Browder–Minty producer in
`AssemblyContext.lean`. -/
example (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (q : palomar_AbstractLifts_XBanach d βBarReal γBarReal)
    (hq : q ∈ closure (K_Aepsi d βBarReal γBarReal)) :
    q ∈ K0_Aepsi d βBarReal γBarReal :=
  K_Aepsi_closure_subset_K0_Aepsi d βBarReal γBarReal hq

/-! ## Congruence of `mfgOperatorEpsPair` under a.e.-equal test triples

We reduce the Lp-test-triple form of `mfgOperatorEpsPair` to its
pointwise-difference form (where the test triple is a literal pointwise
difference of primal coercions), via `setIntegral_congr_ae`. -/

/-- **a.e.-congruence** of `mfgOperatorEpsPair` in the test triple. If two
test triples agree a.e. on the unit cube, the bare-function pairings
agree exactly. -/
lemma mfgOperatorEpsPair_test_congr_ae
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    {Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ}
    {η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ}
    (hη : η₁ =ᵐ[Measure.restrict volume (UnitCube d)] η₂)
    (hν : ν₁ =ᵐ[Measure.restrict volume (UnitCube d)] ν₂)
    (hDν : ∀ i, Dν₁ i =ᵐ[Measure.restrict volume (UnitCube d)] Dν₂ i) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ Dν₁ η₁ ν₁ =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ Dν₂ η₂ ν₂ := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
  -- Combine the per-i ae-equalities of `Dν` into a single ae-equality of the
  -- pointwise dot-product expressions.
  have hDν_dot : (fun x => (DpH x (fun i => Dυ i x) (μ x))
                              ⬝ (fun i => Dν₁ i x))
                  =ᵐ[Measure.restrict volume (UnitCube d)]
                  (fun x => (DpH x (fun i => Dυ i x) (μ x))
                              ⬝ (fun i => Dν₂ i x)) := by
    have hDν_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, Dν₁ i x = Dν₂ i x := by
      rw [MeasureTheory.ae_all_iff]; exact hDν
    refine hDν_all.mono ?_
    intro x hx
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro i _
    change DpH x (fun j => Dυ j x) (μ x) i * Dν₁ i x
        = DpH x (fun j => Dυ j x) (μ x) i * Dν₂ i x
    rw [hx i]
  have hDν_dot2 : (fun x => (fun i => Dυ i x) ⬝ (fun i => Dν₁ i x))
                  =ᵐ[Measure.restrict volume (UnitCube d)]
                  (fun x => (fun i => Dυ i x) ⬝ (fun i => Dν₂ i x)) := by
    have hDν_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, Dν₁ i x = Dν₂ i x := by
      rw [MeasureTheory.ae_all_iff]; exact hDν
    refine hDν_all.mono ?_
    intro x hx
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro i _
    change Dυ i x * Dν₁ i x = Dυ i x * Dν₂ i x
    rw [hx i]
  -- The two integrals are equal by ae-congruence of the integrands.
  have hI1 : (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η₁ x
          + μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν₁ i x))
          + (μ x - 1) * ν₁ x ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η₂ x
            + μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν₂ i x))
            + (μ x - 1) * ν₂ x ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hη, hν, hDν_dot] with x hxη hxν hxDν
    rw [hxη, hxν, hxDν]
  have hI2 : (∫ x in UnitCube d,
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝ (fun i => Dν₁ i x))
          + absPowMinusTwo γBar (υ x) * (υ x * ν₁ x)
        ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                * ((fun i => Dυ i x) ⬝ (fun i => Dν₂ i x))
            + absPowMinusTwo γBar (υ x) * (υ x * ν₂ x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hν, hDν_dot2] with x hxν hxDν
    rw [hxν, hxDν]
  rw [hI1, hI2]

/-! ## Main: monotonicity wrap -/

/-- **CLM-level monotonicity wrap** for `Aepsi_CLM_op`.

The bare-function integrated monotonicity `aepsi_isMonotone_integrated`
(paper line 1066) lifted to the abstract `IsMonotone` predicate of
`Monotone/Operator.lean` for the CLM family `Aepsi_CLM_op` on the
strict-positivity cone `K_Aepsi`.

The proof:
1. unfolds `IsMonotone` and `ContinuousLinearMap.sub_apply`;
2. applies `Aepsi_CLM_op_apply` to expose the bare pairings;
3. transfers the Lp-coercion test triple `(⇑(v₁ - v₂).1, …)` to the
   pointwise-difference test triple `(⇑v₁.1 - ⇑v₂.1, …)` via
   `mfgOperatorEpsPair_test_congr_ae` and `Lp.coeFn_sub`;
4. recognises the resulting expression as
   `aepsiPairingDiff V H DpH γBarReal ε Du₁ Du₂ m₁ u₁ m₂ u₂`; and
5. invokes `aepsi_isMonotone_integrated`.

The integrability side-conditions of step (5) are passed in as the
hypothesis `hInteg` (one quadruple per pair `v₁, v₂ ∈ K_Aepsi`). -/
theorem isMonotone_Aepsi_CLM
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    {ε : ℝ}
    (hMon : HypothesisMonotone H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hInteg : ∀ v₁ v₂ : palomar_AbstractLifts_XBanach d βBarReal γBarReal,
      v₁ ∈ K_Aepsi d βBarReal γBarReal → v₂ ∈ K_Aepsi d βBarReal γBarReal →
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
            (UnitCube d))) :
    IsMonotone (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHyps ε) := by
  intro v₁ hv₁ v₂ hv₂
  -- Abbreviations.
  set m₁ : (Fin d → ℝ) → ℝ := ⇑v₁.1 with hm₁_def
  set m₂ : (Fin d → ℝ) → ℝ := ⇑v₂.1 with hm₂_def
  set u₁ : (Fin d → ℝ) → ℝ := ⇑v₁.2.1 with hu₁_def
  set u₂ : (Fin d → ℝ) → ℝ := ⇑v₂.2.1 with hu₂_def
  set Du₁ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₁.2.2 i) with hDu₁_def
  set Du₂ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₂.2.2 i) with hDu₂_def
  -- Strict positivity from K_Aepsi membership.
  have hpos₁ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₁ x := hv₁
  have hpos₂ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₂ x := hv₂
  -- Integrability hypotheses for `aepsi_isMonotone_integrated`.
  obtain ⟨hI_mfg₁, hI_mfg₂, hI_g₁, hI_g₂⟩ := hInteg v₁ v₂ hv₁ hv₂
  -- Step 1: unfold the pairing via `sub_apply`.
  -- Goal: `0 ≤ (Aepsi_CLM_op auxHyps ε v₁ - Aepsi_CLM_op auxHyps ε v₂) (v₁ - v₂)`
  change 0 ≤ (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHyps ε v₁
              - Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHyps ε v₂) (v₁ - v₂)
  rw [ContinuousLinearMap.sub_apply]
  -- Step 2: unfold each Aepsi_CLM_op application via `Aepsi_CLM_op_apply`.
  rw [Aepsi_CLM_op_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHyps ε v₁ (v₁ - v₂),
      Aepsi_CLM_op_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHyps ε v₂ (v₁ - v₂)]
  -- Step 3: transfer the Lp-coercion test triple to a pointwise-difference
  -- test triple via `Lp.coeFn_sub` and `mfgOperatorEpsPair_test_congr_ae`.
  have h_eta_ae : ⇑((v₁ - v₂).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] m₁ - m₂ := by
    have h_pair : (v₁ - v₂).1 = v₁.1 - v₂.1 := rfl
    rw [h_pair]
    exact MeasureTheory.Lp.coeFn_sub v₁.1 v₂.1
  have h_nu_ae : ⇑((v₁ - v₂).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] u₁ - u₂ := by
    have h_pair : (v₁ - v₂).2.1 = v₁.2.1 - v₂.2.1 := rfl
    rw [h_pair]
    exact MeasureTheory.Lp.coeFn_sub v₁.2.1 v₂.2.1
  have h_Dnu_ae : ∀ i, ⇑((v₁ - v₂).2.2 i)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      fun x => Du₁ i x - Du₂ i x := by
    intro i
    have h_pair : (v₁ - v₂).2.2 i = v₁.2.2 i - v₂.2.2 i := rfl
    rw [h_pair]
    have := MeasureTheory.Lp.coeFn_sub (v₁.2.2 i) (v₂.2.2 i)
    -- `=ᵐ ⇑(v₁.2.2 i) - ⇑(v₂.2.2 i)`; rewrite as pointwise.
    refine this.mono ?_
    intro x hx
    change ⇑(v₁.2.2 i - v₂.2.2 i) x = Du₁ i x - Du₂ i x
    rw [hx]
    rfl
  -- Use the congruence lemma to swap the test triples on each pairing.
  rw [mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε Du₁ m₁ u₁
        h_eta_ae h_nu_ae h_Dnu_ae]
  rw [mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε Du₂ m₂ u₂
        h_eta_ae h_nu_ae h_Dnu_ae]
  -- Step 4/5: the resulting LHS is `aepsiPairingDiff …`, which is `≥ 0` by
  -- `aepsi_isMonotone_integrated`.
  change 0 ≤ aepsiPairingDiff V H DpH γBarReal ε Du₁ Du₂ m₁ u₁ m₂ u₂
  exact aepsi_isMonotone_integrated (V := V) (H := H) (DpH := DpH)
    (γBar := γBarReal) (ε := ε)
    hMon.toLL hε hScalarMono hVecMono hpos₁ hpos₂
    hI_mfg₁ hI_mfg₂ hI_g₁ hI_g₂

/-! ## Sanity-check example

Trivial Hamiltonian (`H ≡ 0`, `D_pH ≡ 0`) sanity check: the unit-test
`example` confirms the statement type-checks under canonical aux hyps.
The proof itself is delegated to the named theorem.

(We do not actually need to *exhibit* a witness for `auxHyps`/`hInteg`
on the trivial Hamiltonian; the example just witnesses the type-shape
of the wrap conclusion.) -/

example
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                    Du m u)
    {ε : ℝ}
    (hMon : HypothesisMonotone (d := d)
              (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)))
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hInteg : ∀ v₁ v₂ : palomar_AbstractLifts_XBanach d βBarReal γBarReal,
      v₁ ∈ K_Aepsi d βBarReal γBarReal → v₂ ∈ K_Aepsi d βBarReal γBarReal →
        (IntegrableOn
          (fun x =>
            (-(⇑v₁.2.1 x)
                - (fun _ _ _ => (0 : ℝ)) x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
                + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
              + (⇑v₁.1) x *
                  ((fun _ _ _ => (0 : Fin d → ℝ))
                      x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
                      ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
              + ((⇑v₁.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
          (UnitCube d)
        ∧ IntegrableOn
            (fun x =>
              (-(⇑v₂.2.1 x)
                  - (fun _ _ _ => (0 : ℝ)) x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
                  + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
                + (⇑v₂.1) x *
                    ((fun _ _ _ => (0 : Fin d → ℝ))
                        x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
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
            (UnitCube d))) :
    IsMonotone (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) auxHyps ε) :=
  isMonotone_Aepsi_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) auxHyps
    hMon hε hScalarMono hVecMono hInteg

/-! ## Hemicontinuity: CLM-level wrap of `lem_hemicont` (Block B.2)

We expose a CLM-level adapter `isHemicontinuous_Aepsi_CLM` that
discharges `IsHemicontinuous K_Aepsi (Aepsi_CLM_op …)` from the bare-
function aggregator `lem_hemicont`. The proof is a routine bridge:

1. unfold the abstract `IsHemicontinuous` predicate;
2. apply `Aepsi_CLM_op_apply` to expose the bare pairing;
3. transfer the Lp-coercion **primal** triple
   `⇑((1-t)•u + t•v).{1,2.1,2.2}` to the pointwise convex-combination
   triple `(cxComb, cxComb, cxCombGrad …)` via the new primal a.e.-
   congruence lemma combined with `Lp.coeFn_smul`/`Lp.coeFn_add`;
4. invoke `lem_hemicont` on the doubleton domain to obtain continuity
   in `t` of the bare-function pairing.

The aggregator-style hypothesis `hData` packages the `lem_hemicont`
`HemicontSegmentData` bundle for the two endpoints. -/

/-- **a.e.-congruence** of `mfgOperatorEpsPair` in the *primal* triple.
If two primal triples `(Du, m, u)` agree a.e. on the unit cube, the
bare-function pairings against any fixed test triple agree exactly.
This is the primal-side analogue of `mfgOperatorEpsPair_test_congr_ae`. -/
lemma mfgOperatorEpsPair_primal_congr_ae
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    {Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ}
    {m₁ m₂ u₁ u₂ : (Fin d → ℝ) → ℝ}
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hm : m₁ =ᵐ[Measure.restrict volume (UnitCube d)] m₂)
    (hu : u₁ =ᵐ[Measure.restrict volume (UnitCube d)] u₂)
    (hDu : ∀ i, Du₁ i =ᵐ[Measure.restrict volume (UnitCube d)] Du₂ i) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Du₁ m₁ u₁ Dν η ν =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Du₂ m₂ u₂ Dν η ν := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
  -- Pointwise a.e.-equality of the gradient-family components, as a
  -- single `∀ i` ae-statement.
  have hDu_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ∀ i, Du₁ i x = Du₂ i x := by
    rw [MeasureTheory.ae_all_iff]; exact hDu
  -- Congruence on the first integral (the unregularised integrand).
  have hI1 : (∫ x in UnitCube d,
        (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * η x
          + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x) ⬝ (fun i => Dν i x))
          + (m₁ x - 1) * ν x ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * η x
            + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x) ⬝ (fun i => Dν i x))
            + (m₂ x - 1) * ν x ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hm, hu, hDu_all] with x hxm hxu hxDu
    have hDu_eq : (fun i => Du₁ i x) = (fun i => Du₂ i x) := funext hxDu
    rw [hxm, hxu, hDu_eq]
  -- Congruence on the second integral (the Gateaux integrand).
  have hI2 : (∫ x in UnitCube d,
        vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
              * ((fun i => Du₁ i x) ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBar (u₁ x) * (u₁ x * ν x)
        ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
                * ((fun i => Du₂ i x) ⬝ (fun i => Dν i x))
            + absPowMinusTwo γBar (u₂ x) * (u₂ x * ν x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hu, hDu_all] with x hxu hxDu
    have hDu_eq : (fun i => Du₁ i x) = (fun i => Du₂ i x) := funext hxDu
    rw [hxu, hDu_eq]
  rw [hI1, hI2]

/-- **CLM-level hemicontinuity wrap** for `Aepsi_CLM_op`.

The bare-function aggregator `lem_hemicont` (paper line 990) lifted to
the abstract `IsHemicontinuous` predicate of
`Monotone/Hemicontinuous.lean` for the CLM family `Aepsi_CLM_op` on
the strict-positivity cone `K_Aepsi`.

The per-pair `HemicontSegmentData` bundle of `lem_hemicont` is
exposed as a universally-quantified hypothesis `hData` on every pair
`(u, v) ∈ K_Aepsi × K_Aepsi` and every test triple
`(η, ν, Dν) := (⇑w.1, ⇑w.2.1, ⇑w.2.2)`. The proof:

1. unfolds `IsHemicontinuous` and applies `Aepsi_CLM_op_apply`;
2. for each `t ∈ [0,1]`, rewrites `⇑((1-t)•u + t•v).*` (the primal
   data extracted by the CLM) as an a.e.-equal `cxComb`/`cxCombGrad`
   form via `Lp.coeFn_smul`, `Lp.coeFn_add`, and the primal a.e.-
   congruence lemma `mfgOperatorEpsPair_primal_congr_ae`;
3. invokes `lem_hemicont` on the doubleton domain
   `{(⇑v.1, ⇑v.2.1, ⇑v.2.2), (⇑u.1, ⇑u.2.1, ⇑u.2.2)}` to obtain
   continuity in `t` of the bare-function pairing;
4. transfers continuity along the pointwise (in `t`) equality of step 2
   via `ContinuousOn.congr`. -/
theorem isHemicontinuous_Aepsi_CLM
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    {ε : ℝ}
    (hReg : RegularityH (d := d) H DpH)
    -- Phase 1c (`infra-P5-theorem1-phase-1c`): the only consumer is
    -- `Aepsi_hemicontinuous_segment`, which itself takes `1 < γBar`.
    (hγ : 1 < γBarReal)
    -- Per `infra-P4-domain-indexed-Aepsi-CLM` (acceptance 6): narrowed to
    -- `K_Aepsi` endpoints only (the universal-endpoint quantifier was
    -- wasteful since `IsHemicontinuous`'s definition only tests
    -- domain endpoints).
    (hData : ∀ (u v : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
      HemicontSegmentData (d := d) V H DpH γBarReal
        (fun i => ⇑(v.2.2 i)) (fun i => ⇑(u.2.2 i))
        (⇑v.1) (⇑u.1) (⇑v.2.1) (⇑u.2.1)
        (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)) :
    Monotone.IsHemicontinuous (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHyps ε) := by
  intro u hu v hv w
  -- Abbreviations for the bare-function endpoints/test.
  set μBar : (Fin d → ℝ) → ℝ := ⇑u.1 with hμBar_def
  set μ : (Fin d → ℝ) → ℝ := ⇑v.1 with hμ_def
  set ῡ : (Fin d → ℝ) → ℝ := ⇑u.2.1 with hῡ_def
  set υ : (Fin d → ℝ) → ℝ := ⇑v.2.1 with hυ_def
  set Dῡ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(u.2.2 i) with hDῡ_def
  set Dυ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v.2.2 i) with hDυ_def
  set η : (Fin d → ℝ) → ℝ := ⇑w.1 with hη_def
  set ν : (Fin d → ℝ) → ℝ := ⇑w.2.1 with hν_def
  set Dν : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(w.2.2 i) with hDν_def
  -- Extract the per-segment dominator bundle for the chosen `u, v, w`.
  obtain ⟨hPos, g_unreg, g_gat, hg_unreg_int, hg_gat_int,
          hF_unreg_meas, hF_unreg_bound, hF_gat_meas, hF_gat_bound⟩ :=
    hData u v hu hv w
  -- Continuity of the bare-function pairing in `t`, from the segment-
  -- level DCT lemma `Aepsi_hemicontinuous_segment`, which accepts
  -- `1 < γBar` directly (Phase 1c, `infra-P5-theorem1-phase-1c`).
  have hCts := Aepsi_hemicontinuous_segment (V := V) (H := H) (DpH := DpH)
                 hReg γBarReal ε hγ Dυ Dῡ μ μBar υ ῡ Dν η ν
                 hPos g_unreg g_gat hg_unreg_int hg_gat_int
                 hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
  -- Goal: ContinuousOn of `t ↦ Aepsi_CLM_op auxHyps ε ((1-t)•u + t•v) w`.
  -- Apply `Aepsi_CLM_op_apply` pointwise in `t` to get the bare pairing
  -- with the Lp-coercion primal triple of `((1-t)•u + t•v)`.
  -- We then bridge via the primal a.e.-congruence to the `cxComb` form,
  -- which is the function of `t` whose continuity is given by `hCts`.
  -- For each `t`, build the a.e.-equality of the primal data.
  have h_prim_eq : ∀ t : ℝ,
      Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHyps ε ((1 - t) • u + t • v) w
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i x => cxCombGrad Dυ Dῡ t i x)
            (fun x => cxComb μ μBar t x)
            (fun x => cxComb υ ῡ t x)
            Dν η ν := by
    intro t
    rw [Aepsi_CLM_op_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHyps ε ((1 - t) • u + t • v) w]
    -- a.e.-equalities for primal data of `(1-t)•u + t•v`.
    have h_m_ae : ⇑(((1 - t) • u + t • v).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxComb μ μBar t x) := by
      have h_pair : ((1 - t) • u + t • v).1 = (1 - t) • u.1 + t • v.1 := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.1) (t • v.1)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) u.1
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t v.1
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxComb, μ, μBar]
    have h_u_ae : ⇑(((1 - t) • u + t • v).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxComb υ ῡ t x) := by
      have h_pair : ((1 - t) • u + t • v).2.1 = (1 - t) • u.2.1 + t • v.2.1 := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.2.1) (t • v.2.1)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) u.2.1
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t v.2.1
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxComb, υ, ῡ]
    have h_Du_ae : ∀ i, (fun x => ⇑(((1 - t) • u + t • v).2.2 i) x)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxCombGrad Dυ Dῡ t i x) := by
      intro i
      have h_pair : ((1 - t) • u + t • v).2.2 i = (1 - t) • u.2.2 i + t • v.2.2 i := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.2.2 i) (t • v.2.2 i)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) (u.2.2 i)
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t (v.2.2 i)
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxCombGrad, Dυ, Dῡ]
    -- Apply the primal a.e.-congruence.
    exact mfgOperatorEpsPair_primal_congr_ae V H DpH γBarReal ε Dν η ν
      h_m_ae h_u_ae h_Du_ae
  -- Now transfer continuity from the `cxComb` form to the
  -- `Lp-coercion` form via `ContinuousOn.congr`.
  -- `ContinuousOn.congr : ContinuousOn f s → (∀ x ∈ s, g x = f x) → ContinuousOn g s`.
  refine hCts.congr ?_
  intro t _ht
  exact h_prim_eq t

/-! ### Sanity-check `example` for the hemicontinuity wrap

Trivial Hamiltonian (`H ≡ 0`, `D_pH ≡ 0`, `V ≡ 0`) sanity check: the
unit-test `example` confirms the statement type-checks under canonical
aux hyps. The proof itself is delegated to the named theorem. -/

example
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    (fun _ => (0 : ℝ))
                    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                    Du m u)
    {ε : ℝ}
    (hReg : RegularityH (d := d)
              (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)))
    (hγ : 1 < γBarReal)
    (hData : ∀ (u v : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
      HemicontSegmentData (d := d)
        (fun _ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
        γBarReal
        (fun i => ⇑(v.2.2 i)) (fun i => ⇑(u.2.2 i))
        (⇑v.1) (⇑u.1) (⇑v.2.1) (⇑u.2.1)
        (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)) :
    Monotone.IsHemicontinuous (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (fun _ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) auxHyps ε) :=
  isHemicontinuous_Aepsi_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (fun _ => (0 : ℝ))
    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) auxHyps
    hReg hγ hData

/-! ## Coercivity: CLM-level wrap of `coercAepsi` (Block B.3)

We expose a CLM-level adapter `isCoerciveAt_Aepsi_CLM` that
discharges `IsCoerciveAt K_Aepsi (Aepsi_CLM_op …) v0` from the
bare-function `Tendsto`-form of `paper:prop:coercAepsi`. The proof is
a routine bridge:

1. Discharge `v0 ∈ K_Aepsi` from the strict-positivity hypothesis on
   `⇑v0.1`.
2. Show `Tendsto (‖·‖) (cobounded X ⊓ 𝓟 K) atTop` via
   `tendsto_norm_cobounded_atTop` and `Filter.Tendsto.mono_left`.
3. Apply `coercAepsi` on the `palomar_AbstractLifts_XBanach`-indexed family with
   `Du_of v := fun i => ⇑(v.2.2 i)`, `m_of v := ⇑v.1`,
   `u_of v := ⇑v.2.1`, `nrm := fun v => ‖v‖`. The hypothesis
   `hbound` (integrated lower bound) and `hquot_tendsto` are passed
   in by the caller, exactly as required by `coercAepsi`.
4. Use `Filter.Tendsto.congr'` to bridge the `coercAepsi` conclusion
   to the abstract `IsCoerciveAt` conclusion. The eventual equality
   uses:
   * `ContinuousLinearMap.sub_apply` to expose the difference,
   * `Aepsi_CLM_op_apply` (twice) to expose the bare pairings,
   * `MeasureTheory.Lp.coeFn_sub` and the a.e.-equalities on the `v0`
     primal data to rewrite `⇑((v - v0).{*})` as the pointwise
     differences with `(0, 1, 0)`,
   * `mfgOperatorEpsPair_test_congr_ae` to swap the test triple,
   * `mfgOperatorEpsPair_primal_congr_ae` to swap the `v0` primal
     triple to the literal `(0, 1, 0)` used by `coercAepsi`.
-/

/-- **CLM-level coercivity wrap** for `Aepsi_CLM_op`.

The bare-function `Tendsto`-form of `coercAepsi` (paper line 982,
`prop:coercAepsi`) lifted to the abstract `IsCoerciveAt` predicate of
`Monotone/Coercive.lean` for the CLM family `Aepsi_CLM_op` on the
strict-positivity cone `K_Aepsi`.

The base-point `v0 : palomar_AbstractLifts_XBanach` is supplied by the caller, together
with three a.e.-equalities expressing that its primal triple
`(⇑(v0.2.2 i), ⇑v0.1, ⇑v0.2.1)` is a.e.-equal to `(0, 1, 0)` — the
base point used by `coercAepsi`. The strict-positivity membership
`v0 ∈ K_Aepsi` follows from `h_m0_ae` (since `1 > 0`).

The integrated lower bound `hbound` and the auxiliary quotient limit
`hquot_tendsto` are exactly the hypotheses of `coercAepsi`,
parameterised on `α := palomar_AbstractLifts_XBanach` with `nrm := fun v => ‖v‖` and the
filter `coerciveFilter (K_Aepsi …) = cobounded ⊓ 𝓟 (K_Aepsi …)`. -/
theorem isCoerciveAt_Aepsi_CLM
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    (ε : ℝ)
    (v0 : palomar_AbstractLifts_XBanach d βBarReal γBarReal)
    (h_m0_ae : ⇑v0.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (1 : ℝ)))
    (h_u0_ae : ⇑v0.2.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (h_Du0_ae : ∀ i, ⇑(v0.2.2 i)
                  =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (g : palomar_AbstractLifts_XBanach d βBarReal γBarReal → ℝ)
    (C : ℝ)
    (hbound :
      ∀ᶠ v in (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        g v - C ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (hquot_tendsto :
      Filter.Tendsto (fun v => g v / ‖v‖)
        (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop) :
    Monotone.IsCoerciveAt (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHyps ε)
      v0 := by
  -- Step 1: `v0 ∈ K_Aepsi` from `h_m0_ae` (strict positivity of `1`).
  have hv0_mem : v0 ∈ K_Aepsi d βBarReal γBarReal := by
    refine h_m0_ae.mono ?_
    intro x hx
    simp [hx]
  refine ⟨hv0_mem, ?_⟩
  -- Step 2: `‖v‖ → ∞` along the coercivity filter.
  have h_nrm_tendsto :
      Filter.Tendsto (fun v : palomar_AbstractLifts_XBanach d βBarReal γBarReal => ‖v‖)
        (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  -- And `‖v‖ > 0` eventually (in fact, `‖v‖ ≥ 1` eventually).
  have h_nrm_pos :
      ∀ᶠ v in (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        (0 : ℝ) < ‖v‖ := by
    refine h_nrm_tendsto.eventually_gt_atTop 0
  -- Step 3: invoke `coercAepsi` on the `palomar_AbstractLifts_XBanach`-indexed family.
  have hCoerc :=
    coercAepsi (V := V) (H := H) (DpH := DpH)
      γBarReal ε
      (l := (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
              ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)))
      (Du_of := fun v : palomar_AbstractLifts_XBanach d βBarReal γBarReal => fun i => ⇑(v.2.2 i))
      (m_of := fun v => ⇑v.1)
      (u_of := fun v => ⇑v.2.1)
      g (fun v => ‖v‖) C
      hbound h_nrm_pos h_nrm_tendsto hquot_tendsto
  -- Step 4: bridge the `coercAepsi` conclusion to the abstract one via
  -- `Filter.Tendsto.congr'`.
  refine hCoerc.congr' ?_
  -- Eventual equality of the two integrand functions of `v`.
  -- We prove the equality pointwise (strong; not just eventual).
  refine Filter.Eventually.of_forall (fun v => ?_)
  -- Apply CLM unfolding lemmas on the LHS.
  have h_subapply :
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V H DpH auxHyps ε v
          - Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHyps ε v0) (v - v0)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
              (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1) := by
    rw [ContinuousLinearMap.sub_apply,
        Aepsi_CLM_op_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHyps ε v (v - v0),
        Aepsi_CLM_op_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHyps ε v0 (v - v0)]
  -- a.e.-equalities for the test triple `(v - v0)`.
  -- `⇑((v - v0).1) =ᵐ ⇑v.1 - 1`.
  have h_eta_ae' : ⇑((v - v0).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      ((⇑v.1) - 1) := by
    have h_pair : (v - v0).1 = v.1 - v0.1 := rfl
    rw [h_pair]
    have hsub := MeasureTheory.Lp.coeFn_sub v.1 v0.1
    filter_upwards [hsub, h_m0_ae] with x hx h0
    -- After `change`, goal becomes `⇑(v.1 - v0.1) x = (⇑v.1 - 1) x`.
    -- `Pi.sub_apply`: `(⇑v.1 - 1) x = ⇑v.1 x - 1`. We rewrite step by step.
    rw [hx]
    change (⇑v.1 - ⇑v0.1) x = (⇑v.1 - 1) x
    rw [Pi.sub_apply, Pi.sub_apply, h0, Pi.one_apply]
  -- `⇑((v - v0).2.1) =ᵐ ⇑v.2.1`.
  have h_nu_ae : ⇑((v - v0).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      ⇑v.2.1 := by
    have h_pair : (v - v0).2.1 = v.2.1 - v0.2.1 := rfl
    rw [h_pair]
    have hsub := MeasureTheory.Lp.coeFn_sub v.2.1 v0.2.1
    filter_upwards [hsub, h_u0_ae] with x hx h0
    rw [hx]
    change (⇑v.2.1 - ⇑v0.2.1) x = ⇑v.2.1 x
    rw [Pi.sub_apply, h0, sub_zero]
  -- `⇑((v - v0).2.2 i) =ᵐ ⇑(v.2.2 i)`.
  have h_Dnu_ae : ∀ i, ⇑((v - v0).2.2 i)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      fun x => ⇑(v.2.2 i) x := by
    intro i
    have h_pair : (v - v0).2.2 i = v.2.2 i - v0.2.2 i := rfl
    rw [h_pair]
    have hsub := MeasureTheory.Lp.coeFn_sub (v.2.2 i) (v0.2.2 i)
    filter_upwards [hsub, h_Du0_ae i] with x hx h0
    rw [hx]
    change (⇑(v.2.2 i) - ⇑(v0.2.2 i)) x = ⇑(v.2.2 i) x
    rw [Pi.sub_apply, h0, sub_zero]
  -- Apply test-triple a.e.-congruence to swap test of first pairing.
  have h_test_swap1 :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
          (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
    mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε
      (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
      h_eta_ae' h_nu_ae h_Dnu_ae
  -- Apply test-triple a.e.-congruence to swap test of second pairing.
  have h_test_swap2 :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
          (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
    mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε
      (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
      h_eta_ae' h_nu_ae h_Dnu_ae
  -- Apply primal-triple a.e.-congruence to swap the second pairing's
  -- primal triple from `v0`'s data to the literal `(0, 1, 0)` used by
  -- `coercAepsi`.
  have h_primal_swap :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
          (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
    refine mfgOperatorEpsPair_primal_congr_ae V H DpH γBarReal ε
      (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
      h_m0_ae h_u0_ae ?_
    intro i
    exact h_Du0_ae i
  -- Now assemble: beta-reduce the goal (it contains `(fun v => …) v`),
  -- then chain the four rewrites. The goal direction is LHS = RHS where
  -- LHS is the `coercAepsi`-form (post-beta) and RHS is the abstract
  -- `Aepsi_CLM_op` form. We rewrite the RHS into `coercAepsi`-form by
  -- applying `h_subapply, h_test_swap1, h_test_swap2, h_primal_swap`
  -- in symmetric direction.
  change (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)) / ‖v‖
        = (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHyps ε v
            - Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps ε v0) (v - v0) / ‖v‖
  rw [h_subapply, h_test_swap1, h_test_swap2, h_primal_swap]

/-! ### Sanity-check `example` for the coercivity wrap

Trivial Hamiltonian (`H ≡ 0`, `D_pH ≡ 0`, `V ≡ 0`) sanity check: the
unit-test `example` confirms the statement type-checks under canonical
aux hyps. The proof itself is delegated to the named theorem. -/

example
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    (fun _ => (0 : ℝ))
                    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                    Du m u)
    (ε : ℝ)
    (v0 : palomar_AbstractLifts_XBanach d βBarReal γBarReal)
    (h_m0_ae : ⇑v0.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (1 : ℝ)))
    (h_u0_ae : ⇑v0.2.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (h_Du0_ae : ∀ i, ⇑(v0.2.2 i)
                  =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (g : palomar_AbstractLifts_XBanach d βBarReal γBarReal → ℝ)
    (C : ℝ)
    (hbound :
      ∀ᶠ v in (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        g v - C ≤
          mfgOperatorEpsPair (V := (fun _ => (0 : ℝ)))
              (H := (fun _ _ _ => (0 : ℝ)))
              (DpH := (fun _ _ _ => (0 : Fin d → ℝ)))
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := (fun _ => (0 : ℝ)))
                (H := (fun _ _ _ => (0 : ℝ)))
                (DpH := (fun _ _ _ => (0 : Fin d → ℝ)))
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (hquot_tendsto :
      Filter.Tendsto (fun v => g v / ‖v‖)
        (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop) :
    Monotone.IsCoerciveAt (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (fun _ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) auxHyps ε)
      v0 :=
  isCoerciveAt_Aepsi_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (fun _ => (0 : ℝ))
    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) auxHyps ε
    v0 h_m0_ae h_u0_ae h_Du0_ae g C hbound hquot_tendsto

/-! ## Domain-indexed totalized operator `Aepsi_CLM_opK`

Per the v3 expert plan post-`mfg-operator-clm` audit (iteration 230)
and `infra-P4-domain-indexed-Aepsi-CLM`: the just-landed
`auxHyps_of_paperHypotheses_on_KAepsi` produces a `K_Aepsi`-indexed
supplier
```
auxHypsK : ∀ q ∈ K_Aepsi, MFGOpEpsAuxHyps … (DuOf q) (mOf q) (uOf q)
```
matching the strict-positivity discharge of the per-triple feeder
`auxHyps_of_paperHypotheses_at_triple`. The operator family
`Aepsi_CLM_op` consumes the structurally-false universal shape
`∀ Du m u, MFGOpEpsAuxHyps …`; we expose here a **totalized**
operator `Aepsi_CLM_opK` that evaluates the CLM only on `K_Aepsi`
(using the per-`q` supplier), and returns `0` outside.

The "totalize via 0 outside" pattern is standard for
Browder–Minty applications where the abstract-VI machinery only
inspects operator values on the convex closed domain. The
monotonicity / hemicontinuity / coercivity statements remain
quantified over `K_Aepsi`-elements, where `Aepsi_CLM_opK` agrees
on-the-nose with the underlying CLM.

The on-domain unfolding `Aepsi_CLM_opK_apply_of_mem` matches the
shape of `Aepsi_CLM_op_apply` and lets the K_Aepsi-form abstract VI
lifts re-use the universal-form proof bodies verbatim. -/

/-- **K_Aepsi-domain-indexed totalized regularised MFG operator family.**

Given a `K_Aepsi`-indexed `auxHypsK` supplier (matching the
just-landed `auxHyps_of_paperHypotheses_on_KAepsi` shape),
`Aepsi_CLM_opK auxHypsK ε` is the function `X → (X →L[ℝ] ℝ)`
whose value at `v` is:

* the CLM `mfgOperatorEps_CLM` built with primal data extracted
  from `v` and the supplier at `v`, when `v ∈ K_Aepsi`,
* the zero CLM, otherwise.

Outside `K_Aepsi` the operator value is never tested by the
Browder–Minty machinery (monotonicity / hemicontinuity / coercivity
are all quantified over `K_Aepsi`-elements). -/
noncomputable def Aepsi_CLM_opK
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ) (v : palomar_AbstractLifts_XBanach d βBarReal γBarReal) :
    palomar_AbstractLifts_XBanach d βBarReal γBarReal →L[ℝ] ℝ := by
  classical
  exact
    if h : v ∈ K_Aepsi d βBarReal γBarReal then
      mfgOperatorEps_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (V := V) (H := H) (DpH := DpH)
        (Du := fun i => ⇑(v.2.2 i)) (m := ⇑v.1) (u := ⇑v.2.1)
        (auxHypsK v h) ε
    else 0

/-- **On-domain identity** for `Aepsi_CLM_opK`. For `v ∈ K_Aepsi`,
the totalized operator equals the CLM built with the supplier at `v`. -/
theorem Aepsi_CLM_opK_apply_of_mem
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ) {v : palomar_AbstractLifts_XBanach d βBarReal γBarReal}
    (hv : v ∈ K_Aepsi d βBarReal γBarReal)
    (q : palomar_AbstractLifts_XBanach d βBarReal γBarReal) :
    Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε v q
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) := by
  classical
  -- `Aepsi_CLM_opK` reduces to the underlying CLM at `v ∈ K_Aepsi`.
  have h_eq : Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK ε v
        = mfgOperatorEps_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            (V := V) (H := H) (DpH := DpH)
            (Du := fun i => ⇑(v.2.2 i)) (m := ⇑v.1) (u := ⇑v.2.1)
            (auxHypsK v hv) ε := by
    unfold Aepsi_CLM_opK
    simp [hv]
  rw [h_eq]
  exact mfgOperatorEps_CLM_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (V := V) (H := H) (DpH := DpH)
    (Du := fun i => ⇑(v.2.2 i)) (m := ⇑v.1) (u := ⇑v.2.1)
    (auxHypsK v hv) ε q

/-- **Off-domain identity** for `Aepsi_CLM_opK`. For
`v ∉ K_Aepsi`, the totalized operator is the zero CLM. -/
theorem Aepsi_CLM_opK_eq_zero_of_not_mem
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ) {v : palomar_AbstractLifts_XBanach d βBarReal γBarReal}
    (hv : v ∉ K_Aepsi d βBarReal γBarReal) :
    Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε v
      = 0 := by
  classical
  unfold Aepsi_CLM_opK
  simp [hv]

/-! ### Sanity-check `example` for `Aepsi_CLM_opK`

The on-domain identity is the load-bearing equation: the K_Aepsi-form
abstract-VI lifts below reduce their goals to the bare-pairing form
via `Aepsi_CLM_opK_apply_of_mem`, exactly as the universal-form lifts
use `Aepsi_CLM_op_apply`. Off-domain the value is `0`, by definition. -/

example
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ) {v : palomar_AbstractLifts_XBanach d βBarReal γBarReal}
    (hv : v ∉ K_Aepsi d βBarReal γBarReal) :
    Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε v = 0 :=
  Aepsi_CLM_opK_eq_zero_of_not_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK ε hv

/-! ## K_Aepsi-form abstract-VI lifts targeting `Aepsi_CLM_opK`

The three lifts below mirror `isMonotone_Aepsi_CLM`,
`isHemicontinuous_Aepsi_CLM`, `isCoerciveAt_Aepsi_CLM` but target the
totalized `Aepsi_CLM_opK` instead of the universal `Aepsi_CLM_op`.
Their proof bodies reduce to the universal-form proofs via the
on-domain identity `Aepsi_CLM_opK_apply_of_mem`, since
monotonicity / hemicontinuity / coercivity all evaluate the operator
only on `K_Aepsi`-elements (where the totalization is transparent).

The hemicontinuity lift narrows the `hData` quantifier to require
`HemicontSegmentData` only at K_Aepsi endpoints, per the task's
acceptance criterion 6 (the universal-endpoint quantifier of
`isHemicontinuous_Aepsi_CLM` is wasteful: only K_Aepsi endpoints are
ever tested by `IsHemicontinuous`'s definition). -/

/-- **CLM-level monotonicity wrap (K_Aepsi-form, totalized).**

Same as `isMonotone_Aepsi_CLM` but targeting the totalized operator
`Aepsi_CLM_opK` and consuming a K_Aepsi-indexed supplier
`auxHypsK`. The proof reduces to `isMonotone_Aepsi_CLM`'s proof body
via the on-domain identity `Aepsi_CLM_opK_apply_of_mem`.

**LL-only carrier.** This is the `_of_ll` sibling: the monotonicity
hypothesis is the bare Lasry–Lions inequality `LLInequality H DpH`
(the type of `HypothesisMonotone.monotone`), NOT the full
`HypothesisMonotone` bundle. The consumer chain
(`aepsi_isMonotone_integrated → aepsi_pointwise_monotone →
llPointwise_nonneg_ae`) projects only the `monotone` field, so the
weaker carrier suffices. The full-bundle version
`isMonotone_Aepsi_CLM_K_Aepsi` below delegates here via `hMon.toLL`. -/
theorem isMonotone_Aepsi_CLM_K_Aepsi_of_ll
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
              ⬝ (v - w))
    (hInteg : ∀ v₁ v₂ : palomar_AbstractLifts_XBanach d βBarReal γBarReal,
      v₁ ∈ K_Aepsi d βBarReal γBarReal → v₂ ∈ K_Aepsi d βBarReal γBarReal →
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
            (UnitCube d))) :
    IsMonotone (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) := by
  intro v₁ hv₁ v₂ hv₂
  -- Abbreviations.
  set m₁ : (Fin d → ℝ) → ℝ := ⇑v₁.1 with hm₁_def
  set m₂ : (Fin d → ℝ) → ℝ := ⇑v₂.1 with hm₂_def
  set u₁ : (Fin d → ℝ) → ℝ := ⇑v₁.2.1 with hu₁_def
  set u₂ : (Fin d → ℝ) → ℝ := ⇑v₂.2.1 with hu₂_def
  set Du₁ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₁.2.2 i) with hDu₁_def
  set Du₂ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₂.2.2 i) with hDu₂_def
  -- Strict positivity from K_Aepsi membership.
  have hpos₁ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₁ x := hv₁
  have hpos₂ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₂ x := hv₂
  -- Integrability hypotheses for `aepsi_isMonotone_integrated`.
  obtain ⟨hI_mfg₁, hI_mfg₂, hI_g₁, hI_g₂⟩ := hInteg v₁ v₂ hv₁ hv₂
  -- Step 1: unfold the pairing via `sub_apply`.
  change 0 ≤ (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHypsK ε v₁
              - Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε v₂) (v₁ - v₂)
  rw [ContinuousLinearMap.sub_apply]
  -- Step 2: unfold each Aepsi_CLM_opK application via on-domain identity.
  rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε hv₁ (v₁ - v₂),
      Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε hv₂ (v₁ - v₂)]
  -- Step 3: transfer the Lp-coercion test triple to a pointwise-difference
  -- test triple via `Lp.coeFn_sub` and `mfgOperatorEpsPair_test_congr_ae`.
  have h_eta_ae : ⇑((v₁ - v₂).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] m₁ - m₂ := by
    have h_pair : (v₁ - v₂).1 = v₁.1 - v₂.1 := rfl
    rw [h_pair]
    exact MeasureTheory.Lp.coeFn_sub v₁.1 v₂.1
  have h_nu_ae : ⇑((v₁ - v₂).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] u₁ - u₂ := by
    have h_pair : (v₁ - v₂).2.1 = v₁.2.1 - v₂.2.1 := rfl
    rw [h_pair]
    exact MeasureTheory.Lp.coeFn_sub v₁.2.1 v₂.2.1
  have h_Dnu_ae : ∀ i, ⇑((v₁ - v₂).2.2 i)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      fun x => Du₁ i x - Du₂ i x := by
    intro i
    have h_pair : (v₁ - v₂).2.2 i = v₁.2.2 i - v₂.2.2 i := rfl
    rw [h_pair]
    have := MeasureTheory.Lp.coeFn_sub (v₁.2.2 i) (v₂.2.2 i)
    refine this.mono ?_
    intro x hx
    change ⇑(v₁.2.2 i - v₂.2.2 i) x = Du₁ i x - Du₂ i x
    rw [hx]
    rfl
  rw [mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε Du₁ m₁ u₁
        h_eta_ae h_nu_ae h_Dnu_ae]
  rw [mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε Du₂ m₂ u₂
        h_eta_ae h_nu_ae h_Dnu_ae]
  change 0 ≤ aepsiPairingDiff V H DpH γBarReal ε Du₁ Du₂ m₁ u₁ m₂ u₂
  exact aepsi_isMonotone_integrated (V := V) (H := H) (DpH := DpH)
    (γBar := γBarReal) (ε := ε)
    hMon hε hScalarMono hVecMono hpos₁ hpos₂
    hI_mfg₁ hI_mfg₂ hI_g₁ hI_g₂

/-- **CLM-level monotonicity wrap (K_Aepsi-form, totalized) — full bundle.**

Thin wrapper over `isMonotone_Aepsi_CLM_K_Aepsi_of_ll` that accepts the
full `HypothesisMonotone H DpH` bundle (preserving all existing T1/T2
call-sites), forwarding only its `monotone` field via `hMon.toLL`. -/
theorem isMonotone_Aepsi_CLM_K_Aepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hMon : HypothesisMonotone H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hInteg : ∀ v₁ v₂ : palomar_AbstractLifts_XBanach d βBarReal γBarReal,
      v₁ ∈ K_Aepsi d βBarReal γBarReal → v₂ ∈ K_Aepsi d βBarReal γBarReal →
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
            (UnitCube d))) :
    IsMonotone (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) :=
  isMonotone_Aepsi_CLM_K_Aepsi_of_ll (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hMon.toLL hε hScalarMono hVecMono hInteg

/-- **CLM-level hemicontinuity wrap (K_Aepsi-form, totalized).**

Same as `isHemicontinuous_Aepsi_CLM` but targeting the totalized
operator `Aepsi_CLM_opK`, with the `hData` quantifier **narrowed** to
K_Aepsi endpoints (per the task's acceptance criterion 6: the
universal-endpoint quantifier of the original lift is wasteful since
`IsHemicontinuous` only tests endpoints in the domain). -/
theorem isHemicontinuous_Aepsi_CLM_K_Aepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hReg : RegularityH (d := d) H DpH)
    -- Phase 1c (`infra-P5-theorem1-phase-1c`): the only consumer is
    -- `Aepsi_hemicontinuous_segment`, which itself takes `1 < γBar`.
    (hγ : 1 < γBarReal)
    (hData : ∀ (u v : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
      HemicontSegmentData (d := d) V H DpH γBarReal
        (fun i => ⇑(v.2.2 i)) (fun i => ⇑(u.2.2 i))
        (⇑v.1) (⇑u.1) (⇑v.2.1) (⇑u.2.1)
        (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)) :
    Monotone.IsHemicontinuous (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) := by
  intro u hu v hv w
  -- Abbreviations.
  set μBar : (Fin d → ℝ) → ℝ := ⇑u.1 with hμBar_def
  set μ : (Fin d → ℝ) → ℝ := ⇑v.1 with hμ_def
  set ῡ : (Fin d → ℝ) → ℝ := ⇑u.2.1 with hῡ_def
  set υ : (Fin d → ℝ) → ℝ := ⇑v.2.1 with hυ_def
  set Dῡ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(u.2.2 i) with hDῡ_def
  set Dυ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v.2.2 i) with hDυ_def
  set η : (Fin d → ℝ) → ℝ := ⇑w.1 with hη_def
  set ν : (Fin d → ℝ) → ℝ := ⇑w.2.1 with hν_def
  set Dν : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(w.2.2 i) with hDν_def
  -- Extract the per-segment dominator bundle for the chosen `u, v, w`.
  obtain ⟨hPos, g_unreg, g_gat, hg_unreg_int, hg_gat_int,
          hF_unreg_meas, hF_unreg_bound, hF_gat_meas, hF_gat_bound⟩ :=
    hData u v hu hv w
  -- Continuity of the bare-function pairing in `t`, from the segment-
  -- level DCT lemma `Aepsi_hemicontinuous_segment`, which accepts
  -- `1 < γBar` directly (Phase 1c, `infra-P5-theorem1-phase-1c`).
  have hCts := Aepsi_hemicontinuous_segment (V := V) (H := H) (DpH := DpH)
                 hReg γBarReal ε hγ Dυ Dῡ μ μBar υ ῡ Dν η ν
                 hPos g_unreg g_gat hg_unreg_int hg_gat_int
                 hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
  -- Bridge: for `t ∈ [0,1]`, the convex combination `(1-t)•u + t•v` lies
  -- in `K_Aepsi` (by `K_Aepsi_convex`), so `Aepsi_CLM_opK` agrees with
  -- the universal CLM there. Then transfer via primal a.e.-congruence
  -- to the `cxComb`-form whose continuity is given by `hCts`.
  have h_prim_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε ((1 - t) • u + t • v) w
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i x => cxCombGrad Dυ Dῡ t i x)
            (fun x => cxComb μ μBar t x)
            (fun x => cxComb υ ῡ t x)
            Dν η ν := by
    intro t ht
    -- `(1-t)•u + t•v ∈ K_Aepsi` via convexity (`a := 1-t`, `b := t`).
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1mt : (0 : ℝ) ≤ 1 - t := by linarith
    have hab : (1 - t) + t = 1 := by ring
    have hConv : (1 - t) • u + t • v ∈ K_Aepsi d βBarReal γBarReal :=
      convex_iff_add_mem.mp (K_Aepsi_convex d βBarReal γBarReal) hu hv h1mt ht0 hab
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hConv w]
    -- Now reduce to the `cxComb` form via primal a.e.-congruence.
    have h_m_ae : ⇑(((1 - t) • u + t • v).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxComb μ μBar t x) := by
      have h_pair : ((1 - t) • u + t • v).1 = (1 - t) • u.1 + t • v.1 := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.1) (t • v.1)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) u.1
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t v.1
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxComb, μ, μBar]
    have h_u_ae : ⇑(((1 - t) • u + t • v).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxComb υ ῡ t x) := by
      have h_pair : ((1 - t) • u + t • v).2.1 = (1 - t) • u.2.1 + t • v.2.1 := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.2.1) (t • v.2.1)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) u.2.1
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t v.2.1
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxComb, υ, ῡ]
    have h_Du_ae : ∀ i, (fun x => ⇑(((1 - t) • u + t • v).2.2 i) x)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxCombGrad Dυ Dῡ t i x) := by
      intro i
      have h_pair : ((1 - t) • u + t • v).2.2 i = (1 - t) • u.2.2 i + t • v.2.2 i := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.2.2 i) (t • v.2.2 i)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) (u.2.2 i)
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t (v.2.2 i)
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxCombGrad, Dυ, Dῡ]
    exact mfgOperatorEpsPair_primal_congr_ae V H DpH γBarReal ε Dν η ν
      h_m_ae h_u_ae h_Du_ae
  refine hCts.congr ?_
  intro t ht
  exact h_prim_eq t ht

/-- **CLM-level hemicontinuity wrap (K_Aepsi-form, totalized, closed-cone
`RegularityHK0` route).**

The AE-route / closed-cone sibling of `isHemicontinuous_Aepsi_CLM_K_Aepsi`.
Identical statement and proof skeleton, but its segment-continuity content is
sourced from `Aepsi_hemicontinuous_setSegment_K0` (the closed-cone DCT lemma
keyed on `RegularityHK0`) rather than `Aepsi_hemicontinuous_segment` (the
strict-cone lemma keyed on the global `RegularityH`). This lets the
`HdeltaK0`-keyed `AepsiUniformContextK.hHC` field be discharged from the
AE-route closed-cone regularity certificate
`regularityHK0_HdeltaK0_DpHepsilon_of_selector` — which needs only
`HypothesisHextJointCont`/`HypothesisDpHMeasurable`/`HdeltaAEPowerEpsData`/`sel`,
NOT the strict `RegularityH (HdeltaPos)` / `hpow` / `hFormPos`.

The per-`(u, v, w)` segment bundle is supplied as `HemicontSegmentDataK0`
(nonnegative density, `aepsiIntegrandAt_unreg_K0` integrand). On `K_Aepsi` the
convex combination `(1-t)•u + t•v` lies in the cone (so the operator agrees with
the universal CLM there via `Aepsi_CLM_opK_apply_of_mem`), and the
`mfgOperatorEpsPair` form produced by `Aepsi_hemicontinuous_setSegment_K0` is
exactly the `cxComb`/`cxCombGrad` form the operator reduces to (same primal
a.e.-congruence step as the strict version). -/
theorem isHemicontinuous_Aepsi_CLM_K_Aepsi_K0
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hRegK0 : StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d) H DpH)
    (hγ : 1 < γBarReal)
    (hData : ∀ (u v : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : palomar_AbstractLifts_XBanach d βBarReal γBarReal),
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0 (d := d)
        V H DpH γBarReal
        (fun i => ⇑(v.2.2 i)) (fun i => ⇑(u.2.2 i))
        (⇑v.1) (⇑u.1) (⇑v.2.1) (⇑u.2.1)
        (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)) :
    Monotone.IsHemicontinuous (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) := by
  intro u hu v hv w
  -- Abbreviations.
  set μBar : (Fin d → ℝ) → ℝ := ⇑u.1 with hμBar_def
  set μ : (Fin d → ℝ) → ℝ := ⇑v.1 with hμ_def
  set ῡ : (Fin d → ℝ) → ℝ := ⇑u.2.1 with hῡ_def
  set υ : (Fin d → ℝ) → ℝ := ⇑v.2.1 with hυ_def
  set Dῡ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(u.2.2 i) with hDῡ_def
  set Dυ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v.2.2 i) with hDυ_def
  set η : (Fin d → ℝ) → ℝ := ⇑w.1 with hη_def
  set ν : (Fin d → ℝ) → ℝ := ⇑w.2.1 with hν_def
  set Dν : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(w.2.2 i) with hDν_def
  -- Extract the closed-cone per-segment dominator bundle for `u, v, w`.
  obtain ⟨hNonneg, g_unreg, g_gat, hg_unreg_int, hg_gat_int,
          hF_unreg_meas, hF_unreg_bound, hF_gat_meas, hF_gat_bound⟩ :=
    hData u v hu hv w
  -- Continuity of the bare-function pairing in `t`, from the closed-cone DCT
  -- lemma `Aepsi_hemicontinuous_setSegment_K0`.
  have hCts := Aepsi_hemicontinuous_setSegment_K0 (V := V) (H := H) (DpH := DpH)
                 hRegK0 γBarReal ε hγ Dυ Dῡ μ μBar υ ῡ Dν η ν
                 hNonneg g_unreg g_gat hg_unreg_int hg_gat_int
                 hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
  -- Bridge: for `t ∈ [0,1]`, the convex combination `(1-t)•u + t•v` lies in
  -- `K_Aepsi`, so `Aepsi_CLM_opK` agrees with the universal CLM there. Then
  -- transfer via primal a.e.-congruence to the `cxComb`-form.
  have h_prim_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε ((1 - t) • u + t • v) w
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i x => cxCombGrad Dυ Dῡ t i x)
            (fun x => cxComb μ μBar t x)
            (fun x => cxComb υ ῡ t x)
            Dν η ν := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1mt : (0 : ℝ) ≤ 1 - t := by linarith
    have hab : (1 - t) + t = 1 := by ring
    have hConv : (1 - t) • u + t • v ∈ K_Aepsi d βBarReal γBarReal :=
      convex_iff_add_mem.mp (K_Aepsi_convex d βBarReal γBarReal) hu hv h1mt ht0 hab
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hConv w]
    have h_m_ae : ⇑(((1 - t) • u + t • v).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxComb μ μBar t x) := by
      have h_pair : ((1 - t) • u + t • v).1 = (1 - t) • u.1 + t • v.1 := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.1) (t • v.1)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) u.1
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t v.1
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxComb, μ, μBar]
    have h_u_ae : ⇑(((1 - t) • u + t • v).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxComb υ ῡ t x) := by
      have h_pair : ((1 - t) • u + t • v).2.1 = (1 - t) • u.2.1 + t • v.2.1 := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.2.1) (t • v.2.1)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) u.2.1
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t v.2.1
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxComb, υ, ῡ]
    have h_Du_ae : ∀ i, (fun x => ⇑(((1 - t) • u + t • v).2.2 i) x)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                    (fun x => cxCombGrad Dυ Dῡ t i x) := by
      intro i
      have h_pair : ((1 - t) • u + t • v).2.2 i = (1 - t) • u.2.2 i + t • v.2.2 i := rfl
      rw [h_pair]
      have h_add := MeasureTheory.Lp.coeFn_add ((1 - t) • u.2.2 i) (t • v.2.2 i)
      have h_smul1 := MeasureTheory.Lp.coeFn_smul (1 - t) (u.2.2 i)
      have h_smul2 := MeasureTheory.Lp.coeFn_smul t (v.2.2 i)
      filter_upwards [h_add, h_smul1, h_smul2] with x hx hx1 hx2
      simp only [Pi.add_apply] at hx
      rw [hx, hx1, hx2]
      simp [cxCombGrad, Dυ, Dῡ]
    exact mfgOperatorEpsPair_primal_congr_ae V H DpH γBarReal ε Dν η ν
      h_m_ae h_u_ae h_Du_ae
  refine hCts.congr ?_
  intro t ht
  exact h_prim_eq t ht

/-- **CLM-level coercivity wrap (K_Aepsi-form, totalized).**

Same as `isCoerciveAt_Aepsi_CLM` but targeting the totalized operator
`Aepsi_CLM_opK` and consuming a K_Aepsi-indexed supplier
`auxHypsK`. The base point `v0` is required to lie in `K_Aepsi`
(both for `IsCoerciveAt`'s domain-membership condition and to
unfold `Aepsi_CLM_opK` at `v0` via the on-domain identity). -/
theorem isCoerciveAt_Aepsi_CLM_K_Aepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ)
    (v0 : palomar_AbstractLifts_XBanach d βBarReal γBarReal)
    (hv0_mem : v0 ∈ K_Aepsi d βBarReal γBarReal)
    (h_m0_ae : ⇑v0.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (1 : ℝ)))
    (h_u0_ae : ⇑v0.2.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (h_Du0_ae : ∀ i, ⇑(v0.2.2 i)
                  =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (g : palomar_AbstractLifts_XBanach d βBarReal γBarReal → ℝ)
    (C : ℝ)
    (hbound :
      ∀ᶠ v in (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        g v - C ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (hquot_tendsto :
      Filter.Tendsto (fun v => g v / ‖v‖)
        (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop) :
    Monotone.IsCoerciveAt (X := palomar_AbstractLifts_XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε)
      v0 := by
  refine ⟨hv0_mem, ?_⟩
  have h_nrm_tendsto :
      Filter.Tendsto (fun v : palomar_AbstractLifts_XBanach d βBarReal γBarReal => ‖v‖)
        (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have h_nrm_pos :
      ∀ᶠ v in (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        (0 : ℝ) < ‖v‖ := by
    refine h_nrm_tendsto.eventually_gt_atTop 0
  have hCoerc :=
    coercAepsi (V := V) (H := H) (DpH := DpH)
      γBarReal ε
      (l := (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
              ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)))
      (Du_of := fun v : palomar_AbstractLifts_XBanach d βBarReal γBarReal => fun i => ⇑(v.2.2 i))
      (m_of := fun v => ⇑v.1)
      (u_of := fun v => ⇑v.2.1)
      g (fun v => ‖v‖) C
      hbound h_nrm_pos h_nrm_tendsto hquot_tendsto
  refine hCoerc.congr' ?_
  -- We need: eventually, the abstract `Aepsi_CLM_opK`-form equals the
  -- `coercAepsi`-form. The `Aepsi_CLM_opK_apply_of_mem` rewrite
  -- requires `v ∈ K_Aepsi`; the `coerciveFilter K_Aepsi` filter
  -- (`cobounded ⊓ principal K_Aepsi`) is contained in
  -- `principal K_Aepsi`, so `v ∈ K_Aepsi` is *eventual* along the
  -- filter (in fact universally, on the principal piece).
  have h_eventually_K :
      ∀ᶠ v in (Bornology.cobounded (palomar_AbstractLifts_XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        v ∈ K_Aepsi d βBarReal γBarReal := by
    refine Filter.eventually_inf_principal.mpr ?_
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [h_eventually_K] with v hvK
  have h_subapply :
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V H DpH auxHypsK ε v
          - Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHypsK ε v0) (v - v0)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
              (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1) := by
    rw [ContinuousLinearMap.sub_apply,
        Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hvK (v - v0),
        Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hv0_mem (v - v0)]
  -- a.e.-equalities for the test triple `(v - v0)`.
  have h_eta_ae' : ⇑((v - v0).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      ((⇑v.1) - 1) := by
    have h_pair : (v - v0).1 = v.1 - v0.1 := rfl
    rw [h_pair]
    have hsub := MeasureTheory.Lp.coeFn_sub v.1 v0.1
    filter_upwards [hsub, h_m0_ae] with x hx h0
    rw [hx]
    change (⇑v.1 - ⇑v0.1) x = (⇑v.1 - 1) x
    rw [Pi.sub_apply, Pi.sub_apply, h0, Pi.one_apply]
  have h_nu_ae : ⇑((v - v0).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      ⇑v.2.1 := by
    have h_pair : (v - v0).2.1 = v.2.1 - v0.2.1 := rfl
    rw [h_pair]
    have hsub := MeasureTheory.Lp.coeFn_sub v.2.1 v0.2.1
    filter_upwards [hsub, h_u0_ae] with x hx h0
    rw [hx]
    change (⇑v.2.1 - ⇑v0.2.1) x = ⇑v.2.1 x
    rw [Pi.sub_apply, h0, sub_zero]
  have h_Dnu_ae : ∀ i, ⇑((v - v0).2.2 i)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      fun x => ⇑(v.2.2 i) x := by
    intro i
    have h_pair : (v - v0).2.2 i = v.2.2 i - v0.2.2 i := rfl
    rw [h_pair]
    have hsub := MeasureTheory.Lp.coeFn_sub (v.2.2 i) (v0.2.2 i)
    filter_upwards [hsub, h_Du0_ae i] with x hx h0
    rw [hx]
    change (⇑(v.2.2 i) - ⇑(v0.2.2 i)) x = ⇑(v.2.2 i) x
    rw [Pi.sub_apply, h0, sub_zero]
  have h_test_swap1 :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
          (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
    mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε
      (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
      h_eta_ae' h_nu_ae h_Dnu_ae
  have h_test_swap2 :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
          (fun i => ⇑((v - v0).2.2 i)) (⇑(v - v0).1) (⇑(v - v0).2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
    mfgOperatorEpsPair_test_congr_ae V H DpH γBarReal ε
      (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
      h_eta_ae' h_nu_ae h_Dnu_ae
  have h_primal_swap :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(v0.2.2 i)) (⇑v0.1) (⇑v0.2.1)
          (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
    refine mfgOperatorEpsPair_primal_congr_ae V H DpH γBarReal ε
      (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
      h_m0_ae h_u0_ae ?_
    intro i
    exact h_Du0_ae i
  change (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)) / ‖v‖
        = (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHypsK ε v
            - Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHypsK ε v0) (v - v0) / ‖v‖
  rw [h_subapply, h_test_swap1, h_test_swap2, h_primal_swap]

/-! ## K0-variant CLM lifts — REMOVED (two-domain redesign child E)

The legacy K0-form lifts `isMonotone_Aepsi_CLM_K0`,
`isHemicontinuous_Aepsi_CLM_K0`, `isCoerciveAt_Aepsi_CLM_K0` were
deleted per `infra-P4-two-domain-redesign-E-delete-K0-form-lifts`.
They consumed an unprovable `hPos`-on-`K0_Aepsi` residue (strict
positivity of the `m`-component for arbitrary K0 elements, which is
strictly stronger than `0 ≤ᵐ ⇑v.1`).

The canonical replacements are the K_Aepsi-form lifts above:
`isMonotone_Aepsi_CLM`, `isHemicontinuous_Aepsi_CLM`,
`isCoerciveAt_Aepsi_CLM`, which run their analytic content on the
strict-positivity cone `K_Aepsi` (where `0 < ⇑v.1` is part of the
domain itself). Downstream Browder–Minty consumers descend a witness
from `closure (K_Aepsi)` into `K0_Aepsi` via
`K_Aepsi_closure_subset_K0_Aepsi`. -/


end Banach
end SimplePower
end Theorems
end StationaryMFG
