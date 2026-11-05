module

public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge
public import StationaryMFG.Theorems.SimplePower.Banach.WeakPairing
public import StationaryMFG.Periodic.WeakCompactness
public import Mathlib.Analysis.LocallyConvex.WeakSpace

@[expose] public section

/-!
# Block D.1 — Pointwise extraction from a weak cluster point

This module discharges Phase-4 task `infra-P4-banach-D1-weak-to-bare`:
given a weakly-extracted cluster point
`ŵ : LpPer β̄ d × SobolevPerLp 1 γ̄ d`
produced by `exists_weak_cluster_point_pair` from the C.5 sequence,
**recover bare-function witnesses** suitable for downstream consumption
by `H4SimplePowerThinInputs` and the limit-passage block (Block E):

1. `(m, u) := (⇑ŵ.1, ⇑ŵ.2.1)` with `MemLpPer β̄ m`, `MemSobolevPer γ̄ u`.
2. A weak-derivative family `Du : Fin d → (Fin d → ℝ) → ℝ` for `u`.
3. Periodicity: `IsPeriodic m`, `IsPeriodic u`.
4. Measurability: `AEStronglyMeasurable m`, `AEStronglyMeasurable u`.

## Strategy

The bridge from a Banach-pair element to bare functions is the C.2
pattern of `Banach/AprioriDischarge.lean`: `MemLpPer` is automatic from
`MeasureTheory.Lp.memLp`, while the *coarse* product realisation
`SobolevPerLp 1 γ̄ d = Lp ℝ γ̄ μ × (Fin d → Lp ℝ γ̄ μ)` does not relate
the function and derivative components, so the weak-derivative
relation is supplied as an explicit certificate `hWeak`.

Periodicity of the bare functions `⇑ŵ.1`, `⇑ŵ.2.1` is **not** automatic
either — `Lp` representatives are only defined a.e., so pointwise
periodicity is a property of the *chosen representative*. We carry it
as two extra certificates `hPerM`, `hPerU`. Upstream, these certificates
are produced by selecting periodic representatives at each step of the
C.5 sequence and transporting periodicity through the weak limit (a
follow-up obligation handled in Block E or in the upstream chain).

## Main contents

* `WeakLimitData` — the per-limit input bundle.
* `WeakLimitData.{m, u, Du}` — bare-function projections.
* `WeakLimitData.{m_memLp, u_sobolev, m_periodic, u_periodic,
  m_aestronglyMeasurable, u_aestronglyMeasurable}` — discharges.
* `weak_limit_to_bare` — headline existential statement.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory
open StationaryMFG.Periodic
open scoped ENNReal

variable {d : ℕ}

/-! ### Per-limit input bundle

`WeakLimitData` packages the weakly-extracted cluster point `w : LpPer β̄
d × SobolevPerLp 1 γ̄ d` together with the auxiliary certificates the
*coarse* `SobolevPerLp` and `LpPer` types do not capture: the
weak-derivative relation between the function and derivative components,
and pointwise periodicity of the chosen representatives. -/

/-- **Per-limit input bundle for the bare-function extraction.**

Fields:
* `w` — the weak limit element produced by
  `exists_weak_cluster_point_pair` on the C.5 sequence.
* `hWeak` — for each coordinate `i`, the `Lp` derivative component
  `w.2.2 i` is a weak partial derivative of the `Lp` value component
  `w.2.1`. (Same certificate pattern as `BanachOutputData.hWeak`.)
* `hPerM` — pointwise periodicity of the `m`-component representative.
* `hPerU` — pointwise periodicity of the `u`-component representative. -/
structure WeakLimitData
    (βBar γBar : ℝ≥0∞) (d : ℕ) where
  /-- The weak cluster point `(m̂, û, D̂û)` in `LpPer β̄ × SobolevPerLp 1 γ̄`. -/
  w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d
  /-- Weak-derivative certificate relating `û` and `D̂û`. -/
  hWeak : ∀ i, Periodic.HasWeakDerivPer i
                (⇑w.2.1 : (Fin d → ℝ) → ℝ)
                (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
  /-- Periodicity of the `m`-component representative. -/
  hPerM : Periodic.IsPeriodic (⇑w.1 : (Fin d → ℝ) → ℝ)
  /-- Periodicity of the `u`-component representative. -/
  hPerU : Periodic.IsPeriodic (⇑w.2.1 : (Fin d → ℝ) → ℝ)

namespace WeakLimitData

variable {βBar γBar : ℝ≥0∞}

/-- Bare-function `m` extracted from the weak cluster point. -/
def m (T : WeakLimitData (d := d) βBar γBar) : (Fin d → ℝ) → ℝ :=
  ⇑T.w.1

/-- Bare-function `u` extracted from the weak cluster point. -/
def u (T : WeakLimitData (d := d) βBar γBar) : (Fin d → ℝ) → ℝ :=
  ⇑T.w.2.1

/-- Bare-function weak-derivative family `Du` extracted from the weak
cluster point. -/
def Du (T : WeakLimitData (d := d) βBar γBar) :
    Fin d → (Fin d → ℝ) → ℝ :=
  fun i x => ⇑(T.w.2.2 i) x

/-- **`m ∈ L^{β̄}_per`** — discharge from the `LpPer`-component of the
weak limit, via the C.2 bridge `memLpPer_of_lpPer`. -/
theorem m_memLp (T : WeakLimitData (d := d) βBar γBar) :
    Periodic.MemLpPer βBar T.m :=
  memLpPer_of_lpPer (d := d) T.w.1

/-- **`u ∈ W^{1,γ̄}_per`** — discharge from the `SobolevPerLp 1`-component
of the weak limit, via the C.2 bridge `memSobolevPer_of_sobolevPerLp`. -/
theorem u_sobolev (T : WeakLimitData (d := d) βBar γBar) :
    Periodic.MemSobolevPer γBar T.u :=
  memSobolevPer_of_sobolevPerLp (d := d) T.w.2 T.hWeak

/-- **`IsPeriodic m`** — direct projection of `hPerM`. -/
theorem m_periodic (T : WeakLimitData (d := d) βBar γBar) :
    Periodic.IsPeriodic T.m :=
  T.hPerM

/-- **`IsPeriodic u`** — direct projection of `hPerU`. -/
theorem u_periodic (T : WeakLimitData (d := d) βBar γBar) :
    Periodic.IsPeriodic T.u :=
  T.hPerU

/-- **`AEStronglyMeasurable m`** — from `MemLpPer.aestronglyMeasurable`. -/
theorem m_aestronglyMeasurable (T : WeakLimitData (d := d) βBar γBar) :
    AEStronglyMeasurable T.m
      (MeasureTheory.Measure.restrict volume (UnitCube d)) :=
  T.m_memLp.aestronglyMeasurable

/-- **`AEStronglyMeasurable u`** — from `MemLpPer.aestronglyMeasurable`. -/
theorem u_aestronglyMeasurable (T : WeakLimitData (d := d) βBar γBar) :
    AEStronglyMeasurable T.u
      (MeasureTheory.Measure.restrict volume (UnitCube d)) :=
  T.u_sobolev.1.aestronglyMeasurable

end WeakLimitData

/-! ### Headline existence statement -/

/-- **Pointwise extraction from a weak cluster point.**

Given a `WeakLimitData` bundle (the weak limit `w` plus the
weak-derivative and periodicity certificates), recover the bare-function
witnesses `(m, u, Du)` together with:
* `MemLpPer β̄ m`, `MemSobolevPer γ̄ u`,
* periodicity `IsPeriodic m`, `IsPeriodic u`,
* a.e.-strong measurability of both components against the
  cube-restricted volume.

This is the entry point for downstream Block E (limit passage) and the
final closure of `H4SimplePowerThinInputs`. -/
theorem weak_limit_to_bare
    {βBar γBar : ℝ≥0∞}
    (T : WeakLimitData (d := d) βBar γBar) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Periodic.MemLpPer βBar m
        ∧ Periodic.MemSobolevPer γBar u
        ∧ Periodic.IsPeriodic m
        ∧ Periodic.IsPeriodic u
        ∧ AEStronglyMeasurable m
            (MeasureTheory.Measure.restrict volume (UnitCube d))
        ∧ AEStronglyMeasurable u
            (MeasureTheory.Measure.restrict volume (UnitCube d))
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i)) := by
  refine ⟨T.m, T.u, T.Du, T.m_memLp, T.u_sobolev, T.m_periodic,
          T.u_periodic, T.m_aestronglyMeasurable,
          T.u_aestronglyMeasurable, ?_⟩
  intro i
  exact T.hWeak i

/-! ### Sanity-check unit test

Exercise `weak_limit_to_bare` on the trivial weak limit `w := 0`. The
zero element of `LpPer β̄ d × SobolevPerLp 1 γ̄ d` projects to the
a.e.-zero bare functions `⇑(0 : Lp …)`. Periodicity certificates come
from transporting `IsPeriodic.zero` along the a.e.-equality
`⇑(0 : Lp …) =ᵐ 0` — but since pointwise periodicity needs a literal
*pointwise* identity, we instead route through the existence form on
the literal constant zero function, witnessed via `m := fun _ => 0` and
`u := fun _ => 0` directly. -/

example {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Periodic.MemLpPer βBar m
        ∧ Periodic.MemSobolevPer γBar u
        ∧ Periodic.IsPeriodic m
        ∧ Periodic.IsPeriodic u
        ∧ AEStronglyMeasurable m
            (MeasureTheory.Measure.restrict volume (UnitCube d))
        ∧ AEStronglyMeasurable u
            (MeasureTheory.Measure.restrict volume (UnitCube d))
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i)) := by
  -- Constant-zero witnesses, sidestepping representative-choice issues
  -- by working at the bare-function level directly.
  haveI : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
            (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  refine ⟨(fun _ => (0 : ℝ)), (fun _ => (0 : ℝ)),
          (fun _ _ => (0 : ℝ)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `MemLpPer βBar 0` from `memLp_const 0`.
    exact MemLp.toMemLpPer (memLp_const (0 : ℝ))
  · -- `MemSobolevPer γBar 0` via the smooth zero witness.
    have h_smooth : Periodic.MemSobolevPer (d := d) γBar
                      ((0 : Periodic.SmoothPeriodic d) :
                        (Fin d → ℝ) → ℝ) :=
      Periodic.MemSobolevPer.of_smoothPeriodic γBar 0
    have h_eq : ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
                  = (fun _ => (0 : ℝ)) := by
      funext _; rfl
    rw [h_eq] at h_smooth
    exact h_smooth
  · exact Periodic.IsPeriodic.const (0 : ℝ)
  · exact Periodic.IsPeriodic.const (0 : ℝ)
  · exact aestronglyMeasurable_const
  · exact aestronglyMeasurable_const
  · -- Weak-derivative `HasWeakDerivPer i 0 0` from the smooth zero
    -- witness `(0 : SmoothPeriodic d)`.
    intro i
    have h_smooth : Periodic.MemSobolevPer (d := d) γBar
                      ((0 : Periodic.SmoothPeriodic d) :
                        (Fin d → ℝ) → ℝ) :=
      Periodic.MemSobolevPer.of_smoothPeriodic γBar 0
    have h_eq : ((0 : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
                  = (fun _ => (0 : ℝ)) := by
      funext _; rfl
    -- Extract a weak-derivative family for the zero function.
    rcases h_smooth.2 with ⟨g, hg⟩
    -- `g i` is some weak derivative of `((0 : SmoothPeriodic d) : ...)`,
    -- hence (after rewriting through `h_eq`) of `fun _ => 0`. We need
    -- `HasWeakDerivPer i (fun _ => 0) (fun _ => 0)`, i.e. that the
    -- constant zero function has zero as a weak derivative.
    -- Use `HasWeakDerivPer.congr_ae` or build from scratch via the
    -- definition of `HasWeakDerivPer` on the smooth zero function.
    -- Direct route: smooth zero has `partialDeriv i 0 = 0` weakly,
    -- which is exactly what we need.
    have h_zero_weak :
        Periodic.HasWeakDerivPer i ((0 : Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)
          ((Periodic.SmoothPeriodic.partialDeriv i
              (0 : Periodic.SmoothPeriodic d)) :
            (Fin d → ℝ) → ℝ) :=
      Periodic.HasWeakDerivPer.of_contDiff i 0
    -- Both sides are pointwise the constant zero; rewrite.
    have h_pd_eq : ((Periodic.SmoothPeriodic.partialDeriv i
                      (0 : Periodic.SmoothPeriodic d)) :
                    (Fin d → ℝ) → ℝ) = (fun _ => (0 : ℝ)) := by
      funext _
      simp [Periodic.SmoothPeriodic.partialDeriv]
    rw [h_eq, h_pd_eq] at h_zero_weak
    exact h_zero_weak

/-! ### Block D.2 — `m ≥ 0` propagates to the weak limit (Mazur)

This section discharges Phase-4 task `infra-P4-banach-D2-cone-closed`:
the non-negative cone in `LpPer βBar d` is convex and norm-closed,
hence — by Mazur's theorem (`Convex.toWeakSpace_closure`) — also
sequentially weakly closed. Consequently the constraint `m_n ≥ 0 a.e.`
along the C.5 sequence persists in the weak limit extracted in D.1.

The substantive content is the Mathlib chain
`Lp` convergence ⇒ convergence in measure ⇒ a.e. along a subsequence,
which we use to lift bare-function pointwise non-negativity to
`Lp`-quotient norm closedness.
-/

open Filter Topology

/-- **The non-negative cone in `LpPer βBar d`.**

`nonNegConeLpPer βBar d := {v | 0 ≤ ⇑v a.e.}` is the set of
`Lp`-quotient elements whose chosen representative is non-negative
almost everywhere on the unit cube. -/
def nonNegConeLpPer (βBar : ℝ≥0∞) (d : ℕ) : Set (Periodic.LpPer βBar d) :=
  {v | 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] (⇑v : (Fin d → ℝ) → ℝ)}

/-- Membership unfolding for `nonNegConeLpPer`. -/
lemma mem_nonNegConeLpPer_iff {βBar : ℝ≥0∞} {v : Periodic.LpPer βBar d} :
    v ∈ nonNegConeLpPer βBar d ↔
      0 ≤ᵐ[Measure.restrict volume (UnitCube d)] (⇑v : (Fin d → ℝ) → ℝ) :=
  Iff.rfl

/-- **Convexity of the non-negative cone in `LpPer βBar d`.**

A convex combination of two `Lp`-quotient elements with non-negative
representatives has a non-negative representative (a.e.). -/
theorem nonNegConeLpPer_convex {βBar : ℝ≥0∞} [Fact (1 ≤ βBar)] :
    Convex ℝ (nonNegConeLpPer βBar d) := by
  intro v₁ hv₁ v₂ hv₂ a b ha hb _hab
  -- Goal: `a • v₁ + b • v₂ ∈ nonNegConeLpPer βBar d`,
  -- i.e. `0 ≤ ⇑(a • v₁ + b • v₂)` a.e.
  change 0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
        (⇑(a • v₁ + b • v₂) : (Fin d → ℝ) → ℝ)
  have h_add :
      ⇑(a • v₁ + b • v₂) =ᵐ[Measure.restrict volume (UnitCube d)]
        ⇑(a • v₁) + ⇑(b • v₂) :=
    MeasureTheory.Lp.coeFn_add (a • v₁) (b • v₂)
  have h2 :
      ⇑(a • v₁) =ᵐ[Measure.restrict volume (UnitCube d)] a • ⇑v₁ :=
    MeasureTheory.Lp.coeFn_smul a v₁
  have h3 :
      ⇑(b • v₂) =ᵐ[Measure.restrict volume (UnitCube d)] b • ⇑v₂ :=
    MeasureTheory.Lp.coeFn_smul b v₂
  filter_upwards [h_add, h2, h3, hv₁, hv₂] with x hxa hx2 hx3 hxv₁ hxv₂
  -- `hxa : ⇑(a • v₁ + b • v₂) x = (⇑(a • v₁) + ⇑(b • v₂)) x`.
  -- `hx2 : ⇑(a • v₁) x = (a • ⇑v₁) x`, `hx3 : ⇑(b • v₂) x = (b • ⇑v₂) x`.
  rw [hxa]
  change 0 ≤ ⇑(a • v₁) x + ⇑(b • v₂) x
  rw [hx2, hx3]
  change 0 ≤ a • ⇑v₁ x + b • ⇑v₂ x
  have ha₁ : 0 ≤ a • (⇑v₁ : (Fin d → ℝ) → ℝ) x := by
    have : 0 ≤ a * (⇑v₁ : (Fin d → ℝ) → ℝ) x := mul_nonneg ha hxv₁
    simpa [smul_eq_mul] using this
  have hb₂ : 0 ≤ b • (⇑v₂ : (Fin d → ℝ) → ℝ) x := by
    have : 0 ≤ b * (⇑v₂ : (Fin d → ℝ) → ℝ) x := mul_nonneg hb hxv₂
    simpa [smul_eq_mul] using this
  exact add_nonneg ha₁ hb₂

/-- **Norm-closedness of the non-negative cone in `LpPer βBar d`.**

If `v_n → v` in the `Lp`-norm and each `v_n` has a non-negative
representative a.e., then so does `v`.

The proof routes `Lp` convergence through convergence in measure
(`MeasureTheory.tendstoInMeasure_of_tendsto_Lp`) and extracts an
a.e.-convergent subsequence; pointwise non-negativity is preserved
along the subsequence, hence in the limit. The argument is the
`LpPer`-quotient analogue of `K_isClosed` in
`Theorems/SimplePower/Regularized.lean`.

-- Adapted from the bare-function `K_isClosed` argument, lifted to the
-- `Lp` quotient via `tendstoInMeasure_of_tendsto_Lp`. -/
theorem nonNegConeLpPer_isClosed {βBar : ℝ≥0∞} [Fact (1 ≤ βBar)] :
    IsClosed (nonNegConeLpPer βBar d) := by
  -- Use the metric-space fact `IsSeqClosed → IsClosed` (`Lp` is metric,
  -- hence first-countable, hence sequential).
  refine IsSeqClosed.isClosed ?_
  intro v_n v hmem hconv
  -- Convergence in `Lp` ⇒ convergence in measure on the unit cube.
  have hInMeas :
      MeasureTheory.TendstoInMeasure
        (Measure.restrict volume (UnitCube d)) (fun n => ⇑(v_n n))
        atTop (⇑v : (Fin d → ℝ) → ℝ) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hconv
  -- Extract an a.e.-convergent subsequence.
  obtain ⟨ns, _hns_mono, hae⟩ := hInMeas.exists_seq_tendsto_ae
  -- Each `v_(ns i)` has a non-negative representative a.e.
  have hpos_seq :
      ∀ i, 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] (⇑(v_n (ns i)) : _) :=
    fun i => hmem (ns i)
  have hpos_all :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, 0 ≤ (⇑(v_n (ns i)) : (Fin d → ℝ) → ℝ) x :=
    (MeasureTheory.ae_all_iff).2 hpos_seq
  -- Conclude `0 ≤ ⇑v x` a.e. via the limit `(v_(ns i)) x → v x`.
  filter_upwards [hpos_all, hae] with x hxpos hxlim
  exact ge_of_tendsto' hxlim hxpos

/-- **Sequential weak closedness of the non-negative cone** (Mazur).

Apply Mathlib's `Convex.toWeakSpace_closure`: the weak closure of a
convex set equals the image of its norm closure. Combined with
`nonNegConeLpPer_isClosed`, this yields that the cone is closed in the
weak topology of `LpPer βBar d`, hence sequentially closed.

The statement is phrased on `WeakSpace ℝ (LpPer βBar d)` — the natural
target topology of `toWeakSpace ℝ _`. -/
theorem nonNegConeLpPer_isSeqClosedW {βBar : ℝ≥0∞} [Fact (1 ≤ βBar)] :
    IsSeqClosed
      ((toWeakSpace ℝ (Periodic.LpPer βBar d)) ''
        (nonNegConeLpPer βBar d)) := by
  -- Strategy: show the image is closed in `WeakSpace ℝ _`, then take
  -- `IsClosed.isSeqClosed`.
  have h_conv : Convex ℝ (nonNegConeLpPer βBar d) := nonNegConeLpPer_convex
  have h_closed : IsClosed (nonNegConeLpPer βBar d) := nonNegConeLpPer_isClosed
  -- Mazur: `(toWeakSpace ℝ _) '' closure s = closure ((toWeakSpace ℝ _) '' s)`.
  have hMazur :
      (toWeakSpace ℝ (Periodic.LpPer βBar d)) ''
          (closure (nonNegConeLpPer βBar d))
        = closure ((toWeakSpace ℝ (Periodic.LpPer βBar d)) ''
            (nonNegConeLpPer βBar d)) :=
    h_conv.toWeakSpace_closure ℝ
  -- Closed ⇒ closure = self.
  rw [h_closed.closure_eq] at hMazur
  -- `hMazur` now reads `(toWeakSpace …) '' s = closure ((toWeakSpace …) '' s)`.
  -- Hence the image is its own closure in `WeakSpace ℝ _`.
  have h_img_closed :
      IsClosed
        ((toWeakSpace ℝ (Periodic.LpPer βBar d)) ''
          (nonNegConeLpPer βBar d)) := by
    rw [hMazur]
    exact isClosed_closure
  exact h_img_closed.isSeqClosed

/-- **`m ≥ 0` propagates to the weak limit** (Phase-4 Block D.2 headline).

Given a sequence `v_k : ℕ → LpPer βBar d` whose images
`toWeakSpace ℝ _ (v_k k)` converge weakly to `toWeakSpace ℝ _ v` and
each `v_k k` has a non-negative representative a.e., the limit `v`
also has a non-negative representative a.e.

This is the sequential incarnation of "Mazur ⇒ the non-negative cone
is weakly closed" used by `exists_weak_cluster_point_pair`. -/
theorem m_nonneg_weak_limit
    {βBar : ℝ≥0∞} [Fact (1 ≤ βBar)]
    {v_k : ℕ → Periodic.LpPer βBar d} {v : Periodic.LpPer βBar d}
    (hmem : ∀ k, 0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
                  (⇑(v_k k) : (Fin d → ℝ) → ℝ))
    (hconv :
      Tendsto (fun k => (toWeakSpace ℝ (Periodic.LpPer βBar d)) (v_k k))
        atTop (𝓝 ((toWeakSpace ℝ (Periodic.LpPer βBar d)) v))) :
    0 ≤ᵐ[Measure.restrict volume (UnitCube d)] (⇑v : (Fin d → ℝ) → ℝ) := by
  -- Apply sequential weak closedness of the cone's image.
  have hSeq :
      IsSeqClosed
        ((toWeakSpace ℝ (Periodic.LpPer βBar d)) ''
          (nonNegConeLpPer βBar d)) :=
    nonNegConeLpPer_isSeqClosedW
  have hmem_img : ∀ k,
      (toWeakSpace ℝ (Periodic.LpPer βBar d)) (v_k k) ∈
        (toWeakSpace ℝ (Periodic.LpPer βBar d)) '' (nonNegConeLpPer βBar d) :=
    fun k => ⟨v_k k, hmem k, rfl⟩
  have hv_img :
      (toWeakSpace ℝ (Periodic.LpPer βBar d)) v ∈
        (toWeakSpace ℝ (Periodic.LpPer βBar d)) '' (nonNegConeLpPer βBar d) :=
    hSeq hmem_img hconv
  -- Extract: there exists `w ∈ cone` with `toWeakSpace ℝ _ w = toWeakSpace ℝ _ v`.
  obtain ⟨w, hw_mem, hw_eq⟩ := hv_img
  -- `toWeakSpace ℝ _` is injective (it's a `LinearEquiv` to a type synonym),
  -- so `w = v`.
  have hwv : w = v := (toWeakSpace ℝ (Periodic.LpPer βBar d)).injective hw_eq
  rw [hwv] at hw_mem
  exact hw_mem

/-! #### Sanity-check unit test for Block D.2

Exercise `m_nonneg_weak_limit` on the trivial constant-zero sequence.
Each `v_k k = 0` has the a.e.-zero representative, hence
`0 ≤ ⇑0 = 0` a.e. — so the cone membership holds. The constant sequence
trivially converges to its constant value. -/

example {βBar : ℝ≥0∞} [Fact (1 ≤ βBar)] :
    0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
      (⇑(0 : Periodic.LpPer βBar d) : (Fin d → ℝ) → ℝ) := by
  refine m_nonneg_weak_limit (v_k := fun _ => (0 : Periodic.LpPer βBar d))
    (v := (0 : Periodic.LpPer βBar d)) ?_ ?_
  · intro _k
    -- `⇑(0 : LpPer βBar d) =ᵐ 0`, so `0 ≤ ⇑0` a.e.
    filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ βBar
      (Measure.restrict volume (UnitCube d))] with x hx
    rw [hx]
  · -- Constant sequence converges to its constant value.
    exact tendsto_const_nhds

/-! ### Block D.3 — Smooth-tester convergence from `WeakSpace`-tendsto

This section converts an abstract `WeakSpace ℝ (LpPer βBar d)`-typed
weak convergence to the concrete smooth-periodic integral-tester
convergence
`∀ ψ : SmoothPeriodic d, ∫ v_n · ψ → ∫ w · ψ`,
and the analogous product-space variants on each component of
`LpPer βBar d × SobolevPerLp 1 γBar d`.

The key technical ingredients are:
* `WeakBilin.tendsto_iff_forall_eval_tendsto` (specialised at every
  `Λ : LpPer βBar d →L[ℝ] ℝ`),
* the canonical `hoelderPairing` integral CLM from `WeakPairing.lean`,
* `MemSobolevPer.of_smoothPeriodic` to certify
  `MemLpPer βBar' (ψ : (Fin d → ℝ) → ℝ)` for any smooth periodic `ψ`,
* `MemLp.coeFn_toLp` to transport the integral back to its original
  `(ψ : (Fin d → ℝ) → ℝ)`-form.

The product-space corollaries compose the single-component bridge with
`ContinuousLinearMap.fst`, `ContinuousLinearMap.snd`, and
`ContinuousLinearMap.proj`. -/

/-- **Smooth-tester convergence from `WeakSpace`-tendsto** (single
`LpPer`-component).

If `v_n → w` in `WeakSpace ℝ (LpPer βBar d)` and `(βBar, βBar')` is an
`ENNReal.HolderConjugate` pair with both exponents finite, then the
integral pairing against any smooth periodic test function converges:
`∫_{[0,1]^d} v_n x · ψ x dx → ∫_{[0,1]^d} w x · ψ x dx`. -/
theorem tendsto_smoothTester_of_banachWeak_lpPer
    {βBar βBar' : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ βBar')]
    (_hpq : ENNReal.HolderConjugate βBar βBar')
    (_hβBar_ne_top : βBar ≠ ∞)
    (v_n : ℕ → Periodic.LpPer βBar d) (w : Periodic.LpPer βBar d)
    (h : Tendsto
            (fun n => toWeakSpace ℝ (Periodic.LpPer βBar d) (v_n n))
            atTop
            (𝓝 (toWeakSpace ℝ (Periodic.LpPer βBar d) w))) :
    ∀ ψ : Periodic.SmoothPeriodic d,
      Tendsto
        (fun n => Periodic.periodicIntegral
          (fun x => (⇑(v_n n)) x *
              (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (Periodic.periodicIntegral
          (fun x => (⇑w) x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
  -- The injectivity argument from `WeakPairing.lean` re-derived here:
  -- `(topDualPairing ℝ E).flip` is injective via `SeparatingDual`.
  have h_inj :
      Function.Injective
        ⇑(topDualPairing ℝ (Periodic.LpPer βBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : (Periodic.LpPer βBar d →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  -- Universal-Λ form of `h`.
  have hΛ_conv : ∀ Λ : Periodic.LpPer βBar d →L[ℝ] ℝ,
      Tendsto (fun n => Λ (v_n n)) atTop (𝓝 (Λ w)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ (Periodic.LpPer βBar d)).flip)
      h_inj).mp h Λ
    simpa using! hh
  -- Specialise at the canonical `hoelderPairing` for each `ψ`.
  intro ψ
  -- Step 1: `ψ` is in `L^{βBar'}_per` (smooth periodic ⇒ MemLpPer for any p).
  have hψ_lp : Periodic.MemLpPer βBar' ((ψ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic βBar' ψ).1
  -- Step 2: build the canonical CLM Λ_ψ via `hoelderPairing`.
  -- We need the `ENNReal.HolderConjugate` instance routed through
  -- `ENNReal.ofReal` of the real exponents — but here we already have
  -- it directly on `βBar, βBar'`. Use `mulCLM.lpPairing` directly.
  set μ : Measure (Fin d → ℝ) :=
    Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)
  haveI hHC' : ENNReal.HolderConjugate βBar βBar' := _hpq
  -- The integral-pairing CLM directly via `lpPairing`:
  -- `Λψ : LpPer βBar d →L[ℝ] ℝ`, `Λψ G = ∫ G x · ψ x ∂μ`.
  let Λψ : Periodic.LpPer βBar d →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (μ := μ) βBar βBar').flip (Periodic.MemLpPer.toLp hψ_lp)
  have hΛψ_apply : ∀ G : Periodic.LpPer βBar d,
      Λψ G = ∫ x, (G x) * ((ψ : (Fin d → ℝ) → ℝ) x) ∂μ := by
    intro G
    change ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
            (μ := μ) βBar βBar').flip
            (Periodic.MemLpPer.toLp hψ_lp) G
            = ∫ x, (G x) * ((ψ : (Fin d → ℝ) → ℝ) x) ∂μ
    rw [ContinuousLinearMap.flip_apply]
    have h := ContinuousLinearMap.lpPairing_eq_integral
      (μ := μ) (p := βBar) (q := βBar')
      (B := ContinuousLinearMap.mul ℝ ℝ) G
      (Periodic.MemLpPer.toLp hψ_lp)
    -- `h : (mul.lpPairing μ βBar βBar') G (toLp ψ)
    --      = ∫ x, mul (G x) ((toLp ψ) x) ∂μ`.
    -- Rewrite via the a.e.-equality `⇑(toLp ψ) =ᵐ ψ`.
    rw [h]
    apply integral_congr_ae
    have h_ae :
        ⇑(Periodic.MemLpPer.toLp hψ_lp) =ᵐ[μ]
          (ψ : (Fin d → ℝ) → ℝ) :=
      MemLp.coeFn_toLp hψ_lp
    filter_upwards [h_ae] with x hx
    -- `mulCLM (G x) (...) = G x * (...)`; rewrite via `hx`.
    change (G x) * (⇑(Periodic.MemLpPer.toLp hψ_lp) x)
        = (G x) * ((ψ : (Fin d → ℝ) → ℝ) x)
    rw [hx]
  -- Step 3: apply the universal-Λ tendsto at `Λψ`.
  have h_eval : Tendsto (fun n => Λψ (v_n n)) atTop (𝓝 (Λψ w)) :=
    hΛ_conv Λψ
  -- Step 4: rewrite both sides via `hΛψ_apply` and `periodicIntegral`.
  have h_rhs :
      Λψ w = Periodic.periodicIntegral
        (fun x => (⇑w) x * (ψ : (Fin d → ℝ) → ℝ) x) := by
    rw [hΛψ_apply]
    rfl
  have h_lhs : ∀ n,
      Λψ (v_n n) = Periodic.periodicIntegral
        (fun x => (⇑(v_n n)) x * (ψ : (Fin d → ℝ) → ℝ) x) := by
    intro n
    rw [hΛψ_apply]
    rfl
  -- Transport `h_eval`.
  rw [h_rhs] at h_eval
  have h_eq : (fun n => Λψ (v_n n))
      = (fun n => Periodic.periodicIntegral
          (fun x => (⇑(v_n n)) x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
    funext n; exact h_lhs n
  rw [h_eq] at h_eval
  exact h_eval

/-! #### Product-space corollaries

For the assembly target `LpPer βBar d × SobolevPerLp 1 γBar d`, we need
the smooth-tester convergence on each factor. We obtain it by composing
the single-component bridge with the natural projections
`fst`, `snd ∘ fst` (the `Lp`-value component of `SobolevPerLp 1`), and
`(proj i) ∘ snd ∘ snd` (the `i`-th gradient component). These are
continuous linear maps, and continuous-linear images preserve weak
convergence. -/

/-- **Smooth-tester convergence on the `LpPer βBar`-factor of a
product weak limit.**

If a sequence in `LpPer βBar d × SobolevPerLp 1 γBar d` converges
weakly to `(w₁, w₂)` (in `WeakSpace`), then the integral pairing of
the first factor against any smooth periodic test function converges. -/
theorem tendsto_smoothTester_of_banachWeak_pair_fst
    {βBar βBar' γBar : ℝ≥0∞}
    [Fact (1 ≤ βBar)] [Fact (1 ≤ βBar')] [Fact (1 ≤ γBar)]
    (hpq : ENNReal.HolderConjugate βBar βBar')
    (hβBar_ne_top : βBar ≠ ∞)
    (z_n : ℕ → Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (z : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (h : Tendsto
            (fun n => toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
              (z_n n))
            atTop
            (𝓝 (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) z))) :
    ∀ ψ : Periodic.SmoothPeriodic d,
      Tendsto
        (fun n => Periodic.periodicIntegral
          (fun x => (⇑(z_n n).1) x * (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (Periodic.periodicIntegral
          (fun x => (⇑z.1) x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
  -- The "fst" CLM on the product.
  set fst_clm : (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                  →L[ℝ] Periodic.LpPer βBar d :=
    ContinuousLinearMap.fst ℝ _ _
  -- Compose `h` with `WeakSpace.map fst_clm` to get a `WeakSpace`-tendsto
  -- on `LpPer βBar d`. Equivalently: extract the universal-Λ form
  -- directly via the `Λ ∘ fst_clm` substitution.
  refine tendsto_smoothTester_of_banachWeak_lpPer (βBar' := βBar')
    hpq hβBar_ne_top (fun n => (z_n n).1) z.1 ?_
  -- The `WeakSpace`-tendsto for the `fst` component.
  have h_inj_prod :
      Function.Injective
        ⇑(topDualPairing ℝ
            (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : ((Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                  →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  have h_inj :
      Function.Injective
        ⇑(topDualPairing ℝ (Periodic.LpPer βBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : (Periodic.LpPer βBar d →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  -- Universal-Λ form on the product.
  have hΛ_prod : ∀ Λ : (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                          →L[ℝ] ℝ,
      Tendsto (fun n => Λ (z_n n)) atTop (𝓝 (Λ z)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip)
      h_inj_prod).mp h Λ
    simpa using! hh
  -- Reassemble for the `fst` factor using `.mpr` of the iff.
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := (topDualPairing ℝ (Periodic.LpPer βBar d)).flip)
        h_inj).mpr ?_
  intro Λ
  -- The goal at this point reads `Tendsto (fun n => topDualPairing.flip … Λ) …`.
  -- Equivalently `Tendsto (fun n => Λ ((z_n n).1)) atTop (𝓝 (Λ z.1))`.
  have h_compose : Tendsto (fun n => Λ ((z_n n).1)) atTop (𝓝 (Λ (z.1))) := by
    have := hΛ_prod (Λ.comp fst_clm)
    simpa [fst_clm] using this
  simpa using! h_compose

/-- **Smooth-tester convergence on the `SobolevPerLp`-value factor of
a product weak limit.**

The "value" component of a `SobolevPerLp 1 γBar d` element is its
first projection (an `Lp ℝ γBar μ` element). This corollary supplies
the smooth-tester convergence on that value factor. -/
theorem tendsto_smoothTester_of_banachWeak_pair_snd_val
    {βBar γBar γBar' : ℝ≥0∞}
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] [Fact (1 ≤ γBar')]
    (hpq : ENNReal.HolderConjugate γBar γBar')
    (hγBar_ne_top : γBar ≠ ∞)
    (z_n : ℕ → Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (z : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (h : Tendsto
            (fun n => toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
              (z_n n))
            atTop
            (𝓝 (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) z))) :
    ∀ ψ : Periodic.SmoothPeriodic d,
      Tendsto
        (fun n => Periodic.periodicIntegral
          (fun x => (⇑(z_n n).2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (Periodic.periodicIntegral
          (fun x => (⇑z.2.1) x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
  -- The "snd ∘ fst" CLM on the product, picking the value-component
  -- of the SobolevPerLp factor.
  set proj_clm : (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                  →L[ℝ] Periodic.LpPer γBar d :=
    (ContinuousLinearMap.fst ℝ (Periodic.LpPer γBar d)
        (Fin d → Periodic.LpPer γBar d)).comp
      (ContinuousLinearMap.snd ℝ _ _)
  -- Reduce to the single-component bridge after constructing the
  -- pushed-forward weak tendsto.
  refine tendsto_smoothTester_of_banachWeak_lpPer (βBar' := γBar')
    hpq hγBar_ne_top (fun n => (z_n n).2.1) z.2.1 ?_
  -- Build the universal-Λ form on the value-component via composition.
  have h_inj_prod :
      Function.Injective
        ⇑(topDualPairing ℝ
            (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : ((Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                  →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  have h_inj :
      Function.Injective
        ⇑(topDualPairing ℝ (Periodic.LpPer γBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : (Periodic.LpPer γBar d →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  have hΛ_prod : ∀ Λ : (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                          →L[ℝ] ℝ,
      Tendsto (fun n => Λ (z_n n)) atTop (𝓝 (Λ z)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip)
      h_inj_prod).mp h Λ
    simpa using! hh
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := (topDualPairing ℝ (Periodic.LpPer γBar d)).flip)
        h_inj).mpr ?_
  intro Λ
  have h_compose :
      Tendsto (fun n => Λ ((z_n n).2.1)) atTop (𝓝 (Λ (z.2.1))) := by
    have := hΛ_prod (Λ.comp proj_clm)
    simpa [proj_clm] using this
  simpa using! h_compose

/-- **Smooth-tester convergence on the `i`-th gradient component of a
product weak limit.**

Composing with `(proj i) ∘ snd ∘ snd` (the `i`-th coordinate of the
gradient family inside `SobolevPerLp 1 γBar d`) reduces to the single
`LpPer γBar d` bridge. -/
theorem tendsto_smoothTester_of_banachWeak_pair_snd_grad
    {βBar γBar γBar' : ℝ≥0∞}
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] [Fact (1 ≤ γBar')]
    (hpq : ENNReal.HolderConjugate γBar γBar')
    (hγBar_ne_top : γBar ≠ ∞)
    (z_n : ℕ → Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (z : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (h : Tendsto
            (fun n => toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
              (z_n n))
            atTop
            (𝓝 (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) z)))
    (i : Fin d) :
    ∀ ψ : Periodic.SmoothPeriodic d,
      Tendsto
        (fun n => Periodic.periodicIntegral
          (fun x => (⇑((z_n n).2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (Periodic.periodicIntegral
          (fun x => (⇑(z.2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
  -- The `i`-th gradient projection CLM.
  set grad_clm : (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                  →L[ℝ] Periodic.LpPer γBar d :=
    (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => Periodic.LpPer γBar d) i).comp
      ((ContinuousLinearMap.snd ℝ (Periodic.LpPer γBar d)
          (Fin d → Periodic.LpPer γBar d)).comp
        (ContinuousLinearMap.snd ℝ _ _))
  refine tendsto_smoothTester_of_banachWeak_lpPer (βBar' := γBar')
    hpq hγBar_ne_top (fun n => (z_n n).2.2 i) (z.2.2 i) ?_
  have h_inj_prod :
      Function.Injective
        ⇑(topDualPairing ℝ
            (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : ((Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                  →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  have h_inj :
      Function.Injective
        ⇑(topDualPairing ℝ (Periodic.LpPer γBar d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : (Periodic.LpPer γBar d →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  have hΛ_prod : ∀ Λ : (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
                          →L[ℝ] ℝ,
      Tendsto (fun n => Λ (z_n n)) atTop (𝓝 (Λ z)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).flip)
      h_inj_prod).mp h Λ
    simpa using! hh
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := (topDualPairing ℝ (Periodic.LpPer γBar d)).flip)
        h_inj).mpr ?_
  intro Λ
  have h_compose :
      Tendsto (fun n => Λ ((z_n n).2.2 i)) atTop (𝓝 (Λ (z.2.2 i))) := by
    have := hΛ_prod (Λ.comp grad_clm)
    simpa [grad_clm] using this
  simpa using! h_compose

/-! #### Sanity-check unit test for Block D.3

Exercise `tendsto_smoothTester_of_banachWeak_lpPer` on the constant
sequence `v_n := w` at the calibration `βBar = 2`. Constant-sequence
weak convergence is `tendsto_const_nhds`; the conclusion is then
`tendsto_const_nhds` for each integral pairing. -/

example (w : Periodic.LpPer (2 : ℝ≥0∞) d) :
    ∀ ψ : Periodic.SmoothPeriodic d,
      Tendsto
        (fun (_ : ℕ) => Periodic.periodicIntegral
          (fun x => (⇑w) x * (ψ : (Fin d → ℝ) → ℝ) x))
        atTop
        (𝓝 (Periodic.periodicIntegral
          (fun x => (⇑w) x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
  -- Hölder conjugate of `2` is `2`.
  have hpq : ENNReal.HolderConjugate (2 : ℝ≥0∞) (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
          rw [ENNReal.ofReal_ofNat]]
    exact (Real.HolderConjugate.two_two).ennrealOfReal
  refine tendsto_smoothTester_of_banachWeak_lpPer (βBar := (2 : ℝ≥0∞))
    (βBar' := (2 : ℝ≥0∞)) hpq (by simp) (fun _ => w) w ?_
  exact tendsto_const_nhds

end Banach
end SimplePower
end Theorems
end StationaryMFG
