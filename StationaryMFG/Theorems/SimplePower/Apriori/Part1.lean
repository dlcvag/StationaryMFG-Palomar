module

public import StationaryMFG.Theorems.SimplePower.StrongIsStrong
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Periodic.SobolevPoincare
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# A priori bounds — upper bound on `∫ u_ε` (paper eq. `eq:uepsiabove`)

This module formalizes part of `thm:apriori-simple.power.growth`
(`Source/FGU-monotone_revised.tex`, lines 1190–1270).

## Paper statement (line 1228, eq. `eq:uepsiabove`)

For `(m_ε, u_ε)` satisfying the strong VI of Proposition `thm:strongAepsi`,
```
∫_{𝕋^d} u_ε dx ≤ ∫_{𝕋^d} (|V| + C·(m_ε^{β̄−1} + 1)) dx.
```

## Paper proof (line 1225)

Integrate the HJB inequality `eq:HJleq0`
```
u_ε(x) + H(x, Du_ε(x), m_ε(x)) − V(x) ≤ 0
```
(from `lem:strong.is.strong`(a), part (a)) over the cube, and bound
`-H(x, p, m) ≤ C·(m^{β̄−1} + 1)` from `(eq:assH.lower.simple)` after dropping
the favorable term `‖p‖^α / C ≥ 0`.

## Lean encoding

The exponent `h.β` of `HypothesisPowerGrowth` matches the paper's `β = β̄ − 1`.
We package the pointwise bound `-H(x, p, m) ≤ h.C·(m^h.β + 1)` as a private
helper `negH_upper_bound_ae` derived directly from `h.lower`. Combined with
the HJB inequality (taken as a hypothesis here, since its production from
the strong VI is the content of `lem_strong_is_strong_HJB_ineq`), we get
the pointwise bound `u(x) ≤ |V x| + h.C·(m x ^ h.β + 1)` a.e. on the cube,
and `setIntegral_mono_ae_restrict` integrates it.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory Set Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Pointwise upper bound on `−H` from `(eq:assH.lower.simple)` -/

/-- From `h : HypothesisPowerGrowth H DpH`, the lower bound on `H` rearranged:
`−H(x, p, m) ≤ h.C · (m^h.β + 1)` for a.e. `x ∈ 𝕋^d` and all `m > 0`, `p`. The
`‖p‖^h.α / h.C` term is dropped using `‖p‖^h.α ≥ 0`.

This is the auxiliary bound used in the paper at line 1225 to control the
integrand of the HJB inequality. -/
private theorem negH_upper_bound_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → -H x p m ≤ h.C * (m ^ h.β + 1) := by
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  filter_upwards [h.lower] with x hx p m hm
  have hb := hx p m hm
  -- hb : H x p m ≥ ‖p‖^h.α / h.C - h.C * (m^h.β + 1)
  -- Drop the nonnegative term ‖p‖^h.α / h.C ≥ 0.
  have hp_nonneg : (0 : ℝ) ≤ ‖p‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hC_pos : 0 < h.C := h.hC
  have hquot_nonneg : (0 : ℝ) ≤ ‖p‖ ^ h.α / h.C := div_nonneg hp_nonneg hC_pos.le
  linarith

/-! ## Boundary extension at `m = 0` (HMpos-0)

The strict-`m > 0` bounds `negH_upper_bound_ae` and `h.lower` are extended
to `0 ≤ m` by combining the existing `m > 0` content with the paper-faithful
right-continuity bridge `H_rc0_of_hHat0` at `m = 0⁺`. The pattern mirrors
`H_abs_bound_nonneg_of_hHat0` (`Hamiltonian/Estimates.lean:2061`).

These two helpers (`negH_upper_bound_ae_nonneg`, `H_lower_bound_ae_nonneg`)
are inputs to the migration of the active `_int_aePeriodic` chain from
strict-positivity to non-negativity (`paperHMposAuth` drain, 2026-05-11). -/

/-- **HMpos-0 (boundary upper bound).** Extends `negH_upper_bound_ae` to
`0 ≤ m` using the paper-faithful Hat0 riders.

The strict-`m > 0` case is direct from `h.lower`. The boundary `m = 0`
case is recovered by passing the bound through the right-continuous
limit `H x p s → H x p 0` as `s → 0⁺` (paper Lemma `(a:Hat0)`,
recorded as `H_rc0_of_hHat0`). -/
private theorem negH_upper_bound_ae_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m → -H x p m ≤ h.C * (m ^ h.β + 1) := by
  have hC := h.hC
  have hβ := h.hβ
  have hαpos : 0 < h.α := lt_trans one_pos h.hα
  have hRC := H_rc0_of_hHat0 hHat0 hFin hAgree
  filter_upwards [h.lower, hRC] with x hxL hxRC
  intro p m hm_nn
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · -- Case `m > 0`: drop the nonneg `‖p‖^α/C` from `hxL`.
    have hb := hxL p m hm_pos
    have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    have hquot_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α / h.C := div_nonneg hp_nn hC.le
    linarith
  · -- Case `m = 0`: route through real-valued tendsto + limit-of-inequality.
    subst hm_eq
    have hLim : Filter.Tendsto (fun s : ℝ => H x p s)
        (𝓝[>] (0 : ℝ)) (𝓝 (H x p 0)) := hxRC p
    -- Tendsto for `-H x p ·`.
    have hLimNeg : Filter.Tendsto (fun s : ℝ => -H x p s)
        (𝓝[>] (0 : ℝ)) (𝓝 (-H x p 0)) := hLim.neg
    -- RHS `R(s) := h.C * (s^β + 1)`, continuous, → `h.C * (0^β + 1) = h.C`.
    set R : ℝ → ℝ := fun s => h.C * (s ^ h.β + 1) with hR_def
    have hR_cont : Continuous R := by
      have h1 : Continuous (fun s : ℝ => s ^ h.β) :=
        Real.continuous_rpow_const hβ.le
      exact continuous_const.mul (h1.add continuous_const)
    have hR_lim : Filter.Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) :=
      hR_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hR_at_zero : R 0 = h.C := by
      simp [hR_def, Real.zero_rpow hβ.ne']
    -- For `s > 0`, `-H x p s ≤ R s` from `hxL`.
    have hEv : ∀ᶠ s in 𝓝[>] (0 : ℝ), -H x p s ≤ R s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hb := hxL p s hs
      have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
      have hquot_nn : (0 : ℝ) ≤ ‖p‖ ^ h.α / h.C := div_nonneg hp_nn hC.le
      have : -H x p s ≤ h.C * (s ^ h.β + 1) := by linarith
      simpa [hR_def] using this
    have hNeg0 : -H x p 0 ≤ h.C := by
      have := le_of_tendsto_of_tendsto hLimNeg hR_lim hEv
      simpa [hR_at_zero] using this
    -- Goal: `-H x p 0 ≤ h.C * ((0 : ℝ)^h.β + 1) = h.C`.
    have h0β_eq : ((0 : ℝ)) ^ h.β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β_eq]
    linarith

/-- **HMpos-0 (boundary lower bound).** Extends `h.lower` to `0 ≤ m`
using the paper-faithful Hat0 riders.

The strict-`m > 0` case is direct from `h.lower`. The boundary `m = 0`
case is recovered by passing the inequality through the right-continuous
limit `H x p s → H x p 0` as `s → 0⁺` (paper Lemma `(a:Hat0)`,
recorded as `H_rc0_of_hHat0`). -/
private theorem H_lower_bound_ae_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m →
        ‖p‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x p m := by
  have hC := h.hC
  have hβ := h.hβ
  have hRC := H_rc0_of_hHat0 hHat0 hFin hAgree
  filter_upwards [h.lower, hRC] with x hxL hxRC
  intro p m hm_nn
  rcases hm_nn.lt_or_eq with hm_pos | hm_eq
  · -- Case `m > 0`: direct from `hxL`.
    exact hxL p m hm_pos
  · -- Case `m = 0`: route through real-valued tendsto + limit-of-inequality.
    subst hm_eq
    have hLim : Filter.Tendsto (fun s : ℝ => H x p s)
        (𝓝[>] (0 : ℝ)) (𝓝 (H x p 0)) := hxRC p
    -- LHS `L(s) := ‖p‖^α/C - C(s^β + 1)`, continuous, → `‖p‖^α/C - C` at 0.
    set L : ℝ → ℝ := fun s => ‖p‖ ^ h.α / h.C - h.C * (s ^ h.β + 1) with hL_def
    have hL_cont : Continuous L := by
      have h1 : Continuous (fun s : ℝ => s ^ h.β) :=
        Real.continuous_rpow_const hβ.le
      exact continuous_const.sub
        (continuous_const.mul (h1.add continuous_const))
    have hL_lim : Filter.Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (L 0)) :=
      hL_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h0β_eq : ((0 : ℝ)) ^ h.β = 0 := Real.zero_rpow hβ.ne'
    have hL_at_zero : L 0 = ‖p‖ ^ h.α / h.C - h.C := by
      simp [hL_def, h0β_eq]
    have hEv : ∀ᶠ s in 𝓝[>] (0 : ℝ), L s ≤ H x p s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa [hL_def] using hxL p s hs
    have hLower0 : ‖p‖ ^ h.α / h.C - h.C ≤ H x p 0 := by
      have := le_of_tendsto_of_tendsto hL_lim hLim hEv
      simpa [hL_at_zero] using this
    -- Goal: `‖p‖^α/h.C - h.C * (0^β + 1) ≤ H x p 0`.
    -- Since `0^β = 0`, RHS coefficient is `h.C * 1 = h.C`.
    rw [h0β_eq]
    linarith

/-! ## A priori upper bound on `∫ u` from the HJB inequality

Phrased as a standalone theorem taking the HJB pointwise inequality as a
hypothesis (the proof of which is `lem_strong_is_strong_HJB_ineq` from the
sibling module `StrongIsStrong.lean`). This separation lets the consumer
apply the bound under whichever variational-inequality form is available.
-/

/-- **Paper eq. `eq:uepsiabove`** (`Source/FGU-monotone_revised.tex`, line 1228).

Under the simple-power-growth hypothesis `h : HypothesisPowerGrowth H DpH`,
together with:

* the HJB pointwise inequality `u(x) + H(x, Du(x), m(x)) − V(x) ≤ 0` a.e.
  (the conclusion of `lem_strong_is_strong_HJB_ineq`);
* a.e. positivity of the density `m`;
* integrability of `u` and of the right-hand side `|V| + C(m^β + 1)` on the
  cube,

we have
```
∫ x in UnitCube d, u x ∂volume
  ≤ ∫ x in UnitCube d, |V x| + h.C * (m x ^ h.β + 1) ∂volume.
```

Proof: combine `negH_upper_bound_ae` (rewriting `−H ≤ C(m^β+1)`) with the
HJB inequality `u ≤ V − H` to get the pointwise bound
`u ≤ V + C(m^β+1) ≤ |V| + C(m^β+1)`, then integrate via
`setIntegral_mono_ae_restrict`. -/
theorem apriori_uepsi_above
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hu : Integrable u (volume.restrict (UnitCube d)))
    (hRHS : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
        ∂(volume : Measure (Fin d → ℝ)) := by
  -- Step 1. Pointwise: `u(x) ≤ |V x| + h.C * (m x ^ h.β + 1)` a.e.
  have hpointwise :
      u ≤ᵐ[volume.restrict (UnitCube d)]
        fun x => |V x| + h.C * (m x ^ h.β + 1) := by
    filter_upwards [hHJB, hMpos, negH_upper_bound_ae (d := d) h]
      with x hx hxm hxnegH
    -- hx : u x + H x (Du · x) (m x) - V x ≤ 0,
    --      i.e. u x ≤ V x - H x (Du · x) (m x).
    -- hxnegH p m hm : -H x p m ≤ h.C * (m^h.β + 1).
    -- hxm : 0 < m x.
    have hH_bnd : -H x (fun i => Du i x) (m x) ≤ h.C * (m x ^ h.β + 1) :=
      hxnegH (fun i => Du i x) (m x) hxm
    -- u x ≤ V x - H x (Du · x) (m x) = V x + (-H x …)
    have hu_le : u x ≤ V x - H x (fun i => Du i x) (m x) := by linarith
    have hVabs : V x ≤ |V x| := le_abs_self _
    -- Combine: u x ≤ V x + (−H ...) ≤ |V x| + h.C * (m x ^ h.β + 1).
    have : u x ≤ V x + h.C * (m x ^ h.β + 1) := by linarith
    linarith
  -- Step 2. Integrate.
  exact setIntegral_mono_ae_restrict hu hRHS hpointwise

/-- **HMpos-1.** Nonneg variant of `apriori_uepsi_above` (paper eq.
`eq:uepsiabove`).

Identical to `apriori_uepsi_above` but requires only `0 ≤ m` a.e.
instead of `0 < m`. The boundary `m = 0` case is recovered by routing
the `-H ≤ C(m^β + 1)` bound through `negH_upper_bound_ae_nonneg`
(paper Hat0 boundary helper), which uses the paper-faithful right-
continuity rider `H_rc0_of_hHat0` at `m = 0⁺`. -/
theorem apriori_uepsi_above_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu : Integrable u (volume.restrict (UnitCube d)))
    (hRHS : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
        ∂(volume : Measure (Fin d → ℝ)) := by
  -- Step 1. Pointwise: `u(x) ≤ |V x| + h.C * (m x ^ h.β + 1)` a.e.
  have hpointwise :
      u ≤ᵐ[volume.restrict (UnitCube d)]
        fun x => |V x| + h.C * (m x ^ h.β + 1) := by
    filter_upwards [hHJB, hMnn,
        negH_upper_bound_ae_nonneg (d := d) h hHat0 hFin hAgree]
      with x hx hxm hxnegH
    have hH_bnd : -H x (fun i => Du i x) (m x) ≤ h.C * (m x ^ h.β + 1) :=
      hxnegH (fun i => Du i x) (m x) hxm
    have hu_le : u x ≤ V x - H x (fun i => Du i x) (m x) := by linarith
    have hVabs : V x ≤ |V x| := le_abs_self _
    have : u x ≤ V x + h.C * (m x ^ h.β + 1) := by linarith
    linarith
  -- Step 2. Integrate.
  exact setIntegral_mono_ae_restrict hu hRHS hpointwise

/-! ## Sanity check -/

/-- **Unit test**: in the trivial setting `H = 0, DpH = 0, V = 0, u = 0,
m ≡ 1, Du = 0` (with `h` an arbitrary `HypothesisPowerGrowth` for the trivial
Hamiltonian), `apriori_uepsi_above` applies — both integrability hypotheses
are discharged for the constant integrands. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
              (fun _ : Fin d → ℝ => (0 : ℝ)) x +
                  H x (fun i => Du i x) ((fun _ : Fin d → ℝ => (1 : ℝ)) x) -
                  (fun _ : Fin d → ℝ => (0 : ℝ)) x ≤ 0) :
    ∫ x in UnitCube d, (fun _ : Fin d → ℝ => (0 : ℝ)) x
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
        (|(fun _ : Fin d → ℝ => (0 : ℝ)) x| +
            h.C * ((fun _ : Fin d → ℝ => (1 : ℝ)) x ^ h.β + 1))
        ∂(volume : Measure (Fin d → ℝ)) := by
  -- The hypothesis `0 < m x = 1` is trivial; both integrability hypotheses
  -- reduce to integrability of constants on the unit cube (a finite measure
  -- after restriction since the cube has finite volume).
  refine apriori_uepsi_above (h := h.toCongestionAprioriPowerData) (V := fun _ => (0 : ℝ)) (Du := Du)
      (m := fun _ => (1 : ℝ)) (u := fun _ => (0 : ℝ)) hHJB ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun _ => (zero_lt_one : (0 : ℝ) < 1))
  · -- `Integrable 0 (volume.restrict (UnitCube d))`: the zero function is integrable.
    exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall (fun _ => rfl))
  · -- `Integrable (fun _ => |0| + h.C * (1^β + 1)) (volume.restrict (UnitCube d))`.
    -- This is integrable on the cube because `volume.restrict (UnitCube d)` is finite.
    have hfin : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
    have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hfin⟩
    exact integrable_const _

/-! ## A priori lower bound on `∫ u_ε` (paper eq. `eq:uepsibelow`, line 1218) -/

/-- **Hölder conjugate pair `(β+1, (β+1)/β)`** for `β > 0`.

This is the standard Young exponent pair used in the absorption step of paper
eq. `eq:uepsibelow`. (A private copy of the same helper is used in
`Coercivity.lean`; we re-derive it locally to keep this module self-contained.)
-/
private lemma holderConjugate_betaPlusOne_apriori {β : ℝ} (hβ : 0 < β) :
    Real.HolderConjugate (β + 1) ((β + 1) / β) := by
  rw [Real.holderConjugate_iff]
  refine ⟨by linarith, ?_⟩
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  field_simp
  ring

/-! ## Hölder lemma `∫|V|·m ≤ (∫|V|^β̄')^{1/β̄'} · (∫m^β̄)^{1/β̄}`

The integral substitution that replaces the pointwise Vbound step by a paper-shape
`L^{β̄}`/`L^{β̄'}` Hölder estimate, with conjugate pair
`(β̄, β̄') = (β + 1, (β + 1)/β)`.

This lemma is the key analytic substitute for the pointwise inequality
`−V x · m x ≥ −max(Vbound, 0) · m x` used in the closed-form Apriori chain.

The numeric content follows directly from
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`. The hypotheses are stated
in terms of bare `Integrable`/`AEStronglyMeasurable`, which we package into
`MemLp` form via `integrable_norm_rpow_iff`.
-/

/-- **Hölder lemma on the unit cube** for the conjugate pair
`(β̄, β̄') = (β + 1, (β + 1)/β)`.

Given `β > 0`, a non-negative density `m` (a.e.), and integrability of
`|V|^{β̄'}` and `m^{β̄}` over the cube, we have
```
∫ |V x| * m x ≤ (∫ |V x|^{β̄'})^{1/β̄'} * (∫ m x^{β̄})^{1/β̄}.
```
With `β̄ = β + 1` and `β̄' = (β + 1)/β`, this rewrites the right-hand side as
`(∫ |V|^{(β+1)/β})^{β/(β+1)} * (∫ m^{β+1})^{1/(β+1)}`. -/
theorem holder_Vm_betaBar
    {β : ℝ} (hβ : 0 < β)
    (V m : (Fin d → ℝ) → ℝ)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
                  (volume.restrict (UnitCube d)))
    (hMβ_int : Integrable (fun x => m x ^ (β + 1))
                  (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, |V x| * m x
        ∂(volume : Measure (Fin d → ℝ))
      ≤ (∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
            ∂(volume : Measure (Fin d → ℝ))) ^ (β / (β + 1))
        * (∫ x in UnitCube d, m x ^ (β + 1)
            ∂(volume : Measure (Fin d → ℝ))) ^ (1 / (β + 1)) := by
  -- Conjugate pair `p = (β+1)/β`, `q = β+1`. Apply Hölder to `f := |V|`,
  -- `g := m`. Both are non-negative.
  set p : ℝ := (β + 1) / β with hp_def
  set q : ℝ := β + 1 with hq_def
  have hβp1_pos : 0 < β + 1 := by linarith
  have hp_pos : 0 < p := by
    have := div_pos hβp1_pos hβ
    simpa [hp_def] using this
  have hq_pos : 0 < q := by simpa [hq_def] using hβp1_pos
  -- The conjugate pair statement (`p` and `q` swapped wrt
  -- `holderConjugate_betaPlusOne_apriori`).
  have hpq : Real.HolderConjugate p q := by
    have h := (holderConjugate_betaPlusOne_apriori hβ).symm
    -- h : Real.HolderConjugate ((β + 1) / β) (β + 1)
    simpa [hp_def, hq_def] using h
  -- Cast `1/p = β/(β+1)` and `1/q = 1/(β+1)`.
  have h_inv_p : (1 : ℝ) / p = β / (β + 1) := by
    have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ
    have hβp1ne : (β + 1 : ℝ) ≠ 0 := ne_of_gt hβp1_pos
    show (1 : ℝ) / ((β + 1) / β) = β / (β + 1)
    field_simp
  have h_inv_q : (1 : ℝ) / q = 1 / (β + 1) := by
    show (1 : ℝ) / (β + 1) = 1 / (β + 1)
    rfl
  -- Package the integrability hypotheses into `MemLp` form.
  -- `|V|` is AEStronglyMeasurable, since `|V x| = ‖V x‖` for real-valued `V`.
  have hAbsV_meas : AEStronglyMeasurable (fun x => |V x|)
      (volume.restrict (UnitCube d)) := by
    have hN : AEStronglyMeasurable (fun x => ‖V x‖)
        (volume.restrict (UnitCube d)) := hV_meas.norm
    refine hN.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact (Real.norm_eq_abs (V x))
  -- `MemLp |V| (ENNReal.ofReal p)` from `Integrable (|V|^p)`.
  -- Use `integrable_norm_rpow_iff` with `f := |V|`, since `‖|V x|‖ = |V x|`.
  have h_pne : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hp_pos
  have h_pne_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have h_qne : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hq_pos
  have h_qne_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have h_pToReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hp_pos.le
  have h_qToReal : (ENNReal.ofReal q).toReal = q :=
    ENNReal.toReal_ofReal hq_pos.le
  -- Build `MemLp |V| (ENNReal.ofReal p)` from `Integrable (fun x => |V x|^p)`.
  have hAbsV_mem :
      MemLp (fun x => |V x|) (ENNReal.ofReal p)
        (volume.restrict (UnitCube d)) := by
    rw [← integrable_norm_rpow_iff hAbsV_meas h_pne h_pne_top]
    -- Goal: Integrable (fun x => ‖|V x|‖ ^ (ofReal p).toReal).
    have hcongr : ∀ x, ‖|V x|‖ ^ (ENNReal.ofReal p).toReal
        = |V x| ^ p := by
      intro x
      rw [Real.norm_of_nonneg (abs_nonneg _), h_pToReal]
    refine hVβp_int.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact (hcongr x).symm
  -- Build `MemLp m (ENNReal.ofReal q)` from `Integrable (fun x => m x^q)` and
  -- a.e. non-negativity of `m`.
  have hm_mem :
      MemLp m (ENNReal.ofReal q) (volume.restrict (UnitCube d)) := by
    rw [← integrable_norm_rpow_iff hm_meas h_qne h_qne_top]
    -- Goal: Integrable (fun x => ‖m x‖ ^ (ofReal q).toReal).
    refine hMβ_int.congr ?_
    filter_upwards [hm_nn] with x hx
    rw [Real.norm_of_nonneg hx, h_qToReal]
  -- Apply the Hölder integral inequality.
  have hHolder :
      ∫ x in UnitCube d, |V x| * m x ∂(volume : Measure (Fin d → ℝ))
        ≤ (∫ x in UnitCube d, |V x| ^ p
              ∂(volume : Measure (Fin d → ℝ))) ^ (1 / p)
          * (∫ x in UnitCube d, m x ^ q
              ∂(volume : Measure (Fin d → ℝ))) ^ (1 / q) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (UnitCube d)) hpq
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      hm_nn hAbsV_mem hm_mem
  -- Rewrite `1/p = β/(β+1)` and `1/q = 1/(β+1)` in the conclusion.
  -- (`p` and `q` are kept as `set`-definitions, so the goal already
  -- mentions them via the abbreviations.)
  rw [h_inv_p, h_inv_q] at hHolder
  exact hHolder

/-- **Pointwise Lagrangian-multiplied lower bound** on the integrand of the
identity at paper line 1212. Multiplying `lagrangian_lower_bound`
(`(m^β)/C − C ≤ DpH·p − H`) through by `m ≥ 0`, we get
```
m·(m^β)/C − C·m ≤ m·(DpH·p − H),
```
i.e. `m^{β+1}/C − C·m ≤ m·(−H + DpH·p)` since `m·m^β = m^{β+1}` for `m > 0`.
-/
private theorem mul_lagrangian_lower_bound_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {β C : ℝ}
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        mx ^ (β + 1) / C - C * mx
          ≤ mx * (-H x p mx + (DpH x p mx) ⬝ p) := by
  filter_upwards [h_lagr] with x hx p mx hmx
  have hL := hx p mx hmx
  have hmx_nn : 0 ≤ mx := hmx.le
  have hmul : mx * ((mx ^ β) / C - C) ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) :=
    mul_le_mul_of_nonneg_left hL hmx_nn
  -- mx * (mx^β) = mx^{β+1} for `mx > 0`.
  have hpow : mx * (mx ^ β) = mx ^ (β + 1) := by
    rw [show (β + 1 : ℝ) = 1 + β from by ring, Real.rpow_add hmx, Real.rpow_one]
  have hLHS : mx * ((mx ^ β) / C - C) = mx ^ (β + 1) / C - C * mx := by
    have hrw : mx * ((mx ^ β) / C - C) = mx * (mx ^ β) / C - mx * C := by ring
    rw [hrw, hpow]; ring
  linarith [hmul, hLHS]

/-- **HMpos-1.** Pointwise Lagrangian-multiplied lower bound extended to
`0 ≤ mx`.

The strict-`mx > 0` case multiplies `h_lagr p mx hpos` by `mx`. The
boundary `mx = 0` case is purely algebraic: both sides collapse to `0`
because `β + 1 > 0` forces `0 ^ (β + 1) = 0`. **No Hat0 riders needed**
— at `mx = 0` we never evaluate `H x p 0`, since the `mx · …` factor
zeroes it out.

This is HMpos-1 of the 5-step plan to drain `paperHMposAuth`; the
strict-positive sibling `mul_lagrangian_lower_bound_ae` is preserved
unchanged. -/
private theorem mul_lagrangian_lower_bound_ae_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p mx, 0 ≤ mx →
        mx ^ (β + 1) / C - C * mx
          ≤ mx * (-H x p mx + (DpH x p mx) ⬝ p) := by
  filter_upwards [h_lagr] with x hx p mx hmx_nn
  rcases hmx_nn.lt_or_eq with hmx_pos | hmx_eq
  · -- Case `mx > 0`: reuse the strict-positive proof.
    have hL := hx p mx hmx_pos
    have hmx_nn' : 0 ≤ mx := hmx_pos.le
    have hmul : mx * ((mx ^ β) / C - C) ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) :=
      mul_le_mul_of_nonneg_left hL hmx_nn'
    have hpow : mx * (mx ^ β) = mx ^ (β + 1) := by
      rw [show (β + 1 : ℝ) = 1 + β from by ring,
          Real.rpow_add hmx_pos, Real.rpow_one]
    have hLHS : mx * ((mx ^ β) / C - C) = mx ^ (β + 1) / C - C * mx := by
      have hrw : mx * ((mx ^ β) / C - C) = mx * (mx ^ β) / C - mx * C := by ring
      rw [hrw, hpow]; ring
    linarith [hmul, hLHS]
  · -- Case `mx = 0`: both sides collapse to `0`.
    subst hmx_eq
    -- LHS: `0 ^ (β + 1) / C - C * 0 = 0 / C - 0 = 0`.
    have hβp1_pos : 0 < β + 1 := by linarith
    have hβp1_ne : (β + 1 : ℝ) ≠ 0 := ne_of_gt hβp1_pos
    have h0pow : (0 : ℝ) ^ (β + 1) = 0 := Real.zero_rpow hβp1_ne
    -- RHS: `0 * (… ) = 0`.
    -- Goal is `0^(β+1)/C - C*0 ≤ 0 * (…)`.
    rw [h0pow]
    simp

/-- **Pointwise post-Young absorption bound**: for all `mx ≥ 0` and any `K ≥ 0`,
Young's inequality with conjugate pair `(β+1, (β+1)/β)` gives
```
K · mx ≤ mx ^ (β+1) / (β+1) + K ^ ((β+1)/β) · β / (β+1).
```
This is `Real.young_inequality_of_nonneg` applied to `(mx, K)`, after rewriting
the `b^q/q` term using `q = (β+1)/β` so that `b^q/q = K^{(β+1)/β} · β/(β+1)`. -/
private theorem young_absorb_lin_into_betaPlusOne {β : ℝ} (hβ : 0 < β)
    (K : ℝ) (hK : 0 ≤ K) (mx : ℝ) (hmx : 0 ≤ mx) :
    K * mx ≤ mx ^ (β + 1) / (β + 1) + K ^ ((β + 1) / β) * (β / (β + 1)) := by
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  have hHC : Real.HolderConjugate (β + 1) ((β + 1) / β) :=
    holderConjugate_betaPlusOne_apriori hβ
  -- Apply `Real.young_inequality_of_nonneg` to `(mx, K)`.
  -- Conclusion: `mx * K ≤ mx^{β+1}/(β+1) + K^{(β+1)/β} / ((β+1)/β)`.
  have hY : mx * K ≤ mx ^ (β + 1) / (β + 1) + K ^ ((β + 1) / β) / ((β + 1) / β) :=
    Real.young_inequality_of_nonneg hmx hK hHC
  -- Rewrite `K^{(β+1)/β} / ((β+1)/β) = K^{(β+1)/β} * β/(β+1)`.
  have hdiv : K ^ ((β + 1) / β) / ((β + 1) / β) = K ^ ((β + 1) / β) * (β / (β + 1)) := by
    field_simp
  rw [hdiv] at hY
  rw [mul_comm K mx]
  exact hY

/-! Forward declarations for the closed-form coefficient witness used
inside `apriori_uepsi_below` and downstream. The actual paper-style
docstring for `apriori_uepsi_below` is attached to the theorem itself,
below. -/

/-- **Closed-form coefficient of the `apriori_uepsi_below` lower bound.**

The witness `C'` produced by `apriori_uepsi_below` is the closed-form
expression `max (2 · h.C) ((2 · h.C + K_Y) + 1)`, where `K_Y` is the
Young residual
```
K_Y = (Vp / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1)),
   Vp  = h.C + max Vbound 0,
   lam = ((h.β + 1) / (2 · h.C)) ^ (1 / (h.β + 1)).
```
The cube-volume factor (`vol = 1`) is unfolded so the value is
manifestly closed-form in `(h.β, h.C, Vbound)`, hence ε-independent.
This `def` is the witness used by the in-line `set C' := …`
binding inside `apriori_uepsi_below`. -/
def aprioriUepsiBelowConst
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound : ℝ) : ℝ :=
  let Vp : ℝ := h.C + max Vbound 0
  let lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1))
  let K_Y : ℝ := (Vp / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1))
  max (2 * h.C) ((2 * h.C + K_Y) + 1)

/-- Strict positivity of the closed-form `apriori_uepsi_below` coefficient. -/
theorem aprioriUepsiBelowConst_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound : ℝ) :
    0 < aprioriUepsiBelowConst h Vbound := by
  unfold aprioriUepsiBelowConst
  have h2C_pos : 0 < 2 * h.C := by have := h.hC; linarith
  exact lt_of_lt_of_le h2C_pos (le_max_left _ _)

/-- Non-negativity of the closed-form `apriori_uepsi_below` coefficient. -/
theorem aprioriUepsiBelowConst_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound : ℝ) :
    0 ≤ aprioriUepsiBelowConst h Vbound :=
  (aprioriUepsiBelowConst_pos h Vbound).le

/-! ### Integral-V variant of the closed-form below-bound

The `_int` sibling consumes integral V-data
`(Vint_bound, Vβp_bound, hVint, hVβp)` instead of the pointwise
`L^∞` bound `(Vbound, hVbnd)`. The Hölder lemma `holder_Vm_betaBar`
substitutes for the pointwise step `−V·m ≥ −max(Vbound, 0)·m`.

The `Vint_bound` argument is kept on the closed-form `def` for
signature uniformity with downstream `_int` consumers; it does
not enter the closed-form constant. (`∫ m` is bounded by Hölder
against the constant `1` instead, which uses `vol(cube) = 1`.)
-/

/-- **Closed-form coefficient of the integral-V variant
`apriori_uepsi_below_closed_int`.**

The witness `C'` produced by `apriori_uepsi_below_closed_int` is
the closed-form expression `max (2 · h.C) (K_Y_int + 1)`, where
`K_Y_int` is the Young residual after Hölder absorption:
```
K_Y_int = (K_eff / lam) ^ ((β+1)/β) · (β / (β+1)),
   K_eff := h.C + Vβp_bound ^ (β/(β+1)),
   lam   := ((β+1) / (2·C)) ^ (1/(β+1)).
```
The `Vint_bound` argument is currently unused and present only for
signature parity. -/
def aprioriUepsiBelowConst_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (_Vint_bound Vβp_bound : ℝ) : ℝ :=
  let lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1))
  let K_eff : ℝ := h.C + Vβp_bound ^ (h.β / (h.β + 1))
  let K_Y_int : ℝ := (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1))
  max (2 * h.C) (K_Y_int + 1)

/-- Strict positivity of the integral-V variant constant. -/
theorem aprioriUepsiBelowConst_int_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    0 < aprioriUepsiBelowConst_int h Vint_bound Vβp_bound := by
  unfold aprioriUepsiBelowConst_int
  have h2C_pos : 0 < 2 * h.C := by have := h.hC; linarith
  exact lt_of_lt_of_le h2C_pos (le_max_left _ _)

/-- Non-negativity of the integral-V variant constant. -/
theorem aprioriUepsiBelowConst_int_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    0 ≤ aprioriUepsiBelowConst_int h Vint_bound Vβp_bound :=
  (aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound).le

/-- **Paper eq. `eq:uepsibelow`** (`Source/FGU-monotone_revised.tex`, line 1218).

Under the simple-power-growth hypothesis `h : HypothesisPowerGrowth H DpH`,
together with:

* the **Lagrangian lower bound** `(m^β)/C − C ≤ DpH·p − H` a.e. for `m > 0`
  (the conclusion of `lagrangian_lower_bound`, paper eq.
  `eq:DpHdotpminusH-estimate1`);
* the **combined identity** at paper line 1212, derived from
  `lem:strong.is.strong.b` and `.c` by testing transport at `φ = u_ε`:
  ```
  ∫ u = ∫ [m·(−H + DpH·Du) + V·m + nonneg_eps_terms] dx;
  ```
* a.e. non-negativity of `m`;
* an a.e.-bound `|V x| ≤ Vbound` (a uniform `L^∞` bound on `V`);
* a.e. non-negativity of the residual `ε`-terms `nonneg_eps_terms ≥ 0`;
* integrability hypotheses needed to apply `setIntegral_mono_ae_restrict`,

there exists a constant `C' > 0` (depending only on `h.C`, `h.β`, `Vbound`)
such that
```
(1/C') · ∫_{UnitCube d} m(x)^{β+1} dx − C' ≤ ∫_{UnitCube d} u(x) dx.
```

With the paper's exponent `β̄ = β + 1` and the convention
`‖m‖_{L^{β̄}}^{β̄} = ∫ m^{β̄}` (for `m ≥ 0`), this is exactly
`(1/C') · ‖m‖_{L^{β̄}}^{β̄} − C' ≤ ∫ u`.

The proof binds `C'` to the closed-form witness
`aprioriUepsiBelowConst h Vbound` defined above; see that `def`'s
docstring for the explicit formula.

The pointwise integrand bound (combined into a single inequality before
integrating) is
```
m^{β+1}/(2C) − C''  ≤  m·(−H + DpH·Du) + V·m + nonneg_eps_terms,
```
obtained from steps:
1. Lagrangian × `m`: `m^{β+1}/C − C·m ≤ m·(−H + DpH·Du)`.
2. `V·m ≥ −Vbound·m` (when `Vbound ≥ 0`; we coerce by replacing
   `Vbound` with `max Vbound 0`).
3. `nonneg_eps_terms ≥ 0`.
4. Young's inequality on `(C + max Vbound 0) · m` with conjugate pair
   `(β+1, (β+1)/β)`, scaled so that the `m^{β+1}` coefficient is at most
   `1/(2C)`. -/
theorem apriori_uepsi_below_closed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConst h Vbound)
        * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConst h Vbound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  -- Constants.
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have h2C_pos : 0 < 2 * h.C := by linarith
  -- Coerced `V`-bound.
  set Vp : ℝ := h.C + max Vbound 0 with hVpdef
  have hVp_nn : 0 ≤ Vp := by
    have h1 : (0 : ℝ) ≤ max Vbound 0 := le_max_right _ _
    linarith [hC_pos.le]
  -- Young scale: `λ := (1/(2C·(β+1)))^{1/(β+1)}`. We work directly with
  -- the scaled quantities `a := λ · mx`, `b := Vp / λ`. Equivalently we
  -- show pointwise: `Vp · mx ≤ (1/(2C)) · mx^{β+1} + K_Y`, where `K_Y` is
  -- the Young residual.
  -- Use `young_absorb_lin_into_betaPlusOne` with the rescaled mass
  -- `mx' := λ * mx` and `K' := Vp / λ`, combined with `λ^{β+1} = 1/(2C·(β+1))^{-1}`.
  -- For simplicity we instead apply the unscaled Young directly to
  -- `(mx_scaled, K_scaled)`. The arithmetic is encapsulated in the
  -- `young_absorb_lin_into_betaPlusOne` helper combined with a final
  -- multiplicative rescale to bring the `m^{β+1}` coefficient to `1/(2C)`.
  --
  -- Concretely, applying `young_absorb_lin_into_betaPlusOne hβ Vp_scaled mx_scaled`
  -- with the substitution `mx ↦ λ * mx`, `Vp ↦ Vp / λ` (so `Vp_scaled · mx_scaled
  -- = Vp · mx`), gives
  --   Vp * mx ≤ (λ * mx)^{β+1}/(β+1) + (Vp/λ)^{(β+1)/β} * β/(β+1)
  --          = λ^{β+1} * mx^{β+1}/(β+1) + (Vp/λ)^{(β+1)/β} * β/(β+1).
  -- Choose `λ^{β+1}/(β+1) = 1/(2C)`, i.e. `λ^{β+1} = (β+1)/(2C)`.
  set lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1)) with hlamdef
  have hbasis_pos : 0 < (h.β + 1) / (2 * h.C) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (h.β + 1) = (h.β + 1) / (2 * h.C) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by
      field_simp
    rw [heq, Real.rpow_one]
  -- The residual constant from Young.
  set K_Y : ℝ := (Vp / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1)) with hK_Ydef
  have hK_Y_nn : 0 ≤ K_Y := by
    have h1 : 0 ≤ Vp / lam := div_nonneg hVp_nn hlam_pos.le
    have h2 : 0 ≤ (Vp / lam) ^ ((h.β + 1) / h.β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  -- Pointwise Young inequality after the scale.
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      Vp * mx ≤ (1 / (2 * h.C)) * mx ^ (h.β + 1) + K_Y := by
    intro mx hmx
    -- Apply Young to (lam * mx, Vp / lam).
    have hlammx_nn : 0 ≤ lam * mx := mul_nonneg hlam_pos.le hmx
    have hVplam_nn : 0 ≤ Vp / lam := div_nonneg hVp_nn hlam_pos.le
    have hY := young_absorb_lin_into_betaPlusOne hβ_pos (Vp / lam) hVplam_nn (lam * mx) hlammx_nn
    -- hY : (Vp / lam) * (lam * mx) ≤ (lam * mx)^{β+1}/(β+1) + (Vp/lam)^{(β+1)/β} * β/(β+1)
    -- LHS simplifies to `Vp * mx`.
    have hLHS : (Vp / lam) * (lam * mx) = Vp * mx := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    -- RHS first summand: `(lam * mx)^{β+1}/(β+1) = lam^{β+1} * mx^{β+1}/(β+1)
    -- = ((β+1)/(2C)) * mx^{β+1} / (β+1) = (1/(2C)) * mx^{β+1}`.
    have hpow_mul :
        (lam * mx) ^ (h.β + 1) = lam ^ (h.β + 1) * mx ^ (h.β + 1) :=
      Real.mul_rpow hlam_pos.le hmx
    have hR1 :
        (lam * mx) ^ (h.β + 1) / (h.β + 1)
          = (1 / (2 * h.C)) * mx ^ (h.β + 1) := by
      rw [hpow_mul, hlam_pow_p]
      have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    exact hY
  -- Pointwise integrand lower bound.
  have hpoint :
      (fun x => (1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [mul_lagrangian_lower_bound_ae (β := h.β) (C := h.C) h_lagr,
        hMpos, hVbnd, hEpsNN] with x hLag hxm hxV hxE
    -- Step 1: Lagrangian × m: `m^{β+1}/C − C·m ≤ m·(-H + DpH·Du)`.
    have hL : m x ^ (h.β + 1) / h.C - h.C * m x
                ≤ m x * (-H x (fun i => Du i x) (m x)
                          + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)) :=
      hLag (fun i => Du i x) (m x) hxm
    -- Step 2: V·m ≥ -|V|·m ≥ -max(Vbound,0)·m (using m ≥ 0).
    have hxm_nn : 0 ≤ m x := hxm.le
    have habsmle : |V x| ≤ Vbound := hxV
    have hVbound_le_max : Vbound ≤ max Vbound 0 := le_max_left _ _
    have habs_le_pos : |V x| ≤ max Vbound 0 := habsmle.trans hVbound_le_max
    have hneg_le : -V x ≤ |V x| := neg_le_abs _
    have hneg_max : -V x ≤ max Vbound 0 := hneg_le.trans habs_le_pos
    have hmaxneg : -max Vbound 0 ≤ V x := by linarith
    -- So `V x * m x ≥ -max Vbound 0 * m x`.
    have hVm_lb : -max Vbound 0 * m x ≤ V x * m x :=
      mul_le_mul_of_nonneg_right hmaxneg hxm_nn
    -- Step 3: Combine 1+2: `(1/C)·m^{β+1} − (C + max Vbound 0)·m
    --                          ≤ m·(-H + DpH·Du) + V·m`.
    have h12 :
        (1 / h.C) * m x ^ (h.β + 1) - Vp * m x
          ≤ m x * (-H x (fun i => Du i x) (m x)
                      + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x := by
      have hLrw : m x ^ (h.β + 1) / h.C - h.C * m x
                    = (1 / h.C) * m x ^ (h.β + 1) - h.C * m x := by ring
      rw [hLrw] at hL
      have : Vp * m x = h.C * m x + max Vbound 0 * m x := by
        rw [hVpdef]; ring
      linarith [hL, hVm_lb]
    -- Step 4: Young: `Vp · m ≤ (1/(2C))·m^{β+1} + K_Y`.
    have hY := hYoung_pt (m x) hxm_nn
    -- So `(1/C)·m^{β+1} - Vp·m ≥ (1/(2C))·m^{β+1} - K_Y`.
    have hY' : (1 / h.C) * m x ^ (h.β + 1) - Vp * m x
                  ≥ (1 / (2 * h.C)) * m x ^ (h.β + 1) - K_Y := by
      have h_aux : (1 / h.C) - (1 / (2 * h.C)) = (1 / (2 * h.C)) := by
        field_simp; ring
      have hrpow_nn : 0 ≤ m x ^ (h.β + 1) := Real.rpow_nonneg hxm_nn _
      have hcoeff_pos : 0 ≤ (1 / (2 * h.C)) := by positivity
      -- (1/C) * m^{β+1} = (1/(2C)) * m^{β+1} + (1/(2C)) * m^{β+1}.
      have hsplit : (1 / h.C) * m x ^ (h.β + 1)
                      = (1 / (2 * h.C)) * m x ^ (h.β + 1)
                        + (1 / (2 * h.C)) * m x ^ (h.β + 1) := by
        have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
        have hCne : h.C ≠ 0 := ne_of_gt hC_pos
        field_simp; ring
      linarith [hY, hsplit]
    -- Step 5: Add `epsTerms ≥ 0`: drop it on the LHS.
    -- Combine: (1/(2C))·m^{β+1} - K_Y - 2C ≤ (1/C)·m^{β+1} - Vp·m - 2C
    --   ≤ ... ≤ m·(-H + DpH·Du) + V·m + epsTerms.
    -- We absorb `2C` into the constant: change the LHS shape to `...- (2C + K_Y)`.
    -- Actually our target is `(1/(2C))·m^{β+1} - (2C + K_Y) ≤ m·(...) + V·m + epsTerms`.
    have hgoal :
        (1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y)
          ≤ m x * (-H x (fun i => Du i x) (m x)
                      + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x := by
      have h2C_nn : 0 ≤ 2 * h.C := h2C_pos.le
      linarith [hY', h12, hxE]
    exact hgoal
  -- Step 6: Integrate the pointwise inequality.
  -- Need integrability of LHS. The LHS is `(1/(2C))·m^{β+1} - (2C + K_Y)` which is
  -- a constant minus a multiple of `m^{β+1}` — both integrable on the cube.
  have hLHS_int :
      Integrable (fun x => (1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        (volume.restrict (UnitCube d)) := by
    have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
    have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
    have hconst : Integrable (fun _ : Fin d → ℝ => (2 * h.C + K_Y))
                    (volume.restrict (UnitCube d)) := integrable_const _
    have hpow : Integrable (fun x => (1 / (2 * h.C)) * m x ^ (h.β + 1))
                  (volume.restrict (UnitCube d)) :=
      hLB_int.const_mul (1 / (2 * h.C))
    exact hpow.sub hconst
  -- Apply `setIntegral_mono_ae_restrict`.
  have hint_le :
      ∫ x in UnitCube d,
          ((1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_int hRHS_int hpoint
  -- Use the identity to convert the RHS into ∫ u.
  rw [← h_identity] at hint_le
  -- LHS rewriting: ∫ ((1/(2C))·m^{β+1} - (2C+K_Y))
  --   = (1/(2C)) · ∫ m^{β+1} - (2C+K_Y) · vol(cube).
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have hcube_finite_inst : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  have hLHS_eq :
      ∫ x in UnitCube d,
          ((1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / (2 * h.C))
          * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
        - (2 * h.C + K_Y) * (volume (UnitCube d)).toReal := by
    have hsub :
        ∫ x in UnitCube d,
            ((1 / (2 * h.C)) * m x ^ (h.β + 1) - (2 * h.C + K_Y))
          ∂(volume : Measure (Fin d → ℝ))
        = (∫ x in UnitCube d, (1 / (2 * h.C)) * m x ^ (h.β + 1)
            ∂(volume : Measure (Fin d → ℝ)))
          - (∫ x in UnitCube d, (2 * h.C + K_Y)
              ∂(volume : Measure (Fin d → ℝ))) := by
      rw [integral_sub (hLB_int.const_mul (1 / (2 * h.C))) (integrable_const _)]
    rw [hsub]
    congr 1
    · rw [integral_const_mul]
    · -- ∫_{cube} (2C + K_Y) dvol = (2C + K_Y) * vol(cube), and vol(cube) = 1.
      rw [MeasureTheory.integral_const]
      -- Goal: (volume.restrict (UnitCube d)).real univ • (2 * h.C + K_Y)
      --        = (2 * h.C + K_Y) * (volume (UnitCube d)).toReal
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, mul_comm]
  rw [hLHS_eq] at hint_le
  -- Define the final constant `C'` via the closed-form `def`
  -- `aprioriUepsiBelowConst h Vbound`. Pre-compute `vol = 1` so the
  -- two forms coincide on the nose.
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by
    simp [hvol_def, volume_unitCube]
  -- The closed-form witness defined in the previous section.
  set C' : ℝ := aprioriUepsiBelowConst (d := d) h Vbound with hC'def
  -- Reduce the closed-form `let`s — `aprioriUepsiBelowConst` unfolds to
  -- `max (2 * h.C) ((2 * h.C + K_Y) + 1)`.
  have hC'_unfold :
      C' = max (2 * h.C) ((2 * h.C + K_Y) + 1) := by
    show aprioriUepsiBelowConst (d := d) h Vbound = _
    -- The `let`-bound `Vp, lam, K_Y` inside `aprioriUepsiBelowConst`
    -- definitionally match the outer `set Vp, set lam, set K_Y`.
    rfl
  have hC'_pos : 0 < C' := by
    rw [hC'_unfold]
    have h1 : 0 ≤ 2 * h.C + K_Y := by linarith [h2C_pos.le, hK_Y_nn]
    have h2 : (0 : ℝ) < (2 * h.C + K_Y) + 1 := by linarith
    exact lt_of_lt_of_le h2 (le_max_right _ _)
  -- Goal now: (1/C') * ∫ m^{β+1} - C' ≤ ∫ u, with `C'` the closed-form.
  -- We have: (1/(2C)) * ∫ m^{β+1} - (2C+K_Y)*vol ≤ ∫ u (= hint_le).
  have hC'_ge_2C : 2 * h.C ≤ C' := by
    rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : (2 * h.C + K_Y) * vol ≤ C' := by
    rw [hC'_unfold, hvol_eq_one, mul_one]
    have : (2 * h.C + K_Y) ≤ (2 * h.C + K_Y) + 1 := by linarith
    exact this.trans (le_max_right _ _)
  -- ∫ m^{β+1} ≥ 0 since `m ≥ 0` a.e. on the cube.
  have hint_nn : 0 ≤ ∫ x in UnitCube d, m x ^ (h.β + 1)
                        ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  -- Coefficient comparison: 1/C' ≤ 1/(2C).
  have h_coeff : (1 / C') ≤ (1 / (2 * h.C)) := by
    apply one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  -- Hence (1/C') * ∫ m^{β+1} ≤ (1/(2C)) * ∫ m^{β+1}.
  have h_lhs_term :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ)))
        ≤ (1 / (2 * h.C)) * (∫ x in UnitCube d, m x ^ (h.β + 1)
                              ∂(volume : Measure (Fin d → ℝ))) :=
    mul_le_mul_of_nonneg_right h_coeff hint_nn
  -- And -C' ≤ -(2C + K_Y) * vol.
  have h_rhs_const : -C' ≤ -((2 * h.C + K_Y) * vol) := by linarith
  linarith [h_lhs_term, h_rhs_const, hint_le]

/-- **Paper eq. `eq:uepsibelow`** — integral-V variant.

Same conclusion as `apriori_uepsi_below_closed`, but the
hypothesis on `V` is integral-level: `∫ |V| ≤ Vint_bound` and
`∫ |V|^{β̄'} ≤ Vβp_bound` (with `β̄' = (β+1)/β`). This variant
substitutes the pointwise step `−V·m ≥ −max(Vbound, 0)·m` by the
Hölder lemma `holder_Vm_betaBar` applied at the integral level.

The witness is the closed-form `aprioriUepsiBelowConst_int h
Vint_bound Vβp_bound`. Its formula is independent of `Vint_bound`
(see the `def` for the explicit shape).

Compared to the `Vbound`-shape sibling, the integrability
hypotheses include `Integrable (fun x => |V x|^{β̄'})` and
`Integrable (fun x => |V x| * m x)`, plus AE-strong-measurability
of `V` and `m` so that `holder_Vm_betaBar` applies. -/
theorem apriori_uepsi_below_closed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConst_int h Vint_bound Vβp_bound)
        * (∫ x in UnitCube d, m x ^ (h.β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConst_int h Vint_bound Vβp_bound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  -- Constants.
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have h2C_pos : 0 < 2 * h.C := by linarith
  -- Young scale (same as the pointwise variant).
  set lam : ℝ := ((h.β + 1) / (2 * h.C)) ^ ((1 : ℝ) / (h.β + 1)) with hlamdef
  have hbasis_pos : 0 < (h.β + 1) / (2 * h.C) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (h.β + 1) = (h.β + 1) / (2 * h.C) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by
      field_simp
    rw [heq, Real.rpow_one]
  -- Effective coefficient `K_eff = h.C + Vβp_bound^{β/(β+1)}`.
  set K_eff : ℝ := h.C + Vβp_bound ^ (h.β / (h.β + 1)) with hK_eff_def
  have hVβp_pow_nn : 0 ≤ Vβp_bound ^ (h.β / (h.β + 1)) :=
    Real.rpow_nonneg hVβp_nn _
  have hK_eff_nn : 0 ≤ K_eff := by
    have : 0 ≤ h.C := hC_pos.le
    linarith
  -- The Young residual.
  set K_Y_int : ℝ := (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1))
    with hK_Y_int_def
  have hK_Y_int_nn : 0 ≤ K_Y_int := by
    have h1 : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have h2 : 0 ≤ (K_eff / lam) ^ ((h.β + 1) / h.β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  -- mEverything below builds the bound `(1/(2C)) X - K_Y_int ≤ ∫ u`,
  -- where `X := ∫ m^{β+1}`, then enlarges the residual to `C'`.
  -- Step A: Pointwise `m^{β+1}/C - C·m ≤ m·(-H + DpH·Du)` (from Lagrangian × m).
  have hlagr_mul := mul_lagrangian_lower_bound_ae (β := h.β) (C := h.C) h_lagr
  have hpointA :
      (fun x => m x ^ (h.β + 1) / h.C - h.C * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))) := by
    filter_upwards [hlagr_mul, hMpos] with x hLag hxm
    exact hLag (fun i => Du i x) (m x) hxm
  -- Integrability for both sides of `hpointA`.
  have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
  have hLB_int_div :
      Integrable (fun x => m x ^ (h.β + 1) / h.C)
        (volume.restrict (UnitCube d)) := by
    have h := hLB_int.const_mul (1 / h.C)
    refine h.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  have hM_int_const :
      Integrable (fun x => h.C * m x) (volume.restrict (UnitCube d)) :=
    hM_int.const_mul _
  have hLHS_A_int :
      Integrable (fun x => m x ^ (h.β + 1) / h.C - h.C * m x)
        (volume.restrict (UnitCube d)) := hLB_int_div.sub hM_int_const
  -- Step B: integrate the *combined* inequality
  --   `m^{β+1}/C - C·m + V·m + 0 ≤ m·(-H+DpH·Du) + V·m + epsTerms`
  -- against `hRHS_int`. Both sides are individual integrable functions.
  have hpointAfull :
      (fun x => m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [hlagr_mul, hMpos, hEpsNN] with x hLag hxm hxe
    have hL := hLag (fun i => Du i x) (m x) hxm
    -- hL : m x^{β+1}/h.C - h.C * m x ≤ m x * (-H+DpH·Du).
    linarith
  -- The LHS uses `V·m`, which we need integrable. Note `V·m` may not be integrable
  -- without absolute values, but we can write
  --   V x * m x = |V x| * m x · sign  — too messy.
  -- Better: use `|V·m| ≤ |V|·m` (since `m ≥ 0`) and conclude integrability of `V·m`.
  have hVm_int_signed : Integrable (fun x => V x * m x)
      (volume.restrict (UnitCube d)) := by
    -- Strong measurability: V·m is AEStronglyMeasurable.
    have hVm_meas : AEStronglyMeasurable (fun x => V x * m x)
        (volume.restrict (UnitCube d)) := hV_meas.mul hm_meas
    -- Bound: |V·m| ≤ |V|·m (a.e., using m ≥ 0).
    have hbound : (fun x => |V x * m x|)
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hMpos] with x hxm
      have hxm_nn : 0 ≤ m x := hxm.le
      rw [abs_mul, abs_of_nonneg hxm_nn]
    -- |V|·m is integrable, so V·m is integrable.
    refine Integrable.mono' hVm_int hVm_meas ?_
    filter_upwards [hbound] with x hb using hb
  have hLHS_full_int :
      Integrable (fun x => m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        (volume.restrict (UnitCube d)) :=
    hLHS_A_int.add hVm_int_signed
  -- Integrate `hpointAfull` against `hRHS_int`.
  have hIntStep :
      ∫ x in UnitCube d,
          (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_full_int hRHS_int hpointAfull
  -- Use the identity to convert the RHS into ∫ u.
  rw [← h_identity] at hIntStep
  -- LHS integral splits.
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Im : ℝ := ∫ x in UnitCube d, m x ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  have hIm_nn : 0 ≤ Im := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hMpos] with x hxm
    exact hxm.le
  set IVm : ℝ := ∫ x in UnitCube d, V x * m x
                  ∂(volume : Measure (Fin d → ℝ)) with hIVm_def
  set IabsVm : ℝ := ∫ x in UnitCube d, |V x| * m x
                      ∂(volume : Measure (Fin d → ℝ)) with hIabsVm_def
  have hLHS_split :
      ∫ x in UnitCube d,
          (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / h.C) * X - h.C * Im + IVm := by
    have h1 : ∫ x in UnitCube d, m x ^ (h.β + 1) / h.C
                ∂(volume : Measure (Fin d → ℝ))
              = (1 / h.C) * X := by
      have hcongr : ∀ x, m x ^ (h.β + 1) / h.C
                          = (1 / h.C) * m x ^ (h.β + 1) := by
        intro x; ring
      simp only [hcongr]
      rw [integral_const_mul]
    have h2 : ∫ x in UnitCube d, h.C * m x
                ∂(volume : Measure (Fin d → ℝ))
              = h.C * Im := by
      rw [integral_const_mul]
    have hadd :
        ∫ x in UnitCube d,
            (m x ^ (h.β + 1) / h.C - h.C * m x + V x * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (m x ^ (h.β + 1) / h.C - h.C * m x)
            ∂(volume : Measure (Fin d → ℝ))
          + ∫ x in UnitCube d, V x * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      integral_add hLHS_A_int hVm_int_signed
    have hsub :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) / h.C - h.C * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, m x ^ (h.β + 1) / h.C
              ∂(volume : Measure (Fin d → ℝ))
          - ∫ x in UnitCube d, h.C * m x
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_sub hLB_int_div hM_int_const
    rw [hadd, hsub, h1, h2]
  rw [hLHS_split] at hIntStep
  -- Lower bound: V·m ≥ -|V|·m, so IVm ≥ -IabsVm.
  have hIVm_lb : -IabsVm ≤ IVm := by
    -- ∫ V·m + ∫ |V|·m = ∫ (V·m + |V|·m) ≥ 0 since V·m + |V|·m ≥ 0
    -- (because V x ≥ -|V x|, m x ≥ 0).
    have hae : (fun x => -(V x * m x))
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hMpos] with x hxm
      have hxm_nn : 0 ≤ m x := hxm.le
      have hVneg : -V x ≤ |V x| := neg_le_abs _
      have := mul_le_mul_of_nonneg_right hVneg hxm_nn
      simpa [neg_mul] using this
    have hIneg :
        ∫ x in UnitCube d, -(V x * m x)
            ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫ x in UnitCube d, |V x| * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hVm_int_signed.neg hVm_int hae
    have hIneg' : -IVm ≤ IabsVm := by
      simpa [hIVm_def, hIabsVm_def, integral_neg] using hIneg
    linarith
  -- Hölder for ∫|V|·m.
  have hHolder :
      IabsVm ≤ Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1)) := by
    have hm_nn_ae : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x := by
      filter_upwards [hMpos] with x hx using hx.le
    have h_holder := holder_Vm_betaBar (d := d) (β := h.β) hβ_pos
        V m hm_nn_ae hV_meas hm_meas hVβp_int hLB_int
    -- h_holder : IabsVm ≤ (∫ |V|^{β̄'})^{β/(β+1)} * X^{1/(β+1)}.
    -- We need to bound (∫ |V|^{β̄'})^{β/(β+1)} ≤ Vβp_bound^{β/(β+1)}.
    have hVβp_int_nn :
        0 ≤ ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
              ∂(volume : Measure (Fin d → ℝ)) := by
      refine integral_nonneg_of_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hexp_nn : 0 ≤ h.β / (h.β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    have hMono : (∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
                    ∂(volume : Measure (Fin d → ℝ))) ^ (h.β / (h.β + 1))
                  ≤ Vβp_bound ^ (h.β / (h.β + 1)) :=
      Real.rpow_le_rpow hVβp_int_nn hVβp ((div_pos hβ_pos hβp1_pos).le)
    have hX_pow_nn : 0 ≤ X ^ (1 / (h.β + 1)) := Real.rpow_nonneg hX_nn _
    have hMul := mul_le_mul_of_nonneg_right hMono hX_pow_nn
    exact h_holder.trans hMul
  -- Hölder for ∫ m: ∫ m·1 ≤ (∫ 1^{β̄'})^{β/(β+1)} · X^{1/(β+1)} = X^{1/(β+1)}.
  have hHolder_m : Im ≤ X ^ (1 / (h.β + 1)) := by
    -- Apply holder_Vm_betaBar with V := 1.
    have h1_meas : AEStronglyMeasurable (fun _ : Fin d → ℝ => (1 : ℝ))
        (volume.restrict (UnitCube d)) := aestronglyMeasurable_const
    have h1_int : Integrable
        (fun x : Fin d → ℝ => |(1 : ℝ)| ^ ((h.β + 1) / h.β))
        (volume.restrict (UnitCube d)) := by
      have hcongr : ∀ x : Fin d → ℝ, |(1 : ℝ)| ^ ((h.β + 1) / h.β) = 1 := by
        intro _
        rw [abs_one, Real.one_rpow]
      have hconst : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
      refine hconst.congr ?_
      filter_upwards with x using (hcongr x).symm
    have hm_nn_ae : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x := by
      filter_upwards [hMpos] with x hx using hx.le
    have h_holder := holder_Vm_betaBar (d := d) (β := h.β) hβ_pos
        (fun _ => (1 : ℝ)) m hm_nn_ae h1_meas hm_meas h1_int hLB_int
    -- LHS: ∫ |1|·m = ∫ m = Im (using |1| = 1).
    have hLHS_eq :
        ∫ x in UnitCube d, |(1 : ℝ)| * m x
            ∂(volume : Measure (Fin d → ℝ))
          = Im := by
      have hcongr : ∀ x : Fin d → ℝ, |(1 : ℝ)| * m x = m x := by
        intro x; rw [abs_one, one_mul]
      simp only [hcongr, hIm_def]
    -- RHS first factor: (∫ 1^{β̄'})^{β/(β+1)} = vol^{β/(β+1)} = 1.
    have hRHS_first :
        (∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
            ∂(volume : Measure (Fin d → ℝ))) ^ (h.β / (h.β + 1)) = 1 := by
      have hint_eq :
          ∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
              ∂(volume : Measure (Fin d → ℝ))
            = 1 := by
        have : ∫ _x in UnitCube d, (1 : ℝ) ∂(volume : Measure (Fin d → ℝ))
              = 1 := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
            Set.univ_inter, volume_unitCube]
        calc ∫ x in UnitCube d, |(1 : ℝ)| ^ ((h.β + 1) / h.β)
                ∂(volume : Measure (Fin d → ℝ))
            = ∫ _x in UnitCube d, (1 : ℝ)
                ∂(volume : Measure (Fin d → ℝ)) := by
              refine integral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro x; rw [abs_one, Real.one_rpow]
          _ = 1 := this
      rw [hint_eq, Real.one_rpow]
    rw [hLHS_eq, hRHS_first, one_mul] at h_holder
    -- h_holder : Im ≤ X ^ (1/(β+1)).
    exact h_holder
  -- Combine: -h.C·Im + IVm ≥ -h.C·X^{1/(β+1)} - Vβp^{β/(β+1)}·X^{1/(β+1)}
  --                       = -K_eff·X^{1/(β+1)}.
  have hX_pow_nn : 0 ≤ X ^ (1 / (h.β + 1)) := Real.rpow_nonneg hX_nn _
  have hCm_ub : h.C * Im ≤ h.C * X ^ (1 / (h.β + 1)) :=
    mul_le_mul_of_nonneg_left hHolder_m hC_pos.le
  have hVm_lb_X : -(Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1))) ≤ IVm := by
    -- IVm ≥ -IabsVm ≥ -(Vβp^{β/(β+1)} · X^{1/(β+1)}).
    have := neg_le_neg hHolder
    linarith [hIVm_lb]
  -- So -h.C·Im + IVm ≥ -K_eff · X^{1/(β+1)}.
  have hCombined :
      -(K_eff * X ^ (1 / (h.β + 1))) ≤ -h.C * Im + IVm := by
    have hsplit : K_eff * X ^ (1 / (h.β + 1))
                    = h.C * X ^ (1 / (h.β + 1))
                      + Vβp_bound ^ (h.β / (h.β + 1)) * X ^ (1 / (h.β + 1)) := by
      rw [hK_eff_def]; ring
    have h1 : -h.C * Im ≥ -h.C * X ^ (1 / (h.β + 1)) := by
      have := hCm_ub
      linarith
    linarith [hVm_lb_X, hsplit]
  -- Step C: scaled Young absorption.
  -- Goal: K_eff * y ≤ (1/(2C)) · y^{β+1} + K_Y_int, with y := X^{1/(β+1)}.
  -- Since y^{β+1} = X.
  have hY_X : (X ^ (1 / (h.β + 1))) ^ (h.β + 1) = X := by
    rw [← Real.rpow_mul hX_nn]
    have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
    have heq : (1 : ℝ) / (h.β + 1) * (h.β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  -- Apply scaled Young to (lam · y, K_eff/lam).
  have hY_pt :
      K_eff * X ^ (1 / (h.β + 1))
        ≤ (1 / (2 * h.C)) * X + K_Y_int := by
    have hylam_nn : 0 ≤ lam * X ^ (1 / (h.β + 1)) :=
      mul_nonneg hlam_pos.le hX_pow_nn
    have hKlam_nn : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have hY := young_absorb_lin_into_betaPlusOne hβ_pos
                  (K_eff / lam) hKlam_nn (lam * X ^ (1 / (h.β + 1))) hylam_nn
    -- hY : (K_eff/lam) * (lam * y) ≤ (lam * y)^{β+1}/(β+1) + (K_eff/lam)^{(β+1)/β} * β/(β+1)
    have hLHS : (K_eff / lam) * (lam * X ^ (1 / (h.β + 1))) = K_eff * X ^ (1 / (h.β + 1)) := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    have hpow_mul :
        (lam * X ^ (1 / (h.β + 1))) ^ (h.β + 1)
          = lam ^ (h.β + 1) * (X ^ (1 / (h.β + 1))) ^ (h.β + 1) :=
      Real.mul_rpow hlam_pos.le hX_pow_nn
    have hR1 :
        (lam * X ^ (1 / (h.β + 1))) ^ (h.β + 1) / (h.β + 1)
          = (1 / (2 * h.C)) * X := by
      rw [hpow_mul, hlam_pow_p, hY_X]
      have hβp1ne : (h.β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    -- hY : K_eff * y ≤ (1/(2C))·X + (K_eff/lam)^{(β+1)/β} * (β/(β+1))
    -- The latter is K_Y_int.
    have hRY : (K_eff / lam) ^ ((h.β + 1) / h.β) * (h.β / (h.β + 1)) = K_Y_int := by
      rw [hK_Y_int_def]
    rw [hRY] at hY
    exact hY
  -- Putting it together: (1/C) X - C·Im + IVm ≤ ∫u
  --   ⟹ (1/C) X - K_eff · X^{1/(β+1)} ≤ ∫u
  --   ⟹ (1/C) X - (1/(2C)) X - K_Y_int ≤ ∫u
  --   ⟹ (1/(2C)) X - K_Y_int ≤ ∫u.
  have hChain :
      (1 / (2 * h.C)) * X - K_Y_int
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
    have h1 : (1 / h.C) * X - K_eff * X ^ (1 / (h.β + 1))
                ≤ (1 / h.C) * X - h.C * Im + IVm := by
      linarith
    have hinequalities : (1 / h.C) * X - K_eff * X ^ (1 / (h.β + 1))
                ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
      linarith [hIntStep]
    -- Combine with Young.
    have h_split : (1 / h.C) * X = (1 / (2 * h.C)) * X + (1 / (2 * h.C)) * X := by
      have h2Cne : (2 * h.C) ≠ 0 := ne_of_gt h2C_pos
      have hCne : h.C ≠ 0 := ne_of_gt hC_pos
      field_simp; ring
    linarith [hY_pt]
  -- Now bind C' := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound and rewrite.
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_unfold : C' = max (2 * h.C) (K_Y_int + 1) := by
    show aprioriUepsiBelowConst_int h Vint_bound Vβp_bound = _
    rfl
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hC'_ge_2C : 2 * h.C ≤ C' := by
    rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : K_Y_int ≤ C' := by
    rw [hC'_unfold]
    have : K_Y_int ≤ K_Y_int + 1 := by linarith
    exact this.trans (le_max_right _ _)
  -- (1/C') ≤ (1/(2C)).
  have h_coeff : (1 / C') ≤ (1 / (2 * h.C)) :=
    one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  have h_lhs_term : (1 / C') * X ≤ (1 / (2 * h.C)) * X :=
    mul_le_mul_of_nonneg_right h_coeff hX_nn
  have h_rhs_const : -C' ≤ -K_Y_int := by linarith
  linarith [h_lhs_term, h_rhs_const, hChain]

/-- **Paper eq. `eq:uepsibelow`** existential wrapper.

`apriori_uepsi_below_closed` provides the bound with the explicit
closed-form witness `aprioriUepsiBelowConst h Vbound`. This wrapper
re-emits the bound in the historical existential shape
`∃ C', 0 < C' ∧ …` for backwards compatibility with downstream
callers. -/
theorem apriori_uepsi_below
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    ∃ C' : ℝ, 0 < C' ∧
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
  ⟨aprioriUepsiBelowConst h Vbound, aprioriUepsiBelowConst_pos h Vbound,
    apriori_uepsi_below_closed (h := h) V Du m u epsTerms Vbound
      h_lagr hMpos hVbnd hEpsNN h_identity hLB_int hRHS_int⟩

/-! ### Sanity check for `apriori_uepsi_below` -/

/-- **Unit test**: `apriori_uepsi_below` applies in a trivial/abstract setting.

Given `h : HypothesisPowerGrowth H DpH`, an abstract Lagrangian lower bound,
and the matching identity/integrability hypotheses on `(V, Du, m, u, epsTerms,
Vbound)` we exhibit the conclusion.

This example simply forwards all hypotheses to the main theorem; its purpose
is to verify that the API is callable from a downstream module. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    ∃ C' : ℝ, 0 < C' ∧
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
  apriori_uepsi_below (h := h) V Du m u epsTerms Vbound
    h_lagr hMpos hVbnd hEpsNN h_identity hLB_int hRHS_int

/-! ## A priori uniform `L^{β̄}` bound on `m_ε` (paper eq. `eq:mepsi.bound`, line 1235)

Combine `apriori_uepsi_above` (eq. `eq:uepsiabove`) with `apriori_uepsi_below`
(eq. `eq:uepsibelow`) to derive a uniform-in-`ε` bound on `∫ m_ε^{β̄} = ∫ m_ε^{β+1}`
by absorbing the `m_ε^{β}`-term on the right-hand side using Young's inequality
with conjugate pair `(β̄, β̄') = (β+1, (β+1)/β)`.

The argument is:

```
(1/C') · X − C'  ≤  ∫ u  ≤  ∫|V| + h.C · ∫ m^β + h.C · vol(cube),
```
with `X := ∫ m^{β+1}`. By the *pointwise* Young-with-scale inequality
`young_absorb_pow_into_betaPlusOne` (proved below),
```
h.C · m^β  ≤  (1/(2C')) · m^{β+1} + K_Y     (pointwise, all `m ≥ 0`),
```
for some explicit constant `K_Y`. Integrating and substituting,
```
(1/C') · X − C'  ≤  ∫|V| + (1/(2C')) · X + K_Y · vol + h.C · vol,
```
so
```
(1/(2C')) · X  ≤  C' + ∫|V| + K_Y · vol + h.C · vol,
```
hence `X ≤ Cfinal` for `Cfinal := 2C' · (C' + Vint_bound + K_Y · vol + h.C · vol)`,
which depends only on `(h.C, h.β, Vint_bound, vol)` — independent of `ε`.

Note: We take `Vint_bound : ℝ` with `∫|V| ≤ Vint_bound` as a hypothesis. The
paper's hypothesis `V ∈ L^{β̄'}_per` produces such a bound by Hölder against the
constant-1 function on the unit cube of volume `1` (`‖V‖_{L¹} ≤ ‖V‖_{L^{β̄'}}`).
-/

/-- **Pointwise Young absorption from `K · m^β` into `δ · m^{β+1}`**.

For `mx ≥ 0` and `K ≥ 0`, applying Young's inequality with conjugate pair
`((β+1)/β, β+1)` to the pair `(λ · mx^β, K/λ)` we get, for any chosen
scale `λ > 0`,
```
K · mx^β  ≤  λ ^ ((β+1)/β) · (β/(β+1)) · mx^{β+1} + (K/λ)^{β+1} / (β+1).
```
The lemma below packages this in the explicit form
```
K · mx^β  ≤  λ_pow · (β/(β+1)) · mx^{β+1} + (K^{β+1} / λ_pow_q) / (β+1),
```
where `λ_pow := λ^{(β+1)/β}` is treated as the user-chosen *coefficient*
on `mx^{β+1}`. By choosing `λ_pow := δ · (β+1)/β`, the coefficient on
`mx^{β+1}` becomes `δ`, giving the absorption inequality used below. -/
private theorem young_absorb_pow_into_betaPlusOne {β : ℝ} (hβ : 0 < β)
    (K : ℝ) (hK : 0 ≤ K) (mx : ℝ) (hmx : 0 ≤ mx)
    (lam : ℝ) (hlam : 0 < lam) :
    K * mx ^ β ≤
      (lam ^ ((β + 1) / β)) * (β / (β + 1)) * mx ^ (β + 1)
        + (K / lam) ^ (β + 1) / (β + 1) := by
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  -- Conjugate pair `((β+1)/β, β+1)`.
  have hHC : Real.HolderConjugate ((β + 1) / β) (β + 1) :=
    (holderConjugate_betaPlusOne_apriori hβ).symm
  -- Apply Young to `(a, b) := (lam * mx^β, K/lam)`.
  have ha_nn : 0 ≤ lam * mx ^ β :=
    mul_nonneg hlam.le (Real.rpow_nonneg hmx _)
  have hb_nn : 0 ≤ K / lam := div_nonneg hK hlam.le
  have hY : (lam * mx ^ β) * (K / lam) ≤
      (lam * mx ^ β) ^ ((β + 1) / β) / ((β + 1) / β)
        + (K / lam) ^ (β + 1) / (β + 1) :=
    Real.young_inequality_of_nonneg ha_nn hb_nn hHC
  -- LHS simplification: `(lam * mx^β) * (K/lam) = K * mx^β`.
  have hLHS : (lam * mx ^ β) * (K / lam) = K * mx ^ β := by
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp
  -- RHS first summand: `(lam * mx^β)^{(β+1)/β}/((β+1)/β)
  --   = lam^{(β+1)/β} * (mx^β)^{(β+1)/β} * (β/(β+1))
  --   = lam^{(β+1)/β} * mx^{β+1} * (β/(β+1))`.
  have hpow_lammx :
      (lam * mx ^ β) ^ ((β + 1) / β)
        = lam ^ ((β + 1) / β) * (mx ^ β) ^ ((β + 1) / β) :=
    Real.mul_rpow hlam.le (Real.rpow_nonneg hmx _)
  have hpow_mx :
      (mx ^ β) ^ ((β + 1) / β) = mx ^ (β + 1) := by
    rw [← Real.rpow_mul hmx]
    have : β * ((β + 1) / β) = β + 1 := by
      field_simp
    rw [this]
  have hdiv : ((β + 1) / β)⁻¹ = β / (β + 1) := by
    field_simp
  have hR1 :
      (lam * mx ^ β) ^ ((β + 1) / β) / ((β + 1) / β)
        = (lam ^ ((β + 1) / β)) * (β / (β + 1)) * mx ^ (β + 1) := by
    rw [hpow_lammx, hpow_mx]
    rw [div_eq_mul_inv, hdiv]
    ring
  rw [hLHS, hR1] at hY
  exact hY

/-! ## Closed-form constants for `apriori_m_bound`

These `def`s expose the constants that the existential-form
theorem `apriori_m_bound` produces, *as explicit functions* of the
simple-power-growth hypothesis `h`, the `L^∞`-bound `Vbound` on
`V`, and the `L¹`-bound `Vint_bound` on `|V|`.

The closed-form coefficient `aprioriUepsiBelowConst` from the lower
`∫ u`-bound is defined earlier in this file, just before
`apriori_uepsi_below`. The remaining `def`s here build on it.

Every constant in the chain depends only on
`(h.β, h.C, Vbound, Vint_bound)` and the cube volume (which is `1`).
In particular every constant is **ε-independent**, which is the
property required by the Phase D residue task
`infra-P5-theorem1-phase-D-mEpsBetaBar-uniform`.
-/

/-- **Closed-form Young residual `R` from the `m^β`-absorption step**
of `apriori_m_bound`. With `δ := 1/(2C')`, `lam_pow := (β+1) δ / β`,
`lam := lam_pow ^ (β/(β+1))`, the residual is
`R = (h.C / lam) ^ (β+1) / (β+1)`. -/
def aprioriMBoundResidual
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConst h Vbound
  let δ : ℝ := 1 / (2 * C')
  let lam_pow : ℝ := (h.β + 1) * δ / h.β
  let lam : ℝ := lam_pow ^ (h.β / (h.β + 1))
  (h.C / lam) ^ (h.β + 1) / (h.β + 1)

/-- **Closed-form witness for `apriori_m_bound`**.

The constant `M` produced by `apriori_m_bound` is
`M = 2 C' · (C' + Vint_bound + R · vol + h.C · vol)`, with `vol = 1`,
`C' = aprioriUepsiBelowConst h Vbound`, and
`R = aprioriMBoundResidual h Vbound`.

This value is ε-independent: it depends only on
`(h.β, h.C, Vbound, Vint_bound)`. -/
def aprioriMBoundClosed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConst h Vbound
  let R  : ℝ := aprioriMBoundResidual h Vbound
  2 * C' * (C' + Vint_bound + R + h.C)

/-- Non-negativity of `aprioriMBoundClosed`, conditional on
`Vint_bound ≥ 0`.

Even when `Vint_bound < 0`, the closed-form expression may be
negative, but the *integrated* bound `∫ m^{β+1} ≤ M` still holds
because the LHS is non-negative — see `apriori_m_bound_closed_bound`. -/
theorem aprioriMBoundClosed_nn_of_Vint_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) :
    0 ≤ aprioriMBoundClosed h Vbound Vint_bound := by
  unfold aprioriMBoundClosed
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hC'_pos : 0 < aprioriUepsiBelowConst h Vbound :=
    aprioriUepsiBelowConst_pos h Vbound
  have h2C'_nn : 0 ≤ 2 * aprioriUepsiBelowConst h Vbound := by linarith
  -- Show the residual factor is nonneg.
  have hR_nn : 0 ≤ aprioriMBoundResidual h Vbound := by
    unfold aprioriMBoundResidual
    -- `(h.C / lam)^{β+1} / (β+1)` with `lam > 0`.
    set C' : ℝ := aprioriUepsiBelowConst h Vbound with hC'_def
    have h2C'_pos : 0 < 2 * C' := by linarith
    set δ : ℝ := 1 / (2 * C') with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
    set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
    have hlam_pow_pos : 0 < lam_pow := by
      rw [hlam_pow_def]
      exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
    set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
    have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hsum_nn :
      0 ≤ aprioriUepsiBelowConst h Vbound + Vint_bound +
            aprioriMBoundResidual h Vbound + h.C :=
    by linarith [hC'_pos, hC_pos, hR_nn]
  exact mul_nonneg h2C'_nn hsum_nn

/-- Alias matching the task naming `apriori_m_bound_closed_nn`. -/
theorem apriori_m_bound_closed_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) :
    0 ≤ aprioriMBoundClosed h Vbound Vint_bound :=
  aprioriMBoundClosed_nn_of_Vint_nn h Vbound Vint_bound hVint_nn

/-- **Paper eq. `eq:mepsi.bound`** (`Source/FGU-monotone_revised.tex`,
line 1235), closed-form variant.

Under the simple-power-growth hypothesis `h : HypothesisPowerGrowth H DpH`,
combining the hypotheses of `apriori_uepsi_above` and
`apriori_uepsi_below_closed` (repeated here verbatim) together with an
a priori `L¹`-bound on `V` on the unit cube, the integral of
`m^{β+1}` is bounded by the **closed-form constant**
`aprioriMBoundClosed h Vbound Vint_bound`, which depends explicitly
on `(h.β, h.C, Vbound, Vint_bound)` — and is *independent of `ε`*.
The bound has shape
```
∫ x in UnitCube d, m x ^ (h.β + 1) ∂volume
  ≤ aprioriMBoundClosed h Vbound Vint_bound.
```

For the historical existential shape `∃ M ≥ 0, ∫ m^{β+1} ≤ M`, see
the wrapper `apriori_m_bound`.

Proof outline:
1. From `apriori_uepsi_below_closed` get
   `(1/C') · X − C' ≤ ∫ u`, with `X := ∫ m^{β+1}` and
   `C' := aprioriUepsiBelowConst h Vbound`.
2. From `apriori_uepsi_above` get `∫ u ≤ ∫|V| + h.C · ∫ m^β + h.C · vol`.
3. Apply pointwise `young_absorb_pow_into_betaPlusOne` with scale `λ` chosen so
   that the coefficient on `m^{β+1}` after multiplying by `h.C` is exactly
   `1/(2C')`, and integrate; that yields `h.C · ∫ m^β ≤ (1/(2C')) · X + R`,
   for an explicit residual `R = aprioriMBoundResidual h Vbound`.
4. Combine: `(1/C') · X − C' ≤ Vint_bound + (1/(2C')) · X + R + h.C · vol`,
   so `(1/(2C')) · X ≤ C' + Vint_bound + R + h.C · vol`, giving
   `X ≤ 2C' · (C' + Vint_bound + R + h.C) = aprioriMBoundClosed h Vbound Vint_bound`
   (using `vol = 1`). -/
theorem apriori_m_bound_closed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosed h Vbound Vint_bound := by
  -- Constants.
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  -- Cube volume / finiteness.
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by
    simp [hvol_def]
  -- Step 1: Lower bound on ∫ u from `apriori_uepsi_below_closed`. We
  -- bind `C'` to the closed-form witness so the final constant `M` is
  -- a closed-form function of `(h, Vbound, Vint_bound)`.
  set C' : ℝ := aprioriUepsiBelowConst h Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_pos h Vbound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed (h := h) V Du m u epsTerms Vbound
      h_lagr hMpos hVbnd hEpsNN h_identity hLB_int hRHSbelow_int
  -- Step 2: Upper bound on ∫ u from `apriori_uepsi_above`.
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above (h := h.toCongestionAprioriPowerData) V Du m u hHJB hMpos hu_int hRHSabove_int
  -- Set X := ∫ m^{β+1}.
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  -- Set Y := ∫ m^β.
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  -- Set Vint := ∫ |V|.
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  -- Compute the upper-bound RHS as `Vint + h.C * (Y + vol)`.
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      -- |V| is the abs of (|V| + h.C·(m^β+1)) − h.C·(m^β+1), but easier: extract
      -- from `hRHSabove_int` by subtraction.
      have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul h.C
      have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                    - h.C * (m x ^ h.β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    -- Now split the integral.
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    -- second term: ∫ h.C * (m^β + 1) = h.C * (Y + vol).
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  -- Combine: (1/C') · X − C' ≤ ∫u ≤ Vint + h.C * (Y + vol).
  have hcomb : (1 / C') * X - C' ≤ Vint + h.C * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + h.C * (Y + vol) := habove_eq
  -- Step 3: Pointwise Young absorption: choose `lam_pow` so that
  --   `lam_pow * (β/(β+1)) = 1/(2C')`,
  -- making the coefficient on `mx^{β+1}` exactly `δ := 1/(2C')`. Since the
  -- pointwise lemma reads `K · mx^β ≤ lam_pow · (β/(β+1)) · mx^{β+1} + ...`
  -- (no `K`-factor on the `mx^{β+1}` term), this δ does the absorption
  -- against the `1/C'`-coefficient on the LHS of `hcomb`.
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  -- Choose `lam_pow := (β+1) * δ / β` so that `lam_pow * (β/(β+1)) = δ`.
  set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (h.β / (h.β + 1)) = δ := by
    rw [hlam_pow_def]
    field_simp
  -- Define lam := lam_pow ^ (β/(β+1)) so that lam^{(β+1)/β} = lam_pow.
  set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((h.β + 1) / h.β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : h.β / (h.β + 1) * ((h.β + 1) / h.β) = 1 := by
      have hβne : h.β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : h.β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  -- Define Young residual and integrate the pointwise bound. We bind
  -- `R` to the closed-form `def` `aprioriMBoundResidual h Vbound`,
  -- whose definitional unfolding yields exactly
  -- `(h.C / lam) ^ (h.β + 1) / (h.β + 1)`.
  set R : ℝ := aprioriMBoundResidual h Vbound with hR_def
  have hR_unfold : R = (h.C / lam) ^ (h.β + 1) / (h.β + 1) := by
    show aprioriMBoundResidual h Vbound = _
    -- The `let`-bound `C', δ, lam_pow, lam` inside `aprioriMBoundResidual`
    -- definitionally match the outer `set C', set δ, set lam_pow, set lam`.
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  -- Apply pointwise Young to `K = h.C` and the chosen `lam`.
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      h.C * mx ^ h.β ≤ δ * mx ^ (h.β + 1) + R := by
    intro mx hmx
    have hY := young_absorb_pow_into_betaPlusOne (β := h.β) hβ_pos
                  h.C hC_pos.le mx hmx lam hlam_pos
    -- hY :  h.C * mx^β ≤ lam^{(β+1)/β} * (β/(β+1)) * mx^{β+1}
    --                       + (h.C/lam)^{β+1}/(β+1)
    rw [hlam_pow_id] at hY
    -- Now `lam_pow * (β/(β+1)) = δ`.
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  -- Integrate: h.C · Y ≤ δ · X + R · vol.
  have hY_int :
      Integrable (fun x => h.C * m x ^ h.β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul h.C
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (h.β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => h.C * m x ^ h.β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (h.β + 1) + R) := by
    filter_upwards [hMpos] with x hxm
    exact hYoung_pt (m x) hxm.le
  have hYint_le :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  -- LHS: `∫ h.C · m^β = h.C · Y`.
  have hYint_LHS :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ))
        = h.C * Y := by
    rw [integral_const_mul]
  -- RHS: `∫ (δ · m^{β+1} + R) = δ · X + R · vol`.
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ))
        = δ * X + R * vol := by
    rw [integral_add (hLB_int.const_mul δ) (integrable_const _),
        integral_const_mul]
    have hone_int :
        ∫ _ in UnitCube d, R ∂(volume : Measure (Fin d → ℝ)) = R * vol := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, hvol_def, mul_comm]
    rw [hone_int]
  rw [hYint_LHS, hYint_RHS] at hYint_le
  -- Combine with hcomb: (1/C') · X − C' ≤ Vint + δ · X + R · vol + h.C · vol.
  have hcomb' :
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + h.C * vol := by
    have : h.C * (Y + vol) = h.C * Y + h.C * vol := by ring
    have h1 : Vint + h.C * (Y + vol) ≤ Vint + (δ * X + R * vol) + h.C * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  -- Coefficient identity: 1/C' - δ = 1/(2C') with `δ = 1/(2C')`.
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  -- Hence (1/(2C')) · X ≤ C' + Vint + R · vol + h.C · vol.
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + h.C * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  -- Use Vint ≤ Vint_bound.
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + h.C * vol := by
    linarith [habs, hVint_le]
  -- Final: X ≤ 2C' · (C' + Vint_bound + R · vol + h.C · vol).
  -- Unfold `aprioriMBoundClosed` to its `let`-form and bridge the
  -- `* vol = * 1` simplification.
  have hM_unfold :
      aprioriMBoundClosed h Vbound Vint_bound
        = 2 * C' * (C' + Vint_bound + R + h.C) := by
    show aprioriMBoundClosed h Vbound Vint_bound = _
    -- The `let`-bound `C', R` inside `aprioriMBoundClosed` definitionally
    -- match the outer `set C', set R`.
    rfl
  -- Multiply both sides of `habs2` by `2C' > 0`.
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + h.C * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  -- Goal: X ≤ aprioriMBoundClosed h Vbound Vint_bound. Bridge by
  -- substituting `vol = 1` in `hmul` and unfolding the `def`.
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  -- hmul : X ≤ 2 * C' * (C' + Vint_bound + R + h.C)
  rw [hM_unfold]
  exact hmul

/-- **Paper eq. `eq:mepsi.bound`** existential wrapper.

`apriori_m_bound_closed` provides the bound with the explicit
closed-form witness `aprioriMBoundClosed h Vbound Vint_bound`. This
wrapper re-emits the bound in the historical existential shape
`∃ M, 0 ≤ M ∧ …` for backwards compatibility with downstream
callers (`apriori_uepsi_mean`, `apriori_aggregate_bound`, …). -/
theorem apriori_m_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
  refine ⟨aprioriMBoundClosed h Vbound Vint_bound, ?_, ?_⟩
  · -- Non-negativity of the closed-form witness. We need
    -- `Vint_bound ≥ 0`, which we extract from the integral bound:
    -- `0 ≤ ∫ |V| ≤ Vint_bound`.
    have hVint_nn : 0 ≤ Vint_bound := by
      have h1 : 0 ≤ ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) := by
        apply integral_nonneg
        intro x; exact abs_nonneg _
      linarith [h1, hVint]
    exact aprioriMBoundClosed_nn_of_Vint_nn h Vbound Vint_bound hVint_nn
  · exact apriori_m_bound_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint

/-! ### Sanity check for `apriori_m_bound` -/

/-- **Unit test**: `apriori_m_bound` applies in a trivial/abstract setting.

Given `h : HypothesisPowerGrowth H DpH` and the matching hypotheses, we
exhibit the conclusion. This example simply forwards all hypotheses to the
main theorem; its purpose is to verify the API is callable. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
  apriori_m_bound (h := h) V Du m u epsTerms Vbound Vint_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint

/-! ## A priori bound on the mean of `u_ε` (paper line 1242)

After `apriori_m_bound` (paper eq. `eq:mepsi.bound`) gives a uniform bound on
`‖m_ε‖_{L^{β̄}}^{β̄} = ∫ m_ε^{β+1}`, substituting back into both
`eq:uepsibelow` and `eq:uepsiabove` yields

  |∫_{𝕋^d} u_ε dx| ≤ C,

with `C` independent of `ε`. The lower bound follows from non-negativity of
`(1/C') · ∫ m^{β+1}`. The upper bound uses the pointwise inequality
`m^β ≤ m^{β+1} + 1` (for `m ≥ 0`) to convert `∫ m^β` into `∫ m^{β+1} + vol`,
which is bounded by `M + vol`.
-/

/-- **Closed-form witness for `apriori_uepsi_mean`**.

The mean-bound constant produced by `apriori_uepsi_mean` is
`Cmean = max C' (Vint_bound + h.C · (M + 2 · vol))` with `vol = 1`,
`C' = aprioriUepsiBelowConst h Vbound`, and
`M = aprioriMBoundClosed h Vbound Vint_bound`.

This value is ε-independent: it depends only on `(h, Vbound, Vint_bound)`. -/
def aprioriUepsiMeanClosed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) : ℝ :=
  max (aprioriUepsiBelowConst h Vbound)
      (Vint_bound + h.C * (aprioriMBoundClosed h Vbound Vint_bound + 2))

/-- Non-negativity of `aprioriUepsiMeanClosed`. The lower bound
`max ≥ aprioriUepsiBelowConst > 0` is unconditional. -/
theorem aprioriUepsiMeanClosed_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) :
    0 ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
  unfold aprioriUepsiMeanClosed
  exact le_trans (aprioriUepsiBelowConst_nn h Vbound) (le_max_left _ _)


/-- **Pointwise inequality** `m^β ≤ m^{β+1} + 1` for `m ≥ 0` and `β > 0`.

Proof by case-split on `m ≤ 1` vs. `m ≥ 1`:
* If `m ≤ 1`, then `m^β ≤ 1^β = 1` (monotonicity of `rpow`).
* If `m ≥ 1`, then `m^β ≤ m^{β+1}` since `m^{β+1} = m · m^β ≥ m^β`.
-/
private lemma rpow_beta_le_rpow_betaPlusOne_add_one
    {β : ℝ} (hβ : 0 < β) {m : ℝ} (hm : 0 ≤ m) :
    m ^ β ≤ m ^ (β + 1) + 1 := by
  rcases le_or_gt m 1 with hm1 | hm1
  · -- m ≤ 1: m^β ≤ 1.
    have hpow_le_one : m ^ β ≤ 1 := by
      have h := Real.rpow_le_one hm hm1 hβ.le
      exact h
    have hpow_nn : 0 ≤ m ^ (β + 1) := Real.rpow_nonneg hm _
    linarith
  · -- m > 1: m^β ≤ m^{β+1}.
    have hm_pos : 0 < m := lt_trans zero_lt_one hm1
    have hpow_le : m ^ β ≤ m ^ (β + 1) := by
      have hβ_le : β ≤ β + 1 := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hm1.le hβ_le
    linarith

/-- **Paper line 1242**, closed-form variant: `|∫ u_ε|` is bounded by
the explicit ε-independent constant `aprioriUepsiMeanClosed h Vbound Vint_bound`.

Combining `apriori_m_bound_closed` (paper eq. `eq:mepsi.bound`),
`apriori_uepsi_below_closed` (paper eq. `eq:uepsibelow`), and
`apriori_uepsi_above` (paper eq. `eq:uepsiabove`), we obtain
```
|∫ x in UnitCube d, u x| ≤ aprioriUepsiMeanClosed h Vbound Vint_bound.
```

The hypotheses are exactly those of `apriori_m_bound`. -/
theorem apriori_uepsi_mean_closed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
  -- Constants.
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  -- Cube finiteness.
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  -- Step 1: From `apriori_m_bound_closed`, get `∫ m^{β+1} ≤ M` with
  -- `M := aprioriMBoundClosed h Vbound Vint_bound`.
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  -- Step 2: From `apriori_uepsi_below_closed`, get
  -- `(1/C') · ∫ m^{β+1} − C' ≤ ∫ u` with `C' := aprioriUepsiBelowConst h Vbound`.
  set C' : ℝ := aprioriUepsiBelowConst h Vbound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_pos h Vbound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed (h := h) V Du m u epsTerms Vbound
      h_lagr hMpos hVbnd hEpsNN h_identity hLB_int hRHSbelow_int
  -- Step 3: From `apriori_uepsi_above`, get `∫ u ≤ ∫ (|V| + h.C · (m^β + 1))`.
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above (h := h.toCongestionAprioriPowerData) V Du m u hHJB hMpos hu_int hRHSabove_int
  -- Step 4: Compute the upper-bound RHS as `Vint + h.C * (Y + vol)`, where
  -- `Y = ∫ m^β`. (Same calculation as in `apriori_m_bound`.)
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                  - h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  -- Step 5: Bound Y = ∫ m^β ≤ X + vol via pointwise `m^β ≤ m^{β+1} + 1`.
  have hY_le_X_plus_vol : Y ≤ X + vol := by
    have hpoint :
        (fun x => m x ^ h.β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (h.β + 1) + 1) := by
      filter_upwards [hMpos] with x hxm
      exact rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm.le
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (h.β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ h.β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = X + vol := by
      rw [integral_add hLB_int hone_int']
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hRHS_eq] at hint_le
    exact hint_le
  -- Step 6: Combine to get the upper bound on `∫ u`.
  have hX_le_M : X ≤ M := hM_le
  have hY_le_M_plus_vol : Y ≤ M + vol := by linarith
  have hVint_le : Vint ≤ Vint_bound := hVint
  set Uint : ℝ := ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) with hUint_def
  -- Upper bound: Uint ≤ Vint + h.C·(Y + vol) ≤ Vint_bound + h.C·(M + 2·vol).
  have hUint_ub : Uint ≤ Vint_bound + h.C * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + h.C * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : h.C * (Y + vol) ≤ h.C * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + h.C * (Y + vol) ≤ Vint_bound + h.C * (M + 2 * vol) := by
      have : h.C * ((M + vol) + vol) = h.C * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  -- Lower bound: Uint ≥ (1/C') · X − C' ≥ −C' (since (1/C')·X ≥ 0).
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    -- hbelow : (1 / C') * X - C' ≤ Uint, but X here equals the integral.
    -- The Set X is defined the same way as the integral in hbelow.
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  -- Step 7: Conclude via the closed-form `aprioriUepsiMeanClosed`.
  -- Unfold `aprioriUepsiMeanClosed` to its `let`-form. The `set C', set M`
  -- inside the body match the outer `set C', set M` definitionally.
  have hCmean_unfold :
      aprioriUepsiMeanClosed h Vbound Vint_bound
        = max C' (Vint_bound + h.C * (M + 2)) := by
    show aprioriUepsiMeanClosed h Vbound Vint_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  -- Substitute `vol = 1` so the upper bound matches the closed-form RHS.
  have hUint_ub' : Uint ≤ Vint_bound + h.C * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + h.C * (M + 2) ≤ aprioriUepsiMeanClosed h Vbound Vint_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- -Cmean ≤ Uint.
    have hneg : -aprioriUepsiMeanClosed h Vbound Vint_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · -- Uint ≤ Cmean.
    linarith [hUint_ub', hCmean_ge_ub]

/-- **Paper line 1242** existential wrapper.

`apriori_uepsi_mean_closed` provides the mean bound with the explicit
closed-form witness `aprioriUepsiMeanClosed h Vbound Vint_bound`. This
wrapper re-emits the bound in the historical existential shape
`∃ Cmean, 0 ≤ Cmean ∧ …` for backwards compatibility with downstream
callers (`apriori_uepsi_Lp`, …). -/
theorem apriori_uepsi_mean
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∃ Cmean : ℝ, 0 ≤ Cmean ∧
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
  ⟨aprioriUepsiMeanClosed h Vbound Vint_bound,
    aprioriUepsiMeanClosed_nn h Vbound Vint_bound,
    apriori_uepsi_mean_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint⟩

/-! ### Sanity check for `apriori_uepsi_mean` -/

/-- **Unit test**: `apriori_uepsi_mean` applies in a trivial/abstract setting.

Given `h : HypothesisPowerGrowth H DpH` and the matching hypotheses (the same
as for `apriori_m_bound`), we exhibit the conclusion. This example simply
forwards all hypotheses to the main theorem; its purpose is to verify the
API is callable. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound) :
    ∃ Cmean : ℝ, 0 ≤ Cmean ∧
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
  apriori_uepsi_mean (h := h) V Du m u epsTerms Vbound Vint_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint

/-! ## A priori `L^{γ̄}` bound on `u_ε` via Poincaré–Wirtinger

This is paper `eq:poincare-torus` (`Source/FGU-monotone_revised.tex`,
line 1245). Combining the mean bound `apriori_uepsi_mean` with the
Poincaré–Wirtinger inequality on the torus
(`Periodic/SobolevPoincare.poincareWirtinger`) yields

```
‖u_ε‖_{L^{γ̄}(𝕋^d)} ≤ C · (‖Du_ε‖_{L^{γ̄}(𝕋^d)} + 1).
```
-/

/-- The `L^p`-norm of a constant function on the unit cube equals the
absolute value of the constant, since `volume (UnitCube d) = 1`. This is
a periodic specialisation of `MeasureTheory.eLpNorm_const`. -/
private lemma lpNormPer_const_unitCube
    (p : ℝ≥0∞) (hp : p ≠ 0) (c : ℝ) :
    lpNormPer (d := d) p (fun _ : Fin d → ℝ => c) = |c| := by
  unfold lpNormPer eLpNormPer
  -- The cube-restricted measure has `univ`-measure equal to `1`.
  have hμuniv :
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]
  have hμ_ne : (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube d)) ≠ 0 := by
    intro h; rw [h] at hμuniv; simp at hμuniv
  rw [MeasureTheory.eLpNorm_const c hp hμ_ne, hμuniv]
  -- ‖c‖ₑ * 1 ^ (1/p.toReal) = ‖c‖ₑ.
  rw [ENNReal.one_rpow, mul_one]
  -- (‖c‖ₑ).toReal = |c|.
  rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- **Closed-form witness for `apriori_uepsi_Lp`**.

The constant `C` produced by `apriori_uepsi_Lp` is
`C := max (poincareWirtingerConstant d) Cmean` with
`Cmean := aprioriUepsiMeanClosed h Vbound Vint_bound`.

This value is ε-independent: it depends only on `(d, h, Vbound, Vint_bound)`. -/
def aprioriUBoundClosed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) : ℝ :=
  max (poincareWirtingerConstant d)
      (aprioriUepsiMeanClosed h Vbound Vint_bound)

/-- Non-negativity of `aprioriUBoundClosed`. The lower bound
`max ≥ poincareWirtingerConstant d ≥ 0` is unconditional. -/
theorem aprioriUBoundClosed_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) :
    0 ≤ aprioriUBoundClosed (d := d) h Vbound Vint_bound := by
  unfold aprioriUBoundClosed
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  exact le_trans hd_nn (le_max_left _ _)

/-- **Paper eq. `eq:poincare-torus`** (`Source/FGU-monotone_revised.tex`,
line 1245), closed-form variant.

Under the hypotheses of `apriori_uepsi_mean` together with the Sobolev
regularity needed by `poincareWirtinger` at exponent `γ̄ = gammaBar h.α h.β`,
the periodic `L^{γ̄}`-norm of `u_ε` is controlled by the periodic
`L^{γ̄}`-norm of its weak gradient up to an additive `1`, with
**closed-form constant** `aprioriUBoundClosed h Vbound Vint_bound`
that is ε-independent:

```
‖u_ε‖_{L^{γ̄}(𝕋^d)} ≤
  aprioriUBoundClosed h Vbound Vint_bound ·
    (∑_i ‖∂_i u_ε‖_{L^{γ̄}(𝕋^d)} + 1).
```

The argument is the standard Poincaré–Wirtinger reduction:

* `apriori_uepsi_mean_closed` controls `|periodicMean u_ε|` by
  `aprioriUepsiMeanClosed h Vbound Vint_bound`.
* `poincareWirtinger` bounds `‖u_ε − periodicMean u_ε‖_{L^{γ̄}}` by
  `d · ∑_i ‖∂_i u_ε‖_{L^{γ̄}}`.
* The triangle inequality for `lpNormPer` collapses these into the stated
  bound, with `C := max d Cmean = aprioriUBoundClosed h Vbound Vint_bound`. -/
theorem apriori_uepsi_Lp_closed
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    -- Sobolev regularity required by `poincareWirtinger` at exponent γ̄.
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed (d := d) h Vbound Vint_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  -- Abbreviations.
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  -- Step 1: from `apriori_uepsi_mean_closed`, get `|∫ u| ≤ Cmean` with
  -- `Cmean := aprioriUepsiMeanClosed h Vbound Vint_bound`.
  set Cmean : ℝ := aprioriUepsiMeanClosed h Vbound Vint_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean := aprioriUepsiMeanClosed_nn h Vbound Vint_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  -- The mean of `u` equals the integral of `u` over the unit cube.
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  -- Step 2: Poincaré–Wirtinger bound on `u − ⟨u⟩`.
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    poincareWirtinger (p := p) hγ_one_le hγ_top
      hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas
      hDu_per hDu_loc hDu_lp
  -- Step 3: triangle inequality `‖u‖ ≤ ‖u − ⟨u⟩‖ + ‖⟨u⟩‖`.
  -- Closure under add: `MemLpPer p u`, `MemLpPer p (const ⟨u⟩)`.
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  -- `MemLpPer p (u − ⟨u⟩)` from closure under subtraction (= add of negative).
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    -- `u - const⟨u⟩ = u + const(-⟨u⟩)` pointwise.
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  -- Real-valued triangle inequality `lpNormPer p (a + b) ≤ lpNormPer p a + lpNormPer p b`.
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    -- Rewrite the LHS of `h` as `lpNormPer p u`.
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  -- Step 4: `lpNormPer p (const ⟨u⟩) = |⟨u⟩| ≤ Cmean`.
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  -- Step 5: combine — `‖u‖ ≤ d · S + Cmean`, where `S := ∑ i, ‖Du i‖`.
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  -- Step 6: identify `C := aprioriUBoundClosed h Vbound Vint_bound`.
  -- Unfold to its `let`-form so `Cmean` matches the closed-form definition.
  set C : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed h Vbound Vint_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  -- Final bound: `‖u‖ ≤ d·S + Cmean ≤ C·S + C = C·(S + 1)`.
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **Paper eq. `eq:poincare-torus`** existential wrapper.

`apriori_uepsi_Lp_closed` provides the bound with the explicit
closed-form witness `aprioriUBoundClosed h Vbound Vint_bound`. This
wrapper re-emits the bound in the historical existential shape
`∃ C, 0 ≤ C ∧ …` for backwards compatibility with downstream
callers (`apriori_aggregate_bound`, `apriori_uepsi_Lp_betaBarPrime`, …). -/
theorem apriori_uepsi_Lp
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    ∃ C : ℝ, 0 ≤ C ∧
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        C * ((∑ i : Fin d, lpNormPer
                (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
  ⟨aprioriUBoundClosed (d := d) h Vbound Vint_bound,
    aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound,
    apriori_uepsi_Lp_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp⟩

/-! ### Sanity check for `apriori_uepsi_Lp` -/

/-- **Unit test**: `apriori_uepsi_Lp` applies in a trivial/abstract setting.

Given the same hypotheses as the theorem, we reproduce the conclusion by
direct forwarding. This example exists solely to confirm the API surface. -/
example
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    ∃ C : ℝ, 0 ≤ C ∧
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        C * ((∑ i : Fin d, lpNormPer
                (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
  apriori_uepsi_Lp (h := h) V Du m u epsTerms Vbound Vint_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint
    hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
    hDu_weak hDu_meas hDu_per hDu_loc hDu_lp

/-! ## Pointwise upper bound on `‖Du‖^{γ̄}` (paper eq. `eq:Duepsiabove`)

This section formalizes `Source/FGU-monotone_revised.tex` lines 1250–1255:
combining the HJB inequality `eq:HJleq0` with `eq:assH.lower.simple` gives
the pointwise bound `‖Du‖^α ≤ C·(m^β + |u| + |V| + 1)` (the unraised
version), and raising it to the power `β̄' = γ̄/α` yields `eq:Duepsiabove`:
```
‖Du‖^{γ̄} ≤ C·(m^{β̄} + |u|^{β̄'} + |V|^{β̄'} + 1)
```
where `β̄ = β + 1`, `β̄' = (β + 1)/β`, and `γ̄ = α · β̄'`.
-/

/-- **Helper**: for nonneg reals `a, b` and `q ≥ 0`,
`(a + b) ^ q ≤ 2^q · (a^q + b^q)`.

Proof: `a + b ≤ 2 · max a b`, then raise to `q ≥ 0` using monotonicity of
`Real.rpow`, and bound `max a b ^ q ≤ a^q + b^q` because the maximum is one
of `a, b` and the other rpow is nonneg. -/
private lemma add_rpow_le_two_rpow_mul {a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hmax_nn : 0 ≤ max a b := le_max_of_le_left ha
  -- Step 1: a + b ≤ 2 * max a b.
  have h1 : a + b ≤ 2 * max a b := by
    have ha' : a ≤ max a b := le_max_left a b
    have hb' : b ≤ max a b := le_max_right a b
    linarith
  -- Step 2: raise both sides to q, monotonicity preserves direction.
  have h2 : (a + b) ^ q ≤ (2 * max a b) ^ q :=
    Real.rpow_le_rpow hab h1 hq
  -- Step 3: (2 * max a b)^q = 2^q * (max a b)^q.
  have h3 : (2 * max a b) ^ q = (2 : ℝ) ^ q * (max a b) ^ q :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmax_nn
  -- Step 4: (max a b)^q ≤ a^q + b^q.
  have h4 : (max a b) ^ q ≤ a ^ q + b ^ q := by
    rcases le_total a b with hab' | hab'
    · rw [max_eq_right hab']
      have : 0 ≤ a ^ q := Real.rpow_nonneg ha q
      linarith
    · rw [max_eq_left hab']
      have : 0 ≤ b ^ q := Real.rpow_nonneg hb q
      linarith
  -- Combine.
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ q :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q
  calc (a + b) ^ q
      ≤ (2 * max a b) ^ q := h2
    _ = (2 : ℝ) ^ q * (max a b) ^ q := h3
    _ ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
        exact mul_le_mul_of_nonneg_left h4 h2pos

/-- **Helper**: for nonneg reals `a, b, c, d` and `q ≥ 0`,
`(a + b + c + d) ^ q ≤ 4^q · (a^q + b^q + c^q + d^q)`.

Proof: chain `add_rpow_le_two_rpow_mul` twice: bound `((a+b)+(c+d))^q` by
`2^q · ((a+b)^q + (c+d)^q)`, then bound each `(a+b)^q` and `(c+d)^q`. -/
private lemma four_add_rpow_le_four_rpow_mul
    {a b c d q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hq : 0 ≤ q) :
    (a + b + c + d) ^ q ≤ (4 : ℝ) ^ q * (a ^ q + b ^ q + c ^ q + d ^ q) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hcd : 0 ≤ c + d := add_nonneg hc hd
  -- Step 1: ((a+b) + (c+d))^q ≤ 2^q * ((a+b)^q + (c+d)^q).
  have h1 : (a + b + (c + d)) ^ q ≤
      (2 : ℝ) ^ q * ((a + b) ^ q + (c + d) ^ q) :=
    add_rpow_le_two_rpow_mul hab hcd hq
  -- Step 2: bound (a+b)^q and (c+d)^q.
  have h2 : (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) :=
    add_rpow_le_two_rpow_mul ha hb hq
  have h3 : (c + d) ^ q ≤ (2 : ℝ) ^ q * (c ^ q + d ^ q) :=
    add_rpow_le_two_rpow_mul hc hd hq
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ q :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q
  -- Combine and use 2^q * 2^q = 4^q.
  have hpow : (2 : ℝ) ^ q * (2 : ℝ) ^ q = (4 : ℝ) ^ q := by
    have h22 : (2 : ℝ) * 2 = 4 := by norm_num
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
                        (by norm_num : (0 : ℝ) ≤ 2), h22]
  calc (a + b + c + d) ^ q
      = (a + b + (c + d)) ^ q := by ring_nf
    _ ≤ (2 : ℝ) ^ q * ((a + b) ^ q + (c + d) ^ q) := h1
    _ ≤ (2 : ℝ) ^ q *
          ((2 : ℝ) ^ q * (a ^ q + b ^ q) +
            (2 : ℝ) ^ q * (c ^ q + d ^ q)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add h2 h3) h2pos
    _ = (2 : ℝ) ^ q * (2 : ℝ) ^ q *
          (a ^ q + b ^ q + c ^ q + d ^ q) := by ring
    _ = (4 : ℝ) ^ q * (a ^ q + b ^ q + c ^ q + d ^ q) := by rw [hpow]

/-- **Pointwise unraised bound** (paper line 1251).

Combining the HJB inequality `u(x) + H(x, Du, m) ≤ V(x)` with
`(eq:assH.lower.simple)` `H(x, p, m) ≥ ‖p‖^α / C − C(m^β + 1)`, we obtain
the pointwise inequality
```
‖Du x‖^α ≤ K · (m x ^ β + |u x| + |V x| + 1)
```
a.e. on the unit cube, where `K = h.C + h.C^2`. -/
theorem apriori_Du_alpha_pointwise
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ h.α ≤
        (h.C + h.C ^ 2) *
          (m x ^ h.β + |u x| + |V x| + 1) := by
  filter_upwards [hHJB, hMpos, h.lower] with x hx hxm hxlow
  -- hxlow at p = (Du · x), m = m x:
  -- H x (Du · x) (m x) ≥ ‖Du · x‖^α / h.C − h.C * (m x ^ h.β + 1).
  have hLow := hxlow (fun i => Du i x) (m x) hxm
  -- Rearranged: ‖Du · x‖^α / h.C ≤ H x (Du · x) (m x) + h.C * (m x ^ h.β + 1).
  -- HJB: u + H − V ≤ 0, i.e. H ≤ V − u.
  -- Combine: ‖Du · x‖^α / h.C ≤ V − u + h.C * (m x ^ h.β + 1)
  --                          ≤ |V| + |u| + h.C * (m x ^ h.β + 1).
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hC2_nn : (0 : ℝ) ≤ h.C ^ 2 := by positivity
  have hpow_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hVabs : V x ≤ |V x| := le_abs_self _
  have hUabs : -u x ≤ |u x| := neg_le_abs _
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β :=
    Real.rpow_nonneg hxm.le _
  -- Multiply hLow rearranged by h.C (positive).
  -- From hLow: ‖p‖^α / h.C - h.C * (m^β + 1) ≤ H, so
  --             ‖p‖^α / h.C ≤ H + h.C * (m^β + 1).
  -- Multiply by h.C: ‖p‖^α ≤ h.C * H + h.C^2 * (m^β + 1).
  have hα_aux :
      ‖(fun i => Du i x)‖ ^ h.α ≤
        h.C * H x (fun i => Du i x) (m x) +
          h.C ^ 2 * (m x ^ h.β + 1) := by
    have := hLow
    -- this : H x (Du · x) (m x) ≥ ‖p‖^α / h.C - h.C * (m x ^ h.β + 1)
    have hCne : h.C ≠ 0 := ne_of_gt hC_pos
    have hmul := mul_le_mul_of_nonneg_left this hC_nn
    -- hmul : h.C * (‖p‖^α / h.C - h.C*(m^β+1)) ≤ h.C * H
    have heq1 : h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C
                        - h.C * (m x ^ h.β + 1))
               = ‖(fun i => Du i x)‖ ^ h.α
                   - h.C ^ 2 * (m x ^ h.β + 1) := by
      have hcancel : h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C) =
              ‖(fun i => Du i x)‖ ^ h.α := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ _ hCne
      have hsq : h.C * (h.C * (m x ^ h.β + 1)) = h.C ^ 2 * (m x ^ h.β + 1) := by
        ring
      calc h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C
                    - h.C * (m x ^ h.β + 1))
          = h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C)
              - h.C * (h.C * (m x ^ h.β + 1)) := by ring
        _ = ‖(fun i => Du i x)‖ ^ h.α
              - h.C ^ 2 * (m x ^ h.β + 1) := by rw [hcancel, hsq]
    rw [heq1] at hmul
    linarith
  -- HJB: H ≤ V - u.
  have hHJB' : H x (fun i => Du i x) (m x) ≤ V x - u x := by linarith
  -- So h.C * H ≤ h.C * (V - u) = h.C * V + h.C * (-u).
  have hCH_le : h.C * H x (fun i => Du i x) (m x) ≤ h.C * (V x - u x) :=
    mul_le_mul_of_nonneg_left hHJB' hC_nn
  -- And h.C * (V - u) = h.C * V + h.C * (-u) ≤ h.C * |V| + h.C * |u|.
  have hCVu : h.C * (V x - u x) ≤ h.C * |V x| + h.C * |u x| := by
    have h1 : h.C * V x ≤ h.C * |V x| := mul_le_mul_of_nonneg_left hVabs hC_nn
    have h2 : h.C * (-u x) ≤ h.C * |u x| := mul_le_mul_of_nonneg_left hUabs hC_nn
    have heq : h.C * (V x - u x) = h.C * V x + h.C * (-u x) := by ring
    linarith
  -- Combine all inequalities.
  -- ‖p‖^α ≤ h.C * H + h.C^2 * (m^β + 1)
  --      ≤ h.C * (V - u) + h.C^2 * (m^β + 1)
  --      ≤ h.C * |V| + h.C * |u| + h.C^2 * m^β + h.C^2.
  have hstep :
      ‖(fun i => Du i x)‖ ^ h.α ≤
        h.C * |V x| + h.C * |u x| + h.C ^ 2 * (m x ^ h.β) + h.C ^ 2 := by
    have : h.C ^ 2 * (m x ^ h.β + 1) =
              h.C ^ 2 * (m x ^ h.β) + h.C ^ 2 := by ring
    linarith
  -- Final step: bound by `(h.C + h.C^2) * (m^β + |u| + |V| + 1)`.
  -- Note: h.C * |V| ≤ (h.C + h.C^2) * |V|, etc.
  have hsum_nn : (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hKge_C : h.C ≤ h.C + h.C ^ 2 := by linarith
  have hKge_C2 : h.C ^ 2 ≤ h.C + h.C ^ 2 := by linarith
  have hK_nn : (0 : ℝ) ≤ h.C + h.C ^ 2 := by linarith
  -- Bound each term:
  have h_Vbound : h.C * |V x| ≤ (h.C + h.C ^ 2) * |V x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Ubound : h.C * |u x| ≤ (h.C + h.C ^ 2) * |u x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Mbound : h.C ^ 2 * (m x ^ h.β) ≤ (h.C + h.C ^ 2) * (m x ^ h.β) :=
    mul_le_mul_of_nonneg_right hKge_C2 hmβ_nn
  have h_Cbound : h.C ^ 2 ≤ (h.C + h.C ^ 2) * 1 := by linarith
  have hRHS_eq : (h.C + h.C ^ 2) * (m x ^ h.β + |u x| + |V x| + 1)
                  = (h.C + h.C ^ 2) * (m x ^ h.β)
                    + (h.C + h.C ^ 2) * |u x|
                    + (h.C + h.C ^ 2) * |V x|
                    + (h.C + h.C ^ 2) * 1 := by ring
  linarith

/-- **HMpos-1.** Nonneg variant of `apriori_Du_alpha_pointwise`
(unraised pointwise bound on `‖Du‖^α`, paper line 1251).

Identical to `apriori_Du_alpha_pointwise` but requires only `0 ≤ m`
a.e. instead of `0 < m`. The boundary `m = 0` case is recovered by
routing the rearranged lower bound `‖p‖^α/C - C(m^β+1) ≤ H x p m`
through `H_lower_bound_ae_nonneg` (paper Hat0 boundary helper), which
uses the paper-faithful right-continuity rider `H_rc0_of_hHat0` at
`m = 0⁺`. -/
theorem apriori_Du_alpha_pointwise_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (hHat0 : HypothesisHat0 H)
    (hFin : Hext_finite_at_zero H)
    (hAgree : H_zero_eq_Hext H)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ h.α ≤
        (h.C + h.C ^ 2) *
          (m x ^ h.β + |u x| + |V x| + 1) := by
  filter_upwards [hHJB, hMnn,
      H_lower_bound_ae_nonneg (d := d) h hHat0 hFin hAgree]
    with x hx hxm hxlow
  -- hxlow at p = (Du · x), m = m x:
  -- ‖p‖^α / h.C - h.C * (m^β+1) ≤ H x (Du · x) (m x).
  have hLow := hxlow (fun i => Du i x) (m x) hxm
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hC2_nn : (0 : ℝ) ≤ h.C ^ 2 := by positivity
  have hpow_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hVabs : V x ≤ |V x| := le_abs_self _
  have hUabs : -u x ≤ |u x| := neg_le_abs _
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β :=
    Real.rpow_nonneg hxm _
  -- Multiply hLow by h.C (positive):
  -- ‖p‖^α ≤ h.C * H + h.C^2 * (m^β + 1).
  have hα_aux :
      ‖(fun i => Du i x)‖ ^ h.α ≤
        h.C * H x (fun i => Du i x) (m x) +
          h.C ^ 2 * (m x ^ h.β + 1) := by
    have hCne : h.C ≠ 0 := ne_of_gt hC_pos
    have hmul := mul_le_mul_of_nonneg_left hLow hC_nn
    -- hmul : h.C * (‖p‖^α / h.C - h.C*(m^β+1)) ≤ h.C * H
    have heq1 : h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C
                        - h.C * (m x ^ h.β + 1))
               = ‖(fun i => Du i x)‖ ^ h.α
                   - h.C ^ 2 * (m x ^ h.β + 1) := by
      have hcancel : h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C) =
              ‖(fun i => Du i x)‖ ^ h.α := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ _ hCne
      have hsq : h.C * (h.C * (m x ^ h.β + 1)) = h.C ^ 2 * (m x ^ h.β + 1) := by
        ring
      calc h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C
                    - h.C * (m x ^ h.β + 1))
          = h.C * (‖(fun i => Du i x)‖ ^ h.α / h.C)
              - h.C * (h.C * (m x ^ h.β + 1)) := by ring
        _ = ‖(fun i => Du i x)‖ ^ h.α
              - h.C ^ 2 * (m x ^ h.β + 1) := by rw [hcancel, hsq]
    rw [heq1] at hmul
    linarith
  -- HJB: H ≤ V - u.
  have hHJB' : H x (fun i => Du i x) (m x) ≤ V x - u x := by linarith
  have hCH_le : h.C * H x (fun i => Du i x) (m x) ≤ h.C * (V x - u x) :=
    mul_le_mul_of_nonneg_left hHJB' hC_nn
  have hCVu : h.C * (V x - u x) ≤ h.C * |V x| + h.C * |u x| := by
    have h1 : h.C * V x ≤ h.C * |V x| := mul_le_mul_of_nonneg_left hVabs hC_nn
    have h2 : h.C * (-u x) ≤ h.C * |u x| := mul_le_mul_of_nonneg_left hUabs hC_nn
    have heq : h.C * (V x - u x) = h.C * V x + h.C * (-u x) := by ring
    linarith
  have hstep :
      ‖(fun i => Du i x)‖ ^ h.α ≤
        h.C * |V x| + h.C * |u x| + h.C ^ 2 * (m x ^ h.β) + h.C ^ 2 := by
    have : h.C ^ 2 * (m x ^ h.β + 1) =
              h.C ^ 2 * (m x ^ h.β) + h.C ^ 2 := by ring
    linarith
  have hsum_nn : (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hKge_C : h.C ≤ h.C + h.C ^ 2 := by linarith
  have hKge_C2 : h.C ^ 2 ≤ h.C + h.C ^ 2 := by linarith
  have hK_nn : (0 : ℝ) ≤ h.C + h.C ^ 2 := by linarith
  have h_Vbound : h.C * |V x| ≤ (h.C + h.C ^ 2) * |V x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Ubound : h.C * |u x| ≤ (h.C + h.C ^ 2) * |u x| :=
    mul_le_mul_of_nonneg_right hKge_C (abs_nonneg _)
  have h_Mbound : h.C ^ 2 * (m x ^ h.β) ≤ (h.C + h.C ^ 2) * (m x ^ h.β) :=
    mul_le_mul_of_nonneg_right hKge_C2 hmβ_nn
  have h_Cbound : h.C ^ 2 ≤ (h.C + h.C ^ 2) * 1 := by linarith
  have hRHS_eq : (h.C + h.C ^ 2) * (m x ^ h.β + |u x| + |V x| + 1)
                  = (h.C + h.C ^ 2) * (m x ^ h.β)
                    + (h.C + h.C ^ 2) * |u x|
                    + (h.C + h.C ^ 2) * |V x|
                    + (h.C + h.C ^ 2) * 1 := by ring
  linarith

/-- **Paper eq. `eq:Duepsiabove`** (`Source/FGU-monotone_revised.tex`,
line 1253).

Pointwise upper bound on `‖Du_ε‖^{γ̄}` derived from the unraised bound
`apriori_Du_alpha_pointwise` by raising to the power `β̄' = γ̄/α`. The
exponent identities `α · β̄' = γ̄` and `β · β̄' = β̄` are used to rewrite
both sides of the inequality. -/
theorem apriori_Du_pointwise_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β ≤
          C * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + 1) := by
  -- Unraised bound from `apriori_Du_alpha_pointwise`.
  have hα_pointwise := apriori_Du_alpha_pointwise (h := h.toCongestionAprioriPowerData) V Du m u hHJB hMpos
  -- Useful facts about exponents.
  have hβ_pos : 0 < h.β := h.hβ
  have hβ_ne : h.β ≠ 0 := ne_of_gt hβ_pos
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_nn : (0 : ℝ) ≤ h.α := hα_pos.le
  -- β̄' = (β + 1)/β > 1, in particular ≥ 1, in particular > 0.
  have hβ' : 1 < betaBar' h.β := one_lt_betaBar' h.β hβ_pos
  have hβ'_ge_one : (1 : ℝ) ≤ betaBar' h.β := hβ'.le
  have hβ'_pos : 0 < betaBar' h.β := lt_trans zero_lt_one hβ'
  have hβ'_nn : (0 : ℝ) ≤ betaBar' h.β := hβ'_pos.le
  -- Identity: α · β̄' = γ̄.
  have hidα : h.α * betaBar' h.β = gammaBar h.α h.β :=
    (gammaBar_eq_alpha_mul_betaBar' h.α h.β hβ_ne).symm
  -- Identity: β · β̄' = β̄.
  have hidβ : h.β * betaBar' h.β = betaBar h.β := by
    unfold betaBar betaBar'
    field_simp
  -- Constant K = h.C + h.C^2 ≥ 0.
  set K : ℝ := h.C + h.C ^ 2 with hK_def
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hK_nn : 0 ≤ K := by
    have : 0 ≤ h.C ^ 2 := by positivity
    simp [hK_def]; linarith
  -- Final constant: C := K^β̄' · 4^β̄'.
  set C : ℝ := K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β with hC_def
  have hKβ'_nn : (0 : ℝ) ≤ K ^ betaBar' h.β :=
    Real.rpow_nonneg hK_nn _
  have h4β'_nn : (0 : ℝ) ≤ (4 : ℝ) ^ betaBar' h.β :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _
  have hC_nn' : 0 ≤ C := mul_nonneg hKβ'_nn h4β'_nn
  refine ⟨C, hC_nn', ?_⟩
  filter_upwards [hα_pointwise, hMpos] with x hx hxm
  -- We have hx : ‖Du x‖^α ≤ K * (m^β + |u| + |V| + 1).
  -- Raise both sides to the power β̄'.
  have hLHS_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hsum_nn :
      (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm.le _
    have h2 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hRHS_nn :
      (0 : ℝ) ≤ K * (m x ^ h.β + |u x| + |V x| + 1) :=
    mul_nonneg hK_nn hsum_nn
  -- Step A: raise hx to the β̄'.
  have hraised :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β ≤
        (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β :=
    Real.rpow_le_rpow hLHS_nn hx hβ'_nn
  -- LHS: (‖p‖^α)^β̄' = ‖p‖^(α·β̄') = ‖p‖^γ̄.
  have hLHS_rewrite :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β =
        ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β := by
    rw [← Real.rpow_mul (norm_nonneg _) h.α (betaBar' h.β)]
    rw [hidα]
  -- RHS: (K * S)^β̄' = K^β̄' * S^β̄' where S = m^β + |u| + |V| + 1.
  have hRHS_split :
      (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β =
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
    Real.mul_rpow hK_nn hsum_nn
  -- Bound S^β̄' ≤ 4^β̄' * ((m^β)^β̄' + |u|^β̄' + |V|^β̄' + 1^β̄').
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm.le _
  have hSpow :
      (m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β ≤
        (4 : ℝ) ^ betaBar' h.β *
          ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β) :=
    four_add_rpow_le_four_rpow_mul hmβ_nn (abs_nonneg _) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1) hβ'_nn
  -- Simplify: (m^β)^β̄' = m^(β·β̄') = m^β̄, and 1^β̄' = 1.
  have hmβ_id : (m x ^ h.β) ^ betaBar' h.β = m x ^ betaBar h.β := by
    rw [← Real.rpow_mul hxm.le h.β (betaBar' h.β)]
    rw [hidβ]
  have h1pow : (1 : ℝ) ^ betaBar' h.β = 1 := Real.one_rpow _
  -- Now assemble.
  have hKβ' : (0 : ℝ) ≤ K ^ betaBar' h.β := hKβ'_nn
  have hRHS_bound :
      K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
        C * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by
    have hstep1 :
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
          K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β)) :=
      mul_le_mul_of_nonneg_left hSpow hKβ'
    -- Rewrite using hmβ_id and h1pow.
    rw [hmβ_id, h1pow] at hstep1
    -- LHS of goal = C * (...) where C = K^β̄' * 4^β̄'.
    have hCeq : C = K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β := hC_def
    calc K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β)
        ≤ K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + 1)) := hstep1
      _ = (K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β) *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by ring
      _ = C * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by rw [hCeq]
  -- Combine: LHS ≤ raised inequality ≤ bound.
  calc ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
      = (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β := hLHS_rewrite.symm
    _ ≤ (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β := hraised
    _ = K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
        hRHS_split
    _ ≤ C * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := hRHS_bound

/-! ### Sanity check for `apriori_Du_pointwise_bound` -/

/-- **Unit test**: in the trivial setting `Du = 0, V = 0, u = 0, m ≡ 1`, the
hypothesis HJB reduces to `H x 0 1 ≤ 0` a.e. Given that hypothesis (and
`m ≡ 1 > 0`), `apriori_Du_pointwise_bound` produces a witness constant
satisfying the pointwise inequality. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
              (fun _ : Fin d → ℝ => (0 : ℝ)) x +
                  H x (fun _ : Fin d => (0 : ℝ))
                      ((fun _ : Fin d → ℝ => (1 : ℝ)) x) -
                  (fun _ : Fin d → ℝ => (0 : ℝ)) x ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
        ‖fun (_ : Fin d) => (0 : ℝ)‖ ^ gammaBar h.α h.β ≤
          C * (((fun _ : Fin d → ℝ => (1 : ℝ)) x) ^ betaBar h.β
                + |(fun _ : Fin d → ℝ => (0 : ℝ)) x| ^ betaBar' h.β
                + |(fun _ : Fin d → ℝ => (0 : ℝ)) x| ^ betaBar' h.β + 1) := by
  refine apriori_Du_pointwise_bound (h := h) (V := fun _ => (0 : ℝ))
      (Du := fun _ _ => (0 : ℝ)) (m := fun _ => (1 : ℝ))
      (u := fun _ => (0 : ℝ)) ?_ ?_
  · -- HJB hypothesis: matches `hHJB` after beta reduction.
    exact hHJB
  · exact Filter.Eventually.of_forall (fun _ => (zero_lt_one : (0 : ℝ) < 1))

/-! ## Integrated pointwise `‖Du_ε‖^{γ̄}` bound (paper line 1256)

This integrates `apriori_Du_pointwise_bound` (paper eq. `eq:Duepsiabove`,
line 1253) over the unit cube to obtain a control of `∫ ‖Du_ε‖^{γ̄}` by a
linear combination of `∫ m_ε^{β̄}`, `∫ |u_ε|^{β̄'}`, `∫ |V|^{β̄'}` and the
cube volume. The constant comes straight from the pointwise lemma and is
therefore ε-independent.

This is the "integrate `eq:Duepsiabove` over `𝕋^d`" step the paper performs
at line 1256, prior to applying the Lp inclusion `L^{γ̄} ↪ L^{β̄'}` and the
Poincaré–Wirtinger inequality.
-/

/-- **Integrated form of paper eq. `eq:Duepsiabove`**
(`Source/FGU-monotone_revised.tex`, line 1256).

Integrating the pointwise bound `apriori_Du_pointwise_bound` over the unit
cube gives a constant `C₁ ≥ 0` (ε-independent) such that
```
∫ ‖Du_ε x‖^{γ̄} dx
  ≤ C₁ · ( ∫ m_ε^{β̄} + ∫ |u_ε|^{β̄'} + ∫ |V|^{β̄'} + vol(UnitCube d) ).
```

The hypotheses are those of `apriori_Du_pointwise_bound` plus integrability
of `‖Du‖^{γ̄}`, `m^{β̄}`, `|u|^{β̄'}`, and `|V|^{β̄'}` on the cube. -/
theorem apriori_Du_integrated_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hDu_int : Integrable (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
                 (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable (fun x => m x ^ betaBar h.β)
                    (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable (fun x => |u x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable (fun x => |V x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d))) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
        C₁ *
          ((∫ x in UnitCube d, m x ^ betaBar h.β
              ∂(volume : Measure (Fin d → ℝ)))
            + (∫ x in UnitCube d, |u x| ^ betaBar' h.β
                ∂(volume : Measure (Fin d → ℝ)))
            + (∫ x in UnitCube d, |V x| ^ betaBar' h.β
                ∂(volume : Measure (Fin d → ℝ)))
            + (volume (UnitCube (d := d))).toReal) := by
  -- Extract the pointwise bound and its constant.
  obtain ⟨C₁, hC₁_nn, hpoint⟩ :=
    apriori_Du_pointwise_bound (h := h) V Du m u hHJB hMpos
  refine ⟨C₁, hC₁_nn, ?_⟩
  -- Cube finiteness.
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have hμfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  -- Abbreviations for the four integrals on the RHS.
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  -- Step 1: setIntegral_mono of the pointwise bound.
  -- RHS of pointwise = C₁ * (m^β̄ + |u|^β̄' + |V|^β̄' + 1).
  set g : (Fin d → ℝ) → ℝ :=
    fun x => C₁ * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                    + |V x| ^ betaBar' h.β + 1) with hg_def
  -- Integrability of `g`.
  have hone_int : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
  have hsum1 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hMbeta_int.add hUbetap_int
  have hsum2 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hsum1.add hVbetap_int
  have hsum3 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β + 1)
      (volume.restrict (UnitCube d)) := hsum2.add hone_int
  have hg_int : Integrable g (volume.restrict (UnitCube d)) :=
    hsum3.const_mul C₁
  -- Apply `setIntegral_mono_ae_restrict`.
  have hint_le :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hDu_int hg_int hpoint
  -- Step 2: Compute ∫ g.
  -- ∫ g = C₁ * ∫ (m^β̄ + |u|^β̄' + |V|^β̄' + 1)
  --     = C₁ * (Im + Iu + Iv + vol).
  have h_int_g_eq :
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ))
        = C₁ * (Im + Iu + Iv + vol) := by
    rw [hg_def]
    rw [integral_const_mul]
    -- Now reduce the inner integral.
    have hinner_eq :
        ∫ x in UnitCube d,
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = Im + Iu + Iv + vol := by
      rw [integral_add hsum2 hone_int]
      rw [integral_add hsum1 hVbetap_int]
      rw [integral_add hMbeta_int hUbetap_int]
      -- ∫ 1 = vol.
      have hone_int_eq :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int_eq]
    rw [hinner_eq]
  -- Step 3: assemble.
  calc ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ))
      ≤ ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := hint_le
    _ = C₁ * (Im + Iu + Iv + vol) := h_int_g_eq
    _ = C₁ * (Im + Iu + Iv + vol) := rfl

/-! ### Sanity check for `apriori_Du_integrated_bound` -/

/-- **Unit test**: in the trivial setting (`Du = 0, V = 0, u = 0, m ≡ 1`)
the lemma applies, given that the four integrability hypotheses are
trivially satisfied (constant integrands on the finite-measure cube). -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
              (fun _ : Fin d → ℝ => (0 : ℝ)) x +
                  H x (fun _ : Fin d => (0 : ℝ))
                      ((fun _ : Fin d → ℝ => (1 : ℝ)) x) -
                  (fun _ : Fin d → ℝ => (0 : ℝ)) x ≤ 0) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      ∫ x in UnitCube d,
          ‖(fun (_ : Fin d) => (0 : ℝ))‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
        C₁ *
          ((∫ x in UnitCube d,
              ((fun _ : Fin d → ℝ => (1 : ℝ)) x) ^ betaBar h.β
              ∂(volume : Measure (Fin d → ℝ)))
            + (∫ x in UnitCube d,
                |(fun _ : Fin d → ℝ => (0 : ℝ)) x| ^ betaBar' h.β
                ∂(volume : Measure (Fin d → ℝ)))
            + (∫ x in UnitCube d,
                |(fun _ : Fin d → ℝ => (0 : ℝ)) x| ^ betaBar' h.β
                ∂(volume : Measure (Fin d → ℝ)))
            + (volume (UnitCube (d := d))).toReal) := by
  -- Cube is a finite-measure set; constant integrands are integrable.
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have hμfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  refine apriori_Du_integrated_bound (h := h) (V := fun _ => (0 : ℝ))
      (Du := fun _ _ => (0 : ℝ)) (m := fun _ => (1 : ℝ))
      (u := fun _ => (0 : ℝ)) hHJB ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun _ => (zero_lt_one : (0 : ℝ) < 1))
  · -- Integrable (fun x => ‖0‖^γ̄): constant integrand.
    exact integrable_const _
  · exact integrable_const _
  · exact integrable_const _
  · exact integrable_const _

/-! ## Closed `L^{γ̄}` bound on `Du_ε` (paper eq. `eq:Duepsi.bound`, line 1265)

The paper closes the chain of estimates as follows: combine the integrated
form of `eq:Duepsiabove` with `eq:mepsi.bound` and `eq:poincare-torus` to
get an inequality of the shape
```
‖Du_ε‖_{L^{γ̄}}^{γ̄} ≤ A · ‖Du_ε‖_{L^{γ̄}}^{β̄'} + B
```
with `γ̄ > β̄'` (since `α > 1`). Young absorption then yields an explicit
ε-independent bound on `‖Du_ε‖_{L^{γ̄}}` (eq. `eq:Duepsi.bound`).

This section delivers the *scalar Young-absorption step*: given a
nonnegative real `T` (interpreted as `‖Du_ε‖_{L^{γ̄}}`) satisfying
`T^q ≤ A · T^r + B` with `q > r ≥ 0`, `A, B ≥ 0`, we exhibit an explicit
nonnegative bound on `T`. The follow-up task
`infra-P4-apriori-Du-bound-closed-assemble` plugs in the actual chain
inputs from `apriori_Du_integrated_bound`, `apriori_m_bound`,
`apriori_uepsi_Lp`, and the `L^{γ̄} ↪ L^{β̄'}` inclusion. -/

/-- **Young absorption — scalar closing step for paper eq. `eq:Duepsi.bound`**.

Given nonnegative reals `T, A, B`, exponents `q > r ≥ 0`, and the
inequality
```
T ^ q ≤ A * T ^ r + B,
```
we have the explicit bound
```
T ≤ (2 * A) ^ (1 / (q - r)) + (2 * B) ^ (1 / q).
```

This is the Young-style absorption argument the paper invokes "because
`γ̄ > β̄'`" at line 1268: split into the two cases according to whether
`A · T^r ≥ B` (then `T^q ≤ 2 A T^r`, hence `T^{q-r} ≤ 2A`) or `A · T^r <
B` (then `T^q < 2B`). -/
theorem apriori_Du_bound_closed
    (T A B q r : ℝ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hrq : r < q)
    (hbound : T ^ q ≤ A * T ^ r + B) :
    T ≤ (2 * A) ^ (1 / (q - r)) + (2 * B) ^ (1 / q) := by
  have hq_pos : 0 < q := lt_of_le_of_lt hr hrq
  have hqr_pos : 0 < q - r := by linarith
  have h2A_nn : (0 : ℝ) ≤ 2 * A := by positivity
  have h2B_nn : (0 : ℝ) ≤ 2 * B := by positivity
  have hT2A_nn : (0 : ℝ) ≤ (2 * A) ^ (1 / (q - r)) :=
    Real.rpow_nonneg h2A_nn _
  have hT2B_nn : (0 : ℝ) ≤ (2 * B) ^ (1 / q) :=
    Real.rpow_nonneg h2B_nn _
  by_cases hcase : A * T ^ r ≥ B
  · -- Case 1: `A T^r ≥ B`. Then `T^q ≤ 2 (A T^r)`.
    have hT_pow_q_le : T ^ q ≤ 2 * (A * T ^ r) := by linarith
    rcases eq_or_lt_of_le hT with hT0 | hT_pos
    · -- T = 0: bound is trivial.
      have hT_eq : T = 0 := hT0.symm
      rw [hT_eq]
      exact add_nonneg hT2A_nn hT2B_nn
    · -- T > 0. Then T^r > 0; cancel.
      have hTr_pos : (0 : ℝ) < T ^ r := Real.rpow_pos_of_pos hT_pos _
      have hpow_split : T ^ q = T ^ r * T ^ (q - r) := by
        rw [← Real.rpow_add hT_pos]
        congr 1; ring
      have hkey : T ^ r * T ^ (q - r) ≤ T ^ r * (2 * A) := by
        calc T ^ r * T ^ (q - r)
            = T ^ q := hpow_split.symm
          _ ≤ 2 * (A * T ^ r) := hT_pow_q_le
          _ = T ^ r * (2 * A) := by ring
      have hineq : T ^ (q - r) ≤ 2 * A :=
        (mul_le_mul_iff_of_pos_left hTr_pos).mp hkey
      have hT_pow_qr_nn : (0 : ℝ) ≤ T ^ (q - r) :=
        Real.rpow_nonneg hT _
      have hpow_le :
          (T ^ (q - r)) ^ (1 / (q - r)) ≤ (2 * A) ^ (1 / (q - r)) :=
        Real.rpow_le_rpow hT_pow_qr_nn hineq (by positivity)
      have hT_recover : (T ^ (q - r)) ^ (1 / (q - r)) = T := by
        rw [← Real.rpow_mul hT]
        have hsimp : (q - r) * (1 / (q - r)) = 1 := by
          field_simp
        rw [hsimp]; exact Real.rpow_one T
      have hT_le_first : T ≤ (2 * A) ^ (1 / (q - r)) := by
        rw [← hT_recover]; exact hpow_le
      linarith
  · -- Case 2: `A T^r < B`. Then `T^q < 2B`.
    push_neg at hcase
    have hT_pow_q_le : T ^ q ≤ 2 * B := by linarith
    have hT_pow_q_nn : (0 : ℝ) ≤ T ^ q := Real.rpow_nonneg hT _
    have hpow_le : (T ^ q) ^ (1 / q) ≤ (2 * B) ^ (1 / q) :=
      Real.rpow_le_rpow hT_pow_q_nn hT_pow_q_le (by positivity)
    have hT_recover : (T ^ q) ^ (1 / q) = T := by
      rw [← Real.rpow_mul hT]
      have hsimp : q * (1 / q) = 1 := by
        field_simp
      rw [hsimp]; exact Real.rpow_one T
    have hT_le_second : T ≤ (2 * B) ^ (1 / q) := by
      rw [← hT_recover]; exact hpow_le
    linarith

/-- **Closed-form bound packaging** for paper eq. `eq:Duepsi.bound`.

Repackages `apriori_Du_bound_closed` as an existential producing an
ε-independent constant `C ≥ 0` with `T ≤ C`. This is the form most
convenient for the downstream aggregator
`infra-P4-apriori-Du-bound-closed-assemble`. -/
theorem apriori_Du_bound_closed_exists
    (T A B q r : ℝ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hrq : r < q)
    (hbound : T ^ q ≤ A * T ^ r + B) :
    ∃ C : ℝ, 0 ≤ C ∧ T ≤ C := by
  refine ⟨(2 * A) ^ (1 / (q - r)) + (2 * B) ^ (1 / q), ?_,
          apriori_Du_bound_closed T A B q r hT hA hB hr hrq hbound⟩
  have h2A_nn : (0 : ℝ) ≤ 2 * A := by positivity
  have h2B_nn : (0 : ℝ) ≤ 2 * B := by positivity
  exact add_nonneg (Real.rpow_nonneg h2A_nn _) (Real.rpow_nonneg h2B_nn _)

/-! ### Sanity check for `apriori_Du_bound_closed` -/

/-- **Unit test**: in the trivial setting `T = 0, A = 1, B = 1`, the bound
holds. -/
example (q r : ℝ) (hr : 0 ≤ r) (hrq : r < q) :
    (0 : ℝ) ≤ (2 * (1 : ℝ)) ^ (1 / (q - r)) + (2 * (1 : ℝ)) ^ (1 / q) := by
  have hq_pos : 0 < q := lt_of_le_of_lt hr hrq
  have hbound : (0 : ℝ) ^ q ≤ 1 * (0 : ℝ) ^ r + 1 := by
    have h1 : (0 : ℝ) ^ q = 0 := Real.zero_rpow (ne_of_gt hq_pos)
    rw [h1]
    have h2 : (0 : ℝ) ≤ 1 * (0 : ℝ) ^ r + 1 := by
      have hr_pow_nn : (0 : ℝ) ≤ (0 : ℝ) ^ r := Real.rpow_nonneg le_rfl _
      linarith
    exact h2
  exact apriori_Du_bound_closed 0 1 1 q r le_rfl (by norm_num) (by norm_num)
    hr hrq hbound

/-! ## Closed-form pointwise constant `aprioriDuPointwiseConst`

This is the explicit witness produced by `apriori_Du_pointwise_bound`:
`C := (h.C + h.C^2)^{β̄'(β)} * 4^{β̄'(β)}`. Exposing it lets us thread an
ε-independent closed-form constant through `apriori_Du_integrated_bound`
and ultimately through the assembled bound on `∫ ‖Du‖^{γ̄}`.

This section feeds task `infra-P5-theorem1-phase-D-DuGammaBar-uniform`.
-/

/-- **Closed-form pointwise constant** for `apriori_Du_pointwise_bound`.

`aprioriDuPointwiseConst h := (h.C + h.C^2)^{β̄'(β)} * 4^{β̄'(β)}`. -/
def aprioriDuPointwiseConst
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) : ℝ :=
  (h.C + h.C ^ 2) ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β

/-- Non-negativity of `aprioriDuPointwiseConst`. -/
theorem aprioriDuPointwiseConst_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) :
    0 ≤ aprioriDuPointwiseConst h := by
  unfold aprioriDuPointwiseConst
  have hC_pos : 0 < h.C := h.hC
  have hK_nn : (0 : ℝ) ≤ h.C + h.C ^ 2 := by
    have : 0 ≤ h.C ^ 2 := by positivity
    linarith
  exact mul_nonneg
    (Real.rpow_nonneg hK_nn _)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)

/-- **Closed-form variant of `apriori_Du_pointwise_bound`.**

Same conclusion as `apriori_Du_pointwise_bound`, but with the witness
constant exposed as `aprioriDuPointwiseConst h`. -/
theorem apriori_Du_pointwise_bound_closed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β ≤
        aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := by
  -- Reproduce the proof of `apriori_Du_pointwise_bound`, but using the
  -- explicit closed-form constant.
  have hα_pointwise := apriori_Du_alpha_pointwise (h := h) V Du m u hHJB hMpos
  have hβ_pos : 0 < h.β := h.hβ
  have hβ_ne : h.β ≠ 0 := ne_of_gt hβ_pos
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hα_nn : (0 : ℝ) ≤ h.α := hα_pos.le
  have hβ' : 1 < betaBar' h.β := one_lt_betaBar' h.β hβ_pos
  have hβ'_pos : 0 < betaBar' h.β := lt_trans zero_lt_one hβ'
  have hβ'_nn : (0 : ℝ) ≤ betaBar' h.β := hβ'_pos.le
  have hidα : h.α * betaBar' h.β = gammaBar h.α h.β :=
    (gammaBar_eq_alpha_mul_betaBar' h.α h.β hβ_ne).symm
  have hidβ : h.β * betaBar' h.β = betaBar h.β := by
    unfold betaBar betaBar'; field_simp
  -- Constant K = h.C + h.C^2 ≥ 0.
  set K : ℝ := h.C + h.C ^ 2 with hK_def
  have hC_pos : 0 < h.C := h.hC
  have hC_nn : (0 : ℝ) ≤ h.C := hC_pos.le
  have hK_nn : 0 ≤ K := by
    have : 0 ≤ h.C ^ 2 := by positivity
    simp [hK_def]; linarith
  -- The closed-form constant `C := K^β̄' * 4^β̄'`.
  have hCeq : aprioriDuPointwiseConst h
                = K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β := by
    unfold aprioriDuPointwiseConst; rfl
  have hKβ'_nn : (0 : ℝ) ≤ K ^ betaBar' h.β :=
    Real.rpow_nonneg hK_nn _
  have h4β'_nn : (0 : ℝ) ≤ (4 : ℝ) ^ betaBar' h.β :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _
  filter_upwards [hα_pointwise, hMpos] with x hx hxm
  have hLHS_nn : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^ h.α :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hsum_nn :
      (0 : ℝ) ≤ m x ^ h.β + |u x| + |V x| + 1 := by
    have h1 : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm.le _
    have h2 : (0 : ℝ) ≤ |u x| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |V x| := abs_nonneg _
    linarith
  have hraised :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β ≤
        (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β :=
    Real.rpow_le_rpow hLHS_nn hx hβ'_nn
  have hLHS_rewrite :
      (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β =
        ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β := by
    rw [← Real.rpow_mul (norm_nonneg _) h.α (betaBar' h.β)]
    rw [hidα]
  have hRHS_split :
      (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β =
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
    Real.mul_rpow hK_nn hsum_nn
  have hmβ_nn : (0 : ℝ) ≤ m x ^ h.β := Real.rpow_nonneg hxm.le _
  have hSpow :
      (m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β ≤
        (4 : ℝ) ^ betaBar' h.β *
          ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β) :=
    four_add_rpow_le_four_rpow_mul hmβ_nn (abs_nonneg _) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1) hβ'_nn
  have hmβ_id : (m x ^ h.β) ^ betaBar' h.β = m x ^ betaBar h.β := by
    rw [← Real.rpow_mul hxm.le h.β (betaBar' h.β)]; rw [hidβ]
  have h1pow : (1 : ℝ) ^ betaBar' h.β = 1 := Real.one_rpow _
  have hRHS_bound :
      K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
        aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := by
    have hstep1 :
        K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) ≤
          K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              ((m x ^ h.β) ^ betaBar' h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + (1 : ℝ) ^ betaBar' h.β)) :=
      mul_le_mul_of_nonneg_left hSpow hKβ'_nn
    rw [hmβ_id, h1pow] at hstep1
    calc K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β)
        ≤ K ^ betaBar' h.β *
            ((4 : ℝ) ^ betaBar' h.β *
              (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                + |V x| ^ betaBar' h.β + 1)) := hstep1
      _ = (K ^ betaBar' h.β * (4 : ℝ) ^ betaBar' h.β) *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by ring
      _ = aprioriDuPointwiseConst h *
            (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
              + |V x| ^ betaBar' h.β + 1) := by rw [hCeq]
  calc ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
      = (‖(fun i => Du i x)‖ ^ h.α) ^ betaBar' h.β := hLHS_rewrite.symm
    _ ≤ (K * (m x ^ h.β + |u x| + |V x| + 1)) ^ betaBar' h.β := hraised
    _ = K ^ betaBar' h.β * ((m x ^ h.β + |u x| + |V x| + 1) ^ betaBar' h.β) :=
        hRHS_split
    _ ≤ aprioriDuPointwiseConst h *
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1) := hRHS_bound

/-- **Closed-form variant of `apriori_Du_integrated_bound`.**

Same conclusion as `apriori_Du_integrated_bound`, but with the witness
constant exposed as `aprioriDuPointwiseConst h`. -/
theorem apriori_Du_integrated_bound_closed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hDu_int : Integrable (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
                 (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable (fun x => m x ^ betaBar h.β)
                    (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable (fun x => |u x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable (fun x => |V x| ^ betaBar' h.β)
                     (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuPointwiseConst h *
        ((∫ x in UnitCube d, m x ^ betaBar h.β
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |u x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, |V x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + (volume (UnitCube (d := d))).toReal) := by
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hpoint :=
    apriori_Du_pointwise_bound_closed (h := h) V Du m u hHJB hMpos
  -- Cube finiteness.
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have hμfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set g : (Fin d → ℝ) → ℝ :=
    fun x => C₁ * (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                    + |V x| ^ betaBar' h.β + 1) with hg_def
  have hone_int : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
  have hsum1 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hMbeta_int.add hUbetap_int
  have hsum2 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β)
      (volume.restrict (UnitCube d)) := hsum1.add hVbetap_int
  have hsum3 : Integrable
      (fun x => m x ^ betaBar h.β + |u x| ^ betaBar' h.β
                  + |V x| ^ betaBar' h.β + 1)
      (volume.restrict (UnitCube d)) := hsum2.add hone_int
  have hg_int : Integrable g (volume.restrict (UnitCube d)) :=
    hsum3.const_mul C₁
  have hint_le :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hDu_int hg_int hpoint
  have h_int_g_eq :
      ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ))
        = C₁ * (Im + Iu + Iv + vol) := by
    rw [hg_def, integral_const_mul]
    have hinner_eq :
        ∫ x in UnitCube d,
          (m x ^ betaBar h.β + |u x| ^ betaBar' h.β
            + |V x| ^ betaBar' h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = Im + Iu + Iv + vol := by
      rw [integral_add hsum2 hone_int]
      rw [integral_add hsum1 hVbetap_int]
      rw [integral_add hMbeta_int hUbetap_int]
      have hone_int_eq :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int_eq]
    rw [hinner_eq]
  calc ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ))
      ≤ ∫ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := hint_le
    _ = C₁ * (Im + Iu + Iv + vol) := h_int_g_eq

/-! ## Closed-form aggregate constant `aprioriDuBoundClosed`

Closed-form witness for `apriori_Du_bound`. Combines the closed-form
sub-witnesses `aprioriDuPointwiseConst h` (for `C₁`),
`aprioriMBoundClosed h Vbound Vint_bound` (for `M`), and
`aprioriUBoundClosed (d := d) h Vbound Vint_bound` (for `Cu`) with the
exponent bookkeeping `r := γ̄⁻¹ * β̄'` and the scalar Young absorption
`apriori_Du_bound_closed`.

This section feeds task `infra-P5-theorem1-phase-D-DuGammaBar-uniform`.
-/

/-- **Closed-form witness for `apriori_Du_bound`**.

The constant `C` produced by `apriori_Du_bound` is
```
(2 * A) ^ (1 / (1 - r)) + (2 * B)
```
where, with `βp := β̄'(β)`, `γ := γ̄(α,β)`, `r := γ⁻¹ * βp`,
`C₁ := aprioriDuPointwiseConst h`,
`M  := aprioriMBoundClosed h Vbound Vint_bound`,
`Cu := aprioriUBoundClosed (d := d) h Vbound Vint_bound`,
```
A := C₁ * (Cu^βp * 2^βp * d^βp)
B := C₁ * (M + Cu^βp * 2^βp + Vβp_bound + 1)
```

This value is ε-independent: it depends only on
`(d, h, Vbound, Vint_bound, Vβp_bound)`. -/
def aprioriDuBoundClosed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Vbound Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C₁ : ℝ := aprioriDuPointwiseConst h.toCongestionAprioriPowerData
  let M  : ℝ := aprioriMBoundClosed h Vbound Vint_bound
  let Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound
  let βp : ℝ := betaBar' h.β
  let γ  : ℝ := gammaBar h.α h.β
  let A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp)
  let B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1)
  let r  : ℝ := γ⁻¹ * βp
  (2 * A) ^ (1 / (1 - r)) + (2 * B)

/-- Non-negativity of `aprioriDuBoundClosed`. The closed expression is a
sum of two terms, the first an `rpow` of a non-negative base (always ≥ 0),
and the second `2 * B` where `B` is non-negative under the consistency
constraint that `Vβp_bound` upper-bounds a non-negative integral. To keep
the lemma free of consistency hypotheses, we observe that `2 * B ≥ 0` need
not hold unconditionally; however, the **first** term `(2*A)^{...} ≥ 0`
holds unconditionally, and the assembled bound `apriori_Du_bound_closed_form`
gives the bound on the LHS regardless. We provide a conditional
non-negativity lemma keyed on `0 ≤ Vβp_bound`. -/
theorem aprioriDuBoundClosed_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  unfold aprioriDuBoundClosed
  set C₁ : ℝ := aprioriDuPointwiseConst h.toCongestionAprioriPowerData with hC₁_def
  set M  : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hCu_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set γ  : ℝ := gammaBar h.α h.β with hγ_def
  set A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  set r  : ℝ := γ⁻¹ * βp with hr_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h.toCongestionAprioriPowerData
  have hM_nn : 0 ≤ M :=
    aprioriMBoundClosed_nn_of_Vint_nn h Vbound Vint_bound hVint_nn
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hβp_pos : 0 < βp :=
    lt_trans zero_lt_one (one_lt_betaBar' h.β h.hβ)
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hCuβp_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2βp_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdβp_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCuβp_nn h2βp_nn) hdβp_nn
  have h2A_nn : 0 ≤ 2 * A := by linarith
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have h1 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCuβp_nn h2βp_nn
    linarith
  have h2B_nn : 0 ≤ 2 * B := by linarith
  have hfirst_nn : 0 ≤ (2 * A) ^ (1 / (1 - r)) := Real.rpow_nonneg h2A_nn _
  linarith

/-- **Paper eq. `eq:Duepsi.bound`** (`Source/FGU-monotone_revised.tex`,
line 1265), closed-form variant.

Same hypotheses as `apriori_Du_bound`. Conclusion gives the bound with
the **closed-form witness** `aprioriDuBoundClosed h Vbound Vint_bound Vβp_bound`.

For the historical existential shape `∃ C ≥ 0, …`, see the wrapper
`apriori_Du_bound`. -/
theorem apriori_Du_bound_closed_form
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  -- Abbreviations matching the existential proof of `apriori_Du_bound`.
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  -- Step 1: closed-form integrated bound.
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h.toCongestionAprioriPowerData with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h.toCongestionAprioriPowerData
  have hint_bound :=
    apriori_Du_integrated_bound_closed (h := h.toCongestionAprioriPowerData) V Du m u hHJB hMpos
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  -- Step 2: closed-form m bound.
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  -- Step 3: closed-form Poincaré bound.
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  -- The rest of the proof mirrors `apriori_Du_bound` line 3022 onward.
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  -- Define the closed-form A and B used in `aprioriDuBoundClosed`.
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hMpos] with x hxm
        exact Real.rpow_nonneg hxm.le _
      -- M ≥ Im ≥ 0.
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  -- Apply the scalar Young absorption lemma `apriori_Du_bound_closed` with
  -- `q := 1`, `r := r`. Note `T = T^1`.
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  -- Simplify `(2*B)^(1/1) = 2*B`.
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  -- Bridge to the closed-form witness.
  have hclosed_eq :
      aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed h Vbound Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

/-! ## Closed assembled `L^{γ̄}` bound on `Du_ε` (paper eq. `eq:Duepsi.bound`)

This section assembles `apriori_Du_bound_closed_exists` (the scalar Young
absorption lemma) with the chain inputs `apriori_Du_integrated_bound`,
`apriori_m_bound`, and `apriori_uepsi_Lp` plus the `L^{γ̄} ↪ L^{β̄'}`
inclusion to produce an ε-independent existential bound on the integral
`∫ ‖Du_ε‖^{γ̄}`.
-/

/-- **Paper eq. `eq:Duepsi.bound`** (`Source/FGU-monotone_revised.tex`,
line 1265), assembled form.

Under the hypothesis bundle of `apriori_uepsi_Lp` together with:
* the integrability hypotheses needed by `apriori_Du_integrated_bound`
  (i.e. `‖Du‖^γ̄`, `m^β̄`, `|u|^β̄'`, `|V|^β̄'` are all integrable on the cube);
* an a-priori `L^{β̄'}`-bound on `V`, namely `∫ |V|^{β̄'} ≤ Vβp_bound`;

there exists an ε-independent constant `C ≥ 0` such that
`∫_{UnitCube d} ‖(fun i => Du i x)‖^{γ̄} ≤ C`. -/
theorem apriori_Du_bound
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    -- Sobolev regularity required by `apriori_uepsi_Lp` at exponent γ̄.
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    -- Integrability hypotheses for `apriori_Du_integrated_bound`.
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    -- An a-priori `L^{β̄'}` bound on `V`.
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    -- `u ∈ L^{γ̄}` is needed for the Lᵖ inclusion to land in `L^{β̄'}`.
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ C := by
  -- Thin wrapper: delegate to the closed-form theorem
  -- `apriori_Du_bound_closed_form`. The witness constant is
  -- `aprioriDuBoundClosed h Vbound Vint_bound Vβp_bound`.
  refine ⟨aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound, ?_, ?_⟩
  · -- Non-negativity. Both `Vint_bound` and `Vβp_bound` upper-bound non-negative
    -- integrals, hence are themselves non-negative; we extract these here.
    have hVint_nn : 0 ≤ Vint_bound := by
      have h_int_abs_nn : 0 ≤ ∫ x in UnitCube d, |V x|
              ∂(volume : Measure (Fin d → ℝ)) := by
        apply integral_nonneg_of_ae
        refine Filter.Eventually.of_forall ?_
        intro x; exact abs_nonneg _
      linarith [le_trans h_int_abs_nn hVint]
    have hVβp_nn : 0 ≤ Vβp_bound := by
      have h_int_abs_nn : 0 ≤ ∫ x in UnitCube d, |V x| ^ betaBar' h.β
              ∂(volume : Measure (Fin d → ℝ)) := by
        apply integral_nonneg_of_ae
        refine Filter.Eventually.of_forall ?_
        intro x; exact Real.rpow_nonneg (abs_nonneg _) _
      linarith [le_trans h_int_abs_nn hVβp]
    exact aprioriDuBoundClosed_nn (d := d) h Vbound Vint_bound Vβp_bound
      hVint_nn hVβp_nn
  · exact apriori_Du_bound_closed_form (h := h) V Du m u epsTerms
      Vbound Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ

/-! ### Sanity check for `apriori_Du_bound` -/

/-- **Unit test**: an `example` exercising the assembled bound by direct
forwarding of the hypothesis bundle (cf. the `apriori_uepsi_Lp` example
pattern). -/
example
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ C :=
  apriori_Du_bound (h := h) V Du m u epsTerms Vbound Vint_bound Vβp_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint
    hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
    hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
    hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ

/-! ## Aggregate a priori bound — paper line 1269

Combine `apriori_m_bound`, `apriori_uepsi_Lp`, and `apriori_Du_bound` into
the headline bound

```
‖m_ε‖_{L^{β̄}}^{β̄} + ‖u_ε‖_{W^{1,γ̄}}^{γ̄} ≤ C
```

(constant `C` independent of ε). This corresponds to
`eq:apriori-simple.power.growth` (line 1196) and is the conclusion of
Theorem `thm:apriori-simple.power.growth`. We summarise the
`W^{1,γ̄}`-norm-to-the-γ̄ via the equivalent quantity
`(lpNormPer γ̄ u)^γ̄ + ∫ ‖Du‖^γ̄`. -/

/-- **Aggregate a priori bound** (paper line 1269,
`eq:apriori-simple.power.growth`).
Combines the m-, u- and Du-bounds into a single ε-independent bound on the
quantity
`∫ m^{β̄} + (lpNormPer γ̄ u)^γ̄ + ∫ ‖Du‖^γ̄`,
which is the `W^{1,γ̄}`-norm-to-the-γ̄ summary used in the paper. -/
theorem apriori_aggregate_bound
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, m x ^ betaBar h.β
          ∂(volume : Measure (Fin d → ℝ)))
        + lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u
            ^ gammaBar h.α h.β
        + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C := by
  -- Abbreviations.
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  -- Step 1: m-bound. Note `betaBar h.β = h.β + 1` definitionally.
  obtain ⟨M, hM_nn, hM_bound⟩ :=
    apriori_m_bound (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' :
      ∫ x in UnitCube d, m x ^ betaBar h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  -- Step 2: Du-bound. ∃ Cd ≥ 0, ∫ ‖Du‖^γ̄ ≤ Cd.
  obtain ⟨Cd, hCd_nn, hCd_bound⟩ :=
    apriori_Du_bound (h := h) V Du m u epsTerms Vbound Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  -- Step 3: Poincaré. ∃ Cu ≥ 0, lpNormPer p u ≤ Cu·(S + 1) with S := ∑ lpNormPer p (Du i).
  obtain ⟨Cu, hCu_nn, hu_pw⟩ :=
    apriori_uepsi_Lp (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  -- Positivity facts on γ.
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  -- Set T := ∫ ‖Du‖^γ̄, S := ∑ lpNormPer p (Du i).
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  -- Step 4: bound `S` via T (and hence Cd).
  -- Per-coord identity: lpNormPer p (Du i) ^ γ = ∫ |Du i|^γ̄.
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  -- Pointwise: |Du i x| ≤ ‖(fun j => Du j x)‖.
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  -- So lpNormPer p (Du i) ^ γ ≤ T ≤ Cd.
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ Cd := by
    intro i
    have h1 : lpNormPer p (Du i) ^ γ ≤ T := by
      rw [hDu_lp_γ i]; exact hDu_i_le i
    exact le_trans h1 hCd_bound
  -- And lpNormPer p (Du i) ≤ Cd^{1/γ}.
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  -- Sum: S ≤ d · Cd^{1/γ}.
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  -- Step 5: lpNormPer p u ≤ Cu · (d·Cd^{1/γ} + 1) =: U.
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have hCu_nn' : 0 ≤ Cu := hCu_nn
    have h1 : lpNormPer p u ≤ Cu * (S + 1) := hu_pw
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn'
    exact le_trans h1 h2
  -- Step 6: (lpNormPer p u)^γ ≤ U^γ.
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  -- Step 7: assemble the aggregate constant C := M + U^γ + Cd.
  have hUγ_nn : 0 ≤ U ^ γ := Real.rpow_nonneg hU_nn _
  refine ⟨M + U ^ γ + Cd, ?_, ?_⟩
  · -- Nonnegativity of the constant.
    have h1 : 0 ≤ M + U ^ γ := by linarith
    linarith
  · -- The aggregate inequality.
    have hsum_le :
        (∫ x in UnitCube d, m x ^ betaBar h.β
              ∂(volume : Measure (Fin d → ℝ)))
          + lpNormPer p u ^ γ
          + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
              ∂(volume : Measure (Fin d → ℝ)))
          ≤ M + U ^ γ + Cd := by
      have e1 : (∫ x in UnitCube d, m x ^ betaBar h.β
              ∂(volume : Measure (Fin d → ℝ))) ≤ M := hM_bound'
      have e2 : lpNormPer p u ^ γ ≤ U ^ γ := hLpu_γ_le
      have e3 : (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
              ∂(volume : Measure (Fin d → ℝ))) ≤ Cd := hCd_bound
      linarith
    -- Rewrite goal back into the named form.
    show (∫ x in UnitCube d, m x ^ betaBar h.β
            ∂(volume : Measure (Fin d → ℝ)))
          + lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u
              ^ gammaBar h.α h.β
          + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
              ∂(volume : Measure (Fin d → ℝ)))
            ≤ M + U ^ γ + Cd
    exact hsum_le

/-! ### Sanity check for `apriori_aggregate_bound` -/

/-- **Unit test**: an `example` exercising the aggregate bound by direct
forwarding of the hypothesis bundle. -/
example
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, m x ^ betaBar h.β
          ∂(volume : Measure (Fin d → ℝ)))
        + lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u
            ^ gammaBar h.α h.β
        + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C :=
  apriori_aggregate_bound (h := h) V Du m u epsTerms Vbound Vint_bound Vβp_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint
    hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
    hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
    hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ

/-! ## Headline theorem `thm:apriori-simple.power.growth`

`Source/FGU-monotone_revised.tex`, **lines 1190–1201**, eq.
`eq:apriori-simple.power.growth`. Paper statement:

> Under the assumptions of Theorem `thm:main-simple.power.growth`, let
> `(m_ε, u_ε) ∈ L^{β̄}(𝕋^d; ℝ^+_0) × W^{1,γ̄}(𝕋^d)` be given by Proposition
> `thm:strongAepsi`. Then
> `‖m_ε‖_{L^{β̄}(𝕋^d)}^{β̄} + ‖u_ε‖_{W^{1,γ̄}(𝕋^d)}^{γ̄} ≤ C`
> for a constant `C > 0` independent of `ε`.

The Lean encoding unfolds the Sobolev `W^{1,γ̄}`-norm-to-the-`γ̄` as the sum
`‖u‖_{L^{γ̄}}^{γ̄} + ∫ ‖Du‖^{γ̄}` (per `CONVENTIONS.md` §1, working with bare
periodic functions on `Fin d → ℝ` and integrals on `UnitCube d`). This matches
the conclusion of `apriori_aggregate_bound`.

The proof is a forwarding to `apriori_aggregate_bound`; the seven paper steps
`eq:uepsibelow → eq:uepsiabove → eq:mepsi.bound → mean bound →
eq:poincare-torus → eq:Duepsiabove → eq:Duepsi.bound` are encoded as the
seven `infra:P4-apriori-*` children that `apriori_aggregate_bound` invokes
internally. -/
theorem thm_apriori_simplePowerGrowth
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, m x ^ betaBar h.β
          ∂(volume : Measure (Fin d → ℝ)))
        + lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u
            ^ gammaBar h.α h.β
        + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C :=
  -- Aggregator combining the seven `infra:P4-apriori-*` children:
  --   eq:uepsibelow, eq:uepsiabove, eq:mepsi.bound, mean bound,
  --   eq:poincare-torus, eq:Duepsiabove, eq:Duepsi.bound.
  apriori_aggregate_bound (h := h) V Du m u epsTerms Vbound Vint_bound Vβp_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint
    hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
    hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
    hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ

/-! ### Sanity check for `thm_apriori_simplePowerGrowth` -/

/-- **Unit test**: a forwarding `example` exercising the headline theorem
`thm_apriori_simplePowerGrowth` (paper eq. `eq:apriori-simple.power.growth`,
line 1196). Identical hypothesis bundle as the underlying aggregator, just
plumbed through the paper-named entry point. -/
example
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, m x ^ betaBar h.β
          ∂(volume : Measure (Fin d → ℝ)))
        + lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u
            ^ gammaBar h.α h.β
        + (∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C :=
  thm_apriori_simplePowerGrowth (h := h) V Du m u epsTerms
    Vbound Vint_bound Vβp_bound
    hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
    hLB_int hMbeta_int hRHSbelow_int hVint
    hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
    hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
    hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ

/-! ## Closed-form aggregator constant `aprioriUniformConstantClosed`

This section delivers the explicit ε-independent closed-form witness
for the aggregate bound, glueing the three closed-form constants
`aprioriMBoundClosed`, `aprioriUBoundClosed`, and `aprioriDuBoundClosed`
into a single value.

The constant has shape `M + U^γ̄ + d * Cd` where
* `M  := aprioriMBoundClosed h Vbound Vint_bound`,
* `Cu := aprioriUBoundClosed h Vbound Vint_bound`,
* `Cd := aprioriDuBoundClosed h Vbound Vint_bound Vβp_bound`,
* `U  := Cu * (d * Cd^{1/γ̄} + 1)`,
* `γ̄  := gammaBar h.α h.β`.

This is the residue-input-form aggregate the `AprioriUniformResidueInputs`
scaffolding of `infra-P5-theorem1-phase-D-discharge-residue` consumes:
the conclusion has the residue's exact shape
`∫|m|^β̄ + ∫|u|^γ̄ + ∑_i ∫|Du i|^γ̄ ≤ aprioriUniformConstantClosed …`.
-/

/-- **Closed-form aggregator constant** for the residue-input form
aggregate apriori bound (paper eq. `eq:apriori-simple.power.growth`).

Glues the three closed-form constants `aprioriMBoundClosed`,
`aprioriUBoundClosed`, `aprioriDuBoundClosed` into a single value
suitable for the `AprioriUniformResidueInputs.uniformConstant` field
of the Phase D scaffolding.

The shape is `M + U^γ̄ + d * Cd` where `U := Cu * (d * Cd^{1/γ̄} + 1)`.
The extra `d * Cd` (rather than `Cd`) accommodates the residue's
per-coordinate `∑_i ∫|Du i|^γ̄ ≤ d · ∫‖Du‖^γ̄ ≤ d · Cd` form (vs. the
single `∫‖Du‖^γ̄ ≤ Cd` of the `apriori_aggregate_bound`). -/
noncomputable def aprioriUniformConstantClosed
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Vbound Vint_bound Vβp_bound : ℝ) : ℝ :=
  let M : ℝ := aprioriMBoundClosed h Vbound Vint_bound
  let Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound
  let Cd : ℝ := aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
  let γ : ℝ := gammaBar h.α h.β
  let U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1)
  M + U ^ γ + (d : ℝ) * Cd

/-- Non-negativity of `aprioriUniformConstantClosed`, conditional on
`Vint_bound, Vβp_bound ≥ 0`. -/
theorem aprioriUniformConstantClosed_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriUniformConstantClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  unfold aprioriUniformConstantClosed
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound with hCu_def
  set Cd : ℝ := aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
    with hCd_def
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hM_nn : 0 ≤ M :=
    aprioriMBoundClosed_nn_of_Vint_nn h Vbound Vint_bound hVint_nn
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hCd_nn : 0 ≤ Cd :=
    aprioriDuBoundClosed_nn (d := d) h Vbound Vint_bound Vβp_bound
      hVint_nn hVβp_nn
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hUγ_nn : 0 ≤ U ^ γ := Real.rpow_nonneg hU_nn _
  have hdCd_nn : 0 ≤ (d : ℝ) * Cd := mul_nonneg hd_nn hCd_nn
  linarith

/-! ### Raw-real (`α, β, C`)-keyed leaf and aggregate constants

The closed-form aggregator constant `aprioriUniformConstantClosed` and all its
leaf constants are pure functions of the numeric power-growth data
`(h.α, h.β, h.C)` — they never touch the heavy analytic fields of
`HypothesisPowerGrowth`. The `…Raw` variants below take those three reals
directly, so a constant can be assembled from a coercive `ε`-INDEPENDENT
constant `C0` (paper `prop:boundsHepsilon`, `eq:H-epsilon.lower.uniform`) WITHOUT
fabricating a `HypothesisPowerGrowth` bundle whose (false) `upper`/`DpH_upper`
fields would have to hold with `C0`.

Each `…Raw` def is a verbatim copy of its bundle-keyed sibling with `h.α/h.β/h.C`
replaced by the explicit `α/β/C`; the `…_eq` bridges record that the two agree
definitionally, so the existing aggregate-bound machinery (which concludes a bound
`≤ aprioriUniformConstantClosed h …`) is identical to `≤ aprioriUniformConstantClosedRaw
h.α h.β h.C …`. This is the D3-prerequisite layer for the coercive A2g rewire
(task `infra-P7-sigfix-T3-drain-D3-a2g-coercive-uniformity-rewire`). -/

/-- Raw-real form of `aprioriUepsiBelowConst` (keyed by `β, C`). -/
def aprioriUepsiBelowConstRaw (β C Vbound : ℝ) : ℝ :=
  let Vp : ℝ := C + max Vbound 0
  let lam : ℝ := ((β + 1) / (2 * C)) ^ ((1 : ℝ) / (β + 1))
  let K_Y : ℝ := (Vp / lam) ^ ((β + 1) / β) * (β / (β + 1))
  max (2 * C) ((2 * C + K_Y) + 1)

/-- Raw-real form of `aprioriMBoundResidual` (keyed by `β, C`). -/
def aprioriMBoundResidualRaw (β C Vbound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConstRaw β C Vbound
  let δ : ℝ := 1 / (2 * C')
  let lam_pow : ℝ := (β + 1) * δ / β
  let lam : ℝ := lam_pow ^ (β / (β + 1))
  (C / lam) ^ (β + 1) / (β + 1)

/-- Raw-real form of `aprioriMBoundClosed` (keyed by `β, C`). -/
def aprioriMBoundClosedRaw (β C Vbound Vint_bound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConstRaw β C Vbound
  let R  : ℝ := aprioriMBoundResidualRaw β C Vbound
  2 * C' * (C' + Vint_bound + R + C)

/-- Raw-real form of `aprioriUepsiMeanClosed` (keyed by `β, C`). -/
def aprioriUepsiMeanClosedRaw (β C Vbound Vint_bound : ℝ) : ℝ :=
  max (aprioriUepsiBelowConstRaw β C Vbound)
      (Vint_bound + C * (aprioriMBoundClosedRaw β C Vbound Vint_bound + 2))

/-- Raw-real form of `aprioriUBoundClosed` (keyed by `β, C`). -/
def aprioriUBoundClosedRaw (d : ℕ) (β C Vbound Vint_bound : ℝ) : ℝ :=
  max (poincareWirtingerConstant d)
      (aprioriUepsiMeanClosedRaw β C Vbound Vint_bound)

/-- Raw-real form of `aprioriDuPointwiseConst` (keyed by `β, C`). -/
def aprioriDuPointwiseConstRaw (β C : ℝ) : ℝ :=
  (C + C ^ 2) ^ betaBar' β * (4 : ℝ) ^ betaBar' β

/-- Raw-real form of `aprioriDuBoundClosed` (keyed by `α, β, C`). -/
def aprioriDuBoundClosedRaw (d : ℕ) (α β C Vbound Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C₁ : ℝ := aprioriDuPointwiseConstRaw β C
  let M  : ℝ := aprioriMBoundClosedRaw β C Vbound Vint_bound
  let Cu : ℝ := aprioriUBoundClosedRaw d β C Vbound Vint_bound
  let βp : ℝ := betaBar' β
  let γ  : ℝ := gammaBar α β
  let A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp)
  let B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1)
  let r  : ℝ := γ⁻¹ * βp
  (2 * A) ^ (1 / (1 - r)) + (2 * B)

/-- Raw-real form of `aprioriUniformConstantClosed` (keyed by `α, β, C`). -/
def aprioriUniformConstantClosedRaw
    (d : ℕ) (α β C Vbound Vint_bound Vβp_bound : ℝ) : ℝ :=
  let M : ℝ := aprioriMBoundClosedRaw β C Vbound Vint_bound
  let Cu : ℝ := aprioriUBoundClosedRaw d β C Vbound Vint_bound
  let Cd : ℝ := aprioriDuBoundClosedRaw d α β C Vbound Vint_bound Vβp_bound
  let γ : ℝ := gammaBar α β
  let U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1)
  M + U ^ γ + (d : ℝ) * Cd

/-- The raw leaf constant agrees with the bundle-keyed one. -/
theorem aprioriUepsiBelowConstRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound : ℝ) :
    aprioriUepsiBelowConst h Vbound = aprioriUepsiBelowConstRaw h.β h.C Vbound := rfl

/-- The raw `M`-residual constant agrees with the bundle-keyed one. -/
theorem aprioriMBoundResidualRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound : ℝ) :
    aprioriMBoundResidual h Vbound = aprioriMBoundResidualRaw h.β h.C Vbound := rfl

/-- The raw `M`-bound constant agrees with the bundle-keyed one. -/
theorem aprioriMBoundClosedRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) :
    aprioriMBoundClosed h Vbound Vint_bound
      = aprioriMBoundClosedRaw h.β h.C Vbound Vint_bound := rfl

/-- The raw `U`-mean constant agrees with the bundle-keyed one. -/
theorem aprioriUepsiMeanClosedRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) :
    aprioriUepsiMeanClosed h Vbound Vint_bound
      = aprioriUepsiMeanClosedRaw h.β h.C Vbound Vint_bound := rfl

/-- The raw `U`-bound constant agrees with the bundle-keyed one. -/
theorem aprioriUBoundClosedRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound : ℝ) :
    aprioriUBoundClosed (d := d) h Vbound Vint_bound
      = aprioriUBoundClosedRaw d h.β h.C Vbound Vint_bound := rfl

/-- The raw `Du`-pointwise constant agrees with the bundle-keyed one. -/
theorem aprioriDuPointwiseConstRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) :
    aprioriDuPointwiseConst h = aprioriDuPointwiseConstRaw h.β h.C := rfl

/-- The raw `Du`-bound constant agrees with the bundle-keyed one. -/
theorem aprioriDuBoundClosedRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound Vβp_bound : ℝ) :
    aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
      = aprioriDuBoundClosedRaw d h.α h.β h.C Vbound Vint_bound Vβp_bound := rfl

/-- The raw aggregator constant agrees with the bundle-keyed one. -/
theorem aprioriUniformConstantClosedRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH) (Vbound Vint_bound Vβp_bound : ℝ) :
    aprioriUniformConstantClosed (d := d) h Vbound Vint_bound Vβp_bound
      = aprioriUniformConstantClosedRaw d h.α h.β h.C Vbound Vint_bound Vβp_bound := rfl

/-- Strict positivity of the raw below-bound coefficient (keyed by `β, C`). -/
theorem aprioriUepsiBelowConstRaw_pos (β C Vbound : ℝ) (hC : 0 < C) :
    0 < aprioriUepsiBelowConstRaw β C Vbound := by
  unfold aprioriUepsiBelowConstRaw
  have h2C_pos : 0 < 2 * C := by linarith
  exact lt_of_lt_of_le h2C_pos (le_max_left _ _)

/-- Non-negativity of the raw below-bound coefficient (keyed by `β, C`). -/
theorem aprioriUepsiBelowConstRaw_nn (β C Vbound : ℝ) (hC : 0 < C) :
    0 ≤ aprioriUepsiBelowConstRaw β C Vbound :=
  (aprioriUepsiBelowConstRaw_pos β C Vbound hC).le

/-- Non-negativity of the raw mean-bound coefficient (keyed by `β, C`). -/
theorem aprioriUepsiMeanClosedRaw_nn (β C Vbound Vint_bound : ℝ) (hC : 0 < C) :
    0 ≤ aprioriUepsiMeanClosedRaw β C Vbound Vint_bound := by
  unfold aprioriUepsiMeanClosedRaw
  exact le_trans (aprioriUepsiBelowConstRaw_nn β C Vbound hC) (le_max_left _ _)

/-- Non-negativity of the raw `U`-bound coefficient (keyed by `β, C`). -/
theorem aprioriUBoundClosedRaw_nn (β C Vbound Vint_bound : ℝ) :
    0 ≤ aprioriUBoundClosedRaw d β C Vbound Vint_bound := by
  unfold aprioriUBoundClosedRaw
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  exact le_trans hd_nn (le_max_left _ _)

/-! ### D3b2 — raw-real (`β, C0`)-keyed `_int` constants

These mirror the bundle-keyed `…_int` constant defs but are keyed by explicit
reals `(β C0 : ℝ)`. They are used by the raw `_int` aggregate-engine helpers. -/

/-- Raw-real form of `aprioriUepsiBelowConst_int` (keyed by `β, C0`). -/
def aprioriUepsiBelowConst_intRaw (β C0 _Vint_bound Vβp_bound : ℝ) : ℝ :=
  let lam : ℝ := ((β + 1) / (2 * C0)) ^ ((1 : ℝ) / (β + 1))
  let K_eff : ℝ := C0 + Vβp_bound ^ (β / (β + 1))
  let K_Y_int : ℝ := (K_eff / lam) ^ ((β + 1) / β) * (β / (β + 1))
  max (2 * C0) (K_Y_int + 1)

/-- Strict positivity of the raw integral-V constant. -/
theorem aprioriUepsiBelowConst_intRaw_pos
    (β C0 Vint_bound Vβp_bound : ℝ) (hC0 : 0 < C0) :
    0 < aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound := by
  unfold aprioriUepsiBelowConst_intRaw
  have h2C_pos : 0 < 2 * C0 := by linarith
  exact lt_of_lt_of_le h2C_pos (le_max_left _ _)

/-- Non-negativity of the raw integral-V constant. -/
theorem aprioriUepsiBelowConst_intRaw_nn
    (β C0 Vint_bound Vβp_bound : ℝ) (hC0 : 0 < C0) :
    0 ≤ aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound :=
  (aprioriUepsiBelowConst_intRaw_pos β C0 Vint_bound Vβp_bound hC0).le

/-- Raw-real form of `aprioriMBoundResidual_int` (keyed by `β, C0`). -/
def aprioriMBoundResidual_intRaw (β C0 Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound
  let δ : ℝ := 1 / (2 * C')
  let lam_pow : ℝ := (β + 1) * δ / β
  let lam : ℝ := lam_pow ^ (β / (β + 1))
  (C0 / lam) ^ (β + 1) / (β + 1)

/-- Raw-real form of `aprioriMBoundClosed_int` (keyed by `β, C0`). -/
def aprioriMBoundClosed_intRaw (β C0 Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound
  let R  : ℝ := aprioriMBoundResidual_intRaw β C0 Vint_bound Vβp_bound
  2 * C' * (C' + Vint_bound + R + C0)

/-- The raw integral-V constant agrees with the bundle-keyed one. -/
theorem aprioriUepsiBelowConst_intRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    aprioriUepsiBelowConst_int h Vint_bound Vβp_bound
      = aprioriUepsiBelowConst_intRaw h.β h.C Vint_bound Vβp_bound := rfl

/-- **Closed-form residue-input-form aggregate apriori bound.**

Same hypothesis bundle as `apriori_aggregate_bound`, but with three
adjustments to the conclusion to match the `AprioriUniformResidueInputs`
shape:
1. The first summand is `∫ |m|^{β+1}` (residue shape) rather than
   `∫ m^{β̄}` — these agree under `m ≥ 0` (which `hMpos` provides
   strictly) and `βBarReal = h.β + 1`.
2. The middle summand is `∫ |u|^γ̄` (residue shape) rather than
   `(lpNormPer p u)^γ̄` — these agree via
   `lpNormPer_eq_integral_rpow` plus `MemLpPer p u`.
3. The third summand is the per-coordinate sum `∑_i ∫|Du i|^γ̄`
   rather than `∫‖Du‖^γ̄`. We have
   `∑_i ∫|Du i|^γ̄ ≤ d · ∫‖Du‖^γ̄ ≤ d · Cd`.

The closed-form constant `aprioriUniformConstantClosed h Vbound
Vint_bound Vβp_bound` is the explicit value `M + U^γ̄ + d * Cd`. -/
theorem apriori_aggregate_bound_residue_form
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vbound Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound)
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed (d := d) h Vbound Vint_bound Vβp_bound := by
  -- Abbreviations.
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  -- Positivity facts.
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  -- Step 1: closed-form m bound. `∫ m^{β+1} ≤ M`.
  set M : ℝ := aprioriMBoundClosed h Vbound Vint_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed (h := h) V Du m u epsTerms Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
  -- Replace `m^{β+1}` by `|m|^{β+1}` using `hMpos`.
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMpos] with x hxpos
    rw [abs_of_pos hxpos]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  -- Step 2: closed-form Du bound. `∫‖Du‖^γ̄ ≤ Cd`.
  set Cd : ℝ := aprioriDuBoundClosed (d := d) h Vbound Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form (h := h) V Du m u epsTerms
      Vbound Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  -- Step 3: closed-form Lp bound on u. `lpNormPer p u ≤ Cu·(S+1)`.
  set Cu : ℝ := aprioriUBoundClosed (d := d) h Vbound Vint_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_nn (d := d) h Vbound Vint_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed (h := h) V Du m u epsTerms
      Vbound Vint_bound
      hHJB h_lagr hMpos hVbnd hEpsNN h_identity hu_int hRHSabove_int
      hLB_int hMbeta_int hRHSbelow_int hVint
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  -- Per-coord identity: lpNormPer p (Du i) ^ γ = ∫ |Du i|^γ̄.
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  -- Pointwise: |Du i x| ≤ ‖(fun j => Du j x)‖.
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    exact Real.rpow_le_rpow (abs_nonneg _) h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, ‖(fun j => Du j x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hDu_i_le_Cd : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ Cd := fun i =>
    le_trans (hDu_i_le i) hCd_bound
  -- ∑_i ∫|Du i|^γ ≤ d * Cd
  have hSum_Du_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
        ∂(volume : Measure (Fin d → ℝ))) ≤ (d : ℝ) * Cd := by
    have hsum_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ ∑ _i : Fin d, Cd :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∫ x in UnitCube d, |Du i x| ^ γ
                  ∂(volume : Measure (Fin d → ℝ)))
        (g := fun _ => Cd)
        (fun i _ => hDu_i_le_Cd i)
    have hconst_sum : ∑ _i : Fin d, Cd = (d : ℝ) * Cd := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← hconst_sum]; exact hsum_le
  have hCd_nn : 0 ≤ Cd := by
    have h_int_nn : (0 : ℝ) ≤ ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    linarith [le_trans h_int_nn hCd_bound]
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq : lpNormPer p (Du i) ^ γ ≤ Cd := by
      rw [hDu_lp_γ i]
      exact hDu_i_le_Cd i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn
    exact le_trans hu_pw h2
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  -- (lpNormPer p u)^γ = ∫|u|^γ.
  have hu_lp_eq : lpNormPer p u ^ γ
      = ∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := u) hp_ne_zero hp_top hu_lp_γ
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p u ^ γ
          = (((∫ x, ‖u x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  -- Assemble.
  unfold aprioriUniformConstantClosed
  show (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ## D4.0b3 — `_int` sibling variants of the closed-form chain

Each `_int` variant below mirrors its pointwise sibling (with the
same closed-form witness shape) but consumes the integral V-data
`(Vint_bound, Vβp_bound)` plus AE-strong-measurability of `V` and
`m` and the `(β+1)/β`-power and `|V|·m` integrability hypotheses,
in place of the pointwise `‖V‖_∞ ≤ Vbound` hypothesis. The
underlying analytic substitution is the Hölder lemma
`holder_Vm_betaBar` (see `apriori_uepsi_below_closed_int`). -/

/-- **Closed-form Young residual `R`** for `apriori_m_bound_closed_int`.
Same shape as `aprioriMBoundResidual` but built from
`aprioriUepsiBelowConst_int` instead of `aprioriUepsiBelowConst`. -/
def aprioriMBoundResidual_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound
  let δ : ℝ := 1 / (2 * C')
  let lam_pow : ℝ := (h.β + 1) * δ / h.β
  let lam : ℝ := lam_pow ^ (h.β / (h.β + 1))
  (h.C / lam) ^ (h.β + 1) / (h.β + 1)

/-- **Closed-form witness for `apriori_m_bound_closed_int`**. Same
shape as `aprioriMBoundClosed` but built on top of the integral
constants. -/
def aprioriMBoundClosed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound
  let R  : ℝ := aprioriMBoundResidual_int h Vint_bound Vβp_bound
  2 * C' * (C' + Vint_bound + R + h.C)

/-- The raw integral residual constant agrees with the bundle-keyed one. -/
theorem aprioriMBoundResidual_intRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    aprioriMBoundResidual_int h Vint_bound Vβp_bound
      = aprioriMBoundResidual_intRaw h.β h.C Vint_bound Vβp_bound := rfl

/-- The raw integral `M`-bound constant agrees with the bundle-keyed one. -/
theorem aprioriMBoundClosed_intRaw_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    aprioriMBoundClosed_int h Vint_bound Vβp_bound
      = aprioriMBoundClosed_intRaw h.β h.C Vint_bound Vβp_bound := rfl

/-- Non-negativity of `aprioriMBoundClosed_int`, conditional on
`Vint_bound ≥ 0`. -/
theorem aprioriMBoundClosed_int_nn_of_Vint_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) :
    0 ≤ aprioriMBoundClosed_int h Vint_bound Vβp_bound := by
  unfold aprioriMBoundClosed_int
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hC'_pos : 0 < aprioriUepsiBelowConst_int h Vint_bound Vβp_bound :=
    aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have h2C'_nn : 0 ≤ 2 * aprioriUepsiBelowConst_int h Vint_bound Vβp_bound := by linarith
  have hR_nn : 0 ≤ aprioriMBoundResidual_int h Vint_bound Vβp_bound := by
    unfold aprioriMBoundResidual_int
    set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
    have h2C'_pos : 0 < 2 * C' := by linarith
    set δ : ℝ := 1 / (2 * C') with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
    set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
    have hlam_pow_pos : 0 < lam_pow := by
      rw [hlam_pow_def]
      exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
    set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
    have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hsum_nn :
      0 ≤ aprioriUepsiBelowConst_int h Vint_bound Vβp_bound + Vint_bound +
            aprioriMBoundResidual_int h Vint_bound Vβp_bound + h.C :=
    by linarith [hC'_pos, hC_pos, hR_nn]
  exact mul_nonneg h2C'_nn hsum_nn

/-- **`apriori_m_bound_closed_int`** — integral V-data variant of
`apriori_m_bound_closed`. Consumes `Vint_bound, Vβp_bound, hVint, hVβp,
hVβp_nn` plus the V-integrability hypotheses required by
`apriori_uepsi_below_closed_int`. -/
theorem apriori_m_bound_closed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, m x ^ (h.β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosed_int h Vint_bound Vβp_bound := by
  -- Constants.
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  -- Cube volume / finiteness.
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by
    simp [hvol_def]
  -- Step 1: Lower bound on ∫ u from `apriori_uepsi_below_closed_int`.
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hMpos hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hLB_int hM_int hRHSbelow_int
  -- Step 2: Upper bound on ∫ u from `apriori_uepsi_above`.
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above (h := h) V Du m u hHJB hMpos hu_int hRHSabove_int
  -- Set X := ∫ m^{β+1}.
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul h.C
      have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                    - h.C * (m x ^ h.β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  -- Combine: (1/C') · X − C' ≤ ∫u ≤ Vint + h.C * (Y + vol).
  have hcomb : (1 / C') * X - C' ≤ Vint + h.C * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + h.C * (Y + vol) := habove_eq
  -- Step 3: Pointwise Young absorption.
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (h.β + 1) * δ / h.β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (h.β / (h.β + 1)) = δ := by
    rw [hlam_pow_def]
    field_simp
  set lam : ℝ := lam_pow ^ (h.β / (h.β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((h.β + 1) / h.β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : h.β / (h.β + 1) * ((h.β + 1) / h.β) = 1 := by
      have hβne : h.β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : h.β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  set R : ℝ := aprioriMBoundResidual_int h Vint_bound Vβp_bound with hR_def
  have hR_unfold : R = (h.C / lam) ^ (h.β + 1) / (h.β + 1) := by
    show aprioriMBoundResidual_int h Vint_bound Vβp_bound = _
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ h.C / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (h.C / lam) ^ (h.β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      h.C * mx ^ h.β ≤ δ * mx ^ (h.β + 1) + R := by
    intro mx hmx
    have hY := young_absorb_pow_into_betaPlusOne (β := h.β) hβ_pos
                  h.C hC_pos.le mx hmx lam hlam_pos
    rw [hlam_pow_id] at hY
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  have hY_int :
      Integrable (fun x => h.C * m x ^ h.β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul h.C
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (h.β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => h.C * m x ^ h.β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (h.β + 1) + R) := by
    filter_upwards [hMpos] with x hxm
    exact hYoung_pt (m x) hxm.le
  have hYint_le :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  have hYint_LHS :
      ∫ x in UnitCube d, h.C * m x ^ h.β
          ∂(volume : Measure (Fin d → ℝ))
        = h.C * Y := by
    rw [integral_const_mul]
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (h.β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ))
        = δ * X + R * vol := by
    rw [integral_add (hLB_int.const_mul δ) (integrable_const _),
        integral_const_mul]
    have hone_int :
        ∫ _ in UnitCube d, R ∂(volume : Measure (Fin d → ℝ)) = R * vol := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
        Set.univ_inter, hvol_def, mul_comm]
    rw [hone_int]
  rw [hYint_LHS, hYint_RHS] at hYint_le
  have hcomb' :
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + h.C * vol := by
    have : h.C * (Y + vol) = h.C * Y + h.C * vol := by ring
    have h1 : Vint + h.C * (Y + vol) ≤ Vint + (δ * X + R * vol) + h.C * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + h.C * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + h.C * vol := by
    linarith [habs, hVint_le]
  have hM_unfold :
      aprioriMBoundClosed_int h Vint_bound Vβp_bound
        = 2 * C' * (C' + Vint_bound + R + h.C) := by
    show aprioriMBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + h.C * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  rw [hM_unfold]
  exact hmul

/-! ## Closed-form mean bound (`_int` variant) -/

/-- **Closed-form witness for `apriori_uepsi_mean_closed_int`**. Same
shape as `aprioriUepsiMeanClosed` but built from the integral
constants. -/
def aprioriUepsiMeanClosed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) : ℝ :=
  max (aprioriUepsiBelowConst_int h Vint_bound Vβp_bound)
      (Vint_bound + h.C * (aprioriMBoundClosed_int h Vint_bound Vβp_bound + 2))

theorem aprioriUepsiMeanClosed_int_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    0 ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
  unfold aprioriUepsiMeanClosed_int
  exact le_trans (aprioriUepsiBelowConst_int_nn h Vint_bound Vβp_bound)
        (le_max_left _ _)

/-- **`apriori_uepsi_mean_closed_int`** — integral V-data variant. -/
theorem apriori_uepsi_mean_closed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
  have hC_pos : 0 < h.C := h.hC
  have hβ_pos : 0 < h.β := h.hβ
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  set C' : ℝ := aprioriUepsiBelowConst_int h Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' := aprioriUepsiBelowConst_int_pos h Vint_bound Vβp_bound
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (h.β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hMpos hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above (h := h) V Du m u hHJB hMpos hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (h.β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMpos] with x hxm
    exact Real.rpow_nonneg hxm.le _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    have : Integrable (fun x => (|V x| + h.C * (m x ^ h.β + 1))
                                  - h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + h.C * (m x ^ h.β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + h.C * (Y + vol) := by
    have hpow_int : Integrable (fun x => h.C * (m x ^ h.β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul h.C
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, h.C * (m x ^ h.β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = h.C * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ h.β + 1)
              ∂(volume : Measure (Fin d → ℝ))
            = Y + ∫ x in UnitCube d, (1 : ℝ)
                    ∂(volume : Measure (Fin d → ℝ)) := by
        rw [integral_add hMbeta_int (integrable_const _)]
      rw [hsub]
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hsplit]
  have hY_le_X_plus_vol : Y ≤ X + vol := by
    have hpoint :
        (fun x => m x ^ h.β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (h.β + 1) + 1) := by
      filter_upwards [hMpos] with x hxm
      exact rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm.le
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (h.β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ h.β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (h.β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = X + vol := by
      rw [integral_add hLB_int hone_int']
      have hone_int :
          ∫ _ in UnitCube d, (1 : ℝ)
              ∂(volume : Measure (Fin d → ℝ)) = vol := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
          Set.univ_inter, hvol_def]
      rw [hone_int]
    rw [hRHS_eq] at hint_le
    exact hint_le
  have hX_le_M : X ≤ M := hM_le
  have hY_le_M_plus_vol : Y ≤ M + vol := by linarith
  have hVint_le : Vint ≤ Vint_bound := hVint
  set Uint : ℝ := ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) with hUint_def
  have hUint_ub : Uint ≤ Vint_bound + h.C * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + h.C * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : h.C * (Y + vol) ≤ h.C * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + h.C * (Y + vol) ≤ Vint_bound + h.C * (M + 2 * vol) := by
      have : h.C * ((M + vol) + vol) = h.C * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  have hCmean_unfold :
      aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound
        = max C' (Vint_bound + h.C * (M + 2)) := by
    show aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  have hUint_ub' : Uint ≤ Vint_bound + h.C * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + h.C * (M + 2) ≤ aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hneg : -aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · linarith [hUint_ub', hCmean_ge_ub]

/-! ## Closed-form Lp bound on `u` (`_int` variant) -/

/-- **Closed-form witness for `apriori_uepsi_Lp_closed_int`**. -/
def aprioriUBoundClosed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) : ℝ :=
  max (poincareWirtingerConstant d)
      (aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound)

theorem aprioriUBoundClosed_int_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH) (Vint_bound Vβp_bound : ℝ) :
    0 ≤ aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound := by
  unfold aprioriUBoundClosed_int
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  exact le_trans hd_nn (le_max_left _ _)

/-- **`apriori_uepsi_Lp_closed_int`** — integral V-data variant of
`apriori_uepsi_Lp_closed`. -/
theorem apriori_uepsi_Lp_closed_int
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean :=
    aprioriUepsiMeanClosed_int_nn h Vint_bound Vβp_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    poincareWirtinger (p := p) hγ_one_le hγ_top
      hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas
      hDu_per hDu_loc hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-! ## Closed-form Du bound (`_int` variant) — D4.0d

Integral-V-data sibling of `aprioriDuBoundClosed` /
`apriori_Du_bound_closed_form`. The two pointwise sub-witnesses
(`aprioriMBoundClosed`, `aprioriUBoundClosed`) are replaced by
their `_int` counterparts so the entire Du chain is
`Vbound`-free; the V contribution from `eq:Duepsi.bound` is
absorbed via `vData.Vβp_bound` (consumed here as the explicit
real `Vβp_bound` plus the integrability/measurability
hypotheses already used by `apriori_m_bound_closed_int` and
`apriori_uepsi_Lp_closed_int`). -/

/-- **Closed-form witness for `apriori_Du_bound_closed_form_int`**.
Same shape as `aprioriDuBoundClosed` but built from the `_int`
M- and U-bound constants, with `Vbound` removed. -/
def aprioriDuBoundClosed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C₁ : ℝ := aprioriDuPointwiseConst h
  let M  : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound
  let Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound
  let βp : ℝ := betaBar' h.β
  let γ  : ℝ := gammaBar h.α h.β
  let A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp)
  let B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1)
  let r  : ℝ := γ⁻¹ * βp
  (2 * A) ^ (1 / (1 - r)) + (2 * B)

/-- Non-negativity of `aprioriDuBoundClosed_int`, conditional on
`Vint_bound, Vβp_bound ≥ 0`. -/
theorem aprioriDuBoundClosed_int_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound := by
  unfold aprioriDuBoundClosed_int
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  set M  : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hCu_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set γ  : ℝ := gammaBar h.α h.β with hγ_def
  set A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  set r  : ℝ := γ⁻¹ * βp with hr_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hM_nn : 0 ≤ M :=
    aprioriMBoundClosed_int_nn_of_Vint_nn h Vint_bound Vβp_bound hVint_nn
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hβp_pos : 0 < βp :=
    lt_trans zero_lt_one (one_lt_betaBar' h.β h.hβ)
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hCuβp_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2βp_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdβp_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCuβp_nn h2βp_nn) hdβp_nn
  have h2A_nn : 0 ≤ 2 * A := by linarith
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have h1 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCuβp_nn h2βp_nn
    linarith
  have h2B_nn : 0 ≤ 2 * B := by linarith
  have hfirst_nn : 0 ≤ (2 * A) ^ (1 / (1 - r)) := Real.rpow_nonneg h2A_nn _
  linarith

/-- **Paper eq. `eq:Duepsi.bound`** (`Source/FGU-monotone_revised.tex`,
line 1265), integral-V-data variant.

Same conclusion as `apriori_Du_bound_closed_form` with the closed-form
constant replaced by `aprioriDuBoundClosed_int`. The pointwise field
`hVbnd : ∀ᵐ x, |V x| ≤ Vbound` is removed; instead we consume the
integral V-data `(Vint_bound, Vβp_bound)` plus the
integrability/measurability hypotheses required by the `_int` chain. -/
theorem apriori_Du_bound_closed_form_int
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound := by
  -- Mirror of `apriori_Du_bound_closed_form` with M- and U-pieces routed
  -- through the `_int` chain.
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  -- Step 1: closed-form integrated bound from eq:Duepsi.bound.
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hint_bound :=
    apriori_Du_integrated_bound_closed (h := h) V Du m u hHJB hMpos
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  -- Step 2: closed-form m bound via the `_int` chain.
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  -- Step 3: closed-form Poincaré bound via the `_int` chain.
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  -- The rest of the proof mirrors `apriori_Du_bound_closed_form` exactly.
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  -- Define the closed-form A and B used in `aprioriDuBoundClosed_int`.
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn' : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hMpos] with x hxm
        exact Real.rpow_nonneg hxm.le _
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  -- Apply the scalar Young absorption lemma.
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  -- Bridge to the closed-form witness `aprioriDuBoundClosed_int`.
  have hclosed_eq :
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

/-! ## Aggregator (`_int` variant)

The aggregate `_int` variant takes the integral V-data
`(Vint_bound, Vβp_bound)`. Both the M, U, and Du pieces flow
through the `_int` chain (D4.0d), so `Vbound` is no longer
needed. -/

/-- **Closed-form aggregator constant** built from the `_int`
M-, U-, and Du-bound witnesses (D4.0d). -/
noncomputable def aprioriUniformConstantClosed_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (Vint_bound Vβp_bound : ℝ) : ℝ :=
  let M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound
  let Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound
  let Cd : ℝ := aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
  let γ : ℝ := gammaBar h.α h.β
  let U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1)
  M + U ^ γ + (d : ℝ) * Cd

theorem aprioriUniformConstantClosed_int_nn
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriUniformConstantClosed_int (d := d) h Vint_bound Vβp_bound := by
  unfold aprioriUniformConstantClosed_int
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hCu_def
  set Cd : ℝ := aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCd_def
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hM_nn : 0 ≤ M :=
    aprioriMBoundClosed_int_nn_of_Vint_nn h Vint_bound Vβp_bound hVint_nn
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hCd_nn : 0 ≤ Cd :=
    aprioriDuBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
      hVint_nn hVβp_nn
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hUγ_nn : 0 ≤ U ^ γ := Real.rpow_nonneg hU_nn _
  have hdCd_nn : 0 ≤ (d : ℝ) * Cd := mul_nonneg hd_nn hCd_nn
  linarith

/-- **`apriori_aggregate_bound_residue_form_int`** — integral V-data
variant of `apriori_aggregate_bound_residue_form`. All three pieces
(M, U, Du) flow through the `_int` chain (D4.0d), so `Vbound` is
no longer required. -/
theorem apriori_aggregate_bound_residue_form_int
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar h.α h.β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed_int (d := d) h Vint_bound Vβp_bound := by
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  -- Step 1: closed-form m bound via `_int`.
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMpos] with x hxpos
    rw [abs_of_pos hxpos]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  -- Step 2: closed-form Du bound via the `_int` chain (D4.0d).
  set Cd : ℝ := aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_closed_form_int (h := h) V Du m u epsTerms
      Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hVβp hu_lp_γ
  -- Step 3: closed-form Lp bound on u via `_int`.
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound
    with hCu_def
  have hCu_nn : 0 ≤ Cu :=
    aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int (h := h) V Du m u epsTerms
      Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_meas hu_per hu_loc hu_sob
      hDu_weak hDu_meas hDu_per hDu_loc hDu_lp
  -- The remainder is identical to `apriori_aggregate_bound_residue_form`.
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    exact Real.rpow_le_rpow (abs_nonneg _) h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, ‖(fun j => Du j x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hDu_i_le_Cd : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ Cd := fun i =>
    le_trans (hDu_i_le i) hCd_bound
  have hSum_Du_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
        ∂(volume : Measure (Fin d → ℝ))) ≤ (d : ℝ) * Cd := by
    have hsum_le : (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ ∑ _i : Fin d, Cd :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∫ x in UnitCube d, |Du i x| ^ γ
                  ∂(volume : Measure (Fin d → ℝ)))
        (g := fun _ => Cd)
        (fun i _ => hDu_i_le_Cd i)
    have hconst_sum : ∑ _i : Fin d, Cd = (d : ℝ) * Cd := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← hconst_sum]; exact hsum_le
  have hCd_nn : 0 ≤ Cd := by
    have h_int_nn : (0 : ℝ) ≤ ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    linarith [le_trans h_int_nn hCd_bound]
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ Cd ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq : lpNormPer p (Du i) ^ γ ≤ Cd := by
      rw [hDu_lp_γ i]
      exact hDu_i_le_Cd i
    have h1 : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ Cd ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at h1; exact h1
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hS_le : S ≤ (d : ℝ) * Cd ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => Cd ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, Cd ^ γ⁻¹ = (d : ℝ) * Cd ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, Cd ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * Cd ^ γ⁻¹ := hconst_sum
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hU_nn : 0 ≤ U := by
    apply mul_nonneg hCu_nn
    have : 0 ≤ (d : ℝ) * Cd ^ γ⁻¹ := mul_nonneg hd_nn hCd_inv_nn
    linarith
  have hu_norm_le_U : lpNormPer p u ≤ U := by
    have h_S1_le : S + 1 ≤ (d : ℝ) * Cd ^ γ⁻¹ + 1 := by linarith
    have h2 : Cu * (S + 1) ≤ Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left h_S1_le hCu_nn
    exact le_trans hu_pw h2
  have hLpu_γ_le : lpNormPer p u ^ γ ≤ U ^ γ := by
    have hLpu_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
    exact Real.rpow_le_rpow hLpu_nn hu_norm_le_U hγ_nn
  have hu_lp_eq : lpNormPer p u ^ γ
      = ∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := u) hp_ne_zero hp_top hu_lp_γ
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p u ^ γ
          = (((∫ x, ‖u x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  unfold aprioriUniformConstantClosed_int
  show (∫ x in UnitCube d, |m x| ^ (h.β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-! ## AE-periodic siblings (Phase 2c-β)

The following three theorems are AE-periodic siblings of
`apriori_uepsi_Lp_closed_int`, `apriori_Du_bound_closed_form_int`, and
`apriori_aggregate_bound_residue_form_int`. They retype the
periodicity hypotheses on `u` and `Du i` from pointwise
`IsPeriodic` to `Periodic.AEPeriodic`, drop the (now-unused) local
integrability hypotheses `hu_loc`/`hDu_loc`, and call
`Periodic.poincareWirtinger_AEPeriodicRep` instead of the
pointwise-periodic `poincareWirtinger`. The chosen periodic
representatives come from `Classical.choice` of the
`Nonempty (Periodic.AEPeriodicRep …)` predicate that defines
`Periodic.AEPeriodic`. -/

/-- **AE-periodic sibling of `apriori_uepsi_Lp_closed_int`.**

Same statement as `apriori_uepsi_Lp_closed_int` except the
periodicity hypotheses `hu_per` and `hDu_per` are typed as
`Periodic.AEPeriodic` (a.e.-periodic with chosen representative)
rather than pointwise `IsPeriodic`, and the local-integrability
hypotheses `hu_loc`, `hDu_loc` are dropped (locality is recovered
inside the AE-periodic Poincaré wrapper from the representative's
pointwise periodicity).

Implementation: identical to `apriori_uepsi_Lp_closed_int` except
the inner Poincaré–Wirtinger call is routed through
`Periodic.poincareWirtinger_AEPeriodicRep`. -/
theorem apriori_uepsi_Lp_closed_int_aePeriodic
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
      aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar h.α h.β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed_int h Vint_bound Vβp_bound with hCmean_def
  have hCmean_nn : 0 ≤ Cmean :=
    aprioriUepsiMeanClosed_int_nn h Vint_bound Vβp_bound
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  -- AE-periodic Poincaré–Wirtinger via chosen representatives.
  let hu_rep : Periodic.AEPeriodicRep (d := d) u := Classical.choice hu_per
  let hDu_rep : ∀ i, Periodic.AEPeriodicRep (d := d) (Du i) :=
    fun i => Classical.choice (hDu_per i)
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    Periodic.poincareWirtinger_AEPeriodicRep (d := d) (p := p) hγ_one_le hγ_top
      hu_rep hu_sob
      hDu_weak hDu_rep hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) := by
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]
    exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
    have hsum :
        u = (u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u) := by
      funext x; simp
    have h := lpNormPer_triangle (p := p)
              (f := u - (fun _ : Fin d → ℝ => periodicMean u))
              (g := fun _ : Fin d → ℝ => periodicMean u)
              hdiff_lp hconst_lp hp_one_le
    have hrew :
        lpNormPer (d := d) p
            ((u - (fun _ : Fin d → ℝ => periodicMean u)) +
              (fun _ : Fin d → ℝ => periodicMean u))
          = lpNormPer (d := d) p u := by
      congr 1; funext x; simp
    rw [hrew] at h
    exact h
  have hp_ne_zero : p ≠ 0 := by
    intro hp0
    rw [hp0] at hp_one_le
    exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) = |periodicMean u| :=
    lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
  set S : ℝ := ∑ i : Fin d, lpNormPer (d := d) p (Du i) with hS_def
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  have hu_le_dS_plus_Cmean :
      lpNormPer (d := d) p u ≤ poincareWirtingerConstant d * S + Cmean := by
    calc lpNormPer (d := d) p u
        ≤ lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
            lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := htri
      _ ≤ poincareWirtingerConstant d * S + |periodicMean u| := by
          rw [h_const_norm]
          exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  have hC_ge_d : poincareWirtingerConstant d ≤ C := by
    rw [hC_unfold]; exact le_max_left _ _
  have hC_ge_Cmean : Cmean ≤ C := by
    rw [hC_unfold]; exact le_max_right _ _
  calc lpNormPer (d := d) p u
      ≤ poincareWirtingerConstant d * S + Cmean := hu_le_dS_plus_Cmean
    _ ≤ C * S + C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hC_ge_d hS_nn
        · exact hC_ge_Cmean
    _ = C * (S + 1) := by ring

/-- **AE-periodic sibling of `apriori_Du_bound_closed_form_int`.**

Same statement except for the periodicity / locality hypothesis
swap (`IsPeriodic` → `Periodic.AEPeriodic` on `u` and each `Du i`,
no `hu_loc`/`hDu_loc`). Body is a thin wrapper: identical to
`apriori_Du_bound_closed_form_int` except the inner call to
`apriori_uepsi_Lp_closed_int` is routed to the new
`apriori_uepsi_Lp_closed_int_aePeriodic`. -/
theorem apriori_Du_bound_closed_form_int_aePeriodic
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionAprioriPowerData H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMpos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
        ≤ Vint_bound)
    (hVβp_le :
      ∫ x in UnitCube d, |V x| ^ ((h.β + 1) / h.β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_pow_int : Integrable (fun x => |V x| ^ ((h.β + 1) / h.β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hEpsNN : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms x)
    (h_identity :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hu_int : Integrable u (volume.restrict (UnitCube d)))
    (hRHSabove_int : Integrable
              (fun x => |V x| + h.C * (m x ^ h.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (h.β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ h.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar h.α h.β))
    (hγ_top : ENNReal.ofReal (gammaBar h.α h.β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' h.β)
        (volume.restrict (UnitCube d)))
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ betaBar' h.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound := by
  -- Mirror of `apriori_Du_bound_closed_form_int` with the inner
  -- `apriori_uepsi_Lp_closed_int` call routed through the AE-periodic
  -- sibling `apriori_uepsi_Lp_closed_int_aePeriodic`.
  set γ : ℝ := gammaBar h.α h.β with hγ_def
  set βp : ℝ := betaBar' h.β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < h.β := h.hβ
  have hα_one_lt : 1 < h.α := h.hα
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' h.β hβ_pos)
  have hβp_one_lt : 1 < βp := by
    rw [hβp_def]; exact one_lt_betaBar' h.β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact gammaBar_pos h.α h.β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = h.α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' h.α h.β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < h.α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  -- Step 1: closed-form integrated bound from eq:Duepsi.bound.
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar h.β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (h.β + 1)) _
    exact hLB_int
  set C₁ : ℝ := aprioriDuPointwiseConst h with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConst_nn h
  have hint_bound :=
    apriori_Du_integrated_bound_closed (h := h) V Du m u hHJB hMpos
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  -- Step 2: closed-form m bound via the `_int` chain.
  set M : ℝ := aprioriMBoundClosed_int h Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (h.β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_closed_int (h := h) V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  -- Step 3: AE-periodic closed-form Poincaré bound via the new sibling.
  set Cu : ℝ := aprioriUBoundClosed_int (d := d) h Vint_bound Vβp_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_int_nn (d := d) h Vint_bound Vβp_bound
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar h.α h.β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_closed_int_aePeriodic (h := h) V Du m u epsTerms
      Vint_bound Vβp_bound
      hHJB h_lagr hMpos hVint hVβp_le hVβp_nn hVβp_pow_int hVm_int hV_meas hm_meas
      hEpsNN h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob
      hDu_weak hDu_per hDu_lp
  -- The rest of the proof mirrors `apriori_Du_bound_closed_form_int` exactly.
  set T : ℝ := ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
                ∂(volume : Measure (Fin d → ℝ)) with hT_def
  set S : ℝ := ∑ i : Fin d, lpNormPer p (Du i) with hS_def
  have hT_nn : 0 ≤ T := by
    apply integral_nonneg_of_ae
    refine Filter.Eventually.of_forall ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => lpNormPer_nonneg p (Du i))
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hβp_pos]
  have hq_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = βp := by rw [hq_def]; exact ENNReal.toReal_ofReal hβp_nn
  have hq_le_p : q ≤ p := by
    rw [hp_def, hq_def]; exact ENNReal.ofReal_le_ofReal hβp_le_γ
  have hDu_lp_γ : ∀ i, lpNormPer p (Du i) ^ γ
      = ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := p) (f := Du i) hp_ne_zero hp_top (hDu_lp i)
    rw [hp_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖Du i x‖ ^ γ
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have heq :
        lpNormPer p (Du i) ^ γ
          = (((∫ x, ‖Du i x‖ ^ γ
                ∂(Measure.restrict volume (UnitCube d))) ^ γ⁻¹) ^ γ) := by
      rw [hbridge]
    rw [heq]
    rw [← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) from hcong]
  have hpoint_le_per_coord :
      ∀ i, ∀ x, |Du i x| ^ γ ≤ ‖(fun j => Du j x)‖ ^ γ := by
    intro i x
    have h1 : |Du i x| ≤ ‖(fun j => Du j x)‖ := by
      have := norm_le_pi_norm (fun j => Du j x) i
      simpa [Real.norm_eq_abs] using this
    have h2 : (0 : ℝ) ≤ |Du i x| := abs_nonneg _
    exact Real.rpow_le_rpow h2 h1 hγ_nn
  have hDu_i_int : ∀ i, Integrable (fun x => |Du i x| ^ γ)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hmem : MemLpPer p (Du i) := hDu_lp i
    have hmemLp : MemLp (Du i) p (volume.restrict (UnitCube d)) := hmem
    have := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at this
    have hcong : (fun x => ‖Du i x‖ ^ γ) = (fun x => |Du i x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at this
    exact this
  have hDu_i_le : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ T := by
    intro i
    apply setIntegral_mono_ae_restrict (hDu_i_int i) hDu_norm_int
    refine Filter.Eventually.of_forall ?_
    intro x; exact hpoint_le_per_coord i x
  have hcoord_le : ∀ i, lpNormPer p (Du i) ^ γ ≤ T := by
    intro i; rw [hDu_lp_γ i]; exact hDu_i_le i
  have hT_inv_nn : 0 ≤ T ^ γ⁻¹ := Real.rpow_nonneg hT_nn _
  have hcoord_le' : ∀ i, lpNormPer p (Du i) ≤ T ^ γ⁻¹ := by
    intro i
    have hL_nn : 0 ≤ lpNormPer p (Du i) := lpNormPer_nonneg p (Du i)
    have hineq := hcoord_le i
    have : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ ≤ T ^ γ⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hL_nn _) hineq (by positivity)
    have hself : (lpNormPer p (Du i) ^ γ) ^ γ⁻¹ = lpNormPer p (Du i) := by
      rw [← Real.rpow_mul hL_nn, mul_inv_cancel₀ hγ_ne, Real.rpow_one]
    rw [hself] at this; exact this
  have hS_le : S ≤ (d : ℝ) * T ^ γ⁻¹ := by
    have hsum_le : ∑ i : Fin d, lpNormPer p (Du i)
        ≤ ∑ _i : Fin d, T ^ γ⁻¹ :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => lpNormPer p (Du i)) (g := fun _ => T ^ γ⁻¹)
        (fun i _ => hcoord_le' i)
    have hconst_sum : ∑ _i : Fin d, T ^ γ⁻¹ = (d : ℝ) * T ^ γ⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    calc S = ∑ i : Fin d, lpNormPer p (Du i) := rfl
      _ ≤ ∑ _i : Fin d, T ^ γ⁻¹ := hsum_le
      _ = (d : ℝ) * T ^ γ⁻¹ := hconst_sum
  have hu_lp_q : MemLpPer q u := by
    have hmemL : MemLp u p (volume.restrict (UnitCube d)) := hu_lp_γ
    have : MemLp u q (volume.restrict (UnitCube d)) :=
      hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
    have hint_nn : 0 ≤ ∫ x, ‖u x‖ ^ βp
        ∂(Measure.restrict volume (UnitCube d)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (norm_nonneg _) _
    have hcong : (fun x => ‖u x‖ ^ βp) = (fun x => |u x| ^ βp) := by
      funext x; rw [Real.norm_eq_abs]
    rw [hcong] at hbridge
    have hβp_ne : βp ≠ 0 := ne_of_gt hβp_pos
    have hint_nn' : 0 ≤ ∫ x in UnitCube d, |u x| ^ βp
        ∂(volume : Measure (Fin d → ℝ)) := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have heq2 :
        lpNormPer q u ^ βp =
          ((∫ x, |u x| ^ βp ∂(Measure.restrict volume (UnitCube d))) ^ βp⁻¹) ^ βp := by
      rw [hbridge]
    rw [heq2, ← Real.rpow_mul hint_nn',
        inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp := by
    have hsum_nn : 0 ≤ Cu * (S + 1) :=
      mul_nonneg hCu_nn (by linarith)
    exact Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar h.β = h.β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar h.β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' h.β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2 <;> rfl
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := hVβp
  have hvol_le : vol ≤ 1 := by rw [hvol_eq_one]
  have hcomb :
      C₁ * (Im + Iu + Iv + vol)
        ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have h1 := add_le_add (add_le_add (add_le_add hIm_le hIu_le) hIv_le) hvol_le
    convert h1 using 1
  have hT_le :
      T ≤ C₁ * (M + (Cu * (S + 1)) ^ βp + Vβp_bound + 1) :=
    le_trans hint_bound' hcomb
  have hSpow_expand :
      (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by
    rw [hCu_pow]
    have hstep :
        Cu ^ βp * (S + 1) ^ βp ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp)) :=
      mul_le_mul_of_nonneg_left hSplus1_pow_le hCu_pow_nn
    rw [h1pow] at hstep
    calc Cu ^ βp * (S + 1) ^ βp
        ≤ Cu ^ βp * ((2 : ℝ) ^ βp * (S ^ βp + 1)) := hstep
      _ = Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) := by ring
  have hT_le_2 :
      T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1) := by
    refine le_trans hT_le ?_
    apply mul_le_mul_of_nonneg_left _ hC₁_nn
    have hadd : (Cu * (S + 1)) ^ βp ≤ Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) :=
      hSpow_expand
    linarith
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ :=
    mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by
    rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    have : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ_pos
    exact mul_pos this hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  -- Define the closed-form A and B used in `aprioriDuBoundClosed_int`.
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hIv_nn : 0 ≤ Iv := by
      apply integral_nonneg_of_ae
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hVβp_nn' : 0 ≤ Vβp_bound := le_trans hIv_nn hIv_le
    have hM_nn : 0 ≤ M := by
      have hIm_nn : 0 ≤ Im := by
        apply integral_nonneg_of_ae
        filter_upwards [hMpos] with x hxm
        exact Real.rpow_nonneg hxm.le _
      linarith [le_trans hIm_nn hIm_le]
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have hAR_T : T ≤ A * T ^ r + B := by
    have hSpow_T :
        S ^ βp ≤ (d : ℝ) ^ βp * T ^ r := by
      calc S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp := hSpow_le
        _ = (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp := hd_T_pow
        _ = (d : ℝ) ^ βp * T ^ r := by rw [hT_pow_iter]
    have hCu2_nn : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    have hSpow_T_add :
        S ^ βp + 1 ≤ (d : ℝ) ^ βp * T ^ r + 1 :=
      add_le_add hSpow_T (le_refl _)
    have hkey :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) + Vβp_bound + 1)
          ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC₁_nn
      have hstep :
          Cu ^ βp * (2 : ℝ) ^ βp * (S ^ βp + 1) ≤
            Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1) :=
        mul_le_mul_of_nonneg_left hSpow_T_add hCu2_nn
      linarith
    have hbig :
        T ≤ C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
                  + Vβp_bound + 1) :=
      le_trans hT_le_2 hkey
    have hexpand :
        C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp * ((d : ℝ) ^ βp * T ^ r + 1)
              + Vβp_bound + 1) = A * T ^ r + B := by
      rw [hA_def, hB_def]; ring
    rw [hexpand] at hbig
    exact hbig
  -- Apply the scalar Young absorption lemma.
  have hT_one : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    have h1 : (1 / (1 : ℝ)) = 1 := by norm_num
    rw [h1, Real.rpow_one]
  -- Bridge to the closed-form witness `aprioriDuBoundClosed_int`.
  have hclosed_eq :
      aprioriDuBoundClosed_int (d := d) h Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed_int h Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq]
  rw [← h_2B_pow]
  exact hT_le_closed

end SimplePower
end Theorems
end StationaryMFG
end
