module

public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext
public import StationaryMFG.Theorems.SimplePower.Banach.UniformSequence
public import StationaryMFG.Theorems.SimplePower.Banach.Closure
public import StationaryMFG.Periodic.Separability
public import Mathlib.MeasureTheory.Function.Floor
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part1
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part1
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part2
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part2
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part3
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part3
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part4
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part4

@[expose] public section

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
open MeasureTheory Filter
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
open MeasureTheory Filter
open StationaryMFG.Periodic
open StationaryMFG.Theorems.SimplePower (StrongVI_setForm)


/-! ### Phase B — paper-hypothesis closed-form aggregator
`mfgOperatorEpsPair_tendsto_set_additive_perturbation_of_paperHypotheses`

Per task `infra-P4-mfgOperatorEpsPair-tendsto-set-additive-perturbation-paperHyp`,
this is the closed-form aggregator that consumes only paper hypotheses
(`hpow, hRegH, hHat0, hFin, hAgree`), test-triple structural data
(measurabilities + a.e. nonnegativity of `m`), and a single dominator
pair `(Gh, hGh_memLp, hGh_bd)` for the HJB summand — and produces the
`mfgOperatorEpsPair_tendsto_set_additive_perturbation` conclusion.

The flux/mass summands need no dominators because the test triple
`(Dν, ν) = (0, 0)` forces both integrands to be pointwise zero. The
HJB η-factor `1_S` is bounded by `1` so a constant `Eh = 1` dominator
suffices internally (no authorised input needed). -/

/-- **Pointwise tendsto for the HJB integrand at the additive
perturbation `m + (1/(n+1)) · 1_S`.**

For a.e. `x`, the perturbation `μ_n x = m x + (1/(n+1)) · 1_S x`
converges to `μ_∞ x = m x` from above (since `1/(n+1) > 0` and
`1_S x ∈ {0, 1}`), so `H(x, Dυ x, μ_n x) → H(x, Dυ x, μ_∞ x)` follows
from the case split on `1_S x`:

* `x ∉ S` (`1_S x = 0`): `μ_n x = m x` is constant in `n`, trivial.
* `x ∈ S` (`1_S x = 1`): `μ_n x = m x + 1/(n+1) → m x`. Standard
  case-split on `m x = 0` (use `H_rc0_of_hHat0`/`hH_rc0`) vs
  `m x > 0` (use `RegularityH.continuous_H_pm`).

This is the additive-perturbation analogue of
`set_perturbation_pointwise_tendsto_H_of_hHat0`. -/
theorem additive_perturbation_pointwise_tendsto_H_of_hHat0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    {S : Set (Fin d → ℝ)}
    {m V υ : (Fin d → ℝ) → ℝ}
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun n : ℕ =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)) := by
  -- Right-continuity at zero for `H` from the paper hypotheses.
  have hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)) :=
    StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hHat0 hFin hAgree
  filter_upwards [hRegH.continuous_H_pm, hm_nn, hH_rc0]
    with x hx_cont hx_m_nn hx_rc0
  -- Set up the perturbation/limit at this `x`.
  set p : Fin d → ℝ := fun i => Dυ i x with hp_def
  set ind : ℝ := S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x with hind_def
  set μN : ℕ → ℝ := fun n => m x + (1 / ((n : ℝ) + 1)) * ind with hμN_def
  set μInf : ℝ := m x with hμInf_def
  -- `1/(n+1) → 0`.
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- `μ_n → μ_∞`.
  have h_μN_tendsto : Filter.Tendsto μN Filter.atTop (𝓝 μInf) := by
    have h1 :
        Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * ind)
          Filter.atTop (𝓝 0) := by
      have := h_one_div_tendsto.mul_const ind
      simpa using this
    have := h1.const_add (m x)
    simpa [hμN_def, hμInf_def, add_zero] using this
  -- `1/(n+1) > 0`.
  have h_one_div_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_pos.mpr hn1
  -- Indicator ≥ 0.
  have h_ind_nn : 0 ≤ ind := by
    rw [hind_def]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  -- `μ_n ≥ μInf` for all `n`.
  have hμN_ge : ∀ n, μInf ≤ μN n := by
    intro n
    show m x ≤ m x + (1 / ((n : ℝ) + 1)) * ind
    have h_prod_nn : 0 ≤ (1 / ((n : ℝ) + 1)) * ind :=
      mul_nonneg (le_of_lt (h_one_div_pos n)) h_ind_nn
    linarith
  -- `μInf ≥ 0` (from `hm_nn`).
  have hμInf_nn : 0 ≤ μInf := hx_m_nn
  -- Convergence of `m ↦ H x p m` to `H x p μInf` along `μ_n`.
  have h_H_tendsto :
      Filter.Tendsto (fun n : ℕ => H x p (μN n)) Filter.atTop
        (𝓝 (H x p μInf)) := by
    -- Case-split on `1_S x ∈ {0, 1}` (or more generally on `ind = 0`
    -- vs `ind > 0`). When `ind = 0`, `μ_n = μInf` constantly. When
    -- `ind > 0`, `μ_n > μInf` strictly so we further split on
    -- `μInf = 0` vs `μInf > 0`.
    by_cases h_ind0 : ind = 0
    · -- `ind = 0`: `μ_n = μInf` constantly.
      have h_const : ∀ n, μN n = μInf := by
        intro n
        show m x + (1 / ((n : ℝ) + 1)) * ind = m x
        rw [h_ind0]; ring
      have h_eq : (fun n => H x p (μN n)) = (fun _ => H x p μInf) := by
        funext n
        rw [h_const n]
      rw [h_eq]
      exact tendsto_const_nhds
    · -- `ind ≠ 0`, so `ind > 0` (since `ind ≥ 0`).
      have h_ind_pos : 0 < ind := lt_of_le_of_ne h_ind_nn (Ne.symm h_ind0)
      -- For each `n`, `(1/(n+1)) * ind > 0`, so `μ_n > μInf`.
      have hμN_gt : ∀ n, μInf < μN n := by
        intro n
        show m x < m x + (1 / ((n : ℝ) + 1)) * ind
        have : 0 < (1 / ((n : ℝ) + 1)) * ind :=
          mul_pos (h_one_div_pos n) h_ind_pos
        linarith
      -- Now case-split on `μInf = 0` vs `μInf > 0`.
      rcases eq_or_lt_of_le hμInf_nn with hμInf0 | hμInf_pos
      · -- `μInf = 0`: use right-continuity at zero (`hH_rc0`).
        have hμInf_zero : μInf = 0 := by linarith [hμInf0]
        -- `μ_n > 0` for all `n` (from `μ_n > μInf = 0`).
        have hμN_pos : ∀ n, (0 : ℝ) < μN n := by
          intro n
          have := hμN_gt n
          rw [hμInf_zero] at this
          exact this
        have h_rc := hx_rc0 p
        have h_μN_tendsto_zero : Filter.Tendsto μN Filter.atTop (𝓝 0) := by
          have := h_μN_tendsto
          rw [hμInf_zero] at this; exact this
        have h_eventually_pos :
            ∀ᶠ n in Filter.atTop, μN n ∈ Set.Ioi (0 : ℝ) :=
          Filter.Eventually.of_forall (fun n => hμN_pos n)
        have h_μN_tendsto_within :
            Filter.Tendsto μN Filter.atTop (𝓝[>] (0 : ℝ)) :=
          tendsto_nhdsWithin_iff.mpr ⟨h_μN_tendsto_zero,
            h_eventually_pos⟩
        have h_comp : Filter.Tendsto (fun n => H x p (μN n)) Filter.atTop
            (𝓝 (H x p 0)) := h_rc.comp h_μN_tendsto_within
        have h_eq : H x p μInf = H x p 0 := by rw [hμInf_zero]
        rw [h_eq]
        exact h_comp
      · -- `μInf > 0`: use ContinuousOn on the open positive-mass set.
        have h_pt_in : (p, μInf) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
          change 0 < μInf; exact hμInf_pos
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
  -- Combine: `-υ x - H x p (μ_n x) + V x → -υ x - H x p μInf + V x`.
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

/-- **Closed-form additive-perturbation aggregator from paper hypotheses.**

Discharges the three authorised inputs (`h_int1_n`, `h_int1_lim`,
`h_tendsto1`) of `mfgOperatorEpsPair_tendsto_set_additive_perturbation`
from paper-level hypotheses + a single HJB dominator pair
`(Gh, hGh_memLp, hGh_bd)`. The HJB η-factor `1_S` is bounded by `1`
so the η-side dominator can be taken as the constant `1` internally. -/
theorem mfgOperatorEpsPair_tendsto_set_additive_perturbation_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε γBar : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- Test-triple data + measurabilities.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ))
    (hS : MeasurableSet S)
    (hm : AEMeasurable m (volume.restrict (UnitCube d)))
    (hV : AEMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEMeasurable υ (volume.restrict (UnitCube d)))
    (hDυ : ∀ i, AEMeasurable (Dυ i) (volume.restrict (UnitCube d)))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    -- HJB dominator pair `(Gh, hGh_memLp, hGh_bd)`.
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
          ≤ Gh x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          Dυ
          (fun x => m x + (1 / ((n : ℝ) + 1)) *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            Dυ m υ
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ)))) := by
  -- Standing positivity facts on the paper exponents.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  have hβp_pos : 0 < (hpow.β + 1) / hpow.β :=
    div_pos hbb_pos hβ_pos
  have hHJB_pq : Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1) := by
    refine ⟨?_, hβp_pos, hbb_pos⟩
    field_simp
  -- Restricted measure (used everywhere below).
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm_def
  haveI : IsFiniteMeasure μm := by
    rw [hμm_def]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Indicator measurability.
  have h_ind_meas : Measurable
      (fun x : (Fin d → ℝ) => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    measurable_one.indicator hS
  -- HJB g-factor measurability (for each `n`).
  have hg_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
        μm := by
    intro n
    -- `μ_n := m + (1/(n+1)) · 1_S` is AE-measurable.
    have hμ : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        μm :=
      hm.add ((measurable_const.mul h_ind_meas).aemeasurable)
    have hDυ_pi : AEMeasurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) μm :=
      aemeasurable_pi_iff.mpr hDυ
    have hxpm : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => Dυ i x),
              m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) μm :=
      aemeasurable_id.prodMk (hDυ_pi.prodMk hμ)
    have hHcomp : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => Dυ i x)
            (m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) μm :=
      hpow.measurable_H.comp_aemeasurable hxpm
    exact (((hυ.neg).sub hHcomp).add hV).aestronglyMeasurable
  -- HJB η-factor (= `1_S`) measurability.
  have hη_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) μm :=
    h_ind_meas.aestronglyMeasurable
  -- HJB g-factor `MemLpPer` at `(β+1)/β` (per-`n`), via dominator.
  have hg_memLp_n : ∀ n : ℕ,
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (fun x =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x) := by
    intro n
    have hbd : ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
          ≤ (1 : ℝ) * ‖Gh x‖ := by
      filter_upwards [hGh_bd n] with x hx
      have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans hx
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hGh_nn, one_mul]
      exact hx
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hGh_memLp.toMemLp (hg_meas n) hbd)
  -- η-factor `MemLpPer` at `β+1` via the constant-1 dominator.
  -- `1_S x ∈ {0, 1}`, and the constant `1 ∈ Lᵝ⁺¹` on a finite measure.
  have h_const_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hη_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
        (fun x : (Fin d → ℝ) =>
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    have hbd : ∀ᵐ x ∂μm,
        ‖S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
          ≤ (1 : ℝ) * ‖(1 : ℝ)‖ := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [norm_one, mul_one, Real.norm_eq_abs]
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; simp
      · rw [Set.indicator_of_notMem hx]; simp
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul h_const_memLp.toMemLp hη_meas hbd)
  -- Per-`n` HJB integrability.
  have h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
          * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) μm := by
    intro n
    exact Periodic.MemLpPer.integrable_mul hHJB_pq (hg_memLp_n n) hη_memLp
  -- Pointwise tendsto for the HJB g-factor.
  have hPointwise_H :
      ∀ᵐ x ∂μm,
        Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  (m x + (1 / ((n : ℝ) + 1)) *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)) :=
    additive_perturbation_pointwise_tendsto_H_of_hHat0
      (V := V) hRegH hHat0 hFin hAgree (S := S) (m := m) (υ := υ) hm_nn Dυ
  -- HJB g-factor dominator bound passes to the limit.
  have hg_lim_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (m x) + V x) μm := by
    have hDυ_pi : AEMeasurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) μm :=
      aemeasurable_pi_iff.mpr hDυ
    have hxpm : AEMeasurable
        (fun x : (Fin d → ℝ) => (x, (fun i : Fin d => Dυ i x), m x)) μm :=
      aemeasurable_id.prodMk (hDυ_pi.prodMk hm)
    have hHcomp : AEMeasurable
        (fun x : (Fin d → ℝ) => H x (fun i => Dυ i x) (m x)) μm :=
      hpow.measurable_H.comp_aemeasurable hxpm
    exact (((hυ.neg).sub hHcomp).add hV).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x) (m x) + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
          ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(υ x) - H x (fun i => Dυ i x)
            (m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖)
      Filter.atTop
      (𝓝 ‖-(υ x) - H x (fun i => Dυ i x) (m x) + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  -- HJB g-factor `MemLpPer` at limit via dominator.
  have hg_lim_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (fun x => -(υ x) - H x (fun i => Dυ i x) (m x) + V x) := by
    have hbd : ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x) (m x) + V x‖
          ≤ (1 : ℝ) * ‖Gh x‖ := by
      filter_upwards [hGh_bd_lim, hGh_bd 0] with x hx h0
      have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans h0
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hGh_nn, one_mul]
      exact hx
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hGh_memLp.toMemLp hg_lim_meas hbd)
  -- Limit HJB integrability.
  have h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
          * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) μm :=
    Periodic.MemLpPer.integrable_mul hHJB_pq hg_lim_memLp hη_memLp
  -- Integral-tendsto via DCT helper `tendsto_setIntegral_HJB_mul_of_dom`.
  have hη_bd_one : ∀ n : ℕ,
      ∀ᵐ x ∂μm,
        ‖S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
          ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    intro _
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  have hη_const_lim : ∀ᵐ x ∂μm,
      Filter.Tendsto
        (fun _ : ℕ => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        Filter.atTop
        (𝓝 (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) :=
    Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
            * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
            * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := hpow.β) hβ_pos
      (gN := fun n x =>
        -(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
      (gInf := fun x =>
        -(υ x) - H x (fun i => Dυ i x) (m x) + V x)
      (ηN := fun _ x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (ηInf := fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      hGh_memLp hη_memLp hg_meas (fun _ => hη_meas) hGh_bd hη_bd_one
      hPointwise_H hη_const_lim
  -- Apply the headline aggregator.
  exact mfgOperatorEpsPair_tendsto_set_additive_perturbation
    (V := V) (H := H) (DpH := DpH) (γBar := γBar) (ε := ε)
    Dυ υ m S h_int1_n h_int1_lim h_tendsto1

/-! ### Sanity-check `example` for the paper-hypothesis aggregator.

Type-shape pin: from paper hypotheses + a single HJB dominator
`(Gh, hGh_memLp, hGh_bd)`, the closed-form aggregator produces the
`mfgOperatorEpsPair`-tendsto along the additive perturbation
`m + (1/(n+1)) · 1_S` against the test triple `(0, 1_S, 0)`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε γBar : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ))
    (hS : MeasurableSet S)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hDυ : ∀ i, Measurable (Dυ i))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
          ≤ Gh x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          Dυ
          (fun x => m x + (1 / ((n : ℝ) + 1)) *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            Dυ m υ
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ)))) :=
  mfgOperatorEpsPair_tendsto_set_additive_perturbation_of_paperHypotheses
    hpow hRegH hHat0 hFin hAgree
    Dυ υ m S hS hm.aemeasurable hV.aemeasurable hυ.aemeasurable
    (fun i => (hDυ i).aemeasurable) hm_nn Gh hGh_memLp hGh_bd

/-! ### Phase C — wrapper `SetAdditiveContinuityInputs.of_paperHypotheses`

Specialise the closed-form aggregator at the `RegularizedBareSolution`
projections `(sol.Du, sol.m, sol.u)`, threading `sol.hmNonneg` for
`hm_nn` and the embedded `MemLpPer`/`MemSobolevPer` measurabilities. -/

/-- **Producer for `SetAdditiveContinuityInputs`** from paper
hypotheses + measurabilities + a single HJB dominator pair on the
HJB integrand of the additive perturbation. This is the closed-form
analogue of `of_hCont`: it discharges `hCont` internally via the
new aggregator. -/
theorem SetAdditiveContinuityInputs.of_paperHypotheses
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hm : AEMeasurable sol.m (volume.restrict (UnitCube d)))
    (hV : AEMeasurable V (volume.restrict (UnitCube d)))
    (hu : AEMeasurable sol.u (volume.restrict (UnitCube d)))
    (hDu : ∀ i, AEMeasurable (sol.Du i) (volume.restrict (UnitCube d)))
    (Gh :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      ∀ (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
        (hSfin : (volume.restrict (UnitCube d)) S < ∞),
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (Gh S hS hSfin))
    (hGh_bd :
      ∀ (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
        (hSfin : (volume.restrict (UnitCube d)) S < ∞),
        ∀ n : ℕ,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖-(sol.u x) - H x (fun i => sol.Du i x)
                (sol.m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
            ≤ Gh S hS hSfin x) :
    SetAdditiveContinuityInputs (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') sol :=
  SetAdditiveContinuityInputs.of_hCont sol
    (fun S hS hSfin =>
      mfgOperatorEpsPair_tendsto_set_additive_perturbation_of_paperHypotheses
        hpow hRegH hHat0 hFin hAgree
        sol.Du sol.u sol.m S hS hm hV hu hDu sol.hmNonneg
        (Gh S hS hSfin) (hGh_memLp S hS hSfin) (hGh_bd S hS hSfin))

/-! ### Sanity-check `example` for the closed-form bundle producer. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hm : Measurable sol.m) (hV : Measurable V)
    (hu : Measurable sol.u) (hDu : ∀ i, Measurable (sol.Du i))
    (Gh :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      ∀ (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
        (hSfin : (volume.restrict (UnitCube d)) S < ∞),
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (Gh S hS hSfin))
    (hGh_bd :
      ∀ (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
        (hSfin : (volume.restrict (UnitCube d)) S < ∞),
        ∀ n : ℕ,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖-(sol.u x) - H x (fun i => sol.Du i x)
                (sol.m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
            ≤ Gh S hS hSfin x) :
    SetAdditiveContinuityInputs (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') sol :=
  SetAdditiveContinuityInputs.of_paperHypotheses sol
    hpow hRegH hHat0 hFin hAgree hm.aemeasurable hV.aemeasurable
    hu.aemeasurable (fun i => (hDu i).aemeasurable)
    Gh hGh_memLp hGh_bd

/-! ### Phase D — internal HJB-residual dominator producer.

Per `infra-P5-T10-drop-setDominator-from-residues`: build the per-`(S, n)`
HJB-residual dominator internally from the paper-form `RegularizedBareSolution`
data plus `hV ∈ MemLpPer β̄'` and the `Hat0` riders. The dominator does
*not* depend on `(S, hS, hSfin)` — it is the closed-form envelope
`Gh x := h.C * (‖Du‖^α + 1) + h.C * ((m + 1)^β + 1) + |u| + |V|`
which is a uniform upper bound for the HJB residual along the
perturbation `μ_n := m + (1/(n+1)) · 1_S` (since `m ≥ 0` and
`(1/(n+1)) · 1_S ∈ [0, 1]`, so `μ_n ∈ [m, m+1]`).

The shape of the producer matches `(Gh, hGh_memLp, hGh_bd)` consumed
by `SetAdditiveContinuityInputs.of_paperHypotheses`, which is
forwarded by `SetAdditiveContinuityInputs.of_paperHypotheses_closed`
below. -/

/-- **Internal HJB-residual dominator** for the additive set perturbation.

Given a `RegularizedBareSolution` at paper-form exponents
`(γ̄, β+1, β̄', γ̄')` together with `hpow`, `hHat0`, `hFin`, `hAgree`
and `hV : MemLpPer β̄' V`, produce a single `(Fin d → ℝ) → ℝ` upper
envelope `Gh` that bounds `‖-u - H(x, Du, m + (1/(n+1)) · 1_S) + V‖`
for every measurable `S ⊆ UnitCube d` of finite restricted-cube
measure and every `n : ℕ`, and lies in `MemLpPer β̄' = MemLpPer ((β+1)/β)`.

The dominator is `S`- and `n`-independent; the per-`(S, hS, hSfin)`
signature is bundled solely for downstream API compatibility. -/
theorem setDominator_of_paperHypotheses
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V) :
    ∃ Gh : (Fin d → ℝ) → ℝ,
      Periodic.MemLpPer
          (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh ∧
      (∀ (S : Set (Fin d → ℝ)),
         MeasurableSet S →
         (volume.restrict (UnitCube d)) S < ∞ →
         ∀ n : ℕ,
         ∀ᵐ x ∂(volume.restrict (UnitCube d)),
           ‖-(sol.u x) - H x (fun i => sol.Du i x)
                 (sol.m x + (1 / ((n : ℝ) + 1)) *
                   S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x‖
             ≤ Gh x) := by
  -- The unit cube has finite measure (used to embed constants in `MemLpPer`).
  haveI hcube_fin :
      IsFiniteMeasure
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Standing positivity facts.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  -- Identify `gammaBar hpow.α hpow.β = hpow.α * (hpow.β + 1) / hpow.β`.
  have hγeq : gammaBar hpow.α hpow.β
              = hpow.α * (hpow.β + 1) / hpow.β := rfl
  -- `m + 1 ∈ MemLpPer (β + 1)`.
  have h_m_plus_one_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
        (fun x : (Fin d → ℝ) => sol.m x + 1) := by
    have h_one : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
      MemLp.toMemLpPer (memLp_const (1 : ℝ))
    exact sol.hmLp.add h_one
  -- Build the dominator via `g_dominator_memLp_betaBar'` evaluated at
  -- `μ := m + 1`, `υ := u`, `Dυ := Du` and `C' := h.C`.
  set Gh : (Fin d → ℝ) → ℝ := fun x =>
    hpow.C * (‖fun i => sol.Du i x‖ ^ hpow.α + 1)
      + hpow.C * ((sol.m x + 1) ^ hpow.β + 1)
      + |sol.u x| + |V x| with hGh_def
  have hυ : Periodic.MemLpPer
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) sol.u := by
    have := sol.huLp
    -- `sol.huLp : MemLpPer (gammaBar hpow.α hpow.β) sol.u`.
    -- Rewrite using `hγeq`.
    simpa [hγeq] using this
  have hDυ : ∀ i,
      Periodic.MemLpPer
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (sol.Du i) := by
    intro i
    have := sol.hDuLp i
    simpa [hγeq] using this
  have hGh_memLp : Periodic.MemLpPer
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh :=
    g_dominator_memLp_betaBar' hpow V sol.u
      (fun x => sol.m x + 1) sol.Du
      h_m_plus_one_memLp hυ hDυ hV hpow.hC
  refine ⟨Gh, hGh_memLp, ?_⟩
  intro S hS _hSfin n
  -- Pointwise bound. Use `H_abs_bound_nonneg_of_hHat0` plus a triangle
  -- inequality and the comparison `(m + (1/(n+1))·1_S)^β ≤ (m + 1)^β`.
  have habs := H_abs_bound_nonneg_of_hHat0 hpow hHat0 hFin hAgree
  filter_upwards [habs, sol.hmNonneg] with x hxAbs hxμ
  -- Set local notation.
  set p_x : Fin d → ℝ := fun i => sol.Du i x with hp_x_def
  set tn : ℝ := 1 / ((n : ℝ) + 1) with htn_def
  have htn_nn : 0 ≤ tn := by
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      apply div_nonneg zero_le_one
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    exact this
  have htn_le_one : tn ≤ 1 := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hnp_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    rw [htn_def, div_le_one hnp_pos]
    linarith
  -- `1_S(x) ∈ {0, 1}`, in particular `1_S(x) ∈ [0, 1]`.
  have hind_nn : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS]
    · simp [Set.indicator_of_notMem hxS]
  have hind_le_one : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS]
    · simp [Set.indicator_of_notMem hxS]
  -- Define `μ_n := m + tn · 1_S` and prove `m ≤ μ_n ≤ m + 1`.
  set μn : ℝ :=
    sol.m x + tn * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x with hμn_def
  have hprod_nn :
      0 ≤ tn * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
    mul_nonneg htn_nn hind_nn
  have hprod_le_one :
      tn * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
    have h1 : tn * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              ≤ tn * 1 :=
      mul_le_mul_of_nonneg_left hind_le_one htn_nn
    have h2 : tn * 1 ≤ 1 := by simpa using htn_le_one
    linarith
  have hμn_nn : 0 ≤ μn := by
    rw [hμn_def]; linarith
  have hμn_le : μn ≤ sol.m x + 1 := by
    rw [hμn_def]; linarith
  -- Apply `hxAbs` at `(p_x, μn)`.
  have hH_abs : |H x p_x μn|
                ≤ hpow.C * (‖p_x‖ ^ hpow.α + 1)
                  + hpow.C * (μn ^ hpow.β + 1) :=
    hxAbs p_x μn hμn_nn
  -- Compare `μn^β ≤ (m + 1)^β` (rpow monotone for `β ≥ 0` and nonneg base).
  have hβ_nn : 0 ≤ hpow.β := hβ_pos.le
  have hμn_pow_le :
      μn ^ hpow.β ≤ (sol.m x + 1) ^ hpow.β := by
    have hbase_nn := hμn_nn
    exact Real.rpow_le_rpow hbase_nn hμn_le hβ_nn
  -- Triangle: `‖-u - H + V‖ ≤ |u| + |H| + |V|`.
  have htri :
      ‖-(sol.u x) - H x p_x μn + V x‖
        ≤ |sol.u x| + |H x p_x μn| + |V x| := by
    rw [Real.norm_eq_abs]
    have h1 : |(-(sol.u x)) - H x p_x μn + V x|
              ≤ |(-(sol.u x)) - H x p_x μn| + |V x| :=
      abs_add_le _ _
    have h2 : |(-(sol.u x)) - H x p_x μn|
              ≤ |-(sol.u x)| + |-(H x p_x μn)| := by
      have := abs_add_le (-(sol.u x)) (-(H x p_x μn))
      have heq : -(sol.u x) + -(H x p_x μn)
                  = (-(sol.u x)) - H x p_x μn := by ring
      rw [heq] at this
      exact this
    have h3 : |-(sol.u x)| = |sol.u x| := abs_neg _
    have h4 : |-(H x p_x μn)| = |H x p_x μn| := abs_neg _
    linarith
  -- Combine: `‖-u - H + V‖ ≤ Gh x`.
  have hC_nn : 0 ≤ hpow.C := hpow.hC.le
  -- Step 1: bound |H| using rpow comparison.
  have hH_abs_2 : |H x p_x μn|
                  ≤ hpow.C * (‖p_x‖ ^ hpow.α + 1)
                    + hpow.C * ((sol.m x + 1) ^ hpow.β + 1) := by
    have : hpow.C * (μn ^ hpow.β + 1)
            ≤ hpow.C * ((sol.m x + 1) ^ hpow.β + 1) := by
      have hle : μn ^ hpow.β + 1 ≤ (sol.m x + 1) ^ hpow.β + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hle hC_nn
    linarith
  -- Final bound.
  have hfinal :
      ‖-(sol.u x) - H x p_x μn + V x‖ ≤ Gh x := by
    have := htri
    have hbnd : |sol.u x| + |H x p_x μn| + |V x|
                ≤ |sol.u x|
                  + (hpow.C * (‖p_x‖ ^ hpow.α + 1)
                     + hpow.C * ((sol.m x + 1) ^ hpow.β + 1))
                  + |V x| := by linarith
    have hcombined :
        ‖-(sol.u x) - H x p_x μn + V x‖
          ≤ |sol.u x|
              + (hpow.C * (‖p_x‖ ^ hpow.α + 1)
                 + hpow.C * ((sol.m x + 1) ^ hpow.β + 1))
              + |V x| := le_trans htri hbnd
    -- Reorder the sum to match `Gh`.
    have heq : |sol.u x|
                + (hpow.C * (‖p_x‖ ^ hpow.α + 1)
                   + hpow.C * ((sol.m x + 1) ^ hpow.β + 1))
                + |V x|
              = Gh x := by
      rw [hGh_def, hp_x_def]; ring
    linarith
  -- Match: `μn` is exactly `sol.m x + (1/(n+1)) · 1_S(x)`, `p_x = fun i => sol.Du i x`.
  -- Both `μn` and `p_x` are `set`-introduced abbreviations and unfold definitionally.
  exact hfinal

/-- **Closed-form producer for `SetAdditiveContinuityInputs`** that
internalises the per-`(S, n)` HJB-residual dominator construction
(via `setDominator_of_paperHypotheses`). The caller no longer
threads `(Gh, hGh_memLp, hGh_bd)`. -/
theorem SetAdditiveContinuityInputs.of_paperHypotheses_closed
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (hV_memLp : Periodic.MemLpPer
                  (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hm : AEMeasurable sol.m (volume.restrict (UnitCube d)))
    (hV : AEMeasurable V (volume.restrict (UnitCube d)))
    (hu : AEMeasurable sol.u (volume.restrict (UnitCube d)))
    (hDu : ∀ i, AEMeasurable (sol.Du i) (volume.restrict (UnitCube d))) :
    SetAdditiveContinuityInputs (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') sol := by
  obtain ⟨Gh, hGh_memLp, hGh_bd⟩ :=
    setDominator_of_paperHypotheses hpow hHat0 hFin hAgree sol hV_memLp
  exact SetAdditiveContinuityInputs.of_paperHypotheses sol
    hpow hRegH hHat0 hFin hAgree hm hV hu hDu
    (fun _S _hS _hSfin => Gh)
    (fun _S _hS _hSfin => hGh_memLp)
    (fun S hS hSfin n => hGh_bd S hS hSfin n)

/-! ### Sanity-check `example` for `of_paperHypotheses_closed`. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (hV_memLp : Periodic.MemLpPer
                  (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hm : AEMeasurable sol.m (volume.restrict (UnitCube d)))
    (hV : AEMeasurable V (volume.restrict (UnitCube d)))
    (hu : AEMeasurable sol.u (volume.restrict (UnitCube d)))
    (hDu : ∀ i, AEMeasurable (sol.Du i) (volume.restrict (UnitCube d))) :
    SetAdditiveContinuityInputs (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') sol :=
  SetAdditiveContinuityInputs.of_paperHypotheses_closed
    hpow hRegH hHat0 hFin hAgree sol hV_memLp hm hV hu hDu

/-! ### Signed-multiplicative perturbation aggregator
`mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses`

Per `infra-P5-hHJ0-continuity-cert-discharge`, this is the closed-form
aggregator for the **signed-multiplicative** perturbation
```
μ_n := m + (1/(n+1)) · σ · m · 1_S,    μ_∞ := m
```
with the test triple held *constant* in `n` at
`(Dν, η, ν) = ((fun _ _ => 0), σ · m · 1_S, (fun _ => 0))`,
`σ ∈ {±1}`. This is the operator-continuity input consumed by
`strongVI_setForm_signed_of_hVIeps_set` and
`hjb_integrated_zero_of_RegularizedBareSolution`.

The perturbation factors as `μ_n x = m x · (1 + tn · σ · 1_S(x))`
with `tn := 1/(n+1) ∈ (0, 1]`, so it is a.e. nonneg and converges
pointwise to `m x`. As in the additive precedent, with `Dν = 0` and
`ν = 0`, two of the three `mfgOperatorPair` summands vanish
pointwise; only the HJB pair contributes. Continuity in mass is via
`RegularityH.continuous_H_pm` plus `H_rc0_of_hHat0`. -/

/-- **Pointwise tendsto for the HJB integrand at the signed-mul
perturbation `m + (1/(n+1)) · σ · m · 1_S`.**

For a.e. `x`, the perturbation `μ_n x = m x + tn·σ·m x·1_S x`
converges to `μ_∞ x = m x`. Case-split on `1_S x` and on `m x = 0`
vs `m x > 0`:

* `1_S x = 0` or `m x = 0`: `μ_n x = m x` constantly in `n`.
* `1_S x = 1` and `m x > 0`:
  - `σ = +1`: `μ_n x = m x · (1 + tn) > m x > 0`. Open-set continuity.
  - `σ = -1`: `μ_n x = m x · (1 - tn)`. For `n ≥ 1`, `tn ≤ 1/2 < 1`,
    so `μ_n x > 0`. Open-set continuity (eventually). -/
theorem signed_mul_perturbation_pointwise_tendsto_H_of_hHat0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
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
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x)
        Filter.atTop
        (𝓝 (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)) := by
  -- Right-continuity at zero for `H` from the paper hypotheses.
  have hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)) :=
    StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hHat0 hFin hAgree
  -- Sign bounds.
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  filter_upwards [hRegH.continuous_H_pm, hm_nn, hH_rc0]
    with x hx_cont hx_m_nn hx_rc0
  -- Set up the perturbation/limit at this `x`.
  set p : Fin d → ℝ := fun i => Dυ i x with hp_def
  set ind : ℝ := S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x with hind_def
  set μN : ℕ → ℝ :=
    fun n => m x + (1 / ((n : ℝ) + 1)) * σ * (m x * ind) with hμN_def
  set μInf : ℝ := m x with hμInf_def
  -- `1/(n+1) → 0`.
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- `μ_n → μ_∞`.
  have h_μN_tendsto : Filter.Tendsto μN Filter.atTop (𝓝 μInf) := by
    have h1 :
        Filter.Tendsto (fun n : ℕ =>
            (1 / ((n : ℝ) + 1)) * σ * (m x * ind))
          Filter.atTop (𝓝 0) := by
      have h_a := h_one_div_tendsto.mul_const σ
      have h_b := h_a.mul_const (m x * ind)
      simpa using h_b
    have := h1.const_add (m x)
    simpa [hμN_def, hμInf_def, add_zero] using this
  -- `1/(n+1) > 0`.
  have h_one_div_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact one_div_pos.mpr hn1
  -- Indicator ≥ 0 and ≤ 1.
  have h_ind_nn : 0 ≤ ind := by
    rw [hind_def]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have h_ind_le_one : ind ≤ 1 := by
    rw [hind_def]
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS]
    · simp [Set.indicator_of_notMem hxS]
  -- `μInf ≥ 0` (from `hm_nn`).
  have hμInf_nn : 0 ≤ μInf := hx_m_nn
  -- Convergence of `m ↦ H x p m` to `H x p μInf` along `μ_n`.
  have h_H_tendsto :
      Filter.Tendsto (fun n : ℕ => H x p (μN n)) Filter.atTop
        (𝓝 (H x p μInf)) := by
    -- Case split on whether `m x · ind = 0` (i.e., either `m x = 0` or
    -- `ind = 0`): then `μ_n = μInf` constantly.
    by_cases h_mInd0 : m x * ind = 0
    · -- Constant case.
      have h_const : ∀ n, μN n = μInf := by
        intro n
        show m x + (1 / ((n : ℝ) + 1)) * σ * (m x * ind) = m x
        rw [h_mInd0]; ring
      have h_eq : (fun n => H x p (μN n)) = (fun _ => H x p μInf) := by
        funext n; rw [h_const n]
      rw [h_eq]
      exact tendsto_const_nhds
    · -- `m x · ind ≠ 0`. Since `m x ≥ 0` and `ind ≥ 0`, both are > 0.
      have h_mInd_pos : 0 < m x * ind := by
        have h_le : 0 ≤ m x * ind := mul_nonneg hx_m_nn h_ind_nn
        exact lt_of_le_of_ne h_le (Ne.symm h_mInd0)
      have h_m_pos : 0 < m x := by
        rcases (mul_pos_iff.mp h_mInd_pos) with ⟨hp, _⟩ | ⟨hn, _⟩
        · exact hp
        · exact absurd hx_m_nn (not_le.mpr hn)
      have hμInf_pos : 0 < μInf := h_m_pos
      -- Show that `μ_n` is eventually positive.
      -- For `σ = -1`: `μ_n = m x - tn · m x · ind = m x · (1 - tn · ind)`.
      -- Since `0 ≤ ind ≤ 1` and `tn → 0`, eventually `tn · ind < 1`, so `μ_n > 0`.
      -- For `σ = +1`: `μ_n = m x + tn · m x · ind ≥ m x > 0` always.
      have h_eventually_pos : ∀ᶠ n in Filter.atTop, 0 < μN n := by
        rcases hσ with hσp | hσn
        · -- `σ = +1`: `μ_n ≥ m x > 0`.
          refine Filter.Eventually.of_forall (fun n => ?_)
          show 0 < m x + (1 / ((n : ℝ) + 1)) * σ * (m x * ind)
          have h_pos : 0 < (1 / ((n : ℝ) + 1)) * σ * (m x * ind) := by
            rw [hσp]
            have h1 : 0 < 1 / ((n : ℝ) + 1) := h_one_div_pos n
            nlinarith
          linarith
        · -- `σ = -1`: need `tn · ind < 1` eventually.
          -- Since `ind ≤ 1`, it suffices that `tn < 1`, i.e., `n ≥ 1`.
          have h_event :
              ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / ((n : ℝ) + 1) < 1 := by
            -- Eventually `n ≥ 1`, so `(n + 1) > 1`, so `1/(n+1) < 1`.
            refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
            have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
            rw [div_lt_one hpos]
            linarith
          filter_upwards [h_event] with n h_lt
          show 0 < m x + (1 / ((n : ℝ) + 1)) * σ * (m x * ind)
          rw [hσn]
          -- `m x + tn · (-1) · (m x · ind) = m x - tn · m x · ind = m x · (1 - tn · ind)`.
          have hfact :
              m x + (1 / ((n : ℝ) + 1)) * (-1) * (m x * ind)
                = m x * (1 - (1 / ((n : ℝ) + 1)) * ind) := by ring
          rw [hfact]
          have h_tn_pos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := h_one_div_pos n
          have h_tn_ind_le : (1 / ((n : ℝ) + 1)) * ind < 1 := by
            calc (1 / ((n : ℝ) + 1)) * ind
                ≤ (1 / ((n : ℝ) + 1)) * 1 :=
                  mul_le_mul_of_nonneg_left h_ind_le_one (le_of_lt h_tn_pos)
              _ < 1 := by rw [mul_one]; exact h_lt
          have h_factor_pos : 0 < 1 - (1 / ((n : ℝ) + 1)) * ind := by
            linarith
          exact mul_pos h_m_pos h_factor_pos
      -- Apply open-set continuity at `(p, μInf)` (using `μInf > 0`).
      have h_pt_in : (p, μInf) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
        change 0 < μInf; exact hμInf_pos
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
  -- Combine: `-υ x - H x p (μ_n x) + V x → -υ x - H x p μInf + V x`.
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

/-- **Closed-form signed-multiplicative aggregator from paper hypotheses.**

Discharges the signed-perturbation operator-continuity certificate
(`hCont_signed`) consumed by `strongVI_setForm_signed_of_hVIeps_set`
and `hjb_integrated_zero_of_RegularizedBareSolution`, from paper-level
hypotheses (`hpow, hRegH, hHat0, hFin, hAgree`) plus a single HJB
dominator pair `(Gh, hGh_memLp, hGh_bd)` and an `m ∈ L^{β+1}_per`
certificate (used to build the `Lᵝ⁺¹` envelope on the test direction
`σ · m · 1_S`).

Mirrors `mfgOperatorEpsPair_tendsto_set_additive_perturbation_of_paperHypotheses`
(this module) but for the multiplicative signed perturbation. -/
theorem mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε γBar : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- Test-triple data + measurabilities.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ))
    (hS : MeasurableSet S)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hDυ : ∀ i, Measurable (Dυ i))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    -- `m ∈ L^{β+1}_per` (for the test-direction `σ·m·1_S` envelope).
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) m)
    -- HJB dominator pair `(Gh, hGh_memLp, hGh_bd)`.
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x‖
          ≤ Gh x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          Dυ
          (fun x => m x + (1 / ((n : ℝ) + 1)) * σ *
                      (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          υ
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            Dυ m υ
            (fun _ _ => (0 : ℝ))
            (fun x => σ * m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)))) := by
  -- Standing positivity facts on the paper exponents.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  have hβp_pos : 0 < (hpow.β + 1) / hpow.β :=
    div_pos hbb_pos hβ_pos
  have hHJB_pq : Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1) := by
    refine ⟨?_, hβp_pos, hbb_pos⟩
    field_simp
  -- Restricted measure (used everywhere below).
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm_def
  haveI : IsFiniteMeasure μm := by
    rw [hμm_def]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Sign bounds.
  have hσ_abs : |σ| ≤ 1 := by rcases hσ with h | h <;> simp [h]
  -- Indicator measurability.
  have h_ind_meas : Measurable
      (fun x : (Fin d → ℝ) => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    measurable_one.indicator hS
  -- Test-direction `σ · m · 1_S` measurability.
  have h_test_meas : Measurable
      (fun x : (Fin d → ℝ) =>
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    ((measurable_const.mul hm).mul h_ind_meas)
  -- HJB g-factor measurability (for each `n`).
  have hg_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x)
        μm := by
    intro n
    -- `μ_n := m + tn · σ · (m · 1_S)` is measurable.
    have hmInd : Measurable
        (fun x : (Fin d → ℝ) =>
          m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      hm.mul h_ind_meas
    have hμ : Measurable
        (fun x : (Fin d → ℝ) =>
          m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) :=
      hm.add ((measurable_const.mul measurable_const).mul hmInd)
    have hDυ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
      measurable_pi_iff.mpr hDυ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => Dυ i x),
              m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))) :=
      measurable_id.prodMk (hDυ_pi.prodMk hμ)
    have hHcomp : Measurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => Dυ i x)
            (m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))) :=
      hpow.measurable_H.comp hxpm
    exact (((hυ.neg).sub hHcomp).add hV).aestronglyMeasurable
  -- HJB η-factor (= `σ · m · 1_S`) measurability.
  have hη_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) μm :=
    h_test_meas.aestronglyMeasurable
  -- HJB g-factor `MemLpPer` at `(β+1)/β` (per-`n`), via dominator.
  have hg_memLp_n : ∀ n : ℕ,
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (fun x =>
          -(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x) := by
    intro n
    have hbd : ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x‖
          ≤ (1 : ℝ) * ‖Gh x‖ := by
      filter_upwards [hGh_bd n] with x hx
      have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans hx
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hGh_nn, one_mul]
      exact hx
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hGh_memLp.toMemLp (hg_meas n) hbd)
  -- η-factor `MemLpPer` at `β+1` via the `m`-dominator.
  -- `|σ · m x · 1_S(x)| ≤ |m x|`, and `m ∈ Lᵝ⁺¹`.
  have hη_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
        (fun x : (Fin d → ℝ) =>
          σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    have hbd : ∀ᵐ x ∂μm,
        ‖σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
          ≤ (1 : ℝ) * ‖m x‖ := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_mul, one_mul]
      have h_ind_nn : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        by_cases hxS : x ∈ S
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_notMem hxS]
      have h_ind_le_one : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
        by_cases hxS : x ∈ S
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_notMem hxS]
      have h_ind_abs_le_one :
          |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
        rw [abs_of_nonneg h_ind_nn]; exact h_ind_le_one
      -- `|σ| · |m x| · |1_S(x)| ≤ 1 · |m x| · 1 = |m x|`.
      have h_step1 : |σ| * |m x| ≤ 1 * |m x| :=
        mul_le_mul_of_nonneg_right hσ_abs (abs_nonneg _)
      have h_step2 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * 1 := by
        have h_a :
            |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| :=
          mul_le_mul_of_nonneg_right h_step1 (abs_nonneg _)
        have h_b :
            1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * 1 :=
          mul_le_mul_of_nonneg_left h_ind_abs_le_one
            (mul_nonneg zero_le_one (abs_nonneg _))
        linarith
      linarith
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hm_memLp.toMemLp hη_meas hbd)
  -- Per-`n` HJB integrability.
  have h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x)
          * (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) μm := by
    intro n
    exact Periodic.MemLpPer.integrable_mul hHJB_pq (hg_memLp_n n) hη_memLp
  -- Pointwise tendsto for the HJB g-factor.
  have hPointwise_H :
      ∀ᵐ x ∂μm,
        Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => Dυ i x)
                  (m x + (1 / ((n : ℝ) + 1)) * σ *
                    (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
                + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)) :=
    signed_mul_perturbation_pointwise_tendsto_H_of_hHat0
      (V := V) hRegH hHat0 hFin hAgree (S := S) (m := m) (υ := υ)
      hm_nn σ hσ Dυ
  -- HJB g-factor dominator bound passes to the limit.
  have hg_lim_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (m x) + V x) μm := by
    have hDυ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Dυ i x)) :=
      measurable_pi_iff.mpr hDυ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) => (x, (fun i : Fin d => Dυ i x), m x)) :=
      measurable_id.prodMk (hDυ_pi.prodMk hm)
    have hHcomp : Measurable
        (fun x : (Fin d → ℝ) => H x (fun i => Dυ i x) (m x)) :=
      hpow.measurable_H.comp hxpm
    exact (((hυ.neg).sub hHcomp).add hV).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x) (m x) + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x‖
          ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(υ x) - H x (fun i => Dυ i x)
            (m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            + V x‖)
      Filter.atTop
      (𝓝 ‖-(υ x) - H x (fun i => Dυ i x) (m x) + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  -- HJB g-factor `MemLpPer` at limit via dominator.
  have hg_lim_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (fun x => -(υ x) - H x (fun i => Dυ i x) (m x) + V x) := by
    have hbd : ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => Dυ i x) (m x) + V x‖
          ≤ (1 : ℝ) * ‖Gh x‖ := by
      filter_upwards [hGh_bd_lim, hGh_bd 0] with x hx h0
      have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans h0
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hGh_nn, one_mul]
      exact hx
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hGh_memLp.toMemLp hg_lim_meas hbd)
  -- Limit HJB integrability.
  have h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
          * (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) μm :=
    Periodic.MemLpPer.integrable_mul hHJB_pq hg_lim_memLp hη_memLp
  -- η-factor pointwise bound (constant in `n`): `‖σ·m·1_S‖ ≤ |m| · 1` —
  -- but actually the helper `tendsto_setIntegral_HJB_mul_of_dom` wants
  -- `‖ηN n x‖ ≤ E x` where `E ∈ L^{β+1}_per`. We pick `E := |m|` via
  -- the simple bound `‖σ·m·1_S‖ ≤ |m|`.
  set Eη : (Fin d → ℝ) → ℝ := fun x => |m x| with hEη_def
  have hEη_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eη := by
    -- `|m x|` has the same L^p seminorm as `m`.
    have h := hm_memLp
    -- `Periodic.MemLpPer p f ↔ Periodic.MemLpPer p (fun x => |f x|)`
    -- via `MemLp.norm` (Mathlib).
    have h_abs : MemLp (fun x => |m x|)
        (ENNReal.ofReal (hpow.β + 1))
        (volume.restrict (UnitCube d)) := by
      have := h.toMemLp.norm
      simpa [Real.norm_eq_abs] using this
    exact MemLp.toMemLpPer h_abs
  have hη_bd_E : ∀ n : ℕ,
      ∀ᵐ x ∂μm,
        ‖σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
          ≤ Eη x := by
    intro _
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Real.norm_eq_abs, hEη_def]
    rw [abs_mul, abs_mul]
    have h_ind_nn : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_notMem hxS]
    have h_ind_le_one : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_notMem hxS]
    have h_ind_abs_le_one :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg h_ind_nn]; exact h_ind_le_one
    have h_step1 : |σ| * |m x| ≤ 1 * |m x| :=
      mul_le_mul_of_nonneg_right hσ_abs (abs_nonneg _)
    have h_step2 :
        |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
          ≤ 1 * |m x| * 1 := by
      have h_a :
          |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| :=
        mul_le_mul_of_nonneg_right h_step1 (abs_nonneg _)
      have h_b :
          1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * 1 :=
        mul_le_mul_of_nonneg_left h_ind_abs_le_one
          (mul_nonneg zero_le_one (abs_nonneg _))
      linarith
    linarith
  -- η-factor pointwise tendsto: constant.
  have hη_const_lim : ∀ᵐ x ∂μm,
      Filter.Tendsto
        (fun _ : ℕ => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        Filter.atTop
        (𝓝 (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) :=
    Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  -- HJB integral-tendsto via DCT helper.
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
                + V x)
            * (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
            * (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := hpow.β) hβ_pos
      (gN := fun n x =>
        -(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            + V x)
      (gInf := fun x =>
        -(υ x) - H x (fun i => Dυ i x) (m x) + V x)
      (ηN := fun _ x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (ηInf := fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      hGh_memLp hEη_memLp hg_meas (fun _ => hη_meas) hGh_bd hη_bd_E
      hPointwise_H hη_const_lim
  -- Now apply the consumer-level lemma directly: with `Dν = 0`, `ν = 0`,
  -- two of the three `mfgOperatorPair` summands vanish pointwise.
  have h_dot_zero : ∀ (x : Fin d → ℝ) (μx : ℝ),
      DpH x (fun i => Dυ i x) μx ⬝ (fun _ : Fin d => (0 : ℝ)) = 0 := by
    intro x μx
    unfold StationaryMFG.Hamiltonian.euclideanDot
    simp
  -- Summand 2 (flux) integrand pointwise zero.
  have h_int2_eq_n : ∀ n : ℕ,
      (fun x =>
        (m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              ⬝ (fun i => (0 : ℝ))))
        = (fun _ => (0 : ℝ)) := by
    intro n
    funext x
    rw [h_dot_zero]
    ring
  have h_int2_eq_lim :
      (fun x =>
        m x * (DpH x (fun i => Dυ i x) (m x)
            ⬝ (fun i => (0 : ℝ))))
        = (fun _ => (0 : ℝ)) := by
    funext x
    rw [h_dot_zero]
    ring
  have h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              ⬝ (fun i => (0 : ℝ)))) μm := by
    intro n
    rw [h_int2_eq_n n]
    exact integrable_zero _ _ _
  have h_int2_lim :
      Integrable (fun x =>
        m x * (DpH x (fun i => Dυ i x) (m x)
            ⬝ (fun i => (0 : ℝ)))) μm := by
    rw [h_int2_eq_lim]
    exact integrable_zero _ _ _
  -- Summand 3 (mass) integrand pointwise zero.
  have h_int3_eq_n : ∀ n : ℕ,
      (fun x =>
        ((m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) - 1)
          * (0 : ℝ))
        = (fun _ => (0 : ℝ)) := by
    intro n; funext x; ring
  have h_int3_eq_lim :
      (fun x => (m x - 1) * (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
    funext x; ring
  have h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        ((m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) - 1)
          * (0 : ℝ)) μm := by
    intro n; rw [h_int3_eq_n n]; exact integrable_zero _ _ _
  have h_int3_lim :
      Integrable (fun x => (m x - 1) * (0 : ℝ)) μm := by
    rw [h_int3_eq_lim]; exact integrable_zero _ _ _
  -- Summand 2 / 3 integral-tendstos: both reduce to `tendsto_const_nhds 0`.
  have h_tendsto2 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
                ⬝ (fun i => (0 : ℝ))))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          m x * (DpH x (fun i => Dυ i x) (m x)
              ⬝ (fun i => (0 : ℝ))))) := by
    have h1 : ∀ n : ℕ,
        (∫ x in UnitCube d,
            (m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              * (DpH x (fun i => Dυ i x)
                  (m x + (1 / ((n : ℝ) + 1)) * σ *
                    (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
                  ⬝ (fun i => (0 : ℝ))))
          = 0 := by
      intro n
      rw [show (fun x =>
            (m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) * σ *
                  (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
                ⬝ (fun i => (0 : ℝ))))
          = (fun _ => (0 : ℝ)) from h_int2_eq_n n]
      simp
    have h2 : (∫ x in UnitCube d,
        m x * (DpH x (fun i => Dυ i x) (m x)
            ⬝ (fun i => (0 : ℝ)))) = 0 := by
      rw [h_int2_eq_lim]; simp
    rw [h2]
    have : (fun n : ℕ => ∫ x in UnitCube d,
        (m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          * (DpH x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              ⬝ (fun i => (0 : ℝ))))
        = (fun _ => (0 : ℝ)) := by
      funext n; exact h1 n
    rw [this]
    exact tendsto_const_nhds
  have h_tendsto3 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          ((m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) - 1)
            * (0 : ℝ))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (m x - 1) * (0 : ℝ))) := by
    have h1 : ∀ n : ℕ,
        (∫ x in UnitCube d,
            ((m x + (1 / ((n : ℝ) + 1)) * σ *
              (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) - 1)
              * (0 : ℝ)) = 0 := by
      intro n
      rw [h_int3_eq_n n]; simp
    have h2 : (∫ x in UnitCube d, (m x - 1) * (0 : ℝ)) = 0 := by
      rw [h_int3_eq_lim]; simp
    rw [h2]
    have : (fun n : ℕ => ∫ x in UnitCube d,
        ((m x + (1 / ((n : ℝ) + 1)) * σ *
            (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) - 1)
          * (0 : ℝ))
        = (fun _ => (0 : ℝ)) := by
      funext n; exact h1 n
    rw [this]
    exact tendsto_const_nhds
  -- Apply the consumer-level lemma.
  exact mfgOperatorEpsPair_tendsto_of_summands
    (V := V) (H := H) (DpH := DpH) (γBar := γBar) (ε := ε)
    Dυ υ (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (μN := fun n x =>
      m x + (1 / ((n : ℝ) + 1)) * σ *
        (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    (μInf := m)
    (ηN := fun _ x =>
      σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (ηInf := fun x =>
      σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    h_int1_n h_int2_n h_int3_n
    h_int1_lim h_int2_lim h_int3_lim
    h_tendsto1 h_tendsto2 h_tendsto3

/-! ### Sanity-check `example` for the signed-perturbation aggregator. -/

example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε γBar : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ))
    (hS : MeasurableSet S)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hDυ : ∀ i, Measurable (Dυ i))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) m)
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) * σ *
                (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x‖
          ≤ Gh x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          Dυ
          (fun x => m x + (1 / ((n : ℝ) + 1)) * σ *
                      (m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          υ
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            Dυ m υ
            (fun _ _ => (0 : ℝ))
            (fun x => σ * m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)))) :=
  mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses
    hpow hRegH hHat0 hFin hAgree
    Dυ υ m σ hσ S hS hm hV hυ hDυ hm_nn hm_memLp Gh hGh_memLp hGh_bd

/-! ## Phase 5 closure — paper HJ0 integrated identity

`infra-P5-theorem1-closed-phase1-hHJ0-equality-from-RegularizedBareSolution`.

Goal: produce the integrated HJ0 identity
```
∫ x in UnitCube d, sol.m x · (sol.u x + H x (Du · x) (m x) − V x) ∂volume = 0
```
from a `RegularizedBareSolution`, matching the
`RegularizedPaperSolutionData.hHJ0` field shape.

### Strategy

The bare-record VI fields evaluate `H` at the *perturbed* density
`m + σ · m · 1_S` (rather than at `m`), so naive parity addition of
`σ ∈ {+1, -1}` cases of `hVIeps_signed` does not cancel the
H-evaluation. We therefore mirror the existing Minty bridge
`strongVI_setForm_of_hVIeps_set`, but applied with a multiplicative
perturbation `ρ_n := m + tn · σ · m · 1_S`:

1. Apply `sol.hVIeps_set` at `(Set.univ, ρ_n, sol.u, sol.Du)`. The
   density direction collapses to `tn · σ · m · 1_S`, the gradient
   direction to `0`, the value direction to `0`.
2. Factor `tn > 0` out of the test triple and divide.
3. Pass `n → ∞` via the authorised operator-continuity input
   `hCont_signed`, landing at
   `0 ≤ mfgOperatorEpsPair γBar ε sol.Du sol.m sol.u 0 (σ·m·1_S) 0`,
   which is exactly `StrongVI_setForm_signed`.
4. Apply `lem_strong_is_strong_HJB_eq_paperForm` (already in
   `StrongIsStrong.lean`) to get the a.e. equality
   `(u + H − V) · m = 0` on the cube.
5. Integrate (a.e.-zero ⇒ integral-zero) to land at the target. -/

open StationaryMFG.Theorems.SimplePower (StrongVI_setForm_signed)

/-- **Signed Minty/δ-limit bridge** from `RegularizedBareSolution.hVIeps_set`
to `StrongVI_setForm_signed` at `(sol.Du, sol.m, sol.u)`.

Mirrors `strongVI_setForm_of_hVIeps_set` but uses the multiplicative
perturbation `ρ_n := m + tn · σ · m · 1_S` (admissible: nonneg since
`tn ∈ (0, 1]`, `σ ∈ {±1}`, `0 ≤ 1_S ≤ 1`, and `m ≥ 0` a.e.). -/
theorem strongVI_setForm_signed_of_hVIeps_set
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    -- For every measurable `S` of finite restricted-cube measure, the
    -- signed-perturbation density `ρ_n := m + (1/(n+1)) · σ · m · 1_S`
    -- lies in `Lᵝ` on the cube. (Authorised: `m ∈ Lᵝ` plus boundedness
    -- of `σ · 1_S`. The discharge from `sol.hmLp` plus `hmNonneg` is
    -- routine via `MemLp.of_le_mul`; we thread it as input to mirror
    -- the precedent of `strongVI_setForm_of_hVIeps_set`.)
    (hRhoMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
      ∀ n : ℕ,
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)))
    -- For every measurable `S` of finite restricted-cube measure, the
    -- "perturbation direction" `σ · m · 1_S` lies in `Lᵝ` on the cube.
    (hSigmaMIndicMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    -- Authorised input: operator-continuity along the multiplicative
    -- signed perturbation `ρ_n := sol.m + (1/(n+1)) · σ · sol.m · 1_S`,
    -- with the test triple held at `(0, σ·m·1_S, 0)`.
    (hCont_signed :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (fun x => σ * sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ))))) :
    StrongVI_setForm_signed V H DpH γBarReal ε sol.Du sol.m sol.u := by
  classical
  intro σ hσ S hS_meas hS_fin
  -- Shorthand.
  set f : (Fin d → ℝ) → ℝ :=
    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) with hf_def
  -- Pointwise nonnegativity of `f = 1_S` and bound `f ≤ 1`.
  have hf_nn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hxS : x ∈ S
    · simp [hf_def, Set.indicator_of_mem hxS]
    · simp [hf_def, Set.indicator_of_notMem hxS]
  have hf_le_one : ∀ x, f x ≤ 1 := by
    intro x
    by_cases hxS : x ∈ S
    · simp [hf_def, Set.indicator_of_mem hxS]
    · simp [hf_def, Set.indicator_of_notMem hxS]
  -- Per-`n` step: `0 ≤ mfgOperatorEpsPair … sol.Du (sol.m + tn·σ·m·1_S) sol.u 0 (σ·m·1_S) 0`.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x * f x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x * f x)
              (fun _ => (0 : ℝ)) := by
    intro n
    -- `tn := 1/(n+1) > 0` and `tn ≤ 1`.
    set tn : ℝ := 1 / ((n : ℝ) + 1) with htn_def
    have htn_pos : (0 : ℝ) < tn := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have htn_le_one : tn ≤ 1 := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rw [htn_def, div_le_one hpos]
      exact hge
    -- Sign value bound: `|σ · 1_S(x)| ≤ 1`, hence `tn · σ · 1_S(x) ≥ -1`,
    -- hence `1 + tn · σ · 1_S(x) ≥ 0`.
    have hσ_abs_le : |σ| ≤ 1 := by
      rcases hσ with rfl | rfl
      · simp
      · simp
    have h_factor_nn : ∀ x, 0 ≤ 1 + tn * σ * f x := by
      intro x
      have h1 : |tn * σ * f x| ≤ 1 := by
        have h2 : |tn * σ * f x| = tn * |σ| * f x := by
          have hfabs : |f x| = f x := abs_of_nonneg (hf_nn x)
          rw [abs_mul, abs_mul, abs_of_pos htn_pos, hfabs]
        rw [h2]
        have hle : tn * |σ| * f x ≤ 1 * 1 * 1 := by
          have := mul_le_mul (mul_le_mul htn_le_one hσ_abs_le (abs_nonneg _) zero_le_one)
                    (hf_le_one x) (hf_nn x) (by positivity)
          simpa using this
        linarith
      have h3 : -1 ≤ tn * σ * f x := by
        have := abs_le.mp h1
        linarith [this.1]
      linarith
    -- Build the perturbed density `ρ_n := m + tn · σ · m · 1_S`.
    set ρ : (Fin d → ℝ) → ℝ :=
      fun x => sol.m x + tn * σ * (sol.m x * f x) with hρ_def
    -- `ρ ≥ 0` a.e.: `ρ x = m x · (1 + tn·σ·1_S(x))`.
    have hρ_nn :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          0 ≤ ρ x := by
      filter_upwards [sol.hmNonneg] with x hxm
      have hfact : ρ x = sol.m x * (1 + tn * σ * f x) := by
        change sol.m x + tn * σ * (sol.m x * f x)
              = sol.m x * (1 + tn * σ * f x)
        ring
      rw [hfact]
      exact mul_nonneg hxm (h_factor_nn x)
    -- `MemLpPer βBar ρ` (authorised input).
    have hρ_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ := by
      have h := hRhoMemLp σ hσ S hS_meas hS_fin n
      -- `h` is at the function `fun x => sol.m x + tn * σ * (sol.m x * f x)`,
      -- which is exactly `ρ` by definition (modulo `tn` unfold).
      have heq :
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            = ρ := by
        funext x
        change sol.m x + (1 / ((n : ℝ) + 1)) * σ *
              (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            = sol.m x + tn * σ * (sol.m x * f x)
        rw [htn_def, hf_def]
      rw [heq] at h
      exact h
    -- `MemLpPer βBar (Set.univ.indicator ρ) = MemLpPer βBar ρ`.
    have hSρ_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (Set.univ.indicator ρ) := by
      have heq : (Set.univ.indicator ρ : (Fin d → ℝ) → ℝ) = ρ := by
        funext x; simp
      rw [heq]; exact hρ_memLp
    -- `MemSobolevPer γBar sol.u` and `MemLpPer γBar (sol.Du i)`.
    have hu_memSob :
        MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) sol.u :=
      sol.memSobolevPer_u
    have hDu_memLp :
        ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (sol.Du i) :=
      sol.hDuLp
    -- Apply the bare-record set-form VI field at `(Set.univ, ρ, sol.u, sol.Du)`.
    have hVI := sol.hVIeps_set Set.univ MeasurableSet.univ ρ sol.u sol.Du
                  hρ_nn hSρ_memLp hu_memSob hDu_memLp sol.hWeakDeriv
    -- Step 1: rewrite primal density via `Set.indicator_univ`.
    have hρ_eq : Set.univ.indicator ρ = ρ := by
      funext x; simp
    rw [hρ_eq] at hVI
    -- Step 2: rewrite test triple `(0, ρ - sol.m, 0)` to `(0, tn·σ·m·f, 0)`.
    have hDν_ae : ∀ i,
        (fun x => sol.Du i x - sol.Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      intro i
      refine Filter.Eventually.of_forall ?_
      intro x; simp
    have hη_ae :
        (ρ - sol.m)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun x => tn * σ * (sol.m x * f x)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      change ρ x - sol.m x = tn * σ * (sol.m x * f x)
      simp [hρ_def]
    have hν_ae :
        (sol.u - sol.u)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x; simp [Pi.sub_apply]
    have hcongr := mfgOperatorEpsPair_congr_ae
      (V := V) (H := H) (DpH := DpH)
      γBarReal ε
      sol.Du ρ sol.u
      (fun i x => sol.Du i x - sol.Du i x)
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      (ρ - sol.m)
      (fun x => tn * σ * (sol.m x * f x))
      (sol.u - sol.u)
      (fun _ : Fin d → ℝ => (0 : ℝ))
      hDν_ae hη_ae hν_ae
    rw [hcongr] at hVI
    -- Step 3: factor `tn` out of the test triple via
    -- `mfgOperatorEpsPair_test_smul`.
    -- Note: `tn · σ · (m · f) = tn · (σ · m · f)`, so we factor `tn`
    -- and leave `σ · m · f` as the unscaled direction.
    have hsmul := mfgOperatorEpsPair_test_smul
      (V := V) (H := H) (DpH := DpH)
      γBarReal ε
      sol.Du ρ sol.u
      tn
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      (fun x => σ * sol.m x * f x)
      (fun _ : Fin d → ℝ => (0 : ℝ))
    have hDν_smul_eq :
        (fun i : Fin d => tn • ((fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i))
          = (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) := by
      funext i; funext x
      change tn • (0 : ℝ) = (0 : ℝ)
      simp
    have hη_smul_eq :
        (tn • (fun x => σ * sol.m x * f x) : (Fin d → ℝ) → ℝ)
          = fun x => tn * σ * (sol.m x * f x) := by
      funext x
      change tn • (σ * sol.m x * f x) = tn * σ * (sol.m x * f x)
      simp [smul_eq_mul]; ring
    have hν_smul_eq :
        (tn • (fun _ : Fin d → ℝ => (0 : ℝ)) : (Fin d → ℝ) → ℝ)
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      change tn • (0 : ℝ) = (0 : ℝ)
      simp
    rw [hDν_smul_eq, hη_smul_eq, hν_smul_eq] at hsmul
    -- Now `hsmul`:
    --   mfgOperatorEpsPair γBar ε sol.Du ρ sol.u 0 (fun x => tn·σ·(m·f)) 0
    --     = tn * mfgOperatorEpsPair γBar ε sol.Du ρ sol.u 0 (σ·m·f) 0
    rw [hsmul] at hVI
    -- Divide by `tn > 0`.
    have hVI' :
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du ρ sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x * f x)
              (fun _ => (0 : ℝ)) :=
      (mul_nonneg_iff_of_pos_left htn_pos).mp hVI
    -- Identify `ρ` with the explicit `(fun x => sol.m x + tn·σ·(m·f))`.
    have hρ_unfold :
        ρ = fun x => sol.m x + tn * σ * (sol.m x * f x) := rfl
    rw [hρ_unfold] at hVI'
    exact hVI'
  -- Pass `n → ∞` via `hCont_signed`.
  -- The `hStep n` shape uses `1/((n:ℝ)+1)` and `f := S.indicator (fun _ => 1)`;
  -- align it with the `hCont_signed σ hσ S hS_meas hS_fin` filter shape.
  have hStep' :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)) := by
    intro n
    have h := hStep n
    -- `f` unfolds to `S.indicator (fun _ => 1)`; substitute.
    simpa [hf_def] using h
  exact ge_of_tendsto' (hCont_signed σ hσ S hS_meas hS_fin) hStep'

/-- **Headline lemma — paper HJ0 integrated identity from a
`RegularizedBareSolution`.**

Conclusion (matches `RegularizedPaperSolutionData.hHJ0`):
```
∫ x in UnitCube d, sol.m x · (sol.u x + H x (Du · x) (m x) − V x) ∂volume = 0.
```

Proof: combine `strongVI_setForm_signed_of_hVIeps_set` (Minty bridge,
this module) with `lem_strong_is_strong_HJB_eq_paperForm` (already in
`StrongIsStrong.lean`) to obtain `(u + H − V) · m =ᵐ 0` on the cube,
then integrate. -/
theorem hjb_integrated_zero_of_RegularizedBareSolution
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hRhoMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
      ∀ n : ℕ,
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)))
    (hSigmaMIndicMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    (hCont_signed :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (fun x => σ * sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)))))
    -- Integrability of the residual times the density on the cube.
    (hResM :
      MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
            * sol.m x)
        (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d,
        sol.m x * (sol.u x +
            H x (fun i => sol.Du i x) (sol.m x) - V x)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
      = 0 := by
  -- Step 1: get `StrongVI_setForm_signed` from the Minty bridge.
  have hSigned : StrongVI_setForm_signed V H DpH γBarReal ε sol.Du sol.m sol.u :=
    strongVI_setForm_signed_of_hVIeps_set sol hRhoMemLp hSigmaMIndicMemLp
      hCont_signed
  -- Step 2: get the a.e. identity `(u + H − V) · m = 0` on the cube.
  have hpaperForm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x) * sol.m x = 0 :=
    StationaryMFG.Theorems.SimplePower.lem_strong_is_strong_HJB_eq_paperForm
      (V := V) (H := H) (DpH := DpH)
      γBarReal ε sol.Du sol.m sol.u hResM hSigned
  -- Step 3: integrate the a.e.-zero function. The integrand of the goal
  -- differs from `hpaperForm`'s integrand only by commutativity of `*`.
  have hae :
      (fun x => sol.m x *
          (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
        =ᵐ[volume.restrict (UnitCube d)] (fun _ => (0 : ℝ)) := by
    refine hpaperForm.mono ?_
    intro x hx
    -- `hx : (u + H − V) · m = 0` ⇒ `m · (u + H − V) = 0` by commutativity.
    change sol.m x * (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x)
        = (0 : ℝ)
    have hcomm : sol.m x *
            (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x)
          = (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x) * sol.m x :=
      mul_comm _ _
    rw [hcomm, hx]
  -- Convert `∫ x in UnitCube d, _ ∂volume` into `∫ x, _ ∂(volume.restrict _)`
  -- so we can apply `MeasureTheory.integral_eq_zero_of_ae`.
  have h_eq_restrict :
      (∫ x in UnitCube d,
          sol.m x * (sol.u x +
              H x (fun i => sol.Du i x) (sol.m x) - V x)
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        = ∫ x,
            sol.m x * (sol.u x +
                H x (fun i => sol.Du i x) (sol.m x) - V x)
              ∂((volume : MeasureTheory.Measure (Fin d → ℝ)).restrict
                  (UnitCube d)) := rfl
  rw [h_eq_restrict]
  exact MeasureTheory.integral_eq_zero_of_ae hae

/-! ### Sanity-check `example` for the headline lemma -/

example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hRhoMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
      ∀ n : ℕ,
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)))
    (hSigmaMIndicMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    (hCont_signed :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (fun x => σ * sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)))))
    (hResM :
      MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
            * sol.m x)
        (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d,
        sol.m x * (sol.u x +
            H x (fun i => sol.Du i x) (sol.m x) - V x)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
      = 0 :=
  hjb_integrated_zero_of_RegularizedBareSolution sol hRhoMemLp
    hSigmaMIndicMemLp hCont_signed hResM

/-! ## Phase 1 v3 — line-1212 transport identity producer

Per `infra-P5-theorem1-closed-phase1-hVIeps-transport-symmetric-equality-at-uEpsi`,
this section assembles the paper line-1212 raw transport identity
```
∫ u_ε = ∫ (m·(−H + DpH·Du) + V·m + ε·(|Du|^γ̄ + |u|^γ̄))
```
from two ingredients (paper lines 1205–1216):

1. The HJ0 integrated identity
   `∫ m·(u + H − V) = 0` (from
   `hjb_integrated_zero_of_RegularizedBareSolution`, this module).
2. The strong-transport identity at `varphi = u_ε`
   `0 = ∫ (−u_ε + m·(DpH·Du − H) + V·m + ε·(|Du|^γ̄ + |u|^γ̄))`
   (paper `eq:strong-transport`, the equality obtained from the σ→0
   Minty-style derivation of the symmetric ±σ form of
   `sol.hVIeps_transport`).

The second ingredient is the genuine analytic content (it hides the
σ→0 limit and the W^{1,γ̄}-tester extension). It is filed as a
follow-up backlog child
`infra-P5-strongTransport-at-uEpsi-from-hVIeps-transport`. The
producer here assembles the line-1212 identity from both ingredients
by additive cancellation: the `m·(u + H − V)` block of the strong-
transport identity (when expanded as `m·DpH·Du − m·H + V·m + …`)
collapses against HJ0 to leave exactly the line-1212 RHS.

Per CONVENTIONS §1b: the strong-transport ingredient is taken as an
authorised input, mirroring iter 433's pattern of taking `hCont_signed`
as authorised in `hjb_integrated_zero_of_RegularizedBareSolution`. -/

/-- **Headline lemma — paper line-1212 transport identity from a
`RegularizedBareSolution`.**

Conclusion (matches `RegularizedPaperSolutionData.hTransport_identity`
and the `hIdentityRaw` shape consumed by
`AprioriUniformPerSolHypothesesC.bClass_h_identity` at
`epsTerms x = ε·|Du|^{γ̄/2 squared} + ε·u^γ̄`):
```
∫ u_ε = ∫ (m·(−H + DpH·Du) + V·m + ε·|Du|^γ̄ + ε·u^γ̄).
```

Inputs:
* `sol : RegularizedBareSolution`.
* `hHJ0_eq` — the HJ0 integrated identity (sourced from
  `hjb_integrated_zero_of_RegularizedBareSolution`).
* `hStrongTransportAtUepsi` — the integrated equality
  `eq:strong-transport` evaluated at `varphi = u_ε` (paper line 1185
  + line 1205 substitution; sourced from the follow-up child task
  `infra-P5-strongTransport-at-uEpsi-from-hVIeps-transport`).

Proof: subtract `hHJ0_eq` from `hStrongTransportAtUepsi` and rearrange
to isolate `∫ u_ε`. The two `∫ m·u + m·H − m·V` blocks cancel
verbatim. -/
theorem hIdentityRaw_of_hVIeps_transport
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    -- HJ0 integrated identity (iter-433 producer output)
    (hHJ0_eq :
      ∫ x in UnitCube d,
          sol.m x * (sol.u x +
              H x (fun i => sol.Du i x) (sol.m x) - V x)
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        = 0)
    -- Strong-transport identity at `varphi = u_ε`
    -- (paper `eq:strong-transport` substituted at `φ = u_ε`).
    --
    -- Per `mfgOperatorEpsPair_pairing_eq` at the differential test
    -- triple `(η, ν, Dν) = (0, u_ε, Du_ε)` against the strong-VI
    -- equation: the pairing collapses to
    -- ```
    -- 0 = ∫ (m · DpH·Du + (m − 1)·u
    --        + ε · (|Du|^γ̄ + |u|^γ̄)).
    -- ```
    -- This is the σ→0 limit of `±σ`-perturbations of
    -- `sol.hVIeps_transport` (paper line 1185). Authorised input per
    -- CONVENTIONS §1b; sourced from the follow-up backlog child
    -- `infra-P5-strongTransport-at-uEpsi-from-hVIeps-transport`.
    (hStrongTransportAtUepsi :
      (0 : ℝ) =
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    -- Pointwise integrability bundle (so that
    -- `MeasureTheory.integral_add` / `_sub` apply at the integrand
    -- level).
    (hu_int : MeasureTheory.Integrable sol.u
              (volume.restrict (UnitCube d)))
    (hMUH_int : MeasureTheory.Integrable
              (fun x => sol.m x *
                (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
              (volume.restrict (UnitCube d)))
    (hRHS_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                          ^ (γBarReal / 2)
                  + ε * |sol.u x| ^ γBarReal)
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, sol.u x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Shorthands for the three integrands. We will show that
  -- `S - H₀ = -f + g` pointwise, where:
  --  * S = strong-transport integrand = m·DpH·Du + (m−1)·u + ε·(...)
  --  * H₀ = HJ0 integrand = m·(u + H − V)
  --  * f = u, g = m·(−H + DpH·Du) + V·m + ε·(...).
  -- Then `0 = ∫S` and `0 = ∫H₀` give `0 = ∫(S − H₀) = ∫(-f + g)`,
  -- i.e. `∫f = ∫g`.
  set f : (Fin d → ℝ) → ℝ := fun x => sol.u x with hf_def
  set g : (Fin d → ℝ) → ℝ :=
    fun x =>
      sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                + (DpH x (fun i => sol.Du i x) (sol.m x))
                    ⬝ (fun i => sol.Du i x))
        + V x * sol.m x
        + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (γBarReal / 2)
        + ε * |sol.u x| ^ γBarReal with hg_def
  set h₀ : (Fin d → ℝ) → ℝ :=
    fun x => sol.m x *
      (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x)
    with hh₀_def
  set sT : (Fin d → ℝ) → ℝ :=
    fun x =>
      sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                  ⬝ (fun i => sol.Du i x))
        + (sol.m x - 1) * sol.u x
        + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (γBarReal / 2)
        + ε * |sol.u x| ^ γBarReal with hsT_def
  -- Step 1: `S − H₀ = -f + g` pointwise. The DpH⬝Du and ε-residue
  -- terms appear identically on both sides; the H/V/u terms collapse
  -- via `m·DpH·Du + (m−1)·u − m·(u+H−V) = m·DpH·Du − u − m·H + V·m`.
  have hPt : ∀ x, sT x - h₀ x = -f x + g x := by
    intro x
    simp only [hsT_def, hh₀_def, hf_def, hg_def]
    ring
  -- Step 2: integrate the pointwise identity. We rewrite both sides
  -- using `MeasureTheory.integral_sub` / `_add` / `_neg`.
  have hf_int' : MeasureTheory.Integrable f
                    (volume.restrict (UnitCube d)) := hu_int
  have hg_int' : MeasureTheory.Integrable g
                    (volume.restrict (UnitCube d)) := hRHS_int
  have hh₀_int' : MeasureTheory.Integrable h₀
                    (volume.restrict (UnitCube d)) := hMUH_int
  -- `S` is integrable: it equals `(-f + g) + h₀` pointwise (from
  -- `hPt`, rearranged: `S = h₀ + (-f + g)`).
  have hSEq : ∀ x, sT x = h₀ x + (-f x + g x) := by
    intro x; have := hPt x; linarith
  have hsT_int : MeasureTheory.Integrable sT
                    (volume.restrict (UnitCube d)) := by
    have hSum : MeasureTheory.Integrable (fun x => h₀ x + (-f x + g x))
                    (volume.restrict (UnitCube d)) :=
      hh₀_int'.add (hf_int'.neg.add hg_int')
    refine hSum.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact (hSEq x).symm
  -- Replace the displayed strong-transport hypothesis by `0 = ∫ sT`.
  have hSTeq : (0 : ℝ) =
      ∫ x in UnitCube d, sT x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    simp only [hsT_def]
    exact hStrongTransportAtUepsi
  -- `∫ sT − ∫ h₀ = ∫ (sT − h₀) = ∫ (-f + g) = -∫f + ∫g`.
  have hSubInt :
      (∫ x in UnitCube d, sT x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) -
      (∫ x in UnitCube d, h₀ x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) =
      ∫ x in UnitCube d, (sT x - h₀ x)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
    (MeasureTheory.integral_sub hsT_int hh₀_int').symm
  have hSubAe :
      ∫ x in UnitCube d, (sT x - h₀ x)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, (-f x + g x)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact hPt x
  have hAddInt :
      (∫ x in UnitCube d, (-f x + g x)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) =
      (∫ x in UnitCube d, -f x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) +
      (∫ x in UnitCube d, g x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) :=
    MeasureTheory.integral_add hf_int'.neg hg_int'
  have hNegF :
      ∫ x in UnitCube d, -f x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) =
        -(∫ x in UnitCube d, f x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) :=
    MeasureTheory.integral_neg _
  -- Combine: `0 = ∫sT`, `0 = ∫h₀`, so `0 = ∫sT − ∫h₀ = -∫f + ∫g`.
  have hH0F : ∫ x in UnitCube d, h₀ x
                ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) = 0 := by
    simp only [hh₀_def]; exact hHJ0_eq
  have hCombined :
      (0 : ℝ) =
      -(∫ x in UnitCube d, f x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) +
      (∫ x in UnitCube d, g x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) := by
    have hZeroSub :
        (0 : ℝ) -
        (∫ x in UnitCube d, h₀ x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) =
        ∫ x in UnitCube d, (-f x + g x)
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
      conv_lhs => rw [hSTeq]
      rw [hSubInt, hSubAe]
    rw [hH0F, sub_zero] at hZeroSub
    rw [hZeroSub, hAddInt, hNegF]
  -- `0 = -∫f + ∫g`, i.e., `∫f = ∫g`.
  have hFG :
      (∫ x in UnitCube d, f x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) =
      (∫ x in UnitCube d, g x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) := by
    linarith
  exact hFG

/-! ### Sanity-check `example` for the headline lemma -/

example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hHJ0_eq :
      ∫ x in UnitCube d,
          sol.m x * (sol.u x +
              H x (fun i => sol.Du i x) (sol.m x) - V x)
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        = 0)
    (hStrongTransportAtUepsi :
      (0 : ℝ) =
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hu_int : MeasureTheory.Integrable sol.u
              (volume.restrict (UnitCube d)))
    (hMUH_int : MeasureTheory.Integrable
              (fun x => sol.m x *
                (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
              (volume.restrict (UnitCube d)))
    (hRHS_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                          ^ (γBarReal / 2)
                  + ε * |sol.u x| ^ γBarReal)
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, sol.u x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  hIdentityRaw_of_hVIeps_transport sol hHJ0_eq hStrongTransportAtUepsi
    hu_int hMUH_int hRHS_int

/-! ## Phase 1 v3 — strong-transport identity at `varphi = u_ε`

Per `infra-P5-strongTransport-at-uEpsi-from-hVIeps-transport`, this
section produces the integrated equality

```
0 = ∫ (m·DpH·Du + (m−1)·u + ε·|Du|^γ̄ + ε·u^γ̄)
```

(the `hStrongTransportAtUepsi` input of
`hIdentityRaw_of_hVIeps_transport`) directly from
`RegularizedBareSolution.hVIeps_transport`.

### Strategy (paper line 1185)

The paper's argument tests `eq:Aepsi.strong-ineq` against
`(μ, υ) = (m, u ± φ)` for `φ ∈ W^{1,γ̄}(𝕋^d)`. The two `≥ 0` and
`≤ 0` inequalities pin the equality
`0 = ⟨A_ε[m,u], (0, φ, Dφ)⟩` for every such `φ`. Specialising
`φ = u_ε` yields, after `mfgOperatorEpsPair_pairing_eq`, the
displayed integrand.

### Decomposition into authorised inputs

The *upper bound* `+1`-direction integrated VI

```
0 ≤ ∫ (m·DpH·Du + (m−1)·u + ε·|Du|^γ̄ + ε·u^γ̄)
```

and the matching `−1`-direction `≥ 0` of the negated integrand are
sourced as **authorised inputs** per CONVENTIONS §1b/§8. Their
discharge from `sol.hVIeps_transport` requires:

1. **W^{1,γ̄}-extension of the smooth-tester transport VI**
   (`strongVI_transport_at_eps`, line 19969 of this file accepts
   only smooth `φ`). Filed as
   `infra-P5-theorem1-closed-phase1-hVIeps-transport-extend-to-MemSobolevPer-tester`.
2. **σ → 0 Minty bridge** combined with the closed-form pairing
   identity `mfgOperatorEpsPair_pairing_eq` (the σ-perturbation
   terms cancel to leading order, leaving the displayed integrand).

Each step is multi-week analytic content; bundling the two scalar
inequalities here mirrors the precedent of
`hjb_integrated_zero_of_RegularizedBareSolution` (iter 433), whose
`hCont_signed` input encodes the analogous σ → 0 bridge for the
HJ0 identity.

### Headline

`strongTransport_at_uEpsi_of_hVIeps_transport` combines the two
authorised inequalities via `le_antisymm` to produce the `0 = ∫ …`
target equality in the exact shape consumed by
`hIdentityRaw_of_hVIeps_transport`. -/

/-- **Headline lemma — strong-transport identity at `varphi = u_ε`.**

Conclusion (matches the `hStrongTransportAtUepsi` input of
`hIdentityRaw_of_hVIeps_transport`, line 24804+ above):
```
0 = ∫ (m·DpH·Du + (m−1)·u + ε·|Du|^γ̄ + ε·u^γ̄).
```

Inputs:

* `sol : RegularizedBareSolution`.
* `hVI_pos` — the `+1`-direction integrated VI
  `0 ≤ ∫ I` evaluated at the strong-transport integrand `I`. Sourced
  from `strongVI_transport_at_eps` extended to `W^{1,γ̄}` testers
  (filed as
  `infra-P5-theorem1-closed-phase1-hVIeps-transport-extend-to-MemSobolevPer-tester`)
  applied at `φ = u_ε, σ = +1`, then expanded via
  `mfgOperatorEpsPair_pairing_eq` and σ → 0.
* `hVI_neg` — the `−1`-direction integrated VI `0 ≤ ∫ (-I)`,
  i.e. `∫ I ≤ 0`. Sourced from the same machinery at `σ = −1`.

Proof: `0 ≤ ∫ I` and `∫ I ≤ 0` together force `∫ I = 0`. -/
theorem strongTransport_at_uEpsi_of_hVIeps_transport
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    -- `+1`-direction VI: `0 ≤ ∫ (strong-transport integrand)`.
    -- Authorised input per CONVENTIONS §1b (paper line 1185 with
    -- `φ = u_ε, σ = +1`); discharge via the W^{1,γ̄} extension of
    -- `strongVI_transport_at_eps` filed as
    -- `infra-P5-theorem1-closed-phase1-hVIeps-transport-extend-to-MemSobolevPer-tester`,
    -- combined with `mfgOperatorEpsPair_pairing_eq` and σ → 0.
    (hVI_pos :
      (0 : ℝ) ≤
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    -- `−1`-direction VI: `∫ (strong-transport integrand) ≤ 0`.
    -- Authorised input (paper line 1185 with `φ = u_ε, σ = −1`);
    -- discharge as for `hVI_pos`.
    (hVI_neg :
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ (0 : ℝ)) :
    (0 : ℝ) =
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  le_antisymm hVI_pos hVI_neg

/-! ### Sanity-check `example`s for the headline lemma

The first `example` pins the type-shape of
`strongTransport_at_uEpsi_of_hVIeps_transport`. The second composes
this lemma with `hIdentityRaw_of_hVIeps_transport` (above) to verify
that together they produce the line-1212 transport identity. -/

example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hVI_pos :
      (0 : ℝ) ≤
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hVI_neg :
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ (0 : ℝ)) :
    (0 : ℝ) =
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  strongTransport_at_uEpsi_of_hVIeps_transport sol hVI_pos hVI_neg

/-- Composed sanity check: feeding
`strongTransport_at_uEpsi_of_hVIeps_transport` (this section) and
`hjb_integrated_zero_of_RegularizedBareSolution` (above) into
`hIdentityRaw_of_hVIeps_transport` reproduces the line-1212 identity
shape. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hHJ0_eq :
      ∫ x in UnitCube d,
          sol.m x * (sol.u x +
              H x (fun i => sol.Du i x) (sol.m x) - V x)
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        = 0)
    (hVI_pos :
      (0 : ℝ) ≤
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hVI_neg :
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (γBarReal / 2)
            + ε * |sol.u x| ^ γBarReal)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ (0 : ℝ))
    (hu_int : MeasureTheory.Integrable sol.u
              (volume.restrict (UnitCube d)))
    (hMUH_int : MeasureTheory.Integrable
              (fun x => sol.m x *
                (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
              (volume.restrict (UnitCube d)))
    (hRHS_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                          ^ (γBarReal / 2)
                  + ε * |sol.u x| ^ γBarReal)
              (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, sol.u x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  hIdentityRaw_of_hVIeps_transport sol hHJ0_eq
    (strongTransport_at_uEpsi_of_hVIeps_transport sol hVI_pos hVI_neg)
    hu_int hMUH_int hRHS_int

/-! ## Phase 1 v3 — `RegularizedPaperSolutionData.of_regularizedBareSolution`

Constructor assembling the four fields of `RegularizedPaperSolutionData`
from a `RegularizedBareSolution` plus the authorised B-class inputs
required by the three already-proved producer lemmas above:

* `hHJ0` ← `hjb_integrated_zero_of_RegularizedBareSolution`
  (HJ0 orthogonality, iter 433);
* `hTransport_identity` ← `hIdentityRaw_of_hVIeps_transport` composed
  with `strongTransport_at_uEpsi_of_hVIeps_transport`
  (paper line-1212 transport identity, iter 436);
* `h_lagr` ← `hpow.lagr` (paper §3 Legendre/convex-at-zero lower bound,
  one-line projection).

This is **pure assembly** — no new mathematics. The structure
`RegularizedPaperSolutionData` is defined in `AssemblyContext.lean`,
which `RegularizedSequence.lean` imports. The producer lemmas are
defined locally above. The structure cannot itself import
`RegularizedSequence` (cyclic), so this constructor must live here. -/

/-- Assemble a `RegularizedPaperSolutionData` from a
`RegularizedBareSolution` together with the authorised B-class inputs
required by the three producer lemmas. The `γBarReal` and `βBarReal`
parameters of `RegularizedPaperSolutionData` are specialised to
`gammaBar hpow.α hpow.β` and `hpow.β + 1` respectively, matching the
paper-side regularised system. -/
noncomputable def RegularizedPaperSolutionData.of_regularizedBareSolution
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    -- Authorised B-class inputs for `hjb_integrated_zero_of_RegularizedBareSolution`
    (hRhoMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
      ∀ n : ℕ,
        MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)))
    (hSigmaMIndicMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    (hCont_signed :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (gammaBar hpow.α hpow.β) ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                (gammaBar hpow.α hpow.β) ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (fun x => σ * sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)))))
    (hResM :
      MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
            * sol.m x)
        (volume.restrict (UnitCube d)))
    -- Authorised B-class inputs for `strongTransport_at_uEpsi_of_hVIeps_transport`
    (hVI_pos :
      (0 : ℝ) ≤
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (gammaBar hpow.α hpow.β / 2)
            + ε * |sol.u x| ^ gammaBar hpow.α hpow.β)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hVI_neg :
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (gammaBar hpow.α hpow.β / 2)
            + ε * |sol.u x| ^ gammaBar hpow.α hpow.β)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ (0 : ℝ))
    -- Authorised B-class integrability inputs for `hIdentityRaw_of_hVIeps_transport`
    (hu_int : MeasureTheory.Integrable sol.u
              (volume.restrict (UnitCube d)))
    (hMUH_int : MeasureTheory.Integrable
              (fun x => sol.m x *
                (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
              (volume.restrict (UnitCube d)))
    (hRHS_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                          ^ (gammaBar hpow.α hpow.β / 2)
                  + ε * |sol.u x| ^ gammaBar hpow.α hpow.β)
              (volume.restrict (UnitCube d))) :
    RegularizedPaperSolutionData (d := d) ε V H DpH
      (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal' hpow :=
  { sol := sol
    hHJ0 :=
      hjb_integrated_zero_of_RegularizedBareSolution sol
        hRhoMemLp hSigmaMIndicMemLp hCont_signed hResM
    hTransport_identity :=
      hIdentityRaw_of_hVIeps_transport sol
        (hjb_integrated_zero_of_RegularizedBareSolution sol
           hRhoMemLp hSigmaMIndicMemLp hCont_signed hResM)
        (strongTransport_at_uEpsi_of_hVIeps_transport sol hVI_pos hVI_neg)
        hu_int hMUH_int hRHS_int
    h_lagr := hpow.lagr }

/-! ### Sanity-check `example` for `of_regularizedBareSolution` -/

example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal' γBarReal' : ℝ}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))]
    (sol : RegularizedBareSolution d ε V H DpH
              (gammaBar hpow.α hpow.β) (hpow.β + 1) βBarReal' γBarReal')
    (hRhoMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
      ∀ n : ℕ,
        MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)))
    (hSigmaMIndicMemLp :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    (hCont_signed :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (gammaBar hpow.α hpow.β) ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                          (sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                (gammaBar hpow.α hpow.β) ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (fun x => σ * sol.m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)))))
    (hResM :
      MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
            * sol.m x)
        (volume.restrict (UnitCube d)))
    (hVI_pos :
      (0 : ℝ) ≤
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (gammaBar hpow.α hpow.β / 2)
            + ε * |sol.u x| ^ gammaBar hpow.α hpow.β)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hVI_neg :
      ∫ x in UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (gammaBar hpow.α hpow.β / 2)
            + ε * |sol.u x| ^ gammaBar hpow.α hpow.β)
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ (0 : ℝ))
    (hu_int : MeasureTheory.Integrable sol.u
              (volume.restrict (UnitCube d)))
    (hMUH_int : MeasureTheory.Integrable
              (fun x => sol.m x *
                (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
              (volume.restrict (UnitCube d)))
    (hRHS_int : MeasureTheory.Integrable
              (fun x =>
                sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                          + (DpH x (fun i => sol.Du i x) (sol.m x))
                              ⬝ (fun i => sol.Du i x))
                  + V x * sol.m x
                  + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                          ^ (gammaBar hpow.α hpow.β / 2)
                  + ε * |sol.u x| ^ gammaBar hpow.α hpow.β)
              (volume.restrict (UnitCube d))) :
    (RegularizedPaperSolutionData.of_regularizedBareSolution
        (hpow := hpow) sol
        hRhoMemLp hSigmaMIndicMemLp hCont_signed hResM
        hVI_pos hVI_neg hu_int hMUH_int hRHS_int).sol = sol := rfl

/-! ## Phase 5 — σ → 0 Minty bridge for the transport family

Per task `infra-P5-strongTransport-uepsi-sigma-to-zero-Minty` (paper
line 1185 → 1212): take the **perturbed-primal** strong-transport VI
from `strongTransport_at_uEpsi_perturbed` (above), where the
σ-perturbation slot lives in the value-function/gradient
`((1+s)·Du, m, (1+s)·u)`, and pass `s = σ/(n+1) → 0` to recover the
**unperturbed-primal** target inequalities `hVI_pos` / `hVI_neg`
consumed by `strongTransport_at_uEpsi_of_hVIeps_transport`.

### Strategy

Mirrors `strongVI_setForm_signed_of_hVIeps_set` (iter 433), the σ → 0
Minty bridge for the **density** family. Differences:

- The σ-perturbation here is in the **gradient/value** slot, not the
  density slot. The perturbation parameter `s_n := σ/(n+1)` is signed.
- The H/DpH terms are **nonlinear in `p`**, so naive ±σ addition does
  not cancel by parity; cancellation is delivered only after dividing
  by `s_n` and taking `n → ∞`.
- The perturbed integrand `Iperturb_n` is *first-order* in `s_n` —
  every term carries an `s_n` factor (from the test-triple slot
  `(s·Du, 0, s·u)`). Dividing by `s_n` (positive for σ=+1, negative
  for σ=−1) gives a sequence converging pointwise (under H/DpH
  continuity) to the bare integrand `I∞`.

### Authorised inputs (per CONVENTIONS §1b/§8)

The pointwise `→` follows from `H, DpH, |·|^{γ̄−2}` continuity and
dominated convergence with an L¹ dominator uniform in `s ∈ [-1,1]`.
Both ingredients are routine but verbose; per CONVENTIONS §1b/§8 we
take the **integral-level** Tendsto convergence as authorised input,
named `hCont_pos` / `hCont_neg`. Discharge of these inputs from
`HypothesisH.continuous` / `HypothesisDpH.continuous` and `MemLpPer`
dominators is filed as a follow-up child task.

### Headline

`strongTransport_at_uEpsi_hVI_pos_of_perturbed`
and `strongTransport_at_uEpsi_hVI_neg_of_perturbed` produce
respectively the `hVI_pos` and `hVI_neg` inputs of
`strongTransport_at_uEpsi_of_hVIeps_transport` from the perturbed
VI plus the authorised σ → 0 Tendsto inputs. -/

/-- The unperturbed-primal **target integrand** (in `hVI_pos` /
`hVI_neg` shape):
`m · (DpH(x, Du, m) ⬝ Du) + (m − 1) · u + ε · (Du⬝Du)^(γ̄/2)
   + ε · u^γ̄`. -/
@[inline] def strongTransportTargetIntegrand
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (x : Fin d → ℝ) : ℝ :=
  sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                ⬝ (fun i => sol.Du i x))
    + (sol.m x - 1) * sol.u x
    + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
            ^ (γBarReal / 2)
    + ε * |sol.u x| ^ γBarReal

/-- The perturbed-primal **transport integrand** at signed scaling
`s : ℝ`, matching the conclusion of
`strongTransport_at_uEpsi_perturbed`. -/
@[inline] def strongTransportPerturbedIntegrand
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                ⬝ (fun i => s * sol.Du i x))
    + (sol.m x - 1) * (s * sol.u x)
    + ε * (vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
              * ((fun i => sol.Du i x + s * sol.Du i x)
                 ⬝ (fun i => s * sol.Du i x))
            + absPowMinusTwo γBarReal
                (sol.u x + s * sol.u x)
              * ((sol.u x + s * sol.u x)
                 * (s * sol.u x)))

/-- **AE-measurability of the perturbed transport integrand.**

For any `s : ℝ`, the integrand
`x ↦ strongTransportPerturbedIntegrand sol s x` is `AEMeasurable` on
the unit cube, given joint measurability of `DpH` (from `RegularityH`).

The argument splits the integrand into its three additive components.
Each `sol.m`, `sol.u`, `sol.Du i` carries `AEStronglyMeasurable` via
`MemLpPer.aestronglyMeasurable`, which on `ℝ` gives `AEMeasurable`.
The `DpH` slice is handled by composing the joint `Measurable`
hypothesis with the `AEMeasurable` tuple
`x ↦ (x, sol.Du x + s · sol.Du x, sol.m x)` via
`Measurable.comp_aemeasurable`. The `vecAbsPowMinusTwo` /
`absPowMinusTwo` factors reduce to `(_)^(c)` for a constant exponent,
handled by `AEMeasurable.pow_const`. -/
lemma strongTransportPerturbedIntegrand_aemeasurable
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        DpH xpm.1 xpm.2.1 xpm.2.2))
    (s : ℝ) :
    AEMeasurable
      (fun x => strongTransportPerturbedIntegrand sol s x)
      (volume.restrict (UnitCube d)) := by
  -- AE-strong measurability of the basic slots.
  have hm_asm : AEStronglyMeasurable sol.m (volume.restrict (UnitCube d)) :=
    sol.hmLp.aestronglyMeasurable
  have hu_asm : AEStronglyMeasurable sol.u (volume.restrict (UnitCube d)) :=
    sol.huLp.aestronglyMeasurable
  have hDu_asm : ∀ i, AEStronglyMeasurable (sol.Du i)
      (volume.restrict (UnitCube d)) :=
    fun i => (sol.hDuLp i).aestronglyMeasurable
  -- Convert to AEMeasurable on ℝ-valued slots.
  have hm_am : AEMeasurable sol.m (volume.restrict (UnitCube d)) :=
    hm_asm.aemeasurable
  have hu_am : AEMeasurable sol.u (volume.restrict (UnitCube d)) :=
    hu_asm.aemeasurable
  have hDu_am : ∀ i, AEMeasurable (sol.Du i) (volume.restrict (UnitCube d)) :=
    fun i => (hDu_asm i).aemeasurable
  -- The shifted gradient `fun x => sol.Du i x + s * sol.Du i x` is AEMeasurable.
  have hDuShift_am : ∀ i,
      AEMeasurable (fun x => sol.Du i x + s * sol.Du i x)
        (volume.restrict (UnitCube d)) :=
    fun i => (hDu_am i).add ((hDu_am i).const_mul s)
  -- The full pi-valued shifted gradient is AEMeasurable into `Fin d → ℝ`.
  have hDuShift_pi : AEMeasurable
      (fun x => (fun i : Fin d => sol.Du i x + s * sol.Du i x))
      (volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr hDuShift_am
  -- The s-scaled gradient `fun x => s * sol.Du i x` is AEMeasurable.
  have hsDu_am : ∀ i,
      AEMeasurable (fun x => s * sol.Du i x)
        (volume.restrict (UnitCube d)) :=
    fun i => (hDu_am i).const_mul s
  -- The tuple `x ↦ (x, (Du+s·Du)(x), m x)` is AEMeasurable.
  have hxpm_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => sol.Du i x + s * sol.Du i x), sol.m x))
      (volume.restrict (UnitCube d)) :=
    aemeasurable_id'.prodMk (hDuShift_pi.prodMk hm_am)
  -- The DpH composition is AEMeasurable into `Fin d → ℝ`.
  have hDpHcomp_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x))
      (volume.restrict (UnitCube d)) :=
    hDpH_meas.comp_aemeasurable hxpm_am
  -- Per-coordinate AEMeasurability of the DpH composition.
  have hDpHcomp_i_am : ∀ i, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x) i)
      (volume.restrict (UnitCube d)) :=
    fun i => (measurable_pi_apply i).comp_aemeasurable hDpHcomp_am
  -- The dot product term `DpH(...) ⬝ (s · Du)`.
  have hdot_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
          ⬝ (fun i => s * sol.Du i x))
      (volume.restrict (UnitCube d)) := by
    -- Unfold `⬝` to a finite sum coordinatewise.
    have h_eq :
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
            ⬝ (fun i => s * sol.Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x) i
                  * (s * sol.Du i x)) := by
      funext x
      rfl
    rw [h_eq]
    refine Finset.aemeasurable_fun_sum _ (fun i _ => ?_)
    exact (hDpHcomp_i_am i).mul (hsDu_am i)
  -- First additive term: `sol.m * (DpH(...) ⬝ (s · Du))`.
  have hT1_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                      ⬝ (fun i => s * sol.Du i x)))
      (volume.restrict (UnitCube d)) :=
    hm_am.mul hdot_am
  -- Second additive term: `(sol.m - 1) * (s * sol.u)`.
  have hT2_am : AEMeasurable
      (fun x : (Fin d → ℝ) => (sol.m x - 1) * (s * sol.u x))
      (volume.restrict (UnitCube d)) :=
    (hm_am.sub_const _).mul (hu_am.const_mul s)
  -- Third additive term: `ε * (...)`.
  -- The `vecAbsPowMinusTwo γBarReal v = (v ⬝ v) ^ ((γBarReal - 2)/2)`.
  -- Use `Real.measurable_rpow_const` for the rpow part.
  -- First: `(Du+s·Du) ⬝ (Du+s·Du)` is AEMeasurable.
  have hDot_self_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i => sol.Du i x + s * sol.Du i x)
          ⬝ (fun i => sol.Du i x + s * sol.Du i x))
      (volume.restrict (UnitCube d)) := by
    have h_eq :
        (fun x : (Fin d → ℝ) =>
          (fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => sol.Du i x + s * sol.Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                (sol.Du i x + s * sol.Du i x)
                  * (sol.Du i x + s * sol.Du i x)) := by
      funext x
      rfl
    rw [h_eq]
    refine Finset.aemeasurable_fun_sum _ (fun i _ => ?_)
    exact (hDuShift_am i).mul (hDuShift_am i)
  -- `vecAbsPowMinusTwo γBarReal (Du+s·Du)` = `(... ⬝ ...) ^ ((γBarReal-2)/2)`.
  have hVec_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBarReal
          (fun i => sol.Du i x + s * sol.Du i x))
      (volume.restrict (UnitCube d)) := by
    change AEMeasurable
      (fun x : (Fin d → ℝ) =>
        ((fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => sol.Du i x + s * sol.Du i x))
          ^ ((γBarReal - 2) / 2))
      _
    exact hDot_self_am.pow_const _
  -- `(Du+s·Du) ⬝ (s·Du)` is AEMeasurable.
  have hDot_mix_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i => sol.Du i x + s * sol.Du i x)
          ⬝ (fun i => s * sol.Du i x))
      (volume.restrict (UnitCube d)) := by
    have h_eq :
        (fun x : (Fin d → ℝ) =>
          (fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => s * sol.Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                (sol.Du i x + s * sol.Du i x) * (s * sol.Du i x)) := by
      funext x
      rfl
    rw [h_eq]
    refine Finset.aemeasurable_fun_sum _ (fun i _ => ?_)
    exact (hDuShift_am i).mul (hsDu_am i)
  -- `vecAbsPowMinusTwo (Du+s·Du) * ((Du+s·Du) ⬝ (s·Du))`.
  have hVecMul_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBarReal
          (fun i => sol.Du i x + s * sol.Du i x)
          * ((fun i => sol.Du i x + s * sol.Du i x)
              ⬝ (fun i => s * sol.Du i x)))
      (volume.restrict (UnitCube d)) :=
    hVec_am.mul hDot_mix_am
  -- `absPowMinusTwo γBarReal (sol.u + s · sol.u)` = `|sol.u + s·sol.u| ^ (γBarReal - 2)`.
  have huShift_am : AEMeasurable
      (fun x => sol.u x + s * sol.u x) (volume.restrict (UnitCube d)) :=
    hu_am.add (hu_am.const_mul s)
  have huShift_abs_am : AEMeasurable
      (fun x => |sol.u x + s * sol.u x|) (volume.restrict (UnitCube d)) :=
    measurable_id.abs.comp_aemeasurable huShift_am
  have hAbsPow_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        absPowMinusTwo γBarReal (sol.u x + s * sol.u x))
      (volume.restrict (UnitCube d)) := by
    change AEMeasurable
      (fun x : (Fin d → ℝ) =>
        |sol.u x + s * sol.u x| ^ (γBarReal - 2))
      _
    exact huShift_abs_am.pow_const _
  -- `(sol.u + s · sol.u) * (s * sol.u)`.
  have hUmul_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (sol.u x + s * sol.u x) * (s * sol.u x))
      (volume.restrict (UnitCube d)) :=
    huShift_am.mul (hu_am.const_mul s)
  -- `absPowMinusTwo γBarReal (sol.u + s · sol.u) * ((sol.u + s · sol.u) * (s · sol.u))`.
  have hAbsMul_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
          * ((sol.u x + s * sol.u x) * (s * sol.u x)))
      (volume.restrict (UnitCube d)) :=
    hAbsPow_am.mul hUmul_am
  -- Combine the bracket factor.
  have hBracket_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBarReal
          (fun i => sol.Du i x + s * sol.Du i x)
          * ((fun i => sol.Du i x + s * sol.Du i x)
              ⬝ (fun i => s * sol.Du i x))
        + absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
          * ((sol.u x + s * sol.u x) * (s * sol.u x)))
      (volume.restrict (UnitCube d)) :=
    hVecMul_am.add hAbsMul_am
  -- Multiply by `ε` (constant).
  have hT3_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        ε * (vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
              * ((fun i => sol.Du i x + s * sol.Du i x)
                  ⬝ (fun i => s * sol.Du i x))
            + absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
              * ((sol.u x + s * sol.u x) * (s * sol.u x))))
      (volume.restrict (UnitCube d)) :=
    hBracket_am.const_mul ε
  -- Sum all three terms.
  unfold strongTransportPerturbedIntegrand
  exact (hT1_am.add hT2_am).add hT3_am

/-- **AE-strong measurability of the perturbed transport integrand.** -/
lemma strongTransportPerturbedIntegrand_aestronglyMeasurable
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        DpH xpm.1 xpm.2.1 xpm.2.2))
    (s : ℝ) :
    AEStronglyMeasurable
      (fun x => strongTransportPerturbedIntegrand sol s x)
      (volume.restrict (UnitCube d)) :=
  (strongTransportPerturbedIntegrand_aemeasurable
    (sol := sol) hDpH_meas s).aestronglyMeasurable

/-- **AE-strong measurability of the rescaled perturbed transport integrand.**
Direct corollary of `strongTransportPerturbedIntegrand_aemeasurable`:
dividing by a constant scalar preserves `AEMeasurable`, hence
`AEStronglyMeasurable` on `ℝ`. -/
lemma strongTransportPerturbedIntegrand_div_aestronglyMeasurable
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        DpH xpm.1 xpm.2.1 xpm.2.2))
    (s : ℝ) :
    AEStronglyMeasurable
      (fun x => strongTransportPerturbedIntegrand sol s x / s)
      (volume.restrict (UnitCube d)) :=
  ((strongTransportPerturbedIntegrand_aemeasurable
    (sol := sol) hDpH_meas s).div_const s).aestronglyMeasurable

/-- **Phase-5 σ → 0 Minty bridge — `+1` direction.**

Produces the unperturbed `hVI_pos` input of
`strongTransport_at_uEpsi_of_hVIeps_transport` from:

* `hStep_pos n` — the per-`n` perturbed-primal VI at `s := 1/(n+1) > 0`,
  exactly the conclusion of
  `strongTransport_at_uEpsi_perturbed sol hp_ge_one (1/(n+1)) hI_A_n hI_B_n`.
* `hCont_pos` — the authorised σ → 0 Tendsto convergence of the
  rescaled perturbed integral `((n+1)) · ∫ Iperturb_n` to the target
  integral `∫ I∞`. (The factor `((n+1)) = (1/(n+1))⁻¹` is the
  reciprocal of the test-slot scaling `s = 1/(n+1)`.)

Conclusion: `0 ≤ ∫ I∞`, the `hVI_pos` shape. -/
theorem strongTransport_at_uEpsi_hVI_pos_of_perturbed
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hCont_pos :
      Filter.Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
              strongTransportTargetIntegrand sol x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))))) :
    (0 : ℝ) ≤
    ∫ x in UnitCube d,
        strongTransportTargetIntegrand sol x
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- For each `n`, multiply the per-step VI by `(n + 1) > 0`,
  -- preserving `≥ 0`.
  have hStep' :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ((n : ℝ) + 1) *
          ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    intro n
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_nonneg hpos (hStep_pos n)
  -- Pass `n → ∞` via `hCont_pos`.
  exact ge_of_tendsto' hCont_pos hStep'

/-- **Phase-5 σ → 0 Minty bridge — `−1` direction.**

Produces the unperturbed `hVI_neg` input of
`strongTransport_at_uEpsi_of_hVIeps_transport` from:

* `hStep_neg n` — the per-`n` perturbed-primal VI at `s := −1/(n+1) < 0`,
  exactly the conclusion of
  `strongTransport_at_uEpsi_perturbed sol hp_ge_one (-1/(n+1)) hI_A_n hI_B_n`.
* `hCont_neg` — the authorised σ → 0 Tendsto convergence of the
  *negated*-rescaled perturbed integral `−((n+1)) · ∫ Iperturb_n` to
  the target integral `∫ I∞`. (Negating compensates the sign flip
  introduced by dividing the per-step `0 ≤ ∫ Iperturb_n` by `s < 0`.)

Conclusion: `∫ I∞ ≤ 0`, the `hVI_neg` shape. -/
theorem strongTransport_at_uEpsi_hVI_neg_of_perturbed
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hCont_neg :
      Filter.Tendsto
        (fun n : ℕ =>
          -((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
              strongTransportTargetIntegrand sol x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))))) :
    ∫ x in UnitCube d,
        strongTransportTargetIntegrand sol x
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
      ≤ (0 : ℝ) := by
  -- For each `n`, multiply the per-step VI by `−(n + 1) ≤ 0`,
  -- flipping `≥ 0` to `≤ 0`.
  have hStep' :
      ∀ n : ℕ,
        -((n : ℝ) + 1) *
          ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
          ≤ (0 : ℝ) := by
    intro n
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hneg : -((n : ℝ) + 1) ≤ 0 := by linarith
    -- `−(n+1) * (nonneg) ≤ 0`.
    have := mul_nonpos_of_nonpos_of_nonneg hneg (hStep_neg n)
    exact this
  -- Pass `n → ∞` via `hCont_neg`.
  exact le_of_tendsto' hCont_neg hStep'

/-! ### Sanity-check `example`s for the Phase-5 σ → 0 bridge

Compose the bridge with `strongTransport_at_uEpsi_of_hVIeps_transport`
to verify the integrand shapes match. -/

/-- Sanity check: `hVI_pos`-shaped output typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hCont_pos :
      Filter.Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
              strongTransportTargetIntegrand sol x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))))) :
    (0 : ℝ) ≤
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  strongTransport_at_uEpsi_hVI_pos_of_perturbed sol hStep_pos hCont_pos

/-- Sanity check: `hVI_neg`-shaped output typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hCont_neg :
      Filter.Tendsto
        (fun n : ℕ =>
          -((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
              strongTransportTargetIntegrand sol x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))))) :
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
      ≤ (0 : ℝ) :=
  strongTransport_at_uEpsi_hVI_neg_of_perturbed sol hStep_neg hCont_neg

/-- Composed sanity check: the σ → 0 bridge feeds
`strongTransport_at_uEpsi_of_hVIeps_transport` directly, producing
the line-1212 strong-transport identity from purely perturbed-VI +
Tendsto inputs. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hCont_pos :
      Filter.Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
              strongTransportTargetIntegrand sol x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))))
    (hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hCont_neg :
      Filter.Tendsto
        (fun n : ℕ =>
          -((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
              strongTransportTargetIntegrand sol x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))))) :
    (0 : ℝ) =
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  strongTransport_at_uEpsi_of_hVIeps_transport sol
    (strongTransport_at_uEpsi_hVI_pos_of_perturbed sol hStep_pos hCont_pos)
    (strongTransport_at_uEpsi_hVI_neg_of_perturbed sol hStep_neg hCont_neg)

/-! ### L¹ dominator (uniform in `s ∈ [-1, 1] ∖ {0}`) for the rescaled
perturbed transport integrand

Per task `infra-P5-strongTransport-perturbed-dominator`. The dominator
is consumed by the DCT discharge of the σ → 0 Tendsto inputs
(`hCont_pos`/`hCont_neg`).

Following CONVENTIONS §1b/§8, we take dominator pieces as authorised
inputs:

* `G_mDpH` — an L¹ envelope with a uniform-in-`s` pointwise bound for
  `|m · DpH(x, (1+s)·Du, m) ⬝ (s·Du) / s|`. (For `s ∈ [-1,1]`, the
  inner argument `(1+s)·Du` varies; bounding this product uniformly in
  `s` requires Hamiltonian-side hypotheses outside this lemma's scope.)
* `G_vec` — an L¹ envelope for the `vecAbsPowMinusTwo`-driven Du-piece.
* `G_scal` — an L¹ envelope for the `absPowMinusTwo`-driven u-piece.
* `MemLpPer 1` certificate for `|m-1|·|u|`. -/

/-- L¹ dominator (uniform in `s ∈ [-1, 1] ∖ {0}`) for the rescaled
perturbed transport integrand `strongTransportPerturbedIntegrand sol s x / s`.

The dominator splits into four `MemLpPer 1` pieces, mirroring the four
summands of `strongTransportPerturbedIntegrand`. For each summand `Tᵢ`,
the lemma takes:
- a `MemLpPer 1` envelope `Gᵢ`, and
- a uniform-in-`s` pointwise bound `|Tᵢ(s,x) / s| ≤ Gᵢ(x)` for
  `s ∈ [-1,1]∖{0}` and a.e. `x ∈ UnitCube d`.

Each `Gᵢ` admits a closed-form discharge (mirroring Phase-4
constructions in `Hamiltonian/Estimates.lean` for `T₁`, and the bounds
`vecAbsPowMinusTwo_mul_dot_abs_le` / `absPowMinusTwo_mul_abs_le` for
`T₃`/`T₄`); these discharges are filed as separate child tasks. -/
theorem strongTransportPerturbedIntegrand_dominator
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    -- Term 1 (`m · DpH(x, (1+s)·Du, m) ⬝ (s·Du)`) dominator.
    (G_mDpH : (Fin d → ℝ) → ℝ)
    (hG_mDpH : MemLpPer (d := d) 1 G_mDpH)
    (h_mDpH_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |sol.m x *
              (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                ⬝ (fun i => s * sol.Du i x)) / s|
            ≤ G_mDpH x)
    -- Term 2 (`(m - 1) · (s · u)`) dominator.
    (hG_mu : MemLpPer (d := d) 1
        (fun x => |sol.m x - 1| * |sol.u x|))
    -- Term 3 (`ε · vecAbsPowMinusTwo γ̄ · ((1+s)·Du ⬝ s·Du)`) dominator.
    (G_vec : (Fin d → ℝ) → ℝ)
    (hG_vec : MemLpPer (d := d) 1 G_vec)
    (h_vec_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |ε * (vecAbsPowMinusTwo γBarReal
                  (fun i => sol.Du i x + s * sol.Du i x)
                * ((fun i => sol.Du i x + s * sol.Du i x)
                    ⬝ (fun i => s * sol.Du i x))) / s|
            ≤ G_vec x)
    -- Term 4 (`ε · absPowMinusTwo γ̄ (u + s·u) · ((u + s·u) · (s · u))`) dominator.
    (G_scal : (Fin d → ℝ) → ℝ)
    (hG_scal : MemLpPer (d := d) 1 G_scal)
    (h_scal_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
                  * ((sol.u x + s * sol.u x) * (s * sol.u x))) / s|
            ≤ G_scal x) :
    ∃ g : (Fin d → ℝ) → ℝ,
      MeasureTheory.IntegrableOn g (UnitCube d) volume ∧
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |strongTransportPerturbedIntegrand sol s x / s| ≤ g x := by
  -- The dominator `g := G_mDpH + |m-1|·|u| + G_vec + G_scal`.
  set Gmu : (Fin d → ℝ) → ℝ :=
    fun x => |sol.m x - 1| * |sol.u x| with hGmu_def
  set g : (Fin d → ℝ) → ℝ :=
    fun x => G_mDpH x + Gmu x + G_vec x + G_scal x with hg_def
  -- `MemLpPer 1` closure under finite addition.
  have hg_mem : MemLpPer (d := d) 1 g := by
    have h12 : MemLpPer (d := d) 1 (G_mDpH + Gmu) :=
      MemLpPer.add hG_mDpH hG_mu
    have h123 : MemLpPer (d := d) 1 (G_mDpH + Gmu + G_vec) :=
      MemLpPer.add h12 hG_vec
    have h1234 : MemLpPer (d := d) 1 (G_mDpH + Gmu + G_vec + G_scal) :=
      MemLpPer.add h123 hG_scal
    convert h1234 using 1
  -- Integrability on the unit cube.
  have hg_int : MeasureTheory.IntegrableOn g (UnitCube d) volume :=
    integrableOn_of_memLpPer (le_refl 1) hg_mem
  refine ⟨g, hg_int, ?_⟩
  intro s hs hs0
  -- Combine the four pointwise bounds.
  filter_upwards [h_mDpH_pt s hs hs0,
                  h_vec_pt s hs hs0,
                  h_scal_pt s hs hs0]
    with x hx_mDpH hx_vec hx_scal
  -- The integrand `I(s,x)` divided by `s` decomposes as four summands.
  -- We use the `add_div` distribution: `(a + b + c) / s = a/s + b/s + c/s`.
  -- By the triangle inequality, `|I/s| ≤ |T₁/s| + |T₂/s| + |T₃/s| + |T₄/s|`,
  -- and each is bounded by the corresponding envelope.
  -- ===== T₁ (m·DpH⬝(s·Du)) =====
  -- This is what `hx_mDpH` directly bounds.
  -- ===== T₂ ((m - 1)(s · u)) =====
  -- |(m - 1)(s · u) / s| = |(m - 1) · u| ≤ |m - 1| * |u|.
  have hT2_eq :
      ((sol.m x - 1) * (s * sol.u x)) / s = (sol.m x - 1) * sol.u x := by
    field_simp
  have hT2_bound :
      |((sol.m x - 1) * (s * sol.u x)) / s| ≤ Gmu x := by
    rw [hT2_eq, abs_mul]
  -- ===== T₃ (ε · vecAbsPowMinusTwo · ⟨V1, Y1⟩) =====
  -- `hx_vec` directly bounds this.
  -- ===== T₄ (ε · absPowMinusTwo · (· · ·)) =====
  -- `hx_scal` directly bounds this.
  -- The integrand `I` (unfolded) divided by `s`.
  -- Use linearity of division: `(A + B + C) / s = A/s + B/s + C/s`,
  -- and `ε · (P + Q) / s = ε · P / s + ε · Q / s`.
  -- Triangle inequality on the four summands.
  set T1 : ℝ := sol.m x *
      (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
        ⬝ (fun i => s * sol.Du i x)) with hT1_def
  set T2 : ℝ := (sol.m x - 1) * (s * sol.u x) with hT2_def
  set T3 : ℝ := ε * (vecAbsPowMinusTwo γBarReal
                      (fun i => sol.Du i x + s * sol.Du i x)
                    * ((fun i => sol.Du i x + s * sol.Du i x)
                        ⬝ (fun i => s * sol.Du i x))) with hT3_def
  set T4 : ℝ := ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
                    * ((sol.u x + s * sol.u x) * (s * sol.u x))) with hT4_def
  -- Decompose: `strongTransportPerturbedIntegrand sol s x = T1 + T2 + (T3 + T4)`.
  have hI_decomp :
      strongTransportPerturbedIntegrand sol s x = T1 + T2 + (T3 + T4) := by
    -- LHS = T1 + T2 + ε · ((vecAbsPowMinusTwo·...) + (absPowMinusTwo·...)).
    -- The ε-block expands to T3 + T4 by `mul_add`.
    have h_eps :
        ε * (vecAbsPowMinusTwo γBarReal
                (fun i => sol.Du i x + s * sol.Du i x)
              * ((fun i => sol.Du i x + s * sol.Du i x)
                  ⬝ (fun i => s * sol.Du i x))
            + absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
              * ((sol.u x + s * sol.u x) * (s * sol.u x)))
          = T3 + T4 := by
      rw [hT3_def, hT4_def, mul_add]
    -- Apply h_eps to rewrite the ε-block and conclude.
    change T1 + T2 + ε * (_ + _) = T1 + T2 + (T3 + T4)
    rw [h_eps]
  -- Divide by s and apply the triangle inequality.
  have hI_div_decomp :
      strongTransportPerturbedIntegrand sol s x / s
        = T1 / s + T2 / s + (T3 / s + T4 / s) := by
    rw [hI_decomp]; ring
  rw [hI_div_decomp]
  -- |a/s + b/s + (c/s + d/s)| ≤ |a/s| + |b/s| + |c/s| + |d/s|
  have htri : |T1 / s + T2 / s + (T3 / s + T4 / s)|
                ≤ |T1 / s| + |T2 / s| + (|T3 / s| + |T4 / s|) := by
    have h1 := abs_add_le (T1 / s + T2 / s) (T3 / s + T4 / s)
    have h2 := abs_add_le (T1 / s) (T2 / s)
    have h3 := abs_add_le (T3 / s) (T4 / s)
    linarith
  -- Combine with the four envelope bounds.
  have hb1 : |T1 / s| ≤ G_mDpH x := hx_mDpH
  have hb2 : |T2 / s| ≤ Gmu x := hT2_bound
  have hb3 : |T3 / s| ≤ G_vec x := hx_vec
  have hb4 : |T4 / s| ≤ G_scal x := hx_scal
  -- Conclude.
  change |T1 / s + T2 / s + (T3 / s + T4 / s)|
            ≤ G_mDpH x + Gmu x + G_vec x + G_scal x
  linarith

/-! ### Closed-form discharge of `G_scal`

Per task `infra-P5-strongTransport-discharge-G_scal`. Produces an
`MemLpPer 1` envelope `G_scal` with the uniform-in-`s` pointwise bound
required by `strongTransportPerturbedIntegrand_dominator`'s `T₄`
input. The envelope is `|ε| · (2^γ̄ + 1) · |sol.u|^γ̄`, derived from
`absPowMinusTwo_mul_abs_le γ̄ hγ ((1+s)·u) u` and the `1 ≤ γ̄`-ranged
`MemLpPer (ENNReal.ofReal γBarReal) sol.u` certificate carried by
`RegularizedBareSolution.huLp`. -/

/-- **Closed-form discharge of `G_scal`.**

For a `RegularizedBareSolution` (with `1 ≤ γ̄`), the envelope
`G_scal x := |ε| * (2^γ̄ + 1) * |sol.u x|^γ̄` is `MemLpPer 1` and
satisfies the uniform-in-`s` pointwise bound required for the `T₄`
slot of `strongTransportPerturbedIntegrand_dominator`.

The pointwise bound exploits the algebraic identity
`(u + s·u) * (s·u) = s · ((1+s)·u · u)` which cancels the outer
division by `s`. After cancellation, the standard crude bound
`absPowMinusTwo_mul_abs_le γ̄ hγ ((1+s)·u) u` gives a
`|(1+s)·u|^γ̄ + |u|^γ̄`-shaped sum, and `|1+s| ≤ 2` for
`s ∈ [-1,1]`. -/
theorem strongTransportDominator_G_scal_of_sol
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hγ : 1 ≤ γBarReal)
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal') :
    ∃ G : (Fin d → ℝ) → ℝ,
      MemLpPer (d := d) 1 G ∧
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          |ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
                  * ((sol.u x + s * sol.u x) * (s * sol.u x))) / s|
            ≤ G x := by
  -- Setup constants.
  have hγ_nn : (0 : ℝ) ≤ γBarReal := le_trans zero_le_one hγ
  have hpne : (ENNReal.ofReal γBarReal) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ)).ne'
  have hpne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγ_nn
  -- Step 1: integrability of `|sol.u|^γ̄` on the unit cube.
  have hInt_u : Integrable (fun x : Fin d → ℝ => |sol.u x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
    have hI := sol.huLp.toMemLp.integrable_norm_rpow hpne hpne_top
    rw [hγtoReal] at hI
    have heq : (fun x : Fin d → ℝ => ‖sol.u x‖ ^ γBarReal)
                = (fun x => |sol.u x| ^ γBarReal) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq] at hI
    exact hI
  -- Step 2: define the envelope.
  set G_scal : (Fin d → ℝ) → ℝ :=
    fun x => |ε| * ((2 : ℝ) ^ γBarReal + 1) * |sol.u x| ^ γBarReal
      with hG_def
  -- Step 3: `MemLpPer 1 G_scal`.
  have hG_mem : MemLpPer (d := d) 1 G_scal := by
    have hInt_scaled : Integrable G_scal (volume.restrict (UnitCube d)) :=
      hInt_u.const_mul (|ε| * ((2 : ℝ) ^ γBarReal + 1))
    exact MemLp.toMemLpPer (memLp_one_iff_integrable.mpr hInt_scaled)
  refine ⟨G_scal, hG_mem, ?_⟩
  intro s hs hs0
  -- Step 4: pointwise bound — derived from a forall-x bound, so we
  -- can simply emit the universal version.
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- Abbreviations.
  set u := sol.u x with hu_def
  -- `(u + s·u) = (1+s)·u`.
  have hsum_eq : sol.u x + s * sol.u x = (1 + s) * u := by
    rw [hu_def]; ring
  -- The numerator factors as `s · (ε · X · ((1+s)·u) · u)`, where
  -- `X := absPowMinusTwo γ̄ ((1+s)·u)`. Hence dividing by `s ≠ 0`
  -- yields `ε · X · ((1+s)·u) · u`, with no `1/s` blowup.
  set X : ℝ := absPowMinusTwo γBarReal ((1 + s) * u) with hX_def
  have hnum_factor :
      ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
              * ((sol.u x + s * sol.u x) * (s * sol.u x)))
        = s * (ε * (X * ((1 + s) * u * u))) := by
    rw [hsum_eq]
    rw [hX_def]
    ring
  have hdiv_eq :
      ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
              * ((sol.u x + s * sol.u x) * (s * sol.u x))) / s
        = ε * (X * ((1 + s) * u * u)) := by
    rw [hnum_factor]
    field_simp
  rw [hdiv_eq]
  -- Step 5: the crude pointwise bound from `absPowMinusTwo_mul_abs_le`.
  have hcrude :
      |X * ((1 + s) * u * u)| ≤ |(1 + s) * u| ^ γBarReal + |u| ^ γBarReal := by
    have h := absPowMinusTwo_mul_abs_le γBarReal hγ ((1 + s) * u) u
    -- `h : |absPowMinusTwo γ̄ ((1+s)·u) * (((1+s)·u) * u)|
    --        ≤ |(1+s)·u|^γ̄ + |u|^γ̄`.
    simpa [hX_def] using h
  -- Step 6: bound `|(1+s)·u|^γ̄` by `2^γ̄ · |u|^γ̄`.
  have habs_1ps_le_two : |1 + s| ≤ 2 := by
    rcases hs with ⟨h1, h2⟩
    have : -2 ≤ 1 + s ∧ 1 + s ≤ 2 := by constructor <;> linarith
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have habs_1ps_nn : (0 : ℝ) ≤ |1 + s| := abs_nonneg _
  have habs_u_nn : (0 : ℝ) ≤ |u| := abs_nonneg _
  have hpow_bound :
      |(1 + s) * u| ^ γBarReal ≤ (2 : ℝ) ^ γBarReal * |u| ^ γBarReal := by
    rw [abs_mul, Real.mul_rpow habs_1ps_nn habs_u_nn]
    have h_le : |1 + s| ^ γBarReal ≤ (2 : ℝ) ^ γBarReal :=
      Real.rpow_le_rpow habs_1ps_nn habs_1ps_le_two hγ_nn
    have hpow_u_nn : 0 ≤ |u| ^ γBarReal := Real.rpow_nonneg habs_u_nn _
    exact mul_le_mul_of_nonneg_right h_le hpow_u_nn
  -- Step 7: assemble.
  have habs_eps_nn : (0 : ℝ) ≤ |ε| := abs_nonneg _
  have hX_nn :
      |X * ((1 + s) * u * u)| ≤ (2 : ℝ) ^ γBarReal * |u| ^ γBarReal
        + |u| ^ γBarReal := by
    have := hcrude
    linarith [hpow_bound]
  -- Multiply both sides by |ε| ≥ 0.
  have habs_total :
      |ε * (X * ((1 + s) * u * u))|
        ≤ |ε| * ((2 : ℝ) ^ γBarReal * |u| ^ γBarReal + |u| ^ γBarReal) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hX_nn habs_eps_nn
  -- Rearrange to match `G_scal x = |ε| * (2^γ̄ + 1) * |u|^γ̄`.
  have hRHS_eq :
      |ε| * ((2 : ℝ) ^ γBarReal * |u| ^ γBarReal + |u| ^ γBarReal)
        = G_scal x := by
    rw [hG_def, hu_def]; ring
  calc |ε * (X * ((1 + s) * u * u))|
      ≤ |ε| * ((2 : ℝ) ^ γBarReal * |u| ^ γBarReal + |u| ^ γBarReal) :=
        habs_total
    _ = G_scal x := hRHS_eq

/-! ### Closed-form discharge of `G_vec`

Per task `infra-P5-strongTransport-discharge-G_vec`. Produces an
`MemLpPer 1` envelope `G_vec` with the uniform-in-`s` pointwise bound
required by `strongTransportPerturbedIntegrand_dominator`'s `T₃`
input. The envelope is `|ε| · (2^γ̄ + 1) · ((Du ⬝ Du)^(γ̄/2))`,
derived from `vecAbsPowMinusTwo_mul_dot_abs_le γ̄ hγ ((1+s)·Du) Du`
and the `1 ≤ γ̄`-ranged `MemLpPer (ENNReal.ofReal γBarReal) (Du i)`
certificates carried by `RegularizedBareSolution.hDuLp`. -/

/-- **`MemLpPer 1` of `(g ⬝ g)^(γ̄/2)` from per-component
`MemLpPer γ̄`.**

Hoists the closure pattern previously inlined as `hInt_dot_rpow`
(L12010–12055). For `γ̄ ≥ 1` and a vector field `g : Fin d → (Fin d → ℝ) → ℝ`
with each component `g i ∈ MemLpPer γ̄`, the pointwise function
`x ↦ ((g·)⬝(g·))^(γ̄/2)` lies in `MemLpPer 1`. The proof bounds it
pointwise by `d^(γ̄-1) · ∑ᵢ |g i|^γ̄` (via Jensen) and concludes by
`MemLp.toMemLpPer ∘ memLp_one_iff_integrable.mpr`. -/
private lemma memLpPer_one_dot_self_rpow_half_of_memLpPer
    {γBarReal : ℝ} (hγ_one_le : (1 : ℝ) ≤ γBarReal)
    (g : Fin d → (Fin d → ℝ) → ℝ)
    (hg : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (g i)) :
    MemLpPer (d := d) 1
      (fun x => ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2)) := by
  have hγ_nn : (0 : ℝ) ≤ γBarReal := le_trans zero_le_one hγ_one_le
  have hpne : (ENNReal.ofReal γBarReal) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ_one_le)).ne'
  have hpne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγ_nn
  -- Integrability of `|g i|^γ̄` from `MemLpPer γ̄ (g i)`.
  have hInt_g_i : ∀ i, Integrable
      (fun x : Fin d → ℝ => |g i x| ^ γBarReal)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hI := (hg i).toMemLp.integrable_norm_rpow hpne hpne_top
    rw [hγtoReal] at hI
    have heq : (fun x : Fin d → ℝ => ‖g i x‖ ^ γBarReal)
                = (fun x => |g i x| ^ γBarReal) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq] at hI
    exact hI
  have hInt_sum : Integrable
      (fun x : Fin d → ℝ => ∑ i, |g i x| ^ γBarReal)
      (volume.restrict (UnitCube d)) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_g_i i)
  have hInt_dom : Integrable
      (fun x : Fin d → ℝ =>
        ((d : ℝ)) ^ (γBarReal - 1) *
          ∑ i, |g i x| ^ γBarReal)
      (volume.restrict (UnitCube d)) := hInt_sum.const_mul _
  -- Pointwise upper bound via the Jensen helper.
  have hPointwise : ∀ x : Fin d → ℝ,
      ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2)
        ≤ ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |g i x| ^ γBarReal :=
    fun x => euclideanDot_self_rpow_le_sum_rpow (d := d) hγ_one_le _
  have hγ2_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
  have hCont : Continuous (fun y : ℝ => y ^ (γBarReal / 2)) :=
    Real.continuous_rpow_const hγ2_nn
  have hDot_aesm : AEStronglyMeasurable
      (fun x : Fin d → ℝ =>
        ((fun i => g i x) ⬝ (fun i => g i x)))
      (volume.restrict (UnitCube d)) := by
    unfold euclideanDot
    refine Finset.aestronglyMeasurable_fun_sum _ ?_
    intro i _
    exact (hg i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
  have hInt_target : Integrable
      (fun x : Fin d → ℝ =>
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2))
      (volume.restrict (UnitCube d)) := by
    apply MeasureTheory.Integrable.mono'
      (g := fun x => ((d : ℝ)) ^ (γBarReal - 1) *
          ∑ i, |g i x| ^ γBarReal)
      hInt_dom
    · exact hCont.comp_aestronglyMeasurable hDot_aesm
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hnn : (0 : ℝ) ≤
          ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2) :=
        Real.rpow_nonneg (euclideanDot_self_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hPointwise x
  exact MemLp.toMemLpPer (memLp_one_iff_integrable.mpr hInt_target)

/-- **Closed-form discharge of `G_vec`.**

For a `RegularizedBareSolution` (with `1 ≤ γ̄`), the envelope
`G_vec x := |ε| * (2^γ̄ + 1) * ((Du x ⬝ Du x) ^ (γ̄/2))` is `MemLpPer 1`
and satisfies the uniform-in-`s` pointwise bound required for the `T₃`
slot of `strongTransportPerturbedIntegrand_dominator`.

The pointwise bound exploits the bilinearity identity
`(1+s)·Du ⬝ (s·Du) = s · ((1+s)·Du ⬝ Du)`, which cancels the outer
division by `s`. After cancellation, the standard crude bound
`vecAbsPowMinusTwo_mul_dot_abs_le γ̄ hγ ((1+s)·Du) Du` gives a
`((1+s)·Du⬝(1+s)·Du)^(γ̄/2) + (Du⬝Du)^(γ̄/2)` sum, and the
homogeneity `((c·V)⬝(c·V)) = c²·(V⬝V)` plus `|1+s| ≤ 2` for
`s ∈ [-1,1]` gives the `2^γ̄`-factor. -/
theorem strongTransportDominator_G_vec_of_sol
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hγ : 1 ≤ γBarReal)
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal') :
    ∃ G : (Fin d → ℝ) → ℝ,
      MemLpPer (d := d) 1 G ∧
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          |ε * (vecAbsPowMinusTwo γBarReal
                  (fun i => sol.Du i x + s * sol.Du i x)
                * ((fun i => sol.Du i x + s * sol.Du i x)
                    ⬝ (fun i => s * sol.Du i x))) / s|
            ≤ G x := by
  have hγ_nn : (0 : ℝ) ≤ γBarReal := le_trans zero_le_one hγ
  -- Step 1: `MemLpPer 1` of the dot-self-rpow factor.
  have hDot_memLpPer : MemLpPer (d := d) 1
      (fun x => ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)) :=
    memLpPer_one_dot_self_rpow_half_of_memLpPer hγ sol.Du sol.hDuLp
  -- Step 2: define the envelope.
  set G_vec : (Fin d → ℝ) → ℝ :=
    fun x => |ε| * ((2 : ℝ) ^ γBarReal + 1) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (γBarReal / 2)
      with hG_def
  -- Step 3: `MemLpPer 1 G_vec`.
  have hG_mem : MemLpPer (d := d) 1 G_vec := by
    -- Multiply the `MemLpPer 1` factor by the constant `|ε| * (2^γ̄+1)`.
    have hInt :=
      (memLp_one_iff_integrable.mp hDot_memLpPer.toMemLp).const_mul
        (|ε| * ((2 : ℝ) ^ γBarReal + 1))
    exact MemLp.toMemLpPer (memLp_one_iff_integrable.mpr hInt)
  refine ⟨G_vec, hG_mem, ?_⟩
  intro s hs hs0
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- Abbreviations.
  set Du : Fin d → ℝ := fun i => sol.Du i x with hDu_def
  -- `(Du i + s · Du i) = (1+s) · Du i`.
  have hsum_eq : (fun i => sol.Du i x + s * sol.Du i x)
                = fun i => (1 + s) * Du i := by
    funext i; rw [hDu_def]; ring
  -- Bilinearity: `V ⬝ (s · w) = s · (V ⬝ w)`. Use a direct unfold.
  have hdot_smul_right : ∀ V W : Fin d → ℝ,
      V ⬝ (fun i => s * W i) = s * (V ⬝ W) := by
    intro V W
    unfold euclideanDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  -- Numerator factors as `s * (ε * (X * ((1+s)·Du ⬝ Du)))`,
  -- where `X := vecAbsPowMinusTwo γ̄ ((1+s)·Du)`.
  set X : ℝ := vecAbsPowMinusTwo γBarReal (fun i => (1 + s) * Du i) with hX_def
  have hnum_factor :
      ε * (vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
            * ((fun i => sol.Du i x + s * sol.Du i x)
                ⬝ (fun i => s * sol.Du i x)))
        = s * (ε * (X * ((fun i => (1 + s) * Du i) ⬝ Du))) := by
    rw [hsum_eq]
    rw [hdot_smul_right]
    rw [hX_def]
    ring
  have hdiv_eq :
      ε * (vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
            * ((fun i => sol.Du i x + s * sol.Du i x)
                ⬝ (fun i => s * sol.Du i x))) / s
        = ε * (X * ((fun i => (1 + s) * Du i) ⬝ Du)) := by
    rw [hnum_factor]
    field_simp
  rw [hdiv_eq]
  -- Step 5: the crude pointwise bound from `vecAbsPowMinusTwo_mul_dot_abs_le`.
  set V : Fin d → ℝ := fun i => (1 + s) * Du i with hV_def
  have hcrude :
      |X * (V ⬝ Du)| ≤ (V ⬝ V) ^ (γBarReal / 2) + (Du ⬝ Du) ^ (γBarReal / 2) := by
    have h := vecAbsPowMinusTwo_mul_dot_abs_le γBarReal hγ V Du
    simpa [hX_def, hV_def] using h
  -- Step 6: bound `(V⬝V)^(γ̄/2) ≤ 2^γ̄ · (Du⬝Du)^(γ̄/2)`.
  -- `V ⬝ V = (1+s)² · (Du ⬝ Du)`.
  have hVV_eq : V ⬝ V = (1 + s) ^ 2 * (Du ⬝ Du) := by
    unfold euclideanDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hV_def]; ring
  have hDuDu_nn : (0 : ℝ) ≤ Du ⬝ Du := euclideanDot_self_nonneg Du
  have h1ps_sq_nn : (0 : ℝ) ≤ (1 + s) ^ 2 := sq_nonneg _
  have hVV_nn : (0 : ℝ) ≤ V ⬝ V := euclideanDot_self_nonneg V
  -- `((1+s)² · (Du·Du))^(γ̄/2) = ((1+s)²)^(γ̄/2) · (Du·Du)^(γ̄/2)`.
  have hVV_rpow_split :
      (V ⬝ V) ^ (γBarReal / 2)
        = ((1 + s) ^ 2) ^ (γBarReal / 2) * (Du ⬝ Du) ^ (γBarReal / 2) := by
    rw [hVV_eq, Real.mul_rpow h1ps_sq_nn hDuDu_nn]
  -- `((1+s)²)^(γ̄/2) = |1+s|^γ̄ ≤ 2^γ̄`.
  have habs_1ps_le_two : |1 + s| ≤ 2 := by
    rcases hs with ⟨h1, h2⟩
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have habs_1ps_nn : (0 : ℝ) ≤ |1 + s| := abs_nonneg _
  have h1ps_sq_eq : (1 + s) ^ 2 = |1 + s| ^ (2 : ℝ) := by
    rw [show ((|1 + s| : ℝ)) ^ (2 : ℝ) = |1 + s| ^ (2 : ℕ) from by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]]
    rw [sq_abs]
  have hpow_VV_eq :
      ((1 + s) ^ 2) ^ (γBarReal / 2) = |1 + s| ^ γBarReal := by
    rw [h1ps_sq_eq, ← Real.rpow_mul habs_1ps_nn]
    congr 1; ring
  have hpow_le_two_γ : |1 + s| ^ γBarReal ≤ (2 : ℝ) ^ γBarReal :=
    Real.rpow_le_rpow habs_1ps_nn habs_1ps_le_two hγ_nn
  have hDuDu_rpow_nn : (0 : ℝ) ≤ (Du ⬝ Du) ^ (γBarReal / 2) :=
    Real.rpow_nonneg hDuDu_nn _
  have hVV_rpow_le :
      (V ⬝ V) ^ (γBarReal / 2)
        ≤ (2 : ℝ) ^ γBarReal * (Du ⬝ Du) ^ (γBarReal / 2) := by
    rw [hVV_rpow_split, hpow_VV_eq]
    exact mul_le_mul_of_nonneg_right hpow_le_two_γ hDuDu_rpow_nn
  -- Step 7: assemble. `|X * (V ⬝ Du)| ≤ 2^γ̄ * (Du⬝Du)^(γ̄/2) + (Du⬝Du)^(γ̄/2)`.
  have habs_X_le :
      |X * (V ⬝ Du)|
        ≤ (2 : ℝ) ^ γBarReal * (Du ⬝ Du) ^ (γBarReal / 2)
            + (Du ⬝ Du) ^ (γBarReal / 2) := by
    have := hcrude
    linarith [hVV_rpow_le]
  -- Multiply by |ε| ≥ 0.
  have habs_eps_nn : (0 : ℝ) ≤ |ε| := abs_nonneg _
  have habs_total :
      |ε * (X * (V ⬝ Du))|
        ≤ |ε| * ((2 : ℝ) ^ γBarReal * (Du ⬝ Du) ^ (γBarReal / 2)
                  + (Du ⬝ Du) ^ (γBarReal / 2)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left habs_X_le habs_eps_nn
  -- Identify with `G_vec x`.
  have hRHS_eq :
      |ε| * ((2 : ℝ) ^ γBarReal * (Du ⬝ Du) ^ (γBarReal / 2)
              + (Du ⬝ Du) ^ (γBarReal / 2))
        = G_vec x := by
    rw [hG_def, hDu_def]; ring
  calc |ε * (X * (V ⬝ Du))|
      ≤ |ε| * ((2 : ℝ) ^ γBarReal * (Du ⬝ Du) ^ (γBarReal / 2)
                + (Du ⬝ Du) ^ (γBarReal / 2)) := habs_total
    _ = G_vec x := hRHS_eq

/-! ### Closed-form discharge of `G_mDpH`

Per task `infra-P5-strongTransport-discharge-G_mDpH`. Produces an
`MemLpPer 1` envelope `G_mDpH` with the uniform-in-`s` pointwise bound
required by `strongTransportPerturbedIntegrand_dominator`'s `T₁`
input. -/

/-- **Closed-form discharge of `G_mDpH`.**

For a `RegularizedBareSolution` whose paper-side exponents
`βBarReal = h.β + 1`, `γBarReal = h.α · (h.β + 1) / h.β` align with
the power-growth bundle `h`, the envelope

```
G_mDpH x := K · h.C · (m x · ‖Du x‖^{α-1} + m x^{1+β-β/α} + m x)
              · ∑ i, |Du_i x|,         K := max (2^{α-1}) 1,
```

is `MemLpPer 1` and satisfies the uniform-in-`s` pointwise bound
required for the `T₁` slot of
`strongTransportPerturbedIntegrand_dominator`.

Strategy:

* The pointwise bound exploits bilinearity in slot 2 of `⬝`,
  `(...) ⬝ (s · Du) = s · ((...) ⬝ Du)`, which cancels the outer `1/s`.
* `mDpH_pointwise_bound` gives `‖m · DpH(x, p, m)‖ ≤ A x` for the
  three-summand Hölder dominator `A`. Cauchy–Schwarz Pi-style yields
  `|m · (V ⬝ Du)| ≤ ‖m·V‖ · ∑ |Du_i|`. Bound `‖(1+s)·Du‖^{α-1} ≤
  2^{α-1} · ‖Du‖^{α-1}` and absorb the constant in `K`.
* `A ∈ MemLpPer γ̄'` via `mDpH_dominator_memLpPer_gammaBar'`.
* `B := ∑ |Du_i| ∈ MemLpPer γ̄` from `Du_i ∈ MemLpPer γ̄`.
* `(γ̄', γ̄)` are Hölder conjugates, so `A · B ∈ L¹` via
  `MemLpPer.integrable_mul`. -/
theorem strongTransportDominator_G_mDpH_of_sol
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (h : HypothesisPowerGrowth H DpH)
    (hβBarPaper : βBarReal = h.β + 1)
    (hγBarPaper : γBarReal = h.α * (h.β + 1) / h.β) :
    ∃ G : (Fin d → ℝ) → ℝ,
      MemLpPer (d := d) 1 G ∧
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          |sol.m x *
              (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                ⬝ (fun i => s * sol.Du i x)) / s|
            ≤ G x := by
  -- Standing positivity facts from the power-growth bundle.
  have hαpos : 0 < h.α := lt_trans one_pos h.hα
  have hα_ge_one : 1 ≤ h.α := h.hα.le
  have hαm1_nn : 0 ≤ h.α - 1 := by linarith
  have hβ_pos : 0 < h.β := h.hβ
  have hbb_pos : 0 < h.β + 1 := by linarith
  have hγb_pos : 0 < h.α * (h.β + 1) / h.β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hγb_gt_one : 1 < h.α * (h.β + 1) / h.β := by
    rw [lt_div_iff₀ h.hβ]; nlinarith [h.hα, h.hβ]
  have hγbm1_pos : 0 < h.α * (h.β + 1) / h.β - 1 := by linarith
  have hγb' : 0 < h.α * (h.β + 1) / h.β /
                  (h.α * (h.β + 1) / h.β - 1) :=
    div_pos hγb_pos hγbm1_pos
  have hγBar_pos : 0 < γBarReal := by rw [hγBarPaper]; exact hγb_pos
  -- Finite-measure instance on the cube.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- The Hamiltonian-side dominator `A x`.
  set A : (Fin d → ℝ) → ℝ :=
    fun x => h.C * (sol.m x * ‖fun j => sol.Du j x‖ ^ (h.α - 1)
                      + sol.m x ^ (1 + h.β - h.β / h.α)
                      + sol.m x) with hA_def
  -- The Cauchy–Schwarz factor `B x := ∑ |Du_i|`.
  set B : (Fin d → ℝ) → ℝ :=
    fun x => ∑ i, |sol.Du i x| with hB_def
  -- Constant absorbing the `2^{α-1}` factor (≥ 1).
  set Kconst : ℝ := max ((2 : ℝ) ^ (h.α - 1)) 1 with hKconst_def
  have hKconst_ge_one : 1 ≤ Kconst := by
    rw [hKconst_def]; exact le_max_right _ _
  have hKconst_nn : 0 ≤ Kconst := le_trans zero_le_one hKconst_ge_one
  have hpow_le_K : (2 : ℝ) ^ (h.α - 1) ≤ Kconst := by
    rw [hKconst_def]; exact le_max_left _ _
  have hpow_two_nn : 0 ≤ (2 : ℝ) ^ (h.α - 1) :=
    Real.rpow_nonneg (by norm_num) _
  -- Step 1: `A ∈ MemLpPer (ENNReal.ofReal γBar')` (where
  -- `γBar' := h.α(h.β+1)/h.β / (h.α(h.β+1)/h.β - 1)`).
  -- Translate `sol.hmLp`, `sol.hDuLp` to the paper exponents.
  have hmLp_paper : MemLpPer (d := d) (ENNReal.ofReal (h.β + 1)) sol.m := by
    rw [show ENNReal.ofReal (h.β + 1) = ENNReal.ofReal βBarReal from by
          rw [hβBarPaper]]
    exact sol.hmLp
  have hDuLp_paper : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (h.α * (h.β + 1) / h.β))
        (sol.Du i) := by
    intro i
    rw [show ENNReal.ofReal (h.α * (h.β + 1) / h.β)
            = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    exact sol.hDuLp i
  have hA_lp : MemLpPer (d := d)
      (ENNReal.ofReal (h.α * (h.β + 1) / h.β /
        (h.α * (h.β + 1) / h.β - 1))) A :=
    StationaryMFG.Hamiltonian.mDpH_dominator_memLpPer_gammaBar'
      h sol.m sol.Du hmLp_paper hDuLp_paper
  -- Step 2: `B ∈ MemLpPer (ENNReal.ofReal γBarReal)`.
  -- Each `|sol.Du i|` is in `MemLpPer γBar` via `MemLp.norm` plus
  -- `‖x‖ = |x|` for `x : ℝ`.
  have hAbsDu_lp : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x : (Fin d → ℝ) => |sol.Du i x|) := by
    intro i
    have hi : MemLp (fun x : (Fin d → ℝ) => ‖sol.Du i x‖)
                (ENNReal.ofReal γBarReal)
                (volume.restrict (UnitCube d)) :=
      (sol.hDuLp i).toMemLp.norm
    have heq :
        (fun x : (Fin d → ℝ) => ‖sol.Du i x‖)
          = (fun x : (Fin d → ℝ) => |sol.Du i x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at hi
    exact MemLp.toMemLpPer hi
  have hB_lp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) B := by
    have h_finsum :
        MemLp (fun x : (Fin d → ℝ) => ∑ i, |sol.Du i x|)
              (ENNReal.ofReal γBarReal)
              (volume.restrict (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (hAbsDu_lp i).toMemLp)
    exact MemLp.toMemLpPer h_finsum
  -- Step 3: Hölder conjugacy `(γBar', γBar)` (real form).
  have hγConj :
      Real.HolderConjugate
        (h.α * (h.β + 1) / h.β / (h.α * (h.β + 1) / h.β - 1))
        (h.α * (h.β + 1) / h.β) := by
    refine Real.holderConjugate_iff.mpr ?_
    refine ⟨?_, ?_⟩
    · -- 1 < γBar'
      rw [lt_div_iff₀ hγbm1_pos]; linarith
    · -- (γBar')⁻¹ + (γBar)⁻¹ = 1
      have hγb_ne : h.α * (h.β + 1) / h.β ≠ 0 := hγb_pos.ne'
      have hγbm1_ne : h.α * (h.β + 1) / h.β - 1 ≠ 0 := hγbm1_pos.ne'
      field_simp
      ring
  -- Step 4: `A * B ∈ L¹` via Hölder, hence `MemLpPer 1`.
  have hB_lp_paper : MemLpPer (d := d)
      (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) B := by
    rw [show ENNReal.ofReal (h.α * (h.β + 1) / h.β)
            = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    exact hB_lp
  have hAB_int : IntegrableOn (fun x => A x * B x) (UnitCube d) :=
    MemLpPer.integrable_mul hγConj hA_lp hB_lp_paper
  have hAB_memLp_one : MemLp (fun x => A x * B x) 1
        (volume.restrict (UnitCube d)) :=
    memLp_one_iff_integrable.mpr hAB_int
  have hAB_memLpPer : MemLpPer (d := d) 1 (fun x => A x * B x) :=
    MemLp.toMemLpPer hAB_memLp_one
  -- The envelope: `G_mDpH x := Kconst * A x * B x`. Equivalently
  -- `Kconst • (A · B)`.
  set Genv : (Fin d → ℝ) → ℝ := fun x => Kconst * A x * B x with hGenv_def
  have hGenv_mem : MemLpPer (d := d) 1 Genv := by
    have h_smul :
        MemLpPer (d := d) 1 (Kconst • (fun x => A x * B x)) :=
      hAB_memLpPer.const_smul Kconst
    -- `Kconst • (A · B) = Kconst * A * B`.
    have heq : (Kconst • (fun x : (Fin d → ℝ) => A x * B x))
                = Genv := by
      funext x
      simp [hGenv_def, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [heq] at h_smul
    exact h_smul
  refine ⟨Genv, hGenv_mem, ?_⟩
  intro s hs hs0
  -- Pointwise bound — held a.e. via `mDpH_pointwise_bound` and
  -- `sol.hmNonneg`.
  filter_upwards [StationaryMFG.Hamiltonian.mDpH_pointwise_bound h
                    (fun x => fun i => sol.Du i x + s * sol.Du i x),
                  sol.hmNonneg]
    with x hxbnd hxm_nn
  -- Abbreviations.
  set m₀ : ℝ := sol.m x with hm₀_def
  set Du₀ : Fin d → ℝ := fun i => sol.Du i x with hDu₀_def
  set Vp : Fin d → ℝ := fun i => Du₀ i + s * Du₀ i with hVp_def
  -- Bilinearity in slot 2 of `⬝`.
  have hdot_smul_right :
      (DpH x Vp m₀) ⬝ (fun i => s * Du₀ i)
        = s * ((DpH x Vp m₀) ⬝ Du₀) := by
    unfold euclideanDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  -- Cancel `s` from the outer division.
  have hdiv_eq :
      m₀ * (DpH x Vp m₀ ⬝ (fun i => s * Du₀ i)) / s
        = m₀ * (DpH x Vp m₀ ⬝ Du₀) := by
    rw [hdot_smul_right]
    rw [show m₀ * (s * (DpH x Vp m₀ ⬝ Du₀))
            = s * (m₀ * (DpH x Vp m₀ ⬝ Du₀)) from by ring]
    rw [mul_div_cancel_left₀ _ hs0]
  -- Translate the goal to bound `|m₀ · (DpH x Vp m₀ ⬝ Du₀)|`.
  show |m₀ * (DpH x Vp m₀ ⬝ (fun i => s * Du₀ i)) / s| ≤ Genv x
  rw [hdiv_eq]
  -- Cauchy–Schwarz Pi-style: `|v ⬝ w| ≤ ‖v‖ · ∑ |w_i|`.
  have hCS : ∀ v w : Fin d → ℝ,
      |v ⬝ w| ≤ ‖v‖ * ∑ i, |w i| := by
    intro v w
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
    linarith
  -- Get the pointwise bound from `mDpH_pointwise_bound` for `m₀ > 0`,
  -- handle `m₀ = 0` separately.
  rcases lt_or_eq_of_le hxm_nn with hm₀_pos | hm₀_zero
  · -- Case `m₀ > 0`.
    -- `|m₀ · (V ⬝ Du)| = m₀ · |V ⬝ Du| ≤ m₀ · ‖V‖ · B x = ‖m₀ • V‖ · B x`.
    have hbnd_mDpH :
        ‖m₀ • DpH x Vp m₀‖
          ≤ h.C * (m₀ * ‖Vp‖ ^ (h.α - 1)
                    + m₀ ^ (1 + h.β - h.β / h.α) + m₀) :=
      hxbnd m₀ hm₀_pos
    -- Replace `‖Vp‖^{α-1}` by `2^{α-1} · ‖Du₀‖^{α-1}`.
    have hVp_norm : ‖Vp‖ = |1 + s| * ‖Du₀‖ := by
      have heq : Vp = (1 + s) • Du₀ := by
        funext i
        rw [hVp_def]; simp [Pi.smul_apply, smul_eq_mul]; ring
      rw [heq, norm_smul, Real.norm_eq_abs]
    have habs_1ps_le_two : |1 + s| ≤ 2 := by
      rcases hs with ⟨h1, h2⟩
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have habs_1ps_nn : (0 : ℝ) ≤ |1 + s| := abs_nonneg _
    have hDu0_norm_nn : (0 : ℝ) ≤ ‖Du₀‖ := norm_nonneg _
    have hVp_pow_eq :
        ‖Vp‖ ^ (h.α - 1) = |1 + s| ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1) := by
      rw [hVp_norm, Real.mul_rpow habs_1ps_nn hDu0_norm_nn]
    have h1ps_pow_le_two :
        |1 + s| ^ (h.α - 1) ≤ (2 : ℝ) ^ (h.α - 1) :=
      Real.rpow_le_rpow habs_1ps_nn habs_1ps_le_two hαm1_nn
    have hDu0_pow_nn : (0 : ℝ) ≤ ‖Du₀‖ ^ (h.α - 1) :=
      Real.rpow_nonneg hDu0_norm_nn _
    have hVp_pow_le :
        ‖Vp‖ ^ (h.α - 1) ≤ (2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1) := by
      rw [hVp_pow_eq]
      exact mul_le_mul_of_nonneg_right h1ps_pow_le_two hDu0_pow_nn
    -- Now bound:
    -- `‖m₀ • V‖ ≤ h.C · (m₀ · 2^{α-1} · ‖Du₀‖^{α-1} + m₀^{1+β-β/α} + m₀)`.
    have hC_nn : 0 ≤ h.C := h.hC.le
    have hm₀_pow_le :
        h.C * (m₀ * ‖Vp‖ ^ (h.α - 1)
                + m₀ ^ (1 + h.β - h.β / h.α) + m₀)
          ≤ h.C * (m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
                + m₀ ^ (1 + h.β - h.β / h.α) + m₀) := by
      have hm₀_le :
          m₀ * ‖Vp‖ ^ (h.α - 1)
            ≤ m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1)) :=
        mul_le_mul_of_nonneg_left hVp_pow_le hxm_nn
      have h_inner_le :
          m₀ * ‖Vp‖ ^ (h.α - 1)
            + m₀ ^ (1 + h.β - h.β / h.α) + m₀
          ≤ m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
            + m₀ ^ (1 + h.β - h.β / h.α) + m₀ := by linarith
      exact mul_le_mul_of_nonneg_left h_inner_le hC_nn
    -- Key step: rearrange to factor `Kconst` out.
    have hbnd_with_K :
        h.C * (m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
                + m₀ ^ (1 + h.β - h.β / h.α) + m₀)
          ≤ Kconst * A x := by
      -- `Kconst ≥ 1` and `Kconst ≥ 2^{α-1}`. So
      -- `m₀ · 2^{α-1} · ‖Du₀‖^{α-1} ≤ Kconst · m₀ · ‖Du₀‖^{α-1}`,
      -- `m₀^{...} ≤ Kconst · m₀^{...}`, and `m₀ ≤ Kconst · m₀`.
      have hm0_pow_le_K :
          m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
            ≤ Kconst * (m₀ * ‖Du₀‖ ^ (h.α - 1)) := by
        have h1 :
            m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
              = (2 : ℝ) ^ (h.α - 1) * (m₀ * ‖Du₀‖ ^ (h.α - 1)) := by
          ring
        rw [h1]
        have hm0Du_nn :
            0 ≤ m₀ * ‖Du₀‖ ^ (h.α - 1) :=
          mul_nonneg hxm_nn hDu0_pow_nn
        exact mul_le_mul_of_nonneg_right hpow_le_K hm0Du_nn
      have hm0β_le_K :
          m₀ ^ (1 + h.β - h.β / h.α)
            ≤ Kconst * m₀ ^ (1 + h.β - h.β / h.α) := by
        have hbase_nn : 0 ≤ m₀ ^ (1 + h.β - h.β / h.α) :=
          Real.rpow_nonneg hxm_nn _
        nlinarith [hKconst_ge_one, hbase_nn]
      have hm0_le_K : m₀ ≤ Kconst * m₀ := by
        nlinarith [hKconst_ge_one, hxm_nn]
      have h_inner_le :
          m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
            + m₀ ^ (1 + h.β - h.β / h.α) + m₀
            ≤ Kconst * (m₀ * ‖Du₀‖ ^ (h.α - 1))
              + Kconst * m₀ ^ (1 + h.β - h.β / h.α)
              + Kconst * m₀ := by
        linarith
      have h_K_factor :
          Kconst * (m₀ * ‖Du₀‖ ^ (h.α - 1))
            + Kconst * m₀ ^ (1 + h.β - h.β / h.α)
            + Kconst * m₀
            = Kconst * (m₀ * ‖Du₀‖ ^ (h.α - 1)
                  + m₀ ^ (1 + h.β - h.β / h.α) + m₀) := by ring
      have h_combined :
          h.C * (m₀ * ((2 : ℝ) ^ (h.α - 1) * ‖Du₀‖ ^ (h.α - 1))
                  + m₀ ^ (1 + h.β - h.β / h.α) + m₀)
            ≤ h.C * (Kconst * (m₀ * ‖Du₀‖ ^ (h.α - 1)
                  + m₀ ^ (1 + h.β - h.β / h.α) + m₀)) := by
        have := mul_le_mul_of_nonneg_left
          (le_trans h_inner_le (le_of_eq h_K_factor)) hC_nn
        exact this
      -- `A x = h.C · (m · ‖Du‖^{α-1} + m^{1+β-β/α} + m)`.
      have hAx_def :
          A x = h.C * (m₀ * ‖Du₀‖ ^ (h.α - 1)
                  + m₀ ^ (1 + h.β - h.β / h.α) + m₀) := by
        rw [hA_def, hm₀_def, hDu₀_def]
      rw [hAx_def]
      -- Goal: ... ≤ Kconst * (h.C * (...)) ≡ h.C * (Kconst * (...))
      have hcomm :
          Kconst * (h.C * (m₀ * ‖Du₀‖ ^ (h.α - 1)
                  + m₀ ^ (1 + h.β - h.β / h.α) + m₀))
            = h.C * (Kconst * (m₀ * ‖Du₀‖ ^ (h.α - 1)
                  + m₀ ^ (1 + h.β - h.β / h.α) + m₀)) := by ring
      rw [hcomm]
      exact h_combined
    -- Combine: `‖m₀ • V‖ ≤ Kconst · A x`.
    have h_mDpH_norm_le_KA :
        ‖m₀ • DpH x Vp m₀‖ ≤ Kconst * A x :=
      le_trans hbnd_mDpH (le_trans hm₀_pow_le hbnd_with_K)
    -- `m₀ * ‖DpH‖ = ‖m₀ • DpH‖` (using m₀ ≥ 0).
    have hsmul_norm : ‖m₀ • DpH x Vp m₀‖ = m₀ * ‖DpH x Vp m₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxm_nn]
    -- Now: `|m₀ · (V ⬝ Du)| ≤ m₀ · ‖V‖ · B x ≤ Kconst · A x · B x`.
    have hCSmDpH := hCS (DpH x Vp m₀) Du₀
    -- `|m₀ * (V ⬝ Du)| = m₀ * |V ⬝ Du|`.
    have habs_m0 :
        |m₀ * (DpH x Vp m₀ ⬝ Du₀)|
          = m₀ * |DpH x Vp m₀ ⬝ Du₀| := by
      rw [abs_mul, abs_of_nonneg hxm_nn]
    have hB_nn : 0 ≤ B x := by
      rw [hB_def]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    -- Multiply `hCSmDpH` by `m₀ ≥ 0`.
    have hbound_main :
        m₀ * |DpH x Vp m₀ ⬝ Du₀|
          ≤ m₀ * (‖DpH x Vp m₀‖ * ∑ i, |Du₀ i|) :=
      mul_le_mul_of_nonneg_left hCSmDpH hxm_nn
    have hassoc :
        m₀ * (‖DpH x Vp m₀‖ * ∑ i, |Du₀ i|)
          = (m₀ * ‖DpH x Vp m₀‖) * ∑ i, |Du₀ i| := by ring
    have hBx_eq : B x = ∑ i, |Du₀ i| := by
      rw [hB_def, hDu₀_def]
    -- Combine through Cauchy–Schwarz and the smul-norm identity.
    have hbound_with_norm :
        m₀ * |DpH x Vp m₀ ⬝ Du₀|
          ≤ ‖m₀ • DpH x Vp m₀‖ * B x := by
      rw [hassoc] at hbound_main
      rw [← hsmul_norm] at hbound_main
      rw [hBx_eq]
      exact hbound_main
    -- Apply the `‖m₀ • V‖ ≤ Kconst · A x` bound.
    have hKAB_nn : 0 ≤ Kconst * A x := by
      have hAx_nn : 0 ≤ A x := by
        rw [hA_def]
        have hα1nn : 0 ≤ ‖fun j => sol.Du j x‖ ^ (h.α - 1) :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hpow_β_nn : 0 ≤ sol.m x ^ (1 + h.β - h.β / h.α) :=
          Real.rpow_nonneg hxm_nn _
        have hsum_nn :
            0 ≤ sol.m x * ‖fun j => sol.Du j x‖ ^ (h.α - 1)
                + sol.m x ^ (1 + h.β - h.β / h.α) + sol.m x := by
          have h1 : 0 ≤ sol.m x * ‖fun j => sol.Du j x‖ ^ (h.α - 1) :=
            mul_nonneg hxm_nn hα1nn
          linarith
        exact mul_nonneg h.hC.le hsum_nn
      exact mul_nonneg hKconst_nn hAx_nn
    have h_bound_final :
        m₀ * |DpH x Vp m₀ ⬝ Du₀| ≤ Kconst * A x * B x := by
      calc m₀ * |DpH x Vp m₀ ⬝ Du₀|
          ≤ ‖m₀ • DpH x Vp m₀‖ * B x := hbound_with_norm
        _ ≤ (Kconst * A x) * B x :=
            mul_le_mul_of_nonneg_right h_mDpH_norm_le_KA hB_nn
        _ = Kconst * A x * B x := by ring
    -- Conclude.
    rw [habs_m0]
    rw [show Genv x = Kconst * A x * B x from rfl]
    exact h_bound_final
  · -- Case `m₀ = 0`. LHS = 0; RHS ≥ 0.
    have hm₀_zero' : m₀ = 0 := hm₀_zero.symm
    have hLHS : m₀ * (DpH x Vp m₀ ⬝ Du₀) = 0 := by
      rw [hm₀_zero']; ring
    rw [hLHS, abs_zero]
    -- `Genv x ≥ 0`.
    have hAx_nn : 0 ≤ A x := by
      rw [hA_def]
      have hα1nn : 0 ≤ ‖fun j => sol.Du j x‖ ^ (h.α - 1) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hpow_β_nn : 0 ≤ sol.m x ^ (1 + h.β - h.β / h.α) :=
        Real.rpow_nonneg hxm_nn _
      have hsum_nn :
          0 ≤ sol.m x * ‖fun j => sol.Du j x‖ ^ (h.α - 1)
              + sol.m x ^ (1 + h.β - h.β / h.α) + sol.m x := by
        have h1 : 0 ≤ sol.m x * ‖fun j => sol.Du j x‖ ^ (h.α - 1) :=
          mul_nonneg hxm_nn hα1nn
        linarith
      exact mul_nonneg h.hC.le hsum_nn
    have hB_nn : 0 ≤ B x := by
      rw [hB_def]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    show 0 ≤ Genv x
    rw [show Genv x = Kconst * A x * B x from rfl]
    exact mul_nonneg (mul_nonneg hKconst_nn hAx_nn) hB_nn

/-! ### Closed-form assembly of the rescaled-transport L¹ dominator

Per task `infra-P5-strongTransport-dominator-closed-assembly`. Combines
the three closed-form `_of_sol` envelope producers
(`strongTransportDominator_G_{scal,vec,mDpH}_of_sol`) with a Hölder
discharge for the `T₂`-slot `MemLpPer 1 (|m - 1| · |u|)` and feeds
them into `strongTransportPerturbedIntegrand_dominator`. -/

/-- **Closed-form `T₂`-slot Hölder discharge.**

For a `RegularizedBareSolution` whose paper-side exponents
`βBarReal = h.β + 1`, `γBarReal = h.α · (h.β + 1) / h.β` align with
the power-growth bundle `h`, the function `|m - 1| · |u|` lies in
`MemLpPer 1`. The proof uses Hölder with the conjugate pair
`(βBar, βBar') = (β + 1, (β + 1) / β)`: from
`sol.hmLp : MemLpPer βBar m` we get `MemLpPer βBar (m - 1)`, and from
`sol.huLp : MemLpPer γBar u` (with `γBar = α · βBar' ≥ βBar'` since
`α ≥ 1`) we descend to `MemLpPer βBar' u` via
`MemLpPer.mono_exponent_finite`. -/
private lemma strongTransportDominator_G_mu_of_sol
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (h : HypothesisPowerGrowth H DpH)
    (hβBarPaper : βBarReal = h.β + 1)
    (hγBarPaper : γBarReal = h.α * (h.β + 1) / h.β) :
    MemLpPer (d := d) 1
      (fun x => |sol.m x - 1| * |sol.u x|) := by
  -- Standing positivity from the bundle.
  have hβ_pos : 0 < h.β := h.hβ
  have hα_pos : 0 < h.α := lt_trans one_pos h.hα
  have hα_ge_one : 1 ≤ h.α := h.hα.le
  have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
  -- `βBar = h.β + 1` and `βBar' = (h.β + 1) / h.β`.
  let βBar : ℝ := h.β + 1
  let βBar' : ℝ := (h.β + 1) / h.β
  have hβBar_pos : 0 < βBar := by show 0 < h.β + 1; linarith
  have hβBar'_pos : 0 < βBar' := by
    show 0 < (h.β + 1) / h.β
    exact div_pos (by linarith) hβ_pos
  have hone_lt_βBar : 1 < βBar := by show 1 < h.β + 1; linarith
  -- Hölder identity `1/βBar + 1/βBar' = 1`.
  have hHolder_sum : βBar⁻¹ + βBar'⁻¹ = 1 := by
    show (h.β + 1)⁻¹ + ((h.β + 1) / h.β)⁻¹ = 1
    have h1 : h.β + 1 ≠ 0 := by linarith
    field_simp; ring
  -- `Real.HolderConjugate βBar βBar'`.
  have hHolder : Real.HolderConjugate βBar βBar' :=
    Real.holderConjugate_iff.mpr ⟨hone_lt_βBar, hHolder_sum⟩
  -- `βBar' ≤ γBarReal` (since `α ≥ 1`, `γBar = α · βBar'`).
  have hβBar'_le_γBar : βBar' ≤ γBarReal := by
    rw [hγBarPaper]
    show (h.β + 1) / h.β ≤ h.α * (h.β + 1) / h.β
    have hbb_nn : 0 ≤ (h.β + 1) / h.β := by
      exact (div_pos (by linarith) hβ_pos).le
    have hα1 : (h.β + 1) / h.β = 1 * ((h.β + 1) / h.β) := by ring
    have hα2 : h.α * (h.β + 1) / h.β = h.α * ((h.β + 1) / h.β) := by ring
    rw [hα1, hα2]
    exact mul_le_mul_of_nonneg_right hα_ge_one hbb_nn
  -- Finite-measure instance.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Step 1: `MemLpPer βBar (m - 1)`.
  have hmLp_paper : MemLpPer (d := d) (ENNReal.ofReal βBar) sol.m := by
    show MemLpPer (ENNReal.ofReal (h.β + 1)) sol.m
    rw [show ENNReal.ofReal (h.β + 1) = ENNReal.ofReal βBarReal from by
          rw [hβBarPaper]]
    exact sol.hmLp
  have hone_const_lp : MemLp (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (ENNReal.ofReal βBar) (Measure.restrict volume (UnitCube d)) :=
    memLp_const (1 : ℝ)
  have hmLp_mathlib : MemLp sol.m (ENNReal.ofReal βBar)
      (Measure.restrict volume (UnitCube d)) := hmLp_paper.toMemLp
  have hsub_mathlib : MemLp (sol.m - fun _ => (1 : ℝ))
      (ENNReal.ofReal βBar) (Measure.restrict volume (UnitCube d)) :=
    hmLp_mathlib.sub hone_const_lp
  have hsub : MemLpPer (d := d) (ENNReal.ofReal βBar)
      (fun x => sol.m x - 1) := by
    have h := MemLp.toMemLpPer (d := d) hsub_mathlib
    -- `(m - fun _ => 1) = fun x => m x - 1` definitionally.
    exact h
  -- Step 2: `MemLpPer βBar' u` via `mono_exponent_finite`.
  have huLp_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) sol.u :=
    sol.huLp
  have h_le_ofReal : ENNReal.ofReal βBar' ≤ ENNReal.ofReal γBarReal :=
    ENNReal.ofReal_le_ofReal hβBar'_le_γBar
  have h_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have huLp_β' : MemLpPer (d := d) (ENNReal.ofReal βBar') sol.u :=
    MemLpPer.mono_exponent_finite h_le_ofReal h_top huLp_γ
  -- Step 3: Hölder integrability of `(m - 1) * u`.
  have hInt_prod : IntegrableOn
      (fun x => (sol.m x - 1) * sol.u x) (UnitCube d) :=
    MemLpPer.integrable_mul (d := d) hHolder hsub huLp_β'
  -- Step 4: Take absolute values.
  have hInt_abs : Integrable
      (fun x => |(sol.m x - 1) * sol.u x|)
      (Measure.restrict volume (UnitCube d)) := hInt_prod.abs
  have hInt_split : Integrable
      (fun x => |sol.m x - 1| * |sol.u x|)
      (Measure.restrict volume (UnitCube d)) := by
    refine hInt_abs.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    show |(sol.m x - 1) * sol.u x| = |sol.m x - 1| * |sol.u x|
    exact abs_mul _ _
  -- Step 5: lift to `MemLpPer 1`.
  exact MemLp.toMemLpPer (memLp_one_iff_integrable.mpr hInt_split)

/-! ### Generic absorption helper and unified `hI_A` integrability

Per task `paperSolFor-final-phase4-aux-hI-A` (2026-05-17 expert plan).
Provides a thin "abs-le `MemLpPer 1` dominator ⇒ `IntegrableOn`"
wrapper and the unified `T₁ + T₂` integrability at parametric
`s ∈ [-1, 1] \ {0}`. The pos/neg specializations consumed by the
side-input constructor (`s = ±1/(n+1)`) follow byte-for-byte. -/

/-- **Generic dominated-`IntegrableOn` from a real `MemLpPer 1`
dominator.** If `|f x| ≤ G x` a.e. and `G ∈ MemLpPer 1`, then `f` is
integrable on the unit cube. -/
lemma integrableOn_of_abs_le_memLpPer_one
    {f G : (Fin d → ℝ) → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hG : MemLpPer (d := d) 1 G)
    (hbound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |f x| ≤ G x) :
    MeasureTheory.IntegrableOn f (UnitCube d) MeasureTheory.volume := by
  -- `G` is integrable on the cube (`MemLpPer 1` ↔ integrable).
  have hG_int : MeasureTheory.Integrable G
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    memLp_one_iff_integrable.mp hG
  -- `‖f x‖ = |f x|` for real-valued `f`.
  have hbound_norm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖f x‖ ≤ G x := by
    refine hbound.mono (fun x hx => ?_)
    rw [Real.norm_eq_abs]; exact hx
  -- Apply `Integrable.mono'`.
  exact hG_int.mono' hf hbound_norm

/-- **Unified `T₁ + T₂` integrability of the perturbed transport
integrand summand.**

For a `RegularizedBareSolution` with paper-aligned exponents and any
`s ∈ [-1, 1] \ {0}`, the summand

```
T₁ + T₂ := m · (DpH(x, (1+s)·Du, m) ⬝ (s·Du))
            + (m - 1) · (s · u)
```

is integrable on the unit cube. Specializing at `s = ±1/(n+1)` yields
the `hI_A_pos` / `hI_A_neg` shapes consumed by
`strongTransport_at_uEpsi_perturbed`.

The proof reuses the closed-form `MemLpPer 1` envelopes
`strongTransportDominator_G_{mDpH,mu}_of_sol` (which bound the
`s`-rescaled `T₁ / s` and `T₂ / s` slots), then absorbs the outer
factor of `s` via `integrableOn_of_abs_le_memLpPer_one`. -/
theorem strongTransport_hI_A_of_sol
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hRegH : RegularityH (d := d) H DpH)
    (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) (hs0 : s ≠ 0) :
    MeasureTheory.IntegrableOn
      (fun x =>
        sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
          ⬝ (fun i => s * sol.Du i x))
        + (sol.m x - 1) * (s * sol.u x))
      (UnitCube d) MeasureTheory.volume := by
  -- Pull out the two closed-form `MemLpPer 1` envelopes.
  obtain ⟨G_mDpH, hG_mDpH, h_mDpH_pt⟩ :=
    strongTransportDominator_G_mDpH_of_sol sol hpow hβBarPaper hγBarPaper
  have hG_mu : MemLpPer (d := d) 1
      (fun x => |sol.m x - 1| * |sol.u x|) :=
    strongTransportDominator_G_mu_of_sol sol hpow hβBarPaper hγBarPaper
  -- Absolute-value of `s`.
  set absS : ℝ := |s| with habsS_def
  have habsS_nn : 0 ≤ absS := abs_nonneg _
  -- ===== Integrability of T₁ =====
  -- Pointwise: `|T₁| = |s| · |T₁ / s| ≤ |s| · G_mDpH x` a.e.
  set T1 : (Fin d → ℝ) → ℝ :=
    fun x => sol.m x *
      (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
        ⬝ (fun i => s * sol.Du i x)) with hT1_def
  -- `|s| • G_mDpH ∈ MemLpPer 1`.
  have hG1_scaled : MemLpPer (d := d) 1 (absS • G_mDpH) :=
    hG_mDpH.const_smul (𝕜 := ℝ) absS
  -- A.e. strong measurability of T₁. We assemble it via AEMeasurable
  -- on each slot then convert at the end.
  have hm_am : AEMeasurable sol.m
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    sol.hmLp.aestronglyMeasurable.aemeasurable
  have hu_am : AEMeasurable sol.u
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    sol.huLp.aestronglyMeasurable.aemeasurable
  have hDu_am : ∀ i, AEMeasurable (sol.Du i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (sol.hDuLp i).aestronglyMeasurable.aemeasurable
  -- Shifted gradient component.
  have hDuShift_am : ∀ i,
      AEMeasurable (fun x => sol.Du i x + s * sol.Du i x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDu_am i).add ((hDu_am i).const_mul s)
  have hDuShift_pi : AEMeasurable
      (fun x => (fun i : Fin d => sol.Du i x + s * sol.Du i x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr hDuShift_am
  have hsDu_am : ∀ i,
      AEMeasurable (fun x => s * sol.Du i x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDu_am i).const_mul s
  -- `DpH x ((1+s)·Du x) (m x)` via the joint measurability bundle.
  have hxpm_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => sol.Du i x + s * sol.Du i x), sol.m x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_id'.prodMk (hDuShift_pi.prodMk hm_am)
  have hDpHcomp_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hRegH.measurable_DpH.comp_aemeasurable hxpm_am
  have hDpHcomp_i_am : ∀ i, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x) i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (measurable_pi_apply i).comp_aemeasurable hDpHcomp_am
  have hdot_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
          ⬝ (fun i => s * sol.Du i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have h_eq :
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
            ⬝ (fun i => s * sol.Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x) i
                  * (s * sol.Du i x)) := by
      funext x; rfl
    rw [h_eq]
    refine Finset.aemeasurable_fun_sum _ (fun i _ => ?_)
    exact (hDpHcomp_i_am i).mul (hsDu_am i)
  have hT1_am : AEMeasurable T1
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    simp only [hT1_def]
    exact hm_am.mul hdot_am
  have hT1_aesm : MeasureTheory.AEStronglyMeasurable T1
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hT1_am.aestronglyMeasurable
  -- Pointwise bound for `T₁`: `|T₁ x| ≤ |s| · G_mDpH x` a.e.
  have hT1_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        |T1 x| ≤ (absS • G_mDpH) x := by
    have hpt := h_mDpH_pt s hs hs0
    refine hpt.mono (fun x hx => ?_)
    -- `|T1 x / s| ≤ G_mDpH x` ⇒ `|T1 x| = |s| * |T1 x / s| ≤ |s| * G_mDpH x`.
    have habs_div : |T1 x / s| = |T1 x| / |s| := by
      rw [abs_div]
    rw [habs_div] at hx
    have habs_s_pos : 0 < |s| := abs_pos.mpr hs0
    have hmul := mul_le_mul_of_nonneg_left hx habs_s_pos.le
    have h_left : |s| * (|T1 x| / |s|) = |T1 x| := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ habs_s_pos.ne'
    rw [h_left] at hmul
    show |T1 x| ≤ absS * G_mDpH x
    rw [habsS_def]
    exact hmul
  have hT1_int : MeasureTheory.IntegrableOn T1 (UnitCube d)
      MeasureTheory.volume :=
    integrableOn_of_abs_le_memLpPer_one hT1_aesm hG1_scaled hT1_bound
  -- ===== Integrability of T₂ =====
  set T2 : (Fin d → ℝ) → ℝ :=
    fun x => (sol.m x - 1) * (s * sol.u x) with hT2_def
  -- `|s| • (|m - 1| · |u|) ∈ MemLpPer 1`.
  have hG2_scaled : MemLpPer (d := d) 1
      (absS • (fun x => |sol.m x - 1| * |sol.u x|)) :=
    hG_mu.const_smul (𝕜 := ℝ) absS
  have hT2_aesm : MeasureTheory.AEStronglyMeasurable T2
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    simp only [hT2_def]
    have hT2_am : AEMeasurable T2
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      simp only [hT2_def]
      exact (hm_am.sub_const 1).mul (hu_am.const_mul s)
    exact hT2_am.aestronglyMeasurable
  have hT2_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        |T2 x| ≤ (absS • (fun x => |sol.m x - 1| * |sol.u x|)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    -- `|T2 x| = |m - 1| * |s| * |u| = |s| * (|m - 1| * |u|)`.
    show |(sol.m x - 1) * (s * sol.u x)|
          ≤ absS * (|sol.m x - 1| * |sol.u x|)
    rw [abs_mul, abs_mul, habsS_def]
    ring_nf
    -- Goal is now `|m x - 1| * (|s| * |u x|) ≤ |s| * (|m x - 1| * |u x|)`
    -- after ring_nf; both sides are equal up to associativity/commutativity.
    rfl
  have hT2_int : MeasureTheory.IntegrableOn T2 (UnitCube d)
      MeasureTheory.volume :=
    integrableOn_of_abs_le_memLpPer_one hT2_aesm hG2_scaled hT2_bound
  -- ===== Sum =====
  exact hT1_int.add hT2_int

/-! ### Unified `T₃ + T₄` integrability of the perturbed regularization summand

Per task `paperSolFor-final-phase4-aux-hI-B` (2026-05-17 expert refinement).
Mirrors the `hI_A` approach (the previous declaration) for the pure
regularization summand. The pos/neg specializations consumed by the
side-input constructor (`s = ±1/(n+1)`) follow byte-for-byte. -/

/-- **Unified `T₃ + T₄` integrability of the perturbed regularization
summand.**

For a `RegularizedBareSolution` with `1 ≤ γ̄`, `ε ≠ 0`, and any
`s ∈ [-1, 1] \ {0}`, the summand

```
T₃ + T₄ := vecAbsPowMinusTwo γ̄ ((1+s)·Du) · ((1+s)·Du ⬝ (s·Du))
            + absPowMinusTwo γ̄ ((1+s)·u) · ((1+s)·u · (s·u))
```

is integrable on the unit cube. Specializing at `s = ±1/(n+1)` yields
the `hI_B_pos` / `hI_B_neg` shapes consumed by
`strongTransport_at_uEpsi_perturbed`.

The proof reuses the closed-form `MemLpPer 1` envelopes
`strongTransportDominator_G_{vec,scal}_of_sol` (which bound the
`s`-rescaled `ε · T₃ / s` and `ε · T₄ / s` slots), then absorbs the
outer `ε / s` factor by multiplying both sides by `|s| / |ε|` (both
nonzero by `hs0`, `hε`). -/
theorem strongTransport_hI_B_of_sol
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hγ : 1 ≤ γBarReal)
    (hε : ε ≠ 0)
    (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) (hs0 : s ≠ 0) :
    MeasureTheory.IntegrableOn
      (fun x =>
        StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo γBarReal
          (fun i => sol.Du i x + s * sol.Du i x)
          * ((fun i => sol.Du i x + s * sol.Du i x)
              ⬝ (fun i => s * sol.Du i x))
        + StationaryMFG.Solutions.MFG.absPowMinusTwo γBarReal
            (sol.u x + s * sol.u x)
          * ((sol.u x + s * sol.u x) * (s * sol.u x)))
      (UnitCube d) MeasureTheory.volume := by
  -- Pull out the two closed-form `MemLpPer 1` envelopes.
  obtain ⟨G_vec, hG_vec, h_vec_pt⟩ :=
    strongTransportDominator_G_vec_of_sol hγ sol
  obtain ⟨G_scal, hG_scal, h_scal_pt⟩ :=
    strongTransportDominator_G_scal_of_sol hγ sol
  -- Scaling constant `c := |s| / |ε|` (both nonzero ⇒ `c ≥ 0`).
  set c : ℝ := |s| / |ε| with hc_def
  have habsS_pos : 0 < |s| := abs_pos.mpr hs0
  have habsE_pos : 0 < |ε| := abs_pos.mpr hε
  have hc_nn : 0 ≤ c := by
    rw [hc_def]; exact div_nonneg habsS_pos.le habsE_pos.le
  -- AE-strong measurability of the basic slots.
  have hm_am : AEMeasurable sol.m
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    sol.hmLp.aestronglyMeasurable.aemeasurable
  have hu_am : AEMeasurable sol.u
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    sol.huLp.aestronglyMeasurable.aemeasurable
  have hDu_am : ∀ i, AEMeasurable (sol.Du i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (sol.hDuLp i).aestronglyMeasurable.aemeasurable
  -- Shifted gradient component `Du i + s · Du i`.
  have hDuShift_am : ∀ i,
      AEMeasurable (fun x => sol.Du i x + s * sol.Du i x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDu_am i).add ((hDu_am i).const_mul s)
  have hsDu_am : ∀ i,
      AEMeasurable (fun x => s * sol.Du i x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDu_am i).const_mul s
  -- Self-dot of the shifted gradient.
  have hDot_self_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i => sol.Du i x + s * sol.Du i x)
          ⬝ (fun i => sol.Du i x + s * sol.Du i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have h_eq :
        (fun x : (Fin d → ℝ) =>
          (fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => sol.Du i x + s * sol.Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                (sol.Du i x + s * sol.Du i x)
                  * (sol.Du i x + s * sol.Du i x)) := by
      funext x; rfl
    rw [h_eq]
    refine Finset.aemeasurable_fun_sum _ (fun i _ => ?_)
    exact (hDuShift_am i).mul (hDuShift_am i)
  -- `vecAbsPowMinusTwo γ̄ ((1+s)·Du)` is AEMeasurable.
  have hVec_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo γBarReal
          (fun i => sol.Du i x + s * sol.Du i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    change AEMeasurable
      (fun x : (Fin d → ℝ) =>
        ((fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => sol.Du i x + s * sol.Du i x))
          ^ ((γBarReal - 2) / 2))
      _
    exact hDot_self_am.pow_const _
  -- Mixed dot `(1+s)·Du ⬝ s·Du`.
  have hDot_mix_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i => sol.Du i x + s * sol.Du i x)
          ⬝ (fun i => s * sol.Du i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have h_eq :
        (fun x : (Fin d → ℝ) =>
          (fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => s * sol.Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                (sol.Du i x + s * sol.Du i x) * (s * sol.Du i x)) := by
      funext x; rfl
    rw [h_eq]
    refine Finset.aemeasurable_fun_sum _ (fun i _ => ?_)
    exact (hDuShift_am i).mul (hsDu_am i)
  -- ===== Integrability of T₃ =====
  set T3 : (Fin d → ℝ) → ℝ :=
    fun x =>
      StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo γBarReal
        (fun i => sol.Du i x + s * sol.Du i x)
        * ((fun i => sol.Du i x + s * sol.Du i x)
            ⬝ (fun i => s * sol.Du i x))
    with hT3_def
  have hT3_am : AEMeasurable T3
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    simp only [hT3_def]
    exact hVec_am.mul hDot_mix_am
  have hT3_aesm : MeasureTheory.AEStronglyMeasurable T3
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hT3_am.aestronglyMeasurable
  -- `c • G_vec ∈ MemLpPer 1`.
  have hG3_scaled : MemLpPer (d := d) 1 (c • G_vec) :=
    hG_vec.const_smul (𝕜 := ℝ) c
  -- Pointwise bound: `|ε · T₃ / s| ≤ G_vec x` ⇒ `|T₃| ≤ c · G_vec x`.
  have hT3_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        |T3 x| ≤ (c • G_vec) x := by
    have hpt := h_vec_pt s hs hs0
    refine hpt.mono (fun x hx => ?_)
    -- `hx : |ε · T₃ x / s| ≤ G_vec x`. We have
    -- `|ε · T₃ x / s| = (|ε| / |s|) · |T₃ x|`.
    have habs_div :
        |ε * T3 x / s| = (|ε| / |s|) * |T3 x| := by
      rw [show ε * T3 x / s = (ε / s) * T3 x by ring]
      rw [abs_mul, abs_div]
    rw [habs_div] at hx
    -- Multiply both sides by `|s| / |ε| = c ≥ 0`.
    have hmul := mul_le_mul_of_nonneg_left hx hc_nn
    -- Simplify LHS: `c · ((|ε| / |s|) · |T₃|) = |T₃|`.
    have h_left : c * ((|ε| / |s|) * |T3 x|) = |T3 x| := by
      rw [hc_def]
      field_simp
    rw [h_left] at hmul
    show |T3 x| ≤ c * G_vec x
    exact hmul
  have hT3_int : MeasureTheory.IntegrableOn T3 (UnitCube d)
      MeasureTheory.volume :=
    integrableOn_of_abs_le_memLpPer_one hT3_aesm hG3_scaled hT3_bound
  -- ===== Integrability of T₄ =====
  -- Shifted scalar `u + s · u`.
  have huShift_am : AEMeasurable
      (fun x => sol.u x + s * sol.u x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hu_am.add (hu_am.const_mul s)
  have huShift_abs_am : AEMeasurable
      (fun x => |sol.u x + s * sol.u x|)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.abs.comp_aemeasurable huShift_am
  have hAbsPow_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        StationaryMFG.Solutions.MFG.absPowMinusTwo γBarReal
          (sol.u x + s * sol.u x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    change AEMeasurable
      (fun x : (Fin d → ℝ) =>
        |sol.u x + s * sol.u x| ^ (γBarReal - 2))
      _
    exact huShift_abs_am.pow_const _
  have hUmul_am : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (sol.u x + s * sol.u x) * (s * sol.u x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    huShift_am.mul (hu_am.const_mul s)
  set T4 : (Fin d → ℝ) → ℝ :=
    fun x =>
      StationaryMFG.Solutions.MFG.absPowMinusTwo γBarReal
        (sol.u x + s * sol.u x)
        * ((sol.u x + s * sol.u x) * (s * sol.u x))
    with hT4_def
  have hT4_am : AEMeasurable T4
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    simp only [hT4_def]
    exact hAbsPow_am.mul hUmul_am
  have hT4_aesm : MeasureTheory.AEStronglyMeasurable T4
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hT4_am.aestronglyMeasurable
  -- `c • G_scal ∈ MemLpPer 1`.
  have hG4_scaled : MemLpPer (d := d) 1 (c • G_scal) :=
    hG_scal.const_smul (𝕜 := ℝ) c
  -- Pointwise bound: `|ε · T₄ / s| ≤ G_scal x` ⇒ `|T₄| ≤ c · G_scal x`.
  have hT4_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        |T4 x| ≤ (c • G_scal) x := by
    have hpt := h_scal_pt s hs hs0
    refine hpt.mono (fun x hx => ?_)
    have habs_div :
        |ε * T4 x / s| = (|ε| / |s|) * |T4 x| := by
      rw [show ε * T4 x / s = (ε / s) * T4 x by ring]
      rw [abs_mul, abs_div]
    rw [habs_div] at hx
    have hmul := mul_le_mul_of_nonneg_left hx hc_nn
    have h_left : c * ((|ε| / |s|) * |T4 x|) = |T4 x| := by
      rw [hc_def]
      field_simp
    rw [h_left] at hmul
    show |T4 x| ≤ c * G_scal x
    exact hmul
  have hT4_int : MeasureTheory.IntegrableOn T4 (UnitCube d)
      MeasureTheory.volume :=
    integrableOn_of_abs_le_memLpPer_one hT4_aesm hG4_scaled hT4_bound
  -- ===== Sum =====
  exact hT3_int.add hT4_int

/-- **Closed-form `L¹` dominator for the rescaled perturbed transport
integrand.**

Combines the three closed-form envelope producers
(`strongTransportDominator_G_{scal,vec,mDpH}_of_sol`) with the Hölder
discharge `strongTransportDominator_G_mu_of_sol` for the `T₂`-slot,
and feeds them into `strongTransportPerturbedIntegrand_dominator`. The
resulting `g` no longer carries any B-class envelope inputs — only the
`RegularizedBareSolution` `sol`, the power-growth bundle `h`, and the
paper-exponent identifications. -/
theorem strongTransportPerturbedIntegrand_dominator_closed
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (h : HypothesisPowerGrowth H DpH)
    (hβBarPaper : βBarReal = h.β + 1)
    (hγBarPaper : γBarReal = h.α * (h.β + 1) / h.β)
    (hγ : 1 ≤ γBarReal) :
    ∃ g : (Fin d → ℝ) → ℝ,
      MeasureTheory.IntegrableOn g (UnitCube d) volume ∧
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |strongTransportPerturbedIntegrand sol s x / s| ≤ g x := by
  obtain ⟨G_mDpH, hG_mDpH, h_mDpH_pt⟩ :=
    strongTransportDominator_G_mDpH_of_sol sol h hβBarPaper hγBarPaper
  obtain ⟨G_vec, hG_vec, h_vec_pt⟩ :=
    strongTransportDominator_G_vec_of_sol hγ sol
  obtain ⟨G_scal, hG_scal, h_scal_pt⟩ :=
    strongTransportDominator_G_scal_of_sol hγ sol
  have hG_mu : MemLpPer (d := d) 1
      (fun x => |sol.m x - 1| * |sol.u x|) :=
    strongTransportDominator_G_mu_of_sol sol h hβBarPaper hγBarPaper
  exact strongTransportPerturbedIntegrand_dominator sol
    G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
    G_scal hG_scal h_scal_pt

/-! ### Pointwise `s → 0` limit of the rescaled perturbed transport
integrand

Per task `infra-P5-strongTransport-perturbed-pointwise-tendsto`. The
limit drives the σ → 0 DCT discharge of the strong-transport bridge. -/

/-- **Pointwise `s → 0` limit (along `𝓝[≠] 0`) of the rescaled
perturbed transport integrand.**

For a fixed `x : Fin d → ℝ`, the rescaled integrand
`strongTransportPerturbedIntegrand sol s x / s` converges as `s → 0`
(through `s ≠ 0`) to `strongTransportTargetIntegrand sol x`,
provided:

* `H` and `DpH` are continuous in their `p`-slot at `(sol.m x)` — the
  paper-side analogue of `RegularityH.continuous_DpH_pm` evaluated at
  the point `(p, m) = (Du, sol.m x)`;
* `1 ≤ γBarReal` (so the `γ̄/2` and `γ̄` rpow exponents are
  nonnegative);
* `0 ≤ sol.u x` (so `|u|^γ̄ = u^γ̄` in `Real.rpow`, matching the
  target's literal shape).

The four summands of the perturbed integrand cancel the `s`-factor by
hand, so the limit is a composition of continuities at `s = 0`, not a
true `0/0` limit. -/
theorem strongTransportPerturbedIntegrand_pointwise_tendsto
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (x : Fin d → ℝ)
    (hDpH_cont_x : Continuous fun (p : Fin d → ℝ) =>
                        DpH x p (sol.m x))
    (hγ : 1 ≤ γBarReal) :
    Filter.Tendsto
      (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (strongTransportTargetIntegrand sol x)) := by
  -- Abbreviations.
  set m₀ : ℝ := sol.m x with hm₀_def
  set u₀ : ℝ := sol.u x with hu₀_def
  set Du₀ : Fin d → ℝ := fun i => sol.Du i x with hDu₀_def
  -- Nonnegativity of `Du₀ ⬝ Du₀`.
  have hDuDu_nn : 0 ≤ Du₀ ⬝ Du₀ := by
    unfold euclideanDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  -- Exponents are nonnegative.
  have hγ_half_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
  have hγ_nn : (0 : ℝ) ≤ γBarReal := by linarith
  -- The perturbed integrand divided by `s`, expanded into four
  -- summands that no longer involve `0/s` cancellations. We work on
  -- `s ≠ 0` and use the bilinearity `v ⬝ (s • w) = s · (v ⬝ w)`.
  -- For convenience, define the four "limit-side" rescaled summands
  -- as functions of `s`.
  -- f1 s = m₀ * (DpH x ((1+s)·Du₀) m₀ ⬝ Du₀)
  -- f2 s = (m₀ - 1) * u₀
  -- f3 s = ε * vecAbsPowMinusTwo γ̄ ((1+s)·Du₀) * (((1+s)·Du₀) ⬝ Du₀)
  -- f4 s = ε * absPowMinusTwo γ̄ ((1+s)·u₀) * (((1+s)·u₀) * u₀)
  let f1 : ℝ → ℝ := fun s =>
    m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀ ⬝ Du₀)
  let f2 : ℝ → ℝ := fun _ => (m₀ - 1) * u₀
  let f3 : ℝ → ℝ := fun s =>
    ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
          * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))
  let f4 : ℝ → ℝ := fun s =>
    ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
          * ((u₀ + s * u₀) * u₀))
  -- Step A. Rewrite the rescaled integrand as f1+f2+f3+f4 on `s ≠ 0`.
  have h_rewrite : ∀ s : ℝ, s ≠ 0 →
      strongTransportPerturbedIntegrand sol s x / s
        = f1 s + f2 s + (f3 s + f4 s) := by
    intro s hs
    -- Unfold the integrand.
    unfold strongTransportPerturbedIntegrand
    -- The integrand is A + B + C where:
    --   A = m * (DpH ⬝ (s·Du))
    --   B = (m - 1) * (s · u)
    --   C = ε * (vec part + scal part)
    -- We compute (A + B + C) / s = A/s + B/s + C/s.
    have hdotR : ∀ (V₁ : Fin d → ℝ),
        V₁ ⬝ (fun i => s * Du₀ i) = s * (V₁ ⬝ Du₀) := by
      intro V₁
      simp only [euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    -- Compute T1 / s.
    have hT1s :
        m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀
                ⬝ (fun i => s * Du₀ i)) / s
          = f1 s := by
      have h := hdotR (DpH x (fun i => Du₀ i + s * Du₀ i) m₀)
      change m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀
                ⬝ (fun i => s * Du₀ i)) / s
            = m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀ ⬝ Du₀)
      rw [h]
      -- Now: m₀ * (s * X) / s = m₀ * X.
      rw [show m₀ * (s * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀ ⬝ Du₀))
            = s * (m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀ ⬝ Du₀))
            from by ring]
      rw [mul_div_cancel_left₀ _ hs]
    -- Compute T2 / s.
    have hT2s : (m₀ - 1) * (s * u₀) / s = f2 s := by
      change (m₀ - 1) * (s * u₀) / s = (m₀ - 1) * u₀
      rw [mul_div_assoc, mul_div_cancel_left₀ _ hs]
    -- Compute T3 / s.
    have hT3s :
        ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i)
                  ⬝ (fun i => s * Du₀ i))) / s
          = f3 s := by
      have h := hdotR (fun i => Du₀ i + s * Du₀ i)
      change ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i)
                  ⬝ (fun i => s * Du₀ i))) / s
            = ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))
      rw [h]
      -- Now: ε * (V * (s * D)) / s = ε * (V * D).
      rw [show (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * (s * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀)))
            = s * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀)) from by ring]
      rw [show ε * (s * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀)))
            = s * (ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))) from by ring]
      rw [mul_div_cancel_left₀ _ hs]
    -- Compute T4 / s.
    have hT4s :
        ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀))) / s
          = f4 s := by
      change ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀))) / s
            = ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * u₀))
      rw [show ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀)))
            = s * (ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * u₀))) from by ring]
      rw [mul_div_cancel_left₀ _ hs]
    -- Combine.
    show (m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀
              ⬝ (fun i => s * Du₀ i))
        + (m₀ - 1) * (s * u₀)
        + ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
                * ((fun i => Du₀ i + s * Du₀ i)
                    ⬝ (fun i => s * Du₀ i))
              + absPowMinusTwo γBarReal (u₀ + s * u₀)
                * ((u₀ + s * u₀) * (s * u₀)))) / s
        = f1 s + f2 s + (f3 s + f4 s)
    have hT3T4 :
        ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i)
                  ⬝ (fun i => s * Du₀ i))
            + absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀))) / s
          = f3 s + f4 s := by
      have hsplit :
          ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
                * ((fun i => Du₀ i + s * Du₀ i)
                    ⬝ (fun i => s * Du₀ i))
              + absPowMinusTwo γBarReal (u₀ + s * u₀)
                * ((u₀ + s * u₀) * (s * u₀)))
            = ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
                * ((fun i => Du₀ i + s * Du₀ i)
                    ⬝ (fun i => s * Du₀ i)))
              + ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
                * ((u₀ + s * u₀) * (s * u₀))) := by ring
      rw [hsplit, add_div, hT3s, hT4s]
    rw [add_div, add_div, hT1s, hT2s, hT3T4]
  -- Step B. Establish the limits of f1, f2, f3, f4 at `s = 0`.
  -- The target equals f1 0 + f2 0 + (f3 0 + f4 0) by direct
  -- algebraic identities (modulo rpow simplifications).
  -- Limit of f1: continuity of `DpH(x, ·, m₀)` and `⬝ Du₀`.
  have hf1_cont : Continuous f1 := by
    -- s ↦ (1+s)·Du₀ is continuous.
    have h_arg : Continuous fun (s : ℝ) => (fun i => Du₀ i + s * Du₀ i) := by
      refine continuous_pi ?_
      intro i
      exact continuous_const.add
        (continuous_id.mul continuous_const)
    -- s ↦ DpH x ((1+s)·Du₀) m₀ continuous.
    have h_DpH : Continuous
        (fun s : ℝ => DpH x (fun i => Du₀ i + s * Du₀ i) m₀) :=
      hDpH_cont_x.comp h_arg
    -- s ↦ (DpH ⬝ Du₀) continuous.
    have h_dot : Continuous
        (fun s : ℝ => DpH x (fun i => Du₀ i + s * Du₀ i) m₀ ⬝ Du₀) := by
      unfold euclideanDot
      refine continuous_finset_sum _ ?_
      intro i _
      exact ((continuous_apply i).comp h_DpH).mul continuous_const
    exact continuous_const.mul h_dot
  -- f1 0 reduces to m₀ · (DpH x Du₀ m₀ ⬝ Du₀).
  have hf1_zero :
      f1 0 = m₀ * (DpH x Du₀ m₀ ⬝ Du₀) := by
    show m₀ * (DpH x (fun i => Du₀ i + 0 * Du₀ i) m₀ ⬝ Du₀)
          = m₀ * (DpH x Du₀ m₀ ⬝ Du₀)
    have heq : (fun i => Du₀ i + 0 * Du₀ i) = Du₀ := by
      funext i; ring
    rw [heq]
  -- f2 is constant.
  have hf2_cont : Continuous f2 := continuous_const
  have hf2_zero : f2 0 = (m₀ - 1) * u₀ := rfl
  -- For f3 and f4, the rpow exponents in absPowMinusTwo /
  -- vecAbsPowMinusTwo are `γ̄ - 2` and `(γ̄ - 2)/2`, which can be
  -- negative. We handle continuity at s = 0 by case-splitting on the
  -- base.

  -- Limit of f3 at 0: we want
  --   (vecAbsPowMinusTwo γ̄ Du₀) * (Du₀ ⬝ Du₀) = (Du₀ ⬝ Du₀)^(γ̄/2).
  have h_vec_id :
      vecAbsPowMinusTwo γBarReal Du₀ * (Du₀ ⬝ Du₀)
        = (Du₀ ⬝ Du₀) ^ (γBarReal / 2) := by
    unfold vecAbsPowMinusTwo
    rcases eq_or_lt_of_le hDuDu_nn with hzero | hpos
    · -- Du₀ ⬝ Du₀ = 0.
      rw [← hzero]
      have h1 : (0 : ℝ) ^ ((γBarReal - 2) / 2) * 0 = 0 := by ring
      rw [h1]
      have hexp_pos : (0 : ℝ) < γBarReal / 2 := by linarith
      rw [Real.zero_rpow hexp_pos.ne']
    · -- Du₀ ⬝ Du₀ > 0: use rpow_add.
      have h_add :
          (Du₀ ⬝ Du₀) ^ ((γBarReal - 2) / 2) * (Du₀ ⬝ Du₀)
            = (Du₀ ⬝ Du₀) ^ ((γBarReal - 2) / 2) * (Du₀ ⬝ Du₀) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      rw [h_add, ← Real.rpow_add hpos]
      congr 1
      ring
  -- f3 → ε * (Du₀ ⬝ Du₀)^(γ̄/2) as s → 0 (Tendsto at 0; not global
  -- continuity, since the rpow exponent (γ̄-2)/2 can be negative).
  have hf3_at : Filter.Tendsto f3 (𝓝 (0 : ℝ))
      (𝓝 (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2))) := by
    -- Use the rewrite f3 s = ε * (((1+s)² · A) ^ ((γ̄-2)/2) * ((1+s) · A)).
    have h_self_eq : ∀ s : ℝ,
        (fun i => Du₀ i + s * Du₀ i) ⬝ (fun i => Du₀ i + s * Du₀ i)
          = (1 + s) ^ 2 * (Du₀ ⬝ Du₀) := by
      intro s
      simp only [euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have h_dot_eq : ∀ s : ℝ,
        (fun i => Du₀ i + s * Du₀ i) ⬝ Du₀
          = (1 + s) * (Du₀ ⬝ Du₀) := by
      intro s
      simp only [euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have hf3_simp : f3 = fun s : ℝ => ε *
        (((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
          * ((1 + s) * (Du₀ ⬝ Du₀))) := by
      funext s
      show ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
            * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))
            = ε * (((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
                * ((1 + s) * (Du₀ ⬝ Du₀)))
      unfold vecAbsPowMinusTwo
      rw [h_self_eq s, h_dot_eq s]
    rw [hf3_simp]
    -- Target value rewrite.
    have htarget :
        ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
        = ε * (((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
              * ((1 + (0:ℝ)) * (Du₀ ⬝ Du₀))) := by
      have hone : (1 + (0:ℝ)) = 1 := by ring
      rw [hone]
      simp only [one_pow, one_mul]
      have hvec := h_vec_id
      unfold vecAbsPowMinusTwo at hvec
      rw [← hvec]
    rw [htarget]
    -- ContinuousAt at s = 0.
    apply Filter.Tendsto.const_mul
    -- s ↦ (1+s) continuous, value 1 at 0.
    have h_one_plus : Filter.Tendsto (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 1) := by
      have hcont : Continuous fun s : ℝ => 1 + s :=
        continuous_const.add continuous_id
      have ht := hcont.tendsto 0
      simpa using ht
    -- s ↦ (1+s)² continuous, value 1.
    have h_sq : Filter.Tendsto (fun s : ℝ => (1 + s) ^ 2) (𝓝 0) (𝓝 1) := by
      have h2 := h_one_plus.mul h_one_plus
      simpa [pow_two] using h2
    -- s ↦ (1+s)² · A continuous at 0, value (1+0)² · A = A.
    -- We keep the "non-simplified" target shape for downstream `comp`.
    have h_sqA : Filter.Tendsto
        (fun s : ℝ => (1 + s) ^ 2 * (Du₀ ⬝ Du₀))
        (𝓝 0) (𝓝 ((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀))) := by
      have h_one_plus_lin : Filter.Tendsto (fun s : ℝ => 1 + s)
          (𝓝 0) (𝓝 (1 + (0:ℝ))) :=
        ((continuous_const.add continuous_id).tendsto 0)
      have h_sq_lin : Filter.Tendsto (fun s : ℝ => (1 + s) ^ 2)
          (𝓝 0) (𝓝 ((1 + (0:ℝ)) ^ 2)) := by
        have hh := h_one_plus_lin.mul h_one_plus_lin
        simpa [pow_two] using hh
      exact h_sq_lin.mul (tendsto_const_nhds (x := (Du₀ ⬝ Du₀)))
    -- s ↦ ((1+s)² · A) ^ ((γ̄-2)/2) continuous at 0:
    --   when A = 0, the function is constantly 0 (handled below);
    --   when A > 0, the base is positive at s = 0 (= A > 0), so
    --   `Real.continuousAt_rpow_const` applies.
    rcases eq_or_lt_of_le hDuDu_nn with hAzero | hApos
    · -- A = 0: both sides are 0.
      have hfn :
          (fun s : ℝ =>
            ((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
            * ((1 + s) * (Du₀ ⬝ Du₀)))
          = fun _ => 0 := by
        funext s
        rw [← hAzero]
        ring
      have hgoal :
          ((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
            * ((1 + (0:ℝ)) * (Du₀ ⬝ Du₀)) = 0 := by
        rw [← hAzero]; ring
      rw [hfn, hgoal]
      exact tendsto_const_nhds
    · -- A > 0.
      -- The rpow exponent factor:
      have h_rpow : Filter.Tendsto
          (fun s : ℝ => ((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2))
          (𝓝 0)
          (𝓝 (((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2))) := by
        have hbase_pos : 0 < (1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀) := by
          have h1 : (1 + (0:ℝ)) ^ 2 = 1 := by ring
          rw [h1]; simpa using hApos
        have hcont :=
          Real.continuousAt_rpow_const ((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀))
            ((γBarReal - 2) / 2) (Or.inl hbase_pos.ne')
        exact hcont.tendsto.comp h_sqA
      -- The linear factor:
      have h_lin : Filter.Tendsto
          (fun s : ℝ => (1 + s) * (Du₀ ⬝ Du₀))
          (𝓝 0)
          (𝓝 ((1 + (0:ℝ)) * (Du₀ ⬝ Du₀))) := by
        have h_one_plus_lin : Filter.Tendsto (fun s : ℝ => 1 + s)
            (𝓝 0) (𝓝 (1 + (0:ℝ))) :=
          ((continuous_const.add continuous_id).tendsto 0)
        exact h_one_plus_lin.mul (tendsto_const_nhds (x := (Du₀ ⬝ Du₀)))
      exact h_rpow.mul h_lin
  -- f4 limit similarly. Now targets `|u|^γ̄` (paper-faithful), valid
  -- for any sign of `u₀` — `|u|^(γ̄-2) · u² = |u|^(γ̄-2) · |u|² = |u|^γ̄`.
  have h_scal_id :
      absPowMinusTwo γBarReal u₀ * (u₀ * u₀) = |u₀| ^ γBarReal := by
    unfold absPowMinusTwo
    by_cases hzero : u₀ = 0
    · -- u = 0.
      rw [hzero]
      have h0 : |(0:ℝ)| ^ (γBarReal - 2) * (0 * 0) = 0 := by
        rw [abs_zero]; ring
      rw [h0, abs_zero]
      have hexp_pos : (0 : ℝ) < γBarReal := by linarith
      rw [Real.zero_rpow hexp_pos.ne']
    · -- u ≠ 0, so |u| > 0.
      have hu_abs_pos : 0 < |u₀| := abs_pos.mpr hzero
      have h_uu : u₀ * u₀ = |u₀| ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
        rw [Real.rpow_natCast]
        rw [show |u₀| ^ (2 : ℕ) = |u₀| * |u₀| from by ring]
        rw [← abs_mul, abs_mul_self]
      rw [h_uu]
      rw [← Real.rpow_add hu_abs_pos]
      have hexp : γBarReal - 2 + 2 = γBarReal := by ring
      rw [hexp]
  have hf4_at : Filter.Tendsto f4 (𝓝 (0 : ℝ))
      (𝓝 (ε * |u₀| ^ γBarReal)) := by
    -- Rewrite f4 s = ε * |1+s|^(γ̄-2) · |u₀|^(γ̄-2) · ((1+s)·u₀ * u₀)
    --              = ε * |1+s|^(γ̄-2) · (1+s) · |u₀|^(γ̄-2) · u₀²
    -- Use absPowMinusTwo expansion.
    have hf4_simp : ∀ s : ℝ,
        f4 s
          = ε * (|1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
                * ((1 + s) * (u₀ * u₀))) := by
      intro s
      show ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * u₀))
          = ε * (|1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
                * ((1 + s) * (u₀ * u₀)))
      unfold absPowMinusTwo
      have hfact : u₀ + s * u₀ = (1 + s) * u₀ := by ring
      rw [hfact]
      rw [abs_mul]
      have habs_pow :
          (|1 + s| * |u₀|) ^ (γBarReal - 2)
            = |1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2) :=
        Real.mul_rpow (abs_nonneg _) (abs_nonneg _)
      rw [habs_pow]
      ring
    have hf4_eq : f4 = fun s : ℝ =>
        ε * (|1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
              * ((1 + s) * (u₀ * u₀))) := by
      funext s; exact hf4_simp s
    rw [hf4_eq]
    -- Target: ε * |u₀|^γ̄ = ε * (|1+0|^(γ̄-2) * |u₀|^(γ̄-2) * ((1+0)·(u₀ * u₀))).
    have htarget :
        ε * |u₀| ^ γBarReal
          = ε * (|1 + (0:ℝ)| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
              * ((1 + (0:ℝ)) * (u₀ * u₀))) := by
      have h1 : (1 + (0:ℝ)) = 1 := by ring
      rw [h1, abs_one, Real.one_rpow, one_mul, one_mul]
      have hsc := h_scal_id
      unfold absPowMinusTwo at hsc
      rw [← hsc]
    rw [htarget]
    apply Filter.Tendsto.const_mul
    -- s ↦ |1+s|^(γ̄-2): use rpow continuity at base 1 ≠ 0.
    have h_abs_one_plus : Filter.Tendsto
        (fun s : ℝ => |1 + s|)
        (𝓝 0) (𝓝 (|1 + (0:ℝ)|)) := by
      have hcont : Continuous fun s : ℝ => |1 + s| :=
        (continuous_const.add continuous_id).abs
      exact hcont.tendsto 0
    have h_one_plus_lin : Filter.Tendsto
        (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 (1 + (0:ℝ))) :=
      ((continuous_const.add continuous_id).tendsto 0)
    -- Continuity of `· ^ (γ̄-2)` at base 1.
    have hbase_pos : (0 : ℝ) < |1 + (0:ℝ)| := by
      rw [show (1 + (0:ℝ)) = 1 by ring, abs_one]
      exact zero_lt_one
    have h_rpow : Filter.Tendsto
        (fun s : ℝ => |1 + s| ^ (γBarReal - 2))
        (𝓝 0) (𝓝 (|1 + (0:ℝ)| ^ (γBarReal - 2))) := by
      have hcont :=
        Real.continuousAt_rpow_const (|1 + (0:ℝ)|) (γBarReal - 2)
          (Or.inl hbase_pos.ne')
      exact hcont.tendsto.comp h_abs_one_plus
    -- The abs |u₀|^(γ̄-2) factor is constant in s.
    have h_uconst : Filter.Tendsto
        (fun _ : ℝ => |u₀| ^ (γBarReal - 2))
        (𝓝 0) (𝓝 (|u₀| ^ (γBarReal - 2))) :=
      tendsto_const_nhds
    -- Linear factor (1+s) · (u₀ · u₀).
    have h_lin : Filter.Tendsto
        (fun s : ℝ => (1 + s) * (u₀ * u₀))
        (𝓝 0) (𝓝 ((1 + (0:ℝ)) * (u₀ * u₀))) :=
      h_one_plus_lin.mul tendsto_const_nhds
    -- Combine: rpow * uconst * lin.
    have h12 : Filter.Tendsto
        (fun s : ℝ => |1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2))
        (𝓝 0) (𝓝 (|1 + (0:ℝ)| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2))) :=
      h_rpow.mul h_uconst
    exact h12.mul h_lin
  -- Step C. Combine the four limits along `𝓝[≠] 0`.
  -- f1, f2 are continuous, so their `Tendsto` is automatic.
  have hf1_at : Filter.Tendsto f1 (𝓝 (0 : ℝ))
      (𝓝 (m₀ * (DpH x Du₀ m₀ ⬝ Du₀))) := by
    have h := hf1_cont.tendsto 0
    rw [hf1_zero] at h
    exact h
  have hf2_at : Filter.Tendsto f2 (𝓝 (0 : ℝ))
      (𝓝 ((m₀ - 1) * u₀)) := by
    have h := hf2_cont.tendsto 0
    rw [hf2_zero] at h
    exact h
  -- Sum the four.
  have hsum_at : Filter.Tendsto
      (fun s : ℝ => f1 s + f2 s + (f3 s + f4 s)) (𝓝 (0 : ℝ))
      (𝓝 (m₀ * (DpH x Du₀ m₀ ⬝ Du₀)
            + (m₀ - 1) * u₀
            + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
                + ε * |u₀| ^ γBarReal))) :=
    (hf1_at.add hf2_at).add (hf3_at.add hf4_at)
  -- Shift to `𝓝[≠] 0` and apply the rewrite.
  have hsum_at' : Filter.Tendsto
      (fun s : ℝ => f1 s + f2 s + (f3 s + f4 s)) (𝓝[≠] (0 : ℝ))
      (𝓝 (m₀ * (DpH x Du₀ m₀ ⬝ Du₀)
            + (m₀ - 1) * u₀
            + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
                + ε * |u₀| ^ γBarReal))) :=
    hsum_at.mono_left nhdsWithin_le_nhds
  -- Express the target value to match.
  have htarget_eq :
      strongTransportTargetIntegrand sol x
        = m₀ * (DpH x Du₀ m₀ ⬝ Du₀)
          + (m₀ - 1) * u₀
          + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
              + ε * |u₀| ^ γBarReal) := by
    show sol.m x * (DpH x (fun i => sol.Du i x) (sol.m x)
              ⬝ (fun i => sol.Du i x))
        + (sol.m x - 1) * sol.u x
        + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (γBarReal / 2)
        + ε * |sol.u x| ^ γBarReal
        = m₀ * (DpH x Du₀ m₀ ⬝ Du₀)
          + (m₀ - 1) * u₀
          + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
              + ε * |u₀| ^ γBarReal)
    ring
  rw [htarget_eq]
  -- Replace the integrand by the f1+f2+f3+f4 sum on `𝓝[≠] 0` via
  -- `Tendsto.congr'`.
  apply Filter.Tendsto.congr' (f₁ := fun s => f1 s + f2 s + (f3 s + f4 s))
  · -- Eventually equal on `𝓝[≠] 0`.
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{s : ℝ | s ≠ 0}, ?_, ?_⟩
    · exact self_mem_nhdsWithin
    · intro s hs
      exact (h_rewrite s hs).symm
  · exact hsum_at'

/-- **Pointwise `s → 0` limit when `sol.m x = 0` (no DpH continuity
required).**

When `sol.m x = 0`, the `m · DpH` summand of the perturbed integrand
vanishes identically in `s`, so the `s → 0` limit reduces to the
combined limit of the three remaining summands (`(m-1)·s·u`, `ε·…
vec…`, `ε·…|u|…`). Neither summand depends on `DpH`, so this
discharge holds **without** any continuity hypothesis on `DpH`.

This is the m=0 branch of
`strongTransportPerturbedIntegrand_pointwise_tendsto_of_powerGrowth`. -/
theorem strongTransportPerturbedIntegrand_pointwise_tendsto_at_m_zero
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (x : Fin d → ℝ)
    (hm_zero : sol.m x = 0)
    (hγ : 1 ≤ γBarReal) :
    Filter.Tendsto
      (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (strongTransportTargetIntegrand sol x)) := by
  -- Mirror the structure of `_pointwise_tendsto`, but the m-DpH summand
  -- vanishes identically since `m₀ = 0`.
  set m₀ : ℝ := sol.m x with hm₀_def
  set u₀ : ℝ := sol.u x with hu₀_def
  set Du₀ : Fin d → ℝ := fun i => sol.Du i x with hDu₀_def
  have hDuDu_nn : 0 ≤ Du₀ ⬝ Du₀ := by
    unfold euclideanDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hγ_half_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
  have hγ_nn : (0 : ℝ) ≤ γBarReal := by linarith
  -- f234: the integrand minus the m-DpH summand, divided by s.
  -- When m₀ = 0, the m-DpH summand is 0 = m₀ * (DpH ⬝ s·Du), so the
  -- integrand equals (m₀-1)·s·u + ε·(vec+scal).
  let f2 : ℝ → ℝ := fun _ => (m₀ - 1) * u₀
  let f3 : ℝ → ℝ := fun s =>
    ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
          * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))
  let f4 : ℝ → ℝ := fun s =>
    ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
          * ((u₀ + s * u₀) * u₀))
  -- Step A: when `m₀ = 0`, the m-DpH summand is identically 0, so
  -- `Iperturb/s = f2 + (f3 + f4)` on `s ≠ 0`.
  have hdotR : ∀ (V₁ : Fin d → ℝ) (s : ℝ),
      V₁ ⬝ (fun i => s * Du₀ i) = s * (V₁ ⬝ Du₀) := by
    intro V₁ s
    simp only [euclideanDot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have h_rewrite : ∀ s : ℝ, s ≠ 0 →
      strongTransportPerturbedIntegrand sol s x / s
        = f2 s + (f3 s + f4 s) := by
    intro s hs
    unfold strongTransportPerturbedIntegrand
    -- T1 = m₀ * (DpH ⬝ s·Du); m₀ = 0 makes T1 = 0.
    have hT1zero :
        m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀
                ⬝ (fun i => s * Du₀ i)) = 0 := by
      rw [show m₀ = (0:ℝ) from hm_zero, zero_mul]
    -- T2 / s.
    have hT2s : (m₀ - 1) * (s * u₀) / s = f2 s := by
      change (m₀ - 1) * (s * u₀) / s = (m₀ - 1) * u₀
      rw [mul_div_assoc, mul_div_cancel_left₀ _ hs]
    -- T3 / s.
    have hT3s :
        ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i)
                  ⬝ (fun i => s * Du₀ i))) / s
          = f3 s := by
      have h := hdotR (fun i => Du₀ i + s * Du₀ i) s
      change ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i)
                  ⬝ (fun i => s * Du₀ i))) / s
            = ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))
      rw [h]
      rw [show (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * (s * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀)))
            = s * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀)) from by ring]
      rw [show ε * (s * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀)))
            = s * (ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))) from by ring]
      rw [mul_div_cancel_left₀ _ hs]
    have hT4s :
        ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀))) / s
          = f4 s := by
      change ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀))) / s
            = ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * u₀))
      rw [show ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀)))
            = s * (ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * u₀))) from by ring]
      rw [mul_div_cancel_left₀ _ hs]
    show (m₀ * (DpH x (fun i => Du₀ i + s * Du₀ i) m₀
              ⬝ (fun i => s * Du₀ i))
        + (m₀ - 1) * (s * u₀)
        + ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
                * ((fun i => Du₀ i + s * Du₀ i)
                    ⬝ (fun i => s * Du₀ i))
              + absPowMinusTwo γBarReal (u₀ + s * u₀)
                * ((u₀ + s * u₀) * (s * u₀)))) / s
        = f2 s + (f3 s + f4 s)
    have hT3T4 :
        ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
              * ((fun i => Du₀ i + s * Du₀ i)
                  ⬝ (fun i => s * Du₀ i))
            + absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * (s * u₀))) / s
          = f3 s + f4 s := by
      have hsplit :
          ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
                * ((fun i => Du₀ i + s * Du₀ i)
                    ⬝ (fun i => s * Du₀ i))
              + absPowMinusTwo γBarReal (u₀ + s * u₀)
                * ((u₀ + s * u₀) * (s * u₀)))
            = ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
                * ((fun i => Du₀ i + s * Du₀ i)
                    ⬝ (fun i => s * Du₀ i)))
              + ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
                * ((u₀ + s * u₀) * (s * u₀))) := by ring
      rw [hsplit, add_div, hT3s, hT4s]
    -- T1 contributes 0, so (T1 + T2)/s = T2/s = f2.
    rw [add_div, add_div, hT1zero, zero_div, zero_add, hT2s, hT3T4]
  -- Step B: limits of f2, f3, f4 at 0 (copied verbatim from
  -- `_pointwise_tendsto` since they do not depend on `DpH`).
  have hf2_cont : Continuous f2 := continuous_const
  have hf2_zero : f2 0 = (m₀ - 1) * u₀ := rfl
  have h_vec_id :
      vecAbsPowMinusTwo γBarReal Du₀ * (Du₀ ⬝ Du₀)
        = (Du₀ ⬝ Du₀) ^ (γBarReal / 2) := by
    unfold vecAbsPowMinusTwo
    rcases eq_or_lt_of_le hDuDu_nn with hzero | hpos
    · rw [← hzero]
      have h1 : (0 : ℝ) ^ ((γBarReal - 2) / 2) * 0 = 0 := by ring
      rw [h1]
      have hexp_pos : (0 : ℝ) < γBarReal / 2 := by linarith
      rw [Real.zero_rpow hexp_pos.ne']
    · have h_add :
          (Du₀ ⬝ Du₀) ^ ((γBarReal - 2) / 2) * (Du₀ ⬝ Du₀)
            = (Du₀ ⬝ Du₀) ^ ((γBarReal - 2) / 2) * (Du₀ ⬝ Du₀) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      rw [h_add, ← Real.rpow_add hpos]
      congr 1
      ring
  have hf3_at : Filter.Tendsto f3 (𝓝 (0 : ℝ))
      (𝓝 (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2))) := by
    have h_self_eq : ∀ s : ℝ,
        (fun i => Du₀ i + s * Du₀ i) ⬝ (fun i => Du₀ i + s * Du₀ i)
          = (1 + s) ^ 2 * (Du₀ ⬝ Du₀) := by
      intro s
      simp only [euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have h_dot_eq : ∀ s : ℝ,
        (fun i => Du₀ i + s * Du₀ i) ⬝ Du₀
          = (1 + s) * (Du₀ ⬝ Du₀) := by
      intro s
      simp only [euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have hf3_simp : f3 = fun s : ℝ => ε *
        (((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
          * ((1 + s) * (Du₀ ⬝ Du₀))) := by
      funext s
      show ε * (vecAbsPowMinusTwo γBarReal (fun i => Du₀ i + s * Du₀ i)
            * ((fun i => Du₀ i + s * Du₀ i) ⬝ Du₀))
            = ε * (((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
                * ((1 + s) * (Du₀ ⬝ Du₀)))
      unfold vecAbsPowMinusTwo
      rw [h_self_eq s, h_dot_eq s]
    rw [hf3_simp]
    have htarget :
        ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
        = ε * (((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
              * ((1 + (0:ℝ)) * (Du₀ ⬝ Du₀))) := by
      have hone : (1 + (0:ℝ)) = 1 := by ring
      rw [hone]
      simp only [one_pow, one_mul]
      have hvec := h_vec_id
      unfold vecAbsPowMinusTwo at hvec
      rw [← hvec]
    rw [htarget]
    apply Filter.Tendsto.const_mul
    have h_one_plus : Filter.Tendsto (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 1) := by
      have hcont : Continuous fun s : ℝ => 1 + s :=
        continuous_const.add continuous_id
      have ht := hcont.tendsto 0
      simpa using ht
    have h_sqA : Filter.Tendsto
        (fun s : ℝ => (1 + s) ^ 2 * (Du₀ ⬝ Du₀))
        (𝓝 0) (𝓝 ((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀))) := by
      have h_one_plus_lin : Filter.Tendsto (fun s : ℝ => 1 + s)
          (𝓝 0) (𝓝 (1 + (0:ℝ))) :=
        ((continuous_const.add continuous_id).tendsto 0)
      have h_sq_lin : Filter.Tendsto (fun s : ℝ => (1 + s) ^ 2)
          (𝓝 0) (𝓝 ((1 + (0:ℝ)) ^ 2)) := by
        have hh := h_one_plus_lin.mul h_one_plus_lin
        simpa [pow_two] using hh
      exact h_sq_lin.mul (tendsto_const_nhds (x := (Du₀ ⬝ Du₀)))
    rcases eq_or_lt_of_le hDuDu_nn with hAzero | hApos
    · have hfn :
          (fun s : ℝ =>
            ((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
            * ((1 + s) * (Du₀ ⬝ Du₀)))
          = fun _ => 0 := by
        funext s
        rw [← hAzero]
        ring
      have hgoal :
          ((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2)
            * ((1 + (0:ℝ)) * (Du₀ ⬝ Du₀)) = 0 := by
        rw [← hAzero]; ring
      rw [hfn, hgoal]
      exact tendsto_const_nhds
    · have h_rpow : Filter.Tendsto
          (fun s : ℝ => ((1 + s) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2))
          (𝓝 0)
          (𝓝 (((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀)) ^ ((γBarReal - 2) / 2))) := by
        have hbase_pos : 0 < (1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀) := by
          have h1 : (1 + (0:ℝ)) ^ 2 = 1 := by ring
          rw [h1]; simpa using hApos
        have hcont :=
          Real.continuousAt_rpow_const ((1 + (0:ℝ)) ^ 2 * (Du₀ ⬝ Du₀))
            ((γBarReal - 2) / 2) (Or.inl hbase_pos.ne')
        exact hcont.tendsto.comp h_sqA
      have h_lin : Filter.Tendsto
          (fun s : ℝ => (1 + s) * (Du₀ ⬝ Du₀))
          (𝓝 0)
          (𝓝 ((1 + (0:ℝ)) * (Du₀ ⬝ Du₀))) := by
        have h_one_plus_lin : Filter.Tendsto (fun s : ℝ => 1 + s)
            (𝓝 0) (𝓝 (1 + (0:ℝ))) :=
          ((continuous_const.add continuous_id).tendsto 0)
        exact h_one_plus_lin.mul (tendsto_const_nhds (x := (Du₀ ⬝ Du₀)))
      exact h_rpow.mul h_lin
  have h_scal_id :
      absPowMinusTwo γBarReal u₀ * (u₀ * u₀) = |u₀| ^ γBarReal := by
    unfold absPowMinusTwo
    by_cases hzero : u₀ = 0
    · rw [hzero]
      have h0 : |(0:ℝ)| ^ (γBarReal - 2) * (0 * 0) = 0 := by
        rw [abs_zero]; ring
      rw [h0, abs_zero]
      have hexp_pos : (0 : ℝ) < γBarReal := by linarith
      rw [Real.zero_rpow hexp_pos.ne']
    · have hu_abs_pos : 0 < |u₀| := abs_pos.mpr hzero
      have h_uu : u₀ * u₀ = |u₀| ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
        rw [Real.rpow_natCast]
        rw [show |u₀| ^ (2 : ℕ) = |u₀| * |u₀| from by ring]
        rw [← abs_mul, abs_mul_self]
      rw [h_uu]
      rw [← Real.rpow_add hu_abs_pos]
      have hexp : γBarReal - 2 + 2 = γBarReal := by ring
      rw [hexp]
  have hf4_at : Filter.Tendsto f4 (𝓝 (0 : ℝ))
      (𝓝 (ε * |u₀| ^ γBarReal)) := by
    have hf4_simp : ∀ s : ℝ,
        f4 s
          = ε * (|1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
                * ((1 + s) * (u₀ * u₀))) := by
      intro s
      show ε * (absPowMinusTwo γBarReal (u₀ + s * u₀)
              * ((u₀ + s * u₀) * u₀))
          = ε * (|1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
                * ((1 + s) * (u₀ * u₀)))
      unfold absPowMinusTwo
      have hfact : u₀ + s * u₀ = (1 + s) * u₀ := by ring
      rw [hfact]
      rw [abs_mul]
      have habs_pow :
          (|1 + s| * |u₀|) ^ (γBarReal - 2)
            = |1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2) :=
        Real.mul_rpow (abs_nonneg _) (abs_nonneg _)
      rw [habs_pow]
      ring
    have hf4_eq : f4 = fun s : ℝ =>
        ε * (|1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
              * ((1 + s) * (u₀ * u₀))) := by
      funext s; exact hf4_simp s
    rw [hf4_eq]
    have htarget :
        ε * |u₀| ^ γBarReal
          = ε * (|1 + (0:ℝ)| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2)
              * ((1 + (0:ℝ)) * (u₀ * u₀))) := by
      have h1 : (1 + (0:ℝ)) = 1 := by ring
      rw [h1, abs_one, Real.one_rpow, one_mul, one_mul]
      have hsc := h_scal_id
      unfold absPowMinusTwo at hsc
      rw [← hsc]
    rw [htarget]
    apply Filter.Tendsto.const_mul
    have h_abs_one_plus : Filter.Tendsto
        (fun s : ℝ => |1 + s|)
        (𝓝 0) (𝓝 (|1 + (0:ℝ)|)) := by
      have hcont : Continuous fun s : ℝ => |1 + s| :=
        (continuous_const.add continuous_id).abs
      exact hcont.tendsto 0
    have h_one_plus_lin : Filter.Tendsto
        (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 (1 + (0:ℝ))) :=
      ((continuous_const.add continuous_id).tendsto 0)
    have hbase_pos : (0 : ℝ) < |1 + (0:ℝ)| := by
      rw [show (1 + (0:ℝ)) = 1 by ring, abs_one]
      exact zero_lt_one
    have h_rpow : Filter.Tendsto
        (fun s : ℝ => |1 + s| ^ (γBarReal - 2))
        (𝓝 0) (𝓝 (|1 + (0:ℝ)| ^ (γBarReal - 2))) := by
      have hcont :=
        Real.continuousAt_rpow_const (|1 + (0:ℝ)|) (γBarReal - 2)
          (Or.inl hbase_pos.ne')
      exact hcont.tendsto.comp h_abs_one_plus
    have h_uconst : Filter.Tendsto
        (fun _ : ℝ => |u₀| ^ (γBarReal - 2))
        (𝓝 0) (𝓝 (|u₀| ^ (γBarReal - 2))) :=
      tendsto_const_nhds
    have h_lin : Filter.Tendsto
        (fun s : ℝ => (1 + s) * (u₀ * u₀))
        (𝓝 0) (𝓝 ((1 + (0:ℝ)) * (u₀ * u₀))) :=
      h_one_plus_lin.mul tendsto_const_nhds
    have h12 : Filter.Tendsto
        (fun s : ℝ => |1 + s| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2))
        (𝓝 0) (𝓝 (|1 + (0:ℝ)| ^ (γBarReal - 2) * |u₀| ^ (γBarReal - 2))) :=
      h_rpow.mul h_uconst
    exact h12.mul h_lin
  have hf2_at : Filter.Tendsto f2 (𝓝 (0 : ℝ))
      (𝓝 ((m₀ - 1) * u₀)) := by
    have h := hf2_cont.tendsto 0
    rw [hf2_zero] at h
    exact h
  have hsum_at : Filter.Tendsto
      (fun s : ℝ => f2 s + (f3 s + f4 s)) (𝓝 (0 : ℝ))
      (𝓝 ((m₀ - 1) * u₀
            + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
                + ε * |u₀| ^ γBarReal))) :=
    hf2_at.add (hf3_at.add hf4_at)
  have hsum_at' : Filter.Tendsto
      (fun s : ℝ => f2 s + (f3 s + f4 s)) (𝓝[≠] (0 : ℝ))
      (𝓝 ((m₀ - 1) * u₀
            + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
                + ε * |u₀| ^ γBarReal))) :=
    hsum_at.mono_left nhdsWithin_le_nhds
  -- Target: when m₀ = 0, the `m·DpH` summand is 0, so the target
  -- value is just `(m₀-1)·u₀ + ε·(Du⬝Du)^(γ̄/2) + ε·|u|^γ̄`.
  have htarget_eq :
      strongTransportTargetIntegrand sol x
        = (m₀ - 1) * u₀
          + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
              + ε * |u₀| ^ γBarReal) := by
    -- The `m₀ * (DpH x Du₀ m₀ ⬝ Du₀)` summand is 0 since `m₀ = sol.m x = 0`.
    have hT1 : m₀ * (DpH x Du₀ m₀ ⬝ Du₀) = 0 := by
      have : m₀ = 0 := hm_zero
      rw [this, zero_mul]
    show m₀ * (DpH x Du₀ m₀ ⬝ Du₀)
        + (m₀ - 1) * u₀
        + ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
        + ε * |u₀| ^ γBarReal
        = (m₀ - 1) * u₀
          + (ε * (Du₀ ⬝ Du₀) ^ (γBarReal / 2)
              + ε * |u₀| ^ γBarReal)
    linarith [hT1]
  rw [htarget_eq]
  apply Filter.Tendsto.congr' (f₁ := fun s => f2 s + (f3 s + f4 s))
  · refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{s : ℝ | s ≠ 0}, ?_, ?_⟩
    · exact self_mem_nhdsWithin
    · intro s hs
      exact (h_rewrite s hs).symm
  · exact hsum_at'

/-- **A.e.-pointwise `s → 0` limit of the rescaled perturbed transport
integrand, derived from the paper power-growth bundle.**

For almost every `x ∈ 𝕋^d`, the rescaled integrand
`strongTransportPerturbedIntegrand sol s x / s` converges as `s → 0`
(through `s ≠ 0`) to `strongTransportTargetIntegrand sol x`,
provided only:

* `hpow : HypothesisPowerGrowth H DpH` (the paper bundle), which
  supplies the `(p, m) ↦ DpH x p m`-on-`{0 < m}` continuity required
  in the `0 < sol.m x` branch and the strict positivity exponents `α > 1`,
  `β > 0` needed to derive `1 ≤ γBarReal`;
* the paper exponent identifications `βBarReal = β + 1` and
  `γBarReal = α (β + 1) / β`.

This is the paper-faithful replacement for the global continuity
hypothesis `∀ x, Continuous fun p => DpH x p (sol.m x)`: at `sol.m x = 0`
the `m · DpH` summand vanishes (no DpH continuity needed), and at
`0 < sol.m x` the joint continuity of `(p, m) ↦ DpH x p m` on the open
half-plane `{0 < m}` slices to give the per-point `Continuous` required.

Per the iter post-0627 / 2026-05-17 expert review re-scoping of
`paperSolFor-final-phase4-aux-hDpH-cont`. -/
theorem strongTransportPerturbedIntegrand_pointwise_tendsto_of_powerGrowth
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto
        (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (strongTransportTargetIntegrand sol x)) := by
  -- `1 ≤ γBarReal` from `1 < α`, `0 < β`.
  have hγ : (1 : ℝ) ≤ γBarReal := by
    rw [hγBarPaper]
    exact le_of_lt
      (StationaryMFG.Hamiltonian.one_lt_gammaBar hpow.α hpow.β hpow.hα hpow.hβ)
  -- Slice `hpow.continuous_DpH_pm` together with `sol.hmNonneg`.
  filter_upwards [hpow.continuous_DpH_pm, sol.hmNonneg]
    with x hContOn hmNN
  by_cases hm : sol.m x = 0
  · -- `sol.m x = 0`: the m·DpH summand vanishes; no DpH continuity needed.
    exact strongTransportPerturbedIntegrand_pointwise_tendsto_at_m_zero
      sol x hm hγ
  · -- `0 < sol.m x`: slice the joint ContinuousOn to a per-point Continuous
    --   in `p` (at fixed `m = sol.m x > 0`), then call `_pointwise_tendsto`.
    have hmpos : 0 < sol.m x := lt_of_le_of_ne hmNN (Ne.symm hm)
    -- The embedding `p ↦ (p, sol.m x)` is continuous and lands in {0 < pm.2}.
    have h_emb_cont : Continuous fun p : Fin d → ℝ => (p, sol.m x) :=
      continuous_id.prodMk continuous_const
    have h_emb_in : ∀ p : Fin d → ℝ,
        (p, sol.m x) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} :=
      fun _ => hmpos
    -- `ContinuousOn.comp_continuous`: precompose by the embedding to get
    -- `Continuous (fun p => DpH x p (sol.m x))`.
    have hCont : Continuous fun p : Fin d → ℝ => DpH x p (sol.m x) := by
      have h := hContOn.comp_continuous h_emb_cont h_emb_in
      -- `h : Continuous ((fun pm => DpH x pm.1 pm.2) ∘ (fun p => (p, sol.m x)))`
      -- which reduces to `Continuous (fun p => DpH x p (sol.m x))`.
      simpa using! h
    exact strongTransportPerturbedIntegrand_pointwise_tendsto
      sol x hCont hγ

/-! ### DCT assembly of the σ → 0 Tendsto inputs (`hCont_pos` / `hCont_neg`)

Per task `infra-P5-strongTransport-DCT-assembly`. We combine the
pointwise limit (`strongTransportPerturbedIntegrand_pointwise_tendsto`)
and the L¹ dominator (`strongTransportPerturbedIntegrand_dominator`) via
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence` along
the natural-number filter `atTop`, with `s_n = ±1/(n+1)`. The factor
`1/s_n = ±(n+1)` is moved out of the integral via
`MeasureTheory.integral_div`. -/

/-- **DCT discharge of `hCont_pos`.**

Combines the pointwise convergence and the L¹ dominator into the
authorised σ → 0 Tendsto input of
`strongTransport_at_uEpsi_hVI_pos_of_perturbed`. -/
theorem strongTransport_hCont_pos
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hPointTendsto :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (strongTransportTargetIntegrand sol x)))
    (hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (UnitCube d)))
    -- Dominator pieces (consumed by `strongTransportPerturbedIntegrand_dominator`).
    (G_mDpH : (Fin d → ℝ) → ℝ)
    (hG_mDpH : MemLpPer (d := d) 1 G_mDpH)
    (h_mDpH_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |sol.m x *
              (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                ⬝ (fun i => s * sol.Du i x)) / s|
            ≤ G_mDpH x)
    (hG_mu : MemLpPer (d := d) 1
        (fun x => |sol.m x - 1| * |sol.u x|))
    (G_vec : (Fin d → ℝ) → ℝ)
    (hG_vec : MemLpPer (d := d) 1 G_vec)
    (h_vec_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |ε * (vecAbsPowMinusTwo γBarReal
                  (fun i => sol.Du i x + s * sol.Du i x)
                * ((fun i => sol.Du i x + s * sol.Du i x)
                    ⬝ (fun i => s * sol.Du i x))) / s|
            ≤ G_vec x)
    (G_scal : (Fin d → ℝ) → ℝ)
    (hG_scal : MemLpPer (d := d) 1 G_scal)
    (h_scal_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
                  * ((sol.u x + s * sol.u x) * (s * sol.u x))) / s|
            ≤ G_scal x) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) *
          ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
            strongTransportTargetIntegrand sol x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))) := by
  -- Notation: s_n = 1/(n+1), positive in (0, 1].
  set sN : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsN_def
  -- s_n > 0.
  have hsN_pos : ∀ n : ℕ, 0 < sN n := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact one_div_pos.mpr hn1
  have hsN_ne : ∀ n : ℕ, sN n ≠ 0 := fun n => (hsN_pos n).ne'
  have hsN_in : ∀ n : ℕ, sN n ∈ Set.Icc (-1 : ℝ) 1 := by
    intro n
    refine ⟨?_, ?_⟩
    · linarith [hsN_pos n]
    · -- 1/(n+1) ≤ 1.
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le zero_lt_one hn1
      have : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) := by simpa using hle
      simpa [hsN_def] using this
  -- 1/s_n = (n:ℝ) + 1.
  have hsN_inv : ∀ n : ℕ, 1 / sN n = (n : ℝ) + 1 := by
    intro n
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      exact h.ne'
    show 1 / (1 / ((n : ℝ) + 1)) = (n : ℝ) + 1
    rw [one_div_one_div]
  -- Tendsto s_n → 0.
  have hsN_tendsto_zero : Filter.Tendsto sN Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hsN_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  -- Tendsto s_n → 0 through {s ≠ 0}.
  have hsN_tendsto_punctured :
      Filter.Tendsto sN Filter.atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within sN
      hsN_tendsto_zero
    refine Filter.Eventually.of_forall ?_
    intro n
    exact hsN_ne n
  -- Define `F n x = Iperturb sol (sN n) x / sN n`.
  set F : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => strongTransportPerturbedIntegrand sol (sN n) x / sN n
    with hF_def
  set fLim : (Fin d → ℝ) → ℝ :=
    fun x => strongTransportTargetIntegrand sol x with hfLim_def
  -- Obtain dominator g.
  obtain ⟨g, hg_int, hg_bound⟩ :=
    strongTransportPerturbedIntegrand_dominator sol
      G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
      G_scal hG_scal h_scal_pt
  -- Dominator hypotheses for DCT.
  have h_meas : ∀ᶠ n in (Filter.atTop : Filter ℕ),
      AEStronglyMeasurable (F n)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact hmeas_pos n
  have h_bound : ∀ᶠ n in (Filter.atTop : Filter ℕ),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖F n x‖ ≤ g x := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hpt := hg_bound (sN n) (hsN_in n) (hsN_ne n)
    filter_upwards [hpt] with x hx
    show |strongTransportPerturbedIntegrand sol (sN n) x / sN n| ≤ g x
    simpa [Real.norm_eq_abs] using hx
  -- Integrability of g (turn `IntegrableOn` into `Integrable` w.r.t. restrict).
  have hg_integrable :
      MeasureTheory.Integrable g
        (MeasureTheory.volume.restrict (UnitCube d)) := hg_int
  -- Pointwise convergence: use the a.e.-pointwise Tendsto input directly.
  have h_lim : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (fLim x)) := by
    filter_upwards [hPointTendsto] with x h_punc
    -- Compose with sN tendsto 𝓝[≠] 0.
    exact h_punc.comp hsN_tendsto_punctured
  -- Apply DCT.
  have h_dct :
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ x, F n x ∂(MeasureTheory.volume.restrict (UnitCube d)))
        Filter.atTop
        (𝓝 (∫ x, fLim x ∂(MeasureTheory.volume.restrict (UnitCube d)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      g h_meas h_bound hg_integrable h_lim
  -- Convert to setIntegral notation and pull `1/sN n` out.
  -- ∫ x in UnitCube d, F n x = ∫ x in UnitCube d, Iperturb/sN n
  --                          = (∫ x in UnitCube d, Iperturb) / sN n
  --                          = ((n+1)) * (∫ x in UnitCube d, Iperturb).
  have h_eq_n : ∀ n : ℕ,
      ∫ x, F n x ∂(MeasureTheory.volume.restrict (UnitCube d))
        = ((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    intro n
    -- ∫ x, F n x ∂(restrict) = ∫ x in UnitCube, F n x ∂volume.
    have hF_int :
        ∫ x, F n x ∂(MeasureTheory.volume.restrict (UnitCube d))
          = ∫ x in UnitCube d, F n x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := rfl
    rw [hF_int]
    -- Now ∫ x in UnitCube d, Iperturb/sN n = (∫ Iperturb)/sN n.
    have h_div :
        ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (sN n) x / sN n
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
          = (∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) / sN n :=
      MeasureTheory.integral_div (sN n)
        (fun x => strongTransportPerturbedIntegrand sol (sN n) x)
    show ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (sN n) x / sN n
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
          = ((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
    rw [h_div]
    -- a / sN n = ((n+1)) * a.
    have h := hsN_inv n
    rw [div_eq_mul_inv]
    rw [show ((n : ℝ) + 1) *
              ∫ x in UnitCube d,
                strongTransportPerturbedIntegrand sol (sN n) x
                ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
            = (∫ x in UnitCube d,
                strongTransportPerturbedIntegrand sol (sN n) x
                ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
              * ((n : ℝ) + 1) from by ring]
    congr 1
    -- (sN n)⁻¹ = (n+1).
    have hinv : (sN n)⁻¹ = (n : ℝ) + 1 := by
      rw [hsN_def]
      simp
    exact hinv
  -- Apply the equality to convert h_dct into the target shape.
  have h_eq_lim :
      ∫ x, fLim x ∂(MeasureTheory.volume.restrict (UnitCube d))
        = ∫ x in UnitCube d, strongTransportTargetIntegrand sol x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := rfl
  rw [h_eq_lim] at h_dct
  -- Rewrite each term of the limit sequence.
  have h_dct' :
      Filter.Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, strongTransportTargetIntegrand sol x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))) := by
    apply h_dct.congr
    intro n
    exact h_eq_n n
  -- Done — the target uses `1/((n:ℝ)+1)` literally; substitute `sN`.
  show Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) *
          ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
      Filter.atTop _
  exact h_dct'

/-- **DCT discharge of `hCont_neg`.**

Combines the pointwise convergence and the L¹ dominator into the
authorised σ → 0 Tendsto input of
`strongTransport_at_uEpsi_hVI_neg_of_perturbed`. The signed scaling is
`s_n = -1/(n+1)`, so `1/s_n = -(n+1)`. -/
theorem strongTransport_hCont_neg
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hPointTendsto :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (strongTransportTargetIntegrand sol x)))
    (hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (G_mDpH : (Fin d → ℝ) → ℝ)
    (hG_mDpH : MemLpPer (d := d) 1 G_mDpH)
    (h_mDpH_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |sol.m x *
              (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                ⬝ (fun i => s * sol.Du i x)) / s|
            ≤ G_mDpH x)
    (hG_mu : MemLpPer (d := d) 1
        (fun x => |sol.m x - 1| * |sol.u x|))
    (G_vec : (Fin d → ℝ) → ℝ)
    (hG_vec : MemLpPer (d := d) 1 G_vec)
    (h_vec_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |ε * (vecAbsPowMinusTwo γBarReal
                  (fun i => sol.Du i x + s * sol.Du i x)
                * ((fun i => sol.Du i x + s * sol.Du i x)
                    ⬝ (fun i => s * sol.Du i x))) / s|
            ≤ G_vec x)
    (G_scal : (Fin d → ℝ) → ℝ)
    (hG_scal : MemLpPer (d := d) 1 G_scal)
    (h_scal_pt :
      ∀ s ∈ Set.Icc (-1 : ℝ) 1, s ≠ 0 →
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          |ε * (absPowMinusTwo γBarReal (sol.u x + s * sol.u x)
                  * ((sol.u x + s * sol.u x) * (s * sol.u x))) / s|
            ≤ G_scal x) :
    Filter.Tendsto
      (fun n : ℕ =>
        -((n : ℝ) + 1) *
          ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
            strongTransportTargetIntegrand sol x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))) := by
  -- Notation: s_n = -1/(n+1), negative in [-1, 0).
  set sN : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 1)) with hsN_def
  have hsN_neg : ∀ n : ℕ, sN n < 0 := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hpos : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn1
    show -(1 / ((n : ℝ) + 1)) < 0
    linarith
  have hsN_ne : ∀ n : ℕ, sN n ≠ 0 := fun n => (hsN_neg n).ne
  have hsN_in : ∀ n : ℕ, sN n ∈ Set.Icc (-1 : ℝ) 1 := by
    intro n
    refine ⟨?_, ?_⟩
    · -- -1 ≤ -1/(n+1).
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le zero_lt_one hn1
      have h : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) := by simpa using hle
      show -1 ≤ -(1 / ((n : ℝ) + 1))
      linarith
    · -- -1/(n+1) ≤ 1.
      linarith [hsN_neg n]
  -- 1/s_n = -((n:ℝ) + 1).
  have hsN_inv : ∀ n : ℕ, 1 / sN n = -((n : ℝ) + 1) := by
    intro n
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      exact h.ne'
    show 1 / -(1 / ((n : ℝ) + 1)) = -((n : ℝ) + 1)
    field_simp
  -- Tendsto s_n → 0 (since `1/(n+1) → 0` and negation is continuous).
  have hsN_tendsto_zero : Filter.Tendsto sN Filter.atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hneg := h.neg
    simpa [hsN_def] using hneg
  -- Tendsto s_n → 0 through {s ≠ 0}.
  have hsN_tendsto_punctured :
      Filter.Tendsto sN Filter.atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within sN
      hsN_tendsto_zero
    refine Filter.Eventually.of_forall ?_
    intro n
    exact hsN_ne n
  set F : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => strongTransportPerturbedIntegrand sol (sN n) x / sN n
    with hF_def
  set fLim : (Fin d → ℝ) → ℝ :=
    fun x => strongTransportTargetIntegrand sol x with hfLim_def
  obtain ⟨g, hg_int, hg_bound⟩ :=
    strongTransportPerturbedIntegrand_dominator sol
      G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
      G_scal hG_scal h_scal_pt
  have h_meas : ∀ᶠ n in (Filter.atTop : Filter ℕ),
      AEStronglyMeasurable (F n)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact hmeas_neg n
  have h_bound : ∀ᶠ n in (Filter.atTop : Filter ℕ),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖F n x‖ ≤ g x := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hpt := hg_bound (sN n) (hsN_in n) (hsN_ne n)
    filter_upwards [hpt] with x hx
    show |strongTransportPerturbedIntegrand sol (sN n) x / sN n| ≤ g x
    simpa [Real.norm_eq_abs] using hx
  have hg_integrable :
      MeasureTheory.Integrable g
        (MeasureTheory.volume.restrict (UnitCube d)) := hg_int
  have h_lim : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (fLim x)) := by
    filter_upwards [hPointTendsto] with x h_punc
    exact h_punc.comp hsN_tendsto_punctured
  have h_dct :
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ x, F n x ∂(MeasureTheory.volume.restrict (UnitCube d)))
        Filter.atTop
        (𝓝 (∫ x, fLim x ∂(MeasureTheory.volume.restrict (UnitCube d)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      g h_meas h_bound hg_integrable h_lim
  have h_eq_n : ∀ n : ℕ,
      ∫ x, F n x ∂(MeasureTheory.volume.restrict (UnitCube d))
        = -((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    intro n
    have hF_int :
        ∫ x, F n x ∂(MeasureTheory.volume.restrict (UnitCube d))
          = ∫ x in UnitCube d, F n x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := rfl
    rw [hF_int]
    have h_div :
        ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (sN n) x / sN n
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
          = (∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) / sN n :=
      MeasureTheory.integral_div (sN n)
        (fun x => strongTransportPerturbedIntegrand sol (sN n) x)
    show ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (sN n) x / sN n
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
          = -((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
    rw [h_div]
    rw [div_eq_mul_inv]
    rw [show -((n : ℝ) + 1) *
              ∫ x in UnitCube d,
                strongTransportPerturbedIntegrand sol (sN n) x
                ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
            = (∫ x in UnitCube d,
                strongTransportPerturbedIntegrand sol (sN n) x
                ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
              * (-((n : ℝ) + 1)) from by ring]
    congr 1
    -- (sN n)⁻¹ = -(n+1).
    have hinv : (sN n)⁻¹ = -((n : ℝ) + 1) := by
      have h := hsN_inv n
      rw [show (1 : ℝ) / sN n = (sN n)⁻¹ from one_div _] at h
      exact h
    exact hinv
  have h_eq_lim :
      ∫ x, fLim x ∂(MeasureTheory.volume.restrict (UnitCube d))
        = ∫ x in UnitCube d, strongTransportTargetIntegrand sol x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := rfl
  rw [h_eq_lim] at h_dct
  have h_dct' :
      Filter.Tendsto
        (fun n : ℕ =>
          -((n : ℝ) + 1) *
            ∫ x in UnitCube d,
              strongTransportPerturbedIntegrand sol (sN n) x
              ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, strongTransportTargetIntegrand sol x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))) := by
    apply h_dct.congr
    intro n
    exact h_eq_n n
  show Filter.Tendsto
      (fun n : ℕ =>
        -((n : ℝ) + 1) *
          ∫ x in UnitCube d,
            strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
            ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
      Filter.atTop _
  exact h_dct'

/-! ### Unit-test `example`: thread DCT discharges into the σ → 0 bridge

This is the closure of the σ → 0 chain: the per-step VI inputs
(`hStep_pos`/`hStep_neg`) plus the DCT-derived Tendsto inputs
(via the `strongTransport_hCont_{pos,neg}` discharges) feed
`strongTransport_at_uEpsi_of_hVIeps_transport`. -/

/-- Unit test: assemble both DCT discharges and feed them into the
σ → 0 bridge composed with the strong-transport identity, using the
closed-form dominator producer (no B-class envelope inputs). -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (h : HypothesisPowerGrowth H DpH)
    (hβBarPaper : βBarReal = h.β + 1)
    (hγBarPaper : γBarReal = h.α * (h.β + 1) / h.β)
    (hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) :
    (0 : ℝ) =
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Derive `1 ≤ γBarReal` from `hpow`.
  have hγ : (1 : ℝ) ≤ γBarReal := by
    rw [hγBarPaper]
    exact le_of_lt
      (StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β h.hα h.hβ)
  -- Derive the a.e.-pointwise Tendsto from `hpow + sol.hmNonneg`.
  have hPointTendsto :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (strongTransportTargetIntegrand sol x)) :=
    strongTransportPerturbedIntegrand_pointwise_tendsto_of_powerGrowth
      sol h hγBarPaper
  -- Closed-form envelope producers: no B-class inputs needed.
  obtain ⟨G_mDpH, hG_mDpH, h_mDpH_pt⟩ :=
    strongTransportDominator_G_mDpH_of_sol sol h hβBarPaper hγBarPaper
  obtain ⟨G_vec, hG_vec, h_vec_pt⟩ :=
    strongTransportDominator_G_vec_of_sol hγ sol
  obtain ⟨G_scal, hG_scal, h_scal_pt⟩ :=
    strongTransportDominator_G_scal_of_sol hγ sol
  have hG_mu : MemLpPer (d := d) 1
      (fun x => |sol.m x - 1| * |sol.u x|) :=
    strongTransportDominator_G_mu_of_sol sol h hβBarPaper hγBarPaper
  -- Feed the four envelopes into the open `_hCont_*` discharges.
  have hCont_pos :=
    strongTransport_hCont_pos sol hPointTendsto hmeas_pos
      G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
      G_scal hG_scal h_scal_pt
  have hCont_neg :=
    strongTransport_hCont_neg sol hPointTendsto hmeas_neg
      G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
      G_scal hG_scal h_scal_pt
  exact strongTransport_at_uEpsi_of_hVIeps_transport sol
    (strongTransport_at_uEpsi_hVI_pos_of_perturbed sol hStep_pos hCont_pos)
    (strongTransport_at_uEpsi_hVI_neg_of_perturbed sol hStep_neg hCont_neg)

/-! ### Headline wrapper: unconditional strong-transport equality

Per task `infra-P5-strongTransport-wire-unconditional-final`. Promotes
the σ → 0 / DCT closure `example` immediately above into a named
theorem, eliminating the B-class authorised inputs `hVI_pos`/`hVI_neg`
of `strongTransport_at_uEpsi_of_hVIeps_transport`. The remaining
inputs are:

* the paper-exponent identifications `hβBarPaper`, `hγBarPaper`;
* `hDpH_cont`, `hmeas_pos`, `hmeas_neg` (regularity);
* the per-`n` perturbed-primal VI inputs `hStep_pos`, `hStep_neg` —
  the paper line-1185 `(μ, υ) = (m, u + s u_\epsi)` substitution at
  `s = ±1/(n+1)`. -/

/-- **Unconditional strong-transport equality at `φ = u_ε`** (paper
lines 1205–1216). Composes the closed-form L¹ dominator
(`strongTransportPerturbedIntegrand_dominator_closed`, via the four
`strongTransportDominator_G_*_of_sol` envelope producers it consumes)
with the two `Tendsto` discharges `strongTransport_hCont_pos` /
`strongTransport_hCont_neg`, and feeds the resulting Tendsto witnesses
through `strongTransport_at_uEpsi_hVI_{pos,neg}_of_perturbed` into
`strongTransport_at_uEpsi_of_hVIeps_transport`. The B-class
authorised inputs `hVI_pos` / `hVI_neg` are eliminated. -/
theorem strongTransport_at_uEpsi_unconditional
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (h : HypothesisPowerGrowth H DpH)
    (hβBarPaper : βBarReal = h.β + 1)
    (hγBarPaper : γBarReal = h.α * (h.β + 1) / h.β)
    (hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) :
    (0 : ℝ) =
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Derive `1 ≤ γBarReal` from `hpow`.
  have hγ : (1 : ℝ) ≤ γBarReal := by
    rw [hγBarPaper]
    exact le_of_lt
      (StationaryMFG.Hamiltonian.one_lt_gammaBar h.α h.β h.hα h.hβ)
  -- Derive the a.e.-pointwise Tendsto from `hpow + sol.hmNonneg`.
  have hPointTendsto :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun s : ℝ => strongTransportPerturbedIntegrand sol s x / s)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (strongTransportTargetIntegrand sol x)) :=
    strongTransportPerturbedIntegrand_pointwise_tendsto_of_powerGrowth
      sol h hγBarPaper
  -- Closed-form envelope producers (no B-class envelope inputs needed).
  obtain ⟨G_mDpH, hG_mDpH, h_mDpH_pt⟩ :=
    strongTransportDominator_G_mDpH_of_sol sol h hβBarPaper hγBarPaper
  obtain ⟨G_vec, hG_vec, h_vec_pt⟩ :=
    strongTransportDominator_G_vec_of_sol hγ sol
  obtain ⟨G_scal, hG_scal, h_scal_pt⟩ :=
    strongTransportDominator_G_scal_of_sol hγ sol
  have hG_mu : MemLpPer (d := d) 1
      (fun x => |sol.m x - 1| * |sol.u x|) :=
    strongTransportDominator_G_mu_of_sol sol h hβBarPaper hγBarPaper
  -- Feed the four envelopes into the open `_hCont_*` discharges.
  have hCont_pos :=
    strongTransport_hCont_pos sol hPointTendsto hmeas_pos
      G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
      G_scal hG_scal h_scal_pt
  have hCont_neg :=
    strongTransport_hCont_neg sol hPointTendsto hmeas_neg
      G_mDpH hG_mDpH h_mDpH_pt hG_mu G_vec hG_vec h_vec_pt
      G_scal hG_scal h_scal_pt
  exact strongTransport_at_uEpsi_of_hVIeps_transport sol
    (strongTransport_at_uEpsi_hVI_pos_of_perturbed sol hStep_pos hCont_pos)
    (strongTransport_at_uEpsi_hVI_neg_of_perturbed sol hStep_neg hCont_neg)

/-- Sanity test: pin the type-shape of
`strongTransport_at_uEpsi_unconditional`. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (h : HypothesisPowerGrowth H DpH)
    (hβBarPaper : βBarReal = h.β + 1)
    (hγBarPaper : γBarReal = h.α * (h.β + 1) / h.β)
    (hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x => strongTransportPerturbedIntegrand sol
                      (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (1 / ((n : ℝ) + 1)) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in UnitCube d,
          strongTransportPerturbedIntegrand sol (-(1 / ((n : ℝ) + 1))) x
          ∂(volume : MeasureTheory.Measure (Fin d → ℝ))) :
    (0 : ℝ) =
    ∫ x in UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + ε * ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (γBarReal / 2)
          + ε * |sol.u x| ^ γBarReal)
        ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  strongTransport_at_uEpsi_unconditional sol h hβBarPaper hγBarPaper
    hmeas_pos hmeas_neg hStep_pos hStep_neg

/-! ### iter db57a9 Phase 2 — paper-faithful tendsto wrapper for the
**indicator-scaling** signed perturbation
`μ_n := m + (1/(n+1)) · σ · (m · 1_S)` (with limit `μ_∞ = m`).

Closes Phase 2 of the iter-0622 v2 plan: produces the operator-continuity
`Tendsto` certificate at the `paperSolFor-side-inputs` `hCont_signed`
shape directly from `(sol, paper hypotheses)`, with no per-query
`(Gh, hGh_memLp, hGh_bd)` authorisation.

The headline tendsto already exists as
`mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses`
(this module, ~line 26580), which consumes an HJB envelope
`(Gh, hGh_memLp, hGh_bd)` plus the test-data measurabilities and the
non-negativity `m ≥ 0`. The present wrapper closes those inputs by:

* deriving the measurabilities of `m, u, V, Du` from
  `sol.{hmLp, huLp, hDuLp}` and `hV.aestronglyMeasurable.aemeasurable`
  via `.aemeasurable.mk` (which gives a true `Measurable` from the
  AE-measurable representative);
* picking the explicit envelope
  `Gh x := h.C · (‖Du‖^α + 1) + h.C · ((2·|m x|)^β + 1) + |u x| + |V x|`,
  whose `MemLpPer ((β+1)/β)` certificate follows from
  `g_dominator_memLp_betaBar'` at the test mass `μ := 2 · |m|` and
  whose pointwise bound is `H_abs_bound_nonneg_of_hHat0` (which handles
  the `m_x = 0` boundary case via the right-continuity bridge).

This is the analogue, for the signed-indicator-scaling shape, of the
iter-0617 `residueOf_signed` supplier, with the difference that the
envelope is fully constructed in-body from `sol` rather than supplied
as a per-query bundle. -/

-- Adapted from `mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses`
-- (this module, ~line 26580) with the `(Gh, hGh_memLp, hGh_bd)` envelope
-- discharged in-body from `g_dominator_memLp_betaBar'` and
-- `H_abs_bound_nonneg_of_hHat0`.
theorem mfgOperatorEpsPair_tendsto_signed_indicator_scaling_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε γBar : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hHFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV_memLp_betap : Periodic.MemLpPer
                  (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hV_meas : Measurable V)
    {βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              βBarReal' γBarReal')
    (hm_meas : Measurable sol.m)
    (hu_meas : Measurable sol.u)
    (hDu_meas : ∀ i, Measurable (sol.Du i))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hγBarEq : γBar = Hamiltonian.gammaBar hpow.α hpow.β) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          sol.Du
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            sol.Du sol.m sol.u
            (fun _ _ => (0 : ℝ))
            (fun x => σ * sol.m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)))) := by
  -- Standing positivity facts.
  have hα_pos : 0 < hpow.α := lt_trans one_pos hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  have hβp_pos : 0 < (hpow.β + 1) / hpow.β := div_pos hbb_pos hβ_pos
  have hγb_pos : 0 < hpow.α * (hpow.β + 1) / hpow.β :=
    div_pos (mul_pos hα_pos hbb_pos) hβ_pos
  -- `m ∈ L^{β+1}_per` (from sol).
  have hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) sol.m :=
    sol.hmLp
  -- `m ≥ 0` a.e. (from sol).
  have hm_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ sol.m x :=
    sol.hmNonneg
  -- Build the test mass `μ_env := fun x => 2 * |m x|` and its
  -- `MemLpPer (β+1)` certificate (used to call
  -- `g_dominator_memLp_betaBar'`).
  set μEnv : (Fin d → ℝ) → ℝ := fun x => 2 * |sol.m x| with hμEnv_def
  have hμEnv_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) μEnv := by
    -- `|m| ∈ MemLpPer (β+1)` via `MemLp.norm`, then scale by 2.
    have h_abs : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
                  (fun x => |sol.m x|) := by
      have := hm_memLp.toMemLp.norm
      have h := MemLp.toMemLpPer this
      have heq : (fun x : (Fin d → ℝ) => ‖sol.m x‖)
                = (fun x : (Fin d → ℝ) => |sol.m x|) := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at h
      exact h
    have h_smul := Periodic.MemLpPer.const_smul (𝕜 := ℝ) h_abs 2
    have heq : ((2 : ℝ) • fun x : (Fin d → ℝ) => |sol.m x|)
              = μEnv := by
      funext x; simp [hμEnv_def, Pi.smul_apply, smul_eq_mul]
    rw [heq] at h_smul
    exact h_smul
  -- `u ∈ L^{γ̄}_per` (from sol). The exponent matches `γ̄ := α(β+1)/β`.
  have hu_memLp_γ :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        sol.u := by
    have := sol.huLp
    simpa [Hamiltonian.gammaBar] using this
  -- Same for each Du i.
  have hDu_memLp_γ : ∀ i,
      Periodic.MemLpPer (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        (sol.Du i) := by
    intro i
    have := sol.hDuLp i
    simpa [Hamiltonian.gammaBar] using this
  -- Use `g_dominator_memLp_betaBar'` to build the envelope
  -- `Gh x := h.C · (‖Du‖^α + 1) + h.C · (μEnv x ^ β + 1) + |u x| + |V x|`.
  set Gh : (Fin d → ℝ) → ℝ :=
    fun x => hpow.C * (‖fun i => sol.Du i x‖ ^ hpow.α + 1)
              + hpow.C * (μEnv x ^ hpow.β + 1)
              + |sol.u x| + |V x| with hGh_def
  have hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh := by
    -- `g_dominator_memLp_betaBar'` builds
    -- `C' · (‖Dυ‖^α + 1) + h.C · (μ^β + 1) + |υ| + |V|` at `C' := h.C`.
    have h := Hamiltonian.g_dominator_memLp_betaBar' hpow V sol.u μEnv
      sol.Du hμEnv_memLp hu_memLp_γ hDu_memLp_γ hV_memLp_betap hpow.hC
    exact h
  -- Pointwise dominator bound via `H_abs_bound_nonneg_of_hHat0`.
  have hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖-(sol.u x) - H x (fun i => sol.Du i x)
              (sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V x‖
          ≤ Gh x := by
    intro n
    have habs :=
      Hamiltonian.H_abs_bound_nonneg_of_hHat0 hpow hHat0 hHFin hAgree
    have hσ_abs : |σ| ≤ 1 := by rcases hσ with h | h <;> simp [h]
    -- `1/(n+1) ∈ [0, 1]`.
    have h_one_div_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact le_of_lt (div_pos one_pos this)
    have h_one_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    filter_upwards [habs, hm_nn] with x hx_abs hx_m_nn
    -- Setup `μn := m + (1/(n+1)) · σ · (m · 1_S)` at this `x`.
    set μn : ℝ := sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                  (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      with hμn_def
    -- Indicator bound.
    have hInd_nn : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_notMem hxS]
    have hInd_le_one : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_notMem hxS]
    -- `μn = m * (1 + (1/(n+1)) · σ · 1_S(x))`.
    -- The factor `(1 + (1/(n+1)) · σ · 1_S(x))` satisfies `[0, 2]`:
    -- lower: `(1/(n+1)) · σ · 1_S ≥ -1 · 1 = -1` (since `|σ| ≤ 1`, ind ≤ 1).
    -- upper: `(1/(n+1)) · σ · 1_S ≤ 1`.
    have h_factor_nn : 0 ≤ 1 + (1 / ((n : ℝ) + 1)) * σ *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      -- |tn · σ · 1_S| ≤ 1 · 1 · 1 = 1.
      have h_prod_abs :
          |(1 / ((n : ℝ) + 1)) * σ *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
        rw [abs_mul, abs_mul]
        have h_one_div_abs : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
          rw [abs_of_nonneg h_one_div_nn]; exact h_one_div_le_one
        have h_ind_abs :
            |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
          rw [abs_of_nonneg hInd_nn]; exact hInd_le_one
        have h1 : |1 / ((n : ℝ) + 1)| * |σ|
                  ≤ 1 * 1 :=
          mul_le_mul h_one_div_abs hσ_abs (abs_nonneg _) zero_le_one
        have h2 : |1 / ((n : ℝ) + 1)| * |σ| *
                    |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                  ≤ 1 * 1 * 1 :=
          mul_le_mul h1 h_ind_abs (abs_nonneg _) (by norm_num)
        linarith [h2]
      have h_prod_ge_neg_one :
          -1 ≤ (1 / ((n : ℝ) + 1)) * σ *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        have := neg_abs_le ((1 / ((n : ℝ) + 1)) * σ *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        linarith [h_prod_abs]
      linarith
    have h_factor_le_two : 1 + (1 / ((n : ℝ) + 1)) * σ *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 2 := by
      have h_prod_abs :
          |(1 / ((n : ℝ) + 1)) * σ *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
        rw [abs_mul, abs_mul]
        have h_one_div_abs : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
          rw [abs_of_nonneg h_one_div_nn]; exact h_one_div_le_one
        have h_ind_abs :
            |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
          rw [abs_of_nonneg hInd_nn]; exact hInd_le_one
        have h1 : |1 / ((n : ℝ) + 1)| * |σ|
                  ≤ 1 * 1 :=
          mul_le_mul h_one_div_abs hσ_abs (abs_nonneg _) zero_le_one
        have h2 : |1 / ((n : ℝ) + 1)| * |σ| *
                    |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                  ≤ 1 * 1 * 1 :=
          mul_le_mul h1 h_ind_abs (abs_nonneg _) (by norm_num)
        linarith [h2]
      have h_prod_le_one :
          (1 / ((n : ℝ) + 1)) * σ *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 :=
        le_of_abs_le h_prod_abs
      linarith
    -- `μn = m * factor`, hence `μn ≥ 0` (m ≥ 0, factor ≥ 0).
    have hμn_eq : μn = sol.m x * (1 + (1 / ((n : ℝ) + 1)) * σ *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      rw [hμn_def]; ring
    have hμn_nn : 0 ≤ μn := by
      rw [hμn_eq]; exact mul_nonneg hx_m_nn h_factor_nn
    -- `μn ≤ 2 · m = 2 · |m|` (since `m ≥ 0`, `|m| = m`).
    have hμn_le : μn ≤ 2 * |sol.m x| := by
      rw [hμn_eq]
      have h_mabs : |sol.m x| = sol.m x := abs_of_nonneg hx_m_nn
      rw [h_mabs]
      calc sol.m x * (1 + (1 / ((n : ℝ) + 1)) * σ *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          ≤ sol.m x * 2 := by
            exact mul_le_mul_of_nonneg_left h_factor_le_two hx_m_nn
        _ = 2 * sol.m x := by ring
    -- Apply `H_abs_bound_nonneg_of_hHat0` at `μn` (since `μn ≥ 0`).
    have hH_bd := hx_abs (fun i => sol.Du i x) μn hμn_nn
    -- `|H(p, μn)| ≤ C(‖p‖^α + 1) + C(μn^β + 1)`.
    -- We need `μn^β ≤ (2|m|)^β = μEnv^β` (monotonicity of `^β` on `[0,∞)`).
    have hμEnv_at : μEnv x = 2 * |sol.m x| := rfl
    have hμn_β_le : μn ^ hpow.β ≤ μEnv x ^ hpow.β := by
      rw [hμEnv_at]
      exact Real.rpow_le_rpow hμn_nn hμn_le hβ_pos.le
    have hμEnv_nn_x : 0 ≤ μEnv x := by
      rw [hμEnv_at]
      have : 0 ≤ |sol.m x| := abs_nonneg _
      linarith
    -- Now combine via triangle: `|-u - H(Du, μn) + V| ≤ |u| + |H| + |V|`.
    have habs1 : |-(sol.u x) - H x (fun i => sol.Du i x) μn + V x|
        ≤ |-(sol.u x) - H x (fun i => sol.Du i x) μn| + |V x| := abs_add_le _ _
    have habs2 : |-(sol.u x) - H x (fun i => sol.Du i x) μn|
        ≤ |sol.u x| + |H x (fun i => sol.Du i x) μn| := by
      have := abs_sub (-(sol.u x)) (H x (fun i => sol.Du i x) μn)
      rw [abs_neg] at this
      linarith
    have hC_nn : 0 ≤ hpow.C := hpow.hC.le
    have hα_term_nn : 0 ≤ ‖fun i => sol.Du i x‖ ^ hpow.α + 1 := by
      have h1 : 0 ≤ ‖fun i => sol.Du i x‖ ^ hpow.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      linarith
    have hH_abs_env : |H x (fun i => sol.Du i x) μn|
        ≤ hpow.C * (‖fun i => sol.Du i x‖ ^ hpow.α + 1)
            + hpow.C * (μEnv x ^ hpow.β + 1) := by
      have hμn_β_nn : 0 ≤ μn ^ hpow.β := Real.rpow_nonneg hμn_nn _
      have h1 : hpow.C * (μn ^ hpow.β + 1)
            ≤ hpow.C * (μEnv x ^ hpow.β + 1) := by
        apply mul_le_mul_of_nonneg_left _ hC_nn
        linarith
      linarith
    -- Conclude.
    show ‖-(sol.u x) - H x (fun i => sol.Du i x) μn + V x‖ ≤ Gh x
    rw [Real.norm_eq_abs]
    simp only [hGh_def]
    linarith [habs1, habs2, hH_abs_env]
  -- Apply the existing closed-form aggregator.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses
      (V := V) (H := H) (DpH := DpH) (ε := ε) (γBar := γBar)
      hpow hRegH hHat0 hHFin hAgree
      sol.Du sol.u sol.m σ hσ S hS
      hm_meas hV_meas hu_meas hDu_meas hm_nn hm_memLp
      Gh hGh_memLp hGh_bd
  exact h_tendsto

/-! ## Step 1 of iter-0694 split — named test points and `K_Aepsi_W` membership

Per `paperSolFor-final-phase5-hWeakDeriv-step1-test-point-K_Aepsi_W-mem`,
the producers `hVIeps_set_of_KAepsi_VI`, `hVIeps_signed_of_KAepsi_VI`,
and `hVIeps_transport_of_KAepsi_VI` build inline `qn := banachPairOfBare …`
test points at each `n : ℕ`. To enable the refined-cone Browder–Minty
path (which runs `Monotone.monotone_abstract_weak` on `K_Aepsi_W` rather
than `K_Aepsi`), these test points must be exposed as named definitions
with companion lemmas asserting their `K_Aepsi_W` membership.

The three named definitions in this section mirror the inline blocks
(line ~256 for `set`, line ~584 for `signed`, line ~1497 for
`transport`). The companion membership lemmas use:
* `aePeriodic_DuOf` from `AssemblyContext.lean:3663` for the `S_AE`
  half of `K_Aepsi_W` (this slot is automatic because
  `S_AE = Set.univ` for every `XBanach`).
* `HasWeakDerivPer.congr_ae_unitCube` from `SobolevPoincare.lean:3226`
  for the `S_W` half — the bare-function weak-derivative tie
  `HasWeakDerivPer i υ (Dυ i)` transports through a.e.-eq of both `u`
  and `Du` components to the `Lp`-side coercions
  `⇑(toLp υ), ⇑(toLp (Dυ i))`.
* The existing positivity argument (verbatim from the inline
  `hqn_K` blocks) for the `K_Aepsi` half.

The Step 1c threading refactor (rewiring each producer to consume the
new named defs) is a follow-up child; the present section adds the
definitions and membership lemmas without touching the producers.
-/

section TestPointKAepsiW

variable {βBarReal γBarReal : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-! ### Set-family test point (Child C — `hVIeps_set_of_KAepsi_VI`)

Mirrors the inline `qn` block at lines 256-258 of this file. Given a
paper test triple `(S, ρ, υ, Dυ)` with `0 ≤ ρ a.e.`, the perturbed
test point at level `n : ℕ` is

  `qn := banachPairOfBare (S.indicator ρ + 1/(n+1)) υ Dυ ⋯`

with `m`-component `MemLpPer` certificate built by adding the
constant `1/(n+1)` to `S.indicator ρ`. -/

/-- **Set-family test point at perturbation level `n`.** Named version
of the inline `qn := banachPairOfBare …` block in
`hVIeps_set_of_KAepsi_VI`. -/
noncomputable def setFamily_test_point_perturbed
    (n : ℕ) {S : Set (Fin d → ℝ)}
    {ρ υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hSρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (S.indicator ρ))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) :
    XBanach d βBarReal γBarReal :=
  let hcst_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
    MemLp.toMemLpPer (memLp_const _)
  let hμn_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    show MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (((S.indicator ρ : (Fin d → ℝ) → ℝ)
            + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))) from
      MemLpPer.add hSρ_memLp hcst_memLp
  banachPairOfBare (m := fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
    (u := υ) (Du := Dυ) hμn_memLp hυ_memSob hDυ_memLp

/-- **K_Aepsi_W membership of the set-family test point.** Discharges
the three slots of `mem_K_Aepsi_W_iff`:
1. `K_Aepsi`: positivity of `S.indicator ρ + 1/(n+1)` a.e. (via
   `0 ≤ ρ a.e.` and `1/(n+1) > 0`).
2. `S_AE`: automatic via `aePeriodic_DuOf` (every `XBanach`
   gradient is AEPeriodic — `S_AE = univ`).
3. `S_W` / `HasWeakDerivPer`: transport `hWeak_υ` through
   `HasWeakDerivPer.congr_ae_unitCube`, using `MemLp.coeFn_toLp` as
   the witness for a.e.-eq of `u, Du` to their bare originals. -/
theorem setFamily_test_point_perturbed_mem_K_Aepsi_W
    (n : ℕ) {S : Set (Fin d → ℝ)}
    {ρ υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (S.indicator ρ))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) :
    setFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n hSρ_memLp hυ_memSob hDυ_memLp
      ∈ K_Aepsi_W d βBarReal γBarReal := by
  classical
  set qn : XBanach d βBarReal γBarReal :=
    setFamily_test_point_perturbed (βBarReal := βBarReal)
      (γBarReal := γBarReal) n hSρ_memLp hυ_memSob hDυ_memLp with hqn_def
  -- The `MemLpPer` certificate that the `banachPairOfBare` consumed.
  have hcst_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
    MemLp.toMemLpPer (memLp_const _)
  have hμn_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
    show MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (((S.indicator ρ : (Fin d → ℝ) → ℝ)
            + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))) from
      MemLpPer.add hSρ_memLp hcst_memLp
  -- Identify `qn` componentwise with the `toLp` images.
  have hqn1 : qn.1 = hμn_memLp.toLp := rfl
  have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
  have hqn22 : ∀ i, qn.2.2 i = (hDυ_memLp i).toLp := fun _ => rfl
  -- a.e.-equality of `⇑qn.1` to the bare perturbation.
  have hqn1_ae :
      (⇑qn.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) := by
    rw [hqn1]
    exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
  -- a.e.-equality of `⇑qn.2.1` to `υ`.
  have hqn21_ae :
      (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
    rw [hqn21]
    exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
  -- a.e.-equality of `⇑(qn.2.2 i)` to `Dυ i`.
  have hqn22_ae : ∀ i,
      (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
    intro i
    rw [hqn22 i]
    exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
  refine ⟨?_, ?_, ?_⟩
  · -- K_Aepsi: positivity a.e.
    -- `0 ≤ S.indicator ρ a.e.` from `0 ≤ ρ a.e.`.
    have hSρ_nn :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 ≤ S.indicator ρ x := by
      filter_upwards [hρ_nn] with x hxρ
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS, hxρ]
      · simp [Set.indicator_of_notMem hxS]
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < S.indicator ρ x + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hSρ_nn] with x hxnn
      linarith
    show ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
    filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
    rw [hx_eq]; exact hx_pos
  · -- S_AE: automatic.
    intro i
    exact aePeriodic_DuOf qn i
  · -- S_W / HasWeakDerivPer: transport via congr_ae_unitCube.
    intro i
    have hWeak_i : HasWeakDerivPer (d := d) i υ (Dυ i) := hWeak_υ i
    -- We need `HasWeakDerivPer i (uOf qn) (DuOf qn i)`, i.e.
    -- `HasWeakDerivPer i ⇑qn.2.1 ⇑(qn.2.2 i)`.
    -- Use `congr_ae_unitCube` with `f := υ → f' := ⇑qn.2.1` (via
    -- symmetry of `hqn21_ae`) and `g := Dυ i → g' := ⇑(qn.2.2 i)`.
    have hf_ae :
        υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑qn.2.1 : (Fin d → ℝ) → ℝ) := hqn21_ae.symm
    have hg_ae :
        Dυ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ) := (hqn22_ae i).symm
    -- `MemLpPer 1 (⇑(qn.2.2 i))` from finite-measure embedding.
    have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
    have hDuOf_qn_memLp1 :
        MemLpPer (d := d) 1 ((⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)) :=
      StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d) (qn.2.2 i))
    -- Apply the congr lemma.
    have := hWeak_i.congr_ae_unitCube hf_ae hDuOf_qn_memLp1 hg_ae
    -- Goal is `HasWeakDerivPer i (uOf qn) (DuOf qn i)`; unfold defs.
    show HasWeakDerivPer (d := d) i (uOf qn) (DuOf qn i)
    simp only [uOf_def, DuOf_def]
    exact this

/-! ### Transport-family test point (Child D — `hVIeps_transport_of_KAepsi_VI`)

Mirrors the inline `qn` block at lines 1497-1499. Given a paper test
triple `(σ, υ, φ)` with `0 ≤ σ a.e.`, the perturbed test point at
level `n : ℕ` is

  `qn := banachPairOfBare (σ + 1/(n+1)) υ φ ⋯`. -/

/-- **Transport-family test point at perturbation level `n`.** -/
noncomputable def transportFamily_test_point_perturbed
    (n : ℕ) {σ υ : (Fin d → ℝ) → ℝ} {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hσ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hφ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) :
    XBanach d βBarReal γBarReal :=
  let hcst_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
    MemLp.toMemLpPer (memLp_const _)
  let hμn_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => σ x + 1 / ((n : ℝ) + 1)) :=
    show MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (((σ : (Fin d → ℝ) → ℝ)
            + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))) from
      MemLpPer.add hσ_memLp hcst_memLp
  banachPairOfBare (m := fun x => σ x + 1 / ((n : ℝ) + 1))
    (u := υ) (Du := φ) hμn_memLp hυ_memSob hφ_memLp

/-- **K_Aepsi_W membership of the transport-family test point.**
Same recipe as `setFamily_test_point_perturbed_mem_K_Aepsi_W`, with
`σ` in place of `S.indicator ρ` and `φ` in place of `Dυ`. -/
theorem transportFamily_test_point_perturbed_mem_K_Aepsi_W
    (n : ℕ) {σ υ : (Fin d → ℝ) → ℝ} {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hσ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x)
    (hσ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hφ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (φ i)) :
    transportFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n hσ_memLp hυ_memSob hφ_memLp
      ∈ K_Aepsi_W d βBarReal γBarReal := by
  classical
  set qn : XBanach d βBarReal γBarReal :=
    transportFamily_test_point_perturbed (βBarReal := βBarReal)
      (γBarReal := γBarReal) n hσ_memLp hυ_memSob hφ_memLp with hqn_def
  have hcst_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
    MemLp.toMemLpPer (memLp_const _)
  have hμn_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => σ x + 1 / ((n : ℝ) + 1)) :=
    show MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (((σ : (Fin d → ℝ) → ℝ)
            + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))) from
      MemLpPer.add hσ_memLp hcst_memLp
  have hqn1 : qn.1 = hμn_memLp.toLp := rfl
  have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
  have hqn22 : ∀ i, qn.2.2 i = (hφ_memLp i).toLp := fun _ => rfl
  have hqn1_ae :
      (⇑qn.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        fun x => σ x + 1 / ((n : ℝ) + 1) := by
    rw [hqn1]; exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
  have hqn21_ae :
      (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
    rw [hqn21]; exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
  have hqn22_ae : ∀ i,
      (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] φ i := by
    intro i
    rw [hqn22 i]
    exact MeasureTheory.MemLp.coeFn_toLp (hφ_memLp i)
  refine ⟨?_, ?_, ?_⟩
  · have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < σ x + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hσ_nn] with x hxnn
      linarith
    show ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
    filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
    rw [hx_eq]; exact hx_pos
  · intro i; exact aePeriodic_DuOf qn i
  · intro i
    have hWeak_i : HasWeakDerivPer (d := d) i υ (φ i) := hWeak_υ i
    have hf_ae :
        υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑qn.2.1 : (Fin d → ℝ) → ℝ) := hqn21_ae.symm
    have hg_ae :
        φ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ) := (hqn22_ae i).symm
    have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
    have hDuOf_qn_memLp1 :
        MemLpPer (d := d) 1 ((⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)) :=
      StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d) (qn.2.2 i))
    have := hWeak_i.congr_ae_unitCube hf_ae hDuOf_qn_memLp1 hg_ae
    show HasWeakDerivPer (d := d) i (uOf qn) (DuOf qn i)
    simp only [uOf_def, DuOf_def]
    exact this

/-! ### Signed-family test point (Child D — `hVIeps_signed_of_KAepsi_VI`)

Mirrors the inline `qn` block at lines 584-585. Given an existing
Banach point `q` plus a sign `σ ∈ {±1}` and measurable set `S`, the
perturbed test point at level `n : ℕ` is

  `qn := (q.1 + (σ · mOf q · 1_S + 1/(n+1))_Lp, q.2)`.

Crucially, `qn.2 = q.2` (literally), so `uOf qn = uOf q` and
`DuOf qn = DuOf q` definitionally. The `K_Aepsi_W` slots for `S_AE`
and `S_W` therefore *inherit* from `q ∈ K_Aepsi_W`. -/

/-- **Signed-family test point at perturbation level `n`.** -/
noncomputable def signedFamily_test_point_perturbed
    (n : ℕ) (q : XBanach d βBarReal γBarReal)
    (σ : ℝ) {S : Set (Fin d → ℝ)}
    (hSσm_const_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))) :
    XBanach d βBarReal γBarReal :=
  (q.1 + hSσm_const_memLp.toLp, q.2)

/-- **K_Aepsi_W membership of the signed-family test point.** The
proof reuses `q ∈ K_Aepsi_W` for the `S_AE` and `S_W` slots (since
`uOf qn = uOf q` and `DuOf qn i = DuOf q i` definitionally), and the
existing inline positivity proof for the `K_Aepsi` slot. The
non-negativity of `mOf q` is read off from `q ∈ K_Aepsi_W` via
`K_Aepsi_W_subset_K_Aepsi` and strict positivity of `mOf q`. -/
theorem signedFamily_test_point_perturbed_mem_K_Aepsi_W
    (n : ℕ) (q : XBanach d βBarReal γBarReal)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {S : Set (Fin d → ℝ)}
    (hSσm_const_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)))
    (hq_W : q ∈ K0_Aepsi_W d βBarReal γBarReal)
    (hm_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x) :
    signedFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n q σ hSσm_const_memLp
      ∈ K_Aepsi_W d βBarReal γBarReal := by
  classical
  set qn : XBanach d βBarReal γBarReal :=
    signedFamily_test_point_perturbed (βBarReal := βBarReal)
      (γBarReal := γBarReal) n q σ hSσm_const_memLp with hqn_def
  -- Componentwise identification.
  have hqn1 : qn.1 = q.1 + hSσm_const_memLp.toLp := rfl
  have hqn2 : qn.2 = q.2 := rfl
  have hqn21 : qn.2.1 = q.2.1 := by rw [hqn2]
  have hqn22 : ∀ i, qn.2.2 i = q.2.2 i := by intro i; rw [hqn2]
  -- a.e.-equality of `⇑qn.1` to the perturbed `m`-bare.
  have hqn1_ae :
      (⇑qn.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        fun x => mOf q x + σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) := by
    rw [hqn1]
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
    show mOf q x + (σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
            = mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- K_Aepsi: positivity from `m ≥ 0`, `σ ∈ {±1}`, and `1/(n+1) > 0`.
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
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
          have h1σ_nn : (0 : ℝ) ≤ 1 + σ := by
            rcases hσ with hσ | hσ
            · rw [hσ]; norm_num
            · rw [hσ]; norm_num
          exact mul_nonneg hxnn h1σ_nn
        · rw [Set.indicator_of_notMem hxS]
          simpa using hxnn
      linarith
    show ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
    filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
    rw [hx_eq]; exact hx_pos
  · -- S_AE: `DuOf qn i = DuOf q i` definitionally; reuse `hq_W.2.1`.
    intro i
    have h_eq : DuOf qn i = DuOf q i := by
      simp only [DuOf_def]; rw [hqn22 i]
    rw [h_eq]; exact hq_W.2.1 i
  · -- S_W: `uOf qn = uOf q` and `DuOf qn i = DuOf q i` definitionally;
    -- reuse `hq_W.2.2`.
    intro i
    have h_u : uOf qn = uOf q := by simp only [uOf_def]; rw [hqn21]
    have h_Du : DuOf qn i = DuOf q i := by
      simp only [DuOf_def]; rw [hqn22 i]
    rw [h_u, h_Du]
    exact hq_W.2.2 i

/-! ### Signed user-probe family test point (Child D′ —
`hVIeps_signed_user_probe_of_KAepsi_VI`)

Mirrors the inline `qn` block at line 943 of this file. Unlike the
signed family (where `qn.2 = q.2`), the signed user-probe family
inline-builds

  `qn := banachPairOfBare (m := mOf q + σ · mOf q · 1_S + 1/(n+1))
                          (u := υ) (Du := Dυ) ⋯`

so `qn.2 = (υ, Dυ).toLp` is user-supplied. The K_Aepsi_W
weak-derivative tie is therefore NOT inherited from `q ∈ K0_Aepsi_W`
and the test-point membership lemma carries an extra
`hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)` hypothesis (paper-faithful;
in the paper the test direction is in the Sobolev space and the
weak-derivative tie is automatic). -/

/-- **Signed user-probe family test point at perturbation level `n`.**
Named version of the inline `qn := banachPairOfBare …` block in
`hVIeps_signed_user_probe_of_KAepsi_VI`. -/
noncomputable def signedUserProbeFamily_test_point_perturbed
    (n : ℕ) (q : XBanach d βBarReal γBarReal)
    (σ : ℝ) {S : Set (Fin d → ℝ)}
    {υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμn_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => mOf q x + σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) :
    XBanach d βBarReal γBarReal :=
  banachPairOfBare (m := fun x => mOf q x + σ * mOf q x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                                  + 1 / ((n : ℝ) + 1))
    (u := υ) (Du := Dυ) hμn_memLp hυ_memSob hDυ_memLp

/-- **K_Aepsi_W membership of the signed user-probe family test point.**
Same recipe as `setFamily_test_point_perturbed_mem_K_Aepsi_W`, with
`mOf q + σ · mOf q · 1_S` in place of `S.indicator ρ`. The strict-
positive admissibility uses `mOf q ≥ 0` a.e. (from `q ∈ K0_Aepsi`,
descended from `q ∈ K0_Aepsi_W` by `K0_Aepsi_W_subset_K0_Aepsi`) and
`σ ∈ {±1}` (so `1 + σ · 1_S ∈ [0, 2]`). -/
theorem signedUserProbeFamily_test_point_perturbed_mem_K_Aepsi_W
    (n : ℕ) (q : XBanach d βBarReal γBarReal)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {S : Set (Fin d → ℝ)}
    {υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμn_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => mOf q x + σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    (hm_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x) :
    signedUserProbeFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n q σ hμn_memLp hυ_memSob hDυ_memLp
      ∈ K_Aepsi_W d βBarReal γBarReal := by
  classical
  set qn : XBanach d βBarReal γBarReal :=
    signedUserProbeFamily_test_point_perturbed (βBarReal := βBarReal)
      (γBarReal := γBarReal) n q σ hμn_memLp hυ_memSob hDυ_memLp with hqn_def
  -- Componentwise identification with the `toLp` images.
  have hqn1 : qn.1 = hμn_memLp.toLp := rfl
  have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
  have hqn22 : ∀ i, qn.2.2 i = (hDυ_memLp i).toLp := fun _ => rfl
  -- a.e.-equality of `⇑qn.1` to the bare perturbation.
  have hqn1_ae :
      (⇑qn.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        fun x => mOf q x + σ * mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) := by
    rw [hqn1]; exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
  -- a.e.-equality of `⇑qn.2.1` to `υ`.
  have hqn21_ae :
      (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
    rw [hqn21]; exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
  -- a.e.-equality of `⇑(qn.2.2 i)` to `Dυ i`.
  have hqn22_ae : ∀ i,
      (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
    intro i
    rw [hqn22 i]
    exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
  refine ⟨?_, ?_, ?_⟩
  · -- K_Aepsi: positivity from `m ≥ 0`, `σ ∈ {±1}`, and `1/(n+1) > 0`.
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
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
          have h1σ_nn : (0 : ℝ) ≤ 1 + σ := by
            rcases hσ with hσ | hσ
            · rw [hσ]; norm_num
            · rw [hσ]; norm_num
          exact mul_nonneg hxnn h1σ_nn
        · rw [Set.indicator_of_notMem hxS]
          simpa using hxnn
      linarith
    show ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
    filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
    rw [hx_eq]; exact hx_pos
  · -- S_AE: automatic via `aePeriodic_DuOf`.
    intro i
    exact aePeriodic_DuOf qn i
  · -- S_W / HasWeakDerivPer: transport `hWeak_υ` via congr_ae_unitCube.
    intro i
    have hWeak_i : HasWeakDerivPer (d := d) i υ (Dυ i) := hWeak_υ i
    have hf_ae :
        υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑qn.2.1 : (Fin d → ℝ) → ℝ) := hqn21_ae.symm
    have hg_ae :
        Dυ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ) := (hqn22_ae i).symm
    have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
    have hDuOf_qn_memLp1 :
        MemLpPer (d := d) 1 ((⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)) :=
      StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d) (qn.2.2 i))
    have := hWeak_i.congr_ae_unitCube hf_ae hDuOf_qn_memLp1 hg_ae
    show HasWeakDerivPer (d := d) i (uOf qn) (DuOf qn i)
    simp only [uOf_def, DuOf_def]
    exact this

/-! ### Signed user-triple family test point (Child D″ user-triple, W-form)

W-form sibling of the inline `qn` block in
`hVIeps_signed_user_triple_of_KAepsi_VI`. Differs from the user-probe
variant by taking the primal density `μ` from the user (rather than
`mOf q`); the perturbed test point at level `n : ℕ` is

  `qn := banachPairOfBare (μ + σ · μ · 1_S + 1/(n+1)) υ Dυ ⋯`. -/

/-- **Signed user-triple family test point at perturbation level `n`.**
Named version of the inline `qn := banachPairOfBare …` block in
`hVIeps_signed_user_triple_of_KAepsi_VI`. -/
noncomputable def signedUserTripleFamily_test_point_perturbed
    (n : ℕ) (σ : ℝ) {S : Set (Fin d → ℝ)}
    {μ υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμn_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) :
    XBanach d βBarReal γBarReal :=
  banachPairOfBare (m := fun x => μ x + σ * μ x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                                  + 1 / ((n : ℝ) + 1))
    (u := υ) (Du := Dυ) hμn_memLp hυ_memSob hDυ_memLp

/-- **K_Aepsi_W membership of the signed user-triple family test point.**
Same recipe as `signedUserProbeFamily_test_point_perturbed_mem_K_Aepsi_W`,
with the user-supplied `μ` in place of `mOf q`. Strict-positive
admissibility uses `μ ≥ 0` a.e. and `σ ∈ {±1}` (so
`1 + σ · 1_S ∈ [0, 2]`). The weak-derivative slot needs the explicit
`hWeak_υ` hypothesis since `υ`/`Dυ` are user-supplied. -/
theorem signedUserTripleFamily_test_point_perturbed_mem_K_Aepsi_W
    (n : ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    {S : Set (Fin d → ℝ)}
    {μ υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμn_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    (hμ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) :
    signedUserTripleFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n σ hμn_memLp hυ_memSob hDυ_memLp
      ∈ K_Aepsi_W d βBarReal γBarReal := by
  classical
  set qn : XBanach d βBarReal γBarReal :=
    signedUserTripleFamily_test_point_perturbed (βBarReal := βBarReal)
      (γBarReal := γBarReal) n σ hμn_memLp hυ_memSob hDυ_memLp with hqn_def
  -- Componentwise identification with the `toLp` images.
  have hqn1 : qn.1 = hμn_memLp.toLp := rfl
  have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
  have hqn22 : ∀ i, qn.2.2 i = (hDυ_memLp i).toLp := fun _ => rfl
  -- a.e.-equality of `⇑qn.1` to the bare perturbation.
  have hqn1_ae :
      (⇑qn.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        fun x => μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) := by
    rw [hqn1]; exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
  -- a.e.-equality of `⇑qn.2.1` to `υ`.
  have hqn21_ae :
      (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
    rw [hqn21]; exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
  -- a.e.-equality of `⇑(qn.2.2 i)` to `Dυ i`.
  have hqn22_ae : ∀ i,
      (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
    intro i
    rw [hqn22 i]
    exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
  refine ⟨?_, ?_, ?_⟩
  · -- K_Aepsi: positivity from `μ ≥ 0`, `σ ∈ {±1}`, and `1/(n+1) > 0`.
    have hcst_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have hμn_pos_ae :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 < μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1) := by
      filter_upwards [hμ_nn] with x hxnn
      have hadd_nn : 0 ≤ μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        by_cases hxS : x ∈ S
        · rw [Set.indicator_of_mem hxS]
          have : μ x + σ * μ x * 1 = μ x * (1 + σ) := by ring
          rw [this]
          have h1σ_nn : (0 : ℝ) ≤ 1 + σ := by
            rcases hσ with hσ | hσ
            · rw [hσ]; norm_num
            · rw [hσ]; norm_num
          exact mul_nonneg hxnn h1σ_nn
        · rw [Set.indicator_of_notMem hxS]
          simpa using hxnn
      linarith
    show ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            0 < (⇑qn.1 : (Fin d → ℝ) → ℝ) x
    filter_upwards [hqn1_ae, hμn_pos_ae] with x hx_eq hx_pos
    rw [hx_eq]; exact hx_pos
  · -- S_AE: automatic via `aePeriodic_DuOf`.
    intro i
    exact aePeriodic_DuOf qn i
  · -- S_W / HasWeakDerivPer: transport `hWeak_υ` via congr_ae_unitCube.
    intro i
    have hWeak_i : HasWeakDerivPer (d := d) i υ (Dυ i) := hWeak_υ i
    have hf_ae :
        υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑qn.2.1 : (Fin d → ℝ) → ℝ) := hqn21_ae.symm
    have hg_ae :
        Dυ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ) := (hqn22_ae i).symm
    have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
    have hDuOf_qn_memLp1 :
        MemLpPer (d := d) 1 ((⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)) :=
      StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d) (qn.2.2 i))
    have := hWeak_i.congr_ae_unitCube hf_ae hDuOf_qn_memLp1 hg_ae
    show HasWeakDerivPer (d := d) i (uOf qn) (DuOf qn i)
    simp only [uOf_def, DuOf_def]
    exact this

end TestPointKAepsiW

/-! ## W-form Minty supplier — `hVIeps_set_of_KAepsi_W_VI`

Iter-0701 Phase 1 of the `paperSolFor-final-phase5-hWeakDeriv`
6-phase plan. W-form sibling of `hVIeps_set_of_KAepsi_VI` (line 160),
swapping:

* `hVI` quantifier: `q' ∈ K_Aepsi → q' ∈ K_Aepsi_W` (refined cone,
  iter 0687).
* Test pair `(υ, Dυ)`: an extra hypothesis
  `hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)` is required to land
  the per-`n` perturbation test point in `K_Aepsi_W`. This is
  paper-faithful: in the paper the test direction is taken in the
  Sobolev space and the weak-derivative tie is automatic.

The proof is a near-copy of `hVIeps_set_of_KAepsi_VI`, with the
substantive change being that `qn ∈ K_Aepsi_W` is discharged via
`setFamily_test_point_perturbed_mem_K_Aepsi_W` (iter 0696). The
`Aepsi_CLM_opK_apply_of_mem` rewrite still needs `qn ∈ K_Aepsi`,
recovered via `K_Aepsi_W_subset_K_Aepsi` (iter 0687).

This consumer is dispatched to by
`paperSection8_hMinty_set_W_of_paperHypotheses` in
`BanachBridge.lean`. -/

/-- **W-form sibling of `hVIeps_set_of_KAepsi_VI`.** Same shape, but
the weak VI is `K_Aepsi_W`-quantified and the test pair `(υ, Dυ)`
carries a weak-derivative tie. No new authorisation parameter. -/
theorem hVIeps_set_of_KAepsi_W_VI
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
    (hVI : ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x)
    (hSρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ))
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- W-form addition: weak-derivative tie for `(υ, Dυ)`.
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
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
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Per-`n` perturbation step (mirror of K-form proof).
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
    -- Build the named W-form test point and its K_Aepsi_W membership.
    set qn : XBanach d βBarReal γBarReal :=
      setFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n hSρ_memLp hυ_memSob hDυ_memLp with hqn_def
    have hqn_KW : qn ∈ K_Aepsi_W d βBarReal γBarReal :=
      setFamily_test_point_perturbed_mem_K_Aepsi_W
        (βBarReal := βBarReal) (γBarReal := γBarReal)
        n hρ_nn hSρ_memLp hυ_memSob hDυ_memLp hWeak_υ
    -- Descend to `qn ∈ K_Aepsi` for the `Aepsi_CLM_opK_apply_of_mem`
    -- rewrite.
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal :=
      K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hqn_KW
    -- Reconstruct the same `MemLpPer βBar` certificate for `μ_n` that
    -- `setFamily_test_point_perturbed` consumed (definitional).
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1)) :=
      show MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (((S.indicator ρ : (Fin d → ℝ) → ℝ)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))) from
        MemLpPer.add hSρ_memLp hcst_memLp
    have hqn1 : qn.1 = hμn_memLp.toLp := rfl
    have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
    have hqn22 : ∀ i, qn.2.2 i = (hDυ_memLp i).toLp := fun _ => rfl
    -- a.e.-equalities.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1) := by
      rw [hqn1]
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      rw [hqn21]
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
      intro i; rw [hqn22 i]
      exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
    -- Apply the K_Aepsi_W-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_KW
    -- Unfold via `Aepsi_CLM_opK_apply_of_mem` using `qn ∈ K_Aepsi`.
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
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
    -- Replace the primal triple.
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

/-! ## W-form signed-family Minty supplier — `hVIeps_signed_of_KAepsi_W_VI`

Iter-0702 phase of the `paperSolFor-final-phase5-hWeakDeriv` plan.
W-form sibling of `hVIeps_signed_of_KAepsi_VI` (line 422). The
signed family is the simplest of the four W-form siblings because
the test point `qn := (q.1 + (σ·m·1_S + 1/(n+1))_Lp, q.2)` keeps the
`u`/`Du` components definitionally equal to `q.2`; the
weak-derivative tie therefore *inherits* from `q ∈ K0_Aepsi_W` and
no extra `hWeak_υ` hypothesis is required.

The proof is a near-copy of `hVIeps_signed_of_KAepsi_VI` (line 422):

* `hq_K0_W : q ∈ K0_Aepsi_W` replaces `hq_K0 : q ∈ K0_Aepsi`. The
  `mOf q ≥ 0` non-negativity is recovered via
  `K0_Aepsi_W_subset_K0_Aepsi`.
* `hVI` quantifies over `q' ∈ K_Aepsi_W` rather than `q' ∈ K_Aepsi`.
* The per-`n` `qn ∈ K_Aepsi_W` discharge dispatches to
  `signedFamily_test_point_perturbed_mem_K_Aepsi_W` (iter 0696)
  rather than the inline positivity computation; the descent to
  `qn ∈ K_Aepsi` (needed for the `Aepsi_CLM_opK_apply_of_mem`
  rewrite) goes via `K_Aepsi_W_subset_K_Aepsi`.

This consumer is dispatched to by
`paperSection8_hMinty_signed_W_of_paperHypotheses` in
`BanachBridge.lean`. -/

/-- **W-form sibling of `hVIeps_signed_of_KAepsi_VI`.** Same shape,
but the weak VI is `K_Aepsi_W`-quantified and the witness lives in
the refined non-negativity cone `K0_Aepsi_W`. No extra `hWeak_υ`
hypothesis is needed (the signed test point's `υ`/`Dυ` factors equal
`q`'s definitionally). No new authorisation parameter. -/
theorem hVIeps_signed_of_KAepsi_W_VI
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
    -- K0_Aepsi_W membership of `q`: refined non-negativity cone.
    (hq_K0_W : q ∈ K0_Aepsi_W d βBarReal γBarReal)
    -- The K_Aepsi_W-form weak VI.
    (hVI : ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (_hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
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
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for `mOf q ≥ 0` a.e.
  have hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal :=
    K0_Aepsi_W_subset_K0_Aepsi d βBarReal γBarReal hq_K0_W
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
    have heq : (σ • (mOf q : (Fin d → ℝ) → ℝ))
                  = fun x => σ * mOf q x := rfl
    rw [heq] at hsmul; exact hsmul
  -- The indicator-restricted version.
  have hSσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (S.indicator (fun x => σ * mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσm_memLp.toMemLp)
  -- Pointwise pull-out of the constant `σ * mOf q x`.
  have hSσm_eq : ∀ x : Fin d → ℝ,
      S.indicator (fun x => σ * mOf q x) x
        = σ * mOf q x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Function-level identity.
  have hSσm_funEq :
      (S.indicator (fun x => σ * mOf q x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x; exact hSσm_eq x
  -- Lp embeddability of the indicator-pulled form.
  have hSσm_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * mOf q x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσm_funEq]; exact hSσm_memLp
  -- Per-`n` strict-positive perturbation step.
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
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
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
    -- Build the named test point and its K_Aepsi_W membership.
    set qn : XBanach d βBarReal γBarReal :=
      signedFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n q σ hSσm_const_memLp with hqn_def
    have hqn_KW : qn ∈ K_Aepsi_W d βBarReal γBarReal :=
      signedFamily_test_point_perturbed_mem_K_Aepsi_W
        (βBarReal := βBarReal) (γBarReal := γBarReal)
        n q σ hσ hSσm_const_memLp hq_K0_W hm_nn
    -- Descend to `qn ∈ K_Aepsi` for the `Aepsi_CLM_opK_apply_of_mem` rewrite.
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal :=
      K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hqn_KW
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
    -- a.e. equality of the m-direction.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      rw [hqn_sub_1]
      exact MeasureTheory.MemLp.coeFn_toLp hSσm_const_memLp.toMemLp
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun _ => (0 : ℝ) := by
      rw [hqn_sub_21]
      exact MeasureTheory.Lp.coeFn_zero ℝ _ _
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          (fun _ => (0 : ℝ)) := by
      intro i
      rw [hqn_sub_22 i]
      exact MeasureTheory.Lp.coeFn_zero ℝ _ _
    -- a.e. equality of the m-primal.
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
    -- The u-primal is unchanged.
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] uOf q :=
      Filter.EventuallyEq.refl _ _
    -- The Du-primal is unchanged.
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] DuOf q i := by
      intro i
      exact Filter.EventuallyEq.refl _ _
    -- Apply the K_Aepsi_W-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_KW
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Substitute the bare-direction representatives.
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

end Banach
end SimplePower
end Theorems
end StationaryMFG
end
