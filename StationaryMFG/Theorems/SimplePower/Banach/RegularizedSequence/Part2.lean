module

public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext
public import StationaryMFG.Theorems.SimplePower.Banach.UniformSequence
public import StationaryMFG.Theorems.SimplePower.Banach.Closure
public import StationaryMFG.Periodic.Separability
public import Mathlib.MeasureTheory.Function.Floor
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part1
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part1

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


/-- **Bare-`β`-decoupled underlying lemma** for the signed family
(D2b-1c-ii-c3). Identical to `mfgOperatorEpsPair_tendsto_signed_perturbation`
but takes the bare growth exponent `(β : ℝ)` with `hβ : 0 < β` INSTEAD of the
`HypothesisPowerGrowth`/`RegularityH` bundles. Its proof only ever used
`hpow.β`/`hpow.hβ` (never `measurable_H`), so this is the `measurable_H`-free
discharge target for the signed `_of_rc0_of_aeMeasH` producer (mirroring how the
set keystone discharges through `mfgOperatorEpsPair_tendsto_set_perturbation`).
ADDITIVE: the strict `…_signed_perturbation` is left intact for T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_beta
    {ε γBarReal : ℝ}
    {β : ℝ} (hβ : 0 < β)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (σ : ℝ)
    (S : Set (Fin d → ℝ))
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
    (h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) - 1)
          * (0 : ℝ))
        (volume.restrict (UnitCube d)))
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
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
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
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h_μN_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) := by
    intro x
    have :=
      h_one_div_tendsto.const_add (m x + σ * m x *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    simpa [hμN, hμInf, add_zero] using this
  have h_μN_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) :=
    Filter.Eventually.of_forall h_μN_pointwise
  have h_ηN_pointwise :
      ∀ x, Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) := by
    intro x
    have :=
      h_one_div_tendsto.const_add (σ * m x *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    simpa [hηN, hηInf, add_zero] using this
  have h_ηN_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) :=
    Filter.Eventually.of_forall h_ηN_pointwise
  have hβ_pos : 0 < β := hβ
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (μN n x) + V x) * ηN n x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (μInf x) + V x) * ηInf x)) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := β) hβ_pos
      (gN := fun n x =>
        -(u x) - H x (fun i => Du i x) (μN n x) + V x)
      (gInf := fun x =>
        -(u x) - H x (fun i => Du i x) (μInf x) + V x)
      (ηN := ηN) (ηInf := ηInf)
      hGh_memLp hEh_memLp hgN1_meas hηN1_meas hGh_bd hEh_bd ?_ h_ηN_ae
    exact hPointwise_H
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

/-! ### Phase G — closed-form aggregator
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`.

Mirror of `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
specialised to the **signed family** `μ_n := m + σ · m · 1_S + 1/(n+1)`
with `σ ∈ {±1}`. Because the test direction is `(0, 0)`, only the HJB
summand is non-trivial: the flux and mass summands have integrand
pointwise zero. Hence:

* Only the HJB-summand dominators `(Gh, Eh)` are required (no flux/mass
  pairs).
* The four trivial integrabilities `h_int{2,3}_{n,lim}` are reduced to
  `(_) * 0 = 0` and dispatched via `integrable_zero` + `Integrable.congr`.
* The two substantive integrabilities `h_int1_{n,lim}` are produced via
  `MemLp.of_le_mul` + `Periodic.MemLpPer.integrable_mul` at the Hölder
  pair `((β+1)/β, β+1)`.
* The `Eh` MemLp comes from `Eh_memLp_betaBar_signed` (envelope
  `|m x| · 2 + 1`), with the `‖σ · m · 1_S + 1/(n+1)‖ ≤ Eh x` bound
  derived inline by triangle inequality + `|σ| ≤ 1`, `|1_S| ≤ 1`,
  `1/(n+1) ≤ 1`.
* The `Gh` MemLp + dominator bound are taken as authorised paper-level
  inputs (mirroring the set aggregator's pattern, where the
  `g_dominator_pointwise` bound at the paper envelope is paper-§8
  material).
* The two measurabilities are from `signed_perturbation_{gN1,ηN1}_meas`,
  and the pointwise tendsto from
  `signed_perturbation_pointwise_tendsto_H_of_hHat0`. -/

/-- **Closed-form aggregator for the signed-perturbation family.**

Mirror of `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
for the signed family `μ_n := m + σ · m · 1_S + 1/(n+1)` with
`σ ∈ {±1}`. Consumes only paper-level hypotheses and an authorised
HJB-residual envelope `(Gh, hGh_memLp, hGh_bd)`; the `Eh` envelope
`|m x| · 2 + 1` is derived inline. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0
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
    -- Test/structural data.
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hSmeas : MeasurableSet S)
    -- Measurabilities.
    (hm : Measurable m) (hV : Measurable V) (hu : Measurable u)
    (hDu : ∀ i, Measurable (Du i))
    -- `m ∈ L^{β+1}_per` (from regularizedSequenceData apriori).
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) m)
    -- `m ≥ 0` a.e.
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    -- HJB-residual envelope (authorised paper-level, mirrors set case).
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x) :
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
  -- Standing positivity facts on the paper exponents.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  have hβp_pos : 0 < (hpow.β + 1) / hpow.β :=
    div_pos hbb_pos hβ_pos
  -- Restricted measure shorthand and finiteness.
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm_def
  haveI : IsFiniteMeasure μm := by
    rw [hμm_def]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Sign bounds: `σ ∈ {±1}` ⇒ `|σ| ≤ 1`.
  have hσ_abs : |σ| ≤ 1 := by
    rcases hσ with h | h <;> simp [h]
  -- Two measurabilities from the iter-301 helpers.
  have hgN1_meas := signed_perturbation_gN1_meas hpow hSmeas hm hV hu hDu σ
    (S := S) (m := m) (V := V) (υ := u) (Dυ := Du)
  have hηN1_meas := signed_perturbation_ηN1_meas hSmeas hm σ
    (S := S) (m := m)
  -- Pointwise tendsto for the HJB summand (iter 301).
  have hPointwise_H :=
    signed_perturbation_pointwise_tendsto_H_of_rc0
      (V := V) (υ := u) hRegH hH_rc0
      (S := S) (m := m) hm_nn σ hσ Du
  -- `Eh` envelope: `|m x| · 2 + 1` (iter 302).
  set Eh : (Fin d → ℝ) → ℝ := fun x => |m x| * 2 + 1 with hEh_def
  have hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh :=
    Eh_memLp_betaBar_signed hβ_pos m hm_memLp
  -- `Eh` pointwise dominator bound, derived inline.
  have hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂μm,
        ‖σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Eh x := by
    intro n
    refine Filter.Eventually.of_forall ?_
    intro x
    -- `0 ≤ 1_S x ≤ 1`.
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    have hInd_abs :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg hInd_bd.1]; exact hInd_bd.2
    -- `1/(n+1)` bound: `0 ≤ 1/(n+1) ≤ 1`.
    have hone_div_nn : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact le_of_lt (div_pos one_pos this)
    have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hone_div_abs : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_nonneg hone_div_nn]; exact hone_div_le_one
    -- Triangle: `|σ * m x * 1_S x + 1/(n+1)| ≤ |σ| * |m x| * |1_S x| + |1/(n+1)|`.
    have htri :
        |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)|
          ≤ |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            + |(1 : ℝ) / ((n : ℝ) + 1)| := abs_add_le _ _
    -- `|σ * m x * 1_S x| ≤ |m x| * 2`.
    have hprod_abs :
        |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
          ≤ |m x| * 2 := by
      rw [abs_mul, abs_mul]
      have hστerm : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * 1 := by
        have hσ_le : |σ| ≤ 1 := hσ_abs
        have h_mul : |σ| * |m x| ≤ 1 * |m x| :=
          mul_le_mul_of_nonneg_right hσ_le (abs_nonneg _)
        have h_ind_le : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * 1 := by
          have h1 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| :=
            mul_le_mul_of_nonneg_right h_mul (abs_nonneg _)
          have h2 : 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ 1 * |m x| * 1 :=
            mul_le_mul_of_nonneg_left hInd_abs
              (mul_nonneg zero_le_one (abs_nonneg _))
          linarith
        exact h_ind_le
      have hsimp : 1 * |m x| * 1 = |m x| := by ring
      have hmnn : (0 : ℝ) ≤ |m x| := abs_nonneg _
      linarith [hστerm, hsimp, hmnn]
    -- Combine.
    show |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)| ≤ |m x| * 2 + 1
    -- Need to combine `htri`, `hprod_abs`, `hone_div_abs`.
    calc |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)|
        ≤ |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            + |(1 : ℝ) / ((n : ℝ) + 1)| := htri
      _ ≤ |m x| * 2 + 1 := by linarith [hprod_abs, hone_div_abs]
  -- Per-`n` HJB summand integrability via `MemLp.of_le_mul` + Hölder.
  have h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x)
          * (σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))) μm := by
    intro n
    have hHJB_pq :
        Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1) := by
      refine ⟨?_, hβp_pos, hbb_pos⟩
      field_simp
    have hgN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => -(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) + V x‖
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
          (fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)‖ ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd n] with x hx
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp (hηN1_meas n) hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq hgN1_memLp hηN1_memLp
  -- Limit-`n` HJB summand integrability via squeeze on individual factors.
  have hgN1_lim_meas :
      AEStronglyMeasurable
        (fun x => -(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x) μm := by
    have hOne : Measurable (fun _ : (Fin d → ℝ) => (1 : ℝ)) := measurable_const
    have hInd : Measurable
        (fun x : (Fin d → ℝ) =>
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      hOne.indicator hSmeas
    have hσm : Measurable (fun x : (Fin d → ℝ) => σ * m x) :=
      measurable_const.mul hm
    have hσmInd : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      hσm.mul hInd
    have hμInf_meas : Measurable
        (fun x : (Fin d → ℝ) =>
          m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      hm.add hσmInd
    have hDu_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => Du i x)) :=
      measurable_pi_iff.mpr hDu
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => Du i x),
              m x + σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) :=
      measurable_id.prodMk (hDu_pi.prodMk hμInf_meas)
    -- Limit-density H composite consumed only as an AE composite.
    have hHcomp : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => Du i x)
            (m x + σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        μm :=
      hpow.measurable_H.comp_aemeasurable hxpm.aemeasurable
    exact (((hu.aemeasurable.neg).sub hHcomp).add
      hV.aemeasurable).aestronglyMeasurable
  have hηN1_lim_meas :
      AEStronglyMeasurable
        (fun x => σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) μm := by
    have hOne : Measurable (fun _ : (Fin d → ℝ) => (1 : ℝ)) := measurable_const
    have hInd : Measurable
        (fun x : (Fin d → ℝ) =>
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      hOne.indicator hSmeas
    have hσm : Measurable (fun x : (Fin d → ℝ) => σ * m x) :=
      measurable_const.mul hm
    exact (hσm.mul hInd).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖)
      Filter.atTop
      (𝓝 ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have hEh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖ ≤ Eh x := by
    -- Pointwise: triangle gives `|σ * m * 1_S| ≤ |m| * 2 ≤ |m| * 2 + 1 = Eh x`.
    refine Filter.Eventually.of_forall ?_
    intro x
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · exact ⟨by simp [Set.indicator_of_mem hxS],
               by simp [Set.indicator_of_mem hxS]⟩
      · exact ⟨by simp [Set.indicator_of_notMem hxS],
               by simp [Set.indicator_of_notMem hxS]⟩
    have hInd_abs :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg hInd_bd.1]; exact hInd_bd.2
    have hprod_abs :
        |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
          ≤ |m x| * 2 := by
      rw [abs_mul, abs_mul]
      have hστerm : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * 1 := by
        have h_mul : |σ| * |m x| ≤ 1 * |m x| :=
          mul_le_mul_of_nonneg_right hσ_abs (abs_nonneg _)
        have h1 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| :=
          mul_le_mul_of_nonneg_right h_mul (abs_nonneg _)
        have h2 : 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * 1 :=
          mul_le_mul_of_nonneg_left hInd_abs
            (mul_nonneg zero_le_one (abs_nonneg _))
        linarith
      have h1mul : 1 * |m x| * 1 = |m x| := by ring
      have hmnn : (0 : ℝ) ≤ |m x| := abs_nonneg _
      linarith [hστerm, h1mul, hmnn]
    show ‖σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
        ≤ |m x| * 2 + 1
    rw [Real.norm_eq_abs]
    linarith [hprod_abs]
  have h_int1_lim :
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x)
          * (σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) μm := by
    have hHJB_pq :
        Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1) := by
      refine ⟨?_, hβp_pos, hbb_pos⟩
      field_simp
    have hgN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => -(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x‖
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
          (fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
            ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd_lim, hEh_bd 0] with x hx h0
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp hηN1_lim_meas hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq
      hgN1_lim_memLp hηN1_lim_memLp
  -- Trivial integrabilities (flux + mass, both pointwise zero).
  have h_dot_zero : ∀ (v : Fin d → ℝ),
      v ⬝ (fun _ : Fin d => (0 : ℝ)) = 0 := by
    intro v
    change ∑ i, v i * (0 : ℝ) = 0
    simp
  have h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              ⬝ (fun _ : Fin d => (0 : ℝ)))) μm := by
    intro n
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              ⬝ (fun _ : Fin d => (0 : ℝ))))
        = fun _ => (0 : ℝ) := by
      funext x
      rw [h_dot_zero]; ring
    rw [heq]; exact integrable_zero _ _ _
  have h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) - 1)
          * (0 : ℝ)) μm := by
    intro n
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) - 1)
          * (0 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext x; ring
    rw [heq]; exact integrable_zero _ _ _
  have h_int2_lim :
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun _ : Fin d => (0 : ℝ)))) μm := by
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun _ : Fin d => (0 : ℝ))))
        = fun _ => (0 : ℝ) := by
      funext x
      rw [h_dot_zero]; ring
    rw [heq]; exact integrable_zero _ _ _
  have h_int3_lim :
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x - 1)
          * (0 : ℝ)) μm := by
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x - 1)
          * (0 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext x; ring
    rw [heq]; exact integrable_zero _ _ _
  -- Discharge the headline.
  exact mfgOperatorEpsPair_tendsto_signed_perturbation
    (V := V) (H := H) (DpH := DpH)
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    hpow hRegH hExp Du u m σ hσ S hSmeas
    h_int1_n h_int2_n h_int3_n
    h_int1_lim h_int2_lim h_int3_lim
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    hgN1_meas hηN1_meas hPointwise_H

/-- **`aeMeasH`-input variant** of
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0`
(D2b-1c-ii-c3, the signed sibling of the c2b set keystone).

The `measurable_H`-free entry point for the signed family, instantiable at
`H := HdeltaK0`. Mirrors the strict `_of_rc0` proof but replaces:

* `signed_perturbation_gN1_meas` (uses `hpow.measurable_H`) by the per-`n`
  AE composite `hHcomp_ae_n` routed through
  `signed_perturbation_gN1_meas_of_aeMeasH`;
* `signed_perturbation_pointwise_tendsto_H_of_rc0` (uses the `RegularityH`
  bundle) by the continuity-only `signed_perturbation_pointwise_tendsto_H_of_cont`
  (consuming the genuine field `hcont_H_pm` + `hH_rc0`);
* the limit-density `H` composite (was `hpow.measurable_H.comp_aemeasurable`)
  by the boundary AE composite `hHcomp_ae_lim`;
* the discharge through `mfgOperatorEpsPair_tendsto_signed_perturbation`
  (takes `hpow`/`hRegH`) by the bare-`β`-decoupled
  `mfgOperatorEpsPair_tendsto_signed_perturbation_of_beta`.

No `RegularityH`/`HypothesisPowerGrowth`/`measurable_H` binder appears.
ADDITIVE: the strict `…_of_rc0` is left intact for T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
    {ε γBarReal : ℝ}
    {β : ℝ} (hβ : 0 < β)
    -- The continuity field on `{0 < m}` (individual, not the bundle).
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    -- Test/structural data.
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hSmeas : MeasurableSet S)
    -- Measurabilities.
    (hm : Measurable m) (hV : Measurable V) (hu : Measurable u)
    (hDu : ∀ i, Measurable (Du i))
    -- `m ∈ L^{β+1}_per` (from regularizedSequenceData apriori).
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) m)
    -- `m ≥ 0` a.e.
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    -- The two H AE composites (replacing `hpow.measurable_H`).
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Du i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Du i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      (volume.restrict (UnitCube d)))
    -- HJB-residual envelope (authorised paper-level, mirrors set case).
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x) :
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
  -- Standing positivity facts on the bare exponent.
  have hβ_pos : 0 < β := hβ
  have hbb_pos : 0 < β + 1 := by linarith
  have hβp_pos : 0 < (β + 1) / β :=
    div_pos hbb_pos hβ_pos
  -- Restricted measure shorthand and finiteness.
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm_def
  haveI : IsFiniteMeasure μm := by
    rw [hμm_def]
    exact ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Sign bounds: `σ ∈ {±1}` ⇒ `|σ| ≤ 1`.
  have hσ_abs : |σ| ≤ 1 := by
    rcases hσ with h | h <;> simp [h]
  -- Two measurabilities; gN1 routed through the AE composite.
  have hgN1_meas := signed_perturbation_gN1_meas_of_aeMeasH (H := H)
    (S := S) (m := m) (V := V) (υ := u) (Dυ := Du)
    hV.aestronglyMeasurable hu.aestronglyMeasurable σ hHcomp_ae_n
  have hηN1_meas := signed_perturbation_ηN1_meas hSmeas hm σ
    (S := S) (m := m)
  -- Pointwise tendsto for the HJB summand (continuity-only sibling).
  have hPointwise_H :=
    signed_perturbation_pointwise_tendsto_H_of_cont
      (V := V) (υ := u) hcont_H_pm hH_rc0
      (S := S) (m := m) hm_nn σ hσ Du
  -- `Eh` envelope: `|m x| · 2 + 1`.
  set Eh : (Fin d → ℝ) → ℝ := fun x => |m x| * 2 + 1 with hEh_def
  have hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh :=
    Eh_memLp_betaBar_signed hβ_pos m hm_memLp
  -- `Eh` pointwise dominator bound, derived inline.
  have hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂μm,
        ‖σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Eh x := by
    intro n
    refine Filter.Eventually.of_forall ?_
    intro x
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    have hInd_abs :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg hInd_bd.1]; exact hInd_bd.2
    have hone_div_nn : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact le_of_lt (div_pos one_pos this)
    have hone_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hone_div_abs : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_nonneg hone_div_nn]; exact hone_div_le_one
    have htri :
        |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)|
          ≤ |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            + |(1 : ℝ) / ((n : ℝ) + 1)| := abs_add_le _ _
    have hprod_abs :
        |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
          ≤ |m x| * 2 := by
      rw [abs_mul, abs_mul]
      have hστerm : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * 1 := by
        have hσ_le : |σ| ≤ 1 := hσ_abs
        have h_mul : |σ| * |m x| ≤ 1 * |m x| :=
          mul_le_mul_of_nonneg_right hσ_le (abs_nonneg _)
        have h_ind_le : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * 1 := by
          have h1 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| :=
            mul_le_mul_of_nonneg_right h_mul (abs_nonneg _)
          have h2 : 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ 1 * |m x| * 1 :=
            mul_le_mul_of_nonneg_left hInd_abs
              (mul_nonneg zero_le_one (abs_nonneg _))
          linarith
        exact h_ind_le
      have hsimp : 1 * |m x| * 1 = |m x| := by ring
      have hmnn : (0 : ℝ) ≤ |m x| := abs_nonneg _
      linarith [hστerm, hsimp, hmnn]
    show |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)| ≤ |m x| * 2 + 1
    calc |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)|
        ≤ |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            + |(1 : ℝ) / ((n : ℝ) + 1)| := htri
      _ ≤ |m x| * 2 + 1 := by linarith [hprod_abs, hone_div_abs]
  -- Per-`n` HJB summand integrability via `MemLp.of_le_mul` + Hölder.
  have h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x)
          * (σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))) μm := by
    intro n
    have hHJB_pq :
        Real.HolderConjugate ((β + 1) / β) (β + 1) := by
      refine ⟨?_, hβp_pos, hbb_pos⟩
      field_simp
    have hgN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => -(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) + V x‖
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
          (fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)‖ ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd n] with x hx
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp (hηN1_meas n) hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq hgN1_memLp hηN1_memLp
  -- Limit-`n` HJB summand integrability via squeeze on individual factors.
  have hgN1_lim_meas :
      AEStronglyMeasurable
        (fun x => -(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x) μm := by
    -- Limit-density H composite consumed only as the boundary AE composite.
    exact (((hu.aemeasurable.neg).sub hHcomp_ae_lim).add
      hV.aemeasurable).aestronglyMeasurable
  have hηN1_lim_meas :
      AEStronglyMeasurable
        (fun x => σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) μm := by
    have hOne : Measurable (fun _ : (Fin d → ℝ) => (1 : ℝ)) := measurable_const
    have hInd : Measurable
        (fun x : (Fin d → ℝ) =>
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      hOne.indicator hSmeas
    have hσm : Measurable (fun x : (Fin d → ℝ) => σ * m x) :=
      measurable_const.mul hm
    exact (hσm.mul hInd).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖)
      Filter.atTop
      (𝓝 ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have hEh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖ ≤ Eh x := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · exact ⟨by simp [Set.indicator_of_mem hxS],
               by simp [Set.indicator_of_mem hxS]⟩
      · exact ⟨by simp [Set.indicator_of_notMem hxS],
               by simp [Set.indicator_of_notMem hxS]⟩
    have hInd_abs :
        |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
      rw [abs_of_nonneg hInd_bd.1]; exact hInd_bd.2
    have hprod_abs :
        |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
          ≤ |m x| * 2 := by
      rw [abs_mul, abs_mul]
      have hστerm : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
            ≤ 1 * |m x| * 1 := by
        have h_mul : |σ| * |m x| ≤ 1 * |m x| :=
          mul_le_mul_of_nonneg_right hσ_abs (abs_nonneg _)
        have h1 : |σ| * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| :=
          mul_le_mul_of_nonneg_right h_mul (abs_nonneg _)
        have h2 : 1 * |m x| * |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
              ≤ 1 * |m x| * 1 :=
          mul_le_mul_of_nonneg_left hInd_abs
            (mul_nonneg zero_le_one (abs_nonneg _))
        linarith
      have h1mul : 1 * |m x| * 1 = |m x| := by ring
      have hmnn : (0 : ℝ) ≤ |m x| := abs_nonneg _
      linarith [hστerm, h1mul, hmnn]
    show ‖σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
        ≤ |m x| * 2 + 1
    rw [Real.norm_eq_abs]
    linarith [hprod_abs]
  have h_int1_lim :
      Integrable (fun x =>
        (-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + V x)
          * (σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) μm := by
    have hHJB_pq :
        Real.HolderConjugate ((β + 1) / β) (β + 1) := by
      refine ⟨?_, hβp_pos, hbb_pos⟩
      field_simp
    have hgN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => -(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(u x) - H x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                + V x‖
            ≤ (1 : ℝ) * ‖Gh x‖ := by
        filter_upwards [hGh_bd_lim, hGh_bd 0] with x hx h0
        have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGh_memLp.toMemLp hgN1_lim_meas hbd)
    have hηN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x‖
            ≤ (1 : ℝ) * ‖Eh x‖ := by
        filter_upwards [hEh_bd_lim, hEh_bd 0] with x hx h0
        have hEh_nn : 0 ≤ Eh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hEh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hEh_memLp.toMemLp hηN1_lim_meas hbd)
    exact Periodic.MemLpPer.integrable_mul hHJB_pq
      hgN1_lim_memLp hηN1_lim_memLp
  -- Trivial integrabilities (flux + mass, both pointwise zero).
  have h_dot_zero : ∀ (v : Fin d → ℝ),
      v ⬝ (fun _ : Fin d => (0 : ℝ)) = 0 := by
    intro v
    change ∑ i, v i * (0 : ℝ) = 0
    simp
  have h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              ⬝ (fun _ : Fin d => (0 : ℝ)))) μm := by
    intro n
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              ⬝ (fun _ : Fin d => (0 : ℝ))))
        = fun _ => (0 : ℝ) := by
      funext x
      rw [h_dot_zero]; ring
    rw [heq]; exact integrable_zero _ _ _
  have h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) - 1)
          * (0 : ℝ)) μm := by
    intro n
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                  + 1 / ((n : ℝ) + 1) - 1)
          * (0 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext x; ring
    rw [heq]; exact integrable_zero _ _ _
  have h_int2_lim :
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun _ : Fin d => (0 : ℝ)))) μm := by
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Du i x)
                (m x + σ * m x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun _ : Fin d => (0 : ℝ))))
        = fun _ => (0 : ℝ) := by
      funext x
      rw [h_dot_zero]; ring
    rw [heq]; exact integrable_zero _ _ _
  have h_int3_lim :
      Integrable (fun x =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x - 1)
          * (0 : ℝ)) μm := by
    have heq : (fun x : (Fin d → ℝ) =>
        (m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x - 1)
          * (0 : ℝ))
        = fun _ => (0 : ℝ) := by
      funext x; ring
    rw [heq]; exact integrable_zero _ _ _
  -- Discharge through the bare-`β`-decoupled underlying lemma.
  exact mfgOperatorEpsPair_tendsto_signed_perturbation_of_beta
    (V := V) (H := H) (DpH := DpH)
    (γBarReal := γBarReal) (ε := ε)
    hβ Du u m σ S
    h_int1_n h_int2_n h_int3_n
    h_int1_lim h_int2_lim h_int3_lim
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    hgN1_meas hηN1_meas hPointwise_H

/-- **Hext-bundle wrapper** recovering the original
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`
signature from the `rc0`-input core `…_of_rc0`. Derives the
right-continuity certificate `hH_rc0` from the
`HypothesisHat0`/`Hext_finite_at_zero`/`H_zero_eq_Hext` bundle via
`Hamiltonian.H_rc0_of_hHat0`, then delegates. (T1 / simple-power chain
entry point; the T3 chain calls `…_of_rc0` directly to stay Hext-free.) -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hSmeas : MeasurableSet S)
    (hm : Measurable m) (hV : Measurable V) (hu : Measurable u)
    (hDu : ∀ i, Measurable (Du i))
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x) :
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
            (fun _ => (0 : ℝ)))) :=
  mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0
    (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hpow hRegH hExp
    (StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hHat0 hFin hAgree)
    Du u m V σ hσ S hSmeas hm hV hu hDu hm_memLp hm_nn
    Gh hGh_memLp hGh_bd

/-- **AE-strongly-measurable `V` wrapper for the signed-perturbation
consumer.**

Same conclusion as
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses` but
takes `hV : AEStronglyMeasurable V (volume.restrict (UnitCube d))`
in place of `hV : Measurable V`. Used by the closed supplier chain
where `V` enters via `MemLpPer V` (whose `AEStronglyMeasurable`
projection is the natural input) rather than via a bare measurability
witness.

The body introduces a measurable representative `V' := hV.mk V`,
transports the only `V`-using hypothesis `hGh_bd` from `V` to `V'`
via the a.e. equality `V =ᵐ V'`, calls the strict consumer at `V'`,
and bridges the resulting `Tendsto` back to the `V`-parameterised
conclusion using `mfgOperatorEpsPair_congr_V_ae` on each sequence
term and on the limit. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hSmeas : MeasurableSet S)
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hDu : ∀ i, Measurable (Du i))
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x) :
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
  -- Build a Measurable representative `V'` of `V`.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  -- Transport the HJB pointwise bound from `V` to `V'`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    filter_upwards [hGh_bd n, hV_ae] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Apply the strict consumer at `V'`.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal')
      hpow hRegH hExp hHat0 hFin hAgree
      Du u m V' σ hσ S hSmeas
      hm hV'_meas hu hDu hm_memLp hm_nn
      Gh hGh_memLp hGh_bd'
  -- Bridge `V' → V` via `mfgOperatorEpsPair_congr_V_ae`.
  have hSeqV_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
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
          (fun _ => (0 : ℝ))
      =
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
          (fun _ => (0 : ℝ)) := fun n =>
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
      V' V H DpH γBarReal ε
      Du
      (fun x => m x + σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
      u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
      (fun _ => (0 : ℝ)) hV_ae_symm
  have hLimV_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)) :=
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
      V' V H DpH γBarReal ε
      Du
      (fun x => m x + σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ => (0 : ℝ)) hV_ae_symm
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
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
      =
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
          (fun _ => (0 : ℝ))) := by
    funext n; exact hSeqV_eq n
  rw [h_seq_funext, hLimV_eq] at h_tendsto
  exact h_tendsto

/-- **`measurable_H`-free aesm-input signed-perturbation keystone**
(D2b-1c-ii-c4b). The `HdeltaK0`-instantiable, AE-strongly-measurable-input
sibling of
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`:
it drops the strict `HypothesisPowerGrowth`/`RegularityH` binders and
instead consumes the genuine individual H field `hcont_H_pm` plus the bare
growth exponent `β`, and the two H AE composites at the signed base
`m + σ·m·𝟙_S` (replacing `hRegH.measurable_H`). The proof is the same
measurable-representative `V`-transport as the strict aesm bridge; only
the inner call delegates to the `measurable_H`-free core
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`.

The two H AE composites depend only on `(H, Du, m, σ, S)` (not on `V`), so
no composite transport is required. **Additive** — the strict producer is
left byte-for-byte intact for T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
    {ε γBarReal : ℝ}
    {β : ℝ} (hβ : 0 < β)
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hH_rc0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
        Filter.Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (H x p 0)))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hSmeas : MeasurableSet S)
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hDu : ∀ i, Measurable (Du i))
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    -- The two H AE composites (replacing `hRegH.measurable_H`).
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Du i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Du i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      (volume.restrict (UnitCube d)))
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x) :
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
  -- Build a Measurable representative `V'` of `V`.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  -- Transport the HJB pointwise bound from `V` to `V'`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    filter_upwards [hGh_bd n, hV_ae] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Apply the `measurable_H`-free `_of_rc0_of_aeMeasH` core at `V'`.
  -- The two H AE composites are unchanged (they do not involve `V`).
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
      (ε := ε) (γBarReal := γBarReal) (β := β) (DpH := DpH)
      hβ hcont_H_pm hH_rc0
      Du u m V' σ hσ S hSmeas
      hm hV'_meas hu hDu hm_memLp hm_nn
      hHcomp_ae_n hHcomp_ae_lim
      Gh hGh_memLp hGh_bd'
  -- Bridge `V' → V` via `mfgOperatorEpsPair_congr_V_ae`.
  have hSeqV_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
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
          (fun _ => (0 : ℝ))
      =
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
          (fun _ => (0 : ℝ)) := fun n =>
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
      V' V H DpH γBarReal ε
      Du
      (fun x => m x + σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
      u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
      (fun _ => (0 : ℝ)) hV_ae_symm
  have hLimV_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)) :=
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
      V' V H DpH γBarReal ε
      Du
      (fun x => m x + σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ => (0 : ℝ)) hV_ae_symm
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
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
      =
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
          (fun _ => (0 : ℝ))) := by
    funext n; exact hSeqV_eq n
  rw [h_seq_funext, hLimV_eq] at h_tendsto
  exact h_tendsto

/-- **Hext-free (`rc0`) AE-strongly-measurable signed-perturbation bridge.**

Identical conclusion and AE-strong-measurability interface to
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
above, but instead of the `Hext_finite_at_zero`-pulling triple
`(hHat0, hFin, hAgree)` it takes the **paper line-1821 right-continuity**
rider `hH_rc0` directly and routes the inner strict call through the
Hext-free core
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0`.

This is the reusable bridge that the substituted-pair `hMinty_signed`
δ-limit wrapper (T3 A1d-final, step 7) consumes: the substituted
operator `A_ε^δ` must stay Hext-free, so its operator-continuity
certificate cannot route through the T1 `_of_paperHypotheses` producer.

The body is the same measurable-representative `V`-transport as the
`_of_paperHypotheses` aesm variant; only the inner call differs. -/
theorem mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
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
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hSmeas : MeasurableSet S)
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hDu : ∀ i, Measurable (Du i))
    (hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (Gh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x) :
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
  -- Build a Measurable representative `V'` of `V`.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  -- Transport the HJB pointwise bound from `V` to `V'`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(u x) - H x (fun i => Du i x)
              (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    filter_upwards [hGh_bd n, hV_ae] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Apply the Hext-free `_of_rc0` core at `V'`.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_rc0
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal')
      hpow hRegH hExp hH_rc0
      Du u m V' σ hσ S hSmeas
      hm hV'_meas hu hDu hm_memLp hm_nn
      Gh hGh_memLp hGh_bd'
  -- Bridge `V' → V` via `mfgOperatorEpsPair_congr_V_ae`.
  have hSeqV_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
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
          (fun _ => (0 : ℝ))
      =
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
          (fun _ => (0 : ℝ)) := fun n =>
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
      V' V H DpH γBarReal ε
      Du
      (fun x => m x + σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
      u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1))
      (fun _ => (0 : ℝ)) hV_ae_symm
  have hLimV_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Du
          (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)) :=
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
      V' V H DpH γBarReal ε
      Du
      (fun x => m x + σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ => (0 : ℝ)) hV_ae_symm
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
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
      =
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
          (fun _ => (0 : ℝ))) := by
    funext n; exact hSeqV_eq n
  rw [h_seq_funext, hLimV_eq] at h_tendsto
  exact h_tendsto

/-! ## Transport-perturbation specialisation: `μ_n := σ + 1/(n+1)`

This section discharges the `hCont` operator-tendsto certificate
consumed by `hVIeps_transport_of_KAepsi_VI` (Child D — transport
family). The headline lemma
`mfgOperatorEpsPair_tendsto_transport_perturbation` specialises the
consumer-level compositional lemma `mfgOperatorEpsPair_tendsto_of_summands`
above at the strict-positive perturbation
`μ_n := σ + 1/(n+1)`, with limit `μ_∞ := σ`.

Structurally this is exactly the set-perturbation case
(`mfgOperatorEpsPair_tendsto_set_perturbation`) with the `S.indicator ρ`
wrapper removed: the primal density is the bare `σ` (assumed nonneg
a.e.) instead of `S.indicator ρ`, and the test gradient family is
`φ` (the transport test direction) in place of `Dυ`. The gradient
test direction `φ - Du` and value-function direction `υ - u` are both
non-zero, so all three integrand-level summands require the full
dominator inputs (mirroring the set case, unlike the signed case
where the test direction is zero).

Per CONVENTIONS §8 the same authorised inputs apply as in the set
case: continuity of `H` and `DpH` in the third argument
(`RegularityH.continuous_*_pm` is `ContinuousOn {m > 0}` only and the
limit `μ_∞ = σ` may equal `0` on `{σ = 0}`, so the per-`x` pointwise
tendstos are paper-level material), per-`n`/per-limit integrability
witnesses, and per-`x` dominator bounds.

This shape exactly matches the abstract pattern set by
`hVIeps_transport_of_KAepsi_VI`. -/

/-- **Headline: `mfgOperatorEpsPair`-tendsto for the transport-family
Minty perturbation `μ_n := σ + 1/(n+1)`.**

This is the Child D-specific (transport family) specialisation of
`mfgOperatorEpsPair_tendsto_of_summands` (above) at the perturbation
arising in `hVIeps_transport_of_KAepsi_VI`'s strict-positive bridge.

The proof mirrors `mfgOperatorEpsPair_tendsto_set_perturbation`
verbatim with `S.indicator ρ` replaced by `σ` (no indicator) and the
test gradient `Dυ` replaced by `φ`:

* the three per-`n`/per-limit integrability witnesses thread through
  the per-summand integrability slots of
  `mfgOperatorEpsPair_tendsto_of_summands`,
* the three integrand-level tendstos discharge through
  `tendsto_setIntegral_HJB_mul_of_dom`,
  `tendsto_setIntegral_flux_mul_of_dom`,
  `tendsto_setIntegral_mass_mul_of_dom` from `Hamiltonian/Estimates.lean`,
  with the Hölder pair fixed by `(hpow.α, hpow.β)`.

Per CONVENTIONS §8: the dominators `Gh, Eh, Gf, Ef, Gm, Em` and the
pointwise tendsto inputs `hPointwise_H`, `hPointwise_DpH` are accepted
as authorised hypotheses. -/
theorem mfgOperatorEpsPair_tendsto_transport_perturbation
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (_hRegH : RegularityH H DpH)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (φ : Fin d → (Fin d → ℝ) → ℝ) (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    (_hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    (_hσ_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    -- Per-`n` integrability of the three `mfgOperatorPair` summands
    -- at the perturbation `μ_n := σ + 1/(n+1)`.
    (h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x)
          * (σ x + 1 / ((n : ℝ) + 1) - m x))
        (volume.restrict (UnitCube d)))
    (h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (σ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (σ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x))
        (volume.restrict (UnitCube d)))
    -- Limit integrability of the three summands at `μ_∞ := σ`.
    (h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => φ i x) (σ x) + V x)
          * (σ x - m x))
        (volume.restrict (UnitCube d)))
    (h_int2_lim :
      Integrable (fun x =>
        σ x
          * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_lim :
      Integrable (fun x =>
        (σ x - 1) * (υ x - u x))
        (volume.restrict (UnitCube d)))
    -- Dominator inputs for the three summands, at the (Hölder)-paired
    -- exponents `((β+1)/β, β+1)` for HJB,
    -- `(γ̄/(γ̄-1), γ̄)` for flux, `(β+1, (β+1)/β)` for mass.
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    -- iter 0617 flux-pair retype: `(γ̄', γ̄) → (β̄, β̄')`.
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x)
    -- Strong measurability of the per-`n` integrand sequences.
    (hgN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)))
    (hηN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
        (volume.restrict (UnitCube d)))
    (hgN2_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ x + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)))
    (hηN2_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x))
        (volume.restrict (UnitCube d)))
    (hgN3_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ x + 1 / ((n : ℝ) + 1) - 1)
        (volume.restrict (UnitCube d)))
    (hηN3_meas : ∀ _n : ℕ,
      AEStronglyMeasurable (fun x => υ x - u x)
        (volume.restrict (UnitCube d)))
    -- Per-`x` pointwise tendsto inputs (authorised, CONVENTIONS §8).
    -- These come from continuity of `H`, `DpH` in the third argument.
    -- Since `μ_∞ = σ` may equal `0` on `{σ = 0}` and
    -- `RegularityH.continuous_*_pm` is `ContinuousOn {m > 0}` only,
    -- these are paper-level inputs.
    (hPointwise_H :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => φ i x)
                  (σ x + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => φ i x)
                    (σ x) + V x)))
    (hPointwise_DpH_prod :
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
                ⬝ (fun i => φ i x - Du i x))))) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
  -- Shorthand for the perturbation and its limit.
  set μN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => σ x + 1 / ((n : ℝ) + 1) with hμN
  set μInf : (Fin d → ℝ) → ℝ := σ with hμInf
  set ηN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => σ x + 1 / ((n : ℝ) + 1) - m x with hηN
  set ηInf : (Fin d → ℝ) → ℝ := fun x => σ x - m x with hηInf
  -- Pointwise tendsto: `1/(n+1) → 0`.
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Pointwise tendsto: `μ_n x → μ_∞ x` for every `x`.
  have h_μN_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) := by
    intro x
    have := h_one_div_tendsto.const_add (σ x)
    simpa [hμN, hμInf, add_zero] using this
  -- Pointwise tendsto: `η_n x → η_∞ x` for every `x`.
  have h_ηN_pointwise :
      ∀ x, Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) := by
    intro x
    have := (h_one_div_tendsto.const_add (σ x)).sub_const (m x)
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
  -- Standing positivity facts on the paper exponents.
  have hβ_pos : 0 < hpow.β := hpow.hβ
  -- Step 1: HJB integrand-level tendsto via `tendsto_setIntegral_HJB_mul_of_dom`.
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => φ i x) (μN n x) + V x) * ηN n x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => φ i x) (μInf x) + V x) * ηInf x)) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := hpow.β) hβ_pos
      (gN := fun n x =>
        -(υ x) - H x (fun i => φ i x) (μN n x) + V x)
      (gInf := fun x =>
        -(υ x) - H x (fun i => φ i x) (μInf x) + V x)
      (ηN := ηN) (ηInf := ηInf)
      hGh_memLp hEh_memLp hgN1_meas hηN1_meas hGh_bd hEh_bd ?_ h_ηN_ae
    exact hPointwise_H
  -- Step 2: flux integrand-level tendsto via direct DCT on the
  -- **product** integrand `μ_n · (DpH·v)`. Same paper-correct
  -- treatment as in `mfgOperatorEpsPair_tendsto_set_perturbation`:
  -- the consumer delivers `hPointwise_DpH_prod` (product-form
  -- pointwise tendsto), no `(a:DpHat0)` is needed.
  have h_tendsto2 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          μN n x * (DpH x (fun i => φ i x) (μN n x)
                      ⬝ (fun i => φ i x - Du i x)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          μInf x * (DpH x (fun i => φ i x) (μInf x)
                      ⬝ (fun i => φ i x - Du i x)))) := by
    -- iter 0617 flux-pair retype: `(γ̄', γ̄) → (β̄, β̄')`.
    set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d)
    set bound : (Fin d → ℝ) → ℝ := fun x => Gf x * Ef x with hbound
    have hbb_pos : 0 < hpow.β + 1 := by linarith
    have hβp_pos : 0 < (hpow.β + 1) / hpow.β := div_pos hbb_pos hβ_pos
    have hpq :
        Real.HolderConjugate (hpow.β + 1) ((hpow.β + 1) / hpow.β) := by
      refine ⟨?_, hbb_pos, hβp_pos⟩
      field_simp
      ring
    have hbound_int : Integrable bound μm := by
      have := Periodic.MemLpPer.integrable_mul
        (p := hpow.β + 1)
        (q := (hpow.β + 1) / hpow.β)
        hpq hGf_memLp hEf_memLp
      exact this
    have hprod_meas : ∀ n,
        AEStronglyMeasurable
          (fun x => μN n x * (DpH x (fun i => φ i x) (μN n x)
                        ⬝ (fun i => φ i x - Du i x))) μm :=
      fun n => (hgN2_meas n).mul (hηN2_meas n)
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hprod_bd : ∀ n, ∀ᵐ x ∂μm,
        ‖μN n x * (DpH x (fun i => φ i x) (μN n x)
                    ⬝ (fun i => φ i x - Du i x))‖ ≤ bound x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    have hprod_lim : ∀ᵐ x ∂μm,
        Filter.Tendsto
          (fun n => μN n x * (DpH x (fun i => φ i x) (μN n x)
                      ⬝ (fun i => φ i x - Du i x)))
          Filter.atTop
          (𝓝 (μInf x * (DpH x (fun i => φ i x) (μInf x)
                      ⬝ (fun i => φ i x - Du i x)))) := by
      filter_upwards [hPointwise_DpH_prod] with x hx
      simpa [μN, μInf] using hx
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hprod_meas hbound_int hprod_bd hprod_lim
  -- Step 3: mass integrand-level tendsto via `tendsto_setIntegral_mass_mul_of_dom`.
  have h_tendsto3 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d, (μN n x - 1) * (υ x - u x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (μInf x - 1) * (υ x - u x))) := by
    refine Hamiltonian.tendsto_setIntegral_mass_mul_of_dom (β := hpow.β) hβ_pos
      (gN := fun n x => μN n x - 1) (gInf := fun x => μInf x - 1)
      (ηN := fun _ x => υ x - u x) (ηInf := fun x => υ x - u x)
      hGm_memLp hEm_memLp hgN3_meas hηN3_meas hGm_bd ?_ h_μN1_ae h_νconst_ae
    intro _
    exact hEm_bd
  -- Apply the consumer-level compositional lemma.
  have h_main :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (μN n) υ
            (fun i x => φ i x - Du i x)
            (ηN n) (fun x => υ x - u x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ μInf υ
              (fun i x => φ i x - Du i x)
              ηInf (fun x => υ x - u x))) := by
    refine mfgOperatorEpsPair_tendsto_of_summands
      (V := V) (H := H) (DpH := DpH)
      φ υ (fun i x => φ i x - Du i x) (fun x => υ x - u x)
      μN μInf ηN ηInf
      h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
      h_tendsto1 h_tendsto2 h_tendsto3
  -- Convert `fun x => υ x - u x` to `υ - u`.
  have h_test_eq :
      (fun x => υ x - u x) = υ - u := by
    funext x; rfl
  rw [h_test_eq] at h_main
  -- Identify `ηInf = σ - m`.
  have h_ηInf_eq : ηInf = σ - m := by
    funext x; simp [hηInf, Pi.sub_apply]
  rw [h_ηInf_eq] at h_main
  exact h_main

/-! ### D2b-1c-ii-c3a — transport `_of_aeMeasH` building blocks

The decls below mirror the **set** c2b keystone
(`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`)
for the transport family. Transport is full-flux/mass (test direction
`(φ - Du, υ - u)` non-zero), so unlike the trivial-flux signed family it
genuinely needs the DpH-of-fields pointwise path. All decls are
`measurable_H`-free (no `RegularityH`/`HypothesisPowerGrowth`/`measurable_H`
binder); they consume per-`n`/boundary H AE composites + the genuine
individual `hcont_H_pm`/`hcont_DpH_pm`/`hDpH_upper`/`hDpH_meas` fields. -/

/-- **`transport_perturbation_pointwise_tendsto_H_of_cont`** — continuity-only
sibling of `transport_perturbation_pointwise_tendsto_H_of_rc0`. Consumes the
genuine individual continuity field `hcont_H_pm`
(`ContinuousOn {m > 0}`, available on `HdeltaK0`) plus the
right-continuity-at-`0` certificate `hH_rc0`, INSTEAD of the `RegularityH`
bundle. Reduces to the set `_of_cont` leaf
`set_perturbation_pointwise_tendsto_H_of_cont` at `S' := Set.univ`,
`ρ' := σ`. The `measurable_H`-free continuity leaf for the transport
`_of_rc0_of_aeMeasH` producer. -/
theorem transport_perturbation_pointwise_tendsto_H_of_cont
    (hcont_H_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
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
  -- Apply the set `_of_cont` version at `S' := Set.univ`, `ρ := σ`.
  have h_set := set_perturbation_pointwise_tendsto_H_of_cont
    (V := V) (υ := υ) hcont_H_pm (S := Set.univ) (ρ := σ) hσ_nn hH_rc0 φ
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x
    simp
  filter_upwards [h_set] with x hx
  have hx' := hx
  rw [h_ind_univ x] at hx'
  exact hx'

/-- **`transport_perturbation_pointwise_tendsto_DpH_of_fields`** —
`_of_fields` sibling of `transport_perturbation_pointwise_tendsto_DpH`.
Takes the genuine individual regularity fields
(`hcont_DpH_pm`, `hDpH_upper`, bare exponents `α β` with `hα : 1 < α`,
`hβ : 0 < β`, constant `C`) DIRECTLY instead of the whole
`HypothesisPowerGrowth` bundle. Reduces to the set
`set_perturbation_pointwise_tendsto_DpH_of_fields` at `S' := Set.univ`,
`ρ' := σ`. The H-measurability-free DpH-pointwise leaf for the transport
`_of_rc0_of_aeMeasH` producer. -/
theorem transport_perturbation_pointwise_tendsto_DpH_of_fields
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hcont_DpH_pm :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hDpH_upper :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
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
  have h_set := set_perturbation_pointwise_tendsto_DpH_of_fields (DpH := DpH)
    hα hβ hcont_DpH_pm hDpH_upper
    (S := Set.univ) (ρ := σ) hσ_nn φ Du
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x
    simp
  filter_upwards [h_set] with x hx
  have hx' := hx
  rw [h_ind_univ x] at hx'
  exact hx'

/-- **`transport_perturbation_ηN2_meas_of_meas`** — decoupled DpH-meas
sibling of `transport_perturbation_ηN2_meas`, taking the global joint
measurability `hDpH_meas` (D2b-1a; `DpHepsilonFam` is globally measurable)
INSTEAD of the `HypothesisPowerGrowth` bundle. The `measurable_H`-free flux
η-factor measurability witness for the transport `_of_rc0_of_aeMeasH`
producer. -/
theorem transport_perturbation_ηN2_meas_of_meas
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
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
  have hDpHcomp : Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))) :=
    hDpH_meas.comp hxpm
  have hDpHcomp_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)) i) :=
    fun i => (measurable_pi_apply i).comp hDpHcomp
  have hφdiff_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) => φ i x - Du i x) :=
    fun i => (hφ i).sub (hDu i)
  have hsum_i : ∀ i : Fin d, Measurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)) i
          * (φ i x - Du i x)) :=
    fun i => (hDpHcomp_i i).mul (hφdiff_i i)
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

/-! ### Phase G — closed-form aggregator
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses`.

Mirror of `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
specialised to the **transport family** `μ_n := σ + 1/(n+1)` with
`σ ≥ 0` a.e. and limit `μ_∞ := σ`. Unlike the signed case, the test
direction is `(φ - Du, υ - u)` (non-zero), so all three integrand-level
summands require the full dominator inputs (mirroring the set case).

The wrapper consumes only paper-level hypotheses + measurabilities +
`σ ∈ L^{β+1}_per` and the six abstract dominator certificates. It
discharges all 20 inputs of `mfgOperatorEpsPair_tendsto_transport_perturbation`
via:

* the six AE-strong-measurability witnesses
  (`transport_perturbation_{gN1,gN2,gN3,ηN1,ηN2,ηN3}_meas`),
* per-`n` and limit integrability of the three product summands
  (via `MemLp.of_le_mul` on each factor + `MemLpPer.integrable_mul`,
  and a full-product squeeze for the flux limit case where bare
  `(DpH·v)` may blow up at `μ_∞ = 0`),
* the two pointwise tendsto inputs
  (`transport_perturbation_pointwise_tendsto_H_of_hHat0`,
  `transport_perturbation_pointwise_tendsto_DpH`).

The dominators themselves are consumed as authorised inputs; their
shapes are paper-prescribed and have been landed in
`Hamiltonian/Estimates.lean` (`{Eh,Gf,Gm,Em,Gh,Ef}_*_transport`). -/

/-- **`mfgOperatorEpsPair_tendsto_transport_perturbation_of_beta`** —
bare-`β`/`α`-decoupled underlying transport lemma. Identical to
`mfgOperatorEpsPair_tendsto_transport_perturbation` but takes the bare
exponent `{β : ℝ} (hβ : 0 < β)` instead of the `HypothesisPowerGrowth`
bundle (and drops the unused `RegularityH`/`SimplePowerExponentFacts`
binders). The strict lemma's body uses ONLY `hpow.β`/`hpow.hβ` (never
`measurable_H`), so the decoupling is verbatim with `hpow.β ↦ β`,
`hpow.hβ ↦ hβ`. This is the `measurable_H`-free discharge target for the
transport `_of_rc0_of_aeMeasH` producer (mirrors the set bare-`β` headline
`mfgOperatorEpsPair_tendsto_set_perturbation`). -/
theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_beta
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {β : ℝ} (hβ : 0 < β)
    (φ : Fin d → (Fin d → ℝ) → ℝ) (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    (_hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    (_hσ_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x)
          * (σ x + 1 / ((n : ℝ) + 1) - m x))
        (volume.restrict (UnitCube d)))
    (h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (σ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        (σ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x))
        (volume.restrict (UnitCube d)))
    (h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => φ i x) (σ x) + V x)
          * (σ x - m x))
        (volume.restrict (UnitCube d)))
    (h_int2_lim :
      Integrable (fun x =>
        σ x
          * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x)))
        (volume.restrict (UnitCube d)))
    (h_int3_lim :
      Integrable (fun x =>
        (σ x - 1) * (υ x - u x))
        (volume.restrict (UnitCube d)))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x)
    (hgN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x)
        (volume.restrict (UnitCube d)))
    (hηN1_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
        (volume.restrict (UnitCube d)))
    (hgN2_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ x + 1 / ((n : ℝ) + 1))
        (volume.restrict (UnitCube d)))
    (hηN2_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x =>
          DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x))
        (volume.restrict (UnitCube d)))
    (hgN3_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => σ x + 1 / ((n : ℝ) + 1) - 1)
        (volume.restrict (UnitCube d)))
    (hηN3_meas : ∀ _n : ℕ,
      AEStronglyMeasurable (fun x => υ x - u x)
        (volume.restrict (UnitCube d)))
    (hPointwise_H :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n : ℕ =>
            -(υ x) - H x (fun i => φ i x)
                  (σ x + 1 / ((n : ℝ) + 1)) + V x)
          Filter.atTop
          (𝓝 (-(υ x) - H x (fun i => φ i x)
                    (σ x) + V x)))
    (hPointwise_DpH_prod :
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
                ⬝ (fun i => φ i x - Du i x))))) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
  set μN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => σ x + 1 / ((n : ℝ) + 1) with hμN
  set μInf : (Fin d → ℝ) → ℝ := σ with hμInf
  set ηN : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => σ x + 1 / ((n : ℝ) + 1) - m x with hηN
  set ηInf : (Fin d → ℝ) → ℝ := fun x => σ x - m x with hηInf
  have h_one_div_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h_μN_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x) Filter.atTop (𝓝 (μInf x)) := by
    intro x
    have := h_one_div_tendsto.const_add (σ x)
    simpa [hμN, hμInf, add_zero] using this
  have h_ηN_pointwise :
      ∀ x, Filter.Tendsto (fun n => ηN n x) Filter.atTop (𝓝 (ηInf x)) := by
    intro x
    have := (h_one_div_tendsto.const_add (σ x)).sub_const (m x)
    simpa [hηN, hηInf, add_zero] using this
  have h_μN1_pointwise :
      ∀ x, Filter.Tendsto (fun n => μN n x - 1) Filter.atTop
              (𝓝 (μInf x - 1)) :=
    fun x => (h_μN_pointwise x).sub_const 1
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
  have h_νconst_ae :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun _ : ℕ => υ x - u x) Filter.atTop
          (𝓝 (υ x - u x)) :=
    Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  have hβ_pos : 0 < β := hβ
  have h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => φ i x) (μN n x) + V x) * ηN n x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => φ i x) (μInf x) + V x) * ηInf x)) := by
    refine Hamiltonian.tendsto_setIntegral_HJB_mul_of_dom (β := β) hβ_pos
      (gN := fun n x =>
        -(υ x) - H x (fun i => φ i x) (μN n x) + V x)
      (gInf := fun x =>
        -(υ x) - H x (fun i => φ i x) (μInf x) + V x)
      (ηN := ηN) (ηInf := ηInf)
      hGh_memLp hEh_memLp hgN1_meas hηN1_meas hGh_bd hEh_bd ?_ h_ηN_ae
    exact hPointwise_H
  have h_tendsto2 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          μN n x * (DpH x (fun i => φ i x) (μN n x)
                      ⬝ (fun i => φ i x - Du i x)))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          μInf x * (DpH x (fun i => φ i x) (μInf x)
                      ⬝ (fun i => φ i x - Du i x)))) := by
    set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d)
    set bound : (Fin d → ℝ) → ℝ := fun x => Gf x * Ef x with hbound
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
    have hprod_meas : ∀ n,
        AEStronglyMeasurable
          (fun x => μN n x * (DpH x (fun i => φ i x) (μN n x)
                        ⬝ (fun i => φ i x - Du i x))) μm :=
      fun n => (hgN2_meas n).mul (hηN2_meas n)
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hprod_bd : ∀ n, ∀ᵐ x ∂μm,
        ‖μN n x * (DpH x (fun i => φ i x) (μN n x)
                    ⬝ (fun i => φ i x - Du i x))‖ ≤ bound x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    have hprod_lim : ∀ᵐ x ∂μm,
        Filter.Tendsto
          (fun n => μN n x * (DpH x (fun i => φ i x) (μN n x)
                      ⬝ (fun i => φ i x - Du i x)))
          Filter.atTop
          (𝓝 (μInf x * (DpH x (fun i => φ i x) (μInf x)
                      ⬝ (fun i => φ i x - Du i x)))) := by
      filter_upwards [hPointwise_DpH_prod] with x hx
      simpa [μN, μInf] using hx
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hprod_meas hbound_int hprod_bd hprod_lim
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
  have h_main :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (μN n) υ
            (fun i x => φ i x - Du i x)
            (ηN n) (fun x => υ x - u x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ μInf υ
              (fun i x => φ i x - Du i x)
              ηInf (fun x => υ x - u x))) := by
    refine mfgOperatorEpsPair_tendsto_of_summands
      (V := V) (H := H) (DpH := DpH)
      φ υ (fun i x => φ i x - Du i x) (fun x => υ x - u x)
      μN μInf ηN ηInf
      h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
      h_tendsto1 h_tendsto2 h_tendsto3
  have h_test_eq :
      (fun x => υ x - u x) = υ - u := by
    funext x; rfl
  rw [h_test_eq] at h_main
  have h_ηInf_eq : ηInf = σ - m := by
    funext x; simp [hηInf, Pi.sub_apply]
  rw [h_ηInf_eq] at h_main
  exact h_main

/-- **`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`**
(D2b-1c-ii-c3a) — the `measurable_H`-free / `HdeltaK0`-instantiable transport
producer. Mirrors the SET c2b keystone
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`
for the full-flux/mass transport family (test triple `(σ, υ, φ - Du)`, no
`S.indicator ρ` wrapper).

Consumes per-`n` + boundary H AE composites (`hHcomp_ae_n`/`hHcomp_ae_lim`,
replacing `hpow.measurable_H`), the global joint DpH measurability
`hDpH_meas` (D2b-1a), and the genuine individual fields
`hcont_H_pm`/`hH_rc0`/`hcont_DpH_pm`/`hDpH_upper` at bare exponents
`{C α β} hα hβ`. NO `RegularityH`/`HypothesisPowerGrowth`/`measurable_H`
binder. Routes through `transport_perturbation_gN1_meas_of_aeMeasH`,
`transport_perturbation_ηN2_meas_of_meas`,
`transport_perturbation_pointwise_tendsto_H_of_cont`,
`transport_perturbation_pointwise_tendsto_DpH_of_fields`, and discharges
through the bare-`β` lemma `…_transport_perturbation_of_beta`. -/
theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
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
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    (hσ : Measurable σ)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hφ : ∀ i, Measurable (φ i)) (hDu : ∀ i, Measurable (Du i))
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x))
      (volume.restrict (UnitCube d)))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
  -- Standing positivity facts on the bare exponents.
  have hα_pos : 0 < α := lt_trans Real.zero_lt_one hα
  have hβ_pos : 0 < β := hβ
  have hbb_pos : 0 < β + 1 := by linarith
  have hβp_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ_pos
  -- Six measurability witnesses (gN1 / ηN2 routed through the AE / meas
  -- variants; the others are the strict transport witnesses).
  have hgN1_meas := transport_perturbation_gN1_meas_of_aeMeasH (H := H)
    (σ := σ) (V := V) (υ := υ) (φ := φ)
    hV.aestronglyMeasurable hυ.aestronglyMeasurable hHcomp_ae_n
  have hηN1_meas := transport_perturbation_ηN1_meas hσ hm
    (σ := σ) (m := m)
  have hgN2_meas := transport_perturbation_gN2_meas hσ
    (σ := σ)
  have hηN2_meas := transport_perturbation_ηN2_meas_of_meas hDpH_meas hσ hφ hDu
    (σ := σ) (φ := φ) (Du := Du)
  have hgN3_meas := transport_perturbation_gN3_meas hσ
    (σ := σ)
  have hηN3_meas := transport_perturbation_ηN3_meas hυ hu
    (υ := υ) (u := u)
  -- Pointwise tendsto inputs (continuity-only H / DpH-of-fields).
  have hPointwise_H :=
    transport_perturbation_pointwise_tendsto_H_of_cont (V := V) (υ := υ)
      hcont_H_pm hH_rc0 (σ := σ) hσ_nn φ
  have hPointwise_DpH_prod :=
    transport_perturbation_pointwise_tendsto_DpH_of_fields (DpH := DpH)
      hα hβ hcont_DpH_pm hDpH_upper
      (σ := σ) hσ_nn φ Du
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
        (-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x)
          * (σ x + 1 / ((n : ℝ) + 1) - m x)) μm := by
    intro n
    have hgN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x‖
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
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x + 1 / ((n : ℝ) + 1) - m x‖
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
        (σ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x))) μm := by
    intro n
    have hgN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => σ x + 1 / ((n : ℝ) + 1)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ (1 : ℝ) * ‖Gf x‖ := by
        filter_upwards [hGf_bd n] with x hx
        have hGf_nn : 0 ≤ Gf x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGf_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGf_memLp.toMemLp (hgN2_meas n) hbd)
    have hηN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => DpH x (fun i => φ i x)
                  (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x)‖ ≤ (1 : ℝ) * ‖Ef x‖ := by
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
        (σ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x)) μm := by
    intro n
    have hgN3_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => σ x + 1 / ((n : ℝ) + 1) - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x + 1 / ((n : ℝ) + 1) - 1‖
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
  -- Limit H composite consumed as `hHcomp_ae_lim` (NO `hpow.measurable_H`).
  have hgN1_lim_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => φ i x) (σ x) + V x) μm := by
    exact (((hυ.aemeasurable.neg).sub hHcomp_ae_lim).add
      hV.aemeasurable).aestronglyMeasurable
  have hηN1_lim_meas :
      AEStronglyMeasurable (fun x => σ x - m x) μm :=
    (hσ.sub hm).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => φ i x) (σ x) + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(υ x) - H x (fun i => φ i x)
            (σ x + 1 / ((n : ℝ) + 1)) + V x‖)
      Filter.atTop
      (𝓝 ‖-(υ x) - H x (fun i => φ i x) (σ x) + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have hEh_bd_lim :
      ∀ᵐ x ∂μm, ‖σ x - m x‖ ≤ Eh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x :=
      MeasureTheory.ae_all_iff.mpr hEh_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          σ x + 1 / ((n : ℝ) + 1) - m x) Filter.atTop
          (𝓝 (σ x - m x)) := by
      have := (h_one_div_tendsto.const_add (σ x)).sub_const (m x)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖σ x + 1 / ((n : ℝ) + 1) - m x‖)
      Filter.atTop (𝓝 ‖σ x - m x‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => φ i x) (σ x) + V x)
          * (σ x - m x)) μm := by
    have hgN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β))
          (fun x => -(υ x) - H x (fun i => φ i x) (σ x) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => φ i x) (σ x) + V x‖
            ≤ (1 : ℝ) * ‖Gh x‖ := by
        filter_upwards [hGh_bd_lim, hGh_bd 0] with x hx h0
        have hGh_nn : 0 ≤ Gh x := (norm_nonneg _).trans h0
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGh_nn, one_mul]
        exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGh_memLp.toMemLp hgN1_lim_meas hbd)
    have hηN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => σ x - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x - m x‖ ≤ (1 : ℝ) * ‖Eh x‖ := by
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
  -- Limit DpH composite uses `hDpH_meas.comp` (STRICT; global D2b-1a).
  have h_int2_lim :
      Integrable (fun x =>
        σ x
          * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))) μm := by
    have hφ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => φ i x)) :=
      measurable_pi_iff.mpr hφ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => φ i x), σ x)) :=
      measurable_id.prodMk (hφ_pi.prodMk hσ)
    have hDpHcomp : Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x)) :=
      hDpH_meas.comp hxpm
    have hDpHcomp_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x) i) :=
      fun i => (measurable_pi_apply i).comp hDpHcomp
    have hφdiff_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) => φ i x - Du i x) :=
      fun i => (hφ i).sub (hDu i)
    have hsum_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x) i
            * (φ i x - Du i x)) :=
      fun i => (hDpHcomp_i i).mul (hφdiff_i i)
    have hdot : Measurable
        (fun x : (Fin d → ℝ) =>
          ∑ i : Fin d,
            DpH x (fun i => φ i x) (σ x) i
              * (φ i x - Du i x)) :=
      Finset.measurable_sum _ (fun i _ => hsum_i i)
    have hdot_eq :
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x)
            ⬝ (fun i => φ i x - Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                DpH x (fun i => φ i x) (σ x) i
                  * (φ i x - Du i x)) := by
      funext x; rfl
    have hflux_lim_meas :
        AEStronglyMeasurable
          (fun x => DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x)) μm := by
      rw [hdot_eq]; exact hdot.aestronglyMeasurable
    have hprod_lim_meas :
        AEStronglyMeasurable
          (fun x => σ x
              * (DpH x (fun i => φ i x) (σ x)
                  ⬝ (fun i => φ i x - Du i x))) μm :=
      hσ.aestronglyMeasurable.mul hflux_lim_meas
    have hbound_int : Integrable (fun x => Gf x * Ef x) μm :=
      Periodic.MemLpPer.integrable_mul hflux_pq hGf_memLp hEf_memLp
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hprod_bd_n : ∀ n : ℕ, ∀ᵐ x ∂μm,
        ‖(σ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x))‖ ≤ Gf x * Ef x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    have hprod_bd_lim : ∀ᵐ x ∂μm,
        ‖σ x * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))‖ ≤ Gf x * Ef x := by
      have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
          ‖(σ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x))‖ ≤ Gf x * Ef x :=
        MeasureTheory.ae_all_iff.mpr hprod_bd_n
      filter_upwards [hPointwise_DpH_prod, h_all_n] with x hx_pt h_seq
      have h_norm_lim : Filter.Tendsto
        (fun n : ℕ => ‖(σ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x))‖)
        Filter.atTop
        (𝓝 ‖σ x * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))‖) :=
        (continuous_norm.tendsto _).comp hx_pt
      exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
        (Filter.Eventually.of_forall h_seq)
    have hbd' : ∀ᵐ x ∂μm,
        ‖σ x * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))‖ ≤ ‖Gf x * Ef x‖ := by
      filter_upwards [hprod_bd_lim, hGf_nn, hEf_nn] with x hx h1 h2
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg h1 h2)]
      simp only [Real.norm_eq_abs] at hx
      exact hx
    exact hbound_int.mono hprod_lim_meas hbd'
  -- Mass limit-integrability.
  have hgN3_lim_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => σ x - 1) μm :=
    (hσ.sub_const _).aestronglyMeasurable
  have hηN3_lim_meas :
      AEStronglyMeasurable (fun x : (Fin d → ℝ) => υ x - u x) μm :=
    (hυ.sub hu).aestronglyMeasurable
  have hGm_bd_lim :
      ∀ᵐ x ∂μm, ‖σ x - 1‖ ≤ Gm x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x :=
      MeasureTheory.ae_all_iff.mpr hGm_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          σ x + 1 / ((n : ℝ) + 1) - 1) Filter.atTop
          (𝓝 (σ x - 1)) := by
      have := (h_one_div_tendsto.const_add (σ x)).sub_const (1 : ℝ)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖σ x + 1 / ((n : ℝ) + 1) - 1‖)
      Filter.atTop (𝓝 ‖σ x - 1‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int3_lim :
      Integrable (fun x => (σ x - 1) * (υ x - u x)) μm := by
    have hgN3_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (β + 1))
          (fun x => σ x - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x - 1‖ ≤ (1 : ℝ) * ‖Gm x‖ := by
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
  -- Apply the bare-`β`-decoupled underlying transport lemma.
  exact mfgOperatorEpsPair_tendsto_transport_perturbation_of_beta
    (V := V) (H := H) (DpH := DpH)
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    (β := β) hβ φ υ u Du m σ hσ_memLp hσ_nn
    h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    Gf Ef hGf_memLp hEf_memLp hGf_bd hEf_bd
    Gm Em hGm_memLp hEm_memLp hGm_bd hEm_bd
    hgN1_meas hηN1_meas hgN2_meas hηN2_meas hgN3_meas hηN3_meas
    hPointwise_H hPointwise_DpH_prod

theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0
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
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    -- Measurabilities of the test-triple structural data.
    (hσ : Measurable σ)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hφ : ∀ i, Measurable (φ i)) (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `σ`.
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    -- `MemLpPer` of `σ` at `βBarReal` (paper-canonical when
    -- `βBarReal = β + 1`; the headline only requires the abstract
    -- exponent, not the paper exponent, since the slot is underscored
    -- in the consumer body).
    (hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    -- The six dominator pairs with `MemLpPer` certificates and the six
    -- a.e. pointwise bounds (authorised inputs).
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    -- iter 0617 flux-pair retype: `(γ̄', γ̄) → (β̄, β̄')`.
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
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
  have hgN1_meas := transport_perturbation_gN1_meas hpow hσ hV hυ hφ
    (σ := σ) (V := V) (υ := υ) (φ := φ)
  have hηN1_meas := transport_perturbation_ηN1_meas hσ hm
    (σ := σ) (m := m)
  have hgN2_meas := transport_perturbation_gN2_meas hσ
    (σ := σ)
  have hηN2_meas := transport_perturbation_ηN2_meas hpow hσ hφ hDu
    (σ := σ) (φ := φ) (Du := Du)
  have hgN3_meas := transport_perturbation_gN3_meas hσ
    (σ := σ)
  have hηN3_meas := transport_perturbation_ηN3_meas hυ hu
    (υ := υ) (u := u)
  -- Pointwise tendsto inputs.
  have hPointwise_H :=
    transport_perturbation_pointwise_tendsto_H_of_rc0
      (V := V) hRegH hH_rc0
      (σ := σ) (υ := υ) hσ_nn φ
  have hPointwise_DpH_prod :=
    transport_perturbation_pointwise_tendsto_DpH (DpH := DpH) hpow
      (σ := σ) hσ_nn φ Du
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
        (-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x)
          * (σ x + 1 / ((n : ℝ) + 1) - m x)) μm := by
    intro n
    have hgN1_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => -(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1)) + V x‖
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
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x + 1 / ((n : ℝ) + 1) - m x‖
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
        (σ x + 1 / ((n : ℝ) + 1))
          * (DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x))) μm := by
    intro n
    have hgN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => σ x + 1 / ((n : ℝ) + 1)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ (1 : ℝ) * ‖Gf x‖ := by
        filter_upwards [hGf_bd n] with x hx
        have hGf_nn : 0 ≤ Gf x := (norm_nonneg _).trans hx
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg hGf_nn, one_mul]
        rw [Real.norm_eq_abs] at hx; exact hx
      exact MemLp.toMemLpPer
        (MemLp.of_le_mul hGf_memLp.toMemLp (hgN2_meas n) hbd)
    have hηN2_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => DpH x (fun i => φ i x)
                  (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x)) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖DpH x (fun i => φ i x)
                (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x)‖ ≤ (1 : ℝ) * ‖Ef x‖ := by
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
        (σ x + 1 / ((n : ℝ) + 1) - 1) * (υ x - u x)) μm := by
    intro n
    have hgN3_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => σ x + 1 / ((n : ℝ) + 1) - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x + 1 / ((n : ℝ) + 1) - 1‖
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
        (fun x => -(υ x) - H x (fun i => φ i x) (σ x) + V x) μm := by
    have hφ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => φ i x)) :=
      measurable_pi_iff.mpr hφ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => φ i x), σ x)) :=
      measurable_id.prodMk (hφ_pi.prodMk hσ)
    -- Limit-density H composite consumed only as an AE composite.
    have hHcomp : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => φ i x) (σ x))
        μm :=
      hpow.measurable_H.comp_aemeasurable hxpm.aemeasurable
    exact (((hυ.aemeasurable.neg).sub hHcomp).add
      hV.aemeasurable).aestronglyMeasurable
  have hηN1_lim_meas :
      AEStronglyMeasurable (fun x => σ x - m x) μm :=
    (hσ.sub hm).aestronglyMeasurable
  have hGh_bd_lim :
      ∀ᵐ x ∂μm,
        ‖-(υ x) - H x (fun i => φ i x) (σ x) + V x‖ ≤ Gh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x :=
      MeasureTheory.ae_all_iff.mpr hGh_bd
    filter_upwards [hPointwise_H, h_all_n] with x hx_pt h_seq
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖-(υ x) - H x (fun i => φ i x)
            (σ x + 1 / ((n : ℝ) + 1)) + V x‖)
      Filter.atTop
      (𝓝 ‖-(υ x) - H x (fun i => φ i x) (σ x) + V x‖) :=
      (continuous_norm.tendsto _).comp hx_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have hEh_bd_lim :
      ∀ᵐ x ∂μm, ‖σ x - m x‖ ≤ Eh x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x :=
      MeasureTheory.ae_all_iff.mpr hEh_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          σ x + 1 / ((n : ℝ) + 1) - m x) Filter.atTop
          (𝓝 (σ x - m x)) := by
      have := (h_one_div_tendsto.const_add (σ x)).sub_const (m x)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖σ x + 1 / ((n : ℝ) + 1) - m x‖)
      Filter.atTop (𝓝 ‖σ x - m x‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => φ i x) (σ x) + V x)
          * (σ x - m x)) μm := by
    have hgN1_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
          (fun x => -(υ x) - H x (fun i => φ i x) (σ x) + V x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖-(υ x) - H x (fun i => φ i x) (σ x) + V x‖
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
          (fun x => σ x - m x) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x - m x‖ ≤ (1 : ℝ) * ‖Eh x‖ := by
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
        σ x
          * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))) μm := by
    have hφ_pi : Measurable
        (fun x : (Fin d → ℝ) => (fun i : Fin d => φ i x)) :=
      measurable_pi_iff.mpr hφ
    have hxpm : Measurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => φ i x), σ x)) :=
      measurable_id.prodMk (hφ_pi.prodMk hσ)
    have hDpHcomp : Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x)) :=
      hpow.measurable_DpH.comp hxpm
    have hDpHcomp_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x) i) :=
      fun i => (measurable_pi_apply i).comp hDpHcomp
    have hφdiff_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) => φ i x - Du i x) :=
      fun i => (hφ i).sub (hDu i)
    have hsum_i : ∀ i : Fin d, Measurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x) i
            * (φ i x - Du i x)) :=
      fun i => (hDpHcomp_i i).mul (hφdiff_i i)
    have hdot : Measurable
        (fun x : (Fin d → ℝ) =>
          ∑ i : Fin d,
            DpH x (fun i => φ i x) (σ x) i
              * (φ i x - Du i x)) :=
      Finset.measurable_sum _ (fun i _ => hsum_i i)
    have hdot_eq :
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => φ i x) (σ x)
            ⬝ (fun i => φ i x - Du i x))
          = (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d,
                DpH x (fun i => φ i x) (σ x) i
                  * (φ i x - Du i x)) := by
      funext x; rfl
    have hflux_lim_meas :
        AEStronglyMeasurable
          (fun x => DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x)) μm := by
      rw [hdot_eq]; exact hdot.aestronglyMeasurable
    have hprod_lim_meas :
        AEStronglyMeasurable
          (fun x => σ x
              * (DpH x (fun i => φ i x) (σ x)
                  ⬝ (fun i => φ i x - Du i x))) μm :=
      hσ.aestronglyMeasurable.mul hflux_lim_meas
    have hbound_int : Integrable (fun x => Gf x * Ef x) μm :=
      Periodic.MemLpPer.integrable_mul hflux_pq hGf_memLp hEf_memLp
    have hGf_nn : ∀ᵐ x ∂μm, 0 ≤ Gf x := by
      filter_upwards [hGf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hEf_nn : ∀ᵐ x ∂μm, 0 ≤ Ef x := by
      filter_upwards [hEf_bd 0] with x hx
      exact (norm_nonneg _).trans hx
    have hprod_bd_n : ∀ n : ℕ, ∀ᵐ x ∂μm,
        ‖(σ x + 1 / ((n : ℝ) + 1)) *
          (DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x))‖ ≤ Gf x * Ef x := by
      intro n
      filter_upwards [hGf_bd n, hEf_bd n, hGf_nn, hEf_nn]
        with x hxg hxη hxG hxE
      rw [norm_mul]
      exact mul_le_mul hxg hxη (norm_nonneg _) hxG
    have hprod_bd_lim : ∀ᵐ x ∂μm,
        ‖σ x * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))‖ ≤ Gf x * Ef x := by
      have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
          ‖(σ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x))‖ ≤ Gf x * Ef x :=
        MeasureTheory.ae_all_iff.mpr hprod_bd_n
      filter_upwards [hPointwise_DpH_prod, h_all_n] with x hx_pt h_seq
      have h_norm_lim : Filter.Tendsto
        (fun n : ℕ => ‖(σ x + 1 / ((n : ℝ) + 1)) *
            (DpH x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
              ⬝ (fun i => φ i x - Du i x))‖)
        Filter.atTop
        (𝓝 ‖σ x * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))‖) :=
        (continuous_norm.tendsto _).comp hx_pt
      exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
        (Filter.Eventually.of_forall h_seq)
    have hbd' : ∀ᵐ x ∂μm,
        ‖σ x * (DpH x (fun i => φ i x) (σ x)
              ⬝ (fun i => φ i x - Du i x))‖ ≤ ‖Gf x * Ef x‖ := by
      filter_upwards [hprod_bd_lim, hGf_nn, hEf_nn] with x hx h1 h2
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg h1 h2)]
      simp only [Real.norm_eq_abs] at hx
      exact hx
    exact hbound_int.mono hprod_lim_meas hbd'
  -- Mass limit-integrability.
  have hgN3_lim_meas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => σ x - 1) μm :=
    (hσ.sub_const _).aestronglyMeasurable
  have hηN3_lim_meas :
      AEStronglyMeasurable (fun x : (Fin d → ℝ) => υ x - u x) μm :=
    (hυ.sub hu).aestronglyMeasurable
  have hGm_bd_lim :
      ∀ᵐ x ∂μm, ‖σ x - 1‖ ≤ Gm x := by
    have h_all_n : ∀ᵐ x ∂μm, ∀ n : ℕ,
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x :=
      MeasureTheory.ae_all_iff.mpr hGm_bd
    filter_upwards [h_all_n] with x h_seq
    have h_one_div_tendsto :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_pt :
        Filter.Tendsto (fun n : ℕ =>
          σ x + 1 / ((n : ℝ) + 1) - 1) Filter.atTop
          (𝓝 (σ x - 1)) := by
      have := (h_one_div_tendsto.const_add (σ x)).sub_const (1 : ℝ)
      simpa [add_zero] using this
    have h_norm_lim : Filter.Tendsto
      (fun n : ℕ => ‖σ x + 1 / ((n : ℝ) + 1) - 1‖)
      Filter.atTop (𝓝 ‖σ x - 1‖) :=
      (continuous_norm.tendsto _).comp h_pt
    exact le_of_tendsto_of_tendsto h_norm_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_seq)
  have h_int3_lim :
      Integrable (fun x => (σ x - 1) * (υ x - u x)) μm := by
    have hgN3_lim_memLp :
        Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
          (fun x => σ x - 1) := by
      have hbd : ∀ᵐ x ∂μm,
          ‖σ x - 1‖ ≤ (1 : ℝ) * ‖Gm x‖ := by
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
  exact mfgOperatorEpsPair_tendsto_transport_perturbation
    (V := V) (H := H) (DpH := DpH)
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    hpow hRegH hExp φ υ u Du m σ hσ_memLp hσ_nn
    h_int1_n h_int2_n h_int3_n h_int1_lim h_int2_lim h_int3_lim
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    Gf Ef hGf_memLp hEf_memLp hGf_bd hEf_bd
    Gm Em hGm_memLp hEm_memLp hGm_bd hEm_bd
    hgN1_meas hηN1_meas hgN2_meas hηN2_meas hgN3_meas hηN3_meas
    hPointwise_H hPointwise_DpH_prod

/-- **Hext-bundle wrapper** recovering the original
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses`
signature from the `rc0`-input core `…_of_rc0`. Derives `hH_rc0` from the
`HypothesisHat0`/`Hext_finite_at_zero`/`H_zero_eq_Hext` bundle via
`Hamiltonian.H_rc0_of_hHat0`, then delegates. (T1 / simple-power chain
entry point; the T3 chain calls `…_of_rc0` directly to stay Hext-free.) -/
theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    (hσ : Measurable σ)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hφ : ∀ i, Measurable (φ i)) (hDu : ∀ i, Measurable (Du i))
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) :=
  mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0
    (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hpow hRegH hExp
    (StationaryMFG.Hamiltonian.H_rc0_of_hHat0 hHat0 hFin hAgree)
    φ υ u Du m V σ hσ hm hV hυ hu hφ hDu hσ_nn hσ_memLp
    Gh Eh hGh_memLp hEh_memLp hGh_bd hEh_bd
    Gf Ef hGf_memLp hEf_memLp hGf_bd hEf_bd
    Gm Em hGm_memLp hEm_memLp hGm_bd hEm_bd

/-! ### Hext-free `rc0` cores for the signed user-probe / user-triple families

The signed **user-probe** perturbation is
`μ_n x := m x + σ · m x · 𝟙_S x + 1/(n+1)` with user-supplied test triple
`(υ, Dυ)` and difference gradient `Dυ - Du`, primal-density base `m`, and
HJB-difference base `m` (the difference subtracts the *same* base `m`).

The signed **user-triple** perturbation has the same shape with a
user-supplied primal density `μF` as the test base while the HJB/mass
difference subtracts an *independent* base `m` (`= mOf q` at the call
site, generally `μF ≠ m`).

Both perturbations have the algebraic form of the **set** perturbation
`S'.indicator ρ + 1/(n+1)` at `S' := Set.univ`,
`ρ := (test base) + σ · (test base) · 𝟙_S`. So both `rc0` cores reduce to
the set core
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0`
exactly as `signed_perturbation_pointwise_tendsto_H_of_rc0` reduces to the
set pointwise leaf. The reduction needs only
`Set.indicator_univ : Set.univ.indicator f = f` to collapse the outer
`Set.univ` indicator in the set core's conclusion into the raw `ρ`. These
cores stay `Hext_finite_at_zero`-free (they take the line-1821
right-continuity certificate `hH_rc0` directly, inherited from the set
core).

The two cores are the analytic foundation for the substituted-pair
`hMinty_signed_user_{probe,triple}` δ-limit wrappers consumed by
the AE-route successor `strongAepsi_deltaK0_family_of_selectorData_ae`
via `hVIeps_signed_user_{probe,triple}_of_KAepsi_VI`. -/

/-- **Hext-free `rc0` core for the signed user-probe family.** Operator
continuity along `μ_n := m + σ·m·𝟙_S + 1/(n+1)` with user test `(υ, Dυ)`
and difference gradient `Dυ - Du`. Reduces to the set core at
`S' := Set.univ`, `ρ := m + σ·m·𝟙_S` (the HJB/mass difference subtracts
the same base `m`). -/
theorem mfgOperatorEpsPair_tendsto_signed_user_probe_perturbation_of_paperHypotheses_of_rc0
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
    -- Test/structural data.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    -- Measurabilities.
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `m`.
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    -- `MemLpPer` of the perturbation base `m + σ·m·𝟙_S` at `βBarReal`.
    (hpert_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        (fun x => m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    -- The six dominator pairs (bounds stated at the user-probe perturbation).
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x + σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x + σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x + σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => m x + σ * m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ i x - Du i x)
          (fun x => (m x + σ * m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - m x)
          (fun x => υ x - u x))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            υ
            (fun i x => Dυ i x - Du i x)
            (fun x => (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m x)
            (fun x => υ x - u x))) := by
  -- Perturbation base `ρ := m + σ·m·𝟙_S`; reduce to the set core at
  -- `S' := Set.univ`, `ρ`.
  set ρ : (Fin d → ℝ) → ℝ :=
    fun x => m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ_def
  -- A.e. non-negativity of `ρ` (mirrors `signed_perturbation_pointwise_…`).
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  have hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hm_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    show 0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = m x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  -- Measurability of `ρ`.
  have hρ_meas : Measurable ρ := by
    have hind : Measurable (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) :=
      (measurable_const).indicator hS
    exact (hm.add ((measurable_const.mul hm).mul hind))
  -- `MemLpPer` of `Set.univ.indicator ρ` from `hpert_memLp` (= `MemLpPer ρ`).
  have hUnivρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    simpa only [Set.indicator_univ, hρ_def] using hpert_memLp
  -- Apply the set core at `S' := Set.univ`, `ρ`; rewrite the six bounds.
  have h_set :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0
      (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hpow hRegH hExp hH_rc0
      Dυ υ u Du m V (Set.univ) ρ
      MeasurableSet.univ hρ_meas hm hV hυ hu hDυ hDu
      hρ_nn hUnivρ_memLp
      Gh Eh hGh_memLp hEh_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGh_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEh_bd n)
      Gf Ef hGf_memLp hEf_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGf_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEf_bd n)
      Gm Em hGm_memLp hEm_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGm_bd n)
      (by simpa only [Set.indicator_univ, hρ_def] using hEm_bd)
  -- Collapse `Set.univ.indicator ρ` to `ρ` in the set core's conclusion.
  simpa only [Set.indicator_univ, hρ_def] using! h_set

/-- **Hext-free `rc0` core for the signed user-triple family.** Operator
continuity along `μ_n := μF + σ·μF·𝟙_S + 1/(n+1)` with user-supplied
primal density `μF` (the test base) and an independent HJB/mass-difference
base `m` (`= mOf q` at the call site). Reduces to the set core at
`S' := Set.univ`, `ρ := μF + σ·μF·𝟙_S`. -/
theorem mfgOperatorEpsPair_tendsto_signed_user_triple_perturbation_of_paperHypotheses_of_rc0
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
    -- Test/structural data: `μF` is the user primal base; `m` is the
    -- independent difference base.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (μF m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    -- Measurabilities.
    (hμF : Measurable μF) (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `μF`.
    (hμF_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μF x)
    -- `MemLpPer` of the perturbation base `μF + σ·μF·𝟙_S` at `βBarReal`.
    (hpert_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        (fun x => μF x + σ * μF x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    -- The six dominator pairs (bounds at the user-triple perturbation).
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (μF x + σ * μF x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μF x + σ * μF x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μF x + σ * μF x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (μF x + σ * μF x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μF x + σ * μF x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => μF x + σ * μF x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ i x - Du i x)
          (fun x => (μF x + σ * μF x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - m x)
          (fun x => υ x - u x))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => μF x + σ * μF x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            υ
            (fun i x => Dυ i x - Du i x)
            (fun x => (μF x + σ * μF x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m x)
            (fun x => υ x - u x))) := by
  -- Perturbation base `ρ := μF + σ·μF·𝟙_S`; reduce to the set core at
  -- `S' := Set.univ`, `ρ`. The HJB/mass difference base stays `m`.
  set ρ : (Fin d → ℝ) → ℝ :=
    fun x => μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ_def
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  have hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hμF_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    show 0 ≤ μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = μF x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  have hρ_meas : Measurable ρ := by
    have hind : Measurable (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) :=
      (measurable_const).indicator hS
    exact (hμF.add ((measurable_const.mul hμF).mul hind))
  have hUnivρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    simpa only [Set.indicator_univ, hρ_def] using hpert_memLp
  have h_set :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0
      (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hpow hRegH hExp hH_rc0
      Dυ υ u Du m V (Set.univ) ρ
      MeasurableSet.univ hρ_meas hm hV hυ hu hDυ hDu
      hρ_nn hUnivρ_memLp
      Gh Eh hGh_memLp hEh_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGh_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEh_bd n)
      Gf Ef hGf_memLp hEf_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGf_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEf_bd n)
      Gm Em hGm_memLp hEm_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGm_bd n)
      (by simpa only [Set.indicator_univ, hρ_def] using hEm_bd)
  simpa only [Set.indicator_univ, hρ_def] using! h_set

/-- **`measurable_H`-free `rc0` producer for the signed user-probe family**
(D2b-1c-ii-c3b). The `HdeltaK0`-instantiable sibling of
`mfgOperatorEpsPair_tendsto_signed_user_probe_perturbation_of_paperHypotheses_of_rc0`.

Like the strict producer, it REDUCES to the SET `_of_aeMeasH` keystone
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`
(the c2b keystone, line 5502) at `S' := Set.univ`, `ρ := m + σ·m·𝟙_S` (the
HJB/mass difference subtracts the same base `m`). Instead of the strict global
`hpow.measurable_H` it consumes the two H AE composites at `ρ + 1/(n+1)` and
`ρ`; all other H/DpH data is the genuine individual fields `hDpH_meas`,
`hcont_H_pm`, `hcont_DpH_pm`, `hDpH_upper` at bare exponents `{C α β} hα hβ`.
NO `RegularityH`/`HypothesisPowerGrowth`/`HypothesisHat0`/`measurable_H`
binder. **Additive** — the strict producer is left byte-for-byte intact for
T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_signed_user_probe_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
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
    -- Test/structural data.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hpert_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        (fun x => m x + σ * m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    -- The two H AE composites at the reduced base `ρ := m + σ·m·𝟙_S`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x)
          (m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      (volume.restrict (UnitCube d)))
    -- The six dominator pairs (bounds stated at the user-probe perturbation).
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x + σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x + σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (m x + σ * m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x + σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => m x + σ * m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ i x - Du i x)
          (fun x => (m x + σ * m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - m x)
          (fun x => υ x - u x))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            υ
            (fun i x => Dυ i x - Du i x)
            (fun x => (m x + σ * m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m x)
            (fun x => υ x - u x))) := by
  -- Perturbation base `ρ := m + σ·m·𝟙_S`; reduce to the set `_of_aeMeasH`
  -- keystone at `S' := Set.univ`, `ρ`.
  set ρ : (Fin d → ℝ) → ℝ :=
    fun x => m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ_def
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  have hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hm_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    show 0 ≤ m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        m x + σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = m x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  have hρ_meas : Measurable ρ := by
    have hind : Measurable (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) :=
      (measurable_const).indicator hS
    exact (hm.add ((measurable_const.mul hm).mul hind))
  have hUnivρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    simpa only [Set.indicator_univ, hρ_def] using hpert_memLp
  -- Apply the set `_of_aeMeasH` keystone at `S' := Set.univ`, `ρ`.
  have h_set :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
      (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (C := C) (α := α) (β := β) hα hβ
      hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ u Du m V (Set.univ) ρ
      MeasurableSet.univ hρ_meas hm hV hυ hu hDυ hDu
      hρ_nn hUnivρ_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hHcomp_ae_n n)
      (by simpa only [Set.indicator_univ, hρ_def] using hHcomp_ae_lim)
      Gh Eh hGh_memLp hEh_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGh_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEh_bd n)
      Gf Ef hGf_memLp hEf_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGf_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEf_bd n)
      Gm Em hGm_memLp hEm_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGm_bd n)
      (by simpa only [Set.indicator_univ, hρ_def] using hEm_bd)
  simpa only [Set.indicator_univ, hρ_def] using! h_set

/-- **`measurable_H`-free `rc0` producer for the signed user-triple family**
(D2b-1c-ii-c3b). The `HdeltaK0`-instantiable sibling of
`mfgOperatorEpsPair_tendsto_signed_user_triple_perturbation_of_paperHypotheses_of_rc0`.

REDUCES to the SET `_of_aeMeasH` keystone
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`
at `S' := Set.univ`, `ρ := μF + σ·μF·𝟙_S` (the HJB/mass difference base stays
the independent `m`). Consumes the two H AE composites at `ρ + 1/(n+1)` and
`ρ` plus the genuine individual fields `hDpH_meas`/`hcont_H_pm`/`hcont_DpH_pm`/
`hDpH_upper` at bare exponents `{C α β} hα hβ`. NO `RegularityH`/
`HypothesisPowerGrowth`/`HypothesisHat0`/`measurable_H` binder. **Additive** —
the strict producer is left byte-for-byte intact for T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_signed_user_triple_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
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
    -- Test/structural data: `μF` is the user primal base; `m` is the
    -- independent difference base.
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (μF m V : (Fin d → ℝ) → ℝ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hμF : Measurable μF) (hm : Measurable m) (hV : Measurable V)
    (hυ : Measurable υ) (hu : Measurable u)
    (hDυ : ∀ i, Measurable (Dυ i)) (hDu : ∀ i, Measurable (Du i))
    (hμF_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μF x)
    (hpert_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        (fun x => μF x + σ * μF x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    -- The two H AE composites at the reduced base `ρ := μF + σ·μF·𝟙_S`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x)
          (μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x)
          (μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      (volume.restrict (UnitCube d)))
    -- The six dominator pairs (bounds at the user-triple perturbation).
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => Dυ i x)
              (μF x + σ * μF x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μF x + σ * μF x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μF x + σ * μF x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (μF x + σ * μF x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖μF x + σ * μF x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => μF x + σ * μF x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ i x - Du i x)
          (fun x => (μF x + σ * μF x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - m x)
          (fun x => υ x - u x))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => μF x + σ * μF x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            υ
            (fun i x => Dυ i x - Du i x)
            (fun x => (μF x + σ * μF x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m x)
            (fun x => υ x - u x))) := by
  -- Perturbation base `ρ := μF + σ·μF·𝟙_S`; reduce to the set `_of_aeMeasH`
  -- keystone at `S' := Set.univ`, `ρ`. The HJB/mass difference base stays `m`.
  set ρ : (Fin d → ℝ) → ℝ :=
    fun x => μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hρ_def
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  have hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hμF_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    show 0 ≤ μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        μF x + σ * μF x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = μF x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  have hρ_meas : Measurable ρ := by
    have hind : Measurable (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) :=
      (measurable_const).indicator hS
    exact (hμF.add ((measurable_const.mul hμF).mul hind))
  have hUnivρ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal)
        ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    simpa only [Set.indicator_univ, hρ_def] using hpert_memLp
  have h_set :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
      (ε := ε) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (C := C) (α := α) (β := β) hα hβ
      hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ u Du m V (Set.univ) ρ
      MeasurableSet.univ hρ_meas hm hV hυ hu hDυ hDu
      hρ_nn hUnivρ_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hHcomp_ae_n n)
      (by simpa only [Set.indicator_univ, hρ_def] using hHcomp_ae_lim)
      Gh Eh hGh_memLp hEh_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGh_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEh_bd n)
      Gf Ef hGf_memLp hEf_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGf_bd n)
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hEf_bd n)
      Gm Em hGm_memLp hEm_memLp
      (by intro n; simpa only [Set.indicator_univ, hρ_def] using hGm_bd n)
      (by simpa only [Set.indicator_univ, hρ_def] using hEm_bd)
  simpa only [Set.indicator_univ, hρ_def] using! h_set

/-! ### AE-strong-measurability bridge wrapper for the transport family

`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
relaxes the strict-`Measurable` hypotheses on `V`, `σ`, `υ`, and each
`φ i` of the strict consumer above to
`AEStronglyMeasurable … (volume.restrict (UnitCube d))`. Bridge strategy
mirrors the set-family wrapper
(`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable`,
extended iter 0690 to relax the test-data fields):

* build measurable representatives `V' := hV.mk V`, `σ' := hσ.mk σ`,
  `υ' := hυ.mk υ`, `φ' i := (hφ i).mk (φ i)`;
* transport the six per-`n` bounds and the `hσ_nn`, `hσ_memLp` inputs
  from `(σ, υ, φ, V)` to `(σ', υ', φ', V')`;
* apply the strict consumer at the primed data;
* bridge the resulting `Tendsto` back to the unprimed data in three
  steps: `V' → V` via `mfgOperatorEpsPair_congr_V_ae`, primal triple
  `(φ', σ', υ') → (φ, σ, υ)` via `mfgOperatorEpsPair_congr_ae_primal`,
  and test triple `(φ' - Du, σ' + 1/n - m, υ' - u) → (φ - Du,
  σ + 1/n - m, υ - u)` via `mfgOperatorEpsPair_congr_ae`. -/

theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable
    {ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hpow : HypothesisPowerGrowth H DpH)
    (hRegH : RegularityH H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- Test-triple data.
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    -- Measurabilities of the test-triple structural data.
    (hσ : AEStronglyMeasurable σ (volume.restrict (UnitCube d)))
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hφ : ∀ i, AEStronglyMeasurable (φ i) (volume.restrict (UnitCube d)))
    (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `σ`.
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    -- `MemLpPer` of `σ` at `βBarReal`.
    (hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    -- The six dominator pairs.
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
  -- Build Measurable representatives of `V, σ, υ, φ`.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  set σ' : (Fin d → ℝ) → ℝ := hσ.mk σ with hσ'_def
  have hσ'_meas : Measurable σ' := hσ.measurable_mk
  have hσ_ae : σ =ᵐ[volume.restrict (UnitCube d)] σ' := hσ.ae_eq_mk
  have hσ_ae_symm : σ' =ᵐ[volume.restrict (UnitCube d)] σ := hσ_ae.symm
  set υ' : (Fin d → ℝ) → ℝ := hυ.mk υ with hυ'_def
  have hυ'_meas : Measurable υ' := hυ.measurable_mk
  have hυ_ae : υ =ᵐ[volume.restrict (UnitCube d)] υ' := hυ.ae_eq_mk
  have hυ_ae_symm : υ' =ᵐ[volume.restrict (UnitCube d)] υ := hυ_ae.symm
  set φ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hφ i).mk (φ i) with hφ'_def
  have hφ'_meas : ∀ i, Measurable (φ' i) := fun i => (hφ i).measurable_mk
  have hφ_ae : ∀ i, φ i =ᵐ[volume.restrict (UnitCube d)] φ' i :=
    fun i => (hφ i).ae_eq_mk
  have hφ_ae_symm : ∀ i, φ' i =ᵐ[volume.restrict (UnitCube d)] φ i :=
    fun i => (hφ_ae i).symm
  -- Transport `hσ_nn` from `σ` to `σ'`.
  have hσ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ' x := by
    filter_upwards [hσ_nn, hσ_ae] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Transport `hσ_memLp` from `σ` to `σ'`.
  have hσ'_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ' :=
    Periodic.MemLpPer.congr_ae_unitCube hσ_memLp hσ_ae
  -- Transport the six per-`n` bounds from `(σ, υ, φ, V)` to
  -- `(σ', υ', φ', V')`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ' x) - H x (fun i => φ' i x)
              (σ' x + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hGh_bd n, hV_ae, hυ_ae, hφ_all_ae,
                    hσ_ae] with x hx hVxeq hυxeq hφxeq hσxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    rw [← hVxeq, ← hυxeq, ← hσxeq, ← hpt]
    exact hx
  have hEh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x := by
    intro n
    filter_upwards [hEh_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hGf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x := by
    intro n
    filter_upwards [hGf_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hEf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ' i x)
              (σ' x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ' i x - Du i x)‖ ≤ Ef x := by
    intro n
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hEf_bd n, hσ_ae, hφ_all_ae] with x hx hσxeq hφxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    have hptsub : (fun i => φ i x - Du i x) = (fun i => φ' i x - Du i x) := by
      funext i; rw [hφxeq i]
    rw [← hσxeq, ← hpt, ← hptsub]
    exact hx
  have hGm_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x := by
    intro n
    filter_upwards [hGm_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hEm_bd' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ' x - u x‖ ≤ Em x := by
    filter_upwards [hEm_bd, hυ_ae] with x hx hυxeq
    rw [← hυxeq]; exact hx
  -- Apply the strict consumer at the primed data `(σ', υ', φ', V')`.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal')
      hpow hRegH hExp hHat0 hFin hAgree
      φ' υ' u Du m V' σ'
      hσ'_meas hm hV'_meas hυ'_meas hu hφ'_meas hDu hσ'_nn hσ'_memLp
      Gh Eh hGh_memLp hEh_memLp hGh_bd' hEh_bd'
      Gf Ef hGf_memLp hEf_memLp hGf_bd' hEf_bd'
      Gm Em hGm_memLp hEm_memLp hGm_bd' hEm_bd'
  -- Bridge the primed `Tendsto` back to the unprimed data in three steps:
  -- (i) `V' → V` via `mfgOperatorEpsPair_congr_V_ae`,
  -- (ii) primal triple `(φ', σ', υ') → (φ, σ, υ)` via
  --      `mfgOperatorEpsPair_congr_ae_primal`,
  -- (iii) test triple `(φ' - Du, σ' + 1/n - m, υ' - u) →
  --       (φ - Du, σ + 1/n - m, υ - u)` via `mfgOperatorEpsPair_congr_ae`.
  -- Per-`n` rewrites for the sequence side.
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => φ' i x - Du i x)
          (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u) := by
    intro n
    -- Step (i): swap V' → V.
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
        (fun i x => φ' i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hV_ae_symm
    -- Step (ii): swap primal `(φ', σ', υ') → (φ, σ, υ)`.
    have hμ_ae : (fun x => σ' x + 1 / ((n : ℝ) + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => σ x + 1 / ((n : ℝ) + 1)) := by
      filter_upwards [hσ_ae_symm] with x hxeq; rw [hxeq]
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ' φ
        (fun x => σ' x + 1 / ((n : ℝ) + 1))
        (fun x => σ x + 1 / ((n : ℝ) + 1))
        υ' υ
        (fun i x => φ' i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hφ_ae_symm hμ_ae hυ_ae_symm
    -- Step (iii): swap test data.
    have hDν_ae : ∀ i, (fun x => φ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => φ i x - Du i x) := by
      intro i
      filter_upwards [hφ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x) := by
      filter_upwards [hσ_ae_symm] with x hxeq; rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ i x - Du i x)
            (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
            (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
        (fun i x => φ' i x - Du i x) (fun i x => φ i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  -- Limit-side rewrite (mirror of `hSeq_eq` without the `1/(n+1)` term).
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' σ' υ'
          (fun i x => φ' i x - Du i x)
          (σ' - m) (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ σ υ
          (fun i x => φ i x - Du i x)
          (σ - m) (υ - u) := by
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        φ' σ' υ'
        (fun i x => φ' i x - Du i x)
        (σ' - m) (υ' - u) hV_ae_symm
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ' φ
        σ' σ
        υ' υ
        (fun i x => φ' i x - Du i x)
        (σ' - m) (υ' - u)
        hφ_ae_symm hσ_ae_symm hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => φ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => φ i x - Du i x) := by
      intro i
      filter_upwards [hφ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (σ' - m)
        =ᵐ[volume.restrict (UnitCube d)] (σ - m) := by
      filter_upwards [hσ_ae_symm] with x hxeq
      change σ' x - m x = σ x - m x
      rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ σ υ
        (fun i x => φ' i x - Du i x) (fun i x => φ i x - Du i x)
        (σ' - m) (σ - m)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  -- Stitch the per-`n` and limit rewrites into a `Tendsto` congruence.
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => φ' i x - Du i x)
          (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  exact h_tendsto

/-- **Hext-free (`rc0`) AE-strongly-measurable transport-perturbation
bridge.**

Identical conclusion and AE-strong-measurability interface to
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
above, but instead of the `Hext_finite_at_zero`-pulling triple
`(hHat0, hFin, hAgree)` it takes the **paper line-1821 right-continuity**
rider `hH_rc0` directly and routes the inner strict call through the
Hext-free core
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0`.

This is the reusable bridge that the substituted-pair `hMinty_transport`
δ-limit wrapper (T3 A1d-final, step 7) consumes: the substituted
operator `A_ε^δ` must stay Hext-free, so its operator-continuity
certificate cannot route through the T1 `_of_paperHypotheses` producer.

The body is the same measurable-representative `(V, σ, υ, φ)`-transport
as the `_of_paperHypotheses` aesm variant; only the inner call differs. -/
theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
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
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    -- Measurabilities of the test-triple structural data.
    (hσ : AEStronglyMeasurable σ (volume.restrict (UnitCube d)))
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hφ : ∀ i, AEStronglyMeasurable (φ i) (volume.restrict (UnitCube d)))
    (hDu : ∀ i, Measurable (Du i))
    -- A.e. non-negativity of `σ`.
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    -- `MemLpPer` of `σ` at `βBarReal`.
    (hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    -- The six dominator pairs.
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
  -- Build Measurable representatives of `V, σ, υ, φ`.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  set σ' : (Fin d → ℝ) → ℝ := hσ.mk σ with hσ'_def
  have hσ'_meas : Measurable σ' := hσ.measurable_mk
  have hσ_ae : σ =ᵐ[volume.restrict (UnitCube d)] σ' := hσ.ae_eq_mk
  have hσ_ae_symm : σ' =ᵐ[volume.restrict (UnitCube d)] σ := hσ_ae.symm
  set υ' : (Fin d → ℝ) → ℝ := hυ.mk υ with hυ'_def
  have hυ'_meas : Measurable υ' := hυ.measurable_mk
  have hυ_ae : υ =ᵐ[volume.restrict (UnitCube d)] υ' := hυ.ae_eq_mk
  have hυ_ae_symm : υ' =ᵐ[volume.restrict (UnitCube d)] υ := hυ_ae.symm
  set φ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hφ i).mk (φ i) with hφ'_def
  have hφ'_meas : ∀ i, Measurable (φ' i) := fun i => (hφ i).measurable_mk
  have hφ_ae : ∀ i, φ i =ᵐ[volume.restrict (UnitCube d)] φ' i :=
    fun i => (hφ i).ae_eq_mk
  have hφ_ae_symm : ∀ i, φ' i =ᵐ[volume.restrict (UnitCube d)] φ i :=
    fun i => (hφ_ae i).symm
  -- Transport `hσ_nn` from `σ` to `σ'`.
  have hσ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ' x := by
    filter_upwards [hσ_nn, hσ_ae] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Transport `hσ_memLp` from `σ` to `σ'`.
  have hσ'_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ' :=
    Periodic.MemLpPer.congr_ae_unitCube hσ_memLp hσ_ae
  -- Transport the six per-`n` bounds from `(σ, υ, φ, V)` to
  -- `(σ', υ', φ', V')`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ' x) - H x (fun i => φ' i x)
              (σ' x + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hGh_bd n, hV_ae, hυ_ae, hφ_all_ae,
                    hσ_ae] with x hx hVxeq hυxeq hφxeq hσxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    rw [← hVxeq, ← hυxeq, ← hσxeq, ← hpt]
    exact hx
  have hEh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x := by
    intro n
    filter_upwards [hEh_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hGf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x := by
    intro n
    filter_upwards [hGf_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hEf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ' i x)
              (σ' x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ' i x - Du i x)‖ ≤ Ef x := by
    intro n
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hEf_bd n, hσ_ae, hφ_all_ae] with x hx hσxeq hφxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    have hptsub : (fun i => φ i x - Du i x) = (fun i => φ' i x - Du i x) := by
      funext i; rw [hφxeq i]
    rw [← hσxeq, ← hpt, ← hptsub]
    exact hx
  have hGm_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x := by
    intro n
    filter_upwards [hGm_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hEm_bd' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ' x - u x‖ ≤ Em x := by
    filter_upwards [hEm_bd, hυ_ae] with x hx hυxeq
    rw [← hυxeq]; exact hx
  -- Apply the Hext-free `_of_rc0` core at the primed data `(σ', υ', φ', V')`.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal')
      hpow hRegH hExp hH_rc0
      φ' υ' u Du m V' σ'
      hσ'_meas hm hV'_meas hυ'_meas hu hφ'_meas hDu hσ'_nn hσ'_memLp
      Gh Eh hGh_memLp hEh_memLp hGh_bd' hEh_bd'
      Gf Ef hGf_memLp hEf_memLp hGf_bd' hEf_bd'
      Gm Em hGm_memLp hEm_memLp hGm_bd' hEm_bd'
  -- Bridge the primed `Tendsto` back to the unprimed data in three steps.
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => φ' i x - Du i x)
          (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u) := by
    intro n
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
        (fun i x => φ' i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hV_ae_symm
    have hμ_ae : (fun x => σ' x + 1 / ((n : ℝ) + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => σ x + 1 / ((n : ℝ) + 1)) := by
      filter_upwards [hσ_ae_symm] with x hxeq; rw [hxeq]
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ' φ
        (fun x => σ' x + 1 / ((n : ℝ) + 1))
        (fun x => σ x + 1 / ((n : ℝ) + 1))
        υ' υ
        (fun i x => φ' i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hφ_ae_symm hμ_ae hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => φ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => φ i x - Du i x) := by
      intro i
      filter_upwards [hφ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x) := by
      filter_upwards [hσ_ae_symm] with x hxeq; rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ i x - Du i x)
            (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
            (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
        (fun i x => φ' i x - Du i x) (fun i x => φ i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' σ' υ'
          (fun i x => φ' i x - Du i x)
          (σ' - m) (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ σ υ
          (fun i x => φ i x - Du i x)
          (σ - m) (υ - u) := by
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        φ' σ' υ'
        (fun i x => φ' i x - Du i x)
        (σ' - m) (υ' - u) hV_ae_symm
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ' φ
        σ' σ
        υ' υ
        (fun i x => φ' i x - Du i x)
        (σ' - m) (υ' - u)
        hφ_ae_symm hσ_ae_symm hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => φ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => φ i x - Du i x) := by
      intro i
      filter_upwards [hφ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (σ' - m)
        =ᵐ[volume.restrict (UnitCube d)] (σ - m) := by
      filter_upwards [hσ_ae_symm] with x hxeq
      change σ' x - m x = σ x - m x
      rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ σ υ
        (fun i x => φ' i x - Du i x) (fun i x => φ i x - Du i x)
        (σ' - m) (σ - m)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => φ' i x - Du i x)
          (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  exact h_tendsto

/-- **`measurable_H`-free aesm-input transport-perturbation keystone**
(D2b-1c-ii-c4b). The `HdeltaK0`-instantiable, AE-strongly-measurable-input
sibling of
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`:
it drops the strict `HypothesisPowerGrowth`/`RegularityH` binders and
instead consumes the genuine individual H/DpH fields (bare exponents
`α β`, `hDpH_meas`, `hcont_H_pm`, `hcont_DpH_pm`, `hDpH_upper`) plus the
two H AE composites at the transport base `σ` (replacing
`hRegH.measurable_H`). The proof is the same measurable-representative
`(σ, υ, φ, V)`-transport as the strict aesm bridge; the two H AE
composites are transported across the `(σ, φ)` a.e.-equalities, and the
inner call delegates to the `measurable_H`-free core
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH`.

**Additive** — the strict producer is left byte-for-byte intact for
T1/T2. -/
theorem mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
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
    -- Test-triple data.
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m V : (Fin d → ℝ) → ℝ)
    (σ : (Fin d → ℝ) → ℝ)
    (hσ : AEStronglyMeasurable σ (volume.restrict (UnitCube d)))
    (hm : Measurable m)
    (hV : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hυ : AEStronglyMeasurable υ (volume.restrict (UnitCube d)))
    (hu : Measurable u)
    (hφ : ∀ i, AEStronglyMeasurable (φ i) (volume.restrict (UnitCube d)))
    (hDu : ∀ i, Measurable (Du i))
    (hσ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ x)
    (hσ_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ)
    -- The two H AE composites (replacing `hRegH.measurable_H`).
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x))
      (volume.restrict (UnitCube d)))
    (Gh Eh : (Fin d → ℝ) → ℝ)
    (hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh)
    (hEh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh)
    (hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ x) - H x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x)
    (hEh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x)
    (Gf Ef : (Fin d → ℝ) → ℝ)
    (hGf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf)
    (hEf_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef)
    (hGf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ i x)
              (σ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ i x - Du i x)‖ ≤ Ef x)
    (Gm Em : (Fin d → ℝ) → ℝ)
    (hGm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm)
    (hEm_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em)
    (hGm_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x)
    (hEm_bd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ x - u x‖ ≤ Em x) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u))) := by
  -- Build Measurable representatives of `V, σ, υ, φ`.
  set V' : (Fin d → ℝ) → ℝ := hV.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.measurable_mk
  have hV_ae : V =ᵐ[volume.restrict (UnitCube d)] V' := hV.ae_eq_mk
  have hV_ae_symm : V' =ᵐ[volume.restrict (UnitCube d)] V := hV_ae.symm
  set σ' : (Fin d → ℝ) → ℝ := hσ.mk σ with hσ'_def
  have hσ'_meas : Measurable σ' := hσ.measurable_mk
  have hσ_ae : σ =ᵐ[volume.restrict (UnitCube d)] σ' := hσ.ae_eq_mk
  have hσ_ae_symm : σ' =ᵐ[volume.restrict (UnitCube d)] σ := hσ_ae.symm
  set υ' : (Fin d → ℝ) → ℝ := hυ.mk υ with hυ'_def
  have hυ'_meas : Measurable υ' := hυ.measurable_mk
  have hυ_ae : υ =ᵐ[volume.restrict (UnitCube d)] υ' := hυ.ae_eq_mk
  have hυ_ae_symm : υ' =ᵐ[volume.restrict (UnitCube d)] υ := hυ_ae.symm
  set φ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hφ i).mk (φ i) with hφ'_def
  have hφ'_meas : ∀ i, Measurable (φ' i) := fun i => (hφ i).measurable_mk
  have hφ_ae : ∀ i, φ i =ᵐ[volume.restrict (UnitCube d)] φ' i :=
    fun i => (hφ i).ae_eq_mk
  have hφ_ae_symm : ∀ i, φ' i =ᵐ[volume.restrict (UnitCube d)] φ i :=
    fun i => (hφ_ae i).symm
  -- Transport `hσ_nn` from `σ` to `σ'`.
  have hσ'_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ σ' x := by
    filter_upwards [hσ_nn, hσ_ae] with x hx hxeq
    rw [← hxeq]; exact hx
  -- Transport `hσ_memLp` from `σ` to `σ'`.
  have hσ'_memLp :
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) σ' :=
    Periodic.MemLpPer.congr_ae_unitCube hσ_memLp hσ_ae
  -- Transport the six per-`n` bounds from `(σ, υ, φ, V)` to
  -- `(σ', υ', φ', V')`.
  have hGh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(υ' x) - H x (fun i => φ' i x)
              (σ' x + 1 / ((n : ℝ) + 1)) + V' x‖ ≤ Gh x := by
    intro n
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hGh_bd n, hV_ae, hυ_ae, hφ_all_ae,
                    hσ_ae] with x hx hVxeq hυxeq hφxeq hσxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    rw [← hVxeq, ← hυxeq, ← hσxeq, ← hpt]
    exact hx
  have hEh_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1) - m x‖ ≤ Eh x := by
    intro n
    filter_upwards [hEh_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hGf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x := by
    intro n
    filter_upwards [hGf_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hEf_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => φ' i x)
              (σ' x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => φ' i x - Du i x)‖ ≤ Ef x := by
    intro n
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hEf_bd n, hσ_ae, hφ_all_ae] with x hx hσxeq hφxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    have hptsub : (fun i => φ i x - Du i x) = (fun i => φ' i x - Du i x) := by
      funext i; rw [hφxeq i]
    rw [← hσxeq, ← hpt, ← hptsub]
    exact hx
  have hGm_bd' : ∀ n : ℕ,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖σ' x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x := by
    intro n
    filter_upwards [hGm_bd n, hσ_ae] with x hx hσxeq
    rw [← hσxeq]; exact hx
  have hEm_bd' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖υ' x - u x‖ ≤ Em x := by
    filter_upwards [hEm_bd, hυ_ae] with x hx hυxeq
    rw [← hυxeq]; exact hx
  -- Transport the two H AE composites to the primed `(σ', φ')`.
  have hHcomp_ae_n' : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ' i x) (σ' x + 1 / ((n : ℝ) + 1)))
      (volume.restrict (UnitCube d)) := by
    intro n
    refine (hHcomp_ae_n n).congr ?_
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hσ_ae, hφ_all_ae] with x hσxeq hφxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    rw [← hσxeq, ← hpt]
  have hHcomp_ae_lim' : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ' i x) (σ' x))
      (volume.restrict (UnitCube d)) := by
    refine hHcomp_ae_lim.congr ?_
    have hφ_all_ae :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ i, φ i x = φ' i x := by
      rw [Filter.eventually_all]; exact hφ_ae
    filter_upwards [hσ_ae, hφ_all_ae] with x hσxeq hφxeq
    have hpt : (fun i => φ i x) = (fun i => φ' i x) := by
      funext i; exact hφxeq i
    rw [← hσxeq, ← hpt]
  -- Apply the `measurable_H`-free `_of_rc0_of_aeMeasH` core at the
  -- primed data `(σ', υ', φ', V')`.
  have h_tendsto :=
    mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_rc0_of_aeMeasH
      (ε := ε) (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (C := C) (α := α) (β := β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      φ' υ' u Du m V' σ'
      hσ'_meas hm hV'_meas hυ'_meas hu hφ'_meas hDu hσ'_nn hσ'_memLp
      hHcomp_ae_n' hHcomp_ae_lim'
      Gh Eh hGh_memLp hEh_memLp hGh_bd' hEh_bd'
      Gf Ef hGf_memLp hEf_memLp hGf_bd' hEf_bd'
      Gm Em hGm_memLp hEm_memLp hGm_bd' hEm_bd'
  -- Bridge the primed `Tendsto` back to the unprimed data in three steps.
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => φ' i x - Du i x)
          (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u) := by
    intro n
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
        (fun i x => φ' i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hV_ae_symm
    have hμ_ae : (fun x => σ' x + 1 / ((n : ℝ) + 1))
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => σ x + 1 / ((n : ℝ) + 1)) := by
      filter_upwards [hσ_ae_symm] with x hxeq; rw [hxeq]
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ' φ
        (fun x => σ' x + 1 / ((n : ℝ) + 1))
        (fun x => σ x + 1 / ((n : ℝ) + 1))
        υ' υ
        (fun i x => φ' i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) hφ_ae_symm hμ_ae hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => φ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => φ i x - Du i x) := by
      intro i
      filter_upwards [hφ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x) := by
      filter_upwards [hσ_ae_symm] with x hxeq; rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ' i x - Du i x)
            (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
            (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
            (fun i x => φ i x - Du i x)
            (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
            (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
        (fun i x => φ' i x - Du i x) (fun i x => φ i x - Du i x)
        (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
        (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' σ' υ'
          (fun i x => φ' i x - Du i x)
          (σ' - m) (υ' - u)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ σ υ
          (fun i x => φ i x - Du i x)
          (σ - m) (υ - u) := by
    have hV_step :
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_V_ae
        V' V H DpH γBarReal ε
        φ' σ' υ'
        (fun i x => φ' i x - Du i x)
        (σ' - m) (υ' - u) hV_ae_symm
    have hprimal_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ' σ' υ'
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae_primal
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ' φ
        σ' σ
        υ' υ
        (fun i x => φ' i x - Du i x)
        (σ' - m) (υ' - u)
        hφ_ae_symm hσ_ae_symm hυ_ae_symm
    have hDν_ae : ∀ i, (fun x => φ' i x - Du i x)
        =ᵐ[volume.restrict (UnitCube d)] (fun x => φ i x - Du i x) := by
      intro i
      filter_upwards [hφ_ae_symm i] with x hxeq; rw [hxeq]
    have hη_ae : (σ' - m)
        =ᵐ[volume.restrict (UnitCube d)] (σ - m) := by
      filter_upwards [hσ_ae_symm] with x hxeq
      change σ' x - m x = σ x - m x
      rw [hxeq]
    have hν_ae : (υ' - u) =ᵐ[volume.restrict (UnitCube d)] (υ - u) := by
      filter_upwards [hυ_ae_symm] with x hxeq
      change υ' x - u x = υ x - u x
      rw [hxeq]
    have htest_step :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ' i x - Du i x)
            (σ' - m) (υ' - u)
        =
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ σ υ
            (fun i x => φ i x - Du i x)
            (σ - m) (υ - u) :=
      StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
        (V := V) (H := H) (DpH := DpH) γBarReal ε
        φ σ υ
        (fun i x => φ' i x - Du i x) (fun i x => φ i x - Du i x)
        (σ' - m) (σ - m)
        (υ' - u) (υ - u) hDν_ae hη_ae hν_ae
    rw [hV_step, hprimal_step, htest_step]
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          γBarReal ε
          φ' (fun x => σ' x + 1 / ((n : ℝ) + 1)) υ'
          (fun i x => φ' i x - Du i x)
          (fun x => σ' x + 1 / ((n : ℝ) + 1) - m x)
          (υ' - u))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ (fun x => σ x + 1 / ((n : ℝ) + 1)) υ
          (fun i x => φ i x - Du i x)
          (fun x => σ x + 1 / ((n : ℝ) + 1) - m x)
          (υ - u)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  exact h_tendsto

/-! ## The `RegularizedSequenceData` record -/

/-- **Headline record.** A per-`k` sequence of regularized bare
solutions at parameters `ε_k → 0`, with a uniform Banach-pair-norm
bound.

The `epsSeq` field is the canonical `1 / (k + 1)` sequence (matching
the F.4 design in `Banach/Closure.lean`).

The `uniformBound` field is stated as a single-existential `∃ C, …`,
exactly as required by the task spec. -/
structure RegularizedSequenceData
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] where
  /-- The ε-sequence (canonical: `epsSeq k := 1 / (k + 1)`). -/
  epsSeq : ℕ → ℝ
  /-- Strict positivity of every ε-step. -/
  heps_pos : ∀ k, 0 < epsSeq k
  /-- ε-steps tend to zero. -/
  heps_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0)
  /-- The per-`k` regularized bare solution at parameter `epsSeq k`. -/
  sol : ∀ k, RegularizedBareSolution d (epsSeq k) V H DpH
                γBarReal βBarReal βBarReal' γBarReal'
  /-- A uniform Banach-pair-norm bound on the bridged pairs. -/
  uniformBound :
    ∃ C : ℝ,
      ∀ k, ‖(sol k).toBanachPair‖ ≤ C

namespace RegularizedSequenceData

/-- **Subsequence reindexing.** Given a strict-mono-ish index
`φ : ℕ → ℕ` with `Tendsto φ atTop atTop`, project every field of a
`RegularizedSequenceData` through `φ`. Used by the HMinty drain to
operate on the F.5 weakly-converging subsequence. -/
noncomputable def subseq
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (φ : ℕ → ℕ)
    (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop) :
    RegularizedSequenceData (d := d)
      γBarReal βBarReal βBarReal' γBarReal' V H DpH where
  epsSeq := fun n => seq.epsSeq (φ n)
  heps_pos := fun n => seq.heps_pos (φ n)
  heps_tendsto := seq.heps_tendsto.comp hφ
  sol := fun n => seq.sol (φ n)
  uniformBound := by
    rcases seq.uniformBound with ⟨C, hC⟩
    exact ⟨C, fun n => hC (φ n)⟩

end RegularizedSequenceData

/-! ## Producer: `regularizedSequenceData_of_paperHypotheses`

Per the AC amendment (CONVENTIONS §8), the producer accepts:
* paper hypotheses `(hmon, hpow, hV, hExp)`,
* a per-`k` `AepsiUniformContextK` supplier (the K_Aepsi-form
  context from `infra-P4-domain-indexed-Aepsi-CLM`, with
  K_Aepsi-indexed `auxHypsK`);
* a per-`k` `AepsiUniformContextK` drives the per-`k`
  `RegularizedBareSolution` extraction via
  `exists_regularizedBareSolution_K` (T4 K_Aepsi-form producer).

After `infra-P4-rebuild-T7-AC2-wire-uniform-bound` (this iter): the
previous `{C : ℝ}` and `hNormBound` parameters are replaced by:
* a non-negative real `Capr ≥ 0` (the ε-uniform paper-residue
  apriori constant), and
* a per-`k`-and-sol witness `hCapr` that the **integrated apriori
  sum** `∫ m^β̄ + ∫ |u|^γ̄ + ∑ ∫ |Du i|^γ̄` is bounded by `Capr` at
  every regularised solution.

The producer body bridges `hCapr` to the uniform Banach-pair norm
bound via `norm_toBanachPair_rpow_min_le_apriori_sum` (the
`rpow_min`-translation lemma below) and `Real.rpow_inv_rpow`.

The hypothesis `hCapr` is the bare-data form of
`aprioriBound_at_eps` post-AC1 — i.e. the per-k user combines
`aprioriInputAuxHyps_of_paperHypotheses` (AC1) with
`aprioriBound_at_eps` (F.3) and rewrites the `lpNormPer u^γ̄` slot
as `∫ |u|^γ̄` via `MemLpPer.norm_toLp_rpow_eq`, plus converts
`∫ ‖Du x‖^γ̄` to `∑ i, ∫ |Du i|^γ̄` (Pi-norm-vs-sum, see
`Periodic.sum_succ_rpow_le`). The uniformity of `Capr` across `k`
is the paper-residue "ε-independent apriori constant" claim.

Migrated from the legacy K0-form `AepsiUniformContext` /
`exists_regularizedBareSolution` chain by
`infra-P4-delete-AepsiUniformContext-K0-form`. The K_Aepsi-indexed
`auxHypsK` field on `AepsiUniformContextK` (per
`infra-P4-domain-indexed-Aepsi-CLM`) is consumed *internally* by
`exists_banachVI_at_eps_KAepsi` (called from
`exists_regularizedBareSolution_K`); the consumer here only routes
the context through, so the per-`k` Minty-discharge body is
structurally unchanged.
-/

/-- **AC2 closed-form translation lemma** —
`‖toBanachPair‖^min ≤ 1 + (integrated apriori sum)`.

Given a `RegularizedBareSolution` at exponents `(β̄, γ̄)` with
`β̄, γ̄ > 0`, the `min(β̄, γ̄)`-th power of its Banach-pair norm
reduces to a closed-form bound in terms of the integrated apriori
quantities `∫ |m|^β̄`, `∫ |u|^γ̄`, and `∑ ∫ |Du i|^γ̄`, plus an
additive `1` slack from the `‖q‖ ≤ 1`-region of the
`max_rpow_min_le_one_add_pair_rpow` reduction.

Composes:
* `MemLpPer.norm_pair_rpow_min_le` (`Periodic/Sobolev.lean`) — the
  product-pair `rpow_min` reduction,
* `MemLpPer.norm_toLp_rpow_eq` (`Periodic/Lp.lean`) — `‖toLp‖^β̄ =
  ∫ |m|^β̄`,
* `MemSobolevPer.norm_toLpSobolev_rpow_le` (`Periodic/Sobolev.lean`)
  — `‖toLpSobolev‖^γ̄ ≤ (d+1)^γ̄ · (∫|u|^γ̄ + ∑∫|Du i|^γ̄)`. -/
lemma RegularizedBareSolution.norm_toBanachPair_rpow_min_le_apriori_sum
    {ε : ℝ} {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβ : 0 < βBarReal) (hγ : 0 < γBarReal)
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal') :
    ‖sol.toBanachPair‖ ^ min βBarReal γBarReal
      ≤ 1 + (∫ x in UnitCube d, |sol.m x| ^ βBarReal)
          + ((d : ℝ) + 1) ^ γBarReal *
              ((∫ x in UnitCube d, |sol.u x| ^ γBarReal) +
                ∑ i, ∫ x in UnitCube d, |sol.Du i x| ^ γBarReal) := by
  -- Shorthands.
  set q : XBanach d βBarReal γBarReal := sol.toBanachPair with hq_def
  set q1 : MeasureTheory.Lp ℝ (ENNReal.ofReal βBarReal)
            (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    sol.hmLp.toLp with hq1
  set q2 : Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d :=
    Periodic.MemSobolevPer.toLpSobolev (p := ENNReal.ofReal γBarReal)
      sol.memSobolevPer_u sol.hDuLp with hq2
  -- Identify `q = (q1, q2)` (definitional unfolding through
  -- `toBanachPair`/`banachPairOfBare`).
  have hq_pair : q = (q1, q2) := rfl
  -- `(ENNReal.ofReal *).toReal = *` for nonneg reals.
  have hβtoReal : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
    ENNReal.toReal_ofReal hβ.le
  have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγ.le
  -- Step 1: `rpow_min` reduction at the pair `(q1, q2)`.
  have hStep1 : ‖q‖ ^ min βBarReal γBarReal
        ≤ 1 + ‖q1‖ ^ βBarReal + ‖q2‖ ^ γBarReal := by
    have h := Periodic.MemLpPer.norm_pair_rpow_min_le
      (βBar := ENNReal.ofReal βBarReal) (γBar := ENNReal.ofReal γBarReal)
      (d := d) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top q1 q2
    rw [hβtoReal, hγtoReal] at h
    rw [hq_pair]; exact h
  -- Step 2: identify `‖q1‖^β̄` with `∫ |sol.m|^β̄`.
  have hStep2 : ‖q1‖ ^ βBarReal
        = ∫ x in UnitCube d, |sol.m x| ^ βBarReal := by
    have h := Periodic.MemLpPer.norm_toLp_rpow_eq (d := d)
      (p := ENNReal.ofReal βBarReal)
      (ENNReal.ofReal_pos.mpr hβ).ne' ENNReal.ofReal_ne_top sol.hmLp
    rw [hβtoReal] at h
    exact h
  -- Step 3: bound `‖q2‖^γ̄` via `norm_toLpSobolev_rpow_le`.
  have hStep3 : ‖q2‖ ^ γBarReal
        ≤ ((d : ℝ) + 1) ^ γBarReal *
              ((∫ x in UnitCube d, |sol.u x| ^ γBarReal) +
                ∑ i, ∫ x in UnitCube d, |sol.Du i x| ^ γBarReal) := by
    have h := Periodic.MemSobolevPer.norm_toLpSobolev_rpow_le (d := d)
      (p := ENNReal.ofReal γBarReal)
      (ENNReal.ofReal_pos.mpr hγ).ne' ENNReal.ofReal_ne_top
      sol.memSobolevPer_u sol.hDuLp
    rw [hγtoReal] at h
    exact h
  -- Combine.
  calc ‖q‖ ^ min βBarReal γBarReal
      ≤ 1 + ‖q1‖ ^ βBarReal + ‖q2‖ ^ γBarReal := hStep1
    _ = 1 + (∫ x in UnitCube d, |sol.m x| ^ βBarReal)
          + ‖q2‖ ^ γBarReal := by rw [hStep2]
    _ ≤ 1 + (∫ x in UnitCube d, |sol.m x| ^ βBarReal)
          + ((d : ℝ) + 1) ^ γBarReal *
              ((∫ x in UnitCube d, |sol.u x| ^ γBarReal) +
                ∑ i, ∫ x in UnitCube d, |sol.Du i x| ^ γBarReal) := by linarith

/-! ### Phase G strip: per-query residue bundles for the three families

Per `infra-P5-phase-G-strip-residue-fields` (iter 1): the producer's
three universally-quantified `hCont_*` operator-tendsto suppliers are
replaced by three universally-quantified residue suppliers, each
returning a bundle of per-query inputs (measurabilities + six abstract
dominator certificates with `MemLpPer` + a.e. bound) consumable by the
closed-form aggregator
`mfgOperatorEpsPair_tendsto_*_perturbation_of_paperHypotheses`. The
aggregator is then invoked inside the producer body to produce the
required `Tendsto` certificate, which is fed to
`hVIeps_*_of_KAepsi_VI` exactly as before. -/

/-- Per-query residue bundle for the **set family**. Packages the
test-triple measurabilities and the six abstract dominator certificates
(`Gh, Eh, Gf, Ef, Gm, Em` with `MemLpPer` + a.e. bounds) consumed by
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses` at a
fixed Banach-witness `q`, set `S`, and test triple `(ρ, υ, Dυ)`. -/
structure SetTendstoResidueOf
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (q : XBanach d βBarReal γBarReal)
    (S : Set (Fin d → ℝ))
    (ρ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- A.e.-strong measurability of the **indicator** `S.indicator ρ` on
  the unit cube. Iter-0713 refactor (option b of
  `paperSolFor-final-phase5-aggregator-closed-set-rho-meas-supplier`):
  relaxed from `AEStronglyMeasurable ρ` to
  `AEStronglyMeasurable (S.indicator ρ)`. The audit showed that the
  downstream consumer
  `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
  uses its `hρ` parameter exclusively through `S.indicator ρ`, so the
  indicator form suffices everywhere. This is the canonical shape
  exposed by the partial aggregator's per-query
  `residueOf_set` supplier (`MemLpPer (S.indicator ρ)`), so the closed
  producer `setTendstoResidueOf_of_paperHypotheses` can build the field
  directly via `hSρ_memLp.aestronglyMeasurable` without needing a
  separate measurability witness for raw `ρ`. -/
  hρ : AEStronglyMeasurable (S.indicator ρ)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `m`-component. -/
  hm : Measurable (mOf q)
  /-- A.e.-strong measurability of the potential `V` on the unit cube.
  Relaxed from `Measurable V` (iter post-0673,
  `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-set`) so that
  the closed supplier `setTendstoResidueOf_of_paperHypotheses` can build
  the field directly from a `MemLpPer V` certificate via
  `MemLpPer.aestronglyMeasurable`. The downstream consumer
  `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
  accepts this weaker shape and routes through a measurable representative
  internally. -/
  hV : AEStronglyMeasurable V (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- A.e.-strong measurability of the test value `υ` on the unit cube.
  Relaxed from `Measurable υ` (iter post-0689); see `hρ` docstring above. -/
  hυ : AEStronglyMeasurable υ (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `u`-component. -/
  hu : Measurable (uOf q)
  /-- A.e.-strong measurability of each test gradient component on the
  unit cube. Relaxed from `Measurable (Dυ i)` (iter post-0689); see `hρ`
  docstring above. -/
  hDυ : ∀ i, AEStronglyMeasurable (Dυ i) (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of each `q`-gradient component. -/
  hDu : ∀ i, Measurable (DuOf q i)
  /-- HJB-residual envelope (dominator). -/
  Gh : (Fin d → ℝ) → ℝ
  /-- HJB-pair test factor envelope (dominator). -/
  Eh : (Fin d → ℝ) → ℝ
  /-- `Gh` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hGh_memLp : Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh
  /-- `Eh` integrability at the Hölder-paired exponent `β+1`. -/
  hEh_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh
  /-- HJB-residual a.e. bound, uniform in `n`. -/
  hGh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖-(υ x) - H x (fun i => Dυ i x)
            (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x
  /-- HJB-pair a.e. bound, uniform in `n`. -/
  hEh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - mOf q x‖ ≤ Eh x
  /-- Flux-residual envelope (dominator). -/
  Gf : (Fin d → ℝ) → ℝ
  /-- Flux test factor envelope (dominator). -/
  Ef : (Fin d → ℝ) → ℝ
  /-- `Gf` integrability at the Hölder-paired exponent `β̄ = β+1`
  (iter 0617 flux-pair retype: was `γ̄'`, now `β̄`; the new
  `(β̄, β̄')` pairing lets `Ef` live at the natural envelope
  exponent — see `paperSolFor-supplier-flux-pairing-beta`). -/
  hGf_memLp :
    Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf
  /-- `Ef` integrability at the Hölder-paired exponent
  `β̄' = (β+1)/β` (iter 0617 flux-pair retype: was `γ̄`). -/
  hEf_memLp :
    Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef
  /-- Flux-residual a.e. bound, uniform in `n`. -/
  hGf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x
  /-- Flux-pair a.e. bound, uniform in `n`. -/
  hEf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖DpH x (fun i => Dυ i x)
            (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          ⬝ (fun i => Dυ i x - DuOf q i x)‖ ≤ Ef x
  /-- Mass-residual envelope (dominator). -/
  Gm : (Fin d → ℝ) → ℝ
  /-- Mass test factor envelope (dominator). -/
  Em : (Fin d → ℝ) → ℝ
  /-- `Gm` integrability at the Hölder-paired exponent `β+1`. -/
  hGm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm
  /-- `Em` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hEm_memLp : Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em
  /-- Mass-residual a.e. bound, uniform in `n`. -/
  hGm_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x
  /-- Mass-pair a.e. bound (n-independent). -/
  hEm_bd :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖υ x - uOf q x‖ ≤ Em x

/-- **Bare-exponent, `aeMeasH`-input residue bundle for the set family**
(D2b-1c-ii-c4). Same data as `SetTendstoResidueOf` but keyed on the bare
growth exponent `β : ℝ` (rather than `hpow.β`) so it is constructible at
`H := HdeltaK0` (where no `HypothesisPowerGrowth` bundle exists), and
carrying additionally the two H AE composites `(hHcomp_ae_n,
hHcomp_ae_lim)` at the test data `(Dυ, S.indicator ρ)`. These composites
are supplied at `HdeltaK0` by `aemeasurable_HdeltaK0_comp_of_rc0`. The
bundle is consumed by
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`. -/
structure SetTendstoResidueOfBare
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (β : ℝ)
    (q : XBanach d βBarReal γBarReal)
    (S : Set (Fin d → ℝ))
    (ρ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- A.e.-strong measurability of the indicator `S.indicator ρ`. -/
  hρ : AEStronglyMeasurable (S.indicator ρ)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `m`-component. -/
  hm : Measurable (mOf q)
  /-- A.e.-strong measurability of the potential `V`. -/
  hV : AEStronglyMeasurable V (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- A.e.-strong measurability of the test value `υ`. -/
  hυ : AEStronglyMeasurable υ (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `u`-component. -/
  hu : Measurable (uOf q)
  /-- A.e.-strong measurability of each test gradient component. -/
  hDυ : ∀ i, AEStronglyMeasurable (Dυ i) (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of each `q`-gradient component. -/
  hDu : ∀ i, Measurable (DuOf q i)
  /-- Per-`n` H AE composite at the test data. -/
  hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
    (fun x : (Fin d → ℝ) =>
      H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
    (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Boundary H AE composite at the test data. -/
  hHcomp_ae_lim : AEMeasurable
    (fun x : (Fin d → ℝ) =>
      H x (fun i => Dυ i x) (S.indicator ρ x))
    (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- HJB-residual envelope (dominator). -/
  Gh : (Fin d → ℝ) → ℝ
  /-- HJB-pair test factor envelope (dominator). -/
  Eh : (Fin d → ℝ) → ℝ
  /-- `Gh` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hGh_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh
  /-- `Eh` integrability at the Hölder-paired exponent `β+1`. -/
  hEh_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh
  /-- HJB-residual a.e. bound, uniform in `n`. -/
  hGh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖-(υ x) - H x (fun i => Dυ i x)
            (S.indicator ρ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x
  /-- HJB-pair a.e. bound, uniform in `n`. -/
  hEh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - mOf q x‖ ≤ Eh x
  /-- Flux-residual envelope (dominator). -/
  Gf : (Fin d → ℝ) → ℝ
  /-- Flux test factor envelope (dominator). -/
  Ef : (Fin d → ℝ) → ℝ
  /-- `Gf` integrability at the Hölder-paired exponent `β+1`. -/
  hGf_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf
  /-- `Ef` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hEf_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef
  /-- Flux-residual a.e. bound, uniform in `n`. -/
  hGf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖S.indicator ρ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x
  /-- Flux-pair a.e. bound, uniform in `n`. -/
  hEf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖DpH x (fun i => Dυ i x)
            (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          ⬝ (fun i => Dυ i x - DuOf q i x)‖ ≤ Ef x
  /-- Mass-residual envelope (dominator). -/
  Gm : (Fin d → ℝ) → ℝ
  /-- Mass test factor envelope (dominator). -/
  Em : (Fin d → ℝ) → ℝ
  /-- `Gm` integrability at the Hölder-paired exponent `β+1`. -/
  hGm_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm
  /-- `Em` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hEm_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em
  /-- Mass-residual a.e. bound, uniform in `n`. -/
  hGm_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖S.indicator ρ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x
  /-- Mass-pair a.e. bound (n-independent). -/
  hEm_bd :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖υ x - uOf q x‖ ≤ Em x

/-- **Bare-exponent, `aeMeasH`-input residue bundle for the signed family**
(D2b-1c-ii-c4b). Same data as `SignedTendstoResidueOf` but keyed on the
bare growth exponent `β : ℝ` (rather than `hpow.β`) so it is constructible
at `H := HdeltaK0`, and carrying additionally the two H AE composites at
the signed base `mOf q + σ·mOf q·𝟙_S`. These composites are supplied at
`HdeltaK0` by `aemeasurable_HdeltaK0_comp_of_rc0`. The bundle is consumed
by
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`. -/
structure SignedTendstoResidueOfBare
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (β : ℝ)
    (q : XBanach d βBarReal γBarReal)
    (σ : ℝ) (S : Set (Fin d → ℝ)) where
  /-- Measurability of `q`'s `m`-component. -/
  hm : Measurable (mOf q)
  /-- A.e.-strong measurability of the potential `V`. -/
  hV : AEStronglyMeasurable V (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `u`-component. -/
  hu : Measurable (uOf q)
  /-- Measurability of each `q`-gradient component. -/
  hDu : ∀ i, Measurable (DuOf q i)
  /-- `mOf q ∈ L^{β+1}_per`. -/
  hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) (mOf q)
  /-- `mOf q ≥ 0` a.e. on the cube. -/
  hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x
  /-- Per-`n` H AE composite at the signed base. -/
  hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
    (fun x : (Fin d → ℝ) =>
      H x (fun i => DuOf q i x)
        (mOf q x + σ * mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
    (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Boundary H AE composite at the signed base. -/
  hHcomp_ae_lim : AEMeasurable
    (fun x : (Fin d → ℝ) =>
      H x (fun i => DuOf q i x)
        (mOf q x + σ * mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
    (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- HJB-residual envelope (dominator). -/
  Gh : (Fin d → ℝ) → ℝ
  /-- `Gh` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hGh_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh
  /-- HJB-residual a.e. bound, uniform in `n`. -/
  hGh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖-(uOf q x) - H x (fun i => DuOf q i x)
            (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x

/-- **Bare-exponent, `aeMeasH`-input residue bundle for the transport
family** (D2b-1c-ii-c4b). Same data as `TransportTendstoResidueOf` but
keyed on the bare growth exponent `β : ℝ` (rather than `hpow.β`) so it is
constructible at `H := HdeltaK0`, and carrying additionally the two H AE
composites at the transport base `σ`. These composites are supplied at
`HdeltaK0` by `aemeasurable_HdeltaK0_comp_of_rc0`. The bundle is consumed
by
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`. -/
structure TransportTendstoResidueOfBare
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (β : ℝ)
    (q : XBanach d βBarReal γBarReal)
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- A.e.-strong measurability of the test density `σ`. -/
  hσ : AEStronglyMeasurable σ (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `m`-component. -/
  hm : Measurable (mOf q)
  /-- A.e.-strong measurability of the potential `V`. -/
  hV : AEStronglyMeasurable V (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- A.e.-strong measurability of the test value `υ`. -/
  hυ : AEStronglyMeasurable υ (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `u`-component. -/
  hu : Measurable (uOf q)
  /-- A.e.-strong measurability of each test gradient component. -/
  hφ : ∀ i, AEStronglyMeasurable (φ i) (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of each `q`-gradient component. -/
  hDu : ∀ i, Measurable (DuOf q i)
  /-- Per-`n` H AE composite at the transport base. -/
  hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
    (fun x : (Fin d → ℝ) =>
      H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
    (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Boundary H AE composite at the transport base. -/
  hHcomp_ae_lim : AEMeasurable
    (fun x : (Fin d → ℝ) =>
      H x (fun i => φ i x) (σ x))
    (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- HJB-residual envelope (dominator). -/
  Gh : (Fin d → ℝ) → ℝ
  /-- HJB-pair test factor envelope (dominator). -/
  Eh : (Fin d → ℝ) → ℝ
  /-- `Gh` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hGh_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Gh
  /-- `Eh` integrability at the Hölder-paired exponent `β+1`. -/
  hEh_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Eh
  /-- HJB-residual a.e. bound, uniform in `n`. -/
  hGh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖-(υ x) - H x (fun i => φ i x)
            (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x
  /-- HJB-pair a.e. bound, uniform in `n`. -/
  hEh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖σ x + 1 / ((n : ℝ) + 1) - mOf q x‖ ≤ Eh x
  /-- Flux-residual envelope (dominator). -/
  Gf : (Fin d → ℝ) → ℝ
  /-- Flux test factor envelope (dominator). -/
  Ef : (Fin d → ℝ) → ℝ
  /-- `Gf` integrability at the Hölder-paired exponent `β+1`. -/
  hGf_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gf
  /-- `Ef` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hEf_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Ef
  /-- Flux-residual a.e. bound, uniform in `n`. -/
  hGf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x
  /-- Flux-pair a.e. bound, uniform in `n`. -/
  hEf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖DpH x (fun i => φ i x)
            (σ x + 1 / ((n : ℝ) + 1))
          ⬝ (fun i => φ i x - DuOf q i x)‖ ≤ Ef x
  /-- Mass-residual envelope (dominator). -/
  Gm : (Fin d → ℝ) → ℝ
  /-- Mass test factor envelope (dominator). -/
  Em : (Fin d → ℝ) → ℝ
  /-- `Gm` integrability at the Hölder-paired exponent `β+1`. -/
  hGm_memLp : Periodic.MemLpPer (ENNReal.ofReal (β + 1)) Gm
  /-- `Em` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hEm_memLp : Periodic.MemLpPer (ENNReal.ofReal ((β + 1) / β)) Em
  /-- Mass-residual a.e. bound, uniform in `n`. -/
  hGm_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x
  /-- Mass-pair a.e. bound (n-independent). -/
  hEm_bd :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖υ x - uOf q x‖ ≤ Em x

/-- Per-query residue bundle for the **signed family**. Packages the
test-triple measurabilities and the single HJB-residual envelope
`(Gh, hGh_memLp, hGh_bd)` consumed by
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses` at
a fixed Banach-witness `q`, sign `σ`, and set `S`. -/
structure SignedTendstoResidueOf
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (q : XBanach d βBarReal γBarReal)
    (σ : ℝ) (S : Set (Fin d → ℝ)) where
  /-- Measurability of `q`'s `m`-component. -/
  hm : Measurable (mOf q)
  /-- A.e.-strong measurability of the potential `V` on the unit cube.
  Relaxed from `Measurable V` (iter post-0674,
  `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-signed`) so
  that the closed supplier `signedTendstoResidueOf_of_paperHypotheses`
  can build the field directly from a `MemLpPer V` certificate via
  `MemLpPer.aestronglyMeasurable`. The downstream consumer
  `mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
  accepts this weaker shape and routes through a measurable
  representative internally. -/
  hV : AEStronglyMeasurable V (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `u`-component. -/
  hu : Measurable (uOf q)
  /-- Measurability of each `q`-gradient component. -/
  hDu : ∀ i, Measurable (DuOf q i)
  /-- `mOf q ∈ L^{β+1}_per`. -/
  hm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) (mOf q)
  /-- `mOf q ≥ 0` a.e. on the cube. -/
  hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x
  /-- HJB-residual envelope (dominator). -/
  Gh : (Fin d → ℝ) → ℝ
  /-- `Gh` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hGh_memLp : Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh
  /-- HJB-residual a.e. bound, uniform in `n`. -/
  hGh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖-(uOf q x) - H x (fun i => DuOf q i x)
            (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x

/-- Per-query residue bundle for the **transport family**. Packages the
test-triple measurabilities and the six abstract dominator certificates
consumed by
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses`
at a fixed Banach-witness `q`, density `σ`, test value `υ`, and test
gradient `φ`. -/
structure TransportTendstoResidueOf
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (q : XBanach d βBarReal γBarReal)
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- A.e.-strong measurability of the test density `σ` on the unit cube.
  Relaxed from `Measurable σ` (iter post-0690,
  `paperSolFor-final-phase5-aggregator-closed-testdata-meas-bridge-transport`)
  so that the closed supplier `transportTendstoResidueOf_of_paperHypotheses`
  can build the field from an AE-strong-measurability certificate rather
  than a strict measurability witness (the partial aggregator's
  `residueOf_transport` supplies `MemLpPer σ`, which does not yield strict
  `Measurable σ`). The downstream consumer
  `mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
  accepts this weaker shape and routes through a measurable representative
  internally. -/
  hσ : AEStronglyMeasurable σ (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `m`-component. -/
  hm : Measurable (mOf q)
  /-- A.e.-strong measurability of the potential `V` on the unit cube.
  Relaxed from `Measurable V` (iter post-0676,
  `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-transport`) so
  that the closed supplier `transportTendstoResidueOf_of_paperHypotheses`
  can build the field directly from a `MemLpPer V` certificate via
  `MemLpPer.aestronglyMeasurable`. The downstream consumer
  `mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable`
  accepts this weaker shape and routes through a measurable
  representative internally. -/
  hV : AEStronglyMeasurable V (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- A.e.-strong measurability of the test value `υ` on the unit cube.
  Relaxed from `Measurable υ` (iter post-0690); see `hσ` docstring above. -/
  hυ : AEStronglyMeasurable υ (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of `q`'s `u`-component. -/
  hu : Measurable (uOf q)
  /-- A.e.-strong measurability of each test gradient component on the
  unit cube. Relaxed from `Measurable (φ i)` (iter post-0690); see `hσ`
  docstring above. -/
  hφ : ∀ i, AEStronglyMeasurable (φ i) (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Measurability of each `q`-gradient component. -/
  hDu : ∀ i, Measurable (DuOf q i)
  /-- HJB-residual envelope (dominator). -/
  Gh : (Fin d → ℝ) → ℝ
  /-- HJB-pair test factor envelope (dominator). -/
  Eh : (Fin d → ℝ) → ℝ
  /-- `Gh` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hGh_memLp : Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh
  /-- `Eh` integrability at the Hölder-paired exponent `β+1`. -/
  hEh_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Eh
  /-- HJB-residual a.e. bound, uniform in `n`. -/
  hGh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖-(υ x) - H x (fun i => φ i x)
            (σ x + 1 / ((n : ℝ) + 1)) + V x‖ ≤ Gh x
  /-- HJB-pair a.e. bound, uniform in `n`. -/
  hEh_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖σ x + 1 / ((n : ℝ) + 1) - mOf q x‖ ≤ Eh x
  /-- Flux-residual envelope (dominator). -/
  Gf : (Fin d → ℝ) → ℝ
  /-- Flux test factor envelope (dominator). -/
  Ef : (Fin d → ℝ) → ℝ
  /-- `Gf` integrability at the Hölder-paired exponent `β̄ = β+1`
  (iter 0617 flux-pair retype). -/
  hGf_memLp :
    Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gf
  /-- `Ef` integrability at the Hölder-paired exponent
  `β̄' = (β+1)/β` (iter 0617 flux-pair retype). -/
  hEf_memLp :
    Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef
  /-- Flux-residual a.e. bound, uniform in `n`. -/
  hGf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖σ x + 1 / ((n : ℝ) + 1)‖ ≤ Gf x
  /-- Flux-pair a.e. bound, uniform in `n`. -/
  hEf_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖DpH x (fun i => φ i x)
            (σ x + 1 / ((n : ℝ) + 1))
          ⬝ (fun i => φ i x - DuOf q i x)‖ ≤ Ef x
  /-- Mass-residual envelope (dominator). -/
  Gm : (Fin d → ℝ) → ℝ
  /-- Mass test factor envelope (dominator). -/
  Em : (Fin d → ℝ) → ℝ
  /-- `Gm` integrability at the Hölder-paired exponent `β+1`. -/
  hGm_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) Gm
  /-- `Em` integrability at the Hölder-paired exponent `(β+1)/β`. -/
  hEm_memLp : Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Em
  /-- Mass-residual a.e. bound, uniform in `n`. -/
  hGm_bd : ∀ n : ℕ,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖σ x + 1 / ((n : ℝ) + 1) - 1‖ ≤ Gm x
  /-- Mass-pair a.e. bound (n-independent). -/
  hEm_bd :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ‖υ x - uOf q x‖ ≤ Em x

/-! ## Per-ε existence wrapper (paper `thm:strongAepsi`)

`exists_regularized_solution_at_eps` is the paper-facing existence
theorem for a single regularised solution at one `ε > 0`. It is the
**single-ε** wrapper around `exists_regularizedBareSolution_K` (in
`AssemblyContext.lean`), with the five Minty/δ-limit inputs of the
producer constructed in closed form from per-family residues + paper
hypotheses, by the same wiring that
`regularizedSequenceData_of_paperHypotheses` uses per-`k` (lines
7170–7228 in this file).

This is paper `thm:strongAepsi` (`Source/FGU-monotone_revised.tex`
§4.1). The mathematical content is fully discharged by
`exists_regularizedBareSolution_K`; this wrapper is a pure refactor
that lifts the per-family residue inputs through the closed-form
producers `mfgOperatorEpsPair_tendsto_*_perturbation_of_paperHypotheses`
and the closure helpers `hVIeps_*_of_KAepsi_VI`. -/

/-- **Paper-facing existence at fixed `ε`** (`thm:strongAepsi`).

Given the paper-level hypotheses
`(hpow, hRegH, hHat0, hFin, hAgree, hExp)`, an `AepsiUniformContextK`
at `ε`, and the per-family residue suppliers
`(residueOf_set, residueOf_signed, residueOf_transport)` together with
the two authorised user-probe / user-triple inputs, produce a
regularised bare solution at that single `ε`.

Body: copy of the per-`k` slice of
`regularizedSequenceData_of_paperHypotheses` (lines 7170–7228),
specialised at the bound `ε` and `ctx`. -/
theorem exists_regularized_solution_at_eps
    {ε : ℝ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hε : 0 < ε)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hRegH : Hamiltonian.RegularityH H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (ctx : AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    (residueOf_set :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            SetTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q S ρ υ Dυ)
    (residueOf_signed :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            SignedTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ S)
    (residueOf_transport :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
            TransportTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ υ φ)
    -- Authorised input (CONVENTIONS §8): operator-continuity certificate
    -- at the **signed-family user-probe** perturbation. Shape mirrors
    -- the per-`k` parameter of `regularizedSequenceData_of_paperHypotheses`
    -- (lines 7083–7117), specialised at the bound `ε`.
    (hSignedUserProbeCont :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
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
                    (fun x => υ x - uOf q x))))
    -- Authorised input (CONVENTIONS §8): operator-continuity certificate
    -- at the **signed-family user-triple** strict-positive perturbation
    -- `μ_n := μ + σ · μ · 1_S + 1/(n+1)` with user-supplied primal
    -- density `μ` (replacing the iter-358 hardcoded `mOf q`). Consumed
    -- by `hVIeps_signed_user_triple_of_KAepsi_VI` to produce the
    -- regularised paper-family VI conclusion. Shape mirrors
    -- `hSignedUserProbeCont` above with the extra
    -- `(μ, hμ_nn, hμ_memLp)` triple threaded through the perturbation
    -- (`mOf q ↦ μ` substitution; `mOf q` continues to appear in the
    -- bare-difference `μ_n - mOf q`).
    (hSignedUserTripleCont :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
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
                    (fun x => υ x - uOf q x))))
    :
    -- **Phase 2a (iter 2 — `AEPeriodic`-typed; no auth parameter).**
    -- The new `RegularizedBareSolution.{hu_per, hDu_per}` fields are
    -- populated in-body by `exists_regularizedBareSolution_K` via
    -- `Periodic.bareCoeFnOfLpPer` from the underlying `XBanach` lift —
    -- no external authorisation parameter needed.
    Nonempty (RegularizedBareSolution d ε V H DpH γBarReal βBarReal
                βBarReal' γBarReal') :=
  exists_regularizedBareSolution_K (ε := ε) hε ctx
    (hMinty_set := fun q hq_K0 hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp _hWeak_υ =>
      let r := residueOf_set q hq_K0 S hS ρ υ Dυ hρ_nn
                hSρ_memLp hυ_memSob hDυ_memLp
      have hCont :=
        mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
          (ε := ε) (γBarReal := γBarReal)
          (βBarReal := βBarReal) (βBarReal' := βBarReal')
          (γBarReal' := γBarReal')
          hpow hRegH hExp hHat0 hFin hAgree
          Dυ υ (uOf q) (DuOf q) (mOf q) V S ρ
          hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
          r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
          r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
          r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
      hVIeps_set_of_KAepsi_VI ctx.auxHypsK q hVI S hS ρ υ Dυ hρ_nn
        hSρ_memLp hυ_memSob hDυ_memLp hCont)
    (hMinty_signed := fun q hq_K0 hVI σ hσ S hS hSfin =>
      let r := residueOf_signed q hq_K0 σ hσ S hS hSfin
      have hCont :=
        mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable
          (ε := ε) (γBarReal := γBarReal)
          (βBarReal := βBarReal) (βBarReal' := βBarReal')
          (γBarReal' := γBarReal')
          hpow hRegH hExp hHat0 hFin hAgree
          (DuOf q) (uOf q) (mOf q) V σ hσ S hS
          r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
          r.Gh r.hGh_memLp r.hGh_bd
      hVIeps_signed_of_KAepsi_VI ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin
        hCont)
    (hMinty_transport := fun q hq_K0 hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp _hWeak_υ =>
      let r := residueOf_transport q hq_K0 σ υ φ hσ_nn
                hσ_memLp hυ_memSob hφ_memLp
      have hCont :=
        mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable
          (ε := ε) (γBarReal := γBarReal)
          (βBarReal := βBarReal) (βBarReal' := βBarReal')
          (γBarReal' := γBarReal')
          hpow hRegH hExp hHat0 hFin hAgree
          φ υ (uOf q) (DuOf q) (mOf q) V σ
          r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
          r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
          r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
          r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
      hVIeps_transport_of_KAepsi_VI ctx.auxHypsK q hVI σ υ φ hσ_nn
        hσ_memLp hυ_memSob hφ_memLp hCont)
    (hMinty_signed_user_probe :=
      fun q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp _hWeak_υ =>
      hVIeps_signed_user_probe_of_KAepsi_VI ctx.auxHypsK q hq_K0 hVI σ hσ
        S hS hSfin υ Dυ hυ_memSob hDυ_memLp
        (hSignedUserProbeCont q hq_K0 σ hσ S hS hSfin υ Dυ
          hυ_memSob hDυ_memLp))
    (hMinty_signed_user_triple :=
      fun q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob
          hDυ_memLp _hWeak_υ =>
      hVIeps_signed_user_triple_of_KAepsi_VI ctx.auxHypsK q hq_K0 hVI σ hσ
        S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp
        (hSignedUserTripleCont q hq_K0 σ hσ S hS hSfin μ υ Dυ
          hμ_nn hμ_memLp hυ_memSob hDυ_memLp))

/-- Sanity-check `example` for `exists_regularized_solution_at_eps`. -/
example
    {ε : ℝ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hε : 0 < ε)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hRegH : Hamiltonian.RegularityH H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (ctx : AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
              βBarReal' γBarReal')
    (residueOf_set :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            SetTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q S ρ υ Dυ)
    (residueOf_signed :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            SignedTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ S)
    (residueOf_transport :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
            TransportTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ υ φ)
    (hSignedUserProbeCont :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
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
                    (fun x => υ x - uOf q x))))
    (hSignedUserTripleCont :
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
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
                    (fun x => υ x - uOf q x))))
    :
    Nonempty (RegularizedBareSolution d ε V H DpH γBarReal βBarReal
                βBarReal' γBarReal') :=
  exists_regularized_solution_at_eps hε hpow hRegH hHat0 hFin hAgree hExp ctx
    residueOf_set residueOf_signed residueOf_transport
    hSignedUserProbeCont hSignedUserTripleCont

/-- **AC3 producer.** Build a `RegularizedSequenceData` record from
the paper hypotheses, given a per-`k` `AepsiUniformContextK` supplier
and a per-`k` Banach-pair-norm certificate.

Per `infra-P5-phase-G-strip-residue-fields` (iter 1): the three
universally-quantified `hCont_*` operator-tendsto §8 suppliers of the
previous shape are replaced by three per-`k`-and-query residue
suppliers (`SetTendstoResidueOf`, `SignedTendstoResidueOf`,
`TransportTendstoResidueOf`) packaging measurabilities + the six
abstract dominator certificates needed by the closed-form
aggregators
`mfgOperatorEpsPair_tendsto_*_perturbation_of_paperHypotheses`. The
producer body invokes the aggregator at each per-`k` query to obtain
the `Tendsto` certificate, which is then fed to
`hVIeps_*_of_KAepsi_VI` to construct the Minty/δ-limit conclusions
exactly as before.

The producer's paper-hypothesis dependency is correspondingly
extended with the four `(hRegH, hHat0, hFin, hAgree)` Hamiltonian-side
hypotheses that the aggregators consume. -/
noncomputable def regularizedSequenceData_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Phase G — additional Hamiltonian-side paper hypotheses consumed by
    -- the closed-form aggregators
    -- `mfgOperatorEpsPair_tendsto_*_perturbation_of_paperHypotheses`.
    (hRegH : Hamiltonian.RegularityH H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- Per-`k` `AepsiUniformContextK` (the K_Aepsi-form context, the
    -- canonical replacement of the legacy K0-form `AepsiUniformContext`
    -- per `infra-P4-delete-AepsiUniformContext-K0-form`).
    (ctxs : ∀ k : ℕ, AepsiUniformContextK (d := d) (epsSeq k) V H DpH
                        γBarReal βBarReal βBarReal' γBarReal')
    -- Per-`k`-and-query residue supplier for the **set family**
    -- strict-positive perturbation `μ_n := S.indicator ρ + 1/(n+1)`.
    -- The bundle's measurabilities + dominator certificates are
    -- consumed by
    -- `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
    -- inside the body to produce the operator `Tendsto` certificate.
    (residueOf_set :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            SetTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q S ρ υ Dυ)
    -- Per-`k`-and-query residue supplier for the **signed family**
    -- strict-positive perturbation
    -- `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)`. Consumed by
    -- `mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`
    -- inside the body.
    (residueOf_signed :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            SignedTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ S)
    -- Per-`k`-and-query residue supplier for the **transport family**
    -- strict-positive perturbation `μ_n := σ + 1/(n+1)`. Consumed by
    -- `mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses`
    -- inside the body.
    (residueOf_transport :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
            TransportTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ υ φ)
    -- Positivity facts on the paper exponents (needed to invoke the
    -- `rpow_min` translation lemmas — `ENNReal.ofReal *` must be
    -- non-zero and the rpow exponent must be positive).
    (hβpos : 0 < βBarReal) (hγpos : 0 < γBarReal)
    -- Per-`k`-and-`sol` ε-uniform integrated apriori sum bound.
    -- Closed-form from `aprioriInputAuxHyps_of_paperHypotheses`
    -- (AC1) plus `aprioriBound_at_eps` (F.3) plus the
    -- `lpNormPer u^γ̄ = ∫ |u|^γ̄` rewrite (`MemLpPer.norm_toLp_rpow_eq`)
    -- and the `‖Du x‖^γ̄`-vs-`∑|Du i x|^γ̄` Pi-norm-vs-sum
    -- comparison. The ε-uniformity of the constant `Capr` is the
    -- paper-residue claim that the apriori constant from
    -- `apriori_at_eps` does not depend on `ε` (only on `(h.C, h.β,
    -- h.α, Vbound, Vint_bound, Vβp_bound)`, all ε-uniform).
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr :
      ∀ k : ℕ,
        ∀ (sol : RegularizedBareSolution d (epsSeq k) V H DpH
                    γBarReal βBarReal βBarReal' γBarReal'),
          (∫ x in UnitCube d, |sol.m x| ^ βBarReal) +
            (∫ x in UnitCube d, |sol.u x| ^ γBarReal) +
            (∑ i, ∫ x in UnitCube d, |sol.Du i x| ^ γBarReal) ≤ Capr)
    -- Authorised input (CONVENTIONS §8): operator-continuity certificate
    -- at the **signed-family user-probe** perturbation
    -- `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)`, supplied per
    -- `(k, q, σ, S, υ, Dυ)`. Consumed by
    -- `hVIeps_signed_user_probe_of_KAepsi_VI`. Filed as a follow-up
    -- closure task — its derivation parallels
    -- `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
    -- with `S.indicator ρ` replaced by `mOf q + σ · mOf q · 1_S`.
    (hSignedUserProbeCont :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal (epsSeq k)
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
                    γBarReal (epsSeq k)
                    Dυ
                    (fun x => mOf q x + σ * mOf q x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x - DuOf q i x)
                    (fun x => σ * mOf q x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    (fun x => υ x - uOf q x))))
    -- Authorised input (CONVENTIONS §8): operator-continuity certificate
    -- at the **signed-family user-triple** strict-positive perturbation
    -- `μ_n := μ + σ · μ · 1_S + 1/(n+1)`, supplied per
    -- `(k, q, σ, S, μ, υ, Dυ)` with the user-density nonneg + Lp
    -- certs. Mirror of `hSignedUserProbeCont` above, but with
    -- user-supplied primal density `μ` (replacing the iter-358
    -- hardcoded `mOf q`). The strict-positive perturbation is positive
    -- a.e. since `μ ≥ 0` (user cert) and `1 + σ · 1_S ∈ [0, 2]`
    -- pointwise (`σ ∈ {±1}`, `0 ≤ 1_S ≤ 1`). Consumed by
    -- `hVIeps_signed_user_triple_of_KAepsi_VI` to produce the regularised
    -- paper-family VI conclusion.
    (hSignedUserTripleCont :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal (epsSeq k)
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
                    γBarReal (epsSeq k)
                    Dυ
                    (fun x => μ x + σ * μ x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x - DuOf q i x)
                    (fun x => (μ x + σ * μ x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                                - mOf q x)
                    (fun x => υ x - uOf q x))))
    :
    -- **Phase 2a (iter 2 — `AEPeriodic`-typed; no auth parameter).**
    -- The new `RegularizedBareSolution.{hu_per, hDu_per}` fields on
    -- each per-`k` solution are populated in-body via
    -- `Periodic.bareCoeFnOfLpPer`.
    RegularizedSequenceData (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH := by
  -- Per-`k` `RegularizedBareSolution` from T4 (K_Aepsi-form
  -- producer). The three Minty/δ-limit conclusions are constructed
  -- in closed form via `hVIeps_*_of_KAepsi_VI` (children C/D of the
  -- two-domain redesign). The required operator-`Tendsto`
  -- certificates are produced in-body by the closed-form aggregators
  -- `mfgOperatorEpsPair_tendsto_*_perturbation_of_paperHypotheses`,
  -- consuming the per-`k`-and-query residue bundles
  -- `residueOf_{set,signed,transport}` (Phase G strip).
  let sol : ∀ k, RegularizedBareSolution d (epsSeq k) V H DpH
                    γBarReal βBarReal βBarReal' γBarReal' := fun k =>
    Classical.choice (exists_regularizedBareSolution_K
        (ε := epsSeq k) (epsSeq_pos k) (ctxs k)
        (hMinty_set := fun q hq_K0 hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp _hWeak_υ =>
          let r := residueOf_set k q hq_K0 S hS ρ υ Dυ hρ_nn
                    hSρ_memLp hυ_memSob hDυ_memLp
          have hCont :=
            mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
              (ε := epsSeq k) (γBarReal := γBarReal)
              (βBarReal := βBarReal) (βBarReal' := βBarReal')
              (γBarReal' := γBarReal')
              hpow hRegH hExp hHat0 hFin hAgree
              Dυ υ (uOf q) (DuOf q) (mOf q) V S ρ
              hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
              r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
              r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
              r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
          hVIeps_set_of_KAepsi_VI (ctxs k).auxHypsK q hVI S hS ρ υ Dυ hρ_nn
            hSρ_memLp hυ_memSob hDυ_memLp hCont)
        (hMinty_signed := fun q hq_K0 hVI σ hσ S hS hSfin =>
          let r := residueOf_signed k q hq_K0 σ hσ S hS hSfin
          have hCont :=
            mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable
              (ε := epsSeq k) (γBarReal := γBarReal)
              (βBarReal := βBarReal) (βBarReal' := βBarReal')
              (γBarReal' := γBarReal')
              hpow hRegH hExp hHat0 hFin hAgree
              (DuOf q) (uOf q) (mOf q) V σ hσ S hS
              r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
              r.Gh r.hGh_memLp r.hGh_bd
          hVIeps_signed_of_KAepsi_VI (ctxs k).auxHypsK q hq_K0 hVI σ hσ S hS hSfin
            hCont)
        (hMinty_transport := fun q hq_K0 hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp _hWeak_υ =>
          let r := residueOf_transport k q hq_K0 σ υ φ hσ_nn
                    hσ_memLp hυ_memSob hφ_memLp
          have hCont :=
            mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable
              (ε := epsSeq k) (γBarReal := γBarReal)
              (βBarReal := βBarReal) (βBarReal' := βBarReal')
              (γBarReal' := γBarReal')
              hpow hRegH hExp hHat0 hFin hAgree
              φ υ (uOf q) (DuOf q) (mOf q) V σ
              r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
              r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
              r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
              r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
          hVIeps_transport_of_KAepsi_VI (ctxs k).auxHypsK q hVI σ υ φ hσ_nn
            hσ_memLp hυ_memSob hφ_memLp hCont)
        (hMinty_signed_user_probe :=
          fun q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp _hWeak_υ =>
          hVIeps_signed_user_probe_of_KAepsi_VI (ctxs k).auxHypsK q hq_K0 hVI σ hσ
            S hS hSfin υ Dυ hυ_memSob hDυ_memLp
            (hSignedUserProbeCont k q hq_K0 σ hσ S hS hSfin υ Dυ
              hυ_memSob hDυ_memLp))
        (hMinty_signed_user_triple :=
          fun q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob
              hDυ_memLp _hWeak_υ =>
          hVIeps_signed_user_triple_of_KAepsi_VI (ctxs k).auxHypsK q hq_K0 hVI σ hσ
            S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp
            (hSignedUserTripleCont k q hq_K0 σ hσ S hS hSfin μ υ Dυ
              hμ_nn hμ_memLp hυ_memSob hDυ_memLp)))
  -- Closed-form derivation of the uniform Banach-pair-norm bound.
  -- Set the uniform `min βBar γBar`-power upper bound `M` derived
  -- from `Capr`, then take the `1/min`-th power to obtain the
  -- norm-level bound `Cnorm`.
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
  -- The desired uniform bound on `‖(sol k).toBanachPair‖`.
  have hbound : ∀ k, ‖(sol k).toBanachPair‖ ≤ Cnorm := by
    intro k
    -- Step A: rpow_min translation at `sol k`.
    have hRpow := RegularizedBareSolution.norm_toBanachPair_rpow_min_le_apriori_sum
      (d := d) (ε := epsSeq k) (V := V) (H := H) (DpH := DpH)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hβpos hγpos (sol k)
    -- Step B: hCapr provides the integrated bound. Since each summand
    -- is non-negative (m ≥ 0 a.e. drops |·|; |u|^γ̄ and |Du i|^γ̄ are
    -- pointwise non-negative; their integrals over the cube are
    -- non-negative), each individual integral is ≤ Capr.
    set Im : ℝ := ∫ x in UnitCube d, |(sol k).m x| ^ βBarReal with hIm
    set Iu : ℝ := ∫ x in UnitCube d, |(sol k).u x| ^ γBarReal with hIu
    set IDu : ℝ := ∑ i, ∫ x in UnitCube d, |(sol k).Du i x| ^ γBarReal with hIDu
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
    have hSum_le : Im + Iu + IDu ≤ Capr := hCapr k (sol k)
    -- Each individual is ≤ Capr.
    have hIm_le : Im ≤ Capr := by linarith
    have hIu_plus_IDu_le : Iu + IDu ≤ Capr := by linarith
    -- Step C: combine to get `‖q‖^min ≤ M`.
    have hRpow' :
        ‖(sol k).toBanachPair‖ ^ m_exp ≤ M := by
      have h1 :
          ‖(sol k).toBanachPair‖ ^ min βBarReal γBarReal
            ≤ 1 + Im + d1γ * (Iu + IDu) := hRpow
      have h2 : 1 + Im + d1γ * (Iu + IDu) ≤ M := by
        have hIm_le' : Im ≤ Capr := hIm_le
        have hSum_le' : Iu + IDu ≤ Capr := hIu_plus_IDu_le
        have hmul_le : d1γ * (Iu + IDu) ≤ d1γ * Capr :=
          mul_le_mul_of_nonneg_left hSum_le' hd1γ_nn
        calc 1 + Im + d1γ * (Iu + IDu)
            ≤ 1 + Capr + d1γ * Capr := by linarith
          _ = M := by simp [hM]
      simpa [hm_exp] using h1.trans h2
    -- Step D: take rpow `(1/m_exp)` to deduce `‖q‖ ≤ Cnorm`.
    have hq_nn : 0 ≤ ‖(sol k).toBanachPair‖ := norm_nonneg _
    have hqM_nn : 0 ≤ ‖(sol k).toBanachPair‖ ^ m_exp :=
      Real.rpow_nonneg hq_nn _
    have hinv_nn : 0 ≤ 1 / m_exp := by
      apply div_nonneg
      · exact zero_le_one
      · exact hm_exp_pos.le
    -- `(‖q‖^m_exp)^(1/m_exp) ≤ M^(1/m_exp)`.
    have hRpowMono :
        (‖(sol k).toBanachPair‖ ^ m_exp) ^ (1 / m_exp)
          ≤ M ^ (1 / m_exp) :=
      Real.rpow_le_rpow hqM_nn hRpow' hinv_nn
    -- `(‖q‖^m_exp)^(1/m_exp) = ‖q‖^(m_exp · (1/m_exp)) = ‖q‖^1 = ‖q‖`.
    have hpow_collapse :
        (‖(sol k).toBanachPair‖ ^ m_exp) ^ (1 / m_exp)
          = ‖(sol k).toBanachPair‖ := by
      rw [← Real.rpow_mul hq_nn]
      have : m_exp * (1 / m_exp) = 1 := by
        field_simp
      rw [this, Real.rpow_one]
    rw [hpow_collapse] at hRpowMono
    exact hRpowMono
  refine
    { epsSeq := epsSeq
      heps_pos := epsSeq_pos
      heps_tendsto := epsSeq_tendsto_zero
      sol := sol
      uniformBound := ⟨Cnorm, hbound⟩ }

/-! ## T8 — Weak-limit producer

Replace F.5's `extractWeakLimit` (which consumes a 7-field
`WeakLimitInputData`) by a producer that **constructs** the weak-limit
input data directly from a `RegularizedSequenceData`.

### What is derived internally

Given a `RegularizedSequenceData`, we can read off:

* the bounded sequence `v_n k := (sol k).toBanachPair`,
* its norm bound (from `seq.uniformBound`),
* the per-`k` non-negativity of the `m`-component representative
  `⇑((sol k).hmLp.toLp)` (from `(sol k).hmNonneg` plus
  `MemLp.coeFn_toLp`).

### Path-B refactor (`infra-P4-rebuild-T8-discharge-aux-weakLimit-selector`)

The previous shape took a single cluster-point-dependent parameter
`hAux : ∀ w, …` packaging a triple `(hWeak, hPerM, hPerU)`. This task
**eliminates that parameter**: the new producer signature drops
`hAux` entirely and instead consumes the narrower sequence-side bare
data (`seqRepU`, `seqRepDu`, …), test-function `Tendsto` hypotheses,
and a chosen periodic limit `(mLim, uLim, DuLim)` plus an a.e.-equality
witness to the cluster point's `Lp.coeFn`. The weak-derivative
limit-passage that was previously demanded universally over `w` is now
**genuinely discharged closed-form** inside `extractWeakLimit` via the
parent task's `Periodic.HasWeakDerivPer.of_weak_limit`.

The reflexivity and strong-dual-separability of the Banach pair are also
parameterised (the producer is generic in real exponents `βBarReal`,
`γBarReal`; the `Fact (1 < ENNReal.ofReal …)` exponent strictness data
needed to call `lpSobolev_product_isReflexive` is best supplied by the
calling site once the concrete exponents are pinned).
-/

/-- **T8 producer — weak-limit input data from a regularized sequence.**

Build a `WeakLimitInputData (d := d) (ENNReal.ofReal βBarReal)
(ENNReal.ofReal γBarReal)` consumable by F.5's `extractWeakLimit`,
sourcing the sequence-side data (`v_n`, `hBound`, `hMpos`) from a
`RegularizedSequenceData`.

The cluster-point-dependent `hAux` parameter of the previous shape has
been **eliminated**; the new parameter list takes the strictly narrower
Path-B inputs (sequence-side bare reps, chosen periodic limit,
test-function `Tendsto` hypotheses, and the residual selector-only
a.e.-equalities). -/
noncomputable def weakLimitData_of_regularizedSequence
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    -- Reflexivity of the Banach pair (parameterised; per AC amendment).
    (hRefl : Periodic.IsReflexiveNormedSpace
              (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
    -- Separability of the strong dual (parameterised; per AC amendment).
    (hSep : TopologicalSpace.SeparableSpace
              (StrongDual ℝ
                (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                  × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)))
    -- Chosen periodic bare-function limit (Path B).
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hMlimPer : Periodic.IsPeriodic mLim)
    (hUlimPer : Periodic.IsPeriodic uLim)
    (hDuLim_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim i))
    -- Sequence-side periodic representatives + per-`n` weak-derivative
    -- relation (Path B).
    (seqRepU : ℕ → (Fin d → ℝ) → ℝ)
    (seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ)
    (hSeqRepWeak : ∀ n i,
      Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i))
    -- Test-function `Tendsto` hypotheses (Path B). The cluster-point
    -- subsequence `φ` is selected internally by `extractWeakLimit`.
    (hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepU (φ k) x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepDu (φ k) i x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x))))
    -- Residual selector-only obstruction (Path A): a.e.-equality
    -- between the chosen bare-function limit and the cluster point's
    -- `Lp.coeFn` representative.
    (auxAeOfClusterPoint :
      ∀ (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
              × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d),
        mLim
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
        ∧ uLim
            =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
        ∧ ∀ i, DuLim i
            =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    WeakLimitInputData (d := d) (ENNReal.ofReal βBarReal)
      (ENNReal.ofReal γBarReal) where
  v_n := fun k => (seq.sol k).toBanachPair
  hBound := by
    -- Boundedness of `Set.range v_n` from the uniform norm bound.
    obtain ⟨C, hC⟩ := seq.uniformBound
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    intro v hv
    rcases hv with ⟨k, rfl⟩
    exact hC k
  hMpos := by
    -- For each `k`, `⇑(v_n k).1 = ⇑((sol k).hmLp.toLp) =ᵐ (sol k).m`,
    -- and `(sol k).m ≥ 0` a.e. by `(sol k).hmNonneg`.
    intro k
    have hcoe :
        (⇑((seq.sol k).toBanachPair.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
            (seq.sol k).m := by
      -- `(seq.sol k).toBanachPair.1 = (seq.sol k).hmLp.toLp`.
      change ((MeasureTheory.MemLp.toLp (seq.sol k).m
                  (seq.sol k).hmLp : MeasureTheory.Lp ℝ
                    (ENNReal.ofReal βBarReal)
                    (MeasureTheory.Measure.restrict MeasureTheory.volume
                      (UnitCube d))) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (seq.sol k).m
      exact MeasureTheory.MemLp.coeFn_toLp (seq.sol k).hmLp
    filter_upwards [hcoe, (seq.sol k).hmNonneg] with x hx hxnn
    -- `⇑(v_n k).1 x = (seq.sol k).m x ≥ 0`.
    rw [hx]
    exact hxnn
  hRefl := hRefl
  hSep := hSep
  mLim := mLim
  uLim := uLim
  DuLim := DuLim
  hMlimPer := hMlimPer
  hUlimPer := hUlimPer
  hDuLim_memLp := hDuLim_memLp
  seqRepU := seqRepU
  seqRepDu := seqRepDu
  hSeqRepWeak := hSeqRepWeak
  hConvU := hConvU
  hConvDu := hConvDu
  auxAeOfClusterPoint := auxAeOfClusterPoint

/-! ## Sanity-check unit `example`s -/

/-- AC2: `aprioriInputs_of_regularizedBareSolution` produces an
`AprioriDischargeInputs`. Pin the type-shape. -/
example
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
    AprioriDischargeInputs (d := d) h V ε hε :=
  aprioriInputs_of_regularizedBareSolution hε h sol aux

/-- AC3: `regularizedSequenceData_of_paperHypotheses` produces a
`RegularizedSequenceData`. Pin the type-shape. Per
`infra-P5-phase-G-strip-residue-fields` (iter 1), the three former
`hCont_*` operator-tendsto §8 suppliers are replaced by three
per-`k`-and-query residue suppliers (`SetTendstoResidueOf`,
`SignedTendstoResidueOf`, `TransportTendstoResidueOf`); the producer
body invokes the closed-form aggregators
`mfgOperatorEpsPair_tendsto_*_perturbation_of_paperHypotheses`
internally, then feeds the resulting `Tendsto` certificates to
`hVIeps_*_of_KAepsi_VI` to construct the Minty/δ-limit conclusions. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hRegH : Hamiltonian.RegularityH H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (ctxs : ∀ k : ℕ, AepsiUniformContextK (d := d) (epsSeq k) V H DpH
                        γBarReal βBarReal βBarReal' γBarReal')
    (residueOf_set :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            SetTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q S ρ υ Dυ)
    (residueOf_signed :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
            SignedTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ S)
    (residueOf_transport :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
            TransportTendstoResidueOf (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              hpow q σ υ φ)
    (hβpos : 0 < βBarReal) (hγpos : 0 < γBarReal)
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr :
      ∀ k : ℕ,
        ∀ (sol : RegularizedBareSolution d (epsSeq k) V H DpH
                    γBarReal βBarReal βBarReal' γBarReal'),
          (∫ x in UnitCube d, |sol.m x| ^ βBarReal) +
            (∫ x in UnitCube d, |sol.u x| ^ γBarReal) +
            (∑ i, ∫ x in UnitCube d, |sol.Du i x| ^ γBarReal) ≤ Capr)
    (hSignedUserProbeCont :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal (epsSeq k)
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
                    γBarReal (epsSeq k)
                    Dυ
                    (fun x => mOf q x + σ * mOf q x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x - DuOf q i x)
                    (fun x => σ * mOf q x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    (fun x => υ x - uOf q x))))
    (hSignedUserTripleCont :
      ∀ k : ℕ,
      ∀ (q : XBanach d βBarReal γBarReal),
        q ∈ K0_Aepsi d βBarReal γBarReal →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x) →
          MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ →
          MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
          (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal (epsSeq k)
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
                    γBarReal (epsSeq k)
                    Dυ
                    (fun x => μ x + σ * μ x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x - DuOf q i x)
                    (fun x => (μ x + σ * μ x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                                - mOf q x)
                    (fun x => υ x - uOf q x))))
    :
    RegularizedSequenceData (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V H DpH :=
  regularizedSequenceData_of_paperHypotheses
    hmon hpow hV hExp hRegH hHat0 hFin hAgree ctxs
    residueOf_set residueOf_signed residueOf_transport
    hβpos hγpos Capr hCapr_nn hCapr hSignedUserProbeCont
    hSignedUserTripleCont

/-- **T8 sanity check.** `weakLimitData_of_regularizedSequence` produces
a `WeakLimitInputData`. Pin the type-shape and exercise the producer
**without** the legacy `hAux` argument (eliminated by Path B). -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (hRefl : Periodic.IsReflexiveNormedSpace
              (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
    (hSep : TopologicalSpace.SeparableSpace
              (StrongDual ℝ
                (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                  × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)))
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hMlimPer : Periodic.IsPeriodic mLim)
    (hUlimPer : Periodic.IsPeriodic uLim)
    (hDuLim_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim i))
    (seqRepU : ℕ → (Fin d → ℝ) → ℝ)
    (seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ)
    (hSeqRepWeak : ∀ n i,
      Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i))
    (hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepU (φ k) x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepDu (φ k) i x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (auxAeOfClusterPoint :
      ∀ (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
              × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d),
        mLim
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
        ∧ uLim
            =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
        ∧ ∀ i, DuLim i
            =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    WeakLimitInputData (d := d) (ENNReal.ofReal βBarReal)
      (ENNReal.ofReal γBarReal) :=
  weakLimitData_of_regularizedSequence seq hRefl hSep
    mLim uLim DuLim hMlimPer hUlimPer hDuLim_memLp
    seqRepU seqRepDu hSeqRepWeak hConvU hConvDu auxAeOfClusterPoint

/-! ## T9 — Limit-passage producer (`LimitSolutionData`)

This block discharges Phase-4 task `infra-P4-rebuild-T9-limitPassage`.

### What T9 builds

`LimitSolutionData` packages the substantive output of the limit
passage block: bare-function periodic data `(m, u, Du)` together with
* `MemLpPer`/`MemSobolevPer` regularity,
* a.e. non-negativity `0 ≤ m`,
* the **function-form strong VI** of `A_0` at `(m, u, Du)`:
  `0 ≤ mfgOperatorPair Du m u (Dυ - Du) (μ - m) (υ - u)` for every
  test triple `(μ, υ, Dυ)`,
* the integrability bundle `H4SimplePowerThinInputs` consumes
  (HJB residual integrability, residual·m integrability, flux
  integrability).

### Producer & AC amendment (per CONVENTIONS §8)

The original AC's "single-input" producer
```
limitSolutionData_of_regularizedSequence
  (hmon …) (hpow …) (hV …) (hExp …) (seq : RegularizedSequenceData …)
```
cannot be discharged closed-form: building `WeakLimitInputData`,
`LimitPassageInputData`, and `main_strong_VI`'s prerequisites
(domain `D`, hemicontinuity, segment closure) from `(hmon, hpow, hV,
hExp, seq)` alone is the genuine multi-week upstream work documented
in the F.7 blocker analysis (`docs/TASKS/backlog/
infra-P4-discharge-F7-final-bundle.md`).

T9 therefore lands the structure plus a producer that explicitly
authorises three auxiliary input bundles:

* `WeakLimitInputBundle` — the missing T8 inputs (Banach
  reflexivity & dual separability of the pair, periodic limit triple,
  sequence-side periodic representatives, test-function `Tendsto`
  hypotheses, cluster-point selector residue).
* `LimitPairingInputs` — per test triple `(μ, υ, Dυ)`, the
  `LimitPassageInputData` test-triple-dependent fields plus the
  assembled convergence `hpair_conv` of the un-regularised pairing
  along the F.5 sequence. Routed through F.6's
  `limitPassage_to_weakVI` to produce the **weak** VI per test triple.
* `MintyClosure` — the domain `D ⊂ MFGTriple d` containing the limit
  triple, segment closure, and hemicontinuity of `A_0` on `D`. Routed
  through `main_strong_VI` to upgrade weak VI to strong VI.

The amendment narrows the gap: each bundle is filed as a follow-up
task with concrete acceptance criteria, named
`infra-P4-rebuild-T9-discharge-{weak-limit-bundle,pairing-inputs,minty-closure}`.

### Final integrability

The strong-VI structure also carries the three integrability fields
`H4SimplePowerThinInputs` consumes (`hRes`, `hResM`, `hFluxInt`),
analogous to F.7's "final integrability bundle". These are also
authorised parameters in this rebuild because they depend on the
limit triple's bare-function values, not on `seq` directly. -/

/-! ### `WeakLimitInputBundle` — authorized aux for the T8 step. -/

/-- **Authorized auxiliary bundle** for T9's limit-passage producer.
Packages the inputs of `weakLimitData_of_regularizedSequence` that
are not derivable from `RegularizedSequenceData` alone. The
follow-up task `infra-P4-rebuild-T9-discharge-weak-limit-bundle`
closes this bundle from `(hExp, seq)` via Banach reflexivity +
periodic-representative selector. -/
structure WeakLimitInputBundle
    (γBarReal βBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] where
  /-- Reflexivity of the Banach pair. -/
  hRefl : Periodic.IsReflexiveNormedSpace
            (Periodic.LpPer (ENNReal.ofReal βBarReal) d
              × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
  /-- Separability of the strong dual. -/
  hSep : TopologicalSpace.SeparableSpace
            (StrongDual ℝ
              (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
  /-- Chosen periodic bare-function limit. -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function value-limit. -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function gradient-limit. -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- Periodicity of `mLim`. -/
  hMlimPer : Periodic.IsPeriodic mLim
  /-- Periodicity of `uLim`. -/
  hUlimPer : Periodic.IsPeriodic uLim
  /-- `MemLpPer 1` of every gradient-limit component. -/
  hDuLim_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim i)
  /-- Periodicity of every gradient-limit component.

  Phase 6a (infra-P5-theorem1-phase-6a-wkBundle-perTestTripleBase):
  added so the per-test-triple regularity record can be derived
  *structurally* from a `WeakLimitInputBundle`. The `MemSobolevPer`
  predicate carries no periodicity information, and `IsPeriodic` is
  pointwise (cannot be derived from a.e.-equality alone). At the
  selector layer this comes from `AEPeriodicRep.periodic`. -/
  hDuLim_periodic : ∀ i, Periodic.IsPeriodic (DuLim i)
  /-- Sequence-side periodic representative of the `u`-component. -/
  seqRepU : ℕ → (Fin d → ℝ) → ℝ
  /-- Sequence-side periodic representative of the gradient family. -/
  seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Per-`n`, per-`i` weak-derivative relation. -/
  hSeqRepWeak : ∀ n i,
    Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i)
  /-- Test-function `Tendsto` for `seqRepU`. -/
  hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepU (φ k) x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Test-function `Tendsto` for `seqRepDu`. -/
  hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepDu (φ k) i x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Cluster-point selector residue. -/
  auxAeOfClusterPoint : ∀
    (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d),
      mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
      ∧ uLim
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
      ∧ ∀ i, DuLim i
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
  /-- `mLim ∈ L^{βBar}_per`. (Derivable from F.5 extraction; carried
  here to avoid Σ-destructuring of the `extractWeakLimit` result.) -/
  hmLim_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) mLim
  /-- `uLim ∈ W^{1,γBar}_per`. -/
  huLim_sob : Periodic.MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim
  /-- `0 ≤ mLim` a.e. on the unit cube. -/
  hmLim_nonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] mLim

/-- **Derived strict-`γ̄` `MemLpPer` for `wkBundle.DuLim i`.**

The cluster-point a.e.-equality field `auxAeOfClusterPoint` of
`WeakLimitInputBundle` provides, for any element `w` of the Banach pair
`LpPer βBar d × SobolevPerLp 1 γBar d`, an a.e.-equality
`DuLim i =ᵐ ⇑(w.2.2 i)` on the unit cube. Since `w.2.2 i : Lp ℝ γBar μ`
is automatically `MemLp` at the cube measure (`Lp.memLp`), and `MemLp`
is stable under a.e.-equality (`MemLp.ae_eq`), the bundle lets us
derive the strict-`γ̄` `MemLpPer` of every coordinate of `DuLim`
*structurally* — no Path-A residue field needed.

This lemma supersedes the legacy `hDuLim_memLp_γ` field in both
`FinalIntegrabilityPaperResidueLp` and
`LimitPairingSelectorPaperResidue` (per
`infra-P5-theorem1-phase-H5b-drop-hDuLim-memLp-from-finIntResidue`). -/
theorem WeakLimitInputBundle.hDuLim_memLp_γ
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal γBarReal) (wkBundle.DuLim i) := by
  -- Pick the zero element of the (inhabited) Banach pair. Any `w`
  -- works; we only need the third conjunct of `auxAeOfClusterPoint w`.
  let w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d := 0
  obtain ⟨_, _, hDu_ae⟩ := wkBundle.auxAeOfClusterPoint w
  -- `Lp.memLp` gives `MemLp ⇑(w.2.2 i) γBar (volume.restrict (UnitCube d))`.
  have hmemLp :
      MeasureTheory.MemLp (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
        (ENNReal.ofReal γBarReal)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.Lp.memLp (w.2.2 i)
  -- Transfer across the a.e.-equality `DuLim i =ᵐ ⇑(w.2.2 i)`. The
  -- predicate `Periodic.MemLpPer p f` is equivalent to
  -- `MemLp f p (volume.restrict (UnitCube d))` (cf. `memLpPer_iff_memLp`).
  exact MemLp.toMemLpPer (hmemLp.ae_eq (hDu_ae i).symm)

/-- **Sanity check (Phase H5b).** The derived strict-`γ̄` `MemLpPer`
on `wkBundle.DuLim i` is well-typed and can be projected directly
from any `WeakLimitInputBundle`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal γBarReal) (wkBundle.DuLim i) :=
  wkBundle.hDuLim_memLp_γ i

/-- **Phase 6a — `(uLim, DuLim i)` weak-derivative tie.**

The `MemSobolevPer` field `huLim_sob.2` of `WeakLimitInputBundle`
existentially quantifies the gradient witness, so it does not directly
identify `DuLim` with the weak derivative of `uLim`. We tie the two
together via the sequence-side data
`(seqRepU, seqRepDu, hSeqRepWeak, hConvU, hConvDu, hDuLim_memLp)` and
`Periodic.HasWeakDerivPer.of_weak_limit` (specialised to the identity
subsequence). -/
theorem WeakLimitInputBundle.huLim_DuLim_weakDeriv
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.HasWeakDerivPer (d := d) i wkBundle.uLim (wkBundle.DuLim i) := by
  refine Periodic.HasWeakDerivPer.of_weak_limit
    (i := i) (u_n := wkBundle.seqRepU)
    (Du_n := fun n => wkBundle.seqRepDu n i)
    (u := wkBundle.uLim) (Du := wkBundle.DuLim i)
    (wkBundle.hDuLim_memLp i) (fun n => wkBundle.hSeqRepWeak n i)
    ?_ ?_
  · intro ψ
    have h := wkBundle.hConvU id strictMono_id ψ
    simpa using h
  · intro ψ
    have h := wkBundle.hConvDu id strictMono_id i ψ
    simpa using h

/-- **Phase 6a — sanity check.** The derived weak-derivative tie can be
projected from any `WeakLimitInputBundle`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.HasWeakDerivPer (d := d) i wkBundle.uLim (wkBundle.DuLim i) :=
  wkBundle.huLim_DuLim_weakDeriv i

/-- **Phase H5c — derived a.e.-strong measurability of the flux
vector field.**

For any `WeakLimitInputBundle` and any power-growth bundle
`hpow : HypothesisPowerGrowth H DpH`, the `Fin d → ℝ`-valued map
`x ↦ mLim x • DpH x (fun i => DuLim i x) (mLim x) = mDpH DpH x (Du x) (m x)`
is a.e.-strongly measurable on the unit cube.

This is paper-derivable from `(a:regularityH)` (joint measurability of
`DpH` carried by `RegularityH`, which `HypothesisPowerGrowth` extends)
plus the `MemLpPer` certificates in the bundle (which give a.e.-strong
measurability of `DuLim i` and `mLim`). It supersedes the legacy
`hFlux_meas` field of `FinalIntegrabilityPaperResidueLp` (per
`infra-P5-theorem1-phase-H5c-drop-hFlux-meas-from-finIntResidue`). -/
theorem WeakLimitInputBundle.hFlux_meas
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : (Fin d → ℝ) =>
        Hamiltonian.mDpH DpH x
          (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  -- Coordinate-wise a.e.-measurability of `DuLim` from its `MemLpPer 1`.
  have hDu_aem : ∀ i,
      AEMeasurable (fun x : (Fin d → ℝ) => wkBundle.DuLim i x)
        (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (wkBundle.hDuLim_memLp i).aestronglyMeasurable.aemeasurable
  -- A.e.-measurability of the pi-valued map `x ↦ (fun i => DuLim i x)`.
  have hDu_pi_aem :
      AEMeasurable (fun x : (Fin d → ℝ) => (fun i : Fin d => wkBundle.DuLim i x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr hDu_aem
  -- A.e.-measurability of `mLim` from its `MemLpPer βBar`.
  have hm_aem : AEMeasurable wkBundle.mLim
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    wkBundle.hmLim_memLp.aestronglyMeasurable.aemeasurable
  -- A.e.-measurability of the tuple `(x, fun i => DuLim i x, mLim x)`.
  have hxpm : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => wkBundle.DuLim i x), wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_id.prodMk (hDu_pi_aem.prodMk hm_aem)
  -- Compose with `hpow.measurable_DpH` to obtain a.e.-measurability of
  -- the `Fin d → ℝ`-valued composition.
  have hDpH_aem : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hpow.measurable_DpH.comp_aemeasurable hxpm
  -- Cast a.e.-measurability to a.e.-strong measurability (the codomain
  -- `Fin d → ℝ` is second-countable metrizable).
  have hDpH_asm :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    hDpH_aem.aestronglyMeasurable
  -- A.e.-strong measurability of `mLim` and the flux is a scalar smul.
  have hm_asm : MeasureTheory.AEStronglyMeasurable wkBundle.mLim
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    wkBundle.hmLim_memLp.aestronglyMeasurable
  -- `mDpH DpH x p m = m • DpH x p m` (definitionally).
  -- Conclude via `AEStronglyMeasurable.smul`.
  exact hm_asm.smul hDpH_asm

/-- **Sanity check (Phase H5c).** The derived a.e.-strong measurability
of the flux vector is well-typed and projectible from the bundle
together with `HypothesisPowerGrowth`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : (Fin d → ℝ) =>
        Hamiltonian.mDpH DpH x
          (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  WeakLimitInputBundle.hFlux_meas (d := d) hpow wkBundle

/-- **Phase H5d — derived `MemLpPer βBar'` of the HJB residual at the
weak limit triple.**

Given:
* `hpow : HypothesisPowerGrowth H DpH` (paper assumption `(onH.powergrowth)`),
* `hHat0`, `hFin`, `hAgree` (paper `(a:Hat0)` plus the two finiteness /
  agreement riders that bridge `Hext` to the raw `H` value at `m = 0`,
  cf. `Hamiltonian.H_rc0_of_hHat0`),
* `hV : MemLpPer βBar' V`,
* `hβBarPaper : βBarReal = hpow.β + 1`,
* `hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β`,
* a `WeakLimitInputBundle (d := d) γBarReal βBarReal`,

the HJB residual `−uLim − H(·, DuLim, mLim) + V` lies in
`L^{β̄'}_per` at the paper exponent `β̄' = (β + 1) / β`.

The proof reduces to `Hamiltonian.g_memLp_betaBar'_nonneg`
(`Estimates.lean`), which discharges the boundary `m = 0` case via
`H_rc0_of_hHat0` and the `m → 0⁺` limit-of-inequality on the upper /
lower bounds of `H`. The bundle inputs:
* `hμ_nn := wkBundle.hmLim_nonneg`,
* `hμ` from `wkBundle.hmLim_memLp` (rewritten via `hβBarPaper`),
* `hυ` from `wkBundle.huLim_sob.1` (whence `MemLpPer γBar uLim`),
  rewritten to the `hpow.α*(hpow.β+1)/hpow.β` shape via `hγBarPaper`,
* `hDυ i` from `wkBundle.hDuLim_memLp_γ i` (Phase H5b derived),
  rewritten via `hγBarPaper`,
* `hV` directly,
* `hg_meas` from a.e.-strong-measurability composition (the `H` part
  via `hpow.measurable_H`, parallel to `WeakLimitInputBundle.hFlux_meas`).

This supersedes the legacy `hRes_Lp` field of
`FinalIntegrabilityPaperResidueLp` (Phase H5d strip; see the task
file `infra-P5-theorem1-phase-H5d-derive-hRes-Lp-collapse-finIntResidue`).
-/
theorem WeakLimitInputBundle.hRes_Lp
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H
        wkBundle.DuLim wkBundle.mLim wkBundle.uLim) := by
  -- Rewrite bundle exponents to the `hpow`-shape.
  have hμ : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.β + 1)) wkBundle.mLim := by
    rw [show ENNReal.ofReal (hpow.β + 1) = ENNReal.ofReal βBarReal from by
          rw [hβBarPaper]]
    exact wkBundle.hmLim_memLp
  -- `MemLpPer γBar uLim` from `huLim_sob.1` (Sobolev predicate is
  -- `MemLpPer ∧ ∃ weak derivs`).
  have hu_γ : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal γBarReal) wkBundle.uLim :=
    wkBundle.huLim_sob.1
  have hυ : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
              wkBundle.uLim := by
    rw [show ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)
          = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    exact hu_γ
  have hDυ : ∀ i, Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
              (wkBundle.DuLim i) := by
    intro i
    rw [show ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)
          = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    exact wkBundle.hDuLim_memLp_γ i
  -- A.e.-strong measurability of the residual `−uLim − H(·, DuLim, mLim) + V`.
  -- Pattern matches `WeakLimitInputBundle.hFlux_meas`: build measurability
  -- of the triple `(x, fun i => DuLim i x, mLim x)` and compose with
  -- `hpow.measurable_H`.
  have hDu_aem : ∀ i,
      AEMeasurable (fun x : (Fin d → ℝ) => wkBundle.DuLim i x)
        (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (wkBundle.hDuLim_memLp i).aestronglyMeasurable.aemeasurable
  have hDu_pi_aem :
      AEMeasurable (fun x : (Fin d → ℝ) =>
                      (fun i : Fin d => wkBundle.DuLim i x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr hDu_aem
  have hm_aem : AEMeasurable wkBundle.mLim
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    wkBundle.hmLim_memLp.aestronglyMeasurable.aemeasurable
  have hxpm : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => wkBundle.DuLim i x), wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_id.prodMk (hDu_pi_aem.prodMk hm_aem)
  have hH_aem : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hpow.measurable_H.comp_aemeasurable hxpm
  have hH_asm :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    hH_aem.aestronglyMeasurable
  have hu_asm := hu_γ.aestronglyMeasurable
  have hV_asm := hV.aestronglyMeasurable
  -- A.e.-strong measurability of the residual.
  have hg_meas' :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(wkBundle.uLim x)
            - H x (fun i => wkBundle.DuLim i x) (wkBundle.mLim x)
            + V x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    ((hu_asm.neg).sub hH_asm).add hV_asm
  -- Apply `g_memLp_betaBar'_nonneg`.
  have hres :=
    Hamiltonian.g_memLp_betaBar'_nonneg (d := d) hpow hHat0 hFin hAgree
      V wkBundle.uLim wkBundle.mLim wkBundle.DuLim
      wkBundle.hmLim_nonneg hg_meas' hμ hυ hDυ hV
  -- Identify with `hjbResidual`.
  exact hres

/-- **Sanity check (Phase H5d).** The derived `MemLpPer βBar'` of the
HJB residual at the weak limit is well-typed and projectible. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H
        wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :=
  WeakLimitInputBundle.hRes_Lp (d := d)
    hpow hHat0 hFin hAgree hV hβBarPaper hγBarPaper wkBundle

/-! ### `WeakLimitSelector` — the genuine periodic-representative-selector residue.

The fields of `WeakLimitInputBundle` split cleanly into two groups:

* **Auto-derivable from `(hExp, seq)`**: the abstract Banach
  reflexivity & strong-dual separability of
  `LpPer βBar d × SobolevPerLp 1 γBar d`. These follow from
  `hExp`'s `1 < βBar`, `βBar < ∞`, `1 < γBar`, `γBar < ∞`, the
  Hölder conjugacy `hExp.βConj`, and the auto-instance
  `lpPer_separable` (Mathlib's `Lp.SecondCountableTopology` on
  the cube measure).

* **Genuinely selector-dependent (Path A obstruction)**: the chosen
  periodic limit `(mLim, uLim, DuLim)`, the sequence-side bare
  representatives `seqRepU`, `seqRepDu`, the test-function
  `Tendsto`-of-integrals statements, and — crucially — the
  cluster-point a.e.-equality `auxAeOfClusterPoint`. None of these
  can be discharged from `(hExp, seq)` alone without first
  introducing a periodic-representative wrapper type for `Lp` (the
  parent task `infra-P4-rebuild-T8-discharge-aux-weakLimit-selector`
  recorded this as the irreducible Path-A obstruction).

`WeakLimitSelector` packages **only the second group** as authorised
inputs to the producer below. -/

/-- **Selector-only authorised inputs** for the
`WeakLimitInputBundle` producer.

Per CONVENTIONS §8 (statement-then-proof discipline), this structure
isolates the genuinely Path-A-selector-dependent fields of
`WeakLimitInputBundle`, leaving the producer to discharge reflexivity
& separability automatically from `hExp`. -/
structure WeakLimitSelector
    (γBarReal βBarReal : ℝ) where
  /-- Chosen periodic bare-function `m`-limit. -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function `u`-limit. -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function gradient-limit family. -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- Periodicity of `mLim`. -/
  hMlimPer : Periodic.IsPeriodic mLim
  /-- Periodicity of `uLim`. -/
  hUlimPer : Periodic.IsPeriodic uLim
  /-- `MemLpPer 1` of every gradient-limit component. -/
  hDuLim_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim i)
  /-- Periodicity of every gradient-limit component.

  Phase 6a (infra-P5-theorem1-phase-6a-wkBundle-perTestTripleBase):
  added so the upstream `WeakLimitInputBundle.hDuLim_periodic` field
  can be populated. At the AE-native selector layer this is the
  underlying `AEPeriodicRep.periodic`; in the legacy selector it is
  an authorised paper-residue input. -/
  hDuLim_periodic : ∀ i, Periodic.IsPeriodic (DuLim i)
  /-- Sequence-side periodic representative of the `u`-component. -/
  seqRepU : ℕ → (Fin d → ℝ) → ℝ
  /-- Sequence-side periodic representative of the gradient family. -/
  seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Per-`n`, per-`i` weak-derivative relation. -/
  hSeqRepWeak : ∀ n i,
    Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i)
  /-- Test-function `Tendsto` for `seqRepU`. -/
  hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepU (φ k) x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Test-function `Tendsto` for `seqRepDu`. -/
  hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepDu (φ k) i x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Cluster-point-residue selector: a.e.-equality between the chosen
  bare-function limit and the cluster point's `Lp.coeFn` representative.
  Universally quantified over `w`, capturing the strict Path-A
  obstruction. -/
  auxAeOfClusterPoint : ∀
    (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d),
      mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
      ∧ uLim
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
      ∧ ∀ i, DuLim i
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
  /-- `mLim ∈ L^{βBar}_per`. -/
  hmLim_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) mLim
  /-- `uLim ∈ W^{1,γBar}_per`. -/
  huLim_sob : Periodic.MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim
  /-- `0 ≤ mLim` a.e. on the unit cube. -/
  hmLim_nonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] mLim

/-! ### Producer: `weakLimitInputBundle_of_regularizedSequence`

Per CONVENTIONS §8, this discharges AC1 of the parent task
(`infra-P4-rebuild-T9-discharge-weak-limit-bundle`) genuinely:
reflexivity and strong-dual separability are **derived** from `hExp`
via `Periodic.lpSobolev_product_isReflexive` and
`Periodic.lpSobolev_product_strongDual_separable`. AC2 / AC3 of the
parent task (the periodic-representative selector) cannot be
honestly closed from `(hExp, seq)` alone in the current structure
(see the `WeakLimitSelector` docstring above for the rationale);
they are taken as authorised inputs through `selector`.

The follow-up task
`infra-P4-rebuild-T9-discharge-weak-limit-bundle-selector` will close
the `WeakLimitSelector` field-by-field once a periodic-representative
wrapper type for `Lp` is in place.

The producer signature is:
```
weakLimitInputBundle_of_regularizedSequence
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (selector : WeakLimitSelector γBarReal βBarReal) :
    WeakLimitInputBundle γBarReal βBarReal
```
-/

/-- **AC1 producer (genuine).** Build a `WeakLimitInputBundle` whose
reflexivity and strong-dual separability fields are **derived from
`hExp`** (via `Periodic.lpSobolev_product_isReflexive` and
`Periodic.lpSobolev_product_strongDual_separable`). The genuinely
selector-dependent fields are read off `selector`.

This discharges the AC1 of `infra-P4-rebuild-T9-discharge-weak-limit-bundle`
in full; AC2 / AC3 are amended into the `WeakLimitSelector` parameter
per CONVENTIONS §8 (filed follow-up
`infra-P4-rebuild-T9-discharge-weak-limit-bundle-selector`). -/
noncomputable def weakLimitInputBundle_of_regularizedSequence
    {γBarReal βBarReal βBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (selector : WeakLimitSelector (d := d) γBarReal βBarReal) :
    WeakLimitInputBundle (d := d) γBarReal βBarReal := by
  -- Step 1: derive `0 < βBarReal` from `1 < ENNReal.ofReal βBarReal`.
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
  -- Step 2: derive `1 < βBarReal'` from `hExp.βConj.symm.lt` (the latter
  -- gives `1 < (ENNReal.ofReal βBarReal').toReal`); then `0 < βBarReal'`.
  have h_one_lt_βBarReal'_toReal :
      (1 : ℝ) < (ENNReal.ofReal βBarReal').toReal :=
    hExp.βConj.symm.lt
  -- We also need positivity of `βBarReal'` to identify
  -- `(ENNReal.ofReal βBarReal').toReal = βBarReal'`. From
  -- `1 < ENNReal.ofReal βBarReal'` we get `0 < βBarReal'`.
  have h_one_lt_βBar' : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal' := by
    -- `hExp.βConj.symm.lt` gives a real-side strict inequality; `betaBar'_one_lt`
    -- in `hExp` is the ℝ≥0∞-side analogue (since `hExp` carries
    -- `betaBar'_one_lt : 1 < ENNReal.ofReal βBarReal'`).
    exact hExp.betaBar'_one_lt
  have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
    by_contra hle
    push_neg at hle
    -- If `βBarReal' ≤ 0`, then `ENNReal.ofReal βBarReal' = 0`.
    have h_zero : ENNReal.ofReal βBarReal' = 0 := by
      apply ENNReal.ofReal_eq_zero.mpr hle
    rw [h_zero] at h_one_lt_βBar'
    exact absurd h_one_lt_βBar' (by simp)
  have h_βBar'_toReal_eq : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
    ENNReal.toReal_ofReal h_βBarReal'_pos.le
  have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
    h_one_lt_βBar'.le
  haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') := ⟨h_one_le_βBar'⟩
  -- Recast `hExp.βConj` as `Real.HolderConjugate βBarReal βBarReal'`.
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
  -- Step 3: similar setup for `γBar`. Conjugate exponent is `γBarReal/(γBarReal - 1)`.
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
  -- Step 4: `βBar ≠ ∞` and `γBar ≠ ∞`.
  have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  -- Step 5: reflexivity & separability via the discharged infrastructure.
  have hRefl :
      Periodic.IsReflexiveNormedSpace
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
    Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  have hSep :
      TopologicalSpace.SeparableSpace
        (StrongDual ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)) :=
    Periodic.lpSobolev_product_strongDual_separable (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Step 6: assemble the bundle from the discharged + selector parts.
  exact
    { hRefl := hRefl
      hSep := hSep
      mLim := selector.mLim
      uLim := selector.uLim
      DuLim := selector.DuLim
      hMlimPer := selector.hMlimPer
      hUlimPer := selector.hUlimPer
      hDuLim_memLp := selector.hDuLim_memLp
      hDuLim_periodic := selector.hDuLim_periodic
      seqRepU := selector.seqRepU
      seqRepDu := selector.seqRepDu
      hSeqRepWeak := selector.hSeqRepWeak
      hConvU := selector.hConvU
      hConvDu := selector.hConvDu
      auxAeOfClusterPoint := selector.auxAeOfClusterPoint
      hmLim_memLp := selector.hmLim_memLp
      huLim_sob := selector.huLim_sob
      hmLim_nonneg := selector.hmLim_nonneg }

/-- **AC1 sanity check.** `weakLimitInputBundle_of_regularizedSequence`
produces a `WeakLimitInputBundle` from `(hExp, selector)` alone (the
selector packages the genuine Path-A residue per CONVENTIONS §8). -/
example
    {γBarReal βBarReal βBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (selector : WeakLimitSelector (d := d) γBarReal βBarReal) :
    WeakLimitInputBundle (d := d) γBarReal βBarReal :=
  weakLimitInputBundle_of_regularizedSequence hExp selector

end Banach
end SimplePower
end Theorems
end StationaryMFG
end
