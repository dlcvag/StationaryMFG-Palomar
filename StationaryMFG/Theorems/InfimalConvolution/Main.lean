module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.BoundaryContinuityConvex
public import StationaryMFG.Solutions.Weak
public import StationaryMFG.Theorems.InfimalConvolution.Existence
public import StationaryMFG.Theorems.InfimalConvolution.Apriori
public import StationaryMFG.Theorems.InfimalConvolution.Compactness
public import StationaryMFG.Theorems.InfimalConvolution.Stabilization
public import StationaryMFG.Theorems.InfimalConvolution.LimitPassage
public import StationaryMFG.Theorems.InfimalConvolution.AprioriDrain

@[expose] public section

/-!
# Theorem 3 — main existence theorem under `HypothesisWeakGrowth`
(paper `thm:main-weak.power.growth`)

Paper reference: `Source/FGU-monotone_revised.tex`, line 327
(statement), lines 1945–1986 (proof in §`sec:proof-weak-growth`).

## Paper statement

Under `(onH.monotone)` (`HypothesisMonotone H DpH`),
`(onH.weakgrowth)` (`HypothesisWeakGrowth H DpH`), and
`V ∈ L^{β̄'}_per`, there exists a **weak solution**
`(m, u) ∈ L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d)` to Problem `prob.smfg`
in the sense of Definition `def:weak` (paper line 286, formalised as
`StationaryMFG.Solutions.Weak.IsWeakSolution`).

## Paper proof outline (lines 1945–1986)

1. By Proposition `thm:strongAepsi.delta` (paper line 1838,
   formalised as `Theorems.InfimalConvolution.thm_strongAepsi_delta`,
   landed iter 0809), for any sequence `ε_k → 0⁺` there exist
   strong-VI solutions `(m_{ε_k}, u_{ε_k})` for the regularized
   operator `A_{ε_k}` (built from the infimal convolution
   `H^{ε_k} := Hdelta H ε_k`).
2. For any test pair `(μ, υ) ∈ L^∞_per × W^{1,∞}_per` with
   `essinf μ > 0`, by `HypothesisWeakGrowth.DpH_upper`
   (`eq:assH.DpH.upper.weak`) the function `D_pH(·, Dυ, μ)` is in
   `L^∞_per`.
3. By Remark `observation` (paper line 1923, formalised in
   `Theorems.InfimalConvolution.Stabilization` /
   `paper-observation-stabilization`), for sufficiently small `ε`,
   `H^ε(x, Dυ, μ) = H(x, Dυ, μ)` and
   `D_pH^ε(x, Dυ, μ) = D_pH(x, Dυ, μ)` pointwise. This is paper
   `eq:existweaksol.delta` (line 1968).
4. By `thm:apriori-weak.power.growth` (paper line 1881, formalised
   as `Theorems.InfimalConvolution.apriori_weak_power_growth`) plus
   weak compactness (`Theorems.InfimalConvolution.Compactness`,
   formalising `eq:compactness.delta`), up to a subsequence
   `(m_{ε_k}, u_{ε_k}) ⇀ (m, u)` weakly in
   `L^{β̄}_per(𝕋^d; ℝ⁺_0) × W^{1,γ̄}_per(𝕋^d)`.
5. Letting `k → ∞` in `eq:existweaksol.delta` using Hölder pairings
   of `L^{β̄'}_per × L^{β̄}_per` and `W^{-1,γ̄'}_per × W^{1,γ̄}_per`,
   plus the vanishing of the `ε_k`-prefactored regularisation terms
   (`(υ - u_{ε_k})` uniformly bounded in `W^{1,γ̄}_per` and
   `ε_k → 0`), one concludes Definition `def:weak` for `(m, u)`
   against the restricted test space `L^∞_per × W^{1,∞}_per` with
   `essinf μ > 0`.

**Structural remark (paper line 1610 / 1326 sibling).** Unlike
`thm:main-simple.power.growth` (Theorem 1), the limit pair `(m, u)`
need **not** lie in the admissible set `𝓚` (no a-priori
`essinf m > 0`), so `rmk:hemicontinuous-upgrade` is **not** invoked
here. The conclusion is a *weak* solution, not a strong one. This
is the structural reason `paper:def:weak` exists in the first place,
paralleling the way `paper:lem:weak.is.strong` services Theorem 2.

## Lean encoding

Per CONVENTIONS §8 (statement-then-proof discipline) and following
the sibling pattern of `thm_main_congestion_growth_paper`
(`Theorems.Congestion.Main`, paper Theorem 2, line 320) and
`thm_main_simplePowerGrowth_paper` (paper Theorem 1, line 314), the
capstone of this module is the **genuinely-closed public theorem**
`thm_main_weak_power_growth_paper`. It takes only paper hypotheses
(`hmon`, `hweak`, `hdiff`, `hmeas`, `hV`) plus documented accepted
AE-route/regularity/V-bound carriers and conjugacy/exponent facts,
and builds the regularized strong-VI family, its side data, the A4
stabilisation `hstab`, and the canonical `ε`-sequence **internally**
before delegating to the conditional limit-passage intermediate.

The limit-passage analytic core (weak-VI limit passage on
`eq:existweaksol.delta`, cone preservation at the weak limit, and the
Hölder pairings of step 5) lives in
`thm_main_weak_power_growth_from_regularized_family`, which is stated
conditionally on a pre-built regularized family + side data.

## Deliverables

* `thm_main_weak_power_growth_paper` — the FINAL genuinely-closed
  public theorem (paper line 327, `thm:main-weak.power.growth`).
  Builds the regularized family, side data, `hstab`, and the
  `ε`-sequence internally; binders are paper hypotheses + accepted
  carriers + conjugacy/exponent facts only.
* `thm_main_weak_power_growth_from_regularized_family` — the
  conditional limit-passage intermediate consumed by the public
  theorem. Takes a pre-built `fam : T3RegularizedStrongFamily`,
  `side : T3RegularizedSideData`, `hstab`, and `εseq` data, and runs
  the C1/C2/C3 weak-limit assembly to the paper `def:weak`
  existential. Conditional, not closed on its own.
* Internal helpers: `weakEpsTerms*`, `T3.hstab_of_selectorFamily`,
  `T3.hIA_of_T3RegularizedStrongFamily`, and the various Hölder-balance
  integrability producers about the internal family.

## References

* Paper: `Source/FGU-monotone_revised.tex`, line 327 (statement),
  lines 1945–1986 (proof, §`sec:proof-weak-growth`); equations
  `eq:existweaksol.delta`, `eq:compactness.delta`.
* Dependencies (all `done`):
  - `paper-thm-strongAepsi-delta` (iter 0809) →
    `Theorems.InfimalConvolution.Existence.thm_strongAepsi_delta`;
  - `paper-thm-apriori-weak-power-growth` →
    `Theorems.InfimalConvolution.Apriori.apriori_weak_power_growth`;
  - `paper-observation-stabilization` →
    `Theorems.InfimalConvolution.Stabilization.stabilization_uniform_of_DpH_small`;
  - `infra-P6-weak-compactness` →
    `Theorems.InfimalConvolution.Compactness.exists_weak_limit_sequence_pair`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace InfimalConvolution

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.Weak
open StationaryMFG.Solutions.MFG
open StationaryMFG.InfimalConvolution
open StationaryMFG.Theorems.SimplePower
open scoped ENNReal Topology

variable {d : ℕ}

/-! ## T3 canonical ε-perturbation remainder

The §1b regularised identity (`hIdentityRaw` in
`T3RegularizedSideData.of_paperHypotheses` and its `AprioriDrain`
relatives) carries an additive ε-perturbation remainder `epsTerms ε x`, which
the consumers use **only** through its non-negativity (`hEpsNNRaw`). The
remainder is otherwise an arbitrary loose function binder.

The canonical paper form of this remainder is pinned as the Euclidean-norm
definition `T3.weakEpsTermsEucl` (below), with its non-negativity
`T3.weakEpsTermsEucl_nonneg`. The D6h family instantiation is
`fun ε => T3.weakEpsTermsEucl γBar ε (fam.u ε) (fam.Du ε)`, so the `epsTerms` /
`hEpsNN(Raw)` binders are dropped from the public theorem. Non-negativity is
all the consumers require of the remainder. -/

namespace T3

/-! ### D6g1 — `hIBC` as an internal producer from `L^∞×W^{1,∞}` test data

The transport-side HJB test integrability `hIBC` of
`T3RegularizedSideData.of_paperHypotheses` is genuinely derivable from the family
regularity (`fam.hDuLp`, `fam.huSob`) together with the paper weak-test
predicate (`IsWeakSolutionTestPair`: `μ ∈ L^∞`, `essinf μ > 0`,
`υ ∈ W^{1,∞}`, `Dυ_i ∈ L^∞`).  The key analytic step is that
`D_pH(·, Dυ, μ)` is **essentially bounded** on the cube, via the paper's
gradient bound `hweak.DpH_upper` (`‖D_pH(x,p,m)‖ ≤ f(p,m)` for `m>0`)
and the continuity `hweak.hf_continuous` of `f` on `{m>0}`: the a.e.
range of `x ↦ (Dυ x, μ x)` lies in a compact box `K ⊆ {m>0}` (from the
`L^∞` bounds and `essinf μ ≥ c > 0`), so `f` is bounded on `K`.

No `H`-at-test-data certificate is needed here — that is the genuinely
missing certificate isolated in the sibling task `D6g2-hIA`. -/

open scoped Hamiltonian in
/-- **D6g1 a.e. boundedness of `D_pH(·, Dυ, μ)`** for an admissible test
pair.  From `hweak.DpH_upper` (`‖D_pH‖ ≤ f` for `m>0`), `essinf μ > 0`,
the `L^∞` bounds on `Dυ`/`μ`, and continuity of `f` on `{m>0}`, the
Euclidean norm of `x ↦ D_pH(x, Dυ x, μ x)` is a.e. bounded by a single
nonnegative constant on the cube. -/
theorem dpH_ae_norm_le_of_testPair
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ} {μ υ : (Fin d → ℝ) → ℝ}
    (htp : IsWeakSolutionTestPair Dυ μ υ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (fun i => Dυ i x) (μ x)‖ ≤ M := by
  classical
  -- `essinf μ ≥ c > 0`.
  obtain ⟨c, hc_pos, hc_le⟩ := htp.lower
  -- a.e. `L^∞` bound on the momentum vector `(Dυ x)`.
  obtain ⟨R, hR_nn, hR⟩ :=
    exists_ae_vector_norm_bound (fun i => htp.Dυ_linf i)
  -- a.e. `L^∞` bound on `μ`.
  obtain ⟨Bμ, hBμ_nn, hBμ⟩ := htp.μ_linf.exists_ae_norm_le
  -- The compact box `K = closedBall 0 R × Icc c (Bμ + c) ⊆ {m>0}`.
  set K : Set ((Fin d → ℝ) × ℝ) :=
    (Metric.closedBall (0 : Fin d → ℝ) R) ×ˢ Set.Icc c (Bμ + c) with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hK_sub : K ⊆ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
    rintro ⟨p, m⟩ ⟨_, hm⟩
    exact lt_of_lt_of_le hc_pos hm.1
  have hK_ne : K.Nonempty := by
    refine ⟨((0 : Fin d → ℝ), c), ?_, ?_⟩
    · simp [Metric.mem_closedBall, hR_nn]
    · exact ⟨le_rfl, by linarith [hc_pos.le]⟩
  -- `f` is bounded on the compact box (extreme value theorem on `{m>0}`).
  have hf_cont_K : ContinuousOn
      (fun pm : (Fin d → ℝ) × ℝ => hweak.f pm.1 pm.2) K :=
    hweak.hf_continuous.mono hK_sub
  obtain ⟨pm0, _, hmax⟩ := hK_compact.exists_isMaxOn hK_ne hf_cont_K
  set Mf : ℝ := hweak.f pm0.1 pm0.2 with hMf_def
  refine ⟨max Mf 0, le_max_right _ _, ?_⟩
  -- a.e. combine the gradient bound, the `L^∞` bounds, and `f`-boundedness.
  filter_upwards [hweak.DpH_upper, hR, hBμ] with x hDpHx hRx hBμx
  -- the test point `(Dυ x, μ x)` lies in the box `K`.
  have hμx_pos : 0 < μ x := lt_of_lt_of_le hc_pos (hc_le x)
  have hmem : ((fun i => Dυ i x), μ x) ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right] using hRx
    · exact hc_le x
    · have : μ x ≤ Bμ := le_trans (le_abs_self _) (by simpa using hBμx)
      linarith [hc_pos.le]
  -- `‖D_pH‖ ≤ f(Dυ x, μ x) ≤ Mf ≤ max Mf 0`.
  calc ‖DpH x (fun i => Dυ i x) (μ x)‖
      ≤ hweak.f (fun i => Dυ i x) (μ x) := hDpHx _ _ hμx_pos
    _ ≤ Mf := hmax hmem
    _ ≤ max Mf 0 := le_max_left _ _

open scoped Hamiltonian in
/-- **D6g1 `hIBC_of_T3RegularizedStrongFamily`.**  The HJB test-pair
integrability clause, produced internally from the regularized family
`fam` and the paper weak-test predicate `htp`.  Drains the `hIBC` binder
of `T3RegularizedSideData.of_paperHypotheses`.

The integrand is `μ·(D_pH(·,Dυ,μ) ⬝ (Dυ − Du_e)) + (μ−1)·(υ − u_e)`,
expanded as `∑ᵢ (μ·D_pH_i)·(Dυ_i − Du_e i) + (μ−1)·(υ − u_e)`.  Each
summand is `(bounded) × (integrable)`:

* `μ·D_pH_i` is essentially bounded (`dpH_ae_norm_le_of_testPair` × `μ`'s
  `L^∞` bound) and `Dυ_i − Du_e i ∈ L^{γ̄} ⊆ L¹`;
* `μ−1` is essentially bounded and `υ − u_e ∈ L^{γ̄} ⊆ L¹`.

No `H`-at-test certificate is used. -/
theorem hIBC_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ} (hγ : 1 ≤ γBarReal)
    {V : (Fin d → ℝ) → ℝ}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {qε : QEpsFamily d}
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ)
    (htp : IsWeakSolutionTestPair Dυ μ υ) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    IntegrableOn
      (fun x =>
        μ x * (DpH x (fun i => Dυ i x) (μ x)
                ⬝ (fun i => Dυ i x - fam.Du e i x))
          + (μ x - 1) * (υ x - fam.u e x))
      (UnitCube d) := by
  classical
  set ν : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hν_def
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_unitCube]
    exact ENNReal.one_lt_top
  have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hγ
  -- `MemLpPer (ofReal γ̄) → Integrable` on the finite cube (`L^{γ̄} ⊆ L¹`).
  have memγ_int : ∀ {g : (Fin d → ℝ) → ℝ},
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) g → Integrable g ν :=
    fun {g} hg => (hg.toMemLp.mono_exponent h1le).integrable le_rfl
  -- L^∞ bounds on the test data.
  obtain ⟨Bμ, hBμ_nn, hBμ⟩ := htp.μ_linf.exists_ae_norm_le
  -- a.e. bound on `D_pH(·,Dυ,μ)`.
  obtain ⟨MD, hMD_nn, hMD⟩ := dpH_ae_norm_le_of_testPair hweak htp
  -- `υ`, `Dυ_i` as `MemLpPer (ofReal γ̄)` (from `L^∞`, finite cube).
  have hυ_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) υ :=
    MemLpPer.of_top_finite (by simp) htp.υ_sob_linf.1
  have hDυ_γ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i) :=
    fun i => MemLpPer.of_top_finite (by simp) (htp.Dυ_linf i)
  -- AEStronglyMeasurable factors.
  have hμ_aesm : AEStronglyMeasurable μ ν :=
    (MemLpPer.of_top_finite (q := ENNReal.ofReal γBarReal) (by simp)
      htp.μ_linf).aestronglyMeasurable
  -- `x ↦ D_pH(x, Dυ x, μ x)` is AE-strongly-measurable: compose
  -- `measurable_DpH` with the AE-measurable test data `(x, Dυ x, μ x)`.
  have hμ_aem : AEMeasurable μ ν := hμ_aesm.aemeasurable
  have hDυ_aem : ∀ j, AEMeasurable (Dυ j) ν :=
    fun j => (MemLpPer.of_top_finite (q := ENNReal.ofReal γBarReal)
      (by simp) (htp.Dυ_linf j)).aestronglyMeasurable.aemeasurable
  have hPi_aem : AEMeasurable (fun x => (fun j => Dυ j x)) ν :=
    AEMeasurable.of_eval hDυ_aem
  have hTriple_aem : AEMeasurable
      (fun x => (x, ((fun j => Dυ j x), μ x))) ν :=
    aemeasurable_id.prodMk (hPi_aem.prodMk hμ_aem)
  have hDpHcomp_aem : AEMeasurable
      (fun x => DpH x (fun j => Dυ j x) (μ x)) ν :=
    hweak.measurable_DpH.comp_aemeasurable hTriple_aem
  have hDpHcomp_aesm : ∀ i, AEStronglyMeasurable
      (fun x => DpH x (fun j => Dυ j x) (μ x) i) ν := by
    intro i
    have hcomp : AEStronglyMeasurable
        (fun x => DpH x (fun j => Dυ j x) (μ x)) ν :=
      aestronglyMeasurable_iff_aemeasurable.mpr hDpHcomp_aem
    exact (continuous_apply i).comp_aestronglyMeasurable hcomp
  -- The gradient summand `∑ᵢ (μ·D_pH_i)·(Dυ_i − Du_e i)`.
  have hGrad : ∀ i, Integrable
      (fun x => (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                  * (Dυ i x - fam.Du e i x)) ν := by
    intro i
    -- integrable factor `Dυ_i − Du_e i ∈ L^{γ̄}`.
    have hg_int : Integrable (fun x => Dυ i x - fam.Du e i x) ν := by
      have := (memγ_int (hDυ_γ i)).sub (memγ_int (fam.hDuLp e he he1 i))
      simpa only [Pi.sub_def] using this
    -- bounded factor `μ·D_pH_i`.
    have hbdd_aesm : AEStronglyMeasurable
        (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) ν :=
      hμ_aesm.mul (hDpHcomp_aesm i)
    have hbdd : ∀ᵐ x ∂ν,
        ‖μ x * DpH x (fun j => Dυ j x) (μ x) i‖ ≤ Bμ * MD := by
      filter_upwards [hBμ, hMD] with x hBμx hMDx
      have hi : ‖DpH x (fun j => Dυ j x) (μ x) i‖ ≤ MD :=
        le_trans (norm_le_pi_norm _ i) hMDx
      calc ‖μ x * DpH x (fun j => Dυ j x) (μ x) i‖
          = ‖μ x‖ * ‖DpH x (fun j => Dυ j x) (μ x) i‖ := by rw [norm_mul]
        _ ≤ Bμ * MD :=
            mul_le_mul (by simpa using hBμx) hi (norm_nonneg _) hBμ_nn
    have := hg_int.bdd_mul hbdd_aesm hbdd
    simpa using this
  -- The value summand `(μ−1)·(υ − u_e)`.
  have hVal : Integrable (fun x => (μ x - 1) * (υ x - fam.u e x)) ν := by
    have hg_int : Integrable (fun x => υ x - fam.u e x) ν := by
      have := (memγ_int hυ_γ).sub (memγ_int (fam.huSob e he he1).1)
      simpa only [Pi.sub_def] using this
    have hbdd_aesm : AEStronglyMeasurable (fun x => μ x - 1) ν :=
      hμ_aesm.sub aestronglyMeasurable_const
    have hbdd : ∀ᵐ x ∂ν, ‖μ x - 1‖ ≤ Bμ + 1 := by
      filter_upwards [hBμ] with x hBμx
      calc ‖μ x - 1‖ ≤ ‖μ x‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ Bμ + 1 := by
            have : ‖μ x‖ ≤ Bμ := by simpa using hBμx
            simp only [norm_one]; linarith
    have := hg_int.bdd_mul hbdd_aesm hbdd
    simpa using this
  -- Assemble: dot product = `∑ᵢ D_pH_i·(Dυ_i − Du_e i)`, so the whole
  -- integrand is `∑ᵢ (μ·D_pH_i)·(Dυ_i − Du_e i) + (μ−1)·(υ − u_e)`.
  have hSum : Integrable
      (fun x => (∑ i, (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                    * (Dυ i x - fam.Du e i x))
                + (μ x - 1) * (υ x - fam.u e x)) ν :=
    (integrable_finset_sum Finset.univ (fun i _ => hGrad i)).add hVal
  refine hSum.congr ?_
  filter_upwards with x
  have hdot : μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - fam.Du e i x))
      = ∑ i, (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - fam.Du e i x) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hdot]

/-! ### D6g2 — `hIA` as an internal producer via the regularized carrier

The transport-side test integrability `hIA` of `T3RegularizedSideData.of_paperHypotheses`
needs the base-`H` composite `H(·, Dυ, μ)` to be `L^{β̄'}` on the test data.
Per the Orchestrator pointer, the missing upper bound is supplied — without a
new paper-side rider — by routing through the **regularized** carrier
`HdeltaK0 hweak e`:

* the test pair has `essinf μ ≥ c > 0`, so the `m > 0` envelope of
  `HdeltaAEPowerEpsData.H_upper_pointwise_ae` applies (no boundary issue);
* the per-test-pair stabilization `hstab` (Remark `observation`) gives
  `HdeltaK0 hweak e (·, Dυ, μ) = H(·, Dυ, μ)` a.e. for any `e` below the
  test-pair threshold, transferring the `Hdelta` upper bound to base `H`;
* the lower bound is `hweak.lower` (base `H`) directly.

Both bounds are a.e. CONSTANT on the cube (the `L^∞` envelopes of `Dυ`/`μ`
control `‖p‖^α` and `m^β`), so `H(·, Dυ, μ)` is a.e. bounded; mirrors the
compact-box shape of `dpH_ae_norm_le_of_testPair`. No new `H`-upper-growth
hypothesis is introduced. -/

open scoped Hamiltonian in
/-- **D6g2 a.e. boundedness of `H(·, Dυ, μ)`** for an admissible test pair.
The lower bound is `hweak.lower` (base `H`); the upper bound is transferred
from the regularized carrier `HdeltaK0 hweak e` via the stabilization equality
`hstab` and `hAE.H_upper_pointwise_ae`.  The `L^∞` envelopes of `Dυ`/`μ` plus
`essinf μ ≥ c > 0` turn both bounds into a single nonnegative constant. -/
theorem H_ae_norm_le_of_testPair
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {Dυ : Fin d → (Fin d → ℝ) → ℝ} {μ υ : (Fin d → ℝ) → ℝ}
    (htp : IsWeakSolutionTestPair Dυ μ υ)
    -- Remark `observation` (paper line 1923) at this test pair: for `e` below
    -- the per-test-pair threshold, the regularized composite agrees with `H`.
    (hstab : ∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           HdeltaK0 hweak e x (fun i => Dυ i x) (μ x)
             = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHepsilonFam hweak qε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        |H x (fun i => Dυ i x) (μ x)| ≤ M := by
  classical
  -- `essinf μ ≥ c > 0`.
  obtain ⟨c, hc_pos, hc_le⟩ := htp.lower
  -- a.e. `L^∞` bound on the momentum vector `(Dυ x)`.
  obtain ⟨R, hR_nn, hR⟩ :=
    exists_ae_vector_norm_bound (fun i => htp.Dυ_linf i)
  -- a.e. `L^∞` bound on `μ`.
  obtain ⟨Bμ, hBμ_nn, hBμ⟩ := htp.μ_linf.exists_ae_norm_le
  -- Hamiltonian-side growth constants.
  have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
  have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
  have hβ_pos : (0 : ℝ) < hweak.β := hweak.hβ
  -- Pick one regularization scale `e` below the test-pair threshold.
  obtain ⟨ε₀, hε₀_pos, hstab_e⟩ := hstab
  set e : ℝ := min (ε₀ / 2) 1 with he_def
  have he_pos : 0 < e := lt_min (by positivity) one_pos
  have he_lt : e < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he_le1 : e ≤ 1 := min_le_right _ _
  obtain ⟨hHeq, _⟩ := hstab_e e he_pos he_lt
  -- The per-`e` regularization constant `Cₑ > 0`.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak e with hCε_def
  obtain ⟨hCε_pos, _⟩ := cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak he_pos
  -- The single constant bound: `M := max (Cₑ(R^α+1)) (C(Bμ^β+1))`.
  refine ⟨max (Cε * (R ^ hweak.α + 1)) (hweak.C * (Bμ ^ hweak.β + 1)), ?_, ?_⟩
  · refine le_trans ?_ (le_max_left _ _)
    have : 0 ≤ R ^ hweak.α := Real.rpow_nonneg hR_nn _
    positivity
  -- a.e. combine the lower (base `H`) and upper (via `Hdelta = H`) bounds.
  filter_upwards [hHeq, hAE.H_upper_pointwise_ae e he_pos he_le1,
    hweak.lower, hR, hBμ] with x hHeqx hUpx hLowx hRx hBμx
  have hμx_pos : 0 < μ x := lt_of_lt_of_le hc_pos (hc_le x)
  have hμx_le : μ x ≤ Bμ := le_trans (le_abs_self _) (by simpa using hBμx)
  set p : Fin d → ℝ := fun i => Dυ i x with hp_def
  have hpnorm : ‖p‖ ≤ R := hRx
  -- nonnegativity of the powers.
  have hpα_nn : 0 ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
  have hμβ_nn : 0 ≤ (μ x) ^ hweak.β := Real.rpow_nonneg hμx_pos.le _
  -- Upper: `H = Hdelta ≤ Cₑ(‖p‖^α+1) − μ^β/Cₑ ≤ Cₑ(R^α+1)`.
  have hUpper : H x p (μ x) ≤ Cε * (R ^ hweak.α + 1) := by
    have hHd := hUpx p (μ x) hμx_pos
    rw [← HdeltaK0_eq_Hdelta_of_pos hweak hμx_pos] at hHd
    rw [hHeqx] at hHd
    have hpαR : ‖p‖ ^ hweak.α ≤ R ^ hweak.α :=
      Real.rpow_le_rpow (norm_nonneg _) hpnorm hα_pos.le
    have hdiv_nn : 0 ≤ (μ x) ^ hweak.β / Cε := div_nonneg hμβ_nn hCε_pos.le
    calc H x p (μ x)
        ≤ Cε * (‖p‖ ^ hweak.α + 1) - (μ x) ^ hweak.β / Cε := hHd
      _ ≤ Cε * (R ^ hweak.α + 1) - 0 := by
            gcongr
      _ = Cε * (R ^ hweak.α + 1) := by ring
  -- Lower: `H ≥ ‖p‖^α/C − C(μ^β+1) ≥ −C(Bμ^β+1)`.
  have hLower : -(hweak.C * (Bμ ^ hweak.β + 1)) ≤ H x p (μ x) := by
    have hHl := hLowx p (μ x) hμx_pos
    have hdivp_nn : 0 ≤ ‖p‖ ^ hweak.α / hweak.C := div_nonneg hpα_nn hC_pos.le
    have hμβR : (μ x) ^ hweak.β ≤ Bμ ^ hweak.β :=
      Real.rpow_le_rpow hμx_pos.le hμx_le hβ_pos.le
    have : -(hweak.C * (Bμ ^ hweak.β + 1))
        ≤ ‖p‖ ^ hweak.α / hweak.C - hweak.C * ((μ x) ^ hweak.β + 1) := by
      have hmono : hweak.C * ((μ x) ^ hweak.β + 1)
          ≤ hweak.C * (Bμ ^ hweak.β + 1) := by
        gcongr
      linarith [hdivp_nn]
    exact le_trans this hHl
  -- Combine into the absolute-value bound.
  rw [abs_le]
  constructor
  · refine le_trans (neg_le_neg (le_max_right _ _)) ?_
    exact hLower
  · exact le_trans hUpper (le_max_left _ _)

open scoped Hamiltonian in
/-- **D6g2 `hIA_of_T3RegularizedStrongFamily`.**  The transport test-pair
integrability clause, produced internally from the regularized family `fam`,
the AE carrier `hAE`, and the per-test-pair stabilization `hstab`.  Drains the
`hIA` binder of `T3RegularizedSideData.of_paperHypotheses`.

The integrand is `A·(μ − fam.m e)` with `A = −υ − H(·,Dυ,μ) + V`, split as:

* `(−υ − H(·,Dυ,μ))·(μ − fam.m e)` : `(a.e. bounded) × L¹` — `H(·,Dυ,μ)` is
  a.e. bounded by `H_ae_norm_le_of_testPair`, `υ ∈ L^∞`, and
  `μ − fam.m e ∈ L¹` (`μ ∈ L^∞ ⊆ L¹`, `fam.m e ∈ L^{β̄} ⊆ L¹`);
* `V·(μ − fam.m e)` : `L^{β̄'} × L^{β̄}` Hölder product via
  `MemLpPer.integrable_mul`.

No new `H`-upper-growth hypothesis is introduced: the upper bound is the
regularized `Hdelta` envelope transferred through `hstab`. -/
theorem hIA_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal βBar' : ℝ}
    (hpqβ : βBarReal.HolderConjugate βBar')
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ)
    (htp : IsWeakSolutionTestPair Dυ μ υ)
    (hstab : ∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           HdeltaK0 hweak e x (fun i => Dυ i x) (μ x)
             = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHepsilonFam hweak qε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x)))
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          * (μ x - fam.m e x))
      (UnitCube d) := by
  classical
  set ν : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hν_def
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_unitCube]
    exact ENNReal.one_lt_top
  -- L^∞ bound on `μ` and `υ`.
  obtain ⟨Bμ, hBμ_nn, hBμ⟩ := htp.μ_linf.exists_ae_norm_le
  obtain ⟨Bυ, hBυ_nn, hBυ⟩ := htp.υ_sob_linf.1.exists_ae_norm_le
  -- a.e. bound on `H(·, Dυ, μ)`.
  obtain ⟨MH, hMH_nn, hMH⟩ := H_ae_norm_le_of_testPair hweak hAE htp hstab
  -- `μ ∈ L¹` (from `L^∞`, finite cube) and `fam.m e ∈ L¹` (from `L^{β̄}`).
  have h1le_β : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (le_of_lt (Real.holderConjugate_iff.mp hpqβ).1)
  have hμ_int : Integrable μ ν :=
    ((MemLpPer.of_top_finite (q := ENNReal.ofReal βBarReal) (by simp)
      htp.μ_linf).toMemLp.mono_exponent h1le_β).integrable le_rfl
  have hm_int : Integrable (fam.m e) ν :=
    ((fam.hmLp e he he1).toMemLp.mono_exponent h1le_β).integrable le_rfl
  have hg_int : Integrable (fun x => μ x - fam.m e x) ν := hμ_int.sub hm_int
  -- AEStronglyMeasurable factors.
  have hμ_aesm : AEStronglyMeasurable μ ν :=
    (MemLpPer.of_top_finite (q := ENNReal.ofReal βBarReal) (by simp)
      htp.μ_linf).aestronglyMeasurable
  have hμ_aem : AEMeasurable μ ν := hμ_aesm.aemeasurable
  have hυ_aesm : AEStronglyMeasurable υ ν :=
    (MemLpPer.of_top_finite (q := ENNReal.ofReal βBarReal) (by simp)
      htp.υ_sob_linf.1).aestronglyMeasurable
  have hDυ_aem : ∀ j, AEMeasurable (Dυ j) ν :=
    fun j => (MemLpPer.of_top_finite (q := ENNReal.ofReal βBarReal)
      (by simp) (htp.Dυ_linf j)).aestronglyMeasurable.aemeasurable
  have hPi_aem : AEMeasurable (fun x => (fun j => Dυ j x)) ν :=
    AEMeasurable.of_eval hDυ_aem
  have hTriple_aem : AEMeasurable
      (fun x => (x, ((fun j => Dυ j x), μ x))) ν :=
    aemeasurable_id.prodMk (hPi_aem.prodMk hμ_aem)
  have hHcomp_aesm : AEStronglyMeasurable
      (fun x => H x (fun j => Dυ j x) (μ x)) ν :=
    aestronglyMeasurable_iff_aemeasurable.mpr
      (hweak.measurable_H.comp_aemeasurable hTriple_aem)
  -- Part 1: `(−υ − H(·,Dυ,μ))·(μ − fam.m e)` is `(bounded) × L¹`.
  have hPart1 : Integrable
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x))
                  * (μ x - fam.m e x)) ν := by
    have hbdd_aesm : AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x)) ν :=
      (hυ_aesm.neg).sub hHcomp_aesm
    have hbdd : ∀ᵐ x ∂ν,
        ‖-(υ x) - H x (fun i => Dυ i x) (μ x)‖ ≤ Bυ + MH := by
      filter_upwards [hBυ, hMH] with x hBυx hMHx
      calc ‖-(υ x) - H x (fun i => Dυ i x) (μ x)‖
          ≤ ‖-(υ x)‖ + ‖H x (fun i => Dυ i x) (μ x)‖ := norm_sub_le _ _
        _ ≤ Bυ + MH := by
            have h1 : ‖-(υ x)‖ ≤ Bυ := by
              rw [norm_neg]; simpa using hBυx
            have h2 : ‖H x (fun i => Dυ i x) (μ x)‖ ≤ MH := by
              rw [Real.norm_eq_abs]; exact hMHx
            linarith
    have := hg_int.bdd_mul hbdd_aesm hbdd
    -- `hg_int.bdd_mul` gives `(μ−m)·(bdd)`; commute to `(bdd)·(μ−m)`.
    refine this.congr ?_
    filter_upwards with x
    ring
  -- Part 2: `V·(μ − fam.m e)` is the `L^{β̄'} × L^{β̄}` Hölder product.
  have hmemβ : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x => μ x - fam.m e x) :=
    MemLp.toMemLpPer
      ((MemLpPer.of_top_finite (q := ENNReal.ofReal βBarReal) (by simp)
        htp.μ_linf).toMemLp.sub (fam.hmLp e he he1).toMemLp)
  have hPart2 : IntegrableOn
      (fun x => V x * (μ x - fam.m e x)) (UnitCube d) :=
    MemLpPer.integrable_mul hpqβ.symm hV hmemβ
  -- Assemble: `A·(μ−m) = (−υ−H)·(μ−m) + V·(μ−m)`.
  have hSum : Integrable
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x)) * (μ x - fam.m e x)
                + V x * (μ x - fam.m e x)) ν :=
    hPart1.add hPart2
  refine hSum.congr ?_
  filter_upwards with x
  ring

end T3

/-! ## `H6WeakGrowthUpstreamPack` — the Phase 6 chain output contract

`H6WeakGrowthUpstreamPack` is the explicit Phase 6 chain *output*
contract for Theorem 3: it packages the genuine outputs of the Phase 6
chain
```
(hmon, hweak, hV)
  → thm:strongAepsi.delta : strong VI (m_ε, u_ε) for A_ε
  → thm:apriori-weak.power.growth : uniform L^{β̄} × W^{1,γ̄} bound
  → eq:compactness.delta : (m_{ε_k}, u_{ε_k}) ⇀ (m, u)
  → paper:observation : H^ε = H, D_pH^ε = D_pH (small ε)
  → eq:existweaksol.delta → def:weak at (m, u)
```
i.e. the limit pair, its regularity, its non-negativity, and the limit
weak-VI.  It is consumed by the live conditional intermediate
`thm_main_weak_power_growth_from_regularized_family`, which the closed
public theorem `thm_main_weak_power_growth_paper` (built INTERNALLY from
the paper hypotheses plus the accepted carriers) delegates to.

This mirrors the closure pattern deployed for Theorem 2
(`Theorems.Congestion.Main.thm_main_congestion_growth_paper`). -/

/--
**Phase 7 upstream-closure bundle for Theorem 3** (paper line 327,
`thm:main-weak.power.growth`).

`H6WeakGrowthUpstreamPack V H DpH betaBar gammaBar` packages the
*output* of the Phase 6 chain
```
(hmon, hweak, hV)
  → thm:strongAepsi.delta
  → thm:apriori-weak.power.growth
  → eq:compactness.delta
  → paper:observation
  → limit_passage_to_weak_VI
```
about the candidate weak-limit pair `(m, u, Du)`. This is the explicit
contract that the Phase 7 drain task
(`infra-P7-sigfix-T3-H6WeakGrowthInputs-drain`) will discharge from
`(hmon, hweak, hV)` end-to-end.

The fields are 1-to-1 with `H6WeakGrowthInputs`, but the framing is
different: `H6WeakGrowthInputs` was the *internal* aggregator-bundle
that the bookkeeping step consumes, whereas
`H6WeakGrowthUpstreamPack` makes explicit that the data records the
*conclusions* of the upstream Phase 6 chain. The producer
`H6WeakGrowthInputs.of_paperHypotheses` decouples the public
paper-facing theorem from the internal bundle.
-/
structure H6WeakGrowthUpstreamPack
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (betaBar gammaBar : ℝ≥0∞) where
  /-- Limit density (output of weak compactness on `(m_{ε_k})`). -/
  m : (Fin d → ℝ) → ℝ
  /-- Limit value function (output of weak compactness on
  `(u_{ε_k})`). -/
  u : (Fin d → ℝ) → ℝ
  /-- Explicit weak-derivative family for `u`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- Regularity `m ∈ L^{β̄}_per` (output of
  `thm:apriori-weak.power.growth` + weak compactness). -/
  mLp : MemLpPer betaBar m
  /-- Regularity `u ∈ W^{1,γ̄}_per` (output of
  `thm:apriori-weak.power.growth` + weak compactness). -/
  uSob : MemSobolevPer gammaBar u
  /-- Non-negativity of `m`, surviving the weak limit
  (`eq:compactness.delta`, paper line 1982). -/
  m_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x
  /-- The weak variational inequality `def:weak` at the limit pair
  (output of the limit passage on `eq:existweaksol.delta`). -/
  hWeakVI : IsWeakSolution V H DpH Du m u
  /-- Weak-derivative tie between `u` and `Du` (`def:weak`). -/
  hDu_weakDeriv : ∀ i, HasWeakDerivPer i u (Du i)
  /-- Each weak-derivative component lives in `L^{γ̄}_per` (`def:weak`). -/
  hDu_memGamma : ∀ i, MemLpPer gammaBar (Du i)

/-! ### Assembly B (partial) — pack from the coherent compactness output + `hWeakVI`

`H6WeakGrowthUpstreamPack.of_weakLimitData` is the *terminal* wiring of
assembly B: it assembles the seven-field `H6WeakGrowthUpstreamPack` from a
single **coherent** weak-compactness output `T3WeakLimitData` (the genuine
A3 extraction `t3WeakCompactness_of_uniformBound`, whose six fields
`m`/`u`/`Du`/`mLp`/`uSob`/`m_nonneg` all live in one fixed
`L^{β̄} × W^{1,γ̄}` along one subsequence) together with the limit-passage
keystone applied to *those same* limits
(`hWeakVI : IsWeakSolution V H DpH ld.Du ld.m ld.u`).

This factoring isolates the remaining analytic content of assembly B. The
six `T3WeakLimitData` fields ARE closed from `(hweak, hV)` + accepted
riders: the chain
`strongAepsi_deltaK0_family_of_selectorData_ae`
→ `T3RegularizedStrongFamily.of_paperHypotheses` + the `_coercive_exp` a-priori engine
→ `t3WeakCompactnessUpstreamPack_of_uniformBound_pinned_full` (A3f)
→ `t3WeakCompactness_of_uniformBound` (A3)
produces a `T3WeakLimitData` with no un-discharged input bundle (the
end-to-end composability of the first two arrows is exhibited by the A2g
witness example above). The SOLE remaining gap is the `hWeakVI` argument:
the keystone `LimitPassage.limit_passage_to_weak_VI_of_paperHypotheses`
consumes per-test-pair analytic certificates — the six Hölder factors
`hg1`/`hμβ`/`hgGrad`/`hDυ`/`hgVal`/`hυ`, the per-test-pair
`WeakConvPairing_universal` certificates `h_weak_m`/`h_weak_Du`/`h_weak_u`
(producible from the A3e `T3BanachLimitResult` via the A3c bridges
`t3WeakCert{M,U,Du}_of_banachWeakConv` once the extraction is shared with
the compactness output), the uniform Gateaux-remainder bound `hbdd`, and
the eventual nonnegativity `hnn` (the A4b `keystone_hnn_of_perEps_VI_and_stabilization`
threaded over all admissible test pairs). The Hölder factors and `hbdd`
are genuine analytic content (growth of `H` under `hweak`, finiteness on
the cube) for which no closed producer from paper hypotheses yet exists;
that is the still-backlog child
`infra-P7-sigfix-T3-drain-A5e2-pack-shrink-hWeakVI`. -/
noncomputable def H6WeakGrowthUpstreamPack.of_weakLimitData
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (_hmon : HypothesisMonotone (d := d) H DpH)
    (_hweak : HypothesisWeakGrowth (d := d) H DpH)
    (_hV : MemLpPer betaBar' V)
    {compPack : T3WeakCompactnessUpstreamPack V H DpH betaBar gammaBar}
    (ld : T3WeakLimitData V H DpH compPack)
    (hWeakVI : IsWeakSolution V H DpH ld.Du ld.m ld.u) :
    H6WeakGrowthUpstreamPack (d := d) V H DpH betaBar gammaBar :=
  { m := ld.m
    u := ld.u
    Du := ld.Du
    mLp := ld.mLp
    uSob := ld.uSob
    m_nonneg := ld.m_nonneg
    hWeakVI := hWeakVI
    hDu_weakDeriv := ld.hDuWeak
    hDu_memGamma := ld.hDu_memGamma }

/-- **Composability witness (anti-sham) for `of_weakLimitData`.** The
genuine A3 compactness output `t3WeakCompactness_of_uniformBound compPack`
feeds the six geometric fields directly; only the limit-passage `hWeakVI`
remains as an explicit input. This certifies that the six pack fields are
discharged from the coherent compactness extraction without re-assuming
any of `m`/`u`/`Du`/`mLp`/`uSob`/`m_nonneg`. -/
example
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hV : MemLpPer betaBar' V)
    (compPack : T3WeakCompactnessUpstreamPack V H DpH betaBar gammaBar)
    (hWeakVI : haveI : Fact (1 ≤ betaBar) := compPack.hβFact
               haveI : Fact (1 ≤ gammaBar) := compPack.hγFact
               IsWeakSolution V H DpH
                 (t3WeakCompactness_of_uniformBound compPack).Du
                 (t3WeakCompactness_of_uniformBound compPack).m
                 (t3WeakCompactness_of_uniformBound compPack).u) :
    H6WeakGrowthUpstreamPack (d := d) V H DpH betaBar gammaBar :=
  haveI : Fact (1 ≤ betaBar) := compPack.hβFact
  haveI : Fact (1 ≤ gammaBar) := compPack.hγFact
  H6WeakGrowthUpstreamPack.of_weakLimitData
    (betaBar' := betaBar') V H DpH hmon hweak hV
    (t3WeakCompactness_of_uniformBound compPack) hWeakVI

/-! ### Assembly B2b — keystone `hnn` threaded over all admissible test pairs

The keystone `LimitPassage.limit_passage_to_weak_VI_of_paperHypotheses`
consumes, per admissible test pair, the eventual nonnegativity `hnn` of
the *stabilised* per-`ε_k` RHS (the three-summand form). The A4b engine
`LimitPassage.keystone_hnn_of_perEps_VI_and_stabilization` produces that
`∀ᶠ k` nonnegativity for ONE test pair from (1) the per-`k` regularised
VI in `mfgOperatorEpsPair` form, (2) the A4 eventual a.e. stabilisation,
(3) the two stabilised-integrand integrabilities.

`keystone_hnn_threaded_of_strongVIfamily` threads that engine over ALL
admissible test pairs, sourcing its inputs from the closed pipeline:

* the per-`k` VI from the A1d-final strong-VI family
  `IsStrongVI_Aepsi` (B2c supplies `hVIfam` along the shared
  extraction's `ext.φ`); specialising it at the test triple discharges the
  defeq seam (`μ - m_n k` is `Pi.sub`, the family yields
  `fun x => μ x - m_n k x` — these are definitionally equal, closed by
  `exact`);
* the A4 stabilisation from `Stabilization.stabilization_uniform_of_DpH_small`
  in its `∃ ε₀, ∀ ε < ε₀` form `hstab`, converted to `∀ᶠ k` here via
  `ε_k → 0` (eventually `0 < ε_k < ε₀`) — this is the `∀ε → ∀ᶠk`
  conversion the A4b body deferred;
* the integrabilities `hIA`/`hIBC` per test pair, exactly as consumed by
  the keystone.

The per-test-pair admissibility regularity certs `hμnn`/`hμLp`/`hυSob`/
`hDυLp`/`hDυweak` are the `IsStrongVI_Aepsi` test-space data.  With the
B2c0 refinement, `IsWeakSolutionTestPair` now carries the full paper
`def:weak` test data (`L^∞ × W^{1,∞}` membership plus `essinf μ > 0`), so
these regularity certs could equally be projected from the predicate; they
are kept as explicit arguments here to mirror the `IsStrongVI_Aepsi`
test-space shape the family was proved against, threaded per pair exactly
as the upstream existence machinery threads its test-pair `MemLpPer`/
`MemSobolevPer` hypotheses. No `0 < m`, no oracle, no new rider. -/
theorem keystone_hnn_threaded_of_strongVIfamily
    {bb gb : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    -- Real-`ε`-indexed regularised Hamiltonian family (at the call site
    -- `Hε := HdeltaK0 hweak`, `DpHε := DpHepsilon hweak qE`).
    {Hε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpHε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {ε : ℕ → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    -- ε-sequence regularising to `0⁺`.
    (hε_pos : ∀ k, 0 < ε k)
    (hε_to0 : Filter.Tendsto ε Filter.atTop (𝓝 0))
    -- (A1d) the per-`k` strong-VI family for the regularised pair
    -- `(Hε (ε k), DpHε (ε k))` at the per-`k` solution triple (along
    -- `ext.φ`).
    (hVIfam : ∀ k,
      IsStrongVI_Aepsi bb gb V (Hε (ε k)) (DpHε (ε k)) γBar (ε k)
        (m_n k) (u_n k) (Du_n k)) :
    ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
      -- per-test-pair admissibility / regularity for `IsStrongVI_Aepsi`.
      (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x) →
      MemLpPer bb μ → MemSobolevPer gb υ →
      (∀ i, MemLpPer gb (Dυ i)) →
      (∀ i, HasWeakDerivPer i υ (Dυ i)) →
      -- (A4) the stabilisation threshold form for this test pair (the
      -- `∃ ε₀, ∀ ε < ε₀` output of `stabilization_uniform_of_DpH_small`).
      (∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           Hε e x (fun i => Dυ i x) (μ x) = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x))) →
      -- the keystone's two stabilised-integrand integrabilities.
      (∀ k, IntegrableOn
        (fun x =>
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x))
        (UnitCube d)) →
      (∀ k, IntegrableOn
        (fun x =>
          μ x * (DpH x (fun i => Dυ i x) (μ x)
                  ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x))
        (UnitCube d)) →
      ∀ᶠ k in Filter.atTop, 0 ≤
        (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                    ⬝ (fun i => Dυ i x - Du_n k i x))
              + (μ x - 1) * (υ x - u_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε k * gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - Du_n k i x) (υ - u_n k) := by
  intro Dυ μ υ _hadm hμnn hμLp hυSob hDυLp hDυweak hstab hIA hIBC
  obtain ⟨ε₀, hε₀_pos, hstabε⟩ := hstab
  -- `ε_k → 0` and `0 < ε₀` give `∀ᶠ k, ε k < ε₀`.
  have hev_lt : ∀ᶠ k in Filter.atTop, ε k < ε₀ :=
    hε_to0.eventually_lt (g := fun _ => ε₀) tendsto_const_nhds hε₀_pos
  -- (A1d) per-`k` VI in `mfgOperatorEpsPair` form, from the strong-VI
  -- family specialised at the test triple (defeq seam discharged here:
  -- `IsStrongVI_Aepsi` yields `fun x => μ x - m_n k x`, defeq to the
  -- `Pi.sub` form `μ - m_n k` the engine consumes).
  have hVIeps : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := Hε (ε k)) (DpH := DpHε (ε k))
            γBar (ε k) Dυ μ υ
            (fun i x => Dυ i x - Du_n k i x)
            (μ - m_n k) (υ - u_n k) := by
    intro k
    exact hVIfam k μ υ Dυ hμnn hμLp hυSob hDυLp hDυweak
  -- (A4) eventual a.e. stabilisation `∀ᶠ k` from the `∃ ε₀, ∀ ε < ε₀` form.
  have hstabH : ∀ᶠ k in Filter.atTop,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Hε (ε k) x (fun i => Dυ i x) (μ x) = H x (fun i => Dυ i x) (μ x) := by
    filter_upwards [hev_lt] with k hk
    exact (hstabε (ε k) (hε_pos k) hk).1
  have hstabDpH : ∀ᶠ k in Filter.atTop,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        DpHε (ε k) x (fun i => Dυ i x) (μ x)
          = DpH x (fun i => Dυ i x) (μ x) := by
    filter_upwards [hev_lt] with k hk
    exact (hstabε (ε k) (hε_pos k) hk).2
  -- Feed the A4b engine, instantiating its abstract per-`k` regularised
  -- Hamiltonian family at `Hε (ε k)`/`DpHε (ε k)`.
  exact LimitPassage.keystone_hnn_of_perEps_VI_and_stabilization
    (V := V) (H := H) (DpH := DpH)
    (Hε := fun k => Hε (ε k)) (DpHε := fun k => DpHε (ε k))
    (γBar := γBar) (ε := ε) (m_n := m_n) (Du_n := Du_n) (u_n := u_n)
    (Dυ := Dυ) (μ := μ) (υ := υ)
    hVIeps hstabH hstabDpH hIA hIBC

/-! ### Assembly C3 (Step 1) — closed full-quantifier `hnn`

`keystone_hnn_full_of_strongVIfamily` is the C3-Step-1 deliverable. It
specialises `keystone_hnn_threaded_of_strongVIfamily` so that the output
matches the `hnn` binder consumed by
`H6WeakGrowthUpstreamPack.of_paperHypotheses` (and
`hWeakVI_of_sharedExtraction`) *verbatim*: the per-test-pair
admissibility/regularity certificates that the threaded engine asks for
(`hμnn`/`hμLp`/`hυSob`/`hDυLp`/`hDυweak`) are **projected internally from
the B2c0 `IsWeakSolutionTestPair` predicate** (the paper `def:weak` test
data: `L^∞ × W^{1,∞}` membership plus `essinf μ > 0`), so the wrapper's
binder carries only the test pair itself plus the accepted analytic riders
`hstab`/`hIA`/`hIBC`.

* `hμnn` (a.e. `0 ≤ μ`) — from `htp.lower` (`essinf μ > 0` in pointwise
  lower-bound form), discharged a.e. by `Filter.Eventually.of_forall`;
* `hμLp : MemLpPer bb μ` — from `htp.μ_linf : MemLpPer ⊤ μ` via
  `MemLpPer.of_top_finite` (`bb ≠ ⊤`);
* `hυSob : MemSobolevPer gb υ` — `⟨MemLpPer.of_top_finite … htp.υ_sob_linf.1,
  htp.υ_sob_linf.2⟩` (the weak-derivative witness is exponent-independent);
* `hDυLp i : MemLpPer gb (Dυ i)` — `MemLpPer.of_top_finite … (htp.Dυ_linf i)`;
* `hDυweak` — `htp.Dυ_weak`.

No `0 < m`, no oracle, no new overstrong rider: the regularity certs come
straight from the paper test-space predicate, and `hstab`/`hIA`/`hIBC` are
the same accepted analytic riders the threaded engine consumes. The output
is the exact `∀ Dυ μ υ, IsWeakSolutionTestPair → ∀ᶠ k, 0 ≤ …` shape of the
`hnn` slot of `of_paperHypotheses`. -/
theorem keystone_hnn_full_of_strongVIfamily
    {bb gb : ℝ≥0∞} (hbb_top : bb ≠ ⊤) (hgb_top : gb ≠ ⊤)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Hε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpHε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {ε : ℕ → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (hε_pos : ∀ k, 0 < ε k)
    (hε_to0 : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hVIfam : ∀ k,
      IsStrongVI_Aepsi bb gb V (Hε (ε k)) (DpHε (ε k)) γBar (ε k)
        (m_n k) (u_n k) (Du_n k)) :
    ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
      -- (A4) the stabilisation threshold form for this test pair.
      (∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           Hε e x (fun i => Dυ i x) (μ x) = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x))) →
      -- the keystone's two stabilised-integrand integrabilities.
      (∀ k, IntegrableOn
        (fun x =>
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x))
        (UnitCube d)) →
      (∀ k, IntegrableOn
        (fun x =>
          μ x * (DpH x (fun i => Dυ i x) (μ x)
                  ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x))
        (UnitCube d)) →
      ∀ᶠ k in Filter.atTop, 0 ≤
        (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                    ⬝ (fun i => Dυ i x - Du_n k i x))
              + (μ x - 1) * (υ x - u_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε k * gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - Du_n k i x) (υ - u_n k) := by
  intro Dυ μ υ htp hstab hIA hIBC
  -- Project the per-test-pair regularity certs from the paper `def:weak`
  -- test-space predicate `IsWeakSolutionTestPair`.
  have hμnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x := by
    obtain ⟨c, hc_pos, hc_le⟩ := htp.lower
    exact Filter.Eventually.of_forall (fun x => le_trans hc_pos.le (hc_le x))
  have hμLp : MemLpPer bb μ := MemLpPer.of_top_finite hbb_top htp.μ_linf
  have hυSob : MemSobolevPer gb υ :=
    ⟨MemLpPer.of_top_finite hgb_top htp.υ_sob_linf.1, htp.υ_sob_linf.2⟩
  have hDυLp : ∀ i, MemLpPer gb (Dυ i) :=
    fun i => MemLpPer.of_top_finite hgb_top (htp.Dυ_linf i)
  have hDυweak : ∀ i, HasWeakDerivPer i υ (Dυ i) := htp.Dυ_weak
  exact keystone_hnn_threaded_of_strongVIfamily
    (bb := bb) (gb := gb) (V := V) (H := H) (DpH := DpH)
    (Hε := Hε) (DpHε := DpHε) (γBar := γBar) (ε := ε)
    (m_n := m_n) (u_n := u_n) (Du_n := Du_n)
    hε_pos hε_to0 hVIfam
    Dυ μ υ htp hμnn hμLp hυSob hDυLp hDυweak hstab hIA hIBC

/-! ### Assembly B2c — shared-extraction terminal wiring + final close

`H6WeakGrowthUpstreamPack.of_sharedExtraction_and_weakVI` is the
option-(a) variant of `of_weakLimitData` from the B2c task note: instead
of a `T3WeakLimitData` over a `compPack`, it reads the six geometric
fields directly off a `T3SharedExtraction` (the SAME `φ`/limits that the
A3c certs and the keystone factors are about). Because the shared
extraction already carries `m`/`u`/`Du`/`mLp`/`uSob`/`m_nonneg`, the pack
is a direct field projection plus the limit-passage `hWeakVI`. -/
noncomputable def H6WeakGrowthUpstreamPack.of_sharedExtraction_and_weakVI
    {betaBar gammaBar : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {mSeq uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (ext : T3SharedExtraction V H DpH betaBar gammaBar mSeq uSeq DuSeq)
    (hWeakVI : IsWeakSolution V H DpH ext.Du ext.m ext.u) :
    H6WeakGrowthUpstreamPack (d := d) V H DpH betaBar gammaBar :=
  { m := ext.m
    u := ext.u
    Du := ext.Du
    mLp := ext.mLp
    uSob := ext.uSob
    m_nonneg := ext.m_nonneg
    hWeakVI := hWeakVI
    hDu_weakDeriv := ext.hDuWeak
    hDu_memGamma := ext.hDu_memGamma }

/-- **Assembly B2c — `hWeakVI` from the shared extraction.**

Feeds the shared weak-limit extraction `ext` (its limits `m`/`u`/`Du`,
the original-sequence `Lᵖ` regularity along `ext.φ`, and the three A3c
`WeakConvPairing_universal` certs) together with the B2c1 six per-test-pair
Hölder/Hamiltonian factors (with `V ∈ L^{β̄'}`, `keystone_sixFactors_of_testPair_VLp`),
the sequence-dependent uniform Gateaux bound `hbdd`, and the threaded
eventual nonnegativity `hnn`, into the keystone
`LimitPassage.limit_passage_to_weak_VI_of_paperHypotheses`, yielding the
weak variational inequality at the shared extraction's limits. -/
theorem hWeakVI_of_sharedExtraction
    {betaBar gammaBar : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {βBar βBar' γBar γBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    (hpqγ : γBar.HolderConjugate γBar')
    (hβBar_eq : ENNReal.ofReal βBar = betaBar)
    (hγBar_eq : ENNReal.ofReal γBar = gammaBar)
    (hβBar'_pos : 0 < βBar')
    (hexp : ENNReal.ofReal γBar' ≤ ENNReal.ofReal βBar)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hreg : RegularityH (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    {mSeq uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (ext : T3SharedExtraction V H DpH betaBar gammaBar mSeq uSeq DuSeq)
    (hmLpSeq : ∀ n, MemLpPer (d := d) (ENNReal.ofReal βBar) (mSeq n))
    (huLpSeq : ∀ n, MemLpPer (d := d) (ENNReal.ofReal γBar) (uSeq n))
    (hDuLpSeq : ∀ n i, MemLpPer (d := d) (ENNReal.ofReal γBar) (DuSeq n i))
    {ε : ℕ → ℝ} (hε_to0 : Filter.Tendsto ε Filter.atTop (𝓝 0))
    {M : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
          ((Fin d → ℝ) → ℝ) → ℝ}
    -- A5c: per-test-pair uniform Gateaux-remainder bound along `ext.φ`.
    (hbdd : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ → ∀ k,
        |gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - DuSeq (ext.φ k) i x) (υ - uSeq (ext.φ k))|
          ≤ M Dυ μ υ)
    -- A1 + A4: eventual nonnegativity of the stabilised per-`ε_k` RHS.
    (hnn : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        ∀ᶠ k in Filter.atTop, 0 ≤
          (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - mSeq (ext.φ k) x)
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                      ⬝ (fun i => Dυ i x - DuSeq (ext.φ k) i x))
                + (μ x - 1) * (υ x - uSeq (ext.φ k) x)
            ∂(volume : Measure (Fin d → ℝ)))
          + ε k * gateauxWpPair γBar Dυ υ
              (fun i x => Dυ i x - DuSeq (ext.φ k) i x)
              (υ - uSeq (ext.φ k))) :
    IsWeakSolution V H DpH ext.Du ext.m ext.u := by
  classical
  haveI : Fact (1 ≤ ENNReal.ofReal βBar') :=
    ⟨ENNReal.one_le_ofReal.mpr hpqβ.symm.lt.le⟩
  haveI : Fact (1 ≤ ENNReal.ofReal γBar') :=
    ⟨ENNReal.one_le_ofReal.mpr hpqγ.symm.lt.le⟩
  have hβBar_top : ENNReal.ofReal βBar ≠ ⊤ := ENNReal.ofReal_ne_top
  -- The six per-test-pair Hölder/Hamiltonian factors (with `V ∈ L^{β̄'}`).
  obtain ⟨hg1, hμβ, hgGrad, hDυ, hgVal, hυ⟩ :=
    LimitPassage.keystone_sixFactors_of_testPair_VLp
      (βBar := βBar) (βBar' := βBar') (γBar := γBar) (γBar' := γBar')
      hβBar'_pos hreg hweak hdiff hexp hβBar_top hV
  -- Regularity of the shared-extraction limits.
  have hm : MemLpPer (d := d) (ENNReal.ofReal βBar) ext.m := by
    rw [hβBar_eq]; exact ext.mLp
  have hu : MemLpPer (d := d) (ENNReal.ofReal γBar) ext.u := by
    rw [hγBar_eq]; exact ext.uSob.1
  have hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (ext.Du i) := by
    intro i
    have hLim : MemLpPer (d := d) gammaBar
        (⇑(ext.DuLimBanach i) : (Fin d → ℝ) → ℝ) :=
      MemLp.toMemLpPer (MeasureTheory.Lp.memLp (ext.DuLimBanach i))
    rw [hγBar_eq]
    exact MemLpPer.congr_ae_unitCube hLim (ext.haeDu i).symm
  -- The three A3c weak-convergence certs about `ext.m/u/Du` along `ext.φ`.
  have hcertM := t3SharedExtraction_weakCertM ext hpqβ hβBar_eq
  have hcertU := t3SharedExtraction_weakCertU ext hpqγ hγBar_eq
  have hcertDu := t3SharedExtraction_weakCertDu ext hpqγ hγBar_eq
  -- Invoke the keystone.
  exact LimitPassage.limit_passage_to_weak_VI_of_paperHypotheses
    (V := V) (H := H) (DpH := DpH)
    (Du := ext.Du) (m := ext.m) (u := ext.u)
    (m_n := fun k => mSeq (ext.φ k))
    (u_n := fun k => uSeq (ext.φ k))
    (Du_n := fun k i => DuSeq (ext.φ k) i)
    (M := M)
    hpqβ hpqγ hε_to0
    hm (fun k => hmLpSeq (ext.φ k))
    hu (fun k => huLpSeq (ext.φ k))
    hDu (fun k i => hDuLpSeq (ext.φ k) i)
    hg1 hμβ hgGrad hDυ hgVal hυ
    (fun _ _ _ _ => hcertM)
    (fun _ _ _ _ i => hcertDu i)
    (fun _ _ _ _ => hcertU)
    hbdd hnn

/-- **Assembly B2c — `H6WeakGrowthUpstreamPack.of_paperHypotheses`.**

Final composition: from the paper hypotheses `(hmon, hweak, hV)` (the
last at the paper exponent `V ∈ L^{β̄'}`) plus the accepted Hamiltonian
rider `hdiff` (`HypothesisHpDifferentiable`), the shared weak-limit
extraction `ext` (output of `t3SharedExtraction_of_uniformBound_pinned`
along the A2g uniform a-priori bound — see the A2g composability witness),
the original-sequence `Lᵖ` regularity, the sequence-uniform Gateaux bound
`hbdd`, and the threaded eventual nonnegativity `hnn` (output of
`keystone_hnn_threaded_of_strongVIfamily`), assemble the seven-field
`H6WeakGrowthUpstreamPack`.

The keystone limit passage runs over the paper-faithful test space
(`IsWeakSolutionTestPair`, `L^∞ × W^{1,∞}` with `essinf μ > 0`, B2c0),
with the six per-test-pair factors produced from the predicate (B2c1,
`keystone_sixFactors_of_testPair_VLp`), the potential entering only the
HJB factor at the paper exponent `β̄'`. **No `H6WeakGrowthInputs` input,
no `0 < m`, no oracle, no new overstrong rider.** -/
noncomputable def H6WeakGrowthUpstreamPack.of_paperHypotheses
    {betaBar gammaBar : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {βBar βBar' γBar γBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    (hpqγ : γBar.HolderConjugate γBar')
    (hβBar_eq : ENNReal.ofReal βBar = betaBar)
    (hγBar_eq : ENNReal.ofReal γBar = gammaBar)
    (hβBar'_pos : 0 < βBar')
    (hexp : ENNReal.ofReal γBar' ≤ ENNReal.ofReal βBar)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    {mSeq uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (ext : T3SharedExtraction V H DpH betaBar gammaBar mSeq uSeq DuSeq)
    (hmLpSeq : ∀ n, MemLpPer (d := d) (ENNReal.ofReal βBar) (mSeq n))
    (huLpSeq : ∀ n, MemLpPer (d := d) (ENNReal.ofReal γBar) (uSeq n))
    (hDuLpSeq : ∀ n i, MemLpPer (d := d) (ENNReal.ofReal γBar) (DuSeq n i))
    {ε : ℕ → ℝ} (hε_to0 : Filter.Tendsto ε Filter.atTop (𝓝 0))
    {M : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
          ((Fin d → ℝ) → ℝ) → ℝ}
    (hbdd : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ → ∀ k,
        |gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - DuSeq (ext.φ k) i x) (υ - uSeq (ext.φ k))|
          ≤ M Dυ μ υ)
    (hnn : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        ∀ᶠ k in Filter.atTop, 0 ≤
          (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - mSeq (ext.φ k) x)
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                      ⬝ (fun i => Dυ i x - DuSeq (ext.φ k) i x))
                + (μ x - 1) * (υ x - uSeq (ext.φ k) x)
            ∂(volume : Measure (Fin d → ℝ)))
          + ε k * gateauxWpPair γBar Dυ υ
              (fun i x => Dυ i x - DuSeq (ext.φ k) i x)
              (υ - uSeq (ext.φ k))) :
    H6WeakGrowthUpstreamPack (d := d) V H DpH betaBar gammaBar :=
  -- `hWeakVI` at the shared extraction's limits, then terminal field
  -- projection.  `hmon` supplies `RegularityH` via `toRegularityH`.
  H6WeakGrowthUpstreamPack.of_sharedExtraction_and_weakVI ext
    (hWeakVI_of_sharedExtraction
      hpqβ hpqγ hβBar_eq hγBar_eq hβBar'_pos hexp
      hmon.toRegularityH hweak hdiff hV ext
      hmLpSeq huLpSeq hDuLpSeq hε_to0 hbdd hnn)

/-! ### Assembly C3 (Step 2) — closed pack producer + finish wrapper

The closed `H6WeakGrowthUpstreamPack` pack producer composes the three C
deliverables INTERNALLY:

* **C1** (`ext` + sequence `Lᵖ` regularity + `ε`/`hε_to0`): the shared
  weak-limit extraction is produced *inline* (the same A2g aggregator
  `apriori_uniform_bound_of_strongVI_family` → `hbound_seq_…` →
  `t3SharedExtraction_of_uniformBound_pinned` chain as
  `t3SharedExtraction_of_paperHypotheses`).  Inlining (rather than calling
  C1 as a black box) keeps the extracted sequence
  `mSeq := fun n => m (εseq n)` **transparent**, which is required to thread
  the per-`k` strong VI through the extraction's `φ`;
* **C2** (`hbdd`): `keystone_hbdd_full_of_uniformControl`, with the uniform
  `Lᵞ` control `Capr` read off the same A2g a-priori bound restricted along
  `φ` (dropping the non-negative `∫|m|^β̄` summand);
* **Step 1** (`hnn`): `keystone_hnn_full_of_strongVIfamily`, with the per-`k`
  strong VI `hVIfam k := hVI (εseq (ext.φ k)) …` from the closed family
  (`hVI`, the C1 family-VI rider), the test-pair regularity discharged
  internally, and the accepted analytic riders `hstab`/`hIA`/`hIBC`.

The result is the seven-field `H6WeakGrowthUpstreamPack` from **only**
`(hmon, hweak, hV)` plus the accepted A2-cluster / A4-stabilisation riders.
No `H6WeakGrowthInputs` input, no `0 < m`, no oracle, no new overstrong
rider. -/
/-! ### D4e: `T3RegularizedSideData` — the regularized-side a-priori bound

`T3RegularizedSideData` packages the single regularized-side deliverable that
the closed `H6WeakGrowthUpstreamPack` pack producer consumes from the ~30
loose binders below: the ε-INDEPENDENT a-priori bound on the regularized
family `(fam.m, fam.u, fam.Du)` (paper `thm:apriori-weak.power.growth`).  All
other downstream uses (`hVI` family, the per-`εseq` `Lᵖ`/`Sobolev`/nonneg
regularity, the analytic `hstab`/`hIA`/`hIBC` riders) read directly off `fam`
and the accepted riders.

`T3RegularizedSideData.of_family` builds this bound from
`fam : T3RegularizedStrongFamily`, the coercive carrier `hUB`, `hV`, the
exponent facts, and the accepted §1b RAW riders — by calling the
exponent-parameterized Young-route engine
`apriori_uniform_bound_of_strongVI_family_coercive_exp_Vlp` (which fixes
`DpHε := DpHepsilonFam hweak qε` internally, so NO `hPow`/`DpHε` binder
appears — D4e GATE #4; and takes only integral V-data, so NO L∞ V-rider — G6c). -/
structure T3RegularizedSideData
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal) where
  /-- The ε-INDEPENDENT a-priori bound on `(fam.m, fam.u, fam.Du)`, on `(0,1]`
  (the regularized family is only ever evaluated along `εseq n ≤ 1`). -/
  apriori_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 →
    (∫ x in UnitCube d, |fam.m ε x| ^ (ENNReal.ofReal βBarReal).toReal
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |fam.u ε x| ^ (ENNReal.ofReal γBarReal).toReal
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d,
            |fam.Du ε i x| ^ (ENNReal.ofReal γBarReal).toReal
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ C

/-- **D4e `T3RegularizedSideData.of_family`.** Builds the regularized-side
a-priori bound from the produced strong-VI family `fam`, the coercive carrier
`hUB`, `hV`, the exponent facts, and the accepted §1b RAW riders.

GATE #4: the signature carries NEITHER `hPow`, `hpowEps`, a loose `DpHε`,
loose `m`/`u`/`Du`/`epsTerms` functions, NOR the `fam`-field regularity
hypotheses (`hmLpFam`/`huSobFam`/`hDu_lpFam`/`hDu_weakFam`/`hmNonnegFam`/`hVI`)
as loose binders — they all come from `fam`.  The remaining binders are the
accepted §1b RAW pass-through sources (`hContRaw`, `hIdentityRaw`,
`epsTerms`+`hEpsNN`, `hRHSbelowRaw`) plus
the `m=0` boundary slice carriers (`hmonBoundary`/`hdiffBoundary`/`sel`).
G6c: the L∞ V-bound cluster is gone — integral V-data is derived from `hV`.
The upper-bound RHS integrability (`hRHSabove`) is now derived internally
(D6f) from `|V| ∈ L¹` + `m^β ∈ L¹`, so `hRHSaboveRaw` is no longer a binder. -/
noncomputable def T3RegularizedSideData.of_family
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal βBar' : ℝ}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    {V : (Fin d → ℝ) → ℝ}
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    -- §1b boundary-slice carriers (genuine `hH0` producer inputs).
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    -- §1b a.e. power-bound carrier for the genuine `Hdelta` composite (the
    -- D6e-3/D6e-4 `hResRaw` producer input).
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    -- Exponent/Hölder facts.
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = gammaBar hweak.α hweak.β)
    (hV : MemLpPer (ENNReal.ofReal βBar') V)
    -- §1b RAW transport-residue riders.
    (epsTerms : ℝ → (Fin d → ℝ) → ℝ)
    (hIdentityRaw : ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ x in UnitCube d, fam.u ε x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                    + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                          (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
            + V x * fam.m ε x
            + epsTerms ε x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hEpsNNRaw : ∀ ε > 0,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms ε x)
    -- Operator-continuity (`hCont`) is now **derived internally** (D6d) from
    -- the closed-cone (`K₀`) hemicontinuity machinery, so `hContRaw` is no
    -- longer a binder. The K0 inputs below feed
    -- `T3.hContRaw_of_T3RegularizedStrongFamily`: the per-`ε` closed-cone
    -- regularity of the canonical `HdeltaK0` carrier and the per-`(ε, S)`
    -- set-segment dominator/measurability bundle (§1b standing-regularity).
    (hγ : 1 < γBarReal)
    (hRegK0 : ∀ ε, 0 < ε → ε ≤ 1 →
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε))
    (g_unreg g_gat :
      (ε : ℝ) → (S : Set (Fin d → ℝ)) → (Fin d → ℝ) → ℝ)
    (hg_unreg_int :
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)),
        IntegrableOn (g_unreg ε S) (UnitCube d))
    (hg_gat_int :
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)),
        IntegrableOn (g_gat ε S) (UnitCube d))
    (hF_unreg_meas :
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fam.Du ε) (fam.Du ε)
              (fun x => fam.m ε x +
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fam.m ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)) x t)
          (volume.restrict (UnitCube d)))
    (hF_unreg_bound :
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fam.Du ε) (fam.Du ε)
              (fun x => fam.m ε x +
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fam.m ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)) x t‖
            ≤ g_unreg ε S x)
    (hF_gat_meas :
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
          (volume.restrict (UnitCube d)))
    (hF_gat_bound :
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t‖
            ≤ g_gat ε S x)
    -- HJB-residual integrability (`hRes`) is now **derived internally**
    -- (D6e-4) from the residual `MemLpPer (β̄')`, so `hResRaw` is no longer a
    -- binder.  The `hC0_le` constant reconciliation below feeds the
    -- `T3.hResRaw_of_T3RegularizedStrongFamily` H-composite producer input.
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    -- §1b RAW RHS integrability pass-through (`hRHSbelow`).  The upper-bound
    -- `hRHSabove` integrability is now **derived internally** (D6f) from the
    -- already-internalised pieces (`|V| ∈ L¹` + `m^β ∈ L¹` + constant), so
    -- `hRHSaboveRaw` is no longer a binder.
    (hRHSbelowRaw : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
        (fun x =>
          fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                    + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                          (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
            + V x * fam.m ε x
            + epsTerms ε x)
        (volume.restrict (UnitCube d))) :
    T3RegularizedSideData hweak qε V fam := by
  classical
  -- Genuine `hH0` from the boundary-slice producer (per-ε on `(0,1]`).
  have hH0 : ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p 0 := fun ε hε hε1ε =>
    t3_hH0_of_bounds hweak qε hUB hmonBoundary hdiffBoundary sel ε hε hε1ε
  -- The integrability cluster from the D4d producers (per-ε on `(0,1]`).
  have hLB_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => fam.m ε x ^ (hweak.β + 1)) (volume.restrict (UnitCube d)) :=
    fun ε hε hε1ε => t3_hLB_int_of_family hweak qε V fam hβBar_eq ε hε hε1ε
  have hMbeta_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => fam.m ε x ^ hweak.β) (volume.restrict (UnitCube d)) :=
    fun ε hε hε1ε => t3_hMbeta_int_of_family hweak qε V fam hβBar_eq ε hε hε1ε
  have hVbetap_int := t3_hVbetap_int_of_family hweak hpqβ hβBar_eq hV
  set Vβp_bound : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' hweak.β
                          ∂(volume : Measure (Fin d → ℝ)) with hVβp_bound_def
  obtain ⟨hVβp_nn, hVβp⟩ := t3_hVβp_constant_of_family hweak hpqβ hβBar_eq hV
  have hRHSabove_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => |V x| + hUB.C0 * (fam.m ε x ^ hweak.β + 1))
      (volume.restrict (UnitCube d)) := fun ε hε hε1ε =>
    t3_hRHSabove_int_of_family_genuine hweak qε fam hUB.C0
      hpqβ hβBar_eq hV ε hε hε1ε
  have hRHSbelow_int := t3_hRHSbelow_int_of_family hweak qε V fam epsTerms hRHSbelowRaw
  -- The §1b pass-throughs (D4b/D4c producers).
  -- Operator-continuity derived internally (D6d) via the closed-cone
  -- (`K₀`) hemicontinuity machinery — no `hContRaw` binder.
  have hCont := T3.hContRaw_of_T3RegularizedStrongFamily
    hweak qε V fam hγ hRegK0 g_unreg g_gat
    hg_unreg_int hg_gat_int hF_unreg_meas hF_unreg_bound
    hF_gat_meas hF_gat_bound
  -- HJB-residual integrability derived internally (D6e-4) from the residual
  -- `MemLpPer (β̄')` via the D4b seam — no `hResRaw` binder.
  have hRes := T3.hResRaw_of_T3RegularizedStrongFamily
    hweak qε V fam hMeas hmonBoundary hdiffBoundary sel hAE hUB hC0_le
    hpqβ hV (by rw [hβBar_eq]; rfl) hγBar_eq
  have hIdentityRaw' := hIdentityRaw_of_family hweak qε V fam epsTerms hIdentityRaw
  have hEpsNN := hEpsNN_of_family epsTerms hEpsNNRaw
  -- Genuinely-derived inputs.
  have hIndicMemLp := t3_hIndicMemLp_of_family (d := d) (βBarReal := βBarReal)
  -- G6c: integral V-data replaces the L∞ rider.  `Vint_bound := ∫|V|`, finite
  -- from `hV`; `hVint` is `le_refl`.  `hVm_int` is the Hölder `|V|·m` pairing;
  -- `hV_meas` is `V`'s a.e.-measurability.  NO `Vbound`/`hVbnd`/`hVint_int`.
  have hVint_int := t3_hVint_int_of_family hweak hpqβ hβBar_eq hV
  set Vint_bound : ℝ := ∫ x in UnitCube d, |V x|
                          ∂(volume : Measure (Fin d → ℝ)) with hVint_bound_def
  have hVint_nn : 0 ≤ Vint_bound := by
    rw [hVint_bound_def]
    exact integral_nonneg (fun x => abs_nonneg _)
  have hVint : ∀ ε : ℝ, ε > 0 →
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound :=
    fun _ _ => le_of_eq hVint_bound_def
  have hVm_int := t3_hVm_int_of_family hweak qε fam hpqβ hV
  have hV_meas := t3_hV_meas_of_family hV
  -- Assemble the ε-INDEPENDENT bound via the Young-route engine (no L∞).
  exact
    { apriori_bound :=
        apriori_uniform_bound_of_strongVI_family_coercive_exp_Vlp
          hweak qε hUB hβBar_eq hγBar_eq
          V fam.Du fam.m fam.u epsTerms Vint_bound Vβp_bound
          hVint_nn hVβp_nn
          fam.hmLp fam.huSob fam.hDuLp fam.hDuWeak fam.hVI fam.hmNonneg
          hIndicMemLp hCont hRes
          hIdentityRaw' hH0 hEpsNN
          hRHSabove_int hLB_int hMbeta_int hRHSbelow_int hVbetap_int
          hVm_int hV_meas hVint hVβp }

/-- **D6h `T3RegularizedSideData.of_paperHypotheses`** — the single producer
that D5 may call to obtain the regularized-side a-priori bound.

This is pure assembly on top of `T3RegularizedSideData.of_family`: each loose
analytic binder of `of_family` is discharged from `fam` plus the gate-allowed
paper carriers.  G6c: the V-bound cluster (`Vbound`/`hVbound_nn`/`hVbnd`) is gone;
all V-data is derived internally from `hV` alone.  Concretely:

* `epsTerms := fun ε => weakEpsTermsEucl γ̄ ε (fam.u ε) (fam.Du ε)` and
  `hEpsNNRaw := weakEpsTermsEucl_nonneg` (D6c3);
* `hIdentityRaw := T3.hIdentityRaw_of_T3RegularizedStrongFamily_fam` (D6c3d) —
  the fully-discharged, `hPow`-free §1b transport identity wrapper;
* `hRegK0 := regularityHK0_Hdelta_of_selector` (per `ε`);
* the closed-cone DCT dominator bundle (`g_unreg`/`g_gat` + the six `hF`
  measurability/bound facts feeding the `hContRaw` field via D6d) from
  `T3.setSegmentDominator_of_T3RegularizedStrongFamily` (D6i-A).

NO `hPow`/`hpowEps`/`DpHε`, NO loose `m`/`u`/`Du`/`epsTerms`/`hIdentityRaw`/
`hContRaw`/`hResRaw`/`hIA`/`hIBC`/`hstab`/`εseq`/`hVI`, NO `*Pack`/`*Inputs`/
`*Oracle`.  The only remaining binders are `fam`, the paper-accepted carriers
(`hmeas`/`hmonBoundary`/`hdiffBoundary`/`sel`/`hAE`/`hUB`/`hC0_le`), the
conjugacy/exponent facts (`hpqβ`/`hpqγ`/`hβBar_eq`/`hγBar_eq`/
`hγ`), and `hV`.  The §1b RHS-below integrability is now derived internally
(D6f2), so there are NO remaining `fam`-dependent integrability pass-throughs. -/
noncomputable def T3RegularizedSideData.of_paperHypotheses
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal βBar' γBar' : ℝ}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    {V : (Fin d → ℝ) → ℝ}
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    -- §1b boundary-slice carriers.
    (hmeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    -- §1b a.e. power-bound carrier for the genuine `Hdelta` composite.
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    -- Exponent/Hölder facts.
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hpqγ : γBar'.HolderConjugate γBarReal)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = gammaBar hweak.α hweak.β)
    (hV : MemLpPer (ENNReal.ofReal βBar') V)
    (hγ : 1 < γBarReal)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    -- §1b RHS-below integrability (`hRHSbelow`) is now **derived internally**
    -- (D6f2) from `fam` + the accepted §1b carriers via Hölder-exponent-balance
    -- (`T3.hRHSbelow_int_of_family_genuine`), so `hRHSbelowRaw` is no longer a
    -- binder.  This closes the LAST §1b `fam`-dependent pass-through.
    -- G6c: the §1b V-bound cluster (`Vbound`/`hVbound_nn`/`hVbnd`) is GONE — the
    -- integral V-data (`∫|V|`, `∫|V|^{β̄'}`, the `|V|·m` Hölder pairing) is
    -- derived internally from `hV : MemLpPer (ofReal βBar') V` alone (the paper's
    -- only hypothesis on `V`), via the Young-route engine.
    :
    T3RegularizedSideData hweak qε V fam := by
  classical
  -- `α ≤ γ̄ = gammaBar α β`: `gammaBar α β = α·(β+1)/β = α + α/β ≥ α`.
  have hαγ : hweak.α ≤ γBarReal := by
    rw [hγBar_eq]
    have hα1 : (1 : ℝ) ≤ hweak.α := hweak.hα.le
    have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
    unfold gammaBar
    rw [le_div_iff₀ hβ0]
    have : hweak.α * hweak.β ≤ hweak.α * (hweak.β + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    linarith
  -- The K0 standing-regularity carrier (per `ε`, on `(0,1]`).
  have hRegK0 : ∀ ε, 0 < ε → ε ≤ 1 →
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) :=
    fun ε hε hε1ε => regularityHK0_Hdelta_of_selector hweak hmonBoundary hdiffBoundary qε sel
      hmeas hAE hε hε1ε
  -- The closed-cone DCT dominator bundle (D6i-A) feeding the `hContRaw` field.
  obtain ⟨g_unreg, g_gat, hg_unreg_int, hg_gat_int,
      hF_unreg_meas, hF_unreg_bound, hF_gat_meas, hF_gat_bound⟩ :=
    T3.setSegmentDominator_of_T3RegularizedStrongFamily
      hweak qε V fam hmeas hmonBoundary hdiffBoundary sel hAE hUB hC0_le
      hβBar_eq hγ hαγ hpqβ hV
  -- The fully-discharged §1b transport identity (D6c3d).
  have hIdentityRaw := T3.hIdentityRaw_of_T3RegularizedStrongFamily_fam
    hweak qε V fam hmeas hmonBoundary hdiffBoundary sel hAE hUB hC0_le
    hβBar_eq hγBar_eq hγ hpqβ hpqγ hV
  -- Assemble via D4e.
  exact T3RegularizedSideData.of_family
    hweak qε hUB fam hmeas hmonBoundary hdiffBoundary sel hAE hpqβ hβBar_eq hγBar_eq hV
    (fun ε => T3.weakEpsTermsEucl γBarReal ε (fam.u ε) (fam.Du ε))
    hIdentityRaw
    (fun ε hε => Filter.Eventually.of_forall (fun x =>
      T3.weakEpsTermsEucl_nonneg γBarReal ε hε.le (fam.u ε) (fam.Du ε) x))
    hγ hRegK0 g_unreg g_gat hg_unreg_int hg_gat_int
    hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
    hC0_le
    (T3.hRHSbelow_int_of_family_genuine hweak qε V fam hmeas hmonBoundary
      hdiffBoundary sel hAE hUB hC0_le hpqβ hβBar_eq hγBar_eq hV hγ)

namespace T3

open scoped Hamiltonian in
/-- **D7 — internal `hstab` producer from the selector family.**

For each admissible test pair `(Dυ, μ, υ)` (`IsWeakSolutionTestPair`,
i.e. `μ ∈ L^∞`, `essinf μ > 0`, `Dυ ∈ L^∞`), the per-test-pair A4
stabilisation of paper Remark `observation` (`eq:existweaksol.delta`,
line 1968) is produced from:

* `hweak : HypothesisWeakGrowth` (paper `onH.weakgrowth`);
* `hDiff : HypothesisHpDifferentiable` (paper line 1670 + `rmk:cxty`);
* the abstract selector family `qε` + its certificate
  `sel : InfConvSelectorFamily` — the accepted carriers per the
  D2c2d/D6h binder lists.

The `L^∞` bound `M` on `D_pH(·, Dυ, μ)` comes from
`dpH_ae_norm_le_of_testPair` (D6g1, off `hweak.DpH_upper` + the test
data). The threshold `ε₀ = ε₀(M+1)` is `eps0 d (M+1)`. For each
`0 < e < ε₀`, a.e. `x`: `μ x > 0`, so the selector's a.e. fields
`sel.H_form`/`sel.DpH_form`/`sel.hSub` apply on the `{0<m}` slice;
combined with `DpH_in_subdiff_zero` (smallness ⇒ `0 ∈ (1/e)∂K(0)`) and
`qSelector_eq_zero_of_DpH_small` (strict-convexity uniqueness), the
minimiser collapses `qε e (x, Dυ x, μ x) = 0`, and the two stabilisation
identities follow from `sel.H_form` (via `K_zero`) and `sel.DpH_form`.

This is the genuine A4 deliverable consumed by
`thm_main_weak_power_growth_from_regularized_family` as its `hstab`
argument — taking NO `hstab`/`εseq`/`*Pack`/`*Inputs`/`*Oracle` binder. -/
theorem hstab_of_selectorFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε) :
    ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
      ∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           HdeltaK0 hweak e x (fun i => Dυ i x) (μ x)
             = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHepsilonFam hweak qε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x)) := by
  intro Dυ μ υ htp
  classical
  -- `essinf μ ≥ c > 0`: the test mass is strictly positive everywhere.
  obtain ⟨c, hc_pos, hc_le⟩ := htp.lower
  -- The `L^∞` bound on `D_pH(·, Dυ, μ)` (D6g1).
  obtain ⟨M, hM_nn, hMbnd⟩ := dpH_ae_norm_le_of_testPair hweak htp
  -- Strictify: `‖D_pH‖ < M + 1` a.e.
  set M' : ℝ := M + 1 with hM'def
  have hM'_nn : 0 ≤ M' := by positivity
  have hMbnd' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖DpH x (fun i => Dυ i x) (μ x)‖ < M' := by
    filter_upwards [hMbnd] with x hx
    exact lt_of_le_of_lt hx (by simp [hM'def])
  refine ⟨Stabilization.eps0 d M', Stabilization.eps0_pos hM'_nn, ?_⟩
  intro e he_pos he_lt
  -- A single a.e. set on which the minimiser collapses to `0`.
  have hcollapse : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      qε e (x, (fun i => Dυ i x), μ x) = 0 := by
    filter_upwards [hMbnd', sel.hSub e he_pos, hDiff.convexOn_H_p,
      hDiff.hasFDerivAt_H_p] with x hxbnd hxSub hxConv hxFD
    have hμx_pos : 0 < μ x := lt_of_lt_of_le hc_pos (hc_le x)
    have hZeroSub : HasSubgradientAt (K hweak) 0
        (e • DpH x (fun i => Dυ i x) (μ x)) :=
      Stabilization.DpH_in_subdiff_zero hweak _ hM'_nn hxbnd he_pos he_lt
    exact qSelector_eq_zero_of_DpH_small hweak hDiff qε he_pos hμx_pos
      (hxConv (μ x) hμx_pos) (fun s => hxFD s (μ x) hμx_pos)
      (hxSub (fun i => Dυ i x) (μ x) hμx_pos) hZeroSub
  refine ⟨?_, ?_⟩
  · -- `Hdelta e = H` a.e.: collapse + `sel.H_form` + `K_zero`.
    filter_upwards [hcollapse, sel.H_form e he_pos] with x hq0 hxHform
    have hμx_pos : 0 < μ x := lt_of_lt_of_le hc_pos (hc_le x)
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hμx_pos]
    rw [hxHform (fun i => Dυ i x) (μ x) hμx_pos, hq0, K_zero hweak, sub_zero]
    simp
  · -- `DpHepsilonFam e = DpH` a.e.: collapse + `sel.DpH_form`.
    filter_upwards [hcollapse, sel.DpH_form e he_pos] with x hq0 hxDpHform
    have hμx_pos : 0 < μ x := lt_of_lt_of_le hc_pos (hc_le x)
    rw [hxDpHform (fun i => Dυ i x) (μ x) hμx_pos, hq0, sub_zero]

end T3

/-- **Theorem 3 — conditional intermediate: weak solution from the produced
regularized family + its a-priori side bound** (paper
`Source/FGU-monotone_revised.tex`, line 327, `thm:main-weak.power.growth`).

This is the genuinely-conditional `(fam, side) → weak solution` limit-passage
intermediate.  It takes the produced canonical `HdeltaK0` strong-VI family
`fam : T3RegularizedStrongFamily` together with its already-built
regularized-side a-priori bound `side : T3RegularizedSideData` (the D6h producer
`T3RegularizedSideData.of_paperHypotheses` constructs `side`), and runs the
C1/C2/C3 weak-limit assembly off `fam`'s fields:

* C1 (`ext`): shared weak-limit extraction at `mSeq := fun n => fam.m (εseq n)`;
* C2 (`hbdd`): uniform Gateaux bound from `side.apriori_bound`;
* C3-Step-1 (`hnn`): `keystone_hnn_full_of_strongVIfamily` threaded with the
  per-test-pair A4 stabilisation `hstab`, with `hIA`/`hIBC` derived internally
  off `fam`.

**Conditional, not closed (on its own).** This intermediate binds the
pre-built regularized family `fam`, its side data `side`, the per-test-pair A4
stabilisation `hstab`, the canonical regularising sequence `εseq`, and the
compactness exponent `Fact`s as loose hypotheses.  It is the internal
limit-passage lemma consumed by the FINAL genuinely-closed public theorem
`thm_main_weak_power_growth_paper` (defined below), which builds
`fam`/`side`/`hstab`/`εseq` **internally** from the paper hypotheses + accepted
carriers and then delegates here.  Cite `thm_main_weak_power_growth_paper` — not
this intermediate — as the closed statement of paper `thm:main-weak.power.growth`. -/
theorem thm_main_weak_power_growth_from_regularized_family
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    -- Paper Theorem 3 hypotheses.
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    {V : (Fin d → ℝ) → ℝ}
    {βBar' γBar' : ℝ}
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hpqγ : γBarReal.HolderConjugate γBar')
    (hβBar'_pos : 0 < βBar')
    (hexp : ENNReal.ofReal γBar' ≤ ENNReal.ofReal βBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    -- The produced regularized family.
    (qε : QEpsFamily d)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    -- Its already-built regularized-side a-priori bound (D6h output).
    (side : T3RegularizedSideData hweak qε V fam)
    -- §1b a.e. power-bound carrier (feeds the internal `hIA`).
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hγ : 1 < γBarReal)
    -- Compactness-side data.
    {bConj gConj : ℝ≥0∞}
    (hβFact : Fact (1 ≤ ENNReal.ofReal βBarReal))
    (hγFact : Fact (1 ≤ ENNReal.ofReal γBarReal))
    [Fact (1 ≤ bConj)] [Fact (1 ≤ gConj)]
    [ENNReal.HolderConjugate (ENNReal.ofReal βBarReal) bConj]
    [ENNReal.HolderConjugate (ENNReal.ofReal γBarReal) gConj]
    (hβ_gt_one : 1 < ENNReal.ofReal βBarReal)
    (hβ_ne_top : ENNReal.ofReal βBarReal ≠ ∞)
    (hγ_gt_one : 1 < ENNReal.ofReal γBarReal)
    (hγ_ne_top : ENNReal.ofReal γBarReal ≠ ∞)
    (εseq : ℕ → ℝ) (hεpos : ∀ n, 0 < εseq n)
    (hε_le1 : ∀ n, εseq n ≤ 1)
    (hεto0 : Filter.Tendsto εseq Filter.atTop (𝓝 0))
    -- A4 stabilisation rider (per admissible test pair) — the one remaining
    -- conditional analytic binder of this intermediate.
    (hstab : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
      ∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           HdeltaK0 hweak e x (fun i => Dυ i x) (μ x)
             = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHepsilonFam hweak qε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x))) :
    ∃ (mLim uLim : (Fin d → ℝ) → ℝ) (DuLim : Fin d → (Fin d → ℝ) → ℝ),
      IsWeakSolution V H DpH DuLim mLim uLim
        ∧ MemLpPer (ENNReal.ofReal βBarReal) mLim
        ∧ MemSobolevPer (ENNReal.ofReal γBarReal) uLim
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 ≤ mLim x)
        ∧ (∀ i, HasWeakDerivPer (d := d) i uLim (DuLim i))
        ∧ (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuLim i)) := by
  classical
  haveI := hβFact
  haveI := hγFact
  set C : ℝ := side.apriori_bound.choose with hC_def
  have hC_nn : 0 ≤ C := side.apriori_bound.choose_spec.1
  have hbound := side.apriori_bound.choose_spec.2
  -- C1: the shared weak-limit extraction.
  have ext := t3SharedExtraction_of_uniformBound_pinned
    (V := V) (H := H) (DpH := DpH)
    (betaBar := ENNReal.ofReal βBarReal) (gammaBar := ENNReal.ofReal γBarReal)
    (betaBar' := bConj) (gammaBar' := gConj)
    hβFact hγFact hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top
    (m := fun n => fam.m (εseq n)) (u := fun n => fam.u (εseq n))
    (Du := fun n i => fam.Du (εseq n) i)
    (fun n => fam.hmLp (εseq n) (hεpos n) (hε_le1 n))
    (fun n => fam.huSob (εseq n) (hεpos n) (hε_le1 n))
    (fun n i => fam.hDuLp (εseq n) (hεpos n) (hε_le1 n) i)
    (fun n i => fam.hDuWeak (εseq n) (hεpos n) (hε_le1 n) i)
    (fun n => fam.hmNonneg (εseq n) (hεpos n) (hε_le1 n)) hC_nn
    (hbound_seq_of_apriori_uniform_bound_of_strongVI_family
      hC_nn hbound εseq hεpos hε_le1)
  set εφ : ℕ → ℝ := fun k => εseq (ext.φ k) with hεφ
  have hεφ_pos : ∀ k, 0 < εφ k := fun k => hεpos (ext.φ k)
  have hεφ_to0 : Filter.Tendsto εφ Filter.atTop (𝓝 0) :=
    hεto0.comp ext.hMono.tendsto_atTop
  have hβReal_nn : (0 : ℝ) ≤ βBarReal := hpqβ.nonneg
  have hγReal_nn : (0 : ℝ) ≤ γBarReal := hpqγ.nonneg
  have hγ_one_le : (1 : ℝ) ≤ γBarReal :=
    le_of_lt (Real.holderConjugate_iff.mp hpqγ).1
  have hbnd_seq := hbound_seq_of_apriori_uniform_bound_of_strongVI_family
    hC_nn hbound εseq hεpos hε_le1
  have htoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγReal_nn
  have hCapr : ∀ k : ℕ,
      (∫ x in UnitCube d, |fam.u (εseq (ext.φ k)) x| ^ γBarReal)
        + (∑ i, ∫ x in UnitCube d, |fam.Du (εseq (ext.φ k)) i x| ^ γBarReal)
          ≤ C := by
    intro k
    have hk := hbnd_seq (ext.φ k)
    have hmnn : 0 ≤ ∫ x in UnitCube d,
        |fam.m (εseq (ext.φ k)) x| ^ (ENNReal.ofReal βBarReal).toReal :=
      MeasureTheory.integral_nonneg
        (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    simp only [htoReal] at hk
    set Im := ∫ x in UnitCube d,
        |fam.m (εseq (ext.φ k)) x| ^ (ENNReal.ofReal βBarReal).toReal with hIm
    set Iu := ∫ x in UnitCube d, |fam.u (εseq (ext.φ k)) x| ^ γBarReal with hIu
    set IDu := ∑ i, ∫ x in UnitCube d, |fam.Du (εseq (ext.φ k)) i x| ^ γBarReal
      with hIDu
    calc Iu + IDu ≤ Im + (Iu + IDu) := by linarith [hmnn]
      _ = (Im + Iu) + IDu := by ring
      _ ≤ C := hk
  have hbddEx := LimitPassage.keystone_hbdd_full_of_uniformControl
    (γBar := γBarReal) hγ_one_le
    (uSeq := fun n => fam.u (εseq n)) (DuSeq := fun n i => fam.Du (εseq n) i)
    (φ := ext.φ)
    (fun k => (fam.huSob (εseq (ext.φ k)) (hεpos (ext.φ k)) (hε_le1 (ext.φ k))).1)
    (fun k i => fam.hDuLp (εseq (ext.φ k)) (hεpos (ext.φ k)) (hε_le1 (ext.φ k)) i)
    C hC_nn hCapr
  set M := hbddEx.choose with hM_def
  have hbdd := hbddEx.choose_spec
  have hnn := keystone_hnn_full_of_strongVIfamily
    (bb := ENNReal.ofReal βBarReal) (gb := ENNReal.ofReal γBarReal)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (V := V) (H := H) (DpH := DpH)
    (Hε := fun e => HdeltaK0 hweak e) (DpHε := fun e => DpHepsilonFam hweak qε e)
    (γBar := γBarReal) (ε := εφ)
    (m_n := fun k => fam.m (εseq (ext.φ k)))
    (u_n := fun k => fam.u (εseq (ext.φ k)))
    (Du_n := fun k i => fam.Du (εseq (ext.φ k)) i)
    hεφ_pos hεφ_to0
    (fun k => fam.hVI (εseq (ext.φ k)) (hεpos (ext.φ k)) (hε_le1 (ext.φ k)))
  have pack := H6WeakGrowthUpstreamPack.of_paperHypotheses
    (betaBar := ENNReal.ofReal βBarReal) (gammaBar := ENNReal.ofReal γBarReal)
    (βBar := βBarReal) (βBar' := βBar') (γBar := γBarReal) (γBar' := γBar')
    hpqβ hpqγ rfl rfl hβBar'_pos hexp
    hmon hweak hdiff hV
    (mSeq := fun n => fam.m (εseq n)) (uSeq := fun n => fam.u (εseq n))
    (DuSeq := fun n i => fam.Du (εseq n) i)
    ext (fun n => fam.hmLp (εseq n) (hεpos n) (hε_le1 n))
    (fun n => (fam.huSob (εseq n) (hεpos n) (hε_le1 n)).1)
    (fun n i => fam.hDuLp (εseq n) (hεpos n) (hε_le1 n) i)
    (ε := εφ) hεφ_to0
    (M := M) hbdd
    (by
      intro Dυ μ υ htp
      exact hnn Dυ μ υ htp (hstab Dυ μ υ htp)
        (fun k => T3.hIA_of_T3RegularizedStrongFamily hpqβ hV hweak hAE fam
          Dυ μ υ htp (hstab Dυ μ υ htp) (εseq (ext.φ k)) (hεpos (ext.φ k))
          (hε_le1 (ext.φ k)))
        (fun k => T3.hIBC_of_T3RegularizedStrongFamily hγ.le hweak fam
          Dυ μ υ htp (εseq (ext.φ k)) (hεpos (ext.φ k)) (hε_le1 (ext.φ k))))
  exact ⟨pack.m, pack.u, pack.Du, pack.hWeakVI, pack.mLp, pack.uSob,
          pack.m_nonneg, pack.hDu_weakDeriv, pack.hDu_memGamma⟩

/-- Weak-growth existence using the implementation's representative bundles,
without a boundary premise on the original Hamiltonian.

The regularized Hamiltonians are evaluated through `HdeltaK0`, whose zero-mass
values are their finite right-hand limits. The original Hamiltonian enters the
weak variational inequality only at strictly positive test masses. The
remaining derivative/measurability representation fields are eliminated by
`thm_main_weak_power_growth_faithful` in `PaperMain.lean`.

All integrability exponents, nonnegativity, and the explicit weak-gradient
conclusions are retained. -/
theorem thm_main_weak_power_growth_no_boundary
    [AxisMixMeasureHypothesis]
    [hdFact : Fact (0 < d)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    -- Paper Theorem 3 hypotheses.
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    -- Joint measurability of the selected implementation representatives.
    (hmeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    -- `V ∈ L^{β̄'}_per` at the conjugate exponent `β̄' = (β+1)/β`.
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      IsWeakSolution V H DpH Du m u
        ∧ MemLpPer (ENNReal.ofReal (hweak.β + 1)) m
        ∧ MemSobolevPer (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, MemLpPer (d := d)
              (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (Du i)) := by
  classical
  -- (0) Build the AE-route inf-conv selector family `(qε, sel)` internally from
  -- the paper hypotheses `(hmon, hweak, hdiff)` and the boundary measurability
  -- rider `hmeas` (paper `lem:inf-conv.selection`; Properties.lean
  -- `infConvSelectorFamily_of_weakGrowth`).  Formerly explicit binders.
  obtain ⟨qε, sel⟩ :=
    infConvSelectorFamily_of_weakGrowth (H := H) (DpH := DpH)
      hmon hweak hdiff hmeas
  -- Discharge the pure arithmetic exponent/conjugacy facts internally from the
  -- paper hypotheses `hweak.hα : 1 < α`, `hweak.hβ : 0 < β`, and the dimension
  -- instance `[Fact (0 < d)]`.  These were formerly explicit binders; they are
  -- all standard Hölder-conjugacy arithmetic at the paper exponents `eq:gamma`
  -- (`β̄ = β+1`, `γ̄ = α(β+1)/β`), reusing the
  -- `SimplePowerExponentFacts` helper layer.
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hdFact.out
  have hExp : SimplePowerExponentFacts
      (hweak.α * (hweak.β + 1) / hweak.β)
      (ENNReal.ofReal (hweak.β + 1))
      (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
      (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) :=
    SimplePowerExponentFacts.standardPaper hweak.hα hweak.hβ
  have hβ : (hweak.β + 1).HolderConjugate ((hweak.β + 1) / hweak.β) :=
    SimplePowerExponentFacts.paper_holderConjugate_betaBar hweak.hβ
  have hγ : (hweak.α * (hweak.β + 1) / hweak.β).HolderConjugate
      ((hweak.α * (hweak.β + 1) / hweak.β)
        / (hweak.α * (hweak.β + 1) / hweak.β - 1)) :=
    SimplePowerExponentFacts.paper_holderConjugate_gammaBar hweak.hα hweak.hβ
  have hβconj : ((hweak.β + 1) / hweak.β).HolderConjugate (hweak.β + 1) := hβ.symm
  have hγconj : ((hweak.α * (hweak.β + 1) / hweak.β)
      / (hweak.α * (hweak.β + 1) / hweak.β - 1)).HolderConjugate
      (hweak.α * (hweak.β + 1) / hweak.β) := hγ.symm
  have hβTop : ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hβBarTop : ENNReal.ofReal (hweak.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ_gt1 : 1 < hweak.β + 1 := by linarith [hweak.hβ]
  have hγ_gt1 : 1 < hweak.α * (hweak.β + 1) / hweak.β := hγ.lt
  -- Discharge the p-Laplacian power-map monotonicity facts internally from
  -- `γ̄ > 1` (paper §2 / Appendix: standard convexity of `t ↦ |t|^{γ̄-2}·t`).
  -- These were formerly explicit binders; both are
  -- `SimplePower.Banach.paperSection8_h*Mono_of_gamma` instantiated at the
  -- pinned exponent `γ̄ = α(β+1)/β`.
  have hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (StationaryMFG.Solutions.MFG.absPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) t * t
              - StationaryMFG.Solutions.MFG.absPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) s * s)
              * (t - s) :=
    SimplePower.Banach.paperSection8_hScalarMono_of_gamma hγ_gt1
  have hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ dotProduct
              (StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) v • v
              - StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) w • w)
              (v - w) :=
    SimplePower.Banach.paperSection8_hVecMono_of_gamma (d := d) hγ_gt1
  -- `γ̄' ≤ β̄`: with `γ̄ > 1` this is `γ̄ ≤ (β+1)(γ̄−1)`, i.e. `γ̄·β ≥ β+1`,
  -- i.e. `α(β+1) ≥ β+1`, i.e. `α ≥ 1`.  True since `α > 1`.
  have hγ'_le_β : ENNReal.ofReal ((hweak.α * (hweak.β + 1) / hweak.β)
        / (hweak.α * (hweak.β + 1) / hweak.β - 1))
      ≤ ENNReal.ofReal (hweak.β + 1) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hα0 : 0 < hweak.α := lt_trans zero_lt_one hweak.hα
    have hβpos : 0 < hweak.β := hweak.hβ
    have hβ1 : (0 : ℝ) < hweak.β + 1 := by linarith
    set γ : ℝ := hweak.α * (hweak.β + 1) / hweak.β with hγ_def
    have hγpos : 0 < γ := div_pos (mul_pos hα0 hβ1) hβpos
    have hγgt1 : 1 < γ := hγ_gt1
    have hγm1 : 0 < γ - 1 := by linarith
    -- `γ / (γ - 1) ≤ β + 1 ⟺ γ ≤ (β+1)(γ-1) ⟺ (β+1) ≤ γ·β`.
    rw [div_le_iff₀ hγm1]
    -- Goal: γ ≤ (β + 1) * (γ - 1).
    -- `γ · β = α(β+1)/β · β = α(β+1) ≥ (β+1)`.
    have hγβ : γ * hweak.β = hweak.α * (hweak.β + 1) := by
      rw [hγ_def]; field_simp
    have hkey : hweak.β + 1 ≤ γ * hweak.β := by
      rw [hγβ]
      have : (1 : ℝ) * (hweak.β + 1) ≤ hweak.α * (hweak.β + 1) :=
        mul_le_mul_of_nonneg_right (le_of_lt hweak.hα) (le_of_lt hβ1)
      linarith
    nlinarith [hkey, hβpos, hγm1]
  -- Abbreviations for the pinned paper exponents.
  set βBarReal : ℝ := hweak.β + 1 with hβBar_def
  set γBarReal : ℝ := hweak.α * (hweak.β + 1) / hweak.β with hγBar_def
  set βBar' : ℝ := (hweak.β + 1) / hweak.β with hβBar'_def
  set γBar' : ℝ := γBarReal / (γBarReal - 1) with hγBar'_def
  -- Positivity of the conjugate exponent `β̄' = (β+1)/β`.
  have hβ'_pos : 0 < βBar' := by
    rw [hβBar'_def]
    exact div_pos (by linarith [hweak.hβ]) hweak.hβ
  -- `1 < γ̄`.
  have hγReal_gt1 : 1 < γBarReal := hγ_gt1
  -- The ENNReal `HolderConjugate`/`Fact` instances at the paper exponents
  -- (Coercivity.lean pattern).
  haveI hHCβ : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBar') :=
    Real.HolderConjugate.ennrealOfReal (by rw [hβBar_def, hβBar'_def]; exact hβ)
  haveI hHCγ : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBar') :=
    Real.HolderConjugate.ennrealOfReal (by rw [hγBar_def, hγBar'_def]; exact hγ)
  have hβ' : βBarReal.HolderConjugate βBar' := by
    rw [hβBar_def, hβBar'_def]; exact hβ
  have hγ'hc : γBarReal.HolderConjugate γBar' := by
    rw [hγBar_def, hγBar'_def]; exact hγ
  haveI hFβ' : Fact (1 ≤ ENNReal.ofReal βBar') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal
        (le_of_lt (Real.holderConjugate_iff.mp hβ'.symm).1)⟩
  haveI hFγ' : Fact (1 ≤ ENNReal.ofReal γBar') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal
        (le_of_lt (Real.holderConjugate_iff.mp hγ'hc.symm).1)⟩
  haveI hFβ : Fact (1 ≤ ENNReal.ofReal βBarReal) :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal (by rw [hβBar_def]; linarith [hβ_gt1])⟩
  haveI hFγ : Fact (1 ≤ ENNReal.ofReal γBarReal) :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal (by rw [hγBar_def]; linarith [hγ_gt1])⟩
  -- `1 < ofReal _` (strict) for both pinned exponents.
  have hβ_ennreal_gt : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr
      (by rw [hβBar_def]; linarith [hβ_gt1])
  have hγ_ennreal_gt : (1 : ℝ≥0∞) < ENNReal.ofReal γBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr
      (by rw [hγBar_def]; linarith [hγ_gt1])
  -- (0a) Internalize the AE-route selector/bound carriers and the
  -- existence-layer analytic-regularity carriers via the G3/G4/G4b producers,
  -- all generic in the just-built `(qε, sel)`.  Formerly explicit binders.
  --   `hCx` — convex-at-zero rider for `H^ε` (paper `lem:H.delta.monotone`).
  --   `hGrad` — `‖D_pH^ε‖`-bound (paper `eq:inf-conv.diff-relation1`).
  have hCx : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.Hdelta hweak ε x p m
              - (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m) ⬝ p
            ≤ StationaryMFG.InfimalConvolution.Hdelta hweak ε x 0 m :=
    fun ε hε hε1 => T3.hCx_of_selector hweak hdiff qε sel ε hε hε1
  have hGrad : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
            ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
                * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1)) :=
    fun ε hε hε1 => T3.hGrad_of_selector hweak qε sel ε hε hε1
  -- `hUB` — uniform Hδ lower/Lagrangian bounds (`hUB.C0 = 2^α(C+1)`).  Kept as a
  -- `let` so its definitional unfolding to `hdeltaUniformBounds_of_selector …`
  -- survives — `hC0_le_of_uniformBounds` states its conclusion about that term.
  set hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε :=
    StationaryMFG.InfimalConvolution.hdeltaUniformBounds_of_selector
      hweak qε sel hCx with hUB_def
  -- `hAE` — the AE power-growth data (paper `eq:H-epsilon.upper.uniform`).
  have hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε :=
    StationaryMFG.InfimalConvolution.hdeltaAEPowerEpsData_of_selector
      hweak qε sel hCx hGrad
  -- `hC0_le` — constant reconciliation `hUB.C0 ≤ CdeltaEps`.
  have hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε := by
    intro ε hε
    rw [hUB_def]
    exact T3.hC0_le_of_uniformBounds hweak qε sel hCx ε hε
  -- The four ε-family analytic measurability riders (G4 producers).
  have hF_HJB_meas_Pos := T3.hF_HJB_meas_Pos_of_selector
    (βBarReal := βBarReal) (γBarReal := γBarReal) (βBarReal' := βBar')
    V hweak qε sel hmeas hV
  have hF_HJB_meas_K0 := T3.hF_HJB_meas_K0_of_selector
    (βBarReal := βBarReal) (γBarReal := γBarReal) (βBarReal' := βBar')
    V hweak qε sel hmeas hmon hdiff hV
  have hF_flux_meas := T3.hF_flux_meas_of_selector
    (βBarReal := βBarReal) (γBarReal := γBarReal)
    hweak qε sel hmeas
  have hF_gat_meas := T3.hF_gat_meas_of_selector
    (βBarReal := βBarReal) (γBarReal := γBarReal)
    hweak qε sel
  -- `aux10` — the constant-test-triple `(0,1,0)` `MFGOpEpsAuxHyps` on raw `Hδ`
  -- (G4b producer; the conjugacy facts `hβ'`/`hγ'hc`/`hβTop` are reused).
  have aux10 := fun ε (hε : 0 < ε) (hε1 : ε ≤ 1) =>
    T3.mfgOpEpsAuxHyps_const01_Hdelta_of_selector
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (βBarReal' := βBar') (γBarReal' := γBar')
      V hweak qε sel hAE hmeas hV hβ' hγ'hc hβTop ε hε hε1
  -- (1) Build the regularized strong-VI family from paper hypotheses.  The
  -- producer returns the family on the SAME `qε` it was fed, so `sel`/`hAE`/`hUB`
  -- stay aligned to the family index.
  have fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal :=
    T3RegularizedStrongFamily.of_paperHypotheses
      V hweak hmon hmeas hmon hdiff qε sel hAE hUB hV hExp hβ hγ
      hβTop hβBarTop hβ_gt1 hγ_gt1 hγ'_le_β hβconj hγconj hd_pos
      hScalarMono hVecMono
      (fun ε hε _ => hC0_le ε hε)
      hF_HJB_meas_Pos hF_HJB_meas_K0 hF_flux_meas hF_gat_meas aux10
  -- (2) Build its regularized-side a-priori bound.
  let side := T3RegularizedSideData.of_paperHypotheses
    hweak qε hUB fam hmeas hmon hdiff sel hAE hβ hγconj
    hβBar_def.symm hγBar_def.symm hV hγReal_gt1
    (fun ε hε => hC0_le ε hε)
  -- (3) The per-test-pair A4 stabilisation.
  have hstab := T3.hstab_of_selectorFamily hweak hdiff qε sel
  -- (4)+(5) Delegate to the conditional intermediate with `ε_n := 1/(n+1)`.
  exact thm_main_weak_power_growth_from_regularized_family
    (βBarReal := βBarReal) (γBarReal := γBarReal)
    hmon hweak hdiff
    (V := V) (βBar' := βBar') (γBar' := γBar')
    hβ hγ hβ'_pos hγ'_le_β hV qε fam side hAE hγReal_gt1
    (bConj := ENNReal.ofReal βBar') (gConj := ENNReal.ofReal γBar')
    hFβ hFγ hβ_ennreal_gt hβBarTop hγ_ennreal_gt hβTop
    Stabilization.T3.canonicalEpsSeq Stabilization.T3.canonicalEpsSeq_pos
    Stabilization.T3.canonicalEpsSeq_le_one Stabilization.T3.canonicalEpsSeq_tendsto
    hstab

/-- Compatibility wrapper for the previous finite-boundary entry point.
The boundary-extension argument is no longer used: regularized Hamiltonians
receive their own canonical boundary values. -/
theorem thm_main_weak_power_growth_paper
    [AxisMixMeasureHypothesis]
    [hdFact : Fact (0 < d)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    -- Paper Theorem 3 hypotheses.
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    -- Joint measurability of the selected implementation representatives.
    (hmeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hH0 : Hamiltonian.HypothesisHZeroExtension (d := d) H)
    -- `V ∈ L^{β̄'}_per` at the conjugate exponent `β̄' = (β+1)/β`.
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      IsWeakSolution V H DpH Du m u
        ∧ MemLpPer (ENNReal.ofReal (hweak.β + 1)) m
        ∧ MemSobolevPer (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, MemLpPer (d := d)
              (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (Du i)) := by
  exact thm_main_weak_power_growth_no_boundary V hmon hweak hdiff hmeas hV

/-! ### Non-vacuity witness for `thm_main_weak_power_growth_paper`

This section instantiates EVERY binder of the public Theorem 3
(`thm_main_weak_power_growth_paper`) at a concrete admissible model and
obtains its conclusion.  Its sole purpose is to **permanently guard against
vacuous-binder regressions**: a non-vacuity witness fails to build the moment
any binder of the public theorem becomes unsatisfiable over its domain.

The motivating incident is the `hWeakDerivK0` binder removed in G7c-2 (commit
`fd90baa`): that binder was *unsatisfiable* (no `HasWeakDerivPer` certificate
exists for `(0, 0, const 1) ∈ K0_Aepsi`), so the theorem was vacuously true
and its "existence" conclusion carried no content.  After G7 made the
weak-derivative tie structural (refined cone `K0_Aepsi_W`), this witness
certifies that the remaining hypothesis set IS jointly satisfiable.

**Model** (`d = 1`, paper weak-growth example at `α = 2, β = 1, C = 1`):

* `H x p m := ‖p‖² − m`     (paper `H(x,p,m) = ‖p‖^α − m^β`),
* `DpH x p m := 2 • p`      (the genuine `p`-gradient of `‖p‖²`),
* `V := 0`.

The dimension `d = 1` is essential: on `Fin 1 → ℝ` the sup-norm equals `|·|`
(= the Euclidean norm), so `‖p‖² = (p 0)²` IS Fréchet-differentiable in `p`.
For `d ≥ 2` the sup-norm has corners and `‖·‖²` is not differentiable there —
exactly the obstruction recorded at `Hamiltonian/Differentiability.lean:213`. -/
namespace T3Nonvacuity

/-- For `d = 1`, the sup-norm of `q : Fin 1 → ℝ` equals `|q 0|`. -/
private lemma norm_fin_one (q : Fin 1 → ℝ) : ‖q‖ = |q 0| := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro i; fin_cases i; simp [Real.norm_eq_abs]
  · have := norm_le_pi_norm q 0; rwa [Real.norm_eq_abs] at this

/-- For `d = 1`, `‖q‖^(2:ℝ) = (q 0)^2`. -/
private lemma norm_sq_fin_one (q : Fin 1 → ℝ) : (‖q‖ : ℝ) ^ (2 : ℝ) = (q 0) ^ 2 := by
  rw [norm_fin_one, Real.rpow_two, sq_abs]

/-- The concrete model Hamiltonian `H(x, p, m) = ‖p‖² − m`. -/
def palomar_Main_nvH : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ :=
  fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)

/-- The concrete model gradient `D_pH(x, p, m) = 2 • p`. -/
def palomar_Main_nvDpH : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ) :=
  fun _ p _ => (2 : ℝ) • p

/-- `HypothesisMonotone` for the concrete model: the Lasry–Lions inequality
collapses to `(m₁−m₂)² + (m₁+m₂)(p₁ 0 − p₂ 0)² ≥ 0`, and the FTC slice is a
direct affine-gradient integral computation. -/
private lemma nvMonotone : HypothesisMonotone (d := 1) palomar_Main_nvH palomar_Main_nvDpH where
  periodic_H := by intro p m; exact IsPeriodic.const _
  periodic_DpH := by intro p _; exact IsPeriodic.const _
  measurable_H := by
    have hcont : Continuous
        (fun (xpm : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ) =>
          (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ) - xpm.2.2 ^ (1 : ℝ)) := by
      have h1 : Continuous
          (fun (xpm : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ) => (‖xpm.2.1‖ : ℝ) ^ (2 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
          ((continuous_norm).comp (continuous_fst.comp continuous_snd))
      have h2 : Continuous
          (fun (xpm : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ) => xpm.2.2 ^ (1 : ℝ)) :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
          (continuous_snd.comp continuous_snd)
      exact h1.sub h2
    exact hcont.measurable
  measurable_DpH := by
    have hcont : Continuous
        (fun (xpm : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ) => ((2 : ℝ) • xpm.2.1 : Fin 1 → ℝ)) :=
      by fun_prop
    exact hcont.measurable
  continuous_H_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    have h1 : Continuous (fun (pm : (Fin 1 → ℝ) × ℝ) => (‖pm.1‖ : ℝ) ^ (2 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
        ((continuous_norm).comp continuous_fst)
    have h2 : Continuous (fun (pm : (Fin 1 → ℝ) × ℝ) => pm.2 ^ (1 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp continuous_snd
    exact (h1.sub h2).continuousOn
  continuous_DpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    unfold palomar_Main_nvDpH
    fun_prop
  monotone := by
    refine Filter.Eventually.of_forall ?_
    intro _ p₁ m₁ p₂ m₂ h1 h2
    show 0 ≤ (-((‖p₁‖ : ℝ) ^ (2:ℝ) - m₁ ^ (1:ℝ)) + ((‖p₂‖ : ℝ) ^ (2:ℝ) - m₂ ^ (1:ℝ)))
            * (m₁ - m₂)
          + (m₁ • ((2:ℝ) • p₁) - m₂ • ((2:ℝ) • p₂)) ⬝ (p₁ - p₂)
    rw [norm_sq_fin_one, norm_sq_fin_one, Real.rpow_one, Real.rpow_one]
    unfold dotProduct
    rw [Fin.sum_univ_one]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [sq_nonneg (m₁ - m₂), sq_nonneg (p₁ 0 - p₂ 0), mul_pos h1 h2,
      mul_nonneg h1.le (sq_nonneg (p₁ 0 - p₂ 0)),
      mul_nonneg h2.le (sq_nonneg (p₁ 0 - p₂ 0))]
  lagr_ftc_slice := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    show ((2:ℝ) • p) ⬝ p
        - (((‖p‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ)) - ((‖(0:Fin 1 → ℝ)‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ)))
        = ∫ t in (0:ℝ)..1, (((2:ℝ) • p) - ((2:ℝ) • (t • p))) ⬝ p
    have hintegrand : ∀ t : ℝ,
        (((2:ℝ) • p) - ((2:ℝ) • (t • p))) ⬝ p = (2 - 2*t) * (p 0) ^ 2 := by
      intro t
      unfold dotProduct
      rw [Fin.sum_univ_one]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [intervalIntegral.integral_congr (g := fun t => (2 - 2*t) * (p 0) ^ 2)
          (fun t _ => hintegrand t)]
    rw [norm_sq_fin_one]
    simp only [norm_zero, Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0)]
    have hlhs : ((2:ℝ) • p) ⬝ p = 2 * (p 0) ^ 2 := by
      unfold dotProduct; rw [Fin.sum_univ_one]
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hlhs, intervalIntegral.integral_mul_const]
    have hint : (∫ t in (0:ℝ)..1, (2 - 2*t)) = 1 := by
      have hsub : (∫ t in (0:ℝ)..1, ((2:ℝ) - 2*t))
          = (∫ t in (0:ℝ)..1, (2:ℝ)) - ∫ t in (0:ℝ)..1, 2*t := by
        rw [intervalIntegral.integral_sub]
        · exact intervalIntegrable_const
        · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
      have hc : (∫ t in (0:ℝ)..1, (2:ℝ)) = 2 := by
        rw [intervalIntegral.integral_const]; norm_num
      rw [hsub, hc, intervalIntegral.integral_const_mul, integral_id]; norm_num
    rw [hint]; ring

/-- `HypothesisWeakGrowth` for the concrete model at `C = 1, α = 2, β = 1`,
with the trivial constant bound function `f ≡ 1`. -/
def palomar_Main_nvWeakGrowth : HypothesisWeakGrowth (d := 1) palomar_Main_nvH palomar_Main_nvDpH where
  toRegularityH := by exact nvMonotone.toRegularityH
  C := 1
  α := 2
  β := 1
  hC := by norm_num
  hα := by norm_num
  hβ := by norm_num
  f := fun p _ => 2 * ‖p‖
  hf_continuous :=
    (continuous_const.mul (continuous_norm.comp continuous_fst)).continuousOn
  upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ m _
    show (‖(0 : Fin 1 → ℝ)‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ) ≤ -(m ^ (1 : ℝ)) / 1 + 1
    rw [norm_zero, Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0), Real.rpow_one]
    linarith
  DpH_upper := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    show ‖((2:ℝ) • p : Fin 1 → ℝ)‖ ≤ 2 * ‖p‖
    rw [norm_smul]
    simp
  lower := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    show (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)
        ≥ (‖p‖ : ℝ) ^ (2 : ℝ) / 1 - 1 * (m ^ (1 : ℝ) + 1)
    have hmrpow : m ^ (1 : ℝ) = m := Real.rpow_one m
    rw [hmrpow]; nlinarith [Real.rpow_nonneg (norm_nonneg p) (2:ℝ)]

/-- `HypothesisHpDifferentiable` for the concrete model.  Differentiability is
genuine here because `d = 1` makes the sup-norm equal `|·|`, so
`‖q‖² = (q 0)²` is Fréchet-differentiable with derivative `dotCLMHam (2 • p)`. -/
private lemma nvDifferentiable : HypothesisHpDifferentiable (d := 1) palomar_Main_nvH palomar_Main_nvDpH where
  hasFDerivAt_H_p := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    show HasFDerivAt (fun q : Fin 1 → ℝ => (‖q‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ))
          (dotCLMHam ((2:ℝ) • p)) p
    have hfun : (fun q : Fin 1 → ℝ => (‖q‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ))
        = (fun q : Fin 1 → ℝ => ((fun t : ℝ => t ^ 2) ∘ (fun q : Fin 1 → ℝ => q 0)) q
            - m ^ (1:ℝ)) := by
      funext q; simp only [Function.comp]; rw [norm_sq_fin_one]
    rw [hfun]
    have hproj : HasFDerivAt (fun q : Fin 1 → ℝ => q 0)
        (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) p :=
      (ContinuousLinearMap.proj (0 : Fin 1) (R := ℝ) (φ := fun _ => ℝ)).hasFDerivAt
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (p 0))
        ((fun q : Fin 1 → ℝ => q 0) p) := by
      simpa using (hasDerivAt_pow 2 (p 0))
    have hcomp := hsq.comp_hasFDerivAt p hproj
    have hconst : HasFDerivAt (fun _ : Fin 1 → ℝ => m ^ (1:ℝ))
        (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) p := hasFDerivAt_const _ p
    have hsub := hcomp.sub hconst
    have hclm : ((2 * (p 0)) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)) - 0
        = dotCLMHam ((2:ℝ) • p) := by
      ext w
      simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.zero_apply,
        sub_zero, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, dotCLMHam_apply, dotProduct,
        Fin.sum_univ_one]
    rw [hclm] at hsub
    exact hsub
  convexOn_H_p := by
    refine Filter.Eventually.of_forall ?_
    intro _ m _
    show ConvexOn ℝ (Set.univ : Set (Fin 1 → ℝ))
          (fun q : Fin 1 → ℝ => (‖q‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ))
    have hfun : (fun q : Fin 1 → ℝ => (‖q‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ))
        = (fun q : Fin 1 → ℝ => (q 0) ^ 2 - m ^ (1:ℝ)) := by
      funext q; rw [norm_sq_fin_one]
    rw [hfun]
    have hlin : IsLinearMap ℝ (fun q : Fin 1 → ℝ => q 0) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    have hsq : ConvexOn ℝ Set.univ (fun q : Fin 1 → ℝ => (q 0) ^ 2) := by
      have hbase : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
        Even.convexOn_pow (even_two)
      simpa only [Function.comp_def, Set.preimage_univ, IsLinearMap.mk'_apply] using
        hbase.comp_linearMap (hlin.mk' _)
    simpa only [Pi.sub_def] using hsq.sub (concaveOn_const (m ^ (1:ℝ)) convex_univ)

/-- `HypothesisDpHMeasurable` for the concrete model (continuity ⇒ measurability). -/
private lemma nvMeasurable : Hamiltonian.HypothesisDpHMeasurable (d := 1) palomar_Main_nvH palomar_Main_nvDpH where
  measurable_H := nvMonotone.measurable_H
  measurable_DpH := nvMonotone.measurable_DpH

/-- `HypothesisHat0` for the concrete model: the right-limit at `0` is `‖p‖²`. -/
private lemma nvHat0 : HypothesisHat0 (d := 1) palomar_Main_nvH := by
  refine ⟨?_⟩
  refine Filter.Eventually.of_forall ?_
  intro x p
  refine ⟨(((‖p‖ : ℝ) ^ (2:ℝ) - 0) : ℝ), ?_⟩
  have hcont : Filter.Tendsto (fun m : ℝ => (‖p‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 ((‖p‖ : ℝ) ^ (2:ℝ) - 0)) := by
    have h1 : Filter.Tendsto (fun m : ℝ => m ^ (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
      have : Filter.Tendsto (fun m : ℝ => m ^ (1:ℝ)) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ (1:ℝ))) :=
        (Real.continuousAt_rpow_const 0 1 (by norm_num)).tendsto
      simp only [Real.zero_rpow (by norm_num : (1:ℝ) ≠ 0)] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (tendsto_const_nhds.sub h1)
  exact (WithTop.continuous_coe.continuousAt).tendsto.comp hcont

/-- `H_zero_eq_Hext` for the concrete model: the raw value `H x p 0 = ‖p‖²`
agrees with the paper's extended value at `0` (by uniqueness of limits). -/
private lemma nvAgree : H_zero_eq_Hext (d := 1) palomar_Main_nvH := by
  refine Filter.Eventually.of_forall ?_
  intro x p
  have hLim : Filter.Tendsto (fun m : ℝ => ((palomar_Main_nvH x p m : ℝ) : WithTop ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (((‖p‖ : ℝ) ^ (2:ℝ) - 0 : ℝ) : WithTop ℝ)) := by
    have hcont : Filter.Tendsto (fun m : ℝ => (‖p‖ : ℝ) ^ (2:ℝ) - m ^ (1:ℝ))
        (𝓝[>] (0:ℝ)) (𝓝 ((‖p‖ : ℝ) ^ (2:ℝ) - 0)) := by
      have h1 : Filter.Tendsto (fun m : ℝ => m ^ (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
        have : Filter.Tendsto (fun m : ℝ => m ^ (1:ℝ)) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ (1:ℝ))) :=
          (Real.continuousAt_rpow_const 0 1 (by norm_num)).tendsto
        simp only [Real.zero_rpow (by norm_num : (1:ℝ) ≠ 0)] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact (tendsto_const_nhds.sub h1)
    exact (WithTop.continuous_coe.continuousAt).tendsto.comp hcont
  have hEpsTendsto := tendsto_Hext_zero_of_exists (H := palomar_Main_nvH) (x := x) (p := p) ⟨_, hLim⟩
  have huniq : H_at_zero palomar_Main_nvH x p = (((‖p‖ : ℝ) ^ (2:ℝ) - 0 : ℝ) : WithTop ℝ) :=
    tendsto_nhds_unique hEpsTendsto hLim
  show ((palomar_Main_nvH x p 0 : ℝ) : WithTop ℝ) = Hext palomar_Main_nvH x p 0
  rw [← H_at_zero_def, huniq]
  have hraw : (palomar_Main_nvH x p 0 : ℝ) = (‖p‖ : ℝ) ^ (2:ℝ) - 0 := by
    simp only [palomar_Main_nvH, Real.zero_rpow (by norm_num : (1:ℝ) ≠ 0)]
  rw [hraw]

/-- `HypothesisHZeroExtension` for the concrete model. -/
private lemma nvHZeroExtension : Hamiltonian.HypothesisHZeroExtension (d := 1) palomar_Main_nvH where
  hHat0 := nvHat0
  hAgree := nvAgree

/-- `HypothesisHextJointCont` for the concrete model: `(p, m) ↦ ‖p‖² − m` is
jointly continuous on the closed cone `{0 ≤ m}`. -/
private lemma nvHextJointCont : Hamiltonian.HypothesisHextJointCont (d := 1) palomar_Main_nvH := by
  refine Filter.Eventually.of_forall ?_
  intro x
  show ContinuousOn (fun pm : (Fin 1 → ℝ) × ℝ =>
      (‖pm.1‖ : ℝ) ^ (2:ℝ) - pm.2 ^ (1:ℝ)) {pm | 0 ≤ pm.2}
  apply ContinuousOn.sub
  · apply ContinuousOn.rpow_const
    · exact (continuous_norm.comp continuous_fst).continuousOn
    · intro pm _; right; norm_num
  · apply ContinuousOn.rpow_const
    · exact continuous_snd.continuousOn
    · intro pm _; right; norm_num

end T3Nonvacuity

/-- **Non-vacuity witness for `thm_main_weak_power_growth_paper`.**

Instantiates EVERY binder of the public Theorem 3 at the concrete admissible
model `H(x,p,m) = ‖p‖² − m`, `D_pH(x,p,m) = 2 • p`, `V = 0` (dimension `d = 1`,
paper exponents `α = 2, β = 1`) and obtains its conclusion — a genuine weak
MFG solution.  This proves the public theorem's hypothesis set is **jointly
satisfiable**, permanently guarding against vacuous-binder regressions of the
kind removed in G7c-2 (the unsatisfiable `hWeakDerivK0`, commit `fd90baa`):
were any binder to become vacuous again, this witness would fail to build. -/
theorem nonvacuity_thm_main_weak_power_growth_paper :
    ∃ (m u : (Fin 1 → ℝ) → ℝ) (Du : Fin 1 → (Fin 1 → ℝ) → ℝ),
      IsWeakSolution (0 : (Fin 1 → ℝ) → ℝ) T3Nonvacuity.palomar_Main_nvH T3Nonvacuity.palomar_Main_nvDpH Du m u
        ∧ MemLpPer (ENNReal.ofReal (T3Nonvacuity.palomar_Main_nvWeakGrowth.β + 1)) m
        ∧ MemSobolevPer
            (ENNReal.ofReal (T3Nonvacuity.palomar_Main_nvWeakGrowth.α * (T3Nonvacuity.palomar_Main_nvWeakGrowth.β + 1)
              / T3Nonvacuity.palomar_Main_nvWeakGrowth.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube 1)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer (d := 1) i u (Du i))
        ∧ (∀ i, MemLpPer (d := 1)
            (ENNReal.ofReal (T3Nonvacuity.palomar_Main_nvWeakGrowth.α * (T3Nonvacuity.palomar_Main_nvWeakGrowth.β + 1)
              / T3Nonvacuity.palomar_Main_nvWeakGrowth.β)) (Du i)) :=
  thm_main_weak_power_growth_paper
    (0 : (Fin 1 → ℝ) → ℝ)
    T3Nonvacuity.nvMonotone
    T3Nonvacuity.palomar_Main_nvWeakGrowth
    T3Nonvacuity.nvDifferentiable
    T3Nonvacuity.nvMeasurable
    T3Nonvacuity.nvHZeroExtension
    (StationaryMFG.Periodic.MemLp.toMemLpPer
      (MeasureTheory.MemLp.zero
        (p := ENNReal.ofReal ((T3Nonvacuity.palomar_Main_nvWeakGrowth.β + 1)
          / T3Nonvacuity.palomar_Main_nvWeakGrowth.β))
        (μ := MeasureTheory.volume.restrict (UnitCube 1))))

/-- **Composability witness (anti-sham) for the `hstab` slot.** The
`∃ ε₀, ∀ ε < ε₀` output of
`Stabilization.stabilization_uniform_of_DpH_small` plugs into the
`hstab` argument of `keystone_hnn_threaded_of_strongVIfamily` verbatim
(same threshold-interval shape, same a.e. stabilisation identities), so
B2c can supply the A4 deliverable directly without reshaping. This would
fail to typecheck if the two shapes diverged. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Hε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpHε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (qOf : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖DpH x (fun i => Dυ i x) (μ x)‖ < M)
    (hUniq : ∀ e, 0 < e → ∀ x : Fin d → ℝ, ∀ q : Fin d → ℝ,
        HasSubgradientAt (K h) q
            (e • DpH x ((fun i => Dυ i x) - q) (μ x)) →
          q = qOf e x (fun i => Dυ i x) (μ x))
    (hHFormula : ∀ e, 0 < e → ∀ x : Fin d → ℝ,
      Hε e x (fun i => Dυ i x) (μ x)
        = H x ((fun i => Dυ i x) - qOf e x (fun i => Dυ i x) (μ x)) (μ x)
          + (1 / e) * K h (qOf e x (fun i => Dυ i x) (μ x)))
    (hDpHFormula : ∀ e, 0 < e → ∀ x : Fin d → ℝ,
      DpHε e x (fun i => Dυ i x) (μ x)
        = DpH x ((fun i => Dυ i x) - qOf e x (fun i => Dυ i x) (μ x))
            (μ x)) :
    ∃ ε₀ > 0, ∀ e, 0 < e → e < ε₀ →
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           Hε e x (fun i => Dυ i x) (μ x) = H x (fun i => Dυ i x) (μ x)) ∧
        (∀ᵐ x ∂(volume.restrict (UnitCube d)),
           DpHε e x (fun i => Dυ i x) (μ x)
             = DpH x (fun i => Dυ i x) (μ x)) :=
  Stabilization.stabilization_uniform_of_DpH_small
    h μ Dυ qOf Hε DpHε hM hbnd hUniq hHFormula hDpHFormula

end InfimalConvolution
end Theorems
end StationaryMFG

end
